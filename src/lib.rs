//! sat-kit: a CDCL SAT solver.
//!
//! M0 scope: DIMACS parsing, two-watched-literal unit propagation,
//! 1UIP clause learning, VSIDS-style activity, geometric restarts.
//! Correctness is held to brute-force agreement on a random 3-SAT corpus
//! plus known encodings (pigeonhole, cardinality-limited colorings).
//! DRAT certificate emission lands in M1.

pub mod dimacs;
pub mod rup;

/// Literal: `1..=n` positive, `-n..=-1` negative (DIMACS convention).
pub type Lit = i32;

#[inline]
pub fn var(l: Lit) -> usize {
    l.unsigned_abs() as usize
}

#[inline]
pub fn neg(l: Lit) -> Lit {
    -l
}

#[inline]
fn lit_idx(l: Lit) -> usize {
    2 * (var(l) - 1) + usize::from(l < 0)
}

struct Clause {
    lits: Vec<Lit>,
    learned: bool,
    /// Literal Block Distance: distinct decision levels in the clause.
    /// Low-LBD clauses generalize; high-LBD ones drop on reduction.
    lbd: u32,
}

#[derive(Clone, Copy, PartialEq)]
enum Assign {
    Unset,
    True,
    False,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Answer {
    Sat,
    Unsat,
}

pub struct Solver {
    n_vars: usize,
    clauses: Vec<Clause>,
    assign: Vec<Assign>,
    level_of: Vec<u32>,
    reason: Vec<Option<u32>>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    learned_count: u64,
    reductions: u64,
    /// learned-clause mass that triggers reduce_db (default 4000)
    pub reduce_threshold: u64,
    watches: Vec<Vec<u32>>,
    activity: Vec<f64>,
    var_inc: f64,
    /// learned-clause additions in DRAT format ("l1 l2 ... 0")
    pub drat: String,
}

impl Solver {
    pub fn new(n_vars: usize) -> Self {
        Solver {
            n_vars,
            clauses: Vec::new(),
            assign: vec![Assign::Unset; n_vars],
            level_of: vec![0; n_vars],
            reason: vec![None; n_vars],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            learned_count: 0,
            reductions: 0,
            reduce_threshold: 4000,
            watches: vec![Vec::new(); 2 * n_vars],
            activity: vec![0.0; n_vars],
            var_inc: 1.0,
            drat: String::new(),
        }
    }

    /// Adds a problem clause (empty clause = trivially UNSAT).
    pub fn add_clause(&mut self, lits: Vec<Lit>) {
        let id = self.clauses.len() as u32;
        let line = fmt_lits(&lits);
        let drat_line = if line.is_empty() { "0\n".to_string() } else { format!("{line} 0\n") };
        self.drat.push_str(&drat_line);
        self.clauses.push(Clause { lits: lits.clone(), learned: false, lbd: 0 });
        if lits.len() >= 2 {
            let c = &self.clauses[id as usize].lits;
            self.watches[lit_idx(c[0])].push(id);
            self.watches[lit_idx(c[1])].push(id);
        }
    }

    fn value(&self, l: Lit) -> Assign {
        match self.assign[var(l) - 1] {
            Assign::Unset => Assign::Unset,
            a if (l > 0) == (a == Assign::True) => Assign::True,
            _ => Assign::False,
        }
    }

    fn assign_lit(&mut self, l: Lit, level: u32, reason: Option<u32>) {
        self.assign[var(l) - 1] = if l > 0 { Assign::True } else { Assign::False };
        self.level_of[var(l) - 1] = level;
        self.reason[var(l) - 1] = reason;
        self.trail.push(l);
    }

    fn unset(&mut self, l: Lit) {
        self.assign[var(l) - 1] = Assign::Unset;
    }

    fn enqueue(&mut self, l: Lit, level: u32, reason: Option<u32>) -> bool {
        match self.value(l) {
            Assign::True => true,
            Assign::False => false,
            Assign::Unset => {
                self.assign_lit(l, level, reason);
                true
            }
        }
    }

    /// Two-watched-literal propagation from `qhead`. Returns the
    /// conflicting clause id on conflict.
    fn propagate(&mut self, level: u32) -> Option<u32> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            // p became true; clauses watching neg(p) need a replacement
            let wp = lit_idx(neg(p));
            let mut i = 0;
            while i < self.watches[wp].len() {
                let cid = self.watches[wp][i];
                if self.clauses[cid as usize].lits[1] != neg(p) {
                    self.clauses[cid as usize].lits.swap(0, 1);
                }
                let first = self.clauses[cid as usize].lits[0];
                if self.value(first) == Assign::True {
                    i += 1; // satisfied; keep the watch
                    continue;
                }
                let lits = &self.clauses[cid as usize].lits;
                let mut found: Option<usize> = None;
                for k in 2..lits.len() {
                    if self.value(lits[k]) != Assign::False {
                        found = Some(k);
                        break;
                    }
                }
                if let Some(k) = found {
                    let nl = lits[k];
                    self.clauses[cid as usize].lits.swap(1, k);
                    let dest = lit_idx(nl);
                    self.watches[dest].push(cid);
                    self.watches[wp].swap_remove(i);
                    continue;
                }
                // unit or conflict on `first`
                if !self.enqueue(first, level, Some(cid)) {
                    return Some(cid);
                }
                i += 1;
            }
        }
        None
    }

    pub fn solve(&mut self) -> Answer {
        self.qhead = 0;
        let mut level: u32 = 0;
        let units: Vec<(u32, Lit)> = self
            .clauses
            .iter()
            .enumerate()
            .filter_map(|(id, c)| {
                if c.lits.is_empty() {
                    None
                } else if c.lits.len() == 1 {
                    Some((id as u32, c.lits[0]))
                } else {
                    None
                }
            })
            .collect();
        if self.clauses.iter().any(|c| c.lits.is_empty()) {
            return Answer::Unsat;
        }
        for (id, l) in units {
            if !self.enqueue(l, 0, Some(id)) {
                return Answer::Unsat;
            }
        }
        if self.propagate(0).is_some() {
            self.drat.push_str("0\n"); // empty clause: UNSAT proof complete
            self.learned_count += 1;
            return Answer::Unsat;
        }
        let mut conflicts_since_restart: u64 = 0;
        let mut restart_limit: u64 = 100;
        loop {
            if let Some(_cid) = self.propagate(level) {
                conflicts_since_restart += 1;
                if level == 0 {
                    // the conflicting clause is fully false at level 0:
                    // the empty clause is RUP and completes the proof
                    self.drat.push_str("0\n");
                    self.learned_count += 1;
                    return Answer::Unsat;
                }
                let cid = _cid;
                let (learned, bt) = self.analyze(cid);
                if learned.is_empty() {
                    return Answer::Unsat;
                }
                // a learned unit is UNSAT only if its lit is false by a
                // LEVEL-0 assignment (permanent). Checking value() here —
                // before the backjump — misreads decision-level falseness
                // as permanent: the corpus caught this on a learned unit
                // [-6] refuting a level-1 decision 6=true.
                if bt == 0 && learned.len() == 1 && self.level_of[var(learned[0]) - 1] == 0 {
                    return Answer::Unsat;
                }
                self.bump_var_inc();
                self.cancel_until(bt);
                level = bt;
                let id = self.clauses.len() as u32;
                let lits = learned.clone();
                self.watches[lit_idx(lits[0])].push(id);
                if lits.len() >= 2 {
                    self.watches[lit_idx(lits[1])].push(id);
                }
                let mut lvls: Vec<u32> =
                    lits.iter().map(|l| self.level_of[var(*l) - 1]).collect();
                lvls.sort_unstable();
                lvls.dedup();
                let lbd = lvls.len() as u32;
                self.drat.push_str(&format!("{} 0\n", fmt_lits(&lits)));
                self.clauses.push(Clause { lits, learned: true, lbd });
                self.learned_count += 1;
                let l = learned[0];
                self.assign_lit(l, level, Some(id));
                continue;
            }
            // clause-DB reduction: when learned mass grows, drop the worst
            // half by LBD (locked clauses — reasons of live assignments —
            // survive). Emits DRAT deletion lines so the certificate
            // mirrors the solver's clause set.
            if self.learned_count > self.reduce_threshold + 300 * self.reductions {
                self.reductions += 1;
                self.reduce_db();
            }
            if conflicts_since_restart >= restart_limit && level > 0 {
                restart_limit = (restart_limit as f64 * 1.5) as u64;
                self.cancel_until(0);
                level = 0;
                conflicts_since_restart = 0;
                continue;
            }
            match self.pick_branch() {
                Some(l) => {
                    self.trail_lim.push(self.trail.len());
                    level += 1;
                    self.assign_lit(l, level, None);
                }
                None => return Answer::Sat,
            }
        }
    }

    /// Drops the worst half of learned clauses by LBD. Locked clauses
    /// (reasons of live assignments), binaries, and LBD <= 2 (glue)
    /// survive. Emits DRAT deletion lines; rebuilds watch lists.
    fn reduce_db(&mut self) {
        let mut locked: Vec<bool> = vec![false; self.clauses.len()];
        for v in 0..self.n_vars {
            if self.assign[v] != Assign::Unset {
                if let Some(cid) = self.reason[v] {
                    locked[cid as usize] = true;
                }
            }
        }
        let mut ranked: Vec<(u32, u32)> = (0..self.clauses.len() as u32)
            .filter(|&id| {
                let c = &self.clauses[id as usize];
                c.learned && !locked[id as usize] && c.lits.len() > 2 && c.lbd > 2
            })
            .map(|id| (self.clauses[id as usize].lbd, id))
            .collect();
        ranked.sort_unstable();
        let dropped: Vec<u32> = ranked
            .iter()
            .take(ranked.len() / 2)
            .map(|(_, id)| *id)
            .collect();
        for &id in dropped.iter().rev() {
            let lits = self.clauses[id as usize].lits.clone();
            self.drat.push_str(&format!("d {} 0\n", fmt_lits(&lits)));
        }
        let mut new_clauses: Vec<Clause> = Vec::with_capacity(self.clauses.len());
        let mut id_map: std::collections::HashMap<u32, u32> =
            std::collections::HashMap::new();
        let mut kept = 0u64;
        for (i, c) in self.clauses.drain(..).enumerate() {
            if dropped.binary_search(&(i as u32)).is_err() {
                id_map.insert(i as u32, new_clauses.len() as u32);
                if c.learned {
                    kept += 1;
                }
                new_clauses.push(c);
            }
        }
        self.clauses = new_clauses;
        self.learned_count = kept;
        for r in self.reason.iter_mut() {
            if let Some(cid) = *r {
                *r = id_map.get(&cid).copied();
            }
        }
        self.watches = vec![Vec::new(); 2 * self.n_vars];
        for (id, c) in self.clauses.iter().enumerate() {
            if c.lits.len() >= 2 {
                self.watches[lit_idx(c.lits[0])].push(id as u32);
                self.watches[lit_idx(c.lits[1])].push(id as u32);
            }
        }
    }

    fn pick_branch(&self) -> Option<Lit> {
        let mut best: Option<usize> = None;
        for v in 0..self.n_vars {
            if self.assign[v] == Assign::Unset
                && best.map_or(true, |b| self.activity[v] > self.activity[b])
            {
                best = Some(v);
            }
        }
        best.map(|v| (v + 1) as Lit)
    }

    fn cancel_until(&mut self, lvl: u32) {
        while (self.trail_lim.len() as u32) > lvl {
            let lim = self.trail_lim.pop().unwrap();
            let tail: Vec<Lit> = self.trail[lim..].to_vec();
            for l in tail {
                self.unset(l);
            }
            self.trail.truncate(lim);
        }
        self.qhead = self.trail.len();
    }

    /// 1UIP learning (MiniSat-style index walk): resolve backwards from
    /// the conflict, clearing each pivot's seen flag so the walk advances
    /// to the remaining current-level literals, until exactly one remains.
    /// Returns the learned clause ordered `[asserting, max-level, ...]`
    /// and the backjump level. No trail mutation happens here —
    /// `cancel_until` does the unsetting.
    fn analyze(&mut self, confl: u32) -> (Vec<Lit>, u32) {
        let cur = self.trail_lim.len() as u32;
        let mut seen = vec![false; self.n_vars];
        let mut learned: Vec<Lit> = Vec::new();
        let mut counter = 0usize;
        let mut cid = confl;
        let mut p: Lit = 0;
        let mut index = self.trail.len().saturating_sub(1);
        // the reason clause being resolved contains the pivot it was the
        // reason FOR — skip it, or the pivot is re-seen (seen was cleared on
        // consumption) and counter is inflated: unsound learned clauses.
        let mut skip: Option<Lit> = None;
        loop {
            let lits = self.clauses[cid as usize].lits.clone();
            for &l in &lits {
                if Some(l) == skip {
                    continue;
                }
                let v = var(l) - 1;
                if !seen[v] && self.level_of[v] > 0 {
                    seen[v] = true;
                    self.activity[v] += self.var_inc;
                    if self.level_of[v] == cur {
                        counter += 1;
                    } else {
                        learned.push(l);
                    }
                }
            }
            while !seen[var(self.trail[index]) - 1] {
                index -= 1;
            }
            p = self.trail[index];
            index = index.saturating_sub(1);
            seen[var(p) - 1] = false;
            skip = Some(p);
            let reason = self.reason[var(p) - 1];
            if counter > 0 {
                counter -= 1;
            }
            if counter == 0 {
                break;
            }
            cid = reason.expect(
                "decision pivot consumed while pathC > 0 — learning invariant broken",
            );
        }
        let uip = neg(p);
        learned.push(uip);
        // backjump level: highest level among the learned lits except uip
        let mut bt = 0u32;
        for &l in learned.iter().filter(|&&l| l != uip) {
            let lv = self.level_of[var(l) - 1];
            if lv > bt {
                bt = lv;
            }
        }
        // order: [uip, max-level lit, rest...]
        let ui = learned.iter().position(|&l| l == uip).unwrap();
        learned.swap(0, ui);
        if learned.len() >= 2 {
            let mi = learned
                .iter()
                .enumerate()
                .skip(1)
                .max_by_key(|(i, l)| (self.level_of[var(**l) - 1], std::cmp::Reverse(*i)))
                .map(|(i, _)| i)
                .unwrap();
            learned.swap(1, mi);
        }
        (learned, bt)
    }

    fn bump_var_inc(&mut self) {
        self.var_inc *= 1.5;
        if self.var_inc > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
    }

    /// Builds a solver from parsed DIMACS.
    pub fn from_dimacs(d: &dimacs::Dimacs) -> Self {
        let mut s = Solver::new(d.n_vars);
        for c in &d.clauses {
            s.add_clause(c.clone());
        }
        s
    }

    /// Number of learned clauses still pending reduction accounting.
    pub fn learned_count(&self) -> u64 {
        self.learned_count
    }

    pub fn model(&self) -> Option<Vec<bool>> {
        Some((0..self.n_vars).map(|v| self.assign[v] == Assign::True).collect())
    }
}

fn fmt_lits(lits: &[Lit]) -> String {
    lits.iter().map(|l| l.to_string()).collect::<Vec<_>>().join(" ")
}
