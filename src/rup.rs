//! RUP (Reverse Unit Propagation) forward checker: validates a DRAT
//! addition stream. Each learned clause must become conflicted when its
//! negations are assumed and unit propagation runs over the formula plus
//! all previously validated clauses. This is the M1 contract: no learned
//! clause ships that the checker cannot prove.

use std::collections::HashMap;

pub struct RupChecker {
    clauses: Vec<Vec<i32>>,
    /// var -> current polarity (true = lit positive holds)
    assign: HashMap<u32, bool>,
    queue: Vec<i32>,
    n_vars: usize,
}

impl RupChecker {
    pub fn new(n_vars: usize) -> Self {
        RupChecker {
            clauses: Vec::new(),
            assign: HashMap::new(),
            queue: Vec::new(),
            n_vars,
        }
    }

    /// Adds a formula clause (available for all subsequent RUP checks).
    pub fn add(&mut self, lits: Vec<i32>) {
        for &l in &lits {
            self.n_vars = self.n_vars.max(l.unsigned_abs() as usize);
        }
        self.clauses.push(lits);
    }

    fn value(&self, l: i32) -> Option<bool> {
        self.assign.get(&l.unsigned_abs()).map(|&b| b == (l > 0))
    }

    fn assign(&mut self, l: i32) {
        self.assign.insert(l.unsigned_abs(), l > 0);
        self.queue.push(l);
    }

    /// Unit propagation to fixpoint over the clause set given current
    /// assignments. Runs at least one full scan (so existing unit clauses
    /// seed the propagation even with an empty queue — this is what makes
    /// the empty clause's RUP check meaningful). Returns true on conflict.
    fn propagate(&mut self) -> bool {
        loop {
            let snapshot = self.clauses.clone();
            let mut new_assign = false;
            for c in &snapshot {
                let mut false_count = 0usize;
                let mut sat = false;
                let mut unit_lit: Option<i32> = None;
                for &cl in c {
                    match self.value(cl) {
                        Some(true) => {
                            sat = true;
                            break;
                        }
                        Some(false) => false_count += 1,
                        None => unit_lit = Some(cl),
                    }
                }
                if sat {
                    continue;
                }
                if false_count == c.len() {
                    return true; // conflict
                }
                if false_count == c.len() - 1 {
                    let u = unit_lit.expect("unit without unset literal");
                    if self.value(u).is_none() {
                        self.assign(u);
                        new_assign = true;
                    }
                }
            }
            if !new_assign {
                return false;
            }
        }
    }

    /// Checks that clause `c` is RUP: assuming its negations propagates to
    /// a conflict. On success, `c` joins the available clause set.
    pub fn check_and_add(&mut self, c: Vec<i32>) -> bool {
        for &l in &c {
            self.n_vars = self.n_vars.max(l.unsigned_abs() as usize);
        }
        // assume negations of c
        for &l in &c {
            let nl = -l;
            match self.value(nl) {
                Some(true) => {} // already assumed
                Some(false) => {
                    // contradiction inside the assumption itself:
                    // c contains l and -l; the clause is a tautology —
                    // trivially implied, accept
                    for &a in &c {
                        self.assign.remove(&a.unsigned_abs());
                    }
                    self.queue.clear();
                    self.clauses.push(c);
                    return true;
                }
                None => self.assign(nl),
            }
        }
        let conflicted = self.propagate();
        // reset the assumption state
        let assumed: Vec<i32> = std::mem::take(&mut self.queue);
        for l in assumed {
            self.assign.remove(&l.unsigned_abs());
        }
        if !conflicted {
            return false;
        }
        self.clauses.push(c);
        true
    }
}
