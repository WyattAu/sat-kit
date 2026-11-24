//! Brute-force cross-check: the solver must agree with exhaustive search
//! on every instance. This is the M0 correctness contract.

use sat_kit::dimacs;
use sat_kit::{Answer, Solver};

/// Exhaustive check over all 2^n assignments.
fn brute(n: usize, clauses: &[Vec<i32>]) -> bool {
    for mask in 0u64..(1u64 << n) {
        let ok = clauses.iter().all(|c| {
            c.iter().any(|&l| {
                let v = l.unsigned_abs() as u64 - 1;
                let val = (mask >> v) & 1 == 1;
                val == (l > 0)
            })
        });
        if ok {
            return true;
        }
    }
    false
}

fn check_instance(n: usize, clauses: &[Vec<i32>], name: &str) {
    let expected = brute(n, clauses);
    let mut s = Solver::new(n);
    for c in clauses {
        s.add_clause(c.clone());
    }
    let got = s.solve();
    assert_eq!(
        got,
        if expected { Answer::Sat } else { Answer::Unsat },
        "{name}: solver says {got:?}, brute force says {expected}"
    );
    // on SAT, verify the model actually satisfies every clause
    if got == Answer::Sat {
        let model = s.model().unwrap();
        for c in clauses {
            assert!(
                c.iter().any(|&l| model[l.unsigned_abs() as usize - 1] == (l > 0)),
                "{name}: model does not satisfy clause {c:?}"
            );
        }
    }
}

/// Tiny xorshift so the corpus is deterministic across runs.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn lit(&mut self, n: usize) -> i32 {
        let v = (self.next() % n as u64) as usize + 1;
        if self.next() & 1 == 0 {
            v as i32
        } else {
            -(v as i32)
        }
    }
}

#[test]
fn known_encodings() {
    // pigeonhole PHP(3 pigeons, 2 holes): 3 pigeons cannot pair-free map
    // into 2 holes -> UNSAT (classic hard-for-resolution family)
    let pigeons = 3u32;
    let holes = 2u32;
    let var = |p: u32, h: u32| ((p - 1) * holes + h) as i32;
    let mut ph: Vec<Vec<i32>> = Vec::new();
    for p in 1..=pigeons {
        ph.push((1..=holes).map(|h| var(p, h)).collect()); // each pigeon in some hole
    }
    for h in 1..=holes {
        for p1 in 1..=pigeons {
            for p2 in (p1 + 1)..=pigeons {
                ph.push(vec![-var(p1, h), -var(p2, h)]); // no hole shared
            }
        }
    }
    let n = (pigeons * holes) as usize;
    let mut s = Solver::new(n);
    for c in &ph {
        s.add_clause(c.clone());
    }
    assert_eq!(s.solve(), Answer::Unsat, "PHP(3,2) must be UNSAT");

    // and PHP(2 pigeons, 3 holes) is SAT
    let pigeons = 2u32;
    let holes = 3u32;
    let var = |p: u32, h: u32| ((p - 1) * holes + h) as i32;
    let mut ph2: Vec<Vec<i32>> = Vec::new();
    for p in 1..=pigeons {
        ph2.push((1..=holes).map(|h| var(p, h)).collect());
    }
    for h in 1..=holes {
        for p1 in 1..=pigeons {
            for p2 in (p1 + 1)..=pigeons {
                ph2.push(vec![-var(p1, h), -var(p2, h)]);
            }
        }
    }
    let mut s2 = Solver::new((pigeons * holes) as usize);
    for c in &ph2 {
        s2.add_clause(c.clone());
    }
    assert_eq!(s2.solve(), Answer::Sat, "PHP(2,3) must be SAT");
    let model = s2.model().unwrap();
    // the encoding implies: each pigeon in >= 1 hole, and no hole shared
    for p in 1..=pigeons {
        let count: u32 = (1..=holes)
            .map(|h| u32::from(model[var(p, h) as usize - 1]))
            .sum();
        assert!(count >= 1, "pigeon {p} in {count} holes");
    }
    for h in 1..=holes {
        let shared: u32 = (1..=pigeons)
            .map(|p| u32::from(model[var(p, h) as usize - 1]))
            .sum();
        assert!(shared <= 1, "hole {h} holds {shared} pigeons");
    }
}

#[test]
fn random_3sat_corpus_agrees_with_brute_force() {
    let mut rng = Rng(0x5A17);
    for inst in 0..150 {
        let n = 8;
        let m = 20 + (inst % 30) as usize * 2; // sweep under- to over-constrained
        let mut clauses = Vec::with_capacity(m);
        for _ in 0..m {
            let mut seen = std::collections::HashSet::new();
            let mut c = Vec::new();
            while c.len() < 3 {
                let l = rng.lit(n);
                if seen.insert(l.unsigned_abs()) {
                    c.push(l);
                }
            }
            clauses.push(c);
        }
        check_instance(n, &clauses, &format!("3sat-{inst}-{m}"));
    }
}

#[test]
fn unit_and_empty_clauses() {
    // directly-false unit
    check_instance(2, &[vec![1], vec![-1]], "unit contradiction");
    // empty clause: trivially UNSAT
    let mut s = Solver::new(1);
    s.add_clause(vec![]);
    assert_eq!(s.solve(), Answer::Unsat);
    // single unit: SAT with forced assignment
    check_instance(2, &[vec![1]], "single unit");
    check_instance(3, &[vec![-2], vec![3, -2], vec![-3, 1]], "small mixed");
}

#[test]
fn dimacs_end_to_end() {
    let src = "p cnf 4 3\n1 2 0\n-1 3 0\n-3 -2 0\n";
    let d = dimacs::parse(src).unwrap();
    let mut s = Solver::new(d.n_vars);
    for c in d.clauses {
        s.add_clause(c);
    }
    assert_eq!(s.solve(), Answer::Sat);
}
