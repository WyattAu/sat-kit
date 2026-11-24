//! M3: the forward checker must validate the largest certificates in
//! reasonable time (competition feasibility: a checker slower than the
//! solver can't serve as a submission tool).

use sat_kit::rup::RupChecker;
use sat_kit::{Answer, Solver};
use std::time::Instant;

#[test]
fn checker_handles_largest_certificate() {
    // PHP(8,7): the largest generator family member (~7k learned clauses)
    let pigeons = 8u32;
    let holes = 7u32;
    let var = |p: u32, h: u32| ((p - 1) * holes + h) as i32;
    let mut ph: Vec<Vec<i32>> = Vec::new();
    for p in 1..=pigeons {
        ph.push((1..=holes).map(|h| var(p, h)).collect());
    }
    for h in 1..=holes {
        for p1 in 1..=pigeons {
            for p2 in (p1 + 1)..=pigeons {
                ph.push(vec![-var(p1, h), -var(p2, h)]);
            }
        }
    }
    let mut s = Solver::new((pigeons * holes) as usize);
    for c in &ph {
        s.add_clause(c.clone());
    }
    assert_eq!(s.solve(), Answer::Unsat);

    let mut chk = RupChecker::new((pigeons * holes) as usize);
    for c in &ph {
        chk.add(c.clone());
    }
    let t0 = Instant::now();
    let mut validated = 0usize;
    for line in s.drat.lines() {
        let mut lits: Vec<i32> = line
            .split_whitespace()
            .filter_map(|t| t.parse().ok())
            .collect();
        assert_eq!(lits.last(), Some(&0));
        lits.pop();
        assert!(chk.check_and_add(lits), "certificate clause failed RUP");
        validated += 1;
    }
    let elapsed = t0.elapsed();
    println!(
        "checker: {validated} clauses in {elapsed:?} ({:.1} clauses/sec)",
        validated as f64 / elapsed.as_secs_f64()
    );
    // feasibility band: the checker validates at least 1k clauses/sec
    assert!(
        validated as f64 / elapsed.as_secs_f64() > 1000.0,
        "checker throughput below competition feasibility"
    );
}
