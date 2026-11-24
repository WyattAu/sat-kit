//! M1 contract: every learned clause in the emitted DRAT stream must pass
//! RUP against the formula plus prior learned clauses, and an UNSAT proof
//! must end with the empty clause. The RupChecker is the verifier.

use sat_kit::rup::RupChecker;
use sat_kit::{Answer, Solver};

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
}

fn check_certificate(n: usize, clauses: &[Vec<i32>], name: &str) -> Answer {
    let mut s = Solver::new(n);
    for c in clauses {
        s.add_clause(c.clone());
    }
    let answer = s.solve();

    // parse the certificate: lines of lits ending in 0
    let mut additions: Vec<Vec<i32>> = Vec::new();
    let mut deletions: Vec<Vec<i32>> = Vec::new();
    for line in s.drat.lines() {
        let deletion = line.trim_start().starts_with('d');
        let body = if deletion { &line[1..] } else { line };
        let mut lits: Vec<i32> = body
            .split_whitespace()
            .filter_map(|t| t.parse().ok())
            .collect();
        // DRAT lines end with the 0 terminator — strip it
        assert_eq!(lits.last(), Some(&0), "line must end in 0: {line}");
        lits.pop();
        if deletion {
            deletions.push(lits);
        } else {
            additions.push(lits); // empty vec = the empty clause
        }
    }
    assert_eq!(
        additions.len(),
        clauses.len() + s.learned_count() as usize,
        "{name}: learned-clause accounting (additions={} clauses={} learned_count={} answer={:?})",
        additions.len(),
        clauses.len(),
        s.learned_count(),
        answer
    );
    // the first additions mirror add_clause() calls in order
    assert!(additions.len() >= clauses.len(), "{name}: missing problem clauses");
    for (i, c) in clauses.iter().enumerate() {
        assert_eq!(additions[i], *c, "{name}: problem clause {i} mismatch");
    }

    let mut chk = RupChecker::new(n);
    for c in clauses {
        if !c.is_empty() {
            chk.add(c.clone());
        } else {
            return answer; // empty problem clause: trivially UNSAT
        }
    }
    // replay deletions and additions in order: deletions must match an
    // available clause exactly (the solver only deletes what it added).
    // Deletion bookkeeping: a deletion references a clause position in the
    // ADDITION stream — track additions so we can locate them.
    let mut add_index = clauses.len();
    let mut del_iter = deletions.iter();
    let mut next_deletion = del_iter.next();
    for (i, learned) in additions[clauses.len()..].iter().enumerate() {
        // deletions that occurred before this addition in the stream
        while let Some(d) = next_deletion {
            assert!(chk.delete(d), "{name}: deletion {d:?} matches nothing");
            next_deletion = del_iter.next();
            let _ = &mut add_index;
        }
        assert!(
            chk.check_and_add(learned.clone()),
            "{name}: learned clause {i} {learned:?} is NOT RUP — unsound learning"
        );
    }
    // trailing deletions after the last addition
    while let Some(d) = next_deletion {
        assert!(chk.delete(d), "{name}: trailing deletion {d:?} matches nothing");
        next_deletion = del_iter.next();
    }
    if answer == Answer::Unsat {
        assert_eq!(
            additions.last().map(|v| v.len()),
            Some(0),
            "{name}: UNSAT proof must end with the empty clause"
        );
    }
    answer
}

#[test]
fn certificates_check_over_corpus() {
    let mut rng = Rng(0x5A17);
    for inst in 0..150u32 {
        let n = 8usize;
        let m = 20 + (inst % 30) as usize * 2;
        let mut clauses = Vec::with_capacity(m);
        for _ in 0..m {
            let mut seen = std::collections::HashSet::new();
            let mut c = Vec::new();
            while c.len() < 3 {
                let v = (rng.next() % n as u64) as usize + 1;
                let l = if rng.next() & 1 == 0 { v as i32 } else { -(v as i32) };
                if seen.insert(l.unsigned_abs()) {
                    c.push(l);
                }
            }
            clauses.push(c);
        }
        check_certificate(n, &clauses, &format!("3sat-{inst}"));
    }
}

#[test]
fn reduction_path_certificate_valid() {
    // force the reduction threshold low so reduce_db fires on a small
    // instance, then validate the full certificate INCLUDING deletions
    let mut rng = Rng(0xDADA);
    for inst in 0..40u32 {
        let n = 12usize;
        let m = 40 + (inst % 20) as usize * 5;
        let mut clauses = Vec::with_capacity(m);
        for _ in 0..m {
            let mut seen = std::collections::HashSet::new();
            let mut c = Vec::new();
            while c.len() < 3 {
                let v = (rng.next() % n as u64) as usize + 1;
                let l = if rng.next() & 1 == 0 { v as i32 } else { -(v as i32) };
                if seen.insert(l.unsigned_abs()) {
                    c.push(l);
                }
            }
            clauses.push(c);
        }
        let mut s = Solver::new(n);
        s.reduce_threshold = 30;
        for c in &clauses {
            s.add_clause(c.clone());
        }
        let answer = s.solve();
        // certificate validation with deletions honored
        let mut additions: Vec<Vec<i32>> = Vec::new();
        let mut deletions: Vec<Vec<i32>> = Vec::new();
        for line in s.drat.lines() {
            let deletion = line.trim_start().starts_with('d');
            let body = if deletion { &line[1..] } else { line };
            let mut lits: Vec<i32> =
                body.split_whitespace().filter_map(|t| t.parse().ok()).collect();
            assert_eq!(lits.last(), Some(&0));
            lits.pop();
            if deletion { deletions.push(lits); } else { additions.push(lits); }
        }
        let mut chk = RupChecker::new(n);
        for c in &clauses {
            chk.add(c.clone());
        }
        let mut del_iter = deletions.iter();
        let mut next_deletion = del_iter.next();
        for learned in additions[clauses.len()..].iter() {
            while let Some(d) = next_deletion {
                assert!(chk.delete(d), "deletion {d:?} matches nothing");
                next_deletion = del_iter.next();
            }
            assert!(
                chk.check_and_add(learned.clone()),
                "learned {learned:?} not RUP after reduction"
            );
            if learned.is_empty() {
                break;
            }
        }
        assert_eq!(
            answer,
            if learned_clause_stream_unsat(&additions[clauses.len()..]) {
                Answer::Unsat
            } else {
                Answer::Sat
            }
        );
    }

    fn learned_clause_stream_unsat(stream: &[Vec<i32>]) -> bool {
        stream.iter().any(|c| c.is_empty())
    }
}

#[test]
fn unsat_proofs_end_with_empty_clause() {
    // PHP(3,2): UNSAT — the certificate must end with the empty clause
    let pigeons = 3u32;
    let holes = 2u32;
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
    check_certificate((pigeons * holes) as usize, &ph, "PHP(3,2)");
}
