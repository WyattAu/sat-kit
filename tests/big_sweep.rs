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

fn brute(n: usize, clauses: &[Vec<i32>]) -> bool {
    for mask in 0u64..(1u64 << n) {
        if clauses.iter().all(|c| c.iter().any(|&l| ((mask >> (l.unsigned_abs() as u64 - 1)) & 1 == 1) == (l > 0))) {
            return true;
        }
    }
    false
}

#[test]
fn big_sweep_n10() {
    let mut rng = Rng(0xC0FFEE);
    for inst in 0..400 {
        let n = 10;
        let m = 30 + (inst % 45) as usize * 3;
        let mut clauses = Vec::with_capacity(m);
        for _ in 0..m {
            let mut seen = std::collections::HashSet::new();
            let mut c = Vec::new();
            while c.len() < 3 {
                let v = (rng.next() % n as u64) as usize + 1;
                let sign = rng.next() & 1 == 0;
                let l = if sign { v as i32 } else { -(v as i32) };
                if seen.insert(l.unsigned_abs()) {
                    c.push(l);
                }
            }
            clauses.push(c);
        }
        let expected = brute(n, &clauses);
        let mut s = Solver::new(n);
        for c in &clauses { s.add_clause(c.clone()); }
        let got = s.solve();
        assert_eq!(
            got,
            if expected { Answer::Sat } else { Answer::Unsat },
            "inst {inst} (n={n} m={m})"
        );
    }
}
