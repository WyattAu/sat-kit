use sat_kit::{Answer, Solver};
#[test]
fn php_scaling_smoke() {
    for (pigeons, holes) in [(4u32, 3u32), (5, 4), (6, 5), (7, 6), (8, 7)] {
        let var = |p: u32, h: u32| ((p - 1) * holes + h) as i32;
        let mut ph: Vec<Vec<i32>> = Vec::new();
        for p in 1..=pigeons { ph.push((1..=holes).map(|h| var(p, h)).collect()); }
        for h in 1..=holes {
            for p1 in 1..=pigeons {
                for p2 in (p1 + 1)..=pigeons {
                    ph.push(vec![-var(p1, h), -var(p2, h)]);
                }
            }
        }
        let t0 = std::time::Instant::now();
        let mut s = Solver::new((pigeons * holes) as usize);
        s.reduce_threshold = u64::MAX; // reduction OFF
        for c in &ph { s.add_clause(c.clone()); }
        let a = s.solve();
        println!("PHP({pigeons},{holes}) [reduction OFF]: {a:?} in {:?}", t0.elapsed());
        assert_eq!(a, Answer::Unsat);
        let learned = s.drat.matches('\n').count() as u64 - ph.len() as u64;
        println!("PHP({pigeons},{holes}): {a:?} in {:?}, learned {learned}", t0.elapsed());
        assert_eq!(a, Answer::Unsat);
    }
}
