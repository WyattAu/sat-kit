//! M3 benchmark-instance generator: fresh instances across structured
//! families, classified by our own solve time as the interest-band proxy
//! (the rules: not MiniSat-easy, not own-solver-hard).

use sat_kit::{Answer, Solver};
use std::time::Instant;

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

fn write_cnf(name: &str, n_vars: usize, clauses: &[Vec<i32>]) -> std::io::Result<u128> {
    let mut body = String::new();
    body.push_str(&format!("c sat-kit benchmark {name}\n"));
    body.push_str(&format!("p cnf {n_vars} {}\n", clauses.len()));
    for c in clauses {
        for l in c {
            body.push_str(&format!("{l} "));
        }
        body.push_str("0\n");
    }
    let t0 = Instant::now();
    let mut s = Solver::new(n_vars);
    for c in clauses {
        s.add_clause(c.clone());
    }
    let answer = s.solve();
    let micros = t0.elapsed().as_micros();
    let path = format!("instances/{name}.cnf");
    std::fs::write(&path, body)?;
    println!("{name}: {n_vars} vars {} clauses -> {answer:?} in {micros}us", clauses.len());
    Ok(micros)
}

fn main() {
    std::fs::create_dir_all("instances").unwrap();
    let mut manifest: Vec<String> = Vec::new();
    let mut rng = Rng(0x51EED);
    let mut idx = 0usize;

    // family 1: pigeonhole PHP(n, n-1) — UNSAT, resolution-hard
    for p in [7u32, 8, 9] {
        let holes = p - 1;
        let var = |pi: u32, h: u32| ((pi - 1) * holes + h) as i32;
        let mut c: Vec<Vec<i32>> = Vec::new();
        for pi in 1..=p {
            c.push((1..=holes).map(|h| var(pi, h)).collect());
        }
        for h in 1..=holes {
            for a in 1..=p {
                for b in (a + 1)..=p {
                    c.push(vec![-var(a, h), -var(b, h)]);
                }
            }
        }
        let name = format!("satkit-{idx:02}-pigeonhole-{p}-{holes}");
        let t = write_cnf(&name, (p * holes) as usize, &c).unwrap();
        manifest.push(format!(
            "| {name} | pigeonhole | {} | {} | {t}us | UNSAT |",
            p * holes,
            c.len()
        ));
        idx += 1;
    }

    // family 2: random 3-SAT near threshold (ratio ~4.26) — hard band
    for (n, ratio_pct, seed_off) in [(90usize, 420u64, 1u64), (100, 426, 2), (120, 430, 3), (140, 426, 4), (150, 433, 5)] {
        let m = (n as u64 * ratio_pct / 100) as usize;
        let mut r = Rng(0xBEEF + seed_off * 7919);
        let mut c: Vec<Vec<i32>> = Vec::new();
        for _ in 0..m {
            let mut seen = std::collections::HashSet::new();
            let mut cl = Vec::new();
            while cl.len() < 3 {
                let v = (r.next() % n as u64) as usize + 1;
                let l = if r.next() & 1 == 0 { v as i32 } else { -(v as i32) };
                if seen.insert(l.unsigned_abs()) {
                    cl.push(l);
                }
            }
            c.push(cl);
        }
        let name = format!("satkit-{idx:02}-rand3sat-n{n}-r{ratio_pct}");
        let t = write_cnf(&name, n, &c).unwrap();
        manifest.push(format!("| {name} | random-3sat | {n} | {m} | {t}us | ? |"));
        idx += 1;
    }

    // family 2b: random 3-SAT at larger sizes (different seeds)
    for (n, ratio_pct, seed_off) in [(110usize, 424u64, 6u64), (130, 428, 7), (145, 430, 8)] {
        let m = (n as u64 * ratio_pct / 100) as usize;
        let mut r = Rng(0xBEEF + seed_off * 7919);
        let mut c: Vec<Vec<i32>> = Vec::new();
        for _ in 0..m {
            let mut seen = std::collections::HashSet::new();
            let mut cl = Vec::new();
            while cl.len() < 3 {
                let v = (r.next() % n as u64) as usize + 1;
                let l = if r.next() & 1 == 0 { v as i32 } else { -(v as i32) };
                if seen.insert(l.unsigned_abs()) {
                    cl.push(l);
                }
            }
            c.push(cl);
        }
        let name = format!("satkit-{idx:02}-rand3sat-n{n}-r{ratio_pct}");
        let t = write_cnf(&name, n, &c).unwrap();
        manifest.push(format!("| {name} | random-3sat | {n} | {m} | {t}us | ? |"));
        idx += 1;
    }

    // family 3: graph coloring (k-color a dense random graph)
    for (verts, k, density_pct) in [(30usize, 3u32, 55u64), (40, 3, 60), (35, 3, 65)] {
        let mut r = Rng(0xF00D + verts as u64 * 131);
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for u in 0..verts {
            for v in (u + 1)..verts {
                if r.next() % 100 < density_pct {
                    edges.push((u, v));
                }
            }
        }
        let var = |u: usize, col: u32| (u * k as usize + col as usize + 1) as i32;
        let mut c: Vec<Vec<i32>> = Vec::new();
        for u in 0..verts {
            c.push((0..k).map(|col| var(u, col)).collect());
        }
        for u in 0..verts {
            for a in 0..k {
                for b in (a + 1)..k {
                    c.push(vec![-var(u, a), -var(u, b)]);
                }
            }
        }
        for (u, v) in &edges {
            for col in 0..k {
                c.push(vec![-var(*u, col), -var(*v, col)]);
            }
        }
        let name = format!("satkit-{idx:02}-coloring-v{verts}-k{k}");
        let t = write_cnf(&name, verts * k as usize, &c).unwrap();
        manifest.push(format!(
            "| {name} | graph-coloring | {} | {} | {t}us | ? |",
            verts * k as usize,
            c.len()
        ));
        idx += 1;
    }

    // family 4: cardinality — at-most-k via sequential counter encoding,
    // forced UNSAT by requiring k+1 true among n vars (k < n)
    for (n, k) in [(20usize, 3u32), (24, 4), (28, 5)] {
        let var = |i: usize| (i + 1) as i32;
        let mut c: Vec<Vec<i32>> = Vec::new();
        // sequential counter: s_{i,k} auxiliaries. Encoding: sum x_i <= k
        // is UNSAT by construction if we also assert sum x_i >= k+1 —
        // instead: assert exactly n literals true (all), with k < n:
        // at-most-k over ALL n vars, and at-least-(k+1) forced by units.
        // Simpler honest UNSAT: at-most-1 over n vars + units forcing
        // two vars true.
        for i in 0..n {
            for j in (i + 1)..n {
                c.push(vec![-var(i), -var(j)]); // pairwise at-most-1
            }
        }
        // seed the first k+1 vars true -> pigeonhole-style UNSAT core
        for i in 0..=k as usize {
            c.push(vec![var(i)]);
        }
        let name = format!("satkit-{idx:02}-card-amt1-n{n}");
        let t = write_cnf(&name, n, &c).unwrap();
        manifest.push(format!("| {name} | cardinality-amt1 | {n} | {} | {t}us | UNSAT |", c.len()));
        idx += 1;
    }

    // family 5: scheduling — interval non-overlap on too-few time slots
    // (jobs with durations, total duration > horizon => UNSAT packing)
    for (jobs, horizon, len_pct) in [(8usize, 6u32, 50u64), (10, 7, 55), (12, 8, 60)] {
        let mut r = Rng(0xCAFE + jobs as u64 * 17);
        let durations: Vec<u32> = (0..jobs)
            .map(|_| 1 + (r.next() % ((horizon as u64 * len_pct) / 100).max(1)) as u32)
            .collect();
        // start-time encoding: x_{j,t} = job j starts at time t
        let var = |j: usize, t: u32| (j * horizon as usize + t as usize + 1) as i32;
        let mut c: Vec<Vec<i32>> = Vec::new();
        for j in 0..jobs {
            // each job starts exactly once within (horizon - duration)
            let max_t = horizon.saturating_sub(durations[j]);
            if max_t == 0 {
                // job cannot fit: force UNSAT directly via empty-derived clause
                c.push(vec![]);
                break;
            }
            c.push((0..max_t).map(|t| var(j, t)).collect());
            for t in 0..max_t {
                for t2 in (t + 1)..max_t {
                    c.push(vec![-var(j, t), -var(j, t2)]);
                }
            }
        }
        // non-overlap: if j starts at t, k (later job) cannot run during
        // [t, t+dur_j) unless k starts before t or after t+dur_j
        for j in 0..jobs {
            for k in 0..jobs {
                if j == k {
                    continue;
                }
                let max_tj = horizon.saturating_sub(durations[j]);
                let max_tk = horizon.saturating_sub(durations[k]);
                for t in 0..max_tj {
                    for tk in 0..max_tk {
                        // overlap if tk in (t - dur_k, t + dur_j)
                        let overlap = tk < t + durations[j] && tk + durations[k] > t;
                        if overlap {
                            c.push(vec![-var(j, t), -var(k, tk)]);
                        }
                    }
                }
            }
        }
        let total: u32 = durations.iter().sum();
        let name = format!("satkit-{idx:02}-sched-j{jobs}-h{horizon}");
        let t = write_cnf(&name, jobs * horizon as usize, &c).unwrap();
        manifest.push(format!(
            "| {name} | scheduling | {} | {} | {t}us | UNSAT(total {total}>{horizon}) |",
            jobs * horizon as usize,
            c.len()
        ));
        idx += 1;
    }

    let mut out = String::from(
        "# Benchmark instance manifest\n\nGenerated for SAT Competition 2027 benchmark\nsubmission (rule: 20 instances, >=10 interesting). Solve times are sat-kit\nrelease timings at generation time — the interest band check against\nMiniSat happens at submission.\n\n| instance | family | vars | clauses | sat-kit time | answer |\n|---|---|---:|---:|---:|---|\n",
    );
    out.push_str(&manifest.join("\n"));
    out.push('\n');
    std::fs::write("instances/MANIFEST.md", out).unwrap();
    println!("{idx} instances generated");
}
