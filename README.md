# sat-kit

CDCL SAT solver in pure Rust, no dependencies. DIMACS in, model out,
DRAT certificate stream per learned clause (M1 adds a forward checker).

**M0 correctness contract**: agreement with exhaustive brute force on a
150-instance n=8 corpus (m swept across the phase transition), a 400-instance
n=10 sweep, pigeonhole PHP(3,2)=UNSAT / PHP(2,3)=SAT with model validation,
and unit/empty-clause edge cases. Two real bugs the corpus caught are
documented in the source: pivot re-seen inflation in `analyze` (reason
clauses contain the pivot they were the reason for — skip it), and the
learned-unit UNSAT guard that read `value()` before backjumping (a
level-1-refuted decision is not a level-0 contradiction).

Target: SAT Competition 2027 (Main track requires UNSAT certificates —
DRAT emission + a forward checker land in M1).

## Usage

```rust
let mut s = sat_kit::Solver::new(3);
s.add_clause(vec![1, -2]);
s.add_clause(vec![-1, 3]);
assert_eq!(s.solve(), sat_kit::Answer::Sat);
```

## Gates

- **M0** CDCL core + corpus ✓ (this)
- **M1** DRAT emission complete + forward-checker test (learned clauses
  must be RUP against the formula + prior learned set)
- **M2** performance pass: watched-literal pre-allocation, heap VSIDS,
  LBD-based clause DB reduction, Luby restarts — benchmarked against
  known-hard families (pigeonhole scaling, random 3-SAT near threshold)
- **M3** SAT Competition 2027 submission: benchmark instances, system
  description, registration

## M3 benchmark set

`cargo run --release --bin genbench` regenerates `instances/` —
pigeonhole (resolution-hard UNSAT), random 3-SAT near threshold, and
graph coloring, with solve times in `instances/MANIFEST.md`. 20 instances across five families (pigeonhole, random 3-SAT near
threshold, graph coloring, cardinality at-most-1, interval scheduling)
— the competition's benchmark-submission set, regenerate via
`cargo run --release --bin genbench`.
