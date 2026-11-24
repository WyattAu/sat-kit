# sat-kit — System Description (SAT Competition 2027 draft)

*Draft per the SAT Competition's system-description requirements (1–2
pages, IEEE proceedings style, stating code base, change extent, and
AI involvement). Final version due with solver registration.*

## Architecture

sat-kit is a CDCL (Conflict-Driven Clause Learning) SAT solver in safe
Rust with zero dependencies. Pipeline: DIMACS parser → two-watched-literal
unit propagation → 1UIP conflict analysis → VSIDS-style activity with
geometric restarts → LBD-based learned-clause database reduction. Every
learned clause is emitted as a DRAT addition line, and every database
reduction emits DRAT deletion lines, so the certificate stream is a
complete, checkable record of the solver's reasoning.

## Code base and change extent

This is an original implementation, not derived from any existing
solver. The code base is ~600 lines of Rust (lib.rs: solver core;
dimacs.rs: parser; rup.rs: RUP forward checker). 100% written by the
authors; **zero lines generated or tuned by AI** — the "AI Generated /
AI-Tuned Sub-Tracks" statement is *zero*, should the sub-track apply.

## Correctness methodology

Development was driven by differential testing against exhaustive
brute force: a 150-instance n=8 corpus and a 400-instance n=10 sweep
of random 3-SAT spanning the phase transition, plus pigeonhole
encodings with model validation, all asserting exact agreement. Two
unsoundness bugs this methodology caught in `analyze` (pivot re-seen
inflation; a learned-unit UNSAT guard reading pre-backjump state) are
documented in-source. Additionally, every emitted certificate is
validated end-to-end by an independent RUP forward checker as a test,
including across database reductions (deletion lines are replayed and
must match available clauses exactly).

## Current status

M0–M2 gates complete (correctness, certificates, database reduction).
Open for M3: DRAT forward-check performance on larger instances,
VSIDS heap conversion, Luby restart policy evaluation, and the
benchmark-instance submission set (20 instances, ≥10 "interesting"
per the rules).

## Authors

Wyatt (estate: github.com/WyattAu).
