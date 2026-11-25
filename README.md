# Constructive Lean 4 Kernel and Exact Zero-Float Certificates for Unconditional $L_N[1/3, 105]$ Las Vegas Integer Factorization

**Author:** Lluis Eriksson  
**Protocol:** `L13FACT-COGENTIC-CERT-1.0`  
**Licenses:** MIT (code, Lean 4 proofs, certificates) / CC-BY-4.0 (manuscript & figures)

## Overview

Independent, explicitly scoped, zero-floating-point two-layer verification companion for the discrete lattice, mod-3 Laplace polynomial ensemble, deterministic 3-adic Newton–Hensel algebraic square-root, Dixon congruence-of-squares splitting, and strong-induction mechanisms of the November 25, 2026 Google Research Cogentic companion preprint on unconditional $L_N[1/3, 105]$ Las Vegas integer factorization.

- **Layer 1 (`lean/CogenticL13Factorization.lean`):** 18 standalone constructive Lean 4.35.0 sub-lemmas (`0` `sorry`, `0` custom `axiom`, `0` `Classical.choice`, `0` warnings; `4 none` + `14 [propext, Quot.sound]`).
- **Layer 2 (`src/l13fact_exact.py`, `src/l13fact_certifier.py`):** Pure-stdlib Python `int`/`Fraction` zero-float auditor across 4 modes (`mod_n_lattice_and_lagrange_split_cert`, `mod3_laplace_ladder_and_smooth_cert`, `adic3_newton_hensel_sqrt_cert`, `dixon_character_and_induction_split_cert`).
- **Canonical Atlas & Red-Team Audit:** 16 canonical certificates verified in `0.081–0.609 ms`, `74/74` pytest checks (`68/68` live adversarial forgeries rejected with exact branch regexes), and full SHA-256 integrity manifest.

## Reproducibility (5-Gate Verification)

```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```

All 5 gates run end-to-end: (1) Lean 4.35.0 build & strict axiom whitelist, (2) zero-float AST audit of `src/*.py`, (3) 16/16 canonical certificate verification, (4) 74/74 pytest adversarial suite, and (5) SHA-256 manifest verification.
