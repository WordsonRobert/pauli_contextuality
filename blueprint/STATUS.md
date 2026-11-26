# Status of every result (working notes)

This folder is the working base for the project. It is organised so that every result can be:

1. read as a precise statement,
2. checked step by step from its proof outline, and
3. formalised in Lean 4 + Mathlib.

The paper is in `paper/`.

```
blueprint/STATUS.md           this file: status of every result, navigation
blueprint/                    the mathematics, one file per area; every result has
                              ID, statement, dependencies, numbered proof steps, Lean notes
  00_conventions.md           objects, notation, conventions (read first)
  01_algebra.md               degree = coset distance, cycle-sign lemma, invariance, operational inequality
  02_hardness.md              chain/split lemmas, Pauli construction, closure lemma, induced hardness
  03_transfer.md              transfer, rigidity, stability, profile bound, extremality
  04_certificates.md          odd cycles, uniform covers, packing theorem, three-qubit barrier
  05_three_qubit.md           doily, W(5,2), universal 1/5 bound, rigidity
  06_cones_sections.md        cone theorem, all subspace sections
  07_geometry.md              Q-(7,2) >= 216 (elementary certificate), Q+(9,2) >= 4783, propagated bounds
  08_targets_ABC.md           status of the attack on deg Q-(7,2) = 315 (targets A, B, C)
  09_lean_plan.md             formalisation roadmap: dependency graph, Mathlib pieces, order of attack
  10_asymptotics.md           ROUND-2 TARGETS A/B/C: trace formula, spectral bound, lim rho_N = 1/2,
                              rate Theta(2^{-N/2}), strict jumps, Hoggar/SIC equality, Q+(7,2) = 315
  11_density_games_tightness.md  ROUND 3: density theorem, LCS-game value -> 5/6, dimension-gap law,
                              tightness <=> Pauli-flat states, limits of the spectral method, sampling
  12_literature_positioning.md   literature review + positioning + referee-risk table for Quantum
  13_lean_findings.md         what the Lean formalisation changed, sharpened, or left open
lean/                         Lean 4 + Mathlib formalisation (compiles, no sorry; see lean/README.md)
certificates/                 standalone checker (37 checks + 18 asymptotic checks X1-X17) + witnesses
data/                         machine-readable certificate data (JSON) for Lean / independent checks
code/                         construction, search and certificate-generation scripts (Python, C)
  asym/                       spectral method: bounds, equality cases, products, Haar constants, ascent
paper/                        the arXiv paper (tex + pdf)
```

## Status of results

Legend:
- **P**: complete written proof (pure mathematics).
- **P+C**: proof that also uses finite facts, each checked by a script and suitable for `decide`/`native_decide`.
- **C**: computational result (explicit witness).
- **E**: evidence only (search).
- **Conj**: conjecture.

| ID | Result | Status | Blueprint |
|---|---|---|---|
| ALG-1 | deg(C) = d(e_C, Im H) (coset distance) | P | 01 |
| ALG-2 | Cycle-sign lemma: the parity of a cycle depends only on incidence + commutation | P | 01 |
| ALG-3 | Invariance of the degree under incidence- and ω-preserving bijections | P | 01 |
| ALG-4 | Noncontextual bound m − 2·deg; quantum value m; visibility threshold | P | 01 |
| HARD-1..4 | Chain lemma, ordered triangle split, E3 conversion, odd-path lemma | P | 02 |
| HARD-5 | Well-definedness of the Pauli construction | P+C (T1–T6, C1–C3, C5) | 02 |
| HARD-6 | Closure lemma (no unintended lines) | P+C (T4, T5, C1, C4) | 02 |
| HARD-7 | Induced hardness: deg = OPT + \|b\| | P | 02 |
| HARD-8 | Sub-configurations of one quadric: deg = OPT | P | 02 |
| HARD-9 | NP-completeness, inapproximability, W[1]-hardness (sub-configurations) | P (uses cited hardness results) | 02 |
| HARD-10 | No-deletion proposition; additive constant unavoidable for this gadget type | P | 02 |
| HARD-11 | Tractable class (each point on ≤ 2 lines) | P | 02 |
| TR-1 | Transfer theorem (group version) | P (needs transitivity) | 03 |
| TR-1' | Uniform-cover transfer (no group needed) | P | 03/04 |
| TR-2 | Equality ⇔ rigidity | P | 03 |
| TR-3 | Stability | P | 03 |
| TR-4 | Profile bound + multi-orbit rigidity | P | 03 |
| TR-5 | Extremality of W(2N−1,2), monotone ρ_N, quadric ladder | P (cites Witt) | 03 |
| CERT-1 | Odd-cycle lemma | P | 04 |
| CERT-2 | Packing ≤ transfer; equality for symmetric families | P | 04 |
| CERT-3 | Three-qubit barrier | P | 04 |
| TQ-1 | deg(Peres–Mermin) = 1, deg(doily) = 3, deg W(5,2) = 63 | P+C | 05 |
| TQ-2 | Every ≤ 3-qubit configuration has deg ≤ ⌊lines/5⌋ | P+C | 05 |
| TQ-3 | Rigidity of optimal W(5,2) assignments | P | 05 |
| CONE-1 | deg Cone_t(G') = 4^t deg G' | P | 06 |
| CONE-2/3 | All subspace sections of W and of quadrics | P (cites Witt for normal forms) | 06 |
| GEO-1 | deg Q−(7,2) ≥ 215 | P+C | 07 |
| **GEO-2** | **deg Q−(7,2) ≥ 216** (new; *elementary certificate*: odd cycles + uniform covers only) | P+C | 07 |
| **GEO-3** | **deg Q+(9,2) ≥ 4783** (refutes the conjectured value 4743) | P+C (+ Witt or explicit isometry) | 07 |
| GEO-4 | deg W(7,2) ≥ 1080, deg W(9,2) ≥ 17538, deg Q−(9,2) ≥ 3960 (all superseded by ASY-3/ASY-9) | P+C | 07 |
| GEO-5 | Upper bounds 1575, 315, 6975, 7087, 31479 (explicit assignments) | C | 07 |
| GEO-6 | ρ2 = ρ3 = 1/5 < ρ4 (strict growth) | P+C | 07 |
| ABC-B | All 16 optimal violated sets of Q−(7,2) found lie in ONE orbit; stabiliser order 1008; orbit size 391680 = 1632·240 | E | 08 |
| ABC-C | Integrality cascade saturates at 216 over all subgroup orbits searched | E | 08 |
| **ASY-1** | **Trace formula**: deg X = \|L_X\|/2 − max_g tr(M_g³)/(12·2^N), M_g = Σ g(a)P_a (any induced X) | P | 10 |
| **ASY-2** | **Spectral lower bound** for induced configurations (trace inequality, no eigenvalues) | P | 10 |
| **ASY-3** | **lim ρ_N = 1/2**; 1/2 − ρ_N ≤ 2^{−N/2}; deg W(7,2) ≥ **1451** (was 1080), W(9,2) ≥ **28786** (was 17538) | P (+C for numbers) | 10 |
| **ASY-4** | deg W(5,2) = 63 is spectrally tight; optimal assignments ↔ **Hoggar SICs** (120 violated sets, stabiliser 12096); **deg Q⁺(7,2) = 315** | P+C | 10 |
| **ASY-5** | 1/2 − ρ_N ≥ 0.2679·2^{−N/2} (N ≥ 6) via Haar-random magic states; rate exactly Θ(2^{−N/2}) | P | 10 |
| **ASY-5′** | Measure-and-assign: E[χggg] = κ(2^{N−2}) per line (Kendall τ of Gamma pairs; κ(1)=1/2, κ(2)=23/64); **every** N-qubit configuration has deg ≤ (1−κ)\|L\|/2; lim inf (1/2−ρ_N)2^{N/2} ≥ (2/π)^{3/2} ≈ 0.508 | P (+C numerics) | 10 |
| **DEN-1..3** | deg X ≥ \|L\|/2 − n^{3/2}2^{N_X/2}/12 (intrinsic N_X); dense ⇒ trivially approximable; hard instances have density 2^{−Ω(k)} | P | 11 |
| **TIGHT-1** | deg X = spectral bound ⇔ ∃ pure state Pauli-flat exactly on X; optimal assignments = its sign patterns | P | 11 |
| **TIGHT-2** | W(5,2): 15360 optimal assignments ↔ 15360 Hoggar fiducials (gauge kernel dim 7); Q⁺(7,2) optimum = sign pattern of \|+⟩^{⊗4} − \|0⟩^{⊗4}; new 5-qubit config with deg 480 | P+C | 11 |
| NEG-1 | ASY-2 can never exceed 297 on Q⁻(7,2) or 1488 on W(7,2) (explicit large-eigenvalue sign patterns) | P+C | 11 |
| **GAME-1..4** | LCS game of C: ω_c = 1 − deg/(3\|L\|); W family ω_c ↓ 5/6 (the minimum possible) with perfect N-EPR Pauli strategies; dimension–gap law 1/6 − Θ(2^{−N/2}); noise thresholds | P (+C) | 11 |
| OP-1 | constant-round test: Pr[win ≥ ω_c + ε] ≤ e^{−2Tε²} against adaptive classical strategies | P | 11 |
| CONJ-4 | κ(k)√k ≥ (2/π)^{3/2} for k ≥ 2 (⇒ ρ_{N+2} > ρ_N for all N ≥ 3); verified N ≤ 19 | Conj | 10 |
| **ASY-6** | τ multiplicative under ⊗; #negative lines = (16^N+4^N−2·10^N)/24; product upper bounds | P+C | 10 |
| **ASY-7** | ρ_N monotone, infinitely many strict jumps, ρ_{N+4} > ρ_N (N ≥ 6), ρ₃ < ρ₄ < … < ρ₁₁ | P+C | 10 |
| **ASY-8** | Universal: every N-qubit configuration has deg ≤ (1/2 − 0.2679·2^{−N/2})·\|L\| (N ≥ 6); sparsity criterion | P | 10 |
| ASY-9 | Quadrics: ρ(Q^±) → 1/2; Q⁺(9,2) ≥ **6426** (was 4783), Q⁻(9,2) ≥ **4873** (was 3960) | P+C | 10 |
| CONJ-3 | Magic conjecture: optimal assignments = sign patterns of max-Pauli-L1 states (exact for N = 2..5) | Conj | 10 |
| CONJ-1 | deg Q−(7,2) = 315 (hence W(7,2) = 1575, Q+(9,2) = 6975) | Conj | 07/08 |
| CONJ-2 | Optimal violated sets of Q−(7,2) form one orbit of size 391680, 240 per anisotropic plane | Conj (ABC-B) | 08 |

## Round-2 headline (blueprint/10)

ρ_N = deg W(2N−1,2)/|L_N| → 1/2, with 0.2679·2^{−N/2} ≤ 1/2 − ρ_N ≤ 2^{−N/2} for N ≥ 6 (asymptotic constant
improved to ≥ (2/π)^{3/2} ≈ 0.508 by ASY-5′). The proof is a trace
identity (deg = |L|/2 − max_g tr(M_g³)/(12d)) plus one positive-semidefinite trace inequality. Equality holds exactly
for N = 3, where the optimal assignments are the Hoggar SIC fiducials. Target C (Lean route avoiding measure theory):
ASY-1 → ASY-2 → ASY-3, and Target A (infinitely many jumps): + ASY-6 Cor. 1 + TR-5 (`Spectral.lean`).

## Most formalisation-friendly route (recommended first Lean target)

**GEO-2 (deg Q−(7,2) ≥ 216)** needs only two short lemmas, CERT-1 (odd cycle) and TR-1' (uniform cover), plus a
finite computation that Lean can check by reflection (`native_decide`). It uses no Witt theorem, no group theory and
no Pauli operator algebra beyond the sign of each line. See `blueprint/07_geometry.md` and
`blueprint/09_lean_plan.md`.

## Reproducing

```
cd certificates && python3 certify.py        # 37 checks + X1-X17, ~1 min, numpy only
cd certificates && python3 certify_asym.py   # only the asymptotic checks X1-X17 (~5 s)
cd code && python3 cert216_full.py           # full elementary chain for 216, all 136 choices of a (~minutes)
```
