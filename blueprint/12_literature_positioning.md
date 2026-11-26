# 12. Literature review and positioning (for a submission to *Quantum*)

Scope: everything a referee in contextuality, nonlocal games, magic, or finite geometry is likely to raise. For each
work this file gives:

- **what it does**,
- **its overlap with us**, and
- **our differentiator**.

Items marked ⚠ are claims we must phrase carefully or verify before submission.

Searches were done in Nov 2026. Re-run them just before submission, because this area is moving fast: three of the
most relevant papers appeared in Dec 2025 – Oct 2026.

---

## A. The "contextuality degree" programme (closest prior art on the *object*)

| Work | What it does | Overlap | Our differentiator |
|---|---|---|---|
| de Boutray, Holweck, Giorgetti, Masson, Saniga, *J. Phys. A* 55, 475301 (2022) | Defines the contextuality degree of line-configurations in W(2N−1,2) and computes it by SAT for quadrics, N ≤ 3–5 | Same invariant (deg = min violated contexts) | They compute; we prove structural theorems (exact formula, bounds for all N, limit). |
| Muller, Saniga, Giorgetti, de Boutray, Holweck, *Math. Struct. Comp. Sci.* 34, 322 (2024), [arXiv:2305.10225](https://arxiv.org/abs/2305.10225) | C code and SAT; improved bounds for rank-4 quadrics; non-contextuality of higher-dimensional contexts; deg W(5,2) = 63 corrected | Small exact values (3, 63, 21, 9) | Our proof of 63 is conceptual (spectral and tight), not exhaustive. We identify optimal W(5,2) assignments with Hoggar SICs. |
| Muller, Saniga, Giorgetti, Holweck, Kelleher, [arXiv:2407.02928](https://arxiv.org/abs/2407.02928) (2024) | Heuristic upper bounds for N = 4–6, plus lower bounds; Table 1: W(7,2) ∈ [1071, 1575], W(9,2) ∈ [17391, 31479], W(11,2) ∈ [279279, 553140]. Quadrics: Q⁺(7,2) ≤ 315 (they "believe" = 315), Q⁻(7,2) ≤ 315, Q⁺(9,2) ≤ 6975, Q⁻(9,2) ≤ 7087, Q⁺(11,2) ≤ 132391, Q⁻(11,2) ≤ 131700 | **All our upper bounds for N ≤ 6 coincide with theirs.** Our negative-line formula reproduces their counts 1908 / 35400 / 615888 | **Lower bounds:** 1451 (vs 1071), 28786 (vs 17391), 527621 (vs 279279), Q⁺(9,2) ≥ 6426, Q⁻(9,2) ≥ 4873, Q⁻(7,2) ≥ 216. **Proof** of their belief Q⁺(7,2) = 315. Closed formula for the negative-line counts. ⚠ Say explicitly that the upper bounds are theirs (our witnesses reproduce them independently). |
| Saniga, Holweck, Kelleher, Muller, Giorgetti, de Boutray, "Hexagons govern three-qubit contextuality", *Quantum* 9, 1601 (2025), [arXiv:2312.07738](https://arxiv.org/abs/2312.07738) | The unsatisfied sets of three-qubit configurations match line sets of classically embedded split Cayley hexagons | Same N = 3 optimal sets (the 63 violated lines) | We explain *why* N = 3 is exceptional: spectral tightness ⇔ the Hoggar SIC exists (TIGHT-1/2). There are 120 optimal violated sets, in one Sp(6,2)-orbit with stabiliser G₂(2) of order 12096. ⚠ Cross-check that our 120 sets are exactly their hexagon-type sets (likely: G₂(2) is the hexagon's automorphism group). Doing so would be a nice bridge. |
| Holweck–Saniga, *IJQI* 15 (2017); Holweck–de Boutray–Saniga, *Sci. Rep.* 12, 8915 (2022) | Small-observable contextuality; the hexagon is contextuality-sensitive | Background | Background |

**Positioning sentence.** "Prior work computed the contextuality degree for N ≤ 3 exactly and gave heuristic upper
bounds for N ≤ 6. We give the first proof techniques that work for all N: an exact trace formula, matching spectral
bounds, the limit 1/2 with rate Θ(2^{−N/2}), and machine-checked certificates."

---

## B. Magic sets, Kochen–Specker parity proofs, algebraic and topological approaches

| Work | What it does | Relation |
|---|---|---|
| Peres (1990), Mermin (1990, 1993); Kernaghan–Peres (1995) | Magic square, pentagram, parity proofs | The prototypes. Our degree generalises "odd number of negative contexts". |
| Arkhipov, [arXiv:1209.3819](https://arxiv.org/abs/1209.3819) (2012) | Magic sets with every observable in 2 contexts reduce to the square or pentagram (planarity) | Our HARD-12 (≤ 2 lines per point ⇒ deg = #closed odd components) is the *quantitative* counterpart in the same regime. |
| Paddock, Russo, Silverthorne, Slofstra, *Alg. Comb.* 6 (2023), [arXiv:2205.04645](https://arxiv.org/abs/2205.04645) | Graph-minor characterisations for graph-incidence LCS games | Same regime as HARD-12; they work at the group level, we work at the value/degree level. |
| Trandafir, Lisoněk, Cabello, *PRL* 129, 200401 (2022), [arXiv:2202.13141](https://arxiv.org/abs/2202.13141) | Irreducible magic sets for n = 3–6, with tight noncontextuality-inequality bounds | Their tight NC bounds are degrees of specific small sets. ⚠ Cite as computing deg for particular configurations, and contrast with our asymptotic and structural theory. |
| Okay, Roberts, Bartlett, Raussendorf, *QIC* (2017), [arXiv:1701.01888](https://arxiv.org/abs/1701.01888); Okay–Raussendorf, *Quantum* 4, 217 (2020) | Cohomological / homotopical obstructions to noncontextual value assignments | Our cycle-sign lemma (ALG-2) is the F₂-cocycle/coboundary picture. Their obstruction is "deg > 0"; ours is the quantitative distance to coboundaries (ALG-1). |
| Abramsky, Barbosa, Kishida, Lal, Mansfield, *CSL* (2015) | All-vs-nothing proofs ⇔ cohomological obstructions | Same: we quantify the obstruction. |
| **Frembs, "Contextuality in the n-qubit Pauli group", [arXiv:2608.11993](https://arxiv.org/abs/2608.11993) (Aug 2026)** | Noncontextual *properties* (Boolean frame functions) on the Pauli group and the symplectic theory; none for n ≥ 3; uses W(2n−1,2), ovoids and Fourier analysis | Very recent, same ambient geometry. Qualitative (existence of frame functions); no degree, no asymptotics. | Complementary: binary vs quantitative. His frame functions of "linear or quadratic-refinement form" appear to match our gauge group (TIGHT-2: kernel = linear ∪ quadratic forms). ⚠ Verify the exact correspondence before claiming it. |
| Kirby–Love, *PRL* 123, 200501 (2019); *PRA* 102 (2020) | Contextuality of Pauli sets (VQE); a set is contextual iff it contains one of 2 four-observable patterns; the noncontextual Hamiltonian problem is NP-complete | Their notion is state-dependent and "contextual or not" (poly time). | Our hardness concerns the *degree* of state-independent configurations: deciding contextuality is easy (rank/cycle check), computing how contextual is hard. This contrast is worth one sentence. |

---

## C. Quantitative contextuality and noise robustness

| Work | Relation |
|---|---|
| Budroni, Cabello, Gühne, Kleinmann, Larsson, "Kochen–Specker contextuality", *Rev. Mod. Phys.* 94, 045007 (2022), [arXiv:2102.13036](https://arxiv.org/abs/2102.13036) | Standard reference: KS inequalities, the compatibility loophole, memory costs. Our GAME-4 / OP-1 discussion of single-system versus nonlocal tests should follow its terminology. |
| Abramsky, Barbosa, Mansfield, *PRL* 119, 050504 (2017), contextual fraction | For an ideal state-independent parity model the contextual fraction is 1 (strong contextuality). Our degree is a *finer* invariant that determines the optimal NC inequality value m − 2deg (ALG-4) and the white-noise threshold 1 − 2ρ. |
| Kleinmann, Gühne, Portillo, Larsson, Cabello, *NJP* 13 (2011), memory cost | The loophole for sequential single-system tests (OP-1). |
| "A computational test of quantum contextuality, and even simpler proofs of quantumness", [arXiv:2405.06787](https://arxiv.org/abs/2405.06787) (2024) ⚠ check the author list | Compiling contextuality games into single-device tests under computational assumptions. Our W-games are natural candidates. Mention as an outlook. |

---

## D. Nonlocal games: linear-system and stabiliser games (closest prior art on the *operational* side)

| Work | What it does | Relation / our differentiator |
|---|---|---|
| Cleve–Mittal, *ICALP* (2014); Cleve–Liu–Slofstra, *JMP* 58 (2017); Slofstra (2019) | LCS games; perfect strategies ↔ operator solutions | Our configurations are LCS games with Pauli operator solutions, and deg ↔ classical value (GAME-1). |
| Håstad, *JACM* 48 (2001) | 3-LIN: 1−ε vs 1/2+ε hardness; LCS games have ω_c ≥ 5/6 | Source of the 5/6 floor (GAME-2) and of our hardness reductions. |
| Taller–Vidick, [arXiv:2507.22444](https://arxiv.org/abs/2507.22444) (2025) | Approximating the *quantum* value of LCS games is RE-hard; states explicitly that classical values of 3-variable LCS games are ≥ 5/6 | Their hard instances have quantum soundness 35/36. They are not perfect-quantum families near 5/6. ⚠ **Novelty claim to verify carefully:** we found no prior explicit family of LCS games with perfect quantum strategies whose classical value → 5/6. Phrase it as "to our knowledge". |
| Bene Watts–Helton, *Commun. Math. Phys.* (2023), [arXiv:2010.16290](https://arxiv.org/abs/2010.16290) | Perfect **3-player** 3XOR games: decidable in poly time; GHZ strategies suffice; classical value bounded away from 1/2 | Different model (3 players, XOR). Avoid confusing "3XOR games" with our 2-player 3-variable LCS games. |
| Lau, "Beyond the magic square game", [arXiv:2603.20748](https://arxiv.org/abs/2603.20748) (2026) | Largest gap with two Bell states: 4/35 (vs 1/9 for the magic square) | Fixed-dimension gap records. Our GAME-3 gives the asymptotic dimension–gap law 1/6 − Θ(2^{−N/2}) for N-qubit Pauli LCS games (equation/variable format). ⚠ Compare formats: row–column versus equation–variable values differ (the magic square has 8/9 versus 17/18). |
| **Zhao, Liew, Ho, Liu, Bulchandani, "Scalable tests of quantum contextuality from stabilizer-testing nonlocal games", [arXiv:2512.16654](https://arxiv.org/abs/2512.16654) (Dec 2025)** | n-player stabiliser-testing games; coding bound p_cl ≤ 7/8 (Reed–Muller); GHZ, toric code (≈3/4), cyclic cluster (p_cl − 1/2 = O(0.885ⁿ)); transfer matrices | **Closest operational prior art.** Differences: (i) **n-player games built from a stabiliser state** versus our **2-player LCS games from arbitrary Pauli configurations**; (ii) their classical value is a *code distance of Im H to the parity vector*, the same form as our ALG-1 (deg = d(e, Im H)). ⚠ Acknowledge this shared coset-distance viewpoint explicitly. (iii) They bound specific families by coding theory; we have an exact trace formula, spectral bounds and tightness via SIC/flat states; (iv) no finite-geometry or polar-space analysis there. |
| Hart, Stephen, Wickenden, Nandkishore, [arXiv:2512.16886](https://arxiv.org/abs/2512.16886) (Dec 2025) | Many-body contextuality and self-testing via games | Background for the "scalable tests" narrative. |
| Brassard–Broadbent–Tapp, quant-ph/0306042 and quant-ph/0408052 | Mermin's parity game: p_cl = 1/2 + 2^{−⌈n/2⌉} | **Same exponent 2^{−n/2}** as our deficit 1/2 − ρ_N = Θ(2^{−N/2}). A natural analogy; mention it. ⚠ Do not overclaim a connection. |
| Ciardo, "On the quantum chromatic gap", [arXiv:2503.23207](https://arxiv.org/abs/2503.23207) (2025) | Parallel-repeated magic-square 3XOR systems as a route to large gaps | Our W family is a *non-repetition* route to the extremal 5/6 value. |
| "An explicit counterexample to Tsirelson's problem via a linear system game", [arXiv:2610.10248](https://arxiv.org/abs/2610.10248) (Oct 2026) | Huge 3-variable LCS; exact classical value **formalised in Lean 4/Mathlib** | Precedent for Lean in this area; cite in the formalisation section. |

---

## E. Magic (nonstabiliserness), SICs and flat states (prior art for TIGHT and CONJ-3)

| Work | What it does | Relation |
|---|---|---|
| Leone, Oliviero, Hamma, "Stabilizer Rényi entropy", *PRL* 128, 050402 (2022), [arXiv:2106.12587](https://arxiv.org/abs/2106.12587) | M_α; M_{1/2} = 2 log D with stabiliser norm D = d^{−1}Σ\|⟨P⟩\|; upper bounds | Our Λ* = max Σ_{a≠0}\|⟨P_a⟩\| = d·D_max − 1. **ASY-2/NEG-1 tie the contextuality degree to the maximal stabiliser norm (α = 1/2).** |
| Cuffaro–Fuchs, "Quantum states with maximal magic", [arXiv:2412.21083](https://arxiv.org/abs/2412.21083) (2024) | WH-covariant SICs uniquely maximise stabiliser entropies (α ≥ 2) | TIGHT-1: spectral tightness ⇔ Pauli-flat states, i.e. SICs when X = V*. Our result is the α = 1/2, *contextuality* incarnation, with a combinatorial consequence (an exact degree). |
| "Maximal magic for two-qubit states", [arXiv:2502.17550](https://arxiv.org/abs/2502.17550) (2025) | Conjecture: WH-MUB states are maximal-magic for n ≠ 1, 3 | Related to CONJ-3 (optimal assignments = sign patterns of max-L1 states). |
| "Extremal magic states from symmetric lattices", [arXiv:2506.11725](https://arxiv.org/abs/2506.11725) (2025) | Classifies three-qubit maximal magic states: **15,360** | **Equals our count of optimal W(5,2) assignments (TIGHT-2: 120 × 128).** Strong independent consistency check. ⚠ Cite. |
| **Cieśliński, "Pauli flat quantum states mimicking maximal magic", [arXiv:2610.07172](https://arxiv.org/abs/2610.07172) (Oct 2026)** | Pauli-flat states; pure ones exist only for N = 1, 3; relaxed pure states with 135 (N = 4) and 496 (N = 5) equal nonzero expectations, γ = 1/3 and 1/4 | **Exactly the states of our TIGHT-1.** Their N = 4 state (−3,1,…,1)/√24 is our closed form \|+⟩^{⊗4} − \|0⟩^{⊗4}, the Q⁺(7,2) optimum. Their N = 5 support type is our X₄₉₆ with deg 480. **They do not mention contextuality.** Our theorem gives these states a precise meaning: flat on X ⇔ deg X attains the spectral bound, and their sign patterns are the optimal noncontextual assignments. ⚠ Cite prominently. |
| Godsil–Roy, *Eur. J. Comb.* 30 (2009); Hoggar (1998); Zhu (2010, 2015) | Pauli-group-covariant SICs exist only for n = 1, 3 (Hoggar lines); their symmetry groups | Used in the TIGHT corollary (W is never tight for N ≥ 4) and for the G₂(2) stabiliser. |
| Howard, Wallman, Veitch, Emerson, *Nature* 510, 351 (2014); Raussendorf (2013); Bermejo-Vega et al., *PRL* 119 (2017) | Contextuality as a resource for magic-state / MBQC computation | Big-picture motivation: here the *extremal* noncontextual strategies are literally sign patterns of maximally magic states. |

---

## F. Complexity background

- Håstad (2001): MAX-E3-LIN, 2 − δ, including bounded occurrence.
- Downey–Fellows, Bonnet–Egri–Lin–Marx: W[1].
- Kirby–Love: NP-completeness of noncontextual Hamiltonians.

Our hardness of deg (HARD-*) combined with DEN-3 places all hard instances at exponentially small spectral density.
The dense regime is trivially approximable (DEN-2).

---

## G. What we can claim as new (draft "Contributions" paragraph)

1. **An exact operator-moment identity.** For every induced Pauli configuration, deg = |L|/2 − max_g tr(M_g³)/(12d).
   Plus a trace-inequality lower bound needing no eigenvalue theory (ASY-1/2), and its density form (DEN-1).
2. **Asymptotics.** lim ρ_N = 1/2 with 0.508 ≲ (1/2 − ρ_N)2^{N/2} ≤ 1. Infinitely many strict jumps; strict growth for
   3 ≤ N ≤ 11. New lower bounds for every N ≥ 4, improving all previously published lower bounds (Section A table).
3. **Tightness ⇔ flat magic states.** Exact degrees deg W(5,2) = 63, deg Q⁺(7,2) = 315 (a conjecture of Muller et
   al.) and a new 5-qubit configuration with deg 480. Optimal W(5,2) assignments ↔ the 15360 Hoggar SIC fiducials.
4. **Operational consequence.** A family of linear-system games with perfect N-EPR-pair Pauli strategies and
   classical value → 5/6, the minimum possible. A dimension–gap law 1/6 − Θ(2^{−N/2}), and constant-round tests.
5. **Hardness at low density, easiness at high density** (DEN-2/3, HARD-*).
6. **Verification.** 550 Lean declarations (core theorems kernel-checked; finite certificates via `native_decide`)
   and an independent Python checker (38 + 18 checks).

## H. Open risks a referee may raise (and our answers)

| Risk | Answer / action |
|---|---|
| "The trace identity is elementary." | Agree it is short. Its value is in the consequences (limit, tightness ⇔ flat states, the game law). Present it as a bridge, not as hard analysis. ⚠ Search the Pauli-Hamiltonian literature once more for tr(H³) commuting-triple identities (e.g. frustration-graph moments) and cite any precedent. |
| "Upper bounds are known (Muller et al.)." | Yes: say so. Ours are independent reproductions plus explicit tensor-product constructions; the new content is the lower bounds and exact values. |
| "Is the 5/6 game family new?" | ⚠ Verify with LCS-game experts (Slofstra, Paddock, Vidick groups). Fallback: "the W family realises the 5/6 floor with perfect Pauli strategies; we determine its rate". |
| "Hardness uses an abstract gadget in Lean." | State it plainly: HARD-5/6 (the Pauli realisation and closure lemma) is proved on paper and checked by script, not yet in Lean. |
| "native_decide." | List every theorem that uses it (`lean/THEOREMS.md` ⚙). Provide kernel-checked `decide` versions for the small ones. |
| AI assistance | *Quantum* requires disclosing the scope of AI use in the author-contribution statement (proof search, code, Lean, text, literature). |
