# 07. Finite geometries: lower bounds, upper bounds, propagation

Fixed model: Q⁻(7,2) = singular points of q⁻(x|z) = x·z + x₁ + z₁ on 4 qubits (119 points, 1071 lines; signs computed
from Pauli products, see data/cert216_Qm7.json).

## GEO-1 deg Q⁻(7,2) ≥ 215 — `qm7_ge_215`
**Elementary proof (no groups).**
1. All 45696 doilies of Q⁻(7,2) are listed: one for each non-singular c and each non-degenerate plane ⟨u,v⟩ ⊆ c^⊥
   (the doily is the set of lines inside {w : ω(w,c) = ω(w,u) = ω(w,v) = 0}; duplicates removed).
2. Every line lies in exactly 640 doilies (computed).
3. Every doily has degree ≥ 3 by CERT-1b: it contains 10 odd grids covering each of its lines 4 times (computed for
   all 45696).
4. TR-1': deg ≥ ⌈45696·3/640⌉ = ⌈214.2⌉ = 215.

## GEO-2 deg Q⁻(7,2) ≥ 216 — `qm7_ge_216` (new)
**Elementary proof (no groups, no Witt).** Verified for all choices of a by code/cert216_full.py.
1. For a non-singular a (q⁻(a) = 1), let O_a be the configuration of the lines of Q⁻(7,2) not contained in a^⊥.
   |O_a| = 756.
2. Exactly 4032 of the 45696 doilies lie inside O_a, and they cover every line of O_a exactly 80 times (computed).
3. TR-1' with GEO-1 step 3: deg O_a ≥ ⌈4032·3/80⌉ = ⌈151.2⌉ = 152.
4. The 136 configurations O_a (one per non-singular a) cover every line of Q⁻(7,2) exactly 96 times. A line lies in
   O_a iff it is not inside a^⊥ (computed; it also follows from counting).
5. TR-1': deg Q⁻(7,2) ≥ ⌈136·152/96⌉ = ⌈215.33⌉ = 216.

**Group version (as in the paper).** Steps 2 and 4 follow from transitivity: Stab(a) acts transitively on O_a (Witt,
or computed via reflections), and O⁻(8,2) acts transitively on L(Q⁻(7,2)).

**Why it works.** Rounding happens twice, first inside O_a (151.2 → 152) and then globally. O_a is not 3-qubit
realisable, so this escapes CERT-3.

## GEO-3 deg Q⁺(9,2) ≥ 4783 (refutes 4743 = |L|/5) — `qp9_ge_4783`
1. The elliptic sections of Q⁺(9,2) are E^⊥ ∩ Q⁺ for E an anisotropic plane of (F^{10}, q⁺). There are 19840 of them;
   each has 1071 lines and is isometric to Q⁻(7,2). Every line of Q⁺(9,2) lies in exactly 896 of them (computed).
2. Each section has degree ≥ 216. Either (i) by ALG-3 with an explicit linear isometry to the model of GEO-2, or
   (ii) by re-running the GEO-2 certificate inside the section, which avoids ALG-3 and is purely computational.
3. TR-1': deg ≥ ⌈19840·216/896⌉ = ⌈4782.86⌉ = 4783 > 4743.
**Explicit section** used in the paper: E = ⟨Y₅, Y₄X₅⟩ (anisotropic: q⁺ = 1 on all 3 non-zero vectors, ω = 1).

## GEO-4 propagated bounds — `bounds_propagated`
- W(7,2) ≥ 1080. Family: the 120 elliptic quadrics of W(7,2) (quadratic forms x·z + c·(x|z) of minus type). Each line
  lies in 24 of them, so ⌈120·216/24⌉ = 1080.
- W(9,2) ≥ 17538. Family: the hyperbolic quadrics of W(9,2) (each ≅ Q⁺(9,2), degree ≥ 4783), uniform by symmetry.
  ⌈86955·4783/23715⌉ = ⌈17537.7⌉ = 17538.
- Q⁻(9,2) ≥ 3960. Family: the elliptic 8-dimensional sections of minus type, each ≅ Q⁻(7,2). 19635·216/1071 = 3960.
**Status.** The arithmetic is certified (A4). The uniform coverage of each family follows from the symmetry groups
(Witt); for a fully group-free proof, compute the families and their coverage as in GEO-2 (sizes: 120 quadrics;
the families for 5 qubits are larger but feasible).

## GEO-5 upper bounds (explicit assignments) — `ub_witnesses`
W(7,2) ≤ 1575, Q⁻(7,2) ≤ 315, Q⁺(9,2) ≤ 6975, Q⁻(9,2) ≤ 7087, W(9,2) ≤ 31479. The witness files are in certificates/.
Each check is a single `native_decide` evaluation once the configuration is computed.

## GEO-6 strict growth — `rho_strict`
ρ₂ = ρ₃ = 1/5 (TQ-1) < 1080/5355 ≤ ρ₄ ≤ 1575/5355 = 5/17, and ρ₄ ≤ ρ₅ ≤ 31479/86955.

## CONJ-1
deg Q⁻(7,2) = 315. Then W(7,2) = 1575 and Q⁺(9,2) = 6975 (the same transfers, with matching upper bounds); all three
have ratio 5/17.
