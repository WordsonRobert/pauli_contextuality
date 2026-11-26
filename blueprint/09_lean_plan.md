# 09. Formalisation plan (Lean 4 + Mathlib)

## Principle: certificates by reflection
Every finite fact is computed by a Lean function over explicit data. One theorem states that the checker returns
`true`, proved by `native_decide` (or `decide` when small). A soundness lemma, proved by hand, turns `true` into the
mathematical statement. Nothing in the main chain needs Witt's theorem or matrices.

## Dependency graph (formalise in this order)

```
L0  Defs: F = ZMod 2, V n, omega, ycount, PauliGrp law                [ALG-0]
L1  Config (abstract): points α, lines : Finset (Finset α), sign       [00]
L2  violated, deg := min over assignments (Finset.inf')                [ALG-1]
L3  odd_cycle_forces_violation                                          [CERT-1]
L4  uniform_cover : family covering each line c times, each deg ≥ d    [TR-1']
        ⇒ deg ≥ ⌈|F| d / c⌉
L5  checker for "grid is an odd cycle" and "doily has 10 odd grids,    [CERT-1b]
        coverage 4" ⇒ deg doily ≥ 3   (L3 + L4)
L6  Q⁻(7,2) data computed in Lean (points = vectors with q = 0;        [07]
        lines = commuting zero-sum triples; signs via L0 formula)
L7  GEO-1 (215) and GEO-2 (216) by L4 + checkers (native_decide)       [07]  ← FIRST BIG MILESTONE
L8  upper-bound witnesses (native_decide)                              [GEO-5]
L9  ALG-0 group law ⇒ ALG-2 cycle-sign lemma ⇒ ALG-3 invariance        [01]  (harder, pure maths)
L10 GEO-3 (4783): either ALG-3 + explicit isometries, or recompute L7   [07]
        inside each of the 19840 sections (heavy computation)
L11 transfer / rigidity / stability / profile (pure maths over L4)     [03]
L12 cone theorem                                                        [06]
L13 hardness value identities (HARD-1..9), closure lemma               [02]  (largest)

-- round 2: spectral method (lean/PauliContextuality/Spectral.lean) --
L14 Pauli matrices as Kronecker products; pauli_mul, trace_pauli,       [10 ASY-1]
        trace_pauli_mul, hermitian; pauli_completeness (induction on N)
L15 trace_formula (Finset algebra)                                       [ASY-1]
L16 rayleigh (PosSemidef ΛI − M) + cubic_trace_bound (trace inequality)  [ASY-2]
L17 W_lower ⇒ ρ_N ≥ 1/2 − 2^{−N/2}; with deg ≤ |L|/2 ⇒ ρ_N → 1/2         [ASY-3]  ← TARGET C
L18 negative_lines (native_decide for N ≤ 5, or trace_formula g ≡ 1)     [ASY-6]
        + TR-5 monotone + infinitely_many_strict_jumps (already proved)  [ASY-7]  ← TARGET A
L19 (optional, measure theory) Haar Beta computation                     [ASY-5]  ← exact rate
```

## Mathlib pieces (round 2 additions)
- `Matrix.kroneckerMap`, `Matrix.reindex`, `finProdFinEquiv`, `Matrix.trace_kronecker`, `Matrix.IsHermitian`,
  `Matrix.PosSemidef`, `Matrix.PosSemidef.conjTranspose_mul_mul_same`, `Matrix.PosSemidef.trace_nonneg`,
  `Finset.inner_mul_le_norm_mul_norm` / `Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy–Schwarz), `Real.sqrt`,
  `Filter.Tendsto`, `tendsto_nhds_unique`. No spectral theorem is needed.

## Mathlib pieces
- `ZMod 2`, `Fin n → ZMod 2`, `Finset.sum`, `Finset.card`, `Finset.inf'`, `Finset.sum_comm` (the double counting in L4
  is `Finset.sum_comm` plus `Finset.card_eq_sum_ones`), `Nat.ceil` / `Int.ceil`, `Finset.filter`.
- Linear algebra (ALG-1b, CONE-1): `Submodule`, `LinearMap`, `Module.finrank`, `Basis.extend`.
- Group actions (TR-1 group version): `MulAction`, `MulAction.orbit`, `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`.
  Not needed if you use L4.
- Not in Mathlib (avoid): Witt's extension theorem, classification of quadratic forms over F₂ in char 2, polar spaces.

## Computational sizes (for `native_decide`)
- Q⁻(7,2): 119 points, 1071 lines. All 45696 doilies with 10 grids each: about 4.6·10⁵ grid checks. Coverage counts:
  45696·15 increments. Per a: filter the doilies inside O_a (4032) and count coverage (80). 136 values of a. Overall
  about 10⁸ elementary operations: fine for compiled `native_decide`.
- Suggested data layout: points as `Fin 256` (bit-packed vectors), lines as `Array (Fin 119 × Fin 119 × Fin 119)`,
  doilies generated in Lean by the c,u,v recipe of GEO-1 (no large literal data needed).
- Upper-bound witnesses: 0/1 arrays of length |P|; check that #violated = claimed.

## Trust
`native_decide` trusts the Lean compiler (an extra axiom, `Lean.ofReduceBool`). For a kernel-only proof, use
`decide` on smaller sub-checks, or proof-producing checkers (much slower). Record which theorems use
`native_decide`.

## Suggested files (see lean/)
- `PauliContextuality/Basic.lean`: L0
- `PauliContextuality/Config.lean`: L1, L2
- `PauliContextuality/Cover.lean`: L3, L4, L11 statements
- `PauliContextuality/Qminus.lean`: L5–L7 (data generation + checkers + main theorem `qm7_ge_216`)
- `PauliContextuality/CycleSign.lean`: L9
- `PauliContextuality/Cone.lean`: L12
- `PauliContextuality/Hardness.lean`: L13
