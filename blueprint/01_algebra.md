# 01. Algebraic foundation

## ALG-0 (Pauli group law) — Lean: `PauliGrp`
**Statement.** On G_n = ZMod 4 × V n define (k₁,p)(k₂,q) = (k₁+k₂+2⟦z_p·x_q⟧, p+q). Then:
1. G_n is a group with identity (0,0); the inverse of (k,p) is (−k − 2⟦z_p·x_p⟧, p).
2. (k,0) is central.
3. (0,p)(0,q) = (2ω(p,q), 0)·(0,q)(0,p).
4. With P(p) = (⟦y(p)⟧, p): P(p)·P(p) = (0,0).

**Proof steps.**
1. Associativity: both sides equal (k₁+k₂+k₃ + 2⟦z_p·x_q⟧ + 2⟦(z_p+z_q)·x_r⟧, p+q+r). The required identity
   2⟦(z_p+z_q)·x_r⟧ = 2⟦z_p·x_r⟧ + 2⟦z_q·x_r⟧ in ZMod 4 holds because 2·(u mod 2) = 2u in ZMod 4. Lemma:
   `(2 : ZMod 4) * ((a : ZMod 2).val : ZMod 4) = 2 * (a.val)` together with `2 * 2 = 0`. Prove it coordinatewise
   by `decide` on ZMod 2 × ZMod 2 × ZMod 2.
2. Identity and inverse: direct computation.
3. Centrality: (k,0)(k',q) = (k+k', q) = (k',q)(k,0), since z_0 = 0 and x_0 = 0.
4. Commutation: (0,p)(0,q) = (2⟦z_p·x_q⟧, p+q) and (0,q)(0,p) = (2⟦z_q·x_p⟧, p+q). These differ by
   2(⟦z_p·x_q⟧ − ⟦z_q·x_p⟧) = 2⟦z_p·x_q + z_q·x_p⟧ = 2ω(p,q).
5. Square: P(p)P(p) = (2y(p) + 2⟦z_p·x_p⟧, 0) = (4y(p), 0) = (0,0), because ⟦z_p·x_p⟧ = y(p).

## ALG-1 (degree is a coset distance) — Lean: `deg_eq_coset_dist`
**Statement.** deg(C) = min_{s ∈ F^P} |Hs + e| = d(e, Im H), and it depends only on the coset e + Im H.
**Proof steps.**
1. For every s, the indicator of the violated lines of s is Hs + e. This is immediate from the definitions.
2. Hence deg = min_s wt(Hs + e) = min_{c ∈ Im H} wt(e + c).
3. If e' − e ∈ Im H, the two minima range over the same set.
**Lean.** Define `deg C := Finset.univ.inf' _ (fun s => (violated C s).card)` over `Fin |P| → ZMod 2`. A finite
minimum always exists.

## ALG-1b (duality) — Lean: `coset_determined_by_cycles`
**Statement.** (Im H)^⊥ = ker Hᵀ. Hence e + Im H = e' + Im H iff y·e = y·e' for every cycle y.
**Proof steps.** This is standard linear algebra over a field (Mathlib: `LinearMap.range`, `Submodule.dualAnnihilator`,
`Matrix.mulVec`, or `ker_transpose` / orthogonal complement for the dot product on F^m). The double orthogonal
(U^⊥)^⊥ = U holds for finite-dimensional spaces with the standard dot product: it is non-degenerate,
although not anisotropic over F₂. This identity is all that is needed.

## ALG-2 (cycle-sign lemma) — Lean: `cycle_parity_eq_inversions`
**Statement.** Let y = {ℓ₁,…,ℓ_k} be a cycle. Write the points of ℓ₁, then of ℓ₂, … as a word w₁…w_{3k}, and fix a
total order ≺ on points. Then Σ_j e(ℓ_j) = Σ_{r<t, w_t ≺ w_r} ω(w_r, w_t) (mod 2).
**Proof steps.**
1. Evaluate M = P(w₁)⋯P(w_{3k}) in the Pauli group (ALG-0). Grouping by lines,
   M = ∏_j (2e(ℓ_j), 0) = (2Σe, 0).
2. Sort the word by adjacent transpositions (bubble sort). Each swap of adjacent P(p)P(q) multiplies by
   (2ω(p,q), 0) (ALG-0.3, centrality). Bubble sort swaps exactly the inverted pairs, each once. Lean: induction on
   the list with an `insertionSort` invariant, or a general lemma "product of a list = product of its sorted
   permutation times the inversion sign" for the commutation-twisted product.
3. In the sorted word each point occurs an even number of times (cycle), and P(p)² = 1 (ALG-0.5), so the sorted
   product is (0,0).
4. Comparing: (2Σe, 0) = (2·inv, 0), so Σe = inv in F.

## ALG-3 (invariance) — Lean: `deg_invariant`
**Statement.** If π : P(C) → P(C') is a bijection sending lines onto lines with ω(πp, πq) = ω(p,q), then
deg C = deg C'.
**Proof steps.**
1. Identify the points and lines of C and C' via π. The incidence matrices then coincide.
2. For each cycle y, ALG-2 applied in C and in C' with the same word and the transported order gives
   y·e_C = y·e_{C'}.
3. By ALG-1b, e_C − e_{C'}∘π ∈ Im H. By ALG-1 the degrees are equal.
**Corollary.** Sp(2n,2) preserves degrees, as do padding p ↦ (p|0) into more qubits and linear isometries between
non-degenerate subspaces.

## ALG-4 (operational inequality) — Lean: `nc_bound`
**Statement.** Let β = Σ_ℓ (−1)^{e(ℓ)}⟨abc⟩. Deterministic noncontextual models give β ≤ m − 2deg, with equality
attained. Mixtures give β ≤ m − 2deg. Quantum mechanics gives β = m. Uniform attenuation v violates the bound iff
v > 1 − 2deg/m.
**Proof steps.**
1. A deterministic model contributes +1 per satisfied line and −1 per violated line, so β = m − 2|V| ≤ m − 2deg.
2. A convex combination of such values is ≤ the maximum.
3. Quantum: the product of the outcomes is the eigenvalue of (−1)^e P(a)P(b)P(c) = I.
4. Attenuation: v·m > m − 2deg ⇔ v > 1 − 2deg/m.
**Lean.** Step 1 is pure arithmetic. Steps 2–4 are a remark; no physics formalisation is needed.

## Remark (frustration)
#violated = energy of H = Σ_ℓ ½(1 − (−1)^{e}σ_aσ_bσ_c). Changing e by a vector of Im H is a gauge transformation, and odd
cycles are frustrated loops.
