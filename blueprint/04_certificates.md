# 04. Certificates: odd cycles, packings, barrier

## CERT-1 (odd-cycle lemma) — `odd_cycle_forces_violation`
**Statement.** If y is a cycle (every point of C lies on an even number of lines of y) with Σ_{ℓ∈y} e(ℓ) = 1, then every
assignment violates an odd number, and hence at least one, of the lines of y.
**Steps.** Σ_{ℓ∈y}[ℓ violated] ≡ Σ_{ℓ∈y}(s(a)+s(b)+s(c)+e(ℓ)) = Σ_p (#lines of y through p)·s(p) + Σe ≡ 0 + 1.
**Lean.** Work in ZMod 2 and use `Finset.sum_comm`. Note Σ [viol] mod 2 = Σ (Hs+e)_ℓ.

## CERT-1b (degree of a grid, of a doily)
1. A grid is a cycle (each point lies on one row and one column). If it is odd, its degree is ≥ 1 (CERT-1).
2. A doily together with its 10 odd grids, each line lying in exactly 4 of them: TR-1' gives deg ≥ ⌈10·1/4⌉ = 3.
3. The upper bound 3 comes from an explicit assignment, or the all-zero one when there are 3 negative lines.

## CERT-2 (packings) — `packing_le_transfer`
**Definition.** A packing is w : F → ℝ≥0 with Σ_{S∋ℓ} w_S ≤ 1 for all ℓ. Its value is Σ w_S deg S.
**Statement.** (a) deg C ≥ value. (b) value ≤ |L(C)|·sup ρ(S). (c) If Γ is line-transitive and F is
Γ-invariant, the optimal value is exactly |L(C)|·max ρ(S).
**Steps.** (a) Σ w_S deg S ≤ Σ w_S |V∩S| = Σ_{ℓ∈V} Σ_{S∋ℓ} w_S ≤ |V|. (b) deg S ≤ r|L(S)| with r = sup ρ, then swap
the sums. (c) Put uniform weight on the orbit of the best S; transitivity makes the coverage constant.

## CERT-3 (three-qubit barrier) — `three_qubit_barrier`
If every S ∈ F embeds into W(5,2), then value ≤ |L(C)|/5 (by TQ-2 and CERT-2b). Consequence: local fractional packings
of 3-qubit witnesses cannot prove deg Q⁻(7,2) > 215, deg W(7,2) > 1071 or deg Q⁺(9,2) > 4743.
GEO-2 (216) escapes the barrier because its intermediate witness O_a is not 3-qubit realisable and the bound is
rounded up inside O_a.
