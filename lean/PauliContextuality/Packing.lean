/-
Packing.lean — blueprint CERT-2 (c) and CERT-3.

  * `packing_orbit` (CERT-2 c): for a line-transitive group, uniform weight 1/c on the translates of S is a
      fractional packing of value |L(C)|·deg S/|L(S)|. Together with CERT-2 (b) (`packing_le_ratio`) the
      optimal packing value over a Γ-invariant family is exactly |L(C)|·max ρ(S).
  * `three_qubit_barrier` (CERT-3): if every member of the family is a configuration on ≤ 3 qubits
      (with the same number of lines and a degree certificate no larger than its degree), the packing
      value is ≤ |L(C)|/5.
-/
import PauliContextuality.Transfer

namespace PauliCtx

namespace Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **CERT-2 (c).** Uniform weights on the orbit of `L` form a packing whose value is
`|L(C)|·d/|L|`, the TR-1 bound. -/
theorem packing_orbit (C : Config α) (H : Subgroup (Equiv.Perm α)) [Fintype H]
    (L : Finset (Finset α)) (hL : L ⊆ C.lines) (hne : L.Nonempty)
    (hmap : ∀ g ∈ H, ∀ l ∈ C.lines, l.map g.toEmbedding ∈ C.lines)
    (htrans : ∀ l ∈ C.lines, ∀ l' ∈ C.lines, ∃ g ∈ H, l.map g.toEmbedding = l') (d : ℕ) :
    ∃ w : H → ℝ, (∀ g, 0 ≤ w g) ∧
      (∀ l ∈ C.lines, ∑ g ∈ Finset.univ.filter (fun g : H => l ∈ imgL g L), w g = 1) ∧
      ∑ g : H, w g * d = (C.lines.card : ℝ) * d / L.card := by
  obtain ⟨c, hc, hcov, hdc⟩ := transfer_cover C H L hL hne hmap htrans
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hLR : (0 : ℝ) < L.card := by exact_mod_cast Finset.card_pos.2 hne
  refine ⟨fun _ => 1 / c, fun _ => by positivity, fun l hl => ?_, ?_⟩
  · rw [Finset.sum_const, hcov l hl, nsmul_eq_mul]; field_simp
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hdcR : (Fintype.card H : ℝ) * L.card = c * C.lines.card := by exact_mod_cast hdc
    field_simp
    linear_combination (d : ℝ) * hdcR

end Config

namespace Spectral

open Config

/-- **CERT-3 (three-qubit barrier).** Let `fam` be a fractional packing of `C` in which every member
`fam i` is (isomorphic to) a configuration on ≤ 3 qubits with the same number of lines, and the
certified degree `d i` is at most the degree of that configuration. Then the packing value is at
most `|L(C)|/5`. -/
theorem three_qubit_barrier {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (C : Config α) (fam : ι → Finset (Finset α)) (hsub : ∀ i, fam i ⊆ C.lines) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hpack : ∀ l ∈ C.lines, ∑ i ∈ Finset.univ.filter (fun i => l ∈ fam i), w i ≤ 1) (d : ι → ℕ)
    (hemb : ∀ i, ∃ M ≤ 3, ∃ L' : Finset (Finset (V M)), ∃ h : L' ⊆ (W M).lines,
      L'.card = (fam i).card ∧ d i ≤ ((W M).sub L' h).deg) :
    ∑ i, w i * d i ≤ (1 / 5) * C.lines.card := by
  refine packing_le_ratio C fam hsub w hw hpack d (1 / 5) (by norm_num) fun i => ?_
  obtain ⟨M, hM, L', h, hc, hd⟩ := hemb i
  have := three_qubit_bound_le M hM L' h
  have h5 : (5 * d i : ℝ) ≤ (fam i).card := by
    rw [← hc]; exact_mod_cast le_trans (Nat.mul_le_mul_left 5 hd) this
  linarith

end Spectral
end PauliCtx
