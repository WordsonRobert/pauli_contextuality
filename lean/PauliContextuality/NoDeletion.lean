/-
NoDeletion.lean — blueprint HARD-11.

  * `no_deletion` (HARD-11.1): in an induced configuration `configX X`, if a family `A` of lines
      "sums" to a commuting triple {a, b, c} ⊆ X (every point lies on an odd number of lines of `A`
      iff it is one of a, b, c), then a + b + c = 0 and {a, b, c} is itself a line of `configX X`.
      So a line cannot be deleted from an induced configuration while keeping its generators.
  * `unavoidable` (HARD-11.2): if a retained line of sign e interacts with its gadget only through a
      parity t, with gadget cost g(t), the total cost min_t ([t ≠ e] + g(t)) equals
      min(g(e), 1 + g(e+1)); a value below g(e) is 1 + g(e+1) ≥ 1.
-/
import PauliContextuality.SpectralConfig

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-- the label sum of a line of `configX X` is zero -/
theorem sum_line_zero {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {l : Finset (V N)}
    (hl : l ∈ (configX X h0).lines) : ∑ p ∈ l, p = 0 := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hl
  have hL := isLine_of_OP h0 hq
  simp only [tri]
  rw [Finset.sum_insert (by simp [hL.ne_ab, hL.ne_ac]), Finset.sum_insert (by simp [hL.ne_bc]),
    Finset.sum_singleton, ← add_assoc, add_self_V]

theorem nsmul_V (k : ℕ) (p : V N) : k • p = if k % 2 = 1 then p else 0 := by
  rw [← Nat.mod_add_div k 2, add_nsmul, mul_nsmul]
  have h2 : 2 • p = 0 := by rw [two_nsmul, add_self_V]
  rw [h2, nsmul_zero, add_zero, Nat.mod_add_div]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

/-- **HARD-11.1 (no deletion).** -/
theorem no_deletion {X : Finset (V N)} (h0 : (0 : V N) ∉ X) (A : Finset (Finset (V N)))
    (hA : A ⊆ (configX X h0).lines) {a b c : V N} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hω : omega a b = 0)
    (hpar : ∀ p, (A.filter (fun l => p ∈ l)).card % 2 = if p ∈ ({a, b, c} : Finset (V N)) then 1 else 0) :
    a + b + c = 0 ∧ ({a, b, c} : Finset (V N)) ∈ (configX X h0).lines := by
  -- Σ_{l∈A} Σ_{p∈l} p = 0, and it equals Σ_p (#{l ∈ A : p ∈ l}) • p = a + b + c
  have h1 : ∑ l ∈ A, ∑ p ∈ l, p = 0 :=
    Finset.sum_eq_zero fun l hl => sum_line_zero h0 (hA hl)
  have h2 : ∑ l ∈ A, ∑ p ∈ l, p = ∑ p : V N, (A.filter (fun l => p ∈ l)).card • p := by
    have : ∀ l ∈ A, ∑ p ∈ l, p = ∑ p : V N, if p ∈ l then p else 0 := by
      intro l _; rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const]
  have h3 : ∑ p : V N, (A.filter (fun l => p ∈ l)).card • p = a + b + c := by
    have : ∀ p : V N, (A.filter (fun l => p ∈ l)).card • p =
        if p ∈ ({a, b, c} : Finset (V N)) then p else 0 := by
      intro p; rw [nsmul_V, hpar p]
      by_cases hp : p ∈ ({a, b, c} : Finset (V N)) <;> simp [hp]
    rw [Finset.sum_congr rfl (fun p _ => this p), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]), Finset.sum_singleton,
      add_assoc]
  have hsum : a + b + c = 0 := by rw [← h3, ← h2, h1]
  refine ⟨hsum, ?_⟩
  have hc' : c = a + b := third_eq hsum
  refine Finset.mem_image.2 ⟨(a, b), mem_OP.2 ⟨ha, hb, hω, hc' ▸ hc⟩, ?_⟩
  simp [tri, hc']

/-- **HARD-11.2 (unavoidable constant).** -/
theorem unavoidable (e : F) (g : F → ℕ) :
    (∀ t : F, min (g e) (1 + g (e + 1)) ≤ (if t ≠ e then 1 else 0) + g t) ∧
    (∃ t : F, (if t ≠ e then 1 else 0) + g t = min (g e) (1 + g (e + 1))) := by
  have hc : ∀ t : F, t = e ∨ t = e + 1 := by intro t; revert t e; decide
  have hne : e + 1 ≠ e := by revert e; decide
  constructor
  · intro t
    rcases hc t with rfl | rfl
    · simp only [ne_eq, not_true_eq_false, if_false, zero_add]; exact min_le_left _ _
    · rw [if_pos hne]; exact min_le_right _ _
  · rcases le_total (g e) (1 + g (e + 1)) with h | h
    · exact ⟨e, by simp [min_eq_left h]⟩
    · exact ⟨e + 1, by rw [if_pos hne, min_eq_right h]⟩

end PauliCtx.Spectral
