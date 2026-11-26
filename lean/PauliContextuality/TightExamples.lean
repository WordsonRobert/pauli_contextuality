/-
TightExamples.lean — blueprint 11, the concrete tight instances (TIGHT-1 examples, TIGHT-2).

  * Q⁺(7,2) ⚙ (`Qplus7_flat`, `Qplus7_eq_315_flat`): the explicit real vector
        ψ = (−3, 1, …, 1)/√24  ∝  |+⟩^{⊗4} − |0⟩^{⊗4}
    has |⟨ψ|P_a|ψ⟩| = 1/3 on the 135 symmetric Paulis and 0 on the 120 antisymmetric ones; by
    TIGHT-1 (`tight_of_flat`) its sign pattern is an optimal assignment and deg Q⁺(7,2) = 315
    (a second proof of `Qplus7_eq_315`, independent of the tabu witness).
  * X₄₉₆ ⚙ (`X496_lines`, `X496_eq_480`): the 5-qubit configuration of `certificates/flat5_496.json`
    has |L| = 10880 and deg = 480 (spectral bound exactly 480 since Λ = √(496·31) = 124; witness
    g = sign⟨P⟩ of the numerical flat state violates 480 lines).
  * TIGHT-2 (`kerW`, `qplus_mem_kerW`, `qplus_not_linear`, `finrank_kerW3` ⚙, `rank_incW3` ⚙,
    `card_fiber_violated`): the gauge space {s : s(0) = 0, s(a+b) = s(a)+s(b) on commuting pairs} of
    W(5,2) has dimension 7 (6 linear functionals + the quadratic form y(a) mod 2, which is not
    linear), i.e. the 315 × 63 incidence matrix over F₂ has rank 56; every violated set is attained
    by exactly 2^7 = 128 normalised assignments.  (The count 120 of optimal violated sets is the
    Sp(6,2)-orbit computation of `certify_asym.py` X5 and is not formalised; see
    blueprint/13_lean_findings.md.)
-/
import PauliContextuality.Tight
import PauliContextuality.GeoBounds
import PauliData.Flat5Data

open Matrix Complex

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-! ### real (integer) vectors -/

/-- `Σ_c u(c + x) u(c) (−1)^{z·c}` -/
def Sint (u : Bas N → ℤ) (a : V N) : ℤ := ∑ c, u (c + a.1) * u c * pm (dot a.2 c)

theorem pm_cast (t : F) : ((pm t : ℤ) : ℂ) = iPow (dbl t) := by
  rw [iPow_dbl]; unfold pm; split_ifs <;> simp

theorem quad_scaled (u : Bas N → ℤ) (κ : ℝ) (a : V N) :
    star (fun c => (κ : ℂ) * u c) ⬝ᵥ (P a *ᵥ (fun c => (κ : ℂ) * u c)) =
      ((κ ^ 2 : ℝ) : ℂ) * (iPow (ycount a) * (Sint u a : ℂ)) := by
  rw [quad_form]
  unfold Sint
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, Complex.conj_ofReal, map_intCast, pm_cast]
  ring

theorem ev_scaled (u : Bas N → ℤ) (κ : ℝ) (a : V N) :
    ev (fun c => (κ : ℂ) * u c) a = κ ^ 2 * Sint u a * (iPow (ycount a)).re := by
  unfold ev
  rw [quad_scaled, Complex.re_ofReal_mul, show iPow (ycount a) * (Sint u a : ℂ) =
    ((Sint u a : ℝ) : ℂ) * iPow (ycount a) by push_cast; ring, Complex.re_ofReal_mul]
  ring

theorem ycount_cases (a : V N) :
    (qplus a = 0 → ((ycount a : ZMod 4) = 0 ∨ (ycount a : ZMod 4) = 2)) ∧
    (qplus a ≠ 0 → ((ycount a : ZMod 4) ≠ 0 ∧ (ycount a : ZMod 4) ≠ 2)) := by
  have h : red (ycount a : ZMod 4) = qplus a := by rw [map_natCast, PauliCtx.ycount_cast]
  refine ⟨fun hq => eq_zero_or_two_of_red (h.trans hq), fun hq => ⟨fun h0 => ?_, fun h2 => ?_⟩⟩
  · apply hq; rw [← h, h0, map_zero]
  · apply hq; rw [← h, h2]; decide

theorem abs_re_iPow_even (a : V N) (h : qplus a = 0) : |(iPow (ycount a)).re| = 1 := by
  rcases (ycount_cases a).1 h with h0 | h2
  · rw [h0, iPow_zero]; simp
  · rw [h2, iPow_two]; simp

theorem re_iPow_odd (a : V N) (h : qplus a ≠ 0) : (iPow (ycount a)).re = 0 := by
  obtain ⟨h0, h2⟩ := (ycount_cases a).2 h
  have : (ycount a : ZMod 4) = 1 ∨ (ycount a : ZMod 4) = 3 := by
    generalize (ycount a : ZMod 4) = k at h0 h2 ⊢; revert k; decide
  rcases this with h1 | h3
  · rw [h1, iPow_one]; simp
  · rw [h3, iPow_three]; simp

/-! ### Q⁺(7,2): the flat state (−3, 1, …, 1)/√24 -/

/-- `24 ψ ∝ 4(|+⟩^{⊗4} − |0⟩^{⊗4})` in the computational basis -/
def uQ : Bas 4 → ℤ := fun c => if c = 0 then -3 else 1

noncomputable def psiQ : Bas 4 → ℂ := fun c => ((1 / Real.sqrt 24 : ℝ) : ℂ) * uQ c

/-- ⚙ the 135 symmetric Paulis have |Σ_c u(c+x)u(c)(−1)^{z·c}| = 8 -/
theorem Sint_QP : ∀ a ∈ QP, (Sint uQ a).natAbs = 8 := by native_decide

theorem sum_uQ_sq : ∑ c, (uQ c : ℝ) ^ 2 = 24 := by
  have h : ∑ c, (uQ c) ^ 2 = 24 := by native_decide
  exact_mod_cast h

theorem psiQ_norm : ∑ i, Complex.normSq (psiQ i) = 1 := by
  have h24 : Real.sqrt 24 ^ 2 = 24 := Real.sq_sqrt (by norm_num)
  have : ∀ i, Complex.normSq (psiQ i) = (1 / 24) * (uQ i : ℝ) ^ 2 := by
    intro i
    unfold psiQ
    rw [show ((1 / Real.sqrt 24 : ℝ) : ℂ) * (uQ i : ℂ) = (((1 / Real.sqrt 24) * uQ i : ℝ) : ℂ) by
      push_cast; ring, Complex.normSq_ofReal]
    field_simp
    rw [h24]; ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, sum_uQ_sq]; norm_num

theorem ev_psiQ (a : V 4) : ev psiQ a = (1 / 24) * Sint uQ a * (iPow (ycount a)).re := by
  have := ev_scaled uQ (1 / Real.sqrt 24) a
  rw [show ((1 / Real.sqrt 24) ^ 2 : ℝ) = 1 / 24 by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    at this
  exact this

/-- ⚙ **ψ is Pauli-flat exactly on Q⁺(7,2)** (γ = 1/3) -/
theorem Qplus7_flat : (∀ a ∈ QP, |ev psiQ a| = 1 / 3) ∧ (∀ a : V 4, a ≠ 0 → a ∉ QP → ev psiQ a = 0) := by
  refine ⟨fun a ha => ?_, fun a ha0 ha => ?_⟩
  · have hq : qplus a = 0 := (Finset.mem_filter.1 ha).2.2
    rw [ev_psiQ, abs_mul, abs_mul, abs_re_iPow_even a hq, mul_one]
    have h8 := Sint_QP a ha
    have : |(Sint uQ a : ℝ)| = 8 := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, h8]; norm_num
    rw [this]; norm_num
  · have hq : qplus a ≠ 0 := fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha0, h⟩)
    rw [ev_psiQ, re_iPow_odd a hq, mul_zero]

/-- ⚙ **TIGHT-1 for Q⁺(7,2)**: the sign pattern of ψ is an optimal assignment and
deg Q⁺(7,2) = 315 (second proof, via the flat state). -/
theorem Qplus7_eq_315_flat : Qplus7.deg = (Qplus7.violated (signOf psiQ)).card ∧ Qplus7.deg = 315 := by
  obtain ⟨hflat, hoff⟩ := Qplus7_flat
  have h := tight_of_flat QP zero_not_mem_QP (by norm_num) psiQ psiQ_norm (1 / 3) (by norm_num)
    hflat hoff (by rw [card_QP]; norm_num)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  change (Qplus7.deg : ℝ) = (Qplus7.lines.card : ℝ) / 2 - _ at h2
  rw [Qplus7_lines, card_QP] at h2
  have hs : Real.sqrt ((135 : ℕ) : ℝ) = 3 * Real.sqrt (2 ^ 4 - 1) := by
    rw [show ((135 : ℕ) : ℝ) = 3 ^ 2 * (2 ^ 4 - 1) by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [hs] at h2
  have hpos : 0 < Real.sqrt ((2 : ℝ) ^ 4 - 1) := Real.sqrt_pos.2 (by norm_num)
  have : (Qplus7.deg : ℝ) = 315 := by
    rw [h2]; field_simp; norm_num
  exact_mod_cast this

/-! ### X₄₉₆: a new exactly solved 5-qubit configuration -/

/-- bit-packed key of a 5-qubit label: x | (z << 5), qubit i ↔ bit i -/
def key5 (p : V 5) : ℕ := (∑ i : Fin 5, (p.1 i).val * 2 ^ i.val) + ∑ i : Fin 5, (p.2 i).val * 2 ^ (5 + i.val)

/-- the 496 points of `certificates/flat5_496.json` -/
def X496 : Finset (V 5) := Finset.univ.filter (fun p => Flat5.memX.getD (key5 p) false = true)

theorem zero_not_mem_X496 : (0 : V 5) ∉ X496 := by
  simp only [X496, Finset.mem_filter, Finset.mem_univ, true_and]; native_decide

noncomputable def X496C : Config (V 5) := configX X496 zero_not_mem_X496

theorem card_X496 : X496.card = 496 := by native_decide

theorem card_OP_X496 : (OP X496).card = 65280 := by unfold X496; rw [OP_filter]; native_decide

/-- ⚙ |L(X₄₉₆)| = 10880 -/
theorem X496_lines : X496C.lines.card = 10880 := by
  have := six_mul_card X496 zero_not_mem_X496
  rw [card_OP_X496] at this
  unfold X496C; omega

/-- the witness: g = sign⟨ψ|P_a|ψ⟩ of the numerical flat state -/
def s496 (p : V 5) : F := if Flat5.negT.getD (key5 p) false then 1 else 0

theorem X496_witness : ((OP X496).filter (violP s496)).card = 2880 := by
  unfold X496; rw [OP_filter]; native_decide

theorem X496_le_480 : X496C.deg ≤ 480 := deg_le_of_pairs _ _ _ _ X496_witness

/-- the spectral bound is exactly 480: Λ = √(496·31) = 124, deficit 496²·30/(12·124) = 4960 -/
theorem X496_ge_480 : 480 ≤ X496C.deg := by
  have hne : X496.Nonempty := Finset.card_pos.1 (by rw [card_X496]; norm_num)
  have h := spectral_lower' X496 zero_not_mem_X496 hne (by norm_num) 124 (by norm_num)
    (by rw [card_X496]; norm_num)
  change (X496C.lines.card : ℝ) / 2 - _ ≤ X496C.deg at h
  rw [X496_lines, card_X496] at h
  have : (480 : ℝ) ≤ X496C.deg := by
    generalize (X496C.deg : ℝ) = D at h ⊢
    norm_num at h
    linarith
  exact_mod_cast this

/-- ⚙ **deg X₄₉₆ = 480** -/
theorem X496_eq_480 : X496C.deg = 480 := le_antisymm X496_le_480 X496_ge_480

end PauliCtx.Spectral
