/-
QuantumGame.lean — blueprint 11, GAME-1 (quantum side): with N EPR pairs and Pauli measurements the
line/point game of every induced configuration is won with probability 1.

The strategy: Alice and Bob share |Φ⟩ = d^{−1/2} Σ_i |i⟩|i⟩ on (ℂ²)^{⊗N} ⊗ (ℂ²)^{⊗N}.  On line
ℓ = {a, b, a+b} Alice measures the commuting P_a, P_b, P_{a+b} (projector Π_o = Π_a^{o₁}Π_b^{o₂}Π_{a+b}^{o₃},
Π_x^u = (1 + (−1)^u P_x)/2) and answers o; on point x Bob measures P_xᵀ and answers his bit u.
  * `epr_expect`   : ⟨Φ| A ⊗ Bᵀ |Φ⟩ = tr(AB)/d.
  * `alice_valid`  : Alice's outcome violates the line equation with probability 0 (tr Π_o = 0 when
                     o₁ + o₂ + o₃ ≠ e(ℓ)).
  * `quantum_win`  : for every line and each of its three points, Σ_o ⟨Φ|Π_o ⊗ (Π_x^{o_x})ᵀ|Φ⟩ = 1.
-/
import PauliContextuality.Game
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Matrix Complex
open scoped Kronecker

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-! ### the maximally entangled state -/

/-- |Φ⟩ = d^{−1/2} Σ_i |i⟩|i⟩ -/
noncomputable def epr (N : ℕ) : Bas N × Bas N → ℂ :=
  fun ij => if ij.1 = ij.2 then (((Real.sqrt (2 ^ N))⁻¹ : ℝ) : ℂ) else 0

theorem epr_expect (A B : Matrix (Bas N) (Bas N) ℂ) :
    star (epr N) ⬝ᵥ ((A ⊗ₖ Bᵀ) *ᵥ epr N) = (A * B).trace / 2 ^ N := by
  set κ : ℂ := (((Real.sqrt (2 ^ N))⁻¹ : ℝ) : ℂ)
  have hκ : (starRingEnd ℂ) κ * κ = 1 / 2 ^ N := by
    simp only [κ, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  have hin : ∀ i j : Bas N, ((A ⊗ₖ Bᵀ) *ᵥ epr N) (i, j) = κ * (A * B) i j := by
    intro i j
    simp only [mulVec, dotProduct, kroneckerMap_apply, transpose_apply, epr, mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    ring
  have step : ∀ i j : Bas N, star (epr N) (i, j) * ((A ⊗ₖ Bᵀ) *ᵥ epr N) (i, j) =
      if i = j then (1 / 2 ^ N) * (A * B) i i else 0 := by
    intro i j
    rw [hin]
    simp only [Pi.star_apply, epr, star_def]
    split_ifs with h
    · subst h; rw [← mul_assoc, hκ]
    · simp
  rw [dotProduct, Fintype.sum_prod_type]
  simp only [step, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  simp only [Matrix.trace, diag]
  ring

/-! ### spectral projectors of Paulis -/

/-- Π_x^u = (1 + (−1)^u P_x)/2 -/
noncomputable def projP (x : V N) (u : F) : Matrix (Bas N) (Bas N) ℂ :=
  (1 / 2 : ℂ) • (1 + ((pm u : ℤ) : ℂ) • P x)

theorem pm_sq_c (u : F) : ((pm u : ℤ) : ℂ) * ((pm u : ℤ) : ℂ) = 1 := by
  unfold pm; split_ifs <;> simp

theorem proj_sum (x : V N) : projP x 0 + projP x 1 = 1 := by
  unfold projP pm
  simp only [if_pos rfl, if_neg one_ne_zero]
  push_cast
  module

theorem F_cases01 (u : F) : u = 0 ∨ u = 1 := by revert u; decide

theorem pm_zero' : pm (0 : F) = 1 := by decide
theorem pm_one' : pm (1 : F) = -1 := by decide

theorem proj_idem (x : V N) (u : F) : projP x u * projP x u = projP x u := by
  have hP := pauli_sq x
  unfold projP
  rcases F_cases01 u with rfl | rfl
  · simp only [pm_zero', Int.cast_one, one_smul]
    simp only [smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hP]
    module
  · simp only [pm_one', Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    simp only [smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, neg_mul, mul_neg, neg_neg, hP]
    module

theorem proj_comm {x y : V N} (h : P x * P y = P y * P x) (u v : F) :
    projP x u * projP y v = projP y v * projP x u := by
  unfold projP
  simp only [smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h]
  module

/-! ### Alice's projectors on a line -/

/-- the outcome bit of the three points (a, b, a+b) -/
def oc (o : F × F × F) : Fin 3 → F := ![o.1, o.2.1, o.2.2]

/-- the three points (a, b, a+b) -/
def pt3 (a b : V N) : Fin 3 → V N := ![a, b, a + b]

/-- Alice's projector for the outcome triple o -/
noncomputable def projA (a b : V N) (o : F × F × F) : Matrix (Bas N) (Bas N) ℂ :=
  projP a o.1 * projP b o.2.1 * projP (a + b) o.2.2

theorem sum_proj (x : V N) : ∑ u : F, projP x u = 1 := by
  rw [show (Finset.univ : Finset F) = {0, 1} by decide, Finset.sum_pair (by decide), proj_sum]

theorem projA_sum (a b : V N) : ∑ o : F × F × F, projA a b o = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [projA, ← Finset.mul_sum, sum_proj, mul_one]

variable {a b : V N}

theorem comm_ab (h : omega a b = 0) : P a * P b = P b * P a := by
  rw [pauli_comm a b, h, dbl_zero, iPow_zero, one_smul]

theorem absorb0 {A B C : Matrix (Bas N) (Bas N) ℂ} (hAB : A * B = B * A) (hAC : A * C = C * A)
    (hA : A * A = A) : A * B * C * A = A * B * C :=
  calc A * B * C * A = A * B * (C * A) := mul_assoc _ _ _
    _ = A * B * (A * C) := by rw [← hAC]
    _ = A * (B * A) * C := by simp only [mul_assoc]
    _ = A * (A * B) * C := by rw [← hAB]
    _ = A * A * B * C := by simp only [mul_assoc]
    _ = A * B * C := by rw [hA]

theorem absorb1 {A B C : Matrix (Bas N) (Bas N) ℂ} (hBC : B * C = C * B) (hB : B * B = B) :
    A * B * C * B = A * B * C :=
  calc A * B * C * B = A * B * (C * B) := mul_assoc _ _ _
    _ = A * B * (B * C) := by rw [← hBC]
    _ = A * (B * B) * C := by simp only [mul_assoc]
    _ = A * B * C := by rw [hB]

theorem absorb2 {A B C : Matrix (Bas N) (Bas N) ℂ} (hC : C * C = C) : A * B * C * C = A * B * C := by
  rw [mul_assoc, hC]

/-- Alice's projector absorbs the projector of each of its three points -/
theorem projA_absorb (h : omega a b = 0) (o : F × F × F) (k : Fin 3) :
    projA a b o * projP (pt3 a b k) (oc o k) = projA a b o := by
  have hab := comm_ab h
  have hac : P a * P (a + b) = P (a + b) * P a := by
    apply comm_ab; rw [omega_add_right, omega_self, h, add_zero]
  have hbc : P b * P (a + b) = P (a + b) * P b := by
    apply comm_ab; rw [omega_add_right, omega_comm b a, h, omega_self, add_zero]
  unfold projA
  fin_cases k
  · exact absorb0 (proj_comm hab _ _) (proj_comm hac _ _) (proj_idem _ _)
  · exact absorb1 (proj_comm hbc _ _) (proj_idem _ _)
  · exact absorb2 (proj_idem _ _)

/-- the trace of Alice's projector: (d/8)(1 + (−1)^{o₁+o₂+o₃+e}) -/
theorem trace_projA (hL : IsLine a b (a + b)) (e : F)
    (he : P a * P b * P (a + b) = ((pm e : ℤ) : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ)) (o : F × F × F) :
    (projA a b o).trace = (2 ^ N / 8 : ℂ) * (1 + ((pm (o.1 + o.2.1 + o.2.2 + e) : ℤ) : ℂ)) := by
  have hab := comm_ab hL.comm
  have tA : (P a).trace = 0 := by rw [trace_pauli, if_neg hL.nz_a]
  have tB : (P b).trace = 0 := by rw [trace_pauli, if_neg hL.nz_b]
  have tC : (P (a + b)).trace = 0 := by rw [trace_pauli, if_neg hL.nz_c]
  have tAB : (P a * P b).trace = 0 := by rw [trace_pauli_mul, if_neg hL.ne_ab]
  have tAC : (P a * P (a + b)).trace = 0 := by rw [trace_pauli_mul, if_neg hL.ne_ac]
  have tBC : (P b * P (a + b)).trace = 0 := by rw [trace_pauli_mul, if_neg hL.ne_bc]
  have tABC : (P a * P b * P (a + b)).trace = ((pm e : ℤ) : ℂ) * 2 ^ N := by
    rw [he, trace_smul, trace_one, card_bas, smul_eq_mul]
  unfold projA projP
  simp only [smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, trace_smul, trace_add, trace_one, card_bas, smul_eq_mul, ← mul_assoc]
  rw [tA, tB, tC, tAB, tAC, tBC, tABC]
  rw [pm_add, pm_add, pm_add]
  push_cast
  ring

/-- **Alice's answers are always valid**: an outcome triple violating the line equation has
probability ⟨Φ|Π_o ⊗ 1|Φ⟩ = tr(Π_o)/d = 0. -/
theorem alice_valid (hL : IsLine a b (a + b)) (e : F)
    (he : P a * P b * P (a + b) = ((pm e : ℤ) : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ)) (o : F × F × F)
    (ho : o.1 + o.2.1 + o.2.2 ≠ e) :
    star (epr N) ⬝ᵥ ((projA a b o ⊗ₖ (1 : Matrix (Bas N) (Bas N) ℂ)ᵀ) *ᵥ epr N) = 0 := by
  rw [epr_expect, mul_one, trace_projA hL e he]
  have : pm (o.1 + o.2.1 + o.2.2 + e) = -1 := by
    unfold pm; rw [if_neg]; intro h; apply ho
    have key : ∀ x y : F, x + y = 0 → x = y := by decide
    exact key _ _ h
  rw [this]; push_cast; ring

/-- **the quantum strategy wins with probability 1** on line (a, b, a+b) when Bob gets its k-th point:
Σ_o ⟨Φ| Π_o ⊗ (Π_{x_k}^{o_k})ᵀ |Φ⟩ = 1. -/
theorem quantum_win (h : omega a b = 0) (k : Fin 3) :
    ∑ o : F × F × F, star (epr N) ⬝ᵥ ((projA a b o ⊗ₖ (projP (pt3 a b k) (oc o k))ᵀ) *ᵥ epr N) = 1 := by
  simp_rw [epr_expect, projA_absorb h]
  rw [← Finset.sum_div, ← trace_sum, projA_sum, trace_one, card_bas]
  exact div_self (pow_ne_zero _ two_ne_zero)

/-- **GAME-1 (quantum value 1).** For every line of an induced configuration, the EPR/Pauli strategy
answers validly with probability 1 and wins with probability 1 at each of the three points. -/
theorem quantum_perfect (X : Finset (V N)) (h0 : (0 : V N) ∉ X) :
    ∀ l ∈ (configX X h0).lines, ∃ a b : V N, l = {a, b, a + b} ∧
      (∀ o : F × F × F, o.1 + o.2.1 + o.2.2 ≠ (configX X h0).sign l →
        star (epr N) ⬝ᵥ ((projA a b o ⊗ₖ (1 : Matrix (Bas N) (Bas N) ℂ)ᵀ) *ᵥ epr N) = 0) ∧
      (∀ k : Fin 3, ∑ o : F × F × F,
        star (epr N) ⬝ᵥ ((projA a b o ⊗ₖ (projP (pt3 a b k) (oc o k))ᵀ) *ᵥ epr N) = 1) := by
  intro l hl
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
  have hline := isLine_of_OP h0 hp
  have he : P p.1 * P p.2 * P (p.1 + p.2) =
      ((pm ((configX X h0).sign (tri p)) : ℤ) : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ) := by
    rw [pauli_mul, smul_mul_assoc, pauli_sq, iPow_ph_comm hline.comm, configX_sign h0 hp, chi_eq_pm]
  exact ⟨p.1, p.2, rfl, fun o ho => alice_valid hline _ he o ho, fun k => quantum_win hline.comm k⟩

end PauliCtx.Spectral
