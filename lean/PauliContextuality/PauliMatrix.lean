/-
PauliMatrix.lean — canonical Pauli matrices and their algebra (blueprint 10_asymptotics.md, ASY-1 "Lean").

Encoding: labels are `V N` (Basic.lean); the Hilbert-space basis is `Fin N → F` (so d = 2^N).
  P_a (r, c) = i^{y(a) + 2 z·c} · [r = c + x],      a = (x | z),
i.e. P_a = i^{y(a)} X^x Z^z, the canonical Hermitian Pauli (Kronecker products are not needed).
Main facts: `pauli_mul` (group law ALG-0 at the matrix level), `trace_pauli`, `trace_pauli_mul`,
`pauli_hermitian`, `pauli_completeness`.
-/
import PauliContextuality.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

open Matrix Complex

namespace PauliCtx

/-! ### powers of `i` indexed by `ZMod 4` -/

def iPow (k : ZMod 4) : ℂ := I ^ k.val

theorem I_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, I_pow_four, one_pow, mul_one]

theorem iPow_add (k l : ZMod 4) : iPow (k + l) = iPow k * iPow l := by
  unfold iPow
  rw [ZMod.val_add, ← pow_add, I_pow_mod (k.val + l.val)]

@[simp] theorem iPow_zero : iPow 0 = 1 := by simp [iPow]

theorem iPow_two : iPow 2 = -1 := by
  show I ^ 2 = -1
  exact I_sq

theorem iPow_natCast (n : ℕ) : iPow (n : ZMod 4) = I ^ n := by
  unfold iPow
  rw [ZMod.val_natCast, ← I_pow_mod]

theorem conj_iPow (k : ZMod 4) : (starRingEnd ℂ) (iPow k) = iPow (-k) := by
  fin_cases k
  · show (starRingEnd ℂ) (I ^ 0) = I ^ 0; simp
  · show (starRingEnd ℂ) (I ^ 1) = I ^ 3; simp [pow_succ]
  · show (starRingEnd ℂ) (I ^ 2) = I ^ 2; simp [pow_succ]
  · show (starRingEnd ℂ) (I ^ 3) = I ^ 1; simp [pow_succ]

theorem iPow_dbl (t : F) : iPow (dbl t) = if t = 0 then 1 else -1 := by
  by_cases h : t = 0
  · subst h; simp
  · have h1 : t = 1 := by revert h; revert t; decide
    subst h1; rw [dbl_one, iPow_two, if_neg (by decide)]

theorem iPow_ne_zero (k : ZMod 4) : iPow k ≠ 0 := pow_ne_zero _ I_ne_zero

theorem iPow_mul_neg (k : ZMod 4) : iPow k * iPow (-k) = 1 := by
  rw [← iPow_add, add_neg_cancel, iPow_zero]

variable {N : ℕ}

/-- basis of `(ℂ²)^{⊗N}` -/
abbrev Bas (N : ℕ) := Fin N → F

/-- dot product on `F^N` -/
def dot (u v : Fin N → F) : F := ∑ k, u k * v k

theorem dot_add_right (u v w : Fin N → F) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply]; ring

theorem dot_add_left (u v w : Fin N → F) : dot (u + v) w = dot u w + dot v w := by
  unfold dot; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply]; ring

theorem dot_comm (u v : Fin N → F) : dot u v = dot v u := by
  unfold dot; refine Finset.sum_congr rfl fun k _ => ?_; ring

/-- The canonical Pauli matrix `P_a = i^{y(a)} X^x Z^z`. -/
def P (a : V N) : Matrix (Bas N) (Bas N) ℂ :=
  Matrix.of fun r c => if r = c + a.1 then iPow ((ycount a : ZMod 4) + dbl (dot a.2 c)) else 0

/-- the phase in `P_a P_b = i^{ph(a,b)} P_{a+b}` -/
def ph (a b : V N) : ZMod 4 :=
  (ycount a : ZMod 4) + ycount b + dbl (dot a.2 b.1) - ycount (a + b)

theorem pauli_mul (a b : V N) : P a * P b = iPow (ph a b) • P (a + b) := by
  ext r c
  simp only [P, mul_apply, of_apply, smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [Finset.sum_eq_single (c + b.1)]
  · simp only [if_true]
    by_cases h : r = c + b.1 + a.1
    · have h' : r = c + (a.1 + b.1) := by rw [h, add_assoc, add_comm b.1]
      rw [if_pos h, if_pos h', ← iPow_add, ← iPow_add]
      congr 1
      unfold ph
      rw [dot_add_right, dot_add_left, dbl_add, dbl_add]
      ring
    · have h' : ¬ r = c + (a.1 + b.1) := by rwa [← add_assoc, add_right_comm]
      rw [if_neg h, if_neg h', zero_mul, mul_zero]
  · intro m _ hm
    rw [if_neg hm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### character sums -/

theorem sum_char (z : Fin N → F) :
    ∑ c : Bas N, iPow (dbl (dot z c)) = if z = 0 then (Fintype.card (Bas N) : ℂ) else 0 := by
  split_ifs with hz
  · subst hz; simp [dot]
  · obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
      by_contra h; push Not at h; exact hz (funext h)
    have hk1 : z k = 1 := by revert hk; generalize z k = t; revert t; decide
    set e : Bas N := Pi.single k 1
    have hze : dot z e = 1 := by
      unfold dot
      rw [Finset.sum_eq_single k]
      · simp [e, hk1]
      · intro j _ hj; simp [e, Pi.single_apply, hj]
      · simp
    have hshift : ∑ c : Bas N, iPow (dbl (dot z c)) = ∑ c : Bas N, iPow (dbl (dot z (c + e))) :=
      (Fintype.sum_equiv (Equiv.addRight e) _ _ (fun c => rfl)).symm
    have hneg : ∑ c : Bas N, iPow (dbl (dot z (c + e))) = - ∑ c : Bas N, iPow (dbl (dot z c)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dot_add_right, hze, dbl_add, iPow_add, dbl_one, iPow_two]; ring
    rw [hneg] at hshift
    have : (2 : ℂ) * ∑ c : Bas N, iPow (dbl (dot z c)) = 0 := by linear_combination hshift
    simpa using this

theorem card_bas : (Fintype.card (Bas N) : ℂ) = 2 ^ N := by
  simp [Fintype.card_fun, ZMod.card]

/-! ### traces -/

theorem add_self_V'' (x : Bas N) : x + x = 0 := by
  ext k; exact add_self_F _

theorem ycount_of_x_zero (a : V N) (h : a.1 = 0) : ycount a = 0 := by
  simp [ycount, h]

theorem trace_pauli (a : V N) : (P a).trace = if a = 0 then (2 ^ N : ℂ) else 0 := by
  unfold Matrix.trace
  simp only [diag, P, of_apply]
  by_cases hx : a.1 = 0
  · have hy := ycount_of_x_zero a hx
    simp only [hx, add_zero, if_true, hy, Nat.cast_zero, zero_add]
    rw [sum_char, card_bas]
    by_cases hz : a.2 = 0
    · have : a = 0 := Prod.ext hx hz
      simp [this]
    · have : a ≠ 0 := fun h => hz (by rw [h]; rfl)
      simp [hz, this]
  · have : a ≠ 0 := fun h => hx (by rw [h]; rfl)
    rw [if_neg this]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    intro h
    exact hx (by simpa using h)

/-! ### products, adjoints, the line sign -/

theorem P_zero : P (0 : V N) = 1 := by
  ext r c
  simp only [P, of_apply, Prod.fst_zero, add_zero, Matrix.one_apply]
  split_ifs with h
  · simp [ycount, dot]
  · rfl

theorem dot_snd_fst_self (a : V N) : dot a.2 a.1 = (ycount a : F) := by
  rw [ycount_cast]; unfold dot qplus; refine Finset.sum_congr rfl fun k _ => ?_; ring

theorem ph_self (a : V N) : ph a a = 0 := by
  unfold ph
  rw [dot_snd_fst_self, ← two_mul_natCast, add_self_V, ycount_of_x_zero 0 rfl]
  have : (4 : ZMod 4) = 0 := rfl
  linear_combination (ycount a : ZMod 4) * this

theorem pauli_sq (a : V N) : P a * P a = 1 := by
  rw [pauli_mul, ph_self, add_self_V, P_zero, iPow_zero, one_smul]

theorem trace_pauli_mul (a b : V N) : (P a * P b).trace = if a = b then (2 ^ N : ℂ) else 0 := by
  rw [pauli_mul, trace_smul, trace_pauli]
  by_cases h : a = b
  · subst h; simp [add_self_V, ph_self]
  · have : a + b ≠ 0 := by
      intro h'; apply h
      have := congrArg (· + b) h'; simpa [add_assoc, add_self_V] using this
    simp [h, this]

theorem dot_swap (a b : V N) : dot a.2 b.1 = dot b.2 a.1 + omega a b := by
  unfold dot omega
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  generalize a.1 k = x1; generalize a.2 k = x2; generalize b.1 k = y1; generalize b.2 k = y2
  revert x1 x2 y1 y2; decide

theorem ph_swap (a b : V N) : ph a b = ph b a + dbl (omega a b) := by
  unfold ph
  rw [dot_swap, dbl_add, add_comm b a]
  ring

theorem ph_eq_signK (a b : V N) : ph a b = signK a b (a + b) := by
  rw [signK_eq]
  have h1 : ∑ i, (a.2 i * b.1 i + (a.2 i + b.2 i) * (a + b).1 i) = dot a.2 b.1 + (ycount (a + b) : F) := by
    rw [ycount_cast]
    unfold dot qplus
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
  rw [h1, dbl_add, ← two_mul_natCast]
  unfold ph
  push_cast
  have : (4 : ZMod 4) = 0 := rfl
  linear_combination (-(ycount (a + b) : ZMod 4)) * this

/-- The commutation relation: `P_b P_a = (-1)^{ω(a,b)} P_a P_b`. -/
theorem pauli_comm (a b : V N) : P b * P a = iPow (dbl (omega a b)) • (P a * P b) := by
  rw [pauli_mul, pauli_mul, smul_smul, ← iPow_add, ph_swap a b, add_comm a b]
  congr 2
  rw [add_comm, add_assoc, ← dbl_add, add_self_F, dbl_zero, add_zero]

theorem conj_iPow_dbl (t : F) : (starRingEnd ℂ) (iPow (dbl t)) = iPow (dbl t) := by
  rw [conj_iPow]; congr 1
  revert t; decide

theorem pauli_hermitian (a : V N) : (P a).IsHermitian := by
  ext r c
  simp only [conjTranspose_apply, P, of_apply, star_def]
  by_cases h : r = c + a.1
  · have h' : c = r + a.1 := by rw [h, add_assoc, add_self_V'', add_zero]
    rw [if_pos h', if_pos h, conj_iPow]
    congr 1
    rw [h', dot_add_right, dbl_add, dot_snd_fst_self, ← two_mul_natCast]
    have hn : ∀ t : F, -dbl t = dbl t := by decide
    rw [neg_add, hn]
    have : (4 : ZMod 4) = 0 := rfl
    linear_combination (-(ycount a : ZMod 4)) * this
  · have h' : ¬ c = r + a.1 := by
      intro h'; apply h; rw [h', add_assoc, add_self_V'', add_zero]
    rw [if_neg h', if_neg h, map_zero]

/-! ### Pauli completeness: Σ_a |⟨v|P_a|v⟩|² = 2^N ‖v‖⁴ -/

theorem quad_form (a : V N) (v : Bas N → ℂ) :
    star v ⬝ᵥ (P a *ᵥ v) =
      iPow (ycount a) * ∑ c, (starRingEnd ℂ) (v (c + a.1)) * v c * iPow (dbl (dot a.2 c)) := by
  simp only [dotProduct, mulVec, P, of_apply, Pi.star_apply, star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, iPow_add]
  ring

theorem char_orth (c c' : Bas N) :
    ∑ z : Bas N, iPow (dbl (dot z c)) * iPow (dbl (dot z c')) = if c = c' then (2 ^ N : ℂ) else 0 := by
  have : ∀ z : Bas N, iPow (dbl (dot z c)) * iPow (dbl (dot z c')) = iPow (dbl (dot (c + c') z)) := by
    intro z; rw [← iPow_add, ← dbl_add, ← dot_add_right, dot_comm]
  simp_rw [this]
  rw [sum_char, card_bas]
  congr 1
  apply propext
  constructor
  · intro h; have := congrArg (· + c') h; simpa [add_assoc, add_self_V''] using this
  · intro h; rw [h, add_self_V'']

theorem pauli_completeness (v : Bas N → ℂ) :
    ∑ a : V N, (Complex.normSq (star v ⬝ᵥ (P a *ᵥ v)) : ℂ) =
      2 ^ N * (∑ i, (Complex.normSq (v i) : ℂ)) ^ 2 := by
  set f : Bas N → Bas N → ℂ := fun x c => (starRingEnd ℂ) (v (c + x)) * v c with hf
  have h1 : ∀ a : V N, (Complex.normSq (star v ⬝ᵥ (P a *ᵥ v)) : ℂ) =
      ∑ c, ∑ c', f a.1 c * (starRingEnd ℂ) (f a.1 c') *
        (iPow (dbl (dot a.2 c)) * iPow (dbl (dot a.2 c'))) := by
    intro a
    rw [Complex.normSq_eq_conj_mul_self, quad_form, map_mul, map_sum]
    have hy : (starRingEnd ℂ) (iPow (ycount a)) * iPow (ycount a) = 1 := by
      rw [conj_iPow, mul_comm, iPow_mul_neg]
    rw [show ∀ (A B C D : ℂ), A * B * (C * D) = (A * C) * (B * D) from fun _ _ _ _ => by ring, hy,
      one_mul, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    simp only [map_mul, conj_iPow_dbl, hf, Complex.conj_conj]
    ring
  have h2 : ∀ x : Bas N, ∑ z : Bas N, ∑ c, ∑ c', f x c * (starRingEnd ℂ) (f x c') *
      (iPow (dbl (dot z c)) * iPow (dbl (dot z c'))) =
      2 ^ N * ∑ c, (Complex.normSq (v (c + x)) : ℂ) * Complex.normSq (v c) := by
    intro x
    calc _ = ∑ c, ∑ c', ∑ z : Bas N, f x c * (starRingEnd ℂ) (f x c') *
          (iPow (dbl (dot z c)) * iPow (dbl (dot z c'))) := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_; rw [Finset.sum_comm]
      _ = ∑ c, ∑ c', f x c * (starRingEnd ℂ) (f x c') * (if c = c' then (2 ^ N : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
          rw [← Finset.mul_sum, char_orth]
      _ = ∑ c, f x c * (starRingEnd ℂ) (f x c) * 2 ^ N := by
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp
      _ = _ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_
          simp only [hf, map_mul, Complex.conj_conj]
          rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; push_cast; ring
  calc ∑ a : V N, (Complex.normSq (star v ⬝ᵥ (P a *ᵥ v)) : ℂ)
      = ∑ x : Bas N, ∑ z : Bas N, ∑ c, ∑ c', f x c * (starRingEnd ℂ) (f x c') *
          (iPow (dbl (dot z c)) * iPow (dbl (dot z c'))) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => h1 (x, z)
    _ = ∑ x : Bas N, 2 ^ N * ∑ c, (Complex.normSq (v (c + x)) : ℂ) * Complex.normSq (v c) :=
        Finset.sum_congr rfl fun x _ => h2 x
    _ = 2 ^ N * (∑ i, (Complex.normSq (v i) : ℂ)) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm, sq, Finset.sum_mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun x => ?_)
        simp [mul_comm]

end PauliCtx
