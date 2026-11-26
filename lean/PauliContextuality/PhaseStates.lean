/-
PhaseStates.lean — blueprint ASY-5 (the rate 1/2 − ρ_N = Θ(2^{−N/2})), proved with a finite ensemble.

Instead of Haar-random states we average over the 4^d *phase states* ψ_ε = (i^{ε_c})_c,
ε ∈ (ZMod 4)^d. For every Pauli P_a with non-zero x-part, ⟨ψ_ε|P_a|ψ_ε⟩ is distributed exactly as a
sum of d independent signs, so its mean absolute value is d·C(d,d/2)/2^d — the same value
w_m = C(2m,m)/4^m (m = d/2) as for Haar-random states. Only the 2^N − 1 Pauli Z's are lost.

Part 1 (this section): the two self-contained ingredients.
  * `rademacher_abs`  : Σ_{k} C(2m,k)·|2m − 2k| = 2m·C(2m,m).
  * `cube_trace_lower` : for Hermitian M and a vector v with ⟨v|M|v⟩ ≥ λ‖v‖² (λ ≥ 0),
      tr M³ ≥ λ³ − (tr M² − λ²)^{3/2}.
-/
import PauliContextuality.SpectralW
import PauliContextuality.NegLines
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Sum

open Matrix Complex Finset

namespace PauliCtx.Spectral

/-! ### the Rademacher identity -/

/-- `C(n,k)(n − 2k) = n (C(n−1,k) − C(n−1,k−1))` for `k ≥ 1` (in ℤ) -/
theorem choose_mul_sub (n k : ℕ) :
    ((n + 1).choose (k + 1) : ℤ) * ((n + 1 : ℤ) - 2 * (k + 1)) =
      (n + 1) * ((n.choose (k + 1) : ℤ) - n.choose k) := by
  have h1 : ((n + 1).choose (k + 1) : ℤ) * (k + 1) = (n + 1) * n.choose k := by
    have := Nat.succ_mul_choose_eq n k
    exact_mod_cast (by rw [mul_comm]; linarith [this] : _)
  have h2 : ((n + 1).choose (k + 1) : ℤ) = n.choose k + n.choose (k + 1) := by
    exact_mod_cast Nat.choose_succ_succ n k
  have h3 : (n.choose (k + 1) : ℤ) * (k + 1) = n.choose k * (n - k) := by
    have := Nat.choose_succ_right_eq n k
    rcases Nat.lt_or_ge n k with hnk | hnk
    · rw [Nat.choose_eq_zero_of_lt hnk, Nat.choose_eq_zero_of_lt (by omega)]; simp
    · have e : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by push_cast [hnk]; ring
      rw [← e]; exact_mod_cast this
  nlinarith [h1, h2, h3]

theorem sum_tele (n j : ℕ) :
    ∑ k ∈ range (j + 1), ((n + 1).choose k : ℤ) * ((n + 1 : ℤ) - 2 * k) = (n + 1) * n.choose j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih]
    have := choose_mul_sub n j
    push_cast at this ⊢
    linarith

/-- **Σ_k C(2m,k)·|2m − 2k| = 2m·C(2m,m)** -/
theorem rademacher_abs (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range (2 * m + 1), ((2 * m).choose k : ℤ) * |(2 * m : ℤ) - 2 * k| =
      2 * m * (2 * m).choose m := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * m = n + 1 := ⟨2 * m - 1, by omega⟩
  have hm' : (2 * m : ℤ) = n + 1 := by exact_mod_cast hn
  -- the signed sum vanishes
  have h0 : ∑ k ∈ range (2 * m + 1), ((2 * m).choose k : ℤ) * ((2 * m : ℤ) - 2 * k) = 0 := by
    have := sum_tele n (n + 1)
    rw [Nat.choose_succ_self, Nat.cast_zero, mul_zero] at this
    rw [hn, hm']; exact this
  -- the positive part lives on k < m
  have hpos : ∑ k ∈ range (2 * m + 1), ((2 * m).choose k : ℤ) * max ((2 * m : ℤ) - 2 * k) 0 =
      ∑ k ∈ range m, ((2 * m).choose k : ℤ) * ((2 * m : ℤ) - 2 * k) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ 2 * m + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico m (2 * m + 1)) (fun k hk => by
      simp only [Finset.mem_Ico] at hk
      rw [max_eq_right (by
        have : (m : ℤ) ≤ k := by exact_mod_cast hk.1
        linarith), mul_zero]), add_zero]
    refine sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [max_eq_left (by
      have : (k : ℤ) + 1 ≤ m := by exact_mod_cast hk
      linarith)]
  have hT : ∑ k ∈ range m, ((2 * m).choose k : ℤ) * ((2 * m : ℤ) - 2 * k) =
      2 * m * n.choose (m - 1) := by
    have := sum_tele n (m - 1)
    rw [show m - 1 + 1 = m by omega] at this
    rw [hn, hm']; exact this
  have hc : ((2 * m).choose m : ℤ) = 2 * n.choose (m - 1) := by
    have := Nat.add_one_mul_choose_eq n (m - 1)
    rw [show m - 1 + 1 = m by omega, ← hn] at this
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    apply mul_right_cancel₀ hm0
    have h' : ((2 * m : ℕ) : ℤ) * n.choose (m - 1) = (2 * m).choose m * m := by exact_mod_cast this
    push_cast at h'; linarith
  have habs : ∀ x : ℤ, |x| = 2 * max x 0 - x := by
    intro x; rcases le_total x 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  calc ∑ k ∈ range (2 * m + 1), ((2 * m).choose k : ℤ) * |(2 * m : ℤ) - 2 * k|
      = ∑ k ∈ range (2 * m + 1), (2 * (((2 * m).choose k : ℤ) * max ((2 * m : ℤ) - 2 * k) 0) -
          ((2 * m).choose k : ℤ) * ((2 * m : ℤ) - 2 * k)) :=
        sum_congr rfl fun k _ => by rw [habs]; ring
    _ = 2 * ∑ k ∈ range m, ((2 * m).choose k : ℤ) * ((2 * m : ℤ) - 2 * k) - 0 := by
        rw [sum_sub_distrib, ← mul_sum, hpos, h0]
    _ = 2 * m * (2 * m).choose m := by rw [hT, hc]; ring

/-! ### a lower bound for tr M³ -/

/-- `x^{3/2}` -/
noncomputable def p32 (x : ℝ) : ℝ := x * Real.sqrt x

theorem p32_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : p32 x ≤ p32 y :=
  mul_le_mul hxy (Real.sqrt_le_sqrt hxy) (Real.sqrt_nonneg _) (le_trans hx hxy)

/-- `Σ |x_i|³ ≤ (Σ x_i²)^{3/2}` -/
theorem sum_abs_cube_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∑ i ∈ s, |x i| ^ 3 ≤ p32 (∑ i ∈ s, x i ^ 2) := by
  set Q := ∑ i ∈ s, x i ^ 2
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg _
  have hle : ∀ i ∈ s, |x i| ≤ Real.sqrt Q := fun i hi => by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _) hi)
  calc ∑ i ∈ s, |x i| ^ 3 = ∑ i ∈ s, |x i| * x i ^ 2 := by
        refine sum_congr rfl fun i _ => ?_; rw [pow_succ, sq_abs]; ring
    _ ≤ ∑ i ∈ s, Real.sqrt Q * x i ^ 2 := sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (hle i hi) (sq_nonneg _)
    _ = p32 Q := by rw [← mul_sum, p32, mul_comm]

variable {d : Type} [Fintype d] [DecidableEq d]

theorem trace_diag_pow (e : d → ℝ) (k : ℕ) :
    ((diagonal (RCLike.ofReal ∘ e : d → ℂ)) ^ k).trace = ∑ i, ((e i ^ k : ℝ) : ℂ) := by
  rw [diagonal_pow, trace_diagonal]; simp

theorem normSq_sum_eq (v : d → ℂ) : (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by
  simp only [dotProduct, Pi.star_apply, star_def, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- **cubic lower bound.** If ⟨v|M|v⟩ ≥ λ‖v‖² with λ ≥ 0 then
tr M³ ≥ λ³ − (tr M² − λ²)^{3/2}. -/
theorem cube_trace_lower (M : Matrix d d ℂ) (hM : M.IsHermitian) (v : d → ℂ) (hv : v ≠ 0) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam * ∑ i, Complex.normSq (v i) ≤ (star v ⬝ᵥ (M *ᵥ v)).re) :
    lam ^ 3 - p32 ((M * M).trace.re - lam ^ 2) ≤ (M * M * M).trace.re := by
  set e := hM.eigenvalues
  set U : Matrix d d ℂ := (hM.eigenvectorUnitary : Matrix d d ℂ)
  set D : Matrix d d ℂ := diagonal (RCLike.ofReal ∘ e)
  have hspec : M = U * D * star U := by
    have := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hpow : ∀ k : ℕ, (M ^ k).trace = (D ^ k).trace := by
    intro k
    have : M ^ k = U * D ^ k * star U := by
      induction k with
      | zero => simp [hUU']
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        conv_lhs => rw [hspec]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
    rw [this, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  have h2 : (M * M).trace.re = ∑ i, e i ^ 2 := by
    rw [← sq, hpow, trace_diag_pow, Complex.re_sum]; exact sum_congr rfl fun i _ => Complex.ofReal_re _
  have h3 : (M * M * M).trace.re = ∑ i, e i ^ 3 := by
    rw [show M * M * M = M ^ 3 by simp [pow_succ], hpow, trace_diag_pow, Complex.re_sum]
    exact sum_congr rfl fun i _ => Complex.ofReal_re _
  -- the Rayleigh quotient in the eigenbasis
  set w := star U *ᵥ v
  have hquad : (star v ⬝ᵥ (M *ᵥ v)).re = ∑ i, e i * Complex.normSq (w i) := by
    have hw : star w = star v ᵥ* U := by
      simp only [w, star_mulVec]; rw [← star_eq_conjTranspose, star_star]
    have : star v ⬝ᵥ (M *ᵥ v) = star w ⬝ᵥ (D *ᵥ w) := by
      rw [hw, hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    rw [this]
    simp only [D, dotProduct, mulVec_diagonal, Pi.star_apply, Function.comp_apply, star_def,
      Complex.re_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← Complex.normSq_eq_conj_mul_self]; simp
  have hnorm : ∑ i, Complex.normSq (w i) = ∑ i, Complex.normSq (v i) := by
    rw [← normSq_sum_eq, ← normSq_sum_eq]
    congr 1
    simp only [w, star_mulVec, star_star]
    rw [dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, star_star, hUU', vecMul_one]
  -- the largest eigenvalue
  have hne : Nonempty d := by
    by_contra h; rw [not_nonempty_iff] at h; exact hv (funext fun i => isEmptyElim i)
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ e univ_nonempty
  set E := e j
  have hS : 0 < ∑ i, Complex.normSq (v i) := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by by_contra h; push Not at h; exact hv (funext h)
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hi)
      (single_le_sum (f := fun i => Complex.normSq (v i)) (fun _ _ => Complex.normSq_nonneg _) (mem_univ i))
  have hR : ∑ i, e i * Complex.normSq (w i) ≤ E * ∑ i, Complex.normSq (w i) := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hj i (mem_univ _)) (Complex.normSq_nonneg _)
  have hlamE : lam ≤ E := by
    rw [hnorm] at hR
    exact le_of_mul_le_mul_right (by linarith) hS
  set Fv := ∑ i, e i ^ 2
  have hsplit2 : ∑ i ∈ univ.erase j, e i ^ 2 = Fv - E ^ 2 := by
    have := (add_sum_erase univ (fun i => e i ^ 2) (mem_univ j)).symm
    simp only [Fv, E] at this ⊢; linarith
  have hsplit3 : ∑ i, e i ^ 3 = E ^ 3 + ∑ i ∈ univ.erase j, e i ^ 3 := (add_sum_erase _ _ (mem_univ j)).symm
  have hneg : -∑ i ∈ univ.erase j, |e i| ^ 3 ≤ ∑ i ∈ univ.erase j, e i ^ 3 := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun i _ => ?_
    have : |e i ^ 3| = |e i| ^ 3 := abs_pow _ _
    linarith [neg_abs_le (e i ^ 3)]
  have hcube := sum_abs_cube_le (univ.erase j) e
  rw [hsplit2] at hcube
  have hE2 : 0 ≤ Fv - E ^ 2 := by rw [← hsplit2]; exact sum_nonneg fun i _ => sq_nonneg _
  have hmono : p32 (Fv - E ^ 2) ≤ p32 (Fv - lam ^ 2) :=
    p32_mono hE2 (by nlinarith)
  have hc3 : lam ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ hlam0 hlamE 3
  rw [h2, h3]
  linarith

/-! ### Rademacher sums over ZMod 4 -/

/-- `2 Re(i^u)` -/
def hZ (u : ZMod 4) : ℤ := if u = 0 then 2 else if u = 2 then -2 else 0

/-- ZMod 4 ≃ two bits, with hZ = sum of the two signs -/
def enc4 : ZMod 4 ≃ (Fin 2 → Bool) where
  toFun u := ![decide (u = 2 ∨ u = 3), decide (u = 1 ∨ u = 2)]
  invFun b := if b 0 then (if b 1 then 2 else 3) else (if b 1 then 1 else 0)
  left_inv := by decide
  right_inv := by decide

def sgnB (b : Bool) : ℤ := if b then -1 else 1

theorem hZ_enc (u : ZMod 4) : hZ u = ∑ j, sgnB (enc4 u j) := by revert u; decide

/-- functions to Bool are subsets -/
def boolFinset (κ : Type*) [Fintype κ] [DecidableEq κ] : (κ → Bool) ≃ Finset κ where
  toFun η := univ.filter (fun k => η k = true)
  invFun A := fun k => decide (k ∈ A)
  left_inv η := by funext k; simp
  right_inv A := by ext k; simp

theorem sum_sgnB {κ : Type*} [Fintype κ] [DecidableEq κ] (η : κ → Bool) :
    ∑ k, sgnB (η k) = (Fintype.card κ : ℤ) - 2 * (boolFinset κ η).card := by
  have h := Finset.sum_filter_add_sum_filter_not univ (fun k => η k = true) (fun k => sgnB (η k))
  rw [← h, Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]; rfl : ∀ k ∈ univ.filter
      (fun k => η k = true), sgnB (η k) = -1),
    Finset.sum_congr rfl (fun k hk => by
      have := (Finset.mem_filter.1 hk).2; simp only [Bool.not_eq_true] at this; rw [this]; rfl :
        ∀ k ∈ univ.filter (fun k => ¬ η k = true), sgnB (η k) = 1)]
  simp only [sum_const, smul_eq_mul, mul_neg, mul_one, boolFinset, Equiv.coe_fn_mk]
  have hc := Finset.card_filter_add_card_filter_not (s := univ) (fun k => η k = true)
  rw [Finset.card_univ] at hc
  rw [← hc]; push_cast; ring

/-- **Σ_{q : ι → ZMod 4} |Σ_i 2Re(i^{q_i})| = 2m·C(2m,m)** with m = |ι| -/
theorem sum_abs_hZ (ι : Type) [Fintype ι] [DecidableEq ι] (hι : 1 ≤ Fintype.card ι) :
    ∑ q : ι → ZMod 4, |∑ i, hZ (q i)| = 2 * Fintype.card ι * (2 * Fintype.card ι).choose (Fintype.card ι) := by
  set m := Fintype.card ι
  -- (ι → ZMod 4) ≃ (ι × Fin 2 → Bool)
  let e : (ι → ZMod 4) ≃ (ι × Fin 2 → Bool) :=
    (Equiv.arrowCongr (Equiv.refl ι) enc4).trans (Equiv.curry ι (Fin 2) Bool).symm
  have hval : ∀ q : ι → ZMod 4, ∑ i, hZ (q i) = ∑ k, sgnB (e q k) := by
    intro q
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [hZ_enc]; rfl
  rw [Fintype.sum_equiv e _ (fun η => |∑ k, sgnB (η k)|) (fun q => by rw [hval])]
  rw [Fintype.sum_equiv (boolFinset (ι × Fin 2)) _ (fun A => |((2 * m : ℕ) : ℤ) - 2 * A.card|)
    (fun η => by rw [sum_sgnB]; simp [m, Fintype.card_prod]; ring_nf)]
  rw [← Finset.powerset_univ]
  have hp := Finset.sum_powerset_apply_card (fun k : ℕ => |((2 * m : ℕ) : ℤ) - 2 * (k : ℤ)|)
    (x := (univ : Finset (ι × Fin 2)))
  rw [hp, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, mul_comm m 2]
  have := rademacher_abs m hι
  simp only [nsmul_eq_mul] at this ⊢
  push_cast at this ⊢
  exact this

/-! ### phase states -/

variable {N : ℕ}

/-- the phase state ψ_ε = (i^{ε_c})_c -/
def psiE (ε : Bas N → ZMod 4) : Bas N → ℂ := fun c => iPow (ε c)

theorem normSq_iPow (k : ZMod 4) : Complex.normSq (iPow k) = 1 := by
  simp [iPow, map_pow, Complex.normSq_I]

theorem norm_psiE (ε : Bas N → ZMod 4) : ∑ c, Complex.normSq (psiE ε c) = 2 ^ N := by
  simp only [psiE, normSq_iPow, sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]; push_cast; ring

theorem psiE_ne_zero (ε : Bas N → ZMod 4) : psiE ε ≠ 0 := by
  intro h
  have := congrFun h 0
  exact iPow_ne_zero _ this

/-- ⟨ψ_ε|P_a|ψ_ε⟩ = Σ_c i^{y(a) + ε_c − ε_{c+x} + 2 z·c} -/
theorem quad_psiE (a : V N) (ε : Bas N → ZMod 4) :
    star (psiE ε) ⬝ᵥ (P a *ᵥ psiE ε) =
      ∑ c, iPow ((ycount a : ZMod 4) + ε c - ε (c + a.1) + dbl (dot a.2 c)) := by
  rw [quad_form, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  simp only [psiE]
  rw [conj_iPow, ← iPow_add, ← iPow_add, ← iPow_add]
  congr 1; ring

theorem two_dbl (t : F) : dbl t + dbl t = 0 := by rw [← dbl_add, add_self_F, dbl_zero]

theorem key_y (a : V N) : 2 * (ycount a : ZMod 4) + dbl (dot a.2 a.1) = 0 := by
  rw [two_mul_natCast, dot_snd_fst_self, two_dbl]

theorem hZ0 : hZ 0 = 2 := by decide
theorem hZ1 : hZ 1 = 0 := by decide
theorem hZ2 : hZ 2 = -2 := by decide
theorem hZ3 : hZ 3 = 0 := by decide

theorem iPow_pair (u : ZMod 4) : iPow u + iPow (-u) = ((hZ u : ℤ) : ℂ) := by
  have h4 : ∀ u : ZMod 4, u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by decide
  rcases h4 u with rfl | rfl | rfl | rfl
  · rw [neg_zero, iPow_zero, hZ0]; norm_num
  · rw [show -(1 : ZMod 4) = 3 from rfl, iPow_one, iPow_three, hZ1]; simp
  · rw [show -(2 : ZMod 4) = 2 from rfl, iPow_two, hZ2]; norm_num
  · rw [show -(3 : ZMod 4) = 1 from rfl, iPow_one, iPow_three, hZ3]; simp

section pairing

variable (a : V N) (k0 : Fin N) (hk0 : a.1 k0 = 1)

/-- the basis vectors with c_{k0} = 1 (one per pair {c, c + x}) -/
def Rc (k0 : Fin N) : Finset (Bas N) := univ.filter (fun c => c k0 = 1)

include hk0 in
theorem shift_k0 (c : Bas N) : (c + a.1) k0 = c k0 + 1 := by simp [hk0]

theorem F_ne_one {t : F} : t ≠ 1 ↔ t = 0 := by revert t; decide

include hk0 in
theorem sum_pair (f : Bas N → ℂ) : ∑ c, f c = ∑ c ∈ Rc k0, (f c + f (c + a.1)) := by
  rw [sum_add_distrib, ← sum_filter_add_sum_filter_not univ (fun c : Bas N => c k0 = 1)]
  congr 1
  refine Finset.sum_nbij' (fun c => c + a.1) (fun c => c + a.1) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    have hc' : ¬ c k0 = 1 := by simpa using hc
    have : (c + a.1) k0 = 1 := by rw [shift_k0 a k0 hk0, F_ne_one.1 hc', zero_add]
    simpa [Rc] using this
  · intro c hc
    have hc' : c k0 = 1 := by simpa [Rc] using hc
    have : ¬ (c + a.1) k0 = 1 := by rw [shift_k0 a k0 hk0, hc']; decide
    simpa using this
  · intro c _; show c + a.1 + a.1 = c; rw [add_assoc, add_self_V'', add_zero]
  · intro c _; show c + a.1 + a.1 = c; rw [add_assoc, add_self_V'', add_zero]
  · intro c _; show f c = f (c + a.1 + a.1); rw [add_assoc, add_self_V'', add_zero]

/-- the phase of the term c -/
def phs (ε : Bas N → ZMod 4) (c : Bas N) : ZMod 4 :=
  (ycount a : ZMod 4) + ε c - ε (c + a.1) + dbl (dot a.2 c)

theorem phs_partner (ε : Bas N → ZMod 4) (c : Bas N) : phs a ε (c + a.1) = -phs a ε c := by
  unfold phs
  rw [add_assoc c a.1 a.1, add_self_V'', add_zero, dot_add_right, dbl_add]
  have h1 := key_y a
  have h2 := two_dbl (dot a.2 c)
  linear_combination h1 + h2

include hk0 in
/-- the expectation value is a sum of `2 Re i^u` over the pairs -/
theorem ev_psiE (ε : Bas N → ZMod 4) : ev (psiE ε) a = ∑ c ∈ Rc k0, (hZ (phs a ε c) : ℝ) := by
  unfold ev
  rw [quad_psiE, sum_pair a k0 hk0]
  have : ∀ c ∈ Rc k0, iPow ((ycount a : ZMod 4) + ε c - ε (c + a.1) + dbl (dot a.2 c)) +
      iPow ((ycount a : ZMod 4) + ε (c + a.1) - ε (c + a.1 + a.1) + dbl (dot a.2 (c + a.1))) =
      ((hZ (phs a ε c) : ℤ) : ℂ) := by
    intro c _
    have := phs_partner a ε c
    unfold phs at this
    rw [this]; exact iPow_pair _
  rw [sum_congr rfl this, Complex.re_sum]
  refine sum_congr rfl fun c _ => ?_
  simp

/-- the change of variables ε ↦ (ε on the complement, the phases on `Rc`) -/
def phiE : (Bas N → ZMod 4) ≃ (Bas N → ZMod 4) where
  toFun ε c := if c k0 = 1 then phs a ε c else ε c
  invFun ε' c := if c k0 = 1 then ε' c - (ycount a : ZMod 4) - dbl (dot a.2 c) + ε' (c + a.1) else ε' c
  left_inv ε := by
    funext c
    by_cases hc : c k0 = 1
    · have : ¬ (c + a.1) k0 = 1 := by rw [shift_k0 a k0 hk0, hc]; decide
      simp only [hc, this, if_true, if_false, phs]; ring
    · simp [hc]
  right_inv ε' := by
    funext c
    by_cases hc : c k0 = 1
    · have : ¬ (c + a.1) k0 = 1 := by rw [shift_k0 a k0 hk0, hc]; decide
      simp only [hc, this, if_true, if_false, phs]; ring
    · simp [hc]

include hk0 in
theorem ev_phiE (ε : Bas N → ZMod 4) :
    ev (psiE ε) a = ∑ c ∈ Rc k0, (hZ (phiE a k0 hk0 ε c) : ℝ) := by
  rw [ev_psiE a k0 hk0]
  refine sum_congr rfl fun c hc => ?_
  have hc' : c k0 = 1 := (mem_filter.1 hc).2
  simp only [phiE, Equiv.coe_fn_mk, hc', if_true]

include hk0 in
theorem card_Rc : 2 * (Rc k0 : Finset (Bas N)).card = 2 ^ N := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Bas N))) (fun c => c k0 = 1)
  have hb : (univ.filter (fun c : Bas N => ¬ c k0 = 1)).card = (Rc k0 : Finset (Bas N)).card := by
    refine Finset.card_nbij' (fun c => c + a.1) (fun c => c + a.1) ?_ ?_ ?_ ?_
    · intro c hc
      have hc' : ¬ c k0 = 1 := by simpa using hc
      have : (c + a.1) k0 = 1 := by rw [shift_k0 a k0 hk0, F_ne_one.1 hc', zero_add]
      simpa [Rc] using this
    · intro c hc
      have hc' : c k0 = 1 := by simpa [Rc] using hc
      have : ¬ (c + a.1) k0 = 1 := by rw [shift_k0 a k0 hk0, hc']; decide
      simpa using this
    · intro c _; show c + a.1 + a.1 = c; rw [add_assoc, add_self_V'', add_zero]
    · intro c _; show c + a.1 + a.1 = c; rw [add_assoc, add_self_V'', add_zero]
  rw [hb, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
  unfold Rc at h ⊢; omega

include hk0 in
/-- **the average over phase states**: Σ_ε |⟨ψ_ε|P_a|ψ_ε⟩| = 4^m·2m·C(2m,m), m = 2^{N−1} -/
theorem sum_abs_ev (hN : 1 ≤ N) :
    ∑ ε : Bas N → ZMod 4, |ev (psiE ε) a| =
      (4 : ℝ) ^ (Rc k0 : Finset (Bas N)).card *
        (2 * (Rc k0 : Finset (Bas N)).card * (2 * (Rc k0 : Finset (Bas N)).card).choose
          (Rc k0 : Finset (Bas N)).card : ℕ) := by
  set m := (Rc k0 : Finset (Bas N)).card
  simp_rw [ev_phiE a k0 hk0]
  rw [Fintype.sum_equiv (phiE a k0 hk0) _ (fun ε' => |∑ c ∈ Rc k0, (hZ (ε' c) : ℝ)|) (fun _ => rfl)]
  -- split ε' into its values on Rc and on the complement
  let e := Equiv.piEquivPiSubtypeProd (fun c : Bas N => c k0 = 1) (fun _ => ZMod 4)
  rw [← Fintype.sum_equiv e.symm (fun qp => |∑ c ∈ Rc k0, (hZ (e.symm qp c) : ℝ)|) _ (fun _ => rfl)]
  have hq : ∀ qp : ((c : {c : Bas N // c k0 = 1}) → ZMod 4) × ((c : {c : Bas N // ¬ c k0 = 1}) → ZMod 4),
      ∑ c ∈ Rc k0, (hZ (e.symm qp c) : ℝ) = ∑ c : {c : Bas N // c k0 = 1}, (hZ (qp.1 c) : ℝ) := by
    intro qp
    rw [Finset.sum_subtype (Rc k0) (p := fun c : Bas N => c k0 = 1) (fun c => by simp [Rc])]
    refine sum_congr rfl fun c _ => ?_
    simp [e, Equiv.piEquivPiSubtypeProd, c.2]
  simp_rw [hq]
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [← mul_sum]
  have hcard : Fintype.card {c : Bas N // ¬ c k0 = 1} = m := by
    rw [Fintype.card_subtype]
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Bas N))) (fun c => c k0 = 1)
    have h2 := card_Rc a k0 hk0
    rw [card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
    have hm : m = (univ.filter (fun c : Bas N => c k0 = 1)).card := rfl
    omega
  have hcard' : Fintype.card {c : Bas N // c k0 = 1} = m := by
    rw [Fintype.card_subtype]; rfl
  rw [Fintype.card_fun, ZMod.card, hcard]
  have hm : 1 ≤ m := by
    have := card_Rc a k0 hk0
    have : 2 ≤ 2 ^ N := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    omega
  have hs := sum_abs_hZ {c : Bas N // c k0 = 1} (by rw [hcard']; exact hm)
  rw [hcard'] at hs
  have : ∑ q : {c : Bas N // c k0 = 1} → ZMod 4, |∑ c, (hZ (q c) : ℝ)| =
      ((2 * m * (2 * m).choose m : ℕ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hs
    push_cast at this ⊢
    rw [← this]
  rw [this]; push_cast; try ring

end pairing

/-! ### existence of a good phase state -/

/-- the Paulis with non-zero x-part -/
def A1 (N : ℕ) : Finset (V N) := univ.filter (fun a => a.1 ≠ 0)

theorem card_A1 (N : ℕ) : (A1 N).card = 4 ^ N - 2 ^ N := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (V N))) (fun a => a.1 ≠ 0)
  have h0 : (univ.filter (fun a : V N => ¬ a.1 ≠ 0)).card = 2 ^ N := by
    rw [show (univ.filter (fun a : V N => ¬ a.1 ≠ 0)) = (univ : Finset (Bas N)).image (fun z => (0, z)) by
      ext a; simp only [not_not, mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro h; exact ⟨a.2, Prod.ext h.symm rfl⟩
      · rintro ⟨z, rfl⟩; rfl]
    rw [card_image_of_injective _ (fun z z' h => by simpa using h), card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin]
  rw [card_univ, card_V, h0] at h
  unfold A1; omega

theorem exists_k0 {a : V N} (ha : a.1 ≠ 0) : ∃ k0, a.1 k0 = 1 := by
  by_contra h; push Not at h
  exact ha (funext fun k => F_ne_one.1 (h k))

theorem card_Rc_eq {a : V N} {k0 : Fin N} (hk0 : a.1 k0 = 1) (hN : 1 ≤ N) :
    (Rc k0 : Finset (Bas N)).card = 2 ^ (N - 1) := by
  have := card_Rc a k0 hk0
  have e : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- the averaged constant: Σ over all phase states of Σ_{a ∈ A1} |⟨P_a⟩| -/
theorem sum_A1 (hN : 1 ≤ N) :
    ∑ ε : Bas N → ZMod 4, ∑ a ∈ A1 N, |ev (psiE ε) a| =
      (A1 N).card * ((4 : ℝ) ^ 2 ^ (N - 1) * (2 * 2 ^ (N - 1) * (2 * 2 ^ (N - 1)).choose (2 ^ (N - 1)) : ℕ)) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (g := fun _ => (4 : ℝ) ^ 2 ^ (N - 1) *
      (2 * 2 ^ (N - 1) * (2 * 2 ^ (N - 1)).choose (2 ^ (N - 1)) : ℕ)) (fun a ha => by
    obtain ⟨k0, hk0⟩ := exists_k0 (mem_filter.1 ha).2
    rw [sum_abs_ev a k0 hk0 hN, card_Rc_eq hk0 hN])]
  rw [sum_const, nsmul_eq_mul]

/-- **a good phase state**: Σ_{a ∈ A1} |⟨ψ_ε|P_a|ψ_ε⟩| ≥ |A1|·2m·C(2m,m)/4^m, m = 2^{N−1} -/
theorem exists_good_phase (hN : 1 ≤ N) : ∃ ε : Bas N → ZMod 4,
    (A1 N).card * ((2 * 2 ^ (N - 1) * (2 * 2 ^ (N - 1)).choose (2 ^ (N - 1)) : ℕ) : ℝ) / 4 ^ 2 ^ (N - 1)
      ≤ ∑ a ∈ A1 N, |ev (psiE ε) a| := by
  set T : ℝ := (A1 N).card * ((4 : ℝ) ^ 2 ^ (N - 1) *
    (2 * 2 ^ (N - 1) * (2 * 2 ^ (N - 1)).choose (2 ^ (N - 1)) : ℕ))
  have hcard : (Fintype.card (Bas N → ZMod 4) : ℝ) = 4 ^ 2 ^ N := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fun, ZMod.card, Fintype.card_fin]; push_cast; ring
  have hsum := sum_A1 (N := N) hN
  have h4 : (4 : ℝ) ^ 2 ^ N = 4 ^ 2 ^ (N - 1) * 4 ^ 2 ^ (N - 1) := by
    rw [← pow_add]; congr 1
    rw [show 2 ^ N = 2 * 2 ^ (N - 1) by rw [← pow_succ']; congr 1; omega]; ring
  obtain ⟨ε, -, hε⟩ := Finset.exists_le_of_sum_le (s := univ) univ_nonempty
    (f := fun _ => T / 4 ^ 2 ^ N) (g := fun ε => ∑ a ∈ A1 N, |ev (psiE ε) a|) (by
      rw [sum_const, card_univ, nsmul_eq_mul, hcard, hsum]
      have : (0 : ℝ) < 4 ^ 2 ^ N := by positivity
      rw [mul_div_cancel₀ _ (ne_of_gt this)])
  refine ⟨ε, le_trans (le_of_eq ?_) hε⟩
  simp only [T]; rw [h4]; field_simp

/-! ### the spectral step -/

theorem quad_Mg (X : Finset (V N)) (g : V N → ℤ) (v : Bas N → ℂ) :
    (star v ⬝ᵥ (Mg X g *ᵥ v)).re = ∑ a ∈ X, (g a : ℝ) * ev v a := by
  classical
  unfold Mg
  induction X using Finset.induction_on with
  | empty => simp
  | insert a X ha ih =>
    rw [sum_insert ha, add_mulVec, dotProduct_add, Complex.add_re, ih, sum_insert ha, smul_mulVec,
      dotProduct_smul]
    simp [ev, Complex.mul_re]

/-- **ASY-5 (finite form).** With t = 2^N, F = t(t² − 1) and ℓ ≤ the normalised phase-state constant,
12·t·deg W(2N−1,2) ≤ 6·t·|L_N| − (ℓ√F)³ + (F − ℓ²F)^{3/2}. -/
theorem asy5_bound (hN : 1 ≤ N) (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ * Real.sqrt ((2 : ℝ) ^ N * (4 ^ N - 1)) ≤
      ((4 ^ N - 2 ^ N : ℕ) : ℝ) * (2 ^ N).choose (2 ^ (N - 1)) / 4 ^ 2 ^ (N - 1)) :
    12 * (2 : ℝ) ^ N * (W N).deg ≤ 6 * 2 ^ N * (W N).lines.card -
      (ℓ * Real.sqrt (2 ^ N * (4 ^ N - 1))) ^ 3 +
      p32 (2 ^ N * (4 ^ N - 1) - (ℓ * Real.sqrt (2 ^ N * (4 ^ N - 1))) ^ 2) := by
  obtain ⟨ε, hε⟩ := exists_good_phase (N := N) hN
  set v := psiE ε
  set lam := ℓ * Real.sqrt ((2 : ℝ) ^ N * (4 ^ N - 1))
  let s : V N → F := fun a => if 0 ≤ ev v a then 0 else 1
  set M := Mg (Wpts N) (gOf s)
  have h2N : (2 : ℕ) * 2 ^ (N - 1) = 2 ^ N := by rw [← pow_succ']; congr 1; omega
  have hgev : ∀ a, (gOf s a : ℝ) * ev v a = |ev v a| := by
    intro a
    simp only [gOf, pm, s]
    split_ifs with h1 h2 h2
    · simp [abs_of_nonneg h1]
    · exact absurd rfl h2
    · simp at h2
    · push Not at h1; simp [abs_of_neg h1]
  have hquad : (star v ⬝ᵥ (M *ᵥ v)).re = ∑ a ∈ Wpts N, |ev v a| := by
    rw [quad_Mg]; exact sum_congr rfl fun a _ => hgev a
  have hA1 : A1 N ⊆ Wpts N := fun a ha => by
    simp only [Wpts, mem_erase, mem_univ, and_true]; intro h; exact (mem_filter.1 ha).2 (by rw [h]; rfl)
  have hge : ∑ a ∈ A1 N, |ev v a| ≤ ∑ a ∈ Wpts N, |ev v a| :=
    sum_le_sum_of_subset_of_nonneg hA1 (fun _ _ _ => abs_nonneg _)
  have hnorm := norm_psiE ε
  have hlam : lam * ∑ i, Complex.normSq (v i) ≤ (star v ⬝ᵥ (M *ᵥ v)).re := by
    rw [hquad, hnorm]
    refine le_trans ?_ (le_trans hε hge)
    rw [card_A1, show (2 * 2 ^ (N - 1)) = 2 ^ N from h2N]
    have h : lam ≤ ((4 ^ N - 2 ^ N : ℕ) : ℝ) * (2 ^ N).choose (2 ^ (N - 1)) / 4 ^ 2 ^ (N - 1) := hℓ
    have hpos : (0 : ℝ) < 4 ^ 2 ^ (N - 1) := by positivity
    calc lam * 2 ^ N ≤ ((4 ^ N - 2 ^ N : ℕ) : ℝ) * (2 ^ N).choose (2 ^ (N - 1)) / 4 ^ 2 ^ (N - 1) * 2 ^ N :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by push_cast; ring
  have hcube := cube_trace_lower M (Mg_hermitian _ _) v (psiE_ne_zero ε) lam (by positivity) hlam
  have h2re : ((2 : ℂ) ^ N).re = 2 ^ N := by
    rw [show (2 : ℂ) ^ N = (((2 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  have h2im : ((2 : ℂ) ^ N).im = 0 := by
    rw [show (2 : ℂ) ^ N = (((2 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
  have htr2 : (M * M).trace.re = 2 ^ N * (4 ^ N - 1) := by
    rw [trace_Mg_sq _ _ (gOf_pm s), card_Wpts]
    have : 1 ≤ 4 ^ N := Nat.one_le_pow _ _ (by norm_num)
    rw [Complex.mul_re, h2re, h2im, zero_mul, sub_zero, Complex.natCast_re]
    push_cast [Nat.cast_sub this]; ring
  have htr3 := trace_cube_viol (Wpts N) (zero_not_mem_W N) s
  have hre : (M * M * M).trace.re = 2 ^ N * (6 * (W N).lines.card - 12 * ((W N).violated s).card) := by
    show (Mg (Wpts N) (gOf s) * Mg (Wpts N) (gOf s) * Mg (Wpts N) (gOf s)).trace.re = _
    rw [htr3, Complex.mul_re, h2re, h2im, zero_mul, sub_zero]
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
      sub_zero]
    norm_num
    rfl
  rw [htr2, hre] at hcube
  have hdeg : ((W N).deg : ℝ) ≤ ((W N).violated s).card := by exact_mod_cast (W N).deg_le s
  have h2pos : (0 : ℝ) < 2 ^ N := by positivity
  nlinarith

/-! ### constants: Wallis -/

/-- `w_M = C(2M,M)/4^M` -/
noncomputable def wM (M : ℕ) : ℝ := (2 * M).choose M / 4 ^ M

/-- **Wallis**: w_M² (2M+1) ≥ 2/π -/
theorem wallis_w (M : ℕ) : 2 / Real.pi ≤ wM M ^ 2 * (2 * M + 1) := by
  have hW := Real.Wallis.W_eq_factorial_ratio M
  have hle := Real.Wallis.W_le M
  have hpos := Real.Wallis.W_pos M
  have hc : ((2 * M).choose M : ℝ) * M.factorial * M.factorial = (2 * M).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show M ≤ 2 * M by omega)
    rw [show 2 * M - M = M by omega] at this
    exact_mod_cast this
  have hprod : wM M ^ 2 * (2 * M + 1) * Real.Wallis.W M = 1 := by
    rw [hW, wM]
    have h1 : (M.factorial : ℝ) ≠ 0 := by positivity
    have h3 : ((2 * M).choose M : ℝ) ≠ 0 := by
      have := Nat.choose_pos (show M ≤ 2 * M by omega); positivity
    rw [← hc]
    field_simp
    ring_nf
    rw [show (4 : ℝ) ^ (M * 2) = ((2 : ℝ) ^ 2) ^ (M * 2) by norm_num, ← pow_mul]; ring_nf
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_le_iff₀ hpi]
  have : wM M ^ 2 * (2 * M + 1) = 1 / Real.Wallis.W M := by
    field_simp; linarith [hprod]
  rw [this]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  linarith

/-- the explicit lower constant ℓ_N with ℓ_N² = (2/π)·t(t−1)/(t+1)², t = 2^N -/
noncomputable def ellN (N : ℕ) : ℝ :=
  Real.sqrt (2 / Real.pi * ((2 : ℝ) ^ N * (2 ^ N - 1) / (2 ^ N + 1) ^ 2))

theorem ellN_ok (hN : 1 ≤ N) :
    ellN N * Real.sqrt ((2 : ℝ) ^ N * (4 ^ N - 1)) ≤
      ((4 ^ N - 2 ^ N : ℕ) : ℝ) * (2 ^ N).choose (2 ^ (N - 1)) / 4 ^ 2 ^ (N - 1) := by
  set t : ℝ := 2 ^ N with ht
  set M := 2 ^ (N - 1)
  have hM' : 2 * M = 2 ^ N := by simp only [M]; rw [← pow_succ']; congr 1; omega
  have hM : (2 : ℝ) * M = t := by
    rw [ht]; exact_mod_cast hM'
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  have h4 : (4 : ℝ) ^ N = t ^ 2 := by rw [ht, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hcast : ((4 ^ N - 2 ^ N : ℕ) : ℝ) = t ^ 2 - t := by
    have : 2 ^ N ≤ 4 ^ N := Nat.pow_le_pow_left (by norm_num) N
    push_cast [this]; rw [h4]
  rw [hcast, h4, ← hM']
  rw [show ((t ^ 2 - t) * ((2 * M).choose M : ℝ) / 4 ^ M) = (t ^ 2 - t) * wM M by rw [wM]; ring]
  have hw := wallis_w M
  rw [hM] at hw
  have hwpos : 0 ≤ wM M := by unfold wM; positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold ellN
  rw [← Real.sqrt_mul (by positivity)]
  have hrhs : 0 ≤ (t ^ 2 - t) * wM M := mul_nonneg (by nlinarith) hwpos
  rw [← Real.sqrt_sq hrhs]
  apply Real.sqrt_le_sqrt
  -- (2/π) t²(t−1)²/(t+1) ≤ (t² − t)² w²
  have ht2 : 0 < t + 1 := by linarith
  have key : 2 / Real.pi * (t * (t - 1) / (t + 1) ^ 2) * (t * (t ^ 2 - 1)) =
      (t ^ 2 - t) ^ 2 * (2 / Real.pi / (t + 1)) := by
    field_simp; ring
  rw [key, mul_pow]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [div_le_iff₀ ht2]; exact hw

/-- φ(ℓ) = ℓ³ − (1 − ℓ²)^{3/2} -/
noncomputable def phiC (ℓ : ℝ) : ℝ := ℓ ^ 3 - p32 (1 - ℓ ^ 2)

theorem ellN_sq (N : ℕ) : ellN N ^ 2 = 2 / Real.pi * ((2 : ℝ) ^ N * (2 ^ N - 1) / (2 ^ N + 1) ^ 2) := by
  unfold ellN
  have ht1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  rw [Real.sq_sqrt (by have := Real.pi_pos; positivity)]

theorem ellN_sq_le_one (N : ℕ) : ellN N ^ 2 ≤ 1 := by
  rw [ellN_sq]
  have ht1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have h1 : (2 : ℝ) ^ N * (2 ^ N - 1) / (2 ^ N + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h2 : 2 / Real.pi ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ (2 : ℝ) ^ N * (2 ^ N - 1) / (2 ^ N + 1) ^ 2 := by
    apply div_nonneg _ (by positivity); nlinarith
  calc _ ≤ 1 * 1 := mul_le_mul h2 h1 h0 (by norm_num)
    _ = 1 := by norm_num

/-- **ASY-5.** (1/2 − ρ_N)·2^{N/2} ≥ φ(ℓ_N) for every N ≥ 2. -/
theorem delta_lower (hN : 2 ≤ N) : phiC (ellN N) ≤ (1 / 2 - rho N) * Real.sqrt (2 ^ N) := by
  have hℓ0 : 0 ≤ ellN N := Real.sqrt_nonneg _
  have hℓ1 : ellN N ^ 2 ≤ 1 := ellN_sq_le_one N
  have hb := asy5_bound (N := N) (by omega) (ellN N) hℓ0 (ellN_ok (by omega))
  have hL := lines_W N (by omega)
  set ℓ := ellN N
  set t : ℝ := 2 ^ N with ht
  have ht4 : 4 ≤ t := by
    rw [ht]; calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have h4 : (4 : ℝ) ^ N = t ^ 2 := by rw [ht, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4] at hb
  set F := t * (t ^ 2 - 1) with hF
  have hFpos : 0 < F := by rw [hF]; nlinarith
  have hsF : Real.sqrt F ^ 2 = F := Real.sq_sqrt hFpos.le
  have hl3 : (ℓ * Real.sqrt F) ^ 3 = F * Real.sqrt F * ℓ ^ 3 := by
    rw [mul_pow, show Real.sqrt F ^ 3 = Real.sqrt F ^ 2 * Real.sqrt F by ring, hsF]; ring
  have hp : p32 (F - (ℓ * Real.sqrt F) ^ 2) = F * Real.sqrt F * p32 (1 - ℓ ^ 2) := by
    rw [mul_pow, hsF, show F - ℓ ^ 2 * F = F * (1 - ℓ ^ 2) by ring, p32, p32,
      Real.sqrt_mul hFpos.le]; ring
  rw [hl3, hp] at hb
  have hLR : 12 * ((W N).lines.card : ℝ) = (t ^ 2 - 1) * (t ^ 2 - 4) := by
    have e1 : 1 ≤ 4 ^ N := Nat.one_le_pow _ _ (by norm_num)
    have e2 : 4 ≤ 4 ^ N := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : ((12 * (W N).lines.card : ℕ) : ℝ) = (((4 ^ N - 1) * (4 ^ N - 4) : ℕ) : ℝ) := by rw [hL]
    push_cast [Nat.cast_sub e1, Nat.cast_sub e2] at this
    rw [← h4]; linarith
  have hLpos : 0 < ((W N).lines.card : ℝ) := by nlinarith
  have hdelta : (1 / 2 - rho N) = (6 * t * (W N).lines.card - 12 * t * (W N).deg) /
      (12 * t * (W N).lines.card) := by
    unfold rho; field_simp; ring
  have hden : 12 * t * ((W N).lines.card : ℝ) = F * (t ^ 2 - 4) := by
    calc 12 * t * ((W N).lines.card : ℝ) = t * (12 * (W N).lines.card) := by ring
      _ = t * ((t ^ 2 - 1) * (t ^ 2 - 4)) := by rw [hLR]
      _ = F * (t ^ 2 - 4) := by rw [hF]; ring
  have hst : Real.sqrt t * Real.sqrt F = t * Real.sqrt (t ^ 2 - 1) := by
    rw [hF, ← Real.sqrt_mul (by linarith), show t * (t * (t ^ 2 - 1)) = t ^ 2 * (t ^ 2 - 1) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
  have hratio : t ^ 2 - 4 ≤ t * Real.sqrt (t ^ 2 - 1) := by
    have hs : (t ^ 2 - 4) ≤ Real.sqrt ((t ^ 2 - 1) * t ^ 2) := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    rw [Real.sqrt_mul (by nlinarith), Real.sqrt_sq (by linarith), mul_comm] at hs
    exact hs
  have hδ0 : 0 ≤ 1 / 2 - rho N := by linarith [rho_le_half N]
  by_cases hφ : phiC ℓ ≤ 0
  · exact le_trans hφ (mul_nonneg hδ0 (Real.sqrt_nonneg _))
  push Not at hφ
  have ht4' : 0 < t ^ 2 - 4 := by nlinarith
  rw [hdelta, hden, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hmain : F * Real.sqrt F * phiC ℓ ≤ 6 * t * (W N).lines.card - 12 * t * (W N).deg := by
    have e : F * Real.sqrt F * phiC ℓ = F * Real.sqrt F * ℓ ^ 3 - F * Real.sqrt F * p32 (1 - ℓ ^ 2) := by
      unfold phiC; ring
    rw [e]; linarith
  have hsq : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  calc phiC ℓ * (F * (t ^ 2 - 4)) = F * phiC ℓ * (t ^ 2 - 4) := by ring
    _ ≤ F * phiC ℓ * (t * Real.sqrt (t ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hratio (mul_pos hFpos hφ).le
    _ = F * Real.sqrt F * phiC ℓ * Real.sqrt t := by rw [← hst]; ring
    _ ≤ (6 * t * (W N).lines.card - 12 * t * (W N).deg) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right hmain hsq

/-! ### explicit consequences -/

theorem ellN_sq_ge (hN : 7 ≤ N) : 6218 / 10000 ≤ ellN N ^ 2 := by
  rw [ellN_sq]
  set t : ℝ := 2 ^ N
  have ht : 128 ≤ t := by
    calc (128 : ℝ) = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hg : 16256 / 16641 ≤ t * (t - 1) / (t + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have h2pi : 2 / 3.1416 ≤ 2 / Real.pi := by
    apply div_le_div_of_nonneg_left (by norm_num) Real.pi_pos hpi.le
  calc (6218 / 10000 : ℝ) ≤ (2 / 3.1416) * (16256 / 16641) := by norm_num
    _ ≤ 2 / Real.pi * (t * (t - 1) / (t + 1) ^ 2) :=
        mul_le_mul h2pi hg (by norm_num) (by positivity)

theorem phiC_ge (hN : 7 ≤ N) : 255 / 1000 ≤ phiC (ellN N) := by
  have h1 := ellN_sq_ge hN
  have h2 := ellN_sq_le_one N
  have hℓ0 : 0 ≤ ellN N := Real.sqrt_nonneg _
  have hℓ : 7885 / 10000 ≤ ellN N := by
    by_contra h; push Not at h; nlinarith
  have hx0 : 0 ≤ 1 - ellN N ^ 2 := by linarith
  have hx : 1 - ellN N ^ 2 ≤ 3782 / 10000 := by linarith
  have hsq : Real.sqrt (1 - ellN N ^ 2) ≤ 615 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hp : p32 (1 - ellN N ^ 2) ≤ 3782 / 10000 * (615 / 1000) :=
    mul_le_mul hx hsq (Real.sqrt_nonneg _) (by norm_num)
  have hc : 7885 / 10000 * (6218 / 10000) ≤ ellN N ^ 3 := by
    rw [show ellN N ^ 3 = ellN N * ellN N ^ 2 by ring]
    exact mul_le_mul hℓ h1 (by norm_num) hℓ0
  unfold phiC; nlinarith

/-- **ASY-5 (explicit rate).** For N ≥ 7:  0.255·2^{−N/2} ≤ 1/2 − ρ_N ≤ 2^{−N/2}. -/
theorem rate_explicit (hN : 7 ≤ N) :
    255 / 1000 / Real.sqrt (2 ^ N) ≤ 1 / 2 - rho N ∧ 1 / 2 - rho N ≤ 1 / Real.sqrt (2 ^ N) := by
  have hs : 0 < Real.sqrt ((2 : ℝ) ^ N) := Real.sqrt_pos.2 (by positivity)
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hs]
    exact le_trans (phiC_ge hN) (delta_lower (by omega))
  · have := W_lower N (by omega)
    unfold rho; linarith

/-- **ASY-7 (iii).** ρ_{N+4} > ρ_N for every N ≥ 7 (strict jump in every window of 4 steps). -/
theorem rho_window (hN : 7 ≤ N) : rho N < rho (N + 4) := by
  have h1 := (rate_explicit hN).1
  have h2 := W_lower (N + 4) (by omega)
  have hs : 0 < Real.sqrt ((2 : ℝ) ^ N) := Real.sqrt_pos.2 (by positivity)
  have e : Real.sqrt ((2 : ℝ) ^ (N + 4)) = 4 * Real.sqrt (2 ^ N) := by
    rw [pow_add, Real.sqrt_mul (by positivity), show ((2 : ℝ) ^ 4) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]; ring
  rw [e] at h2
  change (1 : ℝ) / 2 - 1 / (4 * Real.sqrt (2 ^ N)) ≤ rho (N + 4) at h2
  have : 1 / (4 * Real.sqrt ((2 : ℝ) ^ N)) < 255 / 1000 / Real.sqrt (2 ^ N) := by
    rw [div_lt_div_iff₀ (by positivity) hs]; nlinarith
  linarith

/-! ### the asymptotic constant -/

open Filter Topology in
theorem ellN_tendsto : Tendsto ellN atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have ht : Tendsto (fun N : ℕ => (2 : ℝ) ^ N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hinv : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp ht
  have hg : Tendsto (fun N : ℕ => (2 : ℝ) ^ N * (2 ^ N - 1) / (2 ^ N + 1) ^ 2) atTop (𝓝 1) := by
    have h : ∀ N : ℕ, (2 : ℝ) ^ N * (2 ^ N - 1) / (2 ^ N + 1) ^ 2 =
        (1 - ((2 : ℝ) ^ N)⁻¹) / (1 + ((2 : ℝ) ^ N)⁻¹) ^ 2 := by
      intro N
      have : (0 : ℝ) < 2 ^ N := by positivity
      field_simp
    simp_rw [h]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).div
      (((tendsto_const_nhds (x := (1 : ℝ))).add hinv).pow 2) (by norm_num)
    rw [sub_zero, add_zero, one_pow, div_one] at this
    exact this
  have := ((tendsto_const_nhds (x := 2 / Real.pi)).mul hg).sqrt
  rw [mul_one] at this
  exact this

open Filter Topology in
theorem phiC_continuous : Continuous phiC := by
  unfold phiC p32; fun_prop

open Filter Topology in
/-- **ASY-5 (asymptotic constant).** lim inf (1/2 − ρ_N)·2^{N/2} ≥ (2/π)^{3/2} − (1 − 2/π)^{3/2}: for every
κ below this constant, eventually κ ≤ (1/2 − ρ_N)·2^{N/2}. -/
theorem liminf_delta (κ : ℝ) (hκ : κ < phiC (Real.sqrt (2 / Real.pi))) :
    ∀ᶠ N in atTop, κ ≤ (1 / 2 - rho N) * Real.sqrt (2 ^ N) := by
  have hφ : Tendsto (fun N => phiC (ellN N)) atTop (𝓝 (phiC (Real.sqrt (2 / Real.pi)))) :=
    (phiC_continuous.tendsto _).comp ellN_tendsto
  filter_upwards [hφ.eventually (lt_mem_nhds hκ), eventually_ge_atTop 2] with N h1 h2
  exact le_trans h1.le (delta_lower h2)

end PauliCtx.Spectral
