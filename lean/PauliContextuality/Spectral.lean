/-
Spectral.lean — the trace formula and the spectral lower bound (blueprint/10_asymptotics.md, ASY-0..ASY-7).

Encoding (changed from the original skeleton, which used bit-packed `Fin (4^N)` labels): labels are
`V N` from Basic.lean and Pauli matrices are `P a` from PauliMatrix.lean, indexed by `Fin N → F`.
This makes the Pauli algebra a few lines of Finset algebra and avoids popcount arithmetic.

Design: everything is a TRACE inequality. No spectral theorem, no eigenvalues.
  * ASY-1 trace formula   : `trace_cube` + `trace_cube_comm` (anticommuting pairs cancel).
  * ASY-2 spectral bound  : `rayleigh` (PosSemidef(ΛI − M) from Pauli completeness + Cauchy–Schwarz)
                            and `cubic_trace_bound` (tr[(M+μI)(ΛI−M)(M+μI)] ≥ 0).
  * ASY-7 strict jumps    : `infinitely_many_strict_jumps`.
-/
import PauliContextuality.PauliMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Matrix Complex
open scoped ComplexOrder

namespace PauliCtx.Spectral

variable {N : ℕ}

/-- `g` takes values ±1 -/
def IsPM (g : V N → ℤ) : Prop := ∀ a, g a = 1 ∨ g a = -1

theorem IsPM.sq {g : V N → ℤ} (hg : IsPM g) (a : V N) : (g a : ℂ) * g a = 1 := by
  rcases hg a with h | h <;> simp [h]

/-- an assignment-weighted sum of Paulis over a label set X -/
noncomputable def Mg (X : Finset (V N)) (g : V N → ℤ) : Matrix (Bas N) (Bas N) ℂ :=
  ∑ a ∈ X, (g a : ℂ) • P a

theorem Mg_hermitian (X : Finset (V N)) (g : V N → ℤ) : (Mg X g).IsHermitian := by
  unfold Mg IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conjTranspose_smul, (pauli_hermitian a).eq]
  simp

theorem trace_Mg (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (g : V N → ℤ) : (Mg X g).trace = 0 := by
  unfold Mg
  rw [trace_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hne : a ≠ 0 := fun h => h0 (h ▸ ha)
  rw [trace_smul, trace_pauli, if_neg hne, smul_zero]

theorem trace_Mg_sq (X : Finset (V N)) (g : V N → ℤ) (hg : IsPM g) :
    (Mg X g * Mg X g).trace = 2 ^ N * X.card := by
  unfold Mg
  rw [Finset.sum_mul_sum, trace_sum]
  simp_rw [trace_sum, smul_mul_smul_comm, trace_smul, trace_pauli_mul]
  have : ∀ a ∈ X, ∑ b ∈ X, ((g a : ℂ) * g b) • (if a = b then (2 ^ N : ℂ) else 0) = 2 ^ N := by
    intro a ha
    simp only [smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq X a, if_pos ha, hg.sq, one_mul]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- product of three Paulis -/
theorem trace_pauli_mul3 (a b c : V N) :
    (P a * P b * P c).trace = if a + b = c then iPow (ph a b) * 2 ^ N else 0 := by
  rw [pauli_mul, smul_mul_assoc, trace_smul, trace_pauli_mul, smul_eq_mul]
  split_ifs <;> simp

/-- ASY-1 step 1–2: only triples with `c = a + b` contribute. -/
theorem trace_cube (X : Finset (V N)) (g : V N → ℤ) :
    (Mg X g * Mg X g * Mg X g).trace =
      2 ^ N * ∑ a ∈ X, ∑ b ∈ X,
        if a + b ∈ X then (g a : ℂ) * g b * g (a + b) * iPow (ph a b) else 0 := by
  unfold Mg
  rw [Finset.sum_mul_sum, Finset.sum_mul, trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, trace_sum]
  simp_rw [smul_mul_smul_comm, trace_smul, trace_pauli_mul3, smul_eq_mul]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs <;> ring

theorem one_add_iPow_dbl (t : F) : 1 + iPow (dbl t) = if t = 0 then 2 else 0 := by
  rw [iPow_dbl]; split_ifs <;> norm_num

/-- ASY-1 step 3: anticommuting ordered pairs cancel against their reverses. -/
theorem sum_ph_symm (X : Finset (V N)) (w : V N → V N → ℂ) (hw : ∀ a b, w a b = w b a) :
    ∑ a ∈ X, ∑ b ∈ X, w a b * iPow (ph a b) =
      ∑ a ∈ X, ∑ b ∈ X, if omega a b = 0 then w a b * iPow (ph a b) else 0 := by
  set S := ∑ a ∈ X, ∑ b ∈ X, w a b * iPow (ph a b)
  have hS : S = ∑ a ∈ X, ∑ b ∈ X, w a b * iPow (ph a b) * iPow (dbl (omega a b)) := by
    rw [show S = ∑ a ∈ X, ∑ b ∈ X, w b a * iPow (ph b a) from Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hw b a, ph_swap b a, iPow_add, omega_comm b a]; ring
  have h2 : (2 : ℂ) * S = 2 * ∑ a ∈ X, ∑ b ∈ X, if omega a b = 0 then w a b * iPow (ph a b) else 0 := by
    rw [two_mul]
    nth_rewrite 2 [hS]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := one_add_iPow_dbl (omega a b)
    by_cases h : omega a b = 0
    · rw [if_pos h] at this ⊢; linear_combination (w a b * iPow (ph a b)) * this
    · rw [if_neg h] at this ⊢; linear_combination (w a b * iPow (ph a b)) * this
  exact mul_left_cancel₀ two_ne_zero h2

/-- the sign of a commuting pair as a real number -/
def chi (a b : V N) : ℤ := if ph a b = 0 then 1 else -1

theorem red_ph (a b : V N) : red (ph a b) = omega a b := by
  unfold ph
  rw [map_sub, map_add, map_add, red_dbl, add_zero, map_natCast, map_natCast, map_natCast,
    ycount_cast, ycount_cast, ycount_cast, qplus_add]
  generalize qplus a = x; generalize qplus b = y; generalize omega a b = z
  revert x y z; decide

theorem iPow_ph_comm {a b : V N} (h : omega a b = 0) : iPow (ph a b) = (chi a b : ℂ) := by
  have h' := red_ph a b
  rw [h] at h'
  rcases eq_zero_or_two_of_red h' with h0 | h2
  · simp [chi, h0]
  · rw [h2]; simp only [chi, h2]; rw [if_neg (by decide), iPow_two]; simp

/-- ASY-1 (ordered-pair form): `tr M³ = 2^N Σ_{a,b ∈ X, ω(a,b)=0, a+b ∈ X} χ(a,b) g_a g_b g_{a+b}`. -/
theorem trace_cube_comm (X : Finset (V N)) (g : V N → ℤ) :
    (Mg X g * Mg X g * Mg X g).trace =
      2 ^ N * ∑ a ∈ X, ∑ b ∈ X,
        if omega a b = 0 ∧ a + b ∈ X then ((chi a b * g a * g b * g (a + b) : ℤ) : ℂ) else 0 := by
  rw [trace_cube]
  congr 1
  have := sum_ph_symm X (fun a b => if a + b ∈ X then (g a : ℂ) * g b * g (a + b) else 0)
    (fun a b => by rw [add_comm b a]; split_ifs <;> ring)
  simp only [ite_mul, zero_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : omega a b = 0
  · by_cases h2 : a + b ∈ X
    · simp only [h1, h2, if_true, and_self, iPow_ph_comm h1]; push_cast; ring
    · simp [h1, h2]
  · simp [h1]

/-! ### ASY-2: the cubic trace inequality -/

theorem trace_real_of_hermitian {d : Type} [Fintype d] {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    ((A.trace).re : ℂ) = A.trace := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    rw [Matrix.trace, Complex.im_sum]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    have := congrFun (congrFun hA i) i
    simp only [conjTranspose_apply, star_def] at this
    have h2 := congrArg Complex.im this
    rw [Complex.conj_im] at h2
    simp only [diag]
    linarith

/-- the cubic trace inequality: for Hermitian M with tr M = 0, tr M² = F and ΛI − M ⪰ 0 (Λ > 0),
    tr M³ ≤ ΛF − F²/(dΛ). -/
theorem cubic_trace_bound {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (M : Matrix d d ℂ) (hM : M.IsHermitian)
    (Λ Fv : ℝ) (hΛ : 0 < Λ)
    (hpsd : ((Λ : ℂ) • (1 : Matrix d d ℂ) - M).PosSemidef)
    (htr : M.trace = 0) (htr2 : (M * M).trace = Fv) :
    ((M * M * M).trace).re ≤ Λ * Fv - Fv ^ 2 / (Fintype.card d * Λ) := by
  set dd : ℝ := ((Fintype.card d : ℕ) : ℝ)
  have hd : 0 < dd := by simp [dd, Fintype.card_pos]
  set μ : ℝ := Fv / (dd * Λ)
  set B : Matrix d d ℂ := M + (μ : ℂ) • 1
  have hB : Bᴴ = B := by
    simp only [B, conjTranspose_add, hM.eq, conjTranspose_smul, conjTranspose_one, star_def,
      Complex.conj_ofReal]
  have hpos := (hpsd.conjTranspose_mul_mul_same B).trace_nonneg
  rw [hB] at hpos
  -- expand B (ΛI − M) B
  have hexp : B * ((Λ : ℂ) • 1 - M) * B =
      (Λ : ℂ) • (M * M) + (2 * Λ * μ : ℂ) • M + ((Λ * μ ^ 2 : ℝ) : ℂ) • 1 - M * M * M
        - (2 * μ : ℂ) • (M * M) - ((μ ^ 2 : ℝ) : ℂ) • M := by
    simp only [B, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one, smul_smul, smul_add, smul_sub]
    push_cast
    module
  rw [hexp] at hpos
  simp only [trace_sub, trace_add, trace_smul, trace_one, htr, htr2, smul_eq_mul, mul_zero,
    add_zero, sub_zero] at hpos
  have hre := (Complex.nonneg_iff.1 hpos).1
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.natCast_re, Complex.natCast_im, mul_zero] at hre
  have hμ : μ * (dd * Λ) = Fv := by simp only [μ]; field_simp
  have key : ((M * M * M).trace).re ≤ Λ * Fv + Λ * μ ^ 2 * dd - 2 * μ * Fv := by
    have : (2 * μ : ℂ).re = 2 * μ := by simp
    simp only [Complex.re_ofNat, Complex.im_ofNat] at hre
    nlinarith [hre]
  have : Λ * μ ^ 2 * dd - 2 * μ * Fv = - (Fv ^ 2 / (dd * Λ)) := by
    simp only [μ]; field_simp; ring
  linarith

/-! ### ASY-2: the Rayleigh bound -/

theorem quad_real (A : Matrix (Bas N) (Bas N) ℂ) (hA : A.IsHermitian) (v : Bas N → ℂ) :
    (((star v ⬝ᵥ (A *ᵥ v)).re : ℝ) : ℂ) = star v ⬝ᵥ (A *ᵥ v) := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    exact (hA.im_star_dotProduct_mulVec_self v).symm

/-- `e_a = ⟨v|P_a|v⟩` (real) -/
noncomputable def ev (v : Bas N → ℂ) (a : V N) : ℝ := (star v ⬝ᵥ (P a *ᵥ v)).re

theorem norm2_eq (v : Bas N → ℂ) : ev v 0 = ∑ i, Complex.normSq (v i) := by
  simp only [ev, P_zero, one_mulVec, dotProduct, Pi.star_apply, star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem sum_ev_sq (v : Bas N → ℂ) :
    ∑ a : V N, ev v a ^ 2 = 2 ^ N * (∑ i, Complex.normSq (v i)) ^ 2 := by
  have h := pauli_completeness v
  have h2 : ∀ a : V N, Complex.normSq (star v ⬝ᵥ (P a *ᵥ v)) = ev v a ^ 2 := by
    intro a
    rw [← quad_real _ (pauli_hermitian a) v, Complex.normSq_ofReal, sq]; rfl
  simp_rw [h2] at h
  exact_mod_cast h

/-- Rayleigh bound: `Λ·I − M_g` is positive semidefinite, `Λ = √(|X|(d − 1))`. -/
theorem rayleigh (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (g : V N → ℤ) (hg : IsPM g) :
    ((Real.sqrt (X.card * (2 ^ N - 1)) : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ) - Mg X g).PosSemidef := by
  set Λ := Real.sqrt (X.card * (2 ^ N - 1))
  have hH : ((Λ : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ) - Mg X g).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_sub, (Mg_hermitian X g).eq, conjTranspose_smul, conjTranspose_one]
    simp
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun v => ?_
  set nv : ℝ := ∑ i, Complex.normSq (v i)
  -- the quadratic form is real
  rw [← quad_real _ hH v]
  apply Complex.zero_le_real.2
  have hsplit : (star v ⬝ᵥ (((Λ : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ) - Mg X g) *ᵥ v)).re =
      Λ * nv - ∑ a ∈ X, (g a : ℝ) * ev v a := by
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec, one_mulVec, dotProduct_smul]
    unfold Mg
    rw [sum_mulVec, dotProduct_sum, Complex.re_sum]
    congr 1
    · have := norm2_eq v
      simp only [ev, P_zero, one_mulVec] at this
      rw [smul_eq_mul, Complex.re_ofReal_mul, this]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp [ev, Complex.mul_re]
  rw [hsplit, sub_nonneg]
  -- Σ g_a e_a ≤ Σ |e_a| ≤ √|X| · √(Σ e_a²) ≤ √|X| · √((d−1) nv²) = Λ nv
  have h1 : ∑ a ∈ X, (g a : ℝ) * ev v a ≤ ∑ a ∈ X, |ev v a| := by
    refine Finset.sum_le_sum fun a _ => ?_
    rcases hg a with h | h <;> simp [h, le_abs_self, neg_le_abs]
  have hcs := sq_sum_le_card_mul_sum_sq (s := X) (f := fun a => |ev v a|)
  have h3 : ∑ a ∈ X, |ev v a| ^ 2 ≤ (2 ^ N - 1) * nv ^ 2 := by
    have hall := sum_ev_sq v
    have hsub : ∑ a ∈ X, ev v a ^ 2 ≤ ∑ a ∈ (Finset.univ.erase (0 : V N)), ev v a ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha => Finset.mem_erase.2 ⟨fun h => h0 (h ▸ ha), Finset.mem_univ _⟩)
        (fun _ _ _ => sq_nonneg _)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V N)), norm2_eq] at hall
    simp_rw [sq_abs]
    linarith
  have hnv : 0 ≤ nv := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have habs : 0 ≤ ∑ a ∈ X, |ev v a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hd1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  -- (Σ|e|)² ≤ |X| (d−1) nv² = (Λ nv)²
  have hsq : (∑ a ∈ X, |ev v a|) ^ 2 ≤ (Λ * nv) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc (∑ a ∈ X, |ev v a|) ^ 2 ≤ X.card * ∑ a ∈ X, |ev v a| ^ 2 := hcs
      _ ≤ X.card * ((2 ^ N - 1) * nv ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = X.card * (2 ^ N - 1) * nv ^ 2 := by ring
  have hΛnv : 0 ≤ Λ * nv := mul_nonneg (Real.sqrt_nonneg _) hnv
  have : ∑ a ∈ X, |ev v a| ≤ Λ * nv := by nlinarith [hsq, habs, hΛnv]
  linarith

/-! ### ASY-7 (ii): strict jumps -/

/-- A non-decreasing real sequence with ρ_N < 1/2 for all N and ρ_N → 1/2 is not eventually constant. -/
theorem infinitely_many_strict_jumps (ρ : ℕ → ℝ) (hmono : Monotone ρ) (hlt : ∀ N, ρ N < 1 / 2)
    (hlim : Filter.Tendsto ρ Filter.atTop (nhds (1 / 2))) :
    ∀ N₀, ∃ N ≥ N₀, ρ N < ρ (N + 1) := by
  intro N₀
  by_contra h
  push Not at h
  have hconst : ∀ N ≥ N₀, ρ N = ρ N₀ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ k hk ih => exact (le_antisymm (h k hk) (hmono (Nat.le_succ k))).trans ih
  have : Filter.Tendsto ρ Filter.atTop (nhds (ρ N₀)) :=
    tendsto_const_nhds.congr' (Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop N₀)
      (fun N hN => (hconst N hN).symm))
  have := tendsto_nhds_unique hlim this
  linarith [hlt N₀]

end PauliCtx.Spectral
