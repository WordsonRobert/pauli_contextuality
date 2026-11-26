/-
TightConverse.lean — blueprint 11, TIGHT-1 direction (i) ⇒ (ii), and the equivalence.

  * `psd_mul_zero_of_trace` : A ⪰ 0, B Hermitian, tr(BAB) = 0 ⇒ AB = 0.
  * `cubic_eq_case` : equality in `cubic_trace_bound` forces (ΛI − M)(M + μI) = 0, μ = F/(dΛ).
  * `rank_one_of_idem` : a Hermitian idempotent of trace 1 is |v⟩⟨v| for a unit vector v.
  * `tight_converse` (TIGHT-1, (i) ⇒ (ii)) : if deg X equals the spectral bound, then for every
      optimal assignment s there is a unit vector ψ with ⟨ψ|P_a|ψ⟩ = γ·(−1)^{s(a)} on X
      (γ = √(n(d−1))/n, so γ²n = d − 1) and ⟨ψ|P_a|ψ⟩ = 0 off X ∪ {0}:
      the optimal assignments are exactly sign patterns of Pauli-flat states.
  * `tight_iff` : deg X = spectral bound ⟺ some unit vector is Pauli-flat exactly on X with γ²n = d − 1.
-/
import PauliContextuality.Tight
import Mathlib.Analysis.Matrix.Order

open Matrix Complex
open scoped ComplexOrder

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

section Equality

variable {d : Type} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
theorem trace_BAB (A B : Matrix d d ℂ) (hB : B.IsHermitian) :
    (B * A * B).trace = ∑ i, star (fun j => B j i) ⬝ᵥ (A *ᵥ (fun j => B j i)) := by
  simp only [Matrix.trace, diag, mul_apply, dotProduct, mulVec, Pi.star_apply, star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hBij : ∀ j, (starRingEnd ℂ) (B j i) = B i j := fun j => by
    have := congrFun (congrFun hB i) j
    simpa [conjTranspose_apply] using this
  simp_rw [hBij, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq d] in
/-- A ⪰ 0, B Hermitian, tr(BAB) = 0 ⇒ AB = 0 -/
theorem psd_mul_zero_of_trace (A B : Matrix d d ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian)
    (h : (B * A * B).trace = 0) : A * B = 0 := by
  rw [trace_BAB A B hB] at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ star (fun j => B j i) ⬝ᵥ (A *ᵥ (fun j => B j i)) :=
    fun i _ => hA.dotProduct_mulVec_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext j i
  have h1 := (hA.dotProduct_mulVec_zero_iff (fun j => B j i)).1 (hz i (Finset.mem_univ _))
  have h2 := congrFun h1 j
  simpa [mulVec, dotProduct, mul_apply] using h2

/-- equality in the cubic trace inequality -/
theorem cubic_eq_case [Nonempty d] (M : Matrix d d ℂ) (hM : M.IsHermitian) (Λ Fv : ℝ) (hΛ : 0 < Λ)
    (hpsd : ((Λ : ℂ) • (1 : Matrix d d ℂ) - M).PosSemidef)
    (htr : M.trace = 0) (htr2 : (M * M).trace = Fv)
    (heq : ((M * M * M).trace).re = Λ * Fv - Fv ^ 2 / (Fintype.card d * Λ)) :
    ((Λ : ℂ) • (1 : Matrix d d ℂ) - M) * (M + ((Fv / (Fintype.card d * Λ) : ℝ) : ℂ) • 1) = 0 := by
  set dd : ℝ := ((Fintype.card d : ℕ) : ℝ)
  have hd : 0 < dd := by simp [dd, Fintype.card_pos]
  set μ : ℝ := Fv / (dd * Λ)
  set B : Matrix d d ℂ := M + (μ : ℂ) • 1
  have hB : B.IsHermitian := by
    unfold IsHermitian
    simp only [B, conjTranspose_add, hM.eq, conjTranspose_smul, conjTranspose_one, star_def,
      Complex.conj_ofReal]
  refine psd_mul_zero_of_trace _ B hpsd hB ?_
  have hexp : B * ((Λ : ℂ) • 1 - M) * B =
      (Λ : ℂ) • (M * M) + (2 * Λ * μ : ℂ) • M + ((Λ * μ ^ 2 : ℝ) : ℂ) • 1 - M * M * M
        - (2 * μ : ℂ) • (M * M) - ((μ ^ 2 : ℝ) : ℂ) • M := by
    simp only [B, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one, smul_smul, smul_add, smul_sub]
    push_cast
    module
  have hherm : (B * ((Λ : ℂ) • 1 - M) * B).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, hB.eq, hpsd.1.eq, mul_assoc]
  rw [← trace_real_of_hermitian hherm, hexp]
  simp only [trace_sub, trace_add, trace_smul, trace_one, htr, htr2, smul_eq_mul, mul_zero,
    add_zero, sub_zero]
  have hμ : μ * (dd * Λ) = Fv := by simp only [μ]; field_simp
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.natCast_re, Complex.natCast_im, mul_zero, Complex.re_ofNat,
    Complex.im_ofNat]
  rw [heq]
  have : Λ * μ ^ 2 * dd - 2 * μ * Fv = - (Fv ^ 2 / (dd * Λ)) := by
    simp only [μ]; field_simp; ring
  have e2 : (2 * μ : ℂ).re = 2 * μ := by simp
  simp only [Complex.ofReal_eq_zero]
  nlinarith [this]

omit [DecidableEq d] in
/-- a Hermitian idempotent of trace 1 is a rank-one projector |v⟩⟨v| -/
theorem rank_one_of_idem (R : Matrix d d ℂ) (hR : R.IsHermitian) (hRR : R * R = R)
    (htr : R.trace = 1) : ∃ v : d → ℂ, ∑ i, Complex.normSq (v i) = 1 ∧ R = vecMulVec v (star v) := by
  have hconj : ∀ i j, (starRingEnd ℂ) (R j i) = R i j := fun i j => by
    have := congrFun (congrFun hR i) j
    simpa [conjTranspose_apply] using this
  have hdiag : ∀ i, R i i = ∑ j, ((Complex.normSq (R j i) : ℝ) : ℂ) := by
    intro i
    conv_lhs => rw [← hRR]
    rw [mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self, hconj]
  obtain ⟨i, hi⟩ : ∃ i, R i i ≠ 0 := by
    by_contra h
    push Not at h
    have : R.trace = 0 := Finset.sum_eq_zero fun i _ => h i
    rw [htr] at this; exact one_ne_zero this
  set c : ℝ := ∑ j, Complex.normSq (R j i)
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hcne : c ≠ 0 := by
    intro h; apply hi; rw [hdiag, ← Complex.ofReal_sum]; simp [c] at h ⊢; exact_mod_cast h
  have hc : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  set w : d → ℂ := fun j => R j i
  set v : d → ℂ := (((Real.sqrt c)⁻¹ : ℝ) : ℂ) • w
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hnorm : ∑ j, Complex.normSq (v j) = 1 := by
    simp only [v, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal, w]
    rw [← Finset.mul_sum]
    field_simp
    rw [hsc]
  have hvv : star v ⬝ᵥ v = 1 := by
    have : star v ⬝ᵥ v = ∑ j, ((Complex.normSq (v j) : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, star_def]
      exact Finset.sum_congr rfl fun j _ => by rw [Complex.normSq_eq_conj_mul_self]
    rw [this, ← Complex.ofReal_sum, hnorm]; simp
  have hRw : R *ᵥ w = w := by
    funext j
    show ∑ k, R j k * R k i = R j i
    rw [← mul_apply, hRR]
  have hRv : R *ᵥ v = v := by
    simp only [v, mulVec_smul, hRw]
  have hvR : star v ᵥ* R = star v := by
    have := congrArg star hRv
    rw [star_mulVec, hR.eq] at this
    exact this
  set P := vecMulVec v (star v)
  have hRP : R * P = P := by simp only [P, mul_vecMulVec, hRv]
  have hPR : P * R = P := by simp only [P, vecMulVec_mul, hvR]
  have hPP : P * P = P := by simp only [P, vecMulVec_mul_vecMulVec, hvv, one_smul]
  have hPH : P.IsHermitian := by
    unfold IsHermitian
    simp only [P, conjTranspose_vecMulVec, star_star]
  set S := R - P
  have hSS : Sᴴ * S = S := by
    have hSH : Sᴴ = S := by simp only [S, conjTranspose_sub, hR.eq, hPH.eq]
    rw [hSH]
    simp only [S, sub_mul, mul_sub, hRR, hRP, hPR, hPP]
    abel
  have htrS : S.trace = 0 := by
    simp only [S, trace_sub, htr, P, trace_vecMulVec]
    rw [show v ⬝ᵥ star v = star v ⬝ᵥ v from dotProduct_comm _ _, hvv, _root_.sub_self]
  have hS0 : S = 0 := (trace_conjTranspose_mul_self_eq_zero_iff).1 (by rw [hSS, htrS])
  exact ⟨v, hnorm, sub_eq_zero.1 hS0⟩

end Equality

/-! ### TIGHT-1, (i) ⇒ (ii) -/

theorem trace_vecMulVec_mul (v : Bas N → ℂ) (A : Matrix (Bas N) (Bas N) ℂ) :
    (vecMulVec v (star v) * A).trace = star v ⬝ᵥ (A *ᵥ v) := by
  simp only [Matrix.trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Pi.star_apply,
    star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem trace_Mg_mul_P (X : Finset (V N)) (g : V N → ℤ) (a : V N) :
    (Mg X g * P a).trace = if a ∈ X then 2 ^ N * (g a : ℂ) else 0 := by
  unfold Mg
  rw [Finset.sum_mul, trace_sum]
  simp_rw [smul_mul_assoc, trace_smul, trace_pauli_mul, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs <;> ring

/-- **TIGHT-1, (i) ⇒ (ii).** If deg X equals the spectral bound, every optimal assignment is the sign
pattern of a unit vector that is Pauli-flat exactly on X. -/
theorem tight_converse (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N)
    (hdeg : ((configX X h0).deg : ℝ) = ((configX X h0).lines.card : ℝ) / 2 -
        (X.card : ℝ) * Real.sqrt X.card * (2 ^ N - 2) / (12 * Real.sqrt (2 ^ N - 1)))
    (s : V N → F) (hs : ((configX X h0).violated s).card = (configX X h0).deg) :
    ∃ v : Bas N → ℂ, ∑ i, Complex.normSq (v i) = 1 ∧
      (∀ a ∈ X, ev v a = Real.sqrt (X.card * (2 ^ N - 1)) / X.card * gOf s a) ∧
      (∀ a, a ≠ 0 → a ∉ X → ev v a = 0) := by
  set n : ℝ := (X.card : ℝ)
  set dR : ℝ := 2 ^ N
  set Λ := Real.sqrt (n * (dR - 1))
  set Fv := dR * n
  set M := Mg X (gOf s)
  have hd2 : (2 : ℝ) ≤ dR := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hn : (0 : ℝ) < n := by simp only [n]; exact_mod_cast Finset.card_pos.2 hX
  have hΛ : 0 < Λ := Real.sqrt_pos.2 (by nlinarith)
  have hΛ2 : Λ ^ 2 = n * (dR - 1) := Real.sq_sqrt (by nlinarith)
  have hcard : ((Fintype.card (Bas N) : ℕ) : ℝ) = dR := by simp [dR, Fintype.card_fun, ZMod.card]
  -- the cubic trace equals the bound
  have htc := trace_cube_viol X h0 s
  rw [hs] at htc
  have hre : ((M * M * M).trace).re = Λ * Fv - Fv ^ 2 / (Fintype.card (Bas N) * Λ) := by
    rw [htc, hcard]
    have e1 : ((2 : ℂ) ^ N * (6 * ((configX X h0).lines.card : ℂ) - 12 * ((configX X h0).deg : ℂ))) =
        (((2 : ℝ) ^ N * (6 * ((configX X h0).lines.card : ℝ) - 12 * ((configX X h0).deg : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, Complex.ofReal_re, hdeg]
    have hdef := deficit_eq n dR hn hd2
    simp only [Λ, Fv]
    have hdpos : 0 < dR := by linarith
    rw [← hdef]
    field_simp
    ring
  have heq := cubic_eq_case M (Mg_hermitian X (gOf s)) Λ Fv hΛ (rayleigh X h0 (gOf s) (gOf_pm s))
    (trace_Mg X h0 (gOf s)) (by rw [trace_Mg_sq X (gOf s) (gOf_pm s)]; simp [Fv, dR, n]) hre
  rw [hcard] at heq
  set μ : ℝ := Fv / (dR * Λ)
  have hμ : μ = n / Λ := by simp only [μ, Fv]; field_simp
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hΛμ : Λ + μ = n * dR / Λ := by
    rw [hμ]; field_simp; rw [hΛ2]; ring
  have hΛμpos : 0 < Λ + μ := by positivity
  -- B := M + μ I satisfies B² = (Λ + μ) B
  have hMH : Mᴴ = M := (Mg_hermitian X (gOf s)).eq
  have hMtr : M.trace = 0 := trace_Mg X h0 (gOf s)
  set B : Matrix (Bas N) (Bas N) ℂ := M + (μ : ℂ) • 1
  have hA : (Λ : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ) - M = ((Λ + μ : ℝ) : ℂ) • 1 - B := by
    simp only [B]; push_cast; module
  have hBB : B * B = ((Λ + μ : ℝ) : ℂ) • B := by
    have h := heq
    rw [hA, sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at h
    exact h.symm
  set R : Matrix (Bas N) (Bas N) ℂ := (((Λ + μ)⁻¹ : ℝ) : ℂ) • B
  have hRH : R.IsHermitian := by
    unfold IsHermitian
    simp only [R, B, conjTranspose_smul, conjTranspose_add, hMH,
      conjTranspose_one, star_def, Complex.conj_ofReal]
  have hRR : R * R = R := by
    simp only [R, smul_mul_smul_comm, hBB, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have htrB : B.trace = (μ : ℂ) * dR := by
    simp only [B, trace_add, trace_smul, trace_one, hMtr, smul_eq_mul, zero_add]
    rw [card_bas]; simp [dR]
  have htrR : R.trace = 1 := by
    simp only [R, trace_smul, htrB, smul_eq_mul]
    have e : (Λ + μ)⁻¹ * (μ * dR) = 1 := by rw [hΛμ, hμ]; field_simp
    have : (((Λ + μ)⁻¹ : ℝ) : ℂ) * ((μ : ℂ) * (dR : ℂ)) = (((Λ + μ)⁻¹ * (μ * dR) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, e]; simp
  obtain ⟨v, hv, hRv⟩ := rank_one_of_idem R hRH hRR htrR
  -- M = (Λ + μ)|v⟩⟨v| − μ I
  have hM : M = ((Λ + μ : ℝ) : ℂ) • vecMulVec v (star v) - (μ : ℂ) • 1 := by
    rw [← hRv]
    simp only [R, smul_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hΛμpos.ne', Complex.ofReal_one, one_smul]
    simp only [B]; abel
  -- the Pauli coefficients
  have hcoef : ∀ a : V N, a ≠ 0 →
      (if a ∈ X then 2 ^ N * ((gOf s a : ℤ) : ℂ) else 0) =
        ((Λ + μ : ℝ) : ℂ) * star v ⬝ᵥ (P a *ᵥ v) := by
    intro a ha
    rw [← trace_Mg_mul_P X (gOf s) a]
    change (M * P a).trace = _
    rw [hM, sub_mul, trace_sub, smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul, one_mul,
      trace_pauli, if_neg ha, smul_zero, sub_zero, trace_vecMulVec_mul, smul_eq_mul]
  refine ⟨v, hv, fun a ha => ?_, fun a ha0 ha => ?_⟩
  · have h1 := hcoef a (fun h => h0 (h ▸ ha))
    rw [if_pos ha] at h1
    have hne : ((Λ + μ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΛμpos.ne'
    have hq : star v ⬝ᵥ (P a *ᵥ v) = (2 ^ N * ((gOf s a : ℤ) : ℂ)) / ((Λ + μ : ℝ) : ℂ) := by
      rw [h1]; field_simp
    unfold ev
    rw [hq]
    have e : (2 ^ N * ((gOf s a : ℤ) : ℂ)) / ((Λ + μ : ℝ) : ℂ) =
        (((2 : ℝ) ^ N * (gOf s a : ℝ) / (Λ + μ) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.ofReal_re, hΛμ]
    simp only [dR]
    field_simp
  · have h1 := hcoef a ha0
    rw [if_neg ha] at h1
    have hne : ((Λ + μ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΛμpos.ne'
    have h2 : star v ⬝ᵥ (P a *ᵥ v) = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hne
      · exact h
    unfold ev; rw [h2]; simp

/-- **TIGHT-1.** deg X equals the spectral bound iff some unit vector is Pauli-flat exactly on X,
with |⟨P_a⟩| = γ on X, ⟨P_a⟩ = 0 off X ∪ {0}, and γ²|X| = 2^N − 1. -/
theorem tight_iff (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N) :
    ((configX X h0).deg : ℝ) = ((configX X h0).lines.card : ℝ) / 2 -
        (X.card : ℝ) * Real.sqrt X.card * (2 ^ N - 2) / (12 * Real.sqrt (2 ^ N - 1)) ↔
      ∃ v : Bas N → ℂ, ∑ i, Complex.normSq (v i) = 1 ∧ ∃ γ : ℝ, 0 < γ ∧ γ ^ 2 * X.card = 2 ^ N - 1 ∧
        (∀ a ∈ X, |ev v a| = γ) ∧ (∀ a, a ≠ 0 → a ∉ X → ev v a = 0) := by
  constructor
  · intro hdeg
    obtain ⟨s, hs⟩ := (configX X h0).exists_opt
    obtain ⟨v, hv, hflat, hoff⟩ := tight_converse X h0 hX hN hdeg s hs
    have hn : (0 : ℝ) < X.card := by exact_mod_cast Finset.card_pos.2 hX
    have hd : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    have hd2 : (2 : ℝ) ≤ 2 ^ N := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
    set γ := Real.sqrt (X.card * (2 ^ N - 1)) / X.card
    have hγ : 0 < γ := div_pos (Real.sqrt_pos.2 (by nlinarith)) hn
    refine ⟨v, hv, γ, hγ, ?_, fun a ha => ?_, hoff⟩
    · simp only [γ]
      rw [div_pow, Real.sq_sqrt (by nlinarith)]
      field_simp
    · rw [hflat a ha, abs_mul, abs_of_pos hγ]
      have : |((gOf s a : ℤ) : ℝ)| = 1 := by
        rcases gOf_pm s a with h | h <;> rw [h] <;> simp
      rw [this, mul_one]
  · rintro ⟨v, hv, γ, hγ, hγ2, hflat, hoff⟩
    exact (tight_of_flat X h0 hN v hv γ hγ hflat hoff hγ2).2

end PauliCtx.Spectral
