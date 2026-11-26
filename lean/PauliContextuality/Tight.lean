/-
Tight.lean — blueprint 11, TIGHT-1 (direction (ii) ⇒ (i)) and NEG-1.

  * `pauli_expand` : the Pauli expansion of a rank-one matrix,
        Σ_a ⟨v|P_a|v⟩ P_a = 2^N |v⟩⟨v|.
  * `tight_of_flat` (TIGHT-1, (ii) ⇒ (i)) : if a unit vector ψ has |⟨ψ|P_a|ψ⟩| = γ on X,
        ⟨ψ|P_a|ψ⟩ = 0 off X ∪ {0}, and γ²|X| = 2^N − 1, then
          M_g = (2^N|ψ⟩⟨ψ| − I)/γ  for g = sign⟨P⟩,
        deg (configX X) equals the spectral bound |L|/2 − n^{3/2}(d−2)/(12√(d−1)), and g is optimal.
  * NEG-1 `B_mono`, `spectral_lower_of_valid`, `valid_ge_rayleigh`, `ceiling` : the ASY-2 bound with
        any valid Λ (ΛI − M_g ⪰ 0 for all g) is |L|/2 − B(Λ)/(12d), B(Λ) = ΛF − F²/(dΛ) is
        increasing, and a valid Λ is ≥ ⟨v|M_g|v⟩ for every unit v and every g.  So one explicit pair
        (g, v) caps everything the method can prove.  (The numerical ceilings 297 and 1488 of the
        blueprint are computed in `certificates/certify_asym.py`, X17.)
-/
import PauliContextuality.Density

open Matrix Complex
open scoped ComplexOrder

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-! ### the Pauli expansion of |v⟩⟨v| -/

theorem iPow_ycount_sq (a : V N) :
    iPow (ycount a) * iPow (ycount a) = iPow (dbl (dot a.1 a.2)) := by
  rw [← iPow_add, ← two_mul, two_mul_natCast, PauliCtx.ycount_cast a]
  congr 2

theorem pauli_expand (v : Bas N → ℂ) :
    ∑ a : V N, (star v ⬝ᵥ (P a *ᵥ v)) • P a = (2 ^ N : ℂ) • vecMulVec v (star v) := by
  ext r c
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply, star_def]
  rw [Fintype.sum_prod_type]
  -- only x = r + c contributes
  have hx : ∀ x : Bas N, x ≠ r + c →
      ∑ z : Bas N, (star v ⬝ᵥ (P (x, z) *ᵥ v)) * P (x, z) r c = 0 := by
    intro x hxne
    refine Finset.sum_eq_zero fun z _ => ?_
    have : ¬ r = c + x := by
      intro h; apply hxne; rw [h, add_comm c x, add_assoc, add_self_V'', add_zero]
    simp [P, this]
  rw [Finset.sum_eq_single (r + c) (fun x _ h => hx x h) (fun h => absurd (Finset.mem_univ _) h)]
  have hr : r = c + (r + c) := by rw [add_comm r c, ← add_assoc, add_self_V'', zero_add]
  -- expand the quadratic form
  have hterm : ∀ z : Bas N, (star v ⬝ᵥ (P (r + c, z) *ᵥ v)) * P (r + c, z) r c =
      ∑ c', (starRingEnd ℂ) (v (c' + (r + c))) * v c' * iPow (dbl (dot (r + c') z)) := by
    intro z
    rw [quad_form]
    simp only [P, of_apply, if_pos hr]
    rw [iPow_add, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c' _ => ?_
    have key : iPow (ycount ((r + c, z) : V N)) * iPow (ycount ((r + c, z) : V N)) =
        iPow (dbl (dot (r + c) z)) := iPow_ycount_sq (r + c, z)
    have e : dbl (dot (r + c') z) = dbl (dot (r + c) z) + dbl (dot z c') + dbl (dot z c) := by
      rw [← dbl_add, ← dbl_add]
      congr 1
      rw [dot_comm z c', dot_comm z c, dot_add_left, dot_add_left]
      have : dot c z + dot c z = 0 := add_self_F _
      linear_combination -this
    rw [e, iPow_add, iPow_add, ← key]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hch : ∀ c' : Bas N, ∑ z : Bas N, iPow (dbl (dot (r + c') z)) =
      if c' = r then (2 ^ N : ℂ) else 0 := by
    intro c'
    rw [sum_char, card_bas]
    congr 1
    apply propext
    constructor
    · intro h; have := congrArg (· + c') h; simpa [add_assoc, add_self_V''] using this.symm
    · intro h; rw [h, add_self_V'']
  simp_rw [hch, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ r, if_pos (Finset.mem_univ _)]
  rw [show r + (r + c) = c by rw [← add_assoc, add_self_V'', zero_add]]
  ring

/-! ### rank-one projector facts -/

theorem vecMulVec_sq (v : Bas N → ℂ) (hv : ∑ i, Complex.normSq (v i) = 1) :
    vecMulVec v (star v) * vecMulVec v (star v) = vecMulVec v (star v) := by
  ext r c
  simp only [mul_apply, vecMulVec_apply, Pi.star_apply, star_def]
  have : ∑ j, v r * (starRingEnd ℂ) (v j) * (v j * (starRingEnd ℂ) (v c)) =
      v r * (starRingEnd ℂ) (v c) * ∑ j, ((Complex.normSq (v j) : ℝ) : ℂ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [this, ← Complex.ofReal_sum, hv]; simp

theorem trace_vecMulVec_self (v : Bas N → ℂ) (hv : ∑ i, Complex.normSq (v i) = 1) :
    (vecMulVec v (star v)).trace = 1 := by
  simp only [Matrix.trace, diag, vecMulVec_apply, Pi.star_apply, star_def]
  have : ∑ i, v i * (starRingEnd ℂ) (v i) = ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [this, ← Complex.ofReal_sum, hv]; simp

/-! ### TIGHT-1, (ii) ⇒ (i) -/

/-- the sign pattern of a state: `g(a) = sign ⟨ψ|P_a|ψ⟩` (as an assignment, `0 ↦ +1`) -/
noncomputable def signOf (v : Bas N → ℂ) (a : V N) : F := if 0 ≤ ev v a then 0 else 1

theorem gOf_signOf_mul {v : Bas N → ℂ} {γ : ℝ} {a : V N} (h : |ev v a| = γ) :
    (gOf (signOf v) a : ℝ) * γ = ev v a := by
  unfold gOf signOf pm
  by_cases h0 : 0 ≤ ev v a
  · rw [if_pos h0, if_pos rfl, ← h, abs_of_nonneg h0]; simp
  · rw [if_neg h0, if_neg one_ne_zero, ← h, abs_of_neg (not_le.1 h0)]; simp

theorem ev_complex (v : Bas N → ℂ) (a : V N) : ((ev v a : ℝ) : ℂ) = star v ⬝ᵥ (P a *ᵥ v) :=
  quad_real _ (pauli_hermitian a) v

/-- step 1: γ M_g = 2^N |ψ⟩⟨ψ| − I -/
theorem flat_Mg (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (v : Bas N → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) (γ : ℝ)
    (hflat : ∀ a ∈ X, |ev v a| = γ) (hoff : ∀ a, a ≠ 0 → a ∉ X → ev v a = 0) :
    (γ : ℂ) • Mg X (gOf (signOf v)) = (2 ^ N : ℂ) • vecMulVec v (star v) - 1 := by
  rw [← pauli_expand v]
  have hsplit : ∑ a : V N, (star v ⬝ᵥ (P a *ᵥ v)) • P a =
      ∑ a ∈ insert 0 X, (star v ⬝ᵥ (P a *ᵥ v)) • P a := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
    have ha0 : a ≠ 0 := fun h => ha (h ▸ Finset.mem_insert_self _ _)
    have haX : a ∉ X := fun h => ha (Finset.mem_insert_of_mem h)
    rw [← ev_complex, hoff a ha0 haX]; simp
  rw [hsplit, Finset.sum_insert h0, ← ev_complex, norm2_eq, hv, P_zero]
  simp only [Complex.ofReal_one, one_smul, add_sub_cancel_left]
  unfold Mg
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [smul_smul, ← ev_complex, ← gOf_signOf_mul (hflat a ha)]
  push_cast; ring_nf

/-- step 2: γ³ tr M_g³ = d(d − 1)(d − 2) -/
theorem flat_trace_cube (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (v : Bas N → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) (γ : ℝ)
    (hflat : ∀ a ∈ X, |ev v a| = γ) (hoff : ∀ a, a ≠ 0 → a ∉ X → ev v a = 0) :
    (γ : ℂ) ^ 3 * (Mg X (gOf (signOf v)) * Mg X (gOf (signOf v)) * Mg X (gOf (signOf v))).trace =
      (2 ^ N : ℂ) * (2 ^ N - 1) * (2 ^ N - 2) := by
  set M := Mg X (gOf (signOf v))
  set ρ := vecMulVec v (star v)
  set d : ℂ := 2 ^ N
  have hM := flat_Mg X h0 v hv γ hflat hoff
  have hρ2 := vecMulVec_sq v hv
  have htr := trace_vecMulVec_self v hv
  have hcube : ((γ : ℂ) • M) * ((γ : ℂ) • M) * ((γ : ℂ) • M) =
      (d ^ 3 - 3 * d ^ 2 + 3 * d) • ρ - 1 := by
    rw [hM]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hρ2]
    module
  have h1 : ((γ : ℂ) • M * ((γ : ℂ) • M) * ((γ : ℂ) • M)).trace = (γ : ℂ) ^ 3 * (M * M * M).trace := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, trace_smul, smul_eq_mul]
    ring
  rw [← h1, hcube, trace_sub, trace_smul, htr, trace_one, card_bas]
  simp only [smul_eq_mul, mul_one]
  ring

/-- **TIGHT-1, (ii) ⇒ (i).** A unit vector that is Pauli-flat exactly on X with
γ²|X| = 2^N − 1 makes the spectral bound exact, and its sign pattern is an optimal assignment. -/
theorem tight_of_flat (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hN : 1 ≤ N) (v : Bas N → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) (γ : ℝ) (hγ : 0 < γ)
    (hflat : ∀ a ∈ X, |ev v a| = γ) (hoff : ∀ a, a ≠ 0 → a ∉ X → ev v a = 0)
    (hγ2 : γ ^ 2 * X.card = 2 ^ N - 1) :
    (configX X h0).deg = ((configX X h0).violated (signOf v)).card ∧
      ((configX X h0).deg : ℝ) = ((configX X h0).lines.card : ℝ) / 2 -
        (X.card : ℝ) * Real.sqrt X.card * (2 ^ N - 2) / (12 * Real.sqrt (2 ^ N - 1)) := by
  set n : ℝ := (X.card : ℝ)
  set d : ℝ := 2 ^ N
  set L : ℝ := ((configX X h0).lines.card : ℝ)
  set Vs : ℝ := (((configX X h0).violated (signOf v)).card : ℝ)
  have hd2 : (2 : ℝ) ≤ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this] at hγ2; linarith
  have hX : X.Nonempty := by
    rw [← Finset.card_pos]; have : (0 : ℝ) < (X.card : ℝ) := hn; exact_mod_cast this
  -- the trace identity in real form
  have htc := flat_trace_cube X h0 v hv γ hflat hoff
  rw [trace_cube_viol X h0 (signOf v)] at htc
  have hreal : γ ^ 3 * (d * (6 * L - 12 * Vs)) = d * (d - 1) * (d - 2) := by
    have := congrArg Complex.re htc
    simp only [d, L, Vs]
    have e1 : ((γ : ℂ) ^ 3 * (2 ^ N * (6 * ((configX X h0).lines.card : ℂ) -
        12 * ((configX X h0).violated (signOf v)).card))) =
        ((γ ^ 3 * (2 ^ N * (6 * ((configX X h0).lines.card : ℝ) -
        12 * ((configX X h0).violated (signOf v)).card)) : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((2 : ℂ) ^ N * (2 ^ N - 1) * (2 ^ N - 2)) =
        (((2 : ℝ) ^ N * (2 ^ N - 1) * (2 ^ N - 2) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.ofReal_re, Complex.ofReal_re] at this
    exact this
  -- γ √n = √(d − 1)
  have hd1 : 0 < d - 1 := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hsd2 : Real.sqrt (d - 1) ^ 2 = d - 1 := Real.sq_sqrt hd1.le
  have hsd : 0 < Real.sqrt (d - 1) := Real.sqrt_pos.2 hd1
  have hγn : γ * Real.sqrt n = Real.sqrt (d - 1) := by
    have h1 : (γ * Real.sqrt n) ^ 2 = d - 1 := by rw [mul_pow, hsn2]; exact hγ2
    rw [← h1, Real.sqrt_sq (by positivity)]
  have hV : Vs = L / 2 - n * Real.sqrt n * (d - 2) / (12 * Real.sqrt (d - 1)) := by
    have hdpos : 0 < d := by linarith
    have h3 : γ ^ 3 * (6 * L - 12 * Vs) = (d - 1) * (d - 2) := by
      have := hreal
      have : d * (γ ^ 3 * (6 * L - 12 * Vs)) = d * ((d - 1) * (d - 2)) := by linarith
      exact mul_left_cancel₀ hdpos.ne' this
    -- γ³ n √n = (d−1) √(d−1)
    have h4 : γ ^ 3 * (n * Real.sqrt n) = (d - 1) * Real.sqrt (d - 1) := by
      have : γ ^ 3 * (n * Real.sqrt n) = (γ ^ 2 * n) * (γ * Real.sqrt n) := by ring
      rw [this, hγ2, hγn]
    have hγ3 : 0 < γ ^ 3 := by positivity
    have h5 : γ ^ 3 * (12 * Real.sqrt (d - 1) * Vs) =
        γ ^ 3 * (6 * Real.sqrt (d - 1) * L - (d - 2) * (n * Real.sqrt n)) := by
      linear_combination (-Real.sqrt (d - 1)) * h3 + (d - 2) * h4
    have h6 := mul_left_cancel₀ hγ3.ne' h5
    have hs12 : 0 < 12 * Real.sqrt (d - 1) := by positivity
    calc Vs = (6 * Real.sqrt (d - 1) * L - (d - 2) * (n * Real.sqrt n)) / (12 * Real.sqrt (d - 1)) := by
          rw [eq_div_iff hs12.ne']; linarith [h6]
      _ = L / 2 - n * Real.sqrt n * (d - 2) / (12 * Real.sqrt (d - 1)) := by field_simp; ring
  have hlow := den1 X h0 hX hN
  have hup : ((configX X h0).deg : ℝ) ≤ Vs := by
    simp only [Vs]; exact_mod_cast (configX X h0).deg_le (signOf v)
  have heq : ((configX X h0).deg : ℝ) = Vs := le_antisymm hup (by rw [hV]; exact hlow)
  refine ⟨by simp only [Vs] at heq; exact_mod_cast heq, ?_⟩
  rw [heq, hV]

/-! ### NEG-1: the ceiling of the single-moment spectral method -/

/-- `B(Λ) = ΛF − F²/(dΛ)` -/
noncomputable def Bfun (F d Λ : ℝ) : ℝ := Λ * F - F ^ 2 / (d * Λ)

/-- **NEG-1.** B is increasing in Λ > 0 (for F ≥ 0, d > 0). -/
theorem B_mono (F d : ℝ) (hF : 0 ≤ F) (hd : 0 < d) {Λ₁ Λ₂ : ℝ} (h1 : 0 < Λ₁) (h12 : Λ₁ ≤ Λ₂) :
    Bfun F d Λ₁ ≤ Bfun F d Λ₂ := by
  unfold Bfun
  have h2 : 0 < Λ₂ := lt_of_lt_of_le h1 h12
  have : F ^ 2 / (d * Λ₂) ≤ F ^ 2 / (d * Λ₁) :=
    div_le_div_of_nonneg_left (sq_nonneg F) (by positivity) (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_right h12 hF]

/-- `Λ` is *valid* for X if ΛI − M_g ⪰ 0 for every ±1 pattern g -/
def ValidΛ (X : Finset (V N)) (Λ : ℝ) : Prop :=
  ∀ g : V N → ℤ, IsPM g → ((Λ : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ) - Mg X g).PosSemidef

/-- the Cauchy–Schwarz value √(n(d − 1)) is valid (ASY-2 step 1) -/
theorem valid_sqrt (X : Finset (V N)) (h0 : (0 : V N) ∉ X) :
    ValidΛ X (Real.sqrt (X.card * (2 ^ N - 1))) := fun g hg => rayleigh X h0 g hg

/-- ASY-2 with any valid Λ: deg ≥ |L|/2 − B(Λ)/(12d) -/
theorem spectral_lower_of_valid (X : Finset (V N)) (h0 : (0 : V N) ∉ X)
    (Λ : ℝ) (hΛ : 0 < Λ) (hvalid : ValidΛ X Λ) :
    ((configX X h0).lines.card : ℝ) / 2 - Bfun (2 ^ N * X.card) (2 ^ N) Λ / (12 * 2 ^ N) ≤
      (configX X h0).deg := by
  obtain ⟨s, hs⟩ := (configX X h0).exists_opt
  rw [← hs]
  have hcard : ((Fintype.card (Bas N) : ℕ) : ℝ) = 2 ^ N := by
    simp [ZMod.card]
  have hb := cubic_trace_bound (Mg X (gOf s)) (Mg_hermitian X (gOf s)) Λ (2 ^ N * X.card) hΛ
    (hvalid _ (gOf_pm s)) (trace_Mg X h0 (gOf s))
    (by rw [trace_Mg_sq X (gOf s) (gOf_pm s)]; push_cast; ring)
  rw [hcard, trace_cube_viol X h0 s] at hb
  have hre : ((2 : ℂ) ^ N * (6 * ((configX X h0).lines.card : ℂ) - 12 * ((configX X h0).violated s).card)).re
      = 2 ^ N * (6 * (configX X h0).lines.card - 12 * ((configX X h0).violated s).card) := by
    rw [show ((2 : ℂ) ^ N * (6 * ((configX X h0).lines.card : ℂ) - 12 * ((configX X h0).violated s).card))
        = (((2 : ℝ) ^ N * (6 * ((configX X h0).lines.card : ℝ) - 12 * ((configX X h0).violated s).card) : ℝ) : ℂ)
        by push_cast; ring, Complex.ofReal_re]
  rw [hre] at hb
  unfold Bfun
  have hdpos : (0 : ℝ) < 12 * 2 ^ N := by positivity
  have key : (((configX X h0).lines.card : ℝ) / 2 - ((configX X h0).violated s).card) * (12 * 2 ^ N) ≤
      Λ * (2 ^ N * X.card) - (2 ^ N * X.card) ^ 2 / (2 ^ N * Λ) := by
    have e : (((configX X h0).lines.card : ℝ) / 2 - ((configX X h0).violated s).card) * (12 * 2 ^ N) =
        2 ^ N * (6 * ((configX X h0).lines.card : ℝ) - 12 * ((configX X h0).violated s).card) := by ring
    rw [e]; exact hb
  have h2 := (le_div_iff₀ hdpos).2 key
  linarith

/-- **NEG-1.** a valid Λ is at least the Rayleigh quotient ⟨v|M_g|v⟩ of every unit vector, for
every g (in particular Λ ≥ λ_max(M_g)) -/
theorem valid_ge_rayleigh (X : Finset (V N)) (Λ : ℝ) (hvalid : ValidΛ X Λ) (g : V N → ℤ) (hg : IsPM g)
    (v : Bas N → ℂ) (hv : ∑ i, Complex.normSq (v i) = 1) :
    (star v ⬝ᵥ (Mg X g *ᵥ v)).re ≤ Λ := by
  have h := (hvalid g hg).dotProduct_mulVec_nonneg v
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, sub_nonneg] at h
  have hvv : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, star_def, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_conj_mul_self]
  rw [hvv, hv, Complex.ofReal_one, smul_eq_mul, mul_one] at h
  have := (Complex.le_def.1 h).1
  simpa using this

/-- **NEG-1 (ceiling).** If some ±1 pattern g₀ and unit vector v have Rayleigh quotient λ₀ > 0,
then the bound of ASY-2 with any valid Λ is at most |L|/2 − B(λ₀)/(12d). -/
theorem ceiling (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (Λ : ℝ) (hvalid : ValidΛ X Λ) (g₀ : V N → ℤ) (hg₀ : IsPM g₀)
    (v : Bas N → ℂ) (hv : ∑ i, Complex.normSq (v i) = 1) (hlam : 0 < (star v ⬝ᵥ (Mg X g₀ *ᵥ v)).re) :
    ((configX X h0).lines.card : ℝ) / 2 - Bfun (2 ^ N * X.card) (2 ^ N) Λ / (12 * 2 ^ N) ≤
      ((configX X h0).lines.card : ℝ) / 2 -
        Bfun (2 ^ N * X.card) (2 ^ N) (star v ⬝ᵥ (Mg X g₀ *ᵥ v)).re / (12 * 2 ^ N) := by
  have hle := valid_ge_rayleigh X Λ hvalid g₀ hg₀ v hv
  have hB := B_mono (2 ^ N * X.card) (2 ^ N) (by positivity) (by positivity) hlam hle
  have : (0 : ℝ) < 12 * 2 ^ N := by positivity
  have := div_le_div_of_nonneg_right hB this.le
  linarith

end PauliCtx.Spectral
