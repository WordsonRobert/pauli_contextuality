/-
SpectralW.lean — the full symplectic geometry W(2N−1,2) (blueprint ASY-3, Target C).

  * `card_comm`   : a non-zero label commutes with exactly half of all labels.
  * `card_OP_W`, `lines_W` : 12·|L_N| = (4^N − 1)(4^N − 4).
  * `W_lower`     : deg W(2N−1,2) / |L_N| ≥ 1/2 − 1/√(2^N)   (= 1/2 − 2^{−N/2}).
  * `W_upper`     : deg W(2N−1,2) / |L_N| ≤ 1/2                 (ASY-0).
  * `rho_tendsto_half` : ρ_N → 1/2.                              (Target C)
-/
import PauliContextuality.SpectralConfig
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Matrix Complex Filter Topology

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-- the non-zero labels -/
def Wpts (N : ℕ) : Finset (V N) := Finset.univ.erase 0

theorem zero_not_mem_W (N : ℕ) : (0 : V N) ∉ Wpts N := Finset.notMem_erase _ _

/-- the configuration W(2N−1,2) -/
noncomputable def W (N : ℕ) : Config (V N) := configX (Wpts N) (zero_not_mem_W N)

theorem card_V (N : ℕ) : Fintype.card (V N) = 4 ^ N := by
  simp [Fintype.card_prod, Fintype.card_fun, ZMod.card, ← mul_pow]

theorem card_Wpts (N : ℕ) : (Wpts N).card = 4 ^ N - 1 := by
  rw [Wpts, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_V]

theorem omega_eq_dot (a b : V N) : omega a b = dot a.1 b.2 + dot a.2 b.1 := by
  unfold omega dot; rw [← Finset.sum_add_distrib]

/-- the symplectic character sum vanishes for `a ≠ 0` -/
theorem sum_char_omega {a : V N} (ha : a ≠ 0) : ∑ b : V N, iPow (dbl (omega a b)) = 0 := by
  have : ∀ b : V N, iPow (dbl (omega a b)) = iPow (dbl (dot a.2 b.1)) * iPow (dbl (dot a.1 b.2)) := by
    intro b; rw [omega_eq_dot, dbl_add, iPow_add, mul_comm]
  simp_rw [this]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_char, sum_char]
  by_cases h2 : a.2 = 0
  · have h1 : a.1 ≠ 0 := fun h1 => ha (Prod.ext h1 h2)
    simp [h1]
  · simp [h2]

/-- a non-zero label commutes with exactly half of all labels -/
theorem card_comm {a : V N} (ha : a ≠ 0) :
    2 * (Finset.univ.filter (fun b : V N => omega a b = 0)).card = 4 ^ N := by
  have hs := sum_char_omega ha
  have hsplit : ∑ b : V N, iPow (dbl (omega a b)) =
      ((Finset.univ.filter (fun b : V N => omega a b = 0)).card : ℂ) -
        (Finset.univ.filter (fun b : V N => ¬ omega a b = 0)).card := by
    have : ∀ b : V N, iPow (dbl (omega a b)) =
        (if omega a b = 0 then 1 else 0) - (if ¬ omega a b = 0 then 1 else 0) := by
      intro b; rw [iPow_dbl]; split_ifs <;> simp_all
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (V N)))
    (fun b => omega a b = 0)
  rw [Finset.card_univ, card_V] at htot
  rw [hsplit, sub_eq_zero] at hs
  have hs' : (Finset.univ.filter (fun b : V N => omega a b = 0)).card =
      (Finset.univ.filter (fun b : V N => ¬ omega a b = 0)).card := by exact_mod_cast hs
  omega

theorem card_OP_W (N : ℕ) (hN : 1 ≤ N) :
    2 * (OP (Wpts N)).card = (4 ^ N - 1) * (4 ^ N - 4) := by
  have hfib : ∀ a ∈ Wpts N, 2 * ((Wpts N).filter (fun b => omega a b = 0 ∧ a + b ∈ Wpts N)).card
      = 4 ^ N - 4 := by
    intro a ha
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    have hc := card_comm ha0
    -- remove b = 0 and b = a
    have hset : (Wpts N).filter (fun b => omega a b = 0 ∧ a + b ∈ Wpts N) =
        ((Finset.univ.filter (fun b : V N => omega a b = 0)).erase 0).erase a := by
      ext b
      simp only [Wpts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro ⟨hb, hω, hab⟩
        refine ⟨?_, hb, hω⟩
        intro h; apply hab; rw [h, add_self_V]
      · rintro ⟨hba, hb, hω⟩
        refine ⟨hb, hω, ?_⟩
        intro h; apply hba
        have := congrArg (a + ·) h; simpa [add_cancel_left'] using this
    have h0 : (0 : V N) ∈ Finset.univ.filter (fun b : V N => omega a b = 0) := by
      simp [omega]
    have hA : a ∈ (Finset.univ.filter (fun b : V N => omega a b = 0)).erase 0 := by
      simp [ha0, omega_self]
    rw [hset, Finset.card_erase_of_mem hA, Finset.card_erase_of_mem h0]
    have h4 : 4 ≤ 4 ^ N := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    omega
  have : (OP (Wpts N)).card =
      ∑ a ∈ Wpts N, ((Wpts N).filter (fun b => omega a b = 0 ∧ a + b ∈ Wpts N)).card := by
    rw [OP, Finset.card_filter, Finset.sum_product]
    simp_rw [Finset.card_filter]
  rw [this, Finset.mul_sum, Finset.sum_congr rfl hfib, Finset.sum_const, card_Wpts, smul_eq_mul]

/-- 12 |L_N| = (4^N − 1)(4^N − 4), i.e. |L_N| = (4^N−1)(4^{N−1}−1)/3. -/
theorem lines_W (N : ℕ) (hN : 1 ≤ N) : 12 * (W N).lines.card = (4 ^ N - 1) * (4 ^ N - 4) := by
  have h1 := card_OP_W N hN
  have h2 := six_mul_card (Wpts N) (zero_not_mem_W N)
  unfold W
  omega

/-- ASY-0 for W. -/
theorem W_upper (N : ℕ) : 2 * (W N).deg ≤ (W N).lines.card := (W N).deg_le_half

/-- ASY-3: deg W(2N−1,2)/|L_N| ≥ 1/2 − 1/√(2^N). -/
theorem W_lower (N : ℕ) (hN : 2 ≤ N) :
    (1 : ℝ) / 2 - 1 / Real.sqrt (2 ^ N) ≤ ((W N).deg : ℝ) / (W N).lines.card := by
  set d : ℝ := 2 ^ N with hd
  have hd4 : (4 : ℝ) ≤ d := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have h4N : ((4 ^ N : ℕ) : ℝ) = d ^ 2 := by
    push_cast; rw [hd, ← pow_mul, mul_comm, pow_mul]; norm_num
  have h4N1 : 1 ≤ 4 ^ N := Nat.one_le_pow _ _ (by norm_num)
  have h4N4 : 4 ≤ 4 ^ N := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  set n : ℝ := ((Wpts N).card : ℝ) with hn
  have hn' : n = d ^ 2 - 1 := by
    rw [hn, card_Wpts, Nat.cast_sub h4N1, h4N]; simp
  set L : ℝ := ((W N).lines.card : ℝ) with hL
  have hL' : 12 * L = n * (d ^ 2 - 4) := by
    have := lines_W N (by omega)
    have h' : ((12 * (W N).lines.card : ℕ) : ℝ) = (((4 ^ N - 1) * (4 ^ N - 4) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub h4N1, Nat.cast_sub h4N4] at h'
    rw [hL, hn', ← h4N]
    simpa using h'
  have hne : (Wpts N).Nonempty := Finset.card_pos.1 (by rw [card_Wpts]; omega)
  have hsl := spectral_lower (Wpts N) (zero_not_mem_W N) hne (by omega)
  simp only at hsl
  change L / 2 - (Real.sqrt (n * (d - 1)) * (d * n) - (d * n) ^ 2 / (d * Real.sqrt (n * (d - 1)))) /
      (12 * d) ≤ (W N).deg at hsl
  set Λ := Real.sqrt (n * (d - 1)) with hΛ
  have hn15 : 15 ≤ n := by rw [hn']; nlinarith
  have hΛpos : 0 < Λ := Real.sqrt_pos.2 (by nlinarith)
  have hΛ2 : Λ ^ 2 = n * (d - 1) := Real.sq_sqrt (by nlinarith)
  set sd := Real.sqrt d with hsd
  have hsdpos : 0 < sd := Real.sqrt_pos.2 (by linarith)
  have hsd2 : sd ^ 2 = d := Real.sq_sqrt (by linarith)
  have hdpos : 0 < d := by linarith
  -- the deficit term equals n²(d−2)/(12Λ)
  have hdef : (Λ * (d * n) - (d * n) ^ 2 / (d * Λ)) / (12 * d) = n ^ 2 * (d - 2) / (12 * Λ) := by
    field_simp
    rw [hΛ2]; ring
  -- n·√d ≤ (d+2)·Λ
  have hkey : n * sd ≤ (d + 2) * Λ := by
    have h1 : 0 ≤ n * sd := by positivity
    have h2 : 0 ≤ (d + 2) * Λ := by positivity
    rw [← pow_le_pow_iff_left₀ h1 h2 two_ne_zero, mul_pow, mul_pow, hsd2, hΛ2, hn']
    nlinarith [sq_nonneg d]
  have hLpos : 0 < L := by
    have : 0 < n * (d ^ 2 - 4) := by nlinarith
    linarith
  have hdef_le : n ^ 2 * (d - 2) / (12 * Λ) ≤ L / sd := by
    rw [div_le_div_iff₀ (by positivity) hsdpos]
    have : n ^ 2 * (d - 2) * sd = n * (d - 2) * (n * sd) := by ring
    rw [this]
    have hL12 : L * (12 * Λ) = n * (d - 2) * ((d + 2) * Λ) := by
      rw [show L * (12 * Λ) = (12 * L) * Λ by ring, hL']; ring
    rw [hL12]
    exact mul_le_mul_of_nonneg_left hkey (by nlinarith)
  rw [hdef] at hsl
  rw [le_div_iff₀ hLpos]
  have : (1 / 2 - 1 / sd) * L = L / 2 - L / sd := by field_simp
  rw [this]
  linarith

/-- the ratio ρ_N = deg W(2N−1,2) / |L_N| -/
noncomputable def rho (N : ℕ) : ℝ := ((W N).deg : ℝ) / (W N).lines.card

theorem rho_le_half (N : ℕ) : rho N ≤ 1 / 2 := by
  unfold rho
  have h := W_upper N
  rcases Nat.eq_zero_or_pos (W N).lines.card with h0 | hpos
  · rw [h0]; simp
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    have : (2 * (W N).deg : ℝ) ≤ (W N).lines.card := by exact_mod_cast h
    linarith

/-- **Target C (ASY-3):** lim ρ_N = 1/2. -/
theorem rho_tendsto_half : Tendsto rho atTop (𝓝 (1 / 2)) := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (2 ^ N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlow : Tendsto (fun N : ℕ => (1 : ℝ) / 2 - 1 / Real.sqrt (2 ^ N)) atTop (𝓝 (1 / 2)) := by
    have := (tendsto_inv_atTop_zero.comp hsqrt)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ) / 2)).sub this
    simpa [one_div] using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact W_lower N hN
  · exact Eventually.of_forall rho_le_half

end PauliCtx.Spectral
