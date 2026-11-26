/-
Chain.lean — blueprint 10, ASY-7 (iv) extended: the strict chain ρ₅ < ρ₆ < … < ρ₁₁
(together with GEO-6 `rho_chain`: ρ₂ = ρ₃ < ρ₄ < ρ₅, so ρ₃ < ρ₄ < … < ρ₁₁).

Upper bounds on ρ_N: product witnesses (ASY-6 Cor. 2, Tensor.lean; new here: N = 10 = 4+3+3).
Lower bounds on ρ_{N+1}: ASY-2 (`spectral_lower'`) with Λ₀ = ⌊√((4^{N+1}−1)(2^{N+1}−1))⌋.
All comparisons are exact rational arithmetic (`certify_asym.py`, X9).
-/
import PauliContextuality.Tensor

namespace PauliCtx.Spectral

open Config

/-- **N = 10 (4+3+3).** deg W(19,2) ≤ 43768473840. -/
theorem W19_le : (W 10).deg ≤ 43768473840 := by
  set w := witnessAssign 3 (fun _ => true) witnessW5
  set u := arrAssign (N := 4) arrW7
  have h7 := tau_mul u w witW7_zero witW5_zero
  have h10 := tau_mul (sjoin u w) w (sjoin_zero witW7_zero witW5_zero) witW5_zero
  rw [h7, tau3, tau4] at h10
  have h := deg_W_le_tau (N := 4 + 3 + 3) (sjoin (sjoin u w) w)
  rw [h10, lines_W_int (4 + 3 + 3) (by norm_num) 91625532075 (by decide)] at h
  change (W (4 + 3 + 3)).deg ≤ _
  generalize (W (4 + 3 + 3)).deg = D at h ⊢
  norm_num at h
  omega

/-- the ASY-2 lower bound with an integer Λ₀, in the form used below -/
theorem W_ge_of (N : ℕ) (hN : 1 ≤ N) (L n : ℕ) (hL : (W N).lines.card = L) (hn : 4 ^ N - 1 = n)
    (Λ₀ : ℕ) (hΛ₀ : 0 < Λ₀) (hle : Λ₀ ^ 2 ≤ n * (2 ^ N - 1)) :
    (L : ℝ) / 2 - (n : ℝ) ^ 2 * (2 ^ N - 2) / (12 * Λ₀) ≤ (W N).deg := by
  have hne : (Wpts N).Nonempty := Finset.card_pos.1 (by
    rw [card_Wpts]; have : 4 ≤ 4 ^ N := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    omega)
  have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  have hle' : ((Λ₀ : ℝ)) ^ 2 ≤ ((Wpts N).card : ℝ) * (2 ^ N - 1) := by
    rw [card_Wpts, hn]
    have : ((Λ₀ ^ 2 : ℕ) : ℝ) ≤ ((n * (2 ^ N - 1) : ℕ) : ℝ) := by exact_mod_cast hle
    push_cast [Nat.cast_sub h1] at this
    exact this
  have h := spectral_lower' (Wpts N) (zero_not_mem_W N) hne hN Λ₀ (by exact_mod_cast hΛ₀) hle'
  change ((W N).lines.card : ℝ) / 2 - _ ≤ (W N).deg at h
  rw [hL, card_Wpts, hn] at h
  exact h

theorem W11_ge : 527310 ≤ (W 6).deg := by
  have h := W_ge_of 6 (by norm_num) 1396395 4095 (lines_W_int 6 (by norm_num) _ (by decide))
    (by norm_num) 507 (by norm_num) (by norm_num)
  have : (527309 : ℝ) < (W 6).deg := by
    generalize ((W 6).deg : ℝ) = D at h ⊢; norm_num at h; linarith
  have : 527309 < (W 6).deg := by exact_mod_cast this
  omega

theorem W13_ge : 9227009 ≤ (W 7).deg := by
  have h := W_ge_of 7 (by norm_num) 22362795 16383 (lines_W_int 7 (by norm_num) _ (by decide))
    (by norm_num) 1442 (by norm_num) (by norm_num)
  have : (9227008 : ℝ) < (W 7).deg := by
    generalize ((W 7).deg : ℝ) = D at h ⊢; norm_num at h; linarith
  have : 9227008 < (W 7).deg := by exact_mod_cast this
  omega

theorem W15_ge : 156700263 ≤ (W 8).deg := by
  have h := W_ge_of 8 (by norm_num) 357886635 65535 (lines_W_int 8 (by norm_num) _ (by decide))
    (by norm_num) 4087 (by norm_num) (by norm_num)
  have : (156700262 : ℝ) < (W 8).deg := by
    generalize ((W 8).deg : ℝ) = D at h ⊢; norm_num at h; linarith
  have : 156700262 < (W 8).deg := by exact_mod_cast this
  omega

theorem W17_ge : 2610897506 ≤ (W 9).deg := by
  have h := W_ge_of 9 (by norm_num) 5726513835 262143 (lines_W_int 9 (by norm_num) _ (by decide))
    (by norm_num) 11573 (by norm_num) (by norm_num)
  have : (2610897505 : ℝ) < (W 9).deg := by
    generalize ((W 9).deg : ℝ) = D at h ⊢; norm_num at h; linarith
  have : 2610897505 < (W 9).deg := by exact_mod_cast this
  omega

theorem W19_ge : 42953569015 ≤ (W 10).deg := by
  have h := W_ge_of 10 (by norm_num) 91625532075 1048575 (lines_W_int 10 (by norm_num) _ (by decide))
    (by norm_num) 32751 (by norm_num) (by norm_num)
  have : (42953569014 : ℝ) < (W 10).deg := by
    generalize ((W 10).deg : ℝ) = D at h ⊢; norm_num at h; linarith
  have : 42953569014 < (W 10).deg := by exact_mod_cast this
  omega

theorem W21_ge : 700635858598 ≤ (W 11).deg := by
  have h := W_ge_of 11 (by norm_num) 1466013756075 4194303
    (lines_W_int 11 (by norm_num) _ (by decide)) (by norm_num) 92659 (by norm_num) (by norm_num)
  have : (700635858597 : ℝ) < (W 11).deg := by
    generalize ((W 11).deg : ℝ) = D at h ⊢; norm_num at h; linarith
  have : 700635858597 < (W 11).deg := by exact_mod_cast this
  omega

theorem rho_bounds (N : ℕ) (L lo up : ℕ) (hL : (W N).lines.card = L) (hpos : 0 < L)
    (hlo : lo ≤ (W N).deg) (hup : (W N).deg ≤ up) :
    (lo : ℝ) / L ≤ rho N ∧ rho N ≤ (up : ℝ) / L := by
  unfold rho; rw [hL]
  have hL' : (0 : ℝ) < L := by exact_mod_cast hpos
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hlo) hL'.le
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hup) hL'.le

theorem rho_lower (N : ℕ) (L lo : ℕ) (hL : (W N).lines.card = L) (hpos : 0 < L)
    (hlo : lo ≤ (W N).deg) : (lo : ℝ) / L ≤ rho N := by
  unfold rho; rw [hL]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hlo) (by exact_mod_cast hpos.le)

theorem rho_upper (N : ℕ) (L up : ℕ) (hL : (W N).lines.card = L) (hpos : 0 < L)
    (hup : (W N).deg ≤ up) : rho N ≤ (up : ℝ) / L := by
  unfold rho; rw [hL]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hup) (by exact_mod_cast hpos.le)

/-- **ASY-7 (iv), extended.** ρ₅ < ρ₆ < ρ₇ < ρ₈ < ρ₉ < ρ₁₀ < ρ₁₁. -/
theorem rho_chain_ext :
    rho 5 < rho 6 ∧ rho 6 < rho 7 ∧ rho 7 < rho 8 ∧ rho 8 < rho 9 ∧ rho 9 < rho 10 ∧
      rho 10 < rho 11 := by
  have L5 := card_lines_W5
  have L6 := lines_W_int 6 (by norm_num) 1396395 (by decide)
  have L7 := lines_W_int 7 (by norm_num) 22362795 (by decide)
  have L8 := lines_W_int 8 (by norm_num) 357886635 (by decide)
  have L9 := lines_W_int 9 (by norm_num) 5726513835 (by decide)
  have L10 := lines_W_int 10 (by norm_num) 91625532075 (by decide)
  have L11 := lines_W_int 11 (by norm_num) 1466013756075 (by decide)
  have u5 := rho_upper 5 _ _ L5 (by norm_num) W9_le_31479
  have u6 := rho_upper 6 _ _ L6 (by norm_num) W11_le
  have u7 := rho_upper 7 _ _ L7 (by norm_num) W13_le
  have u8 := rho_upper 8 _ _ L8 (by norm_num) W15_le
  have u9 := rho_upper 9 _ _ L9 (by norm_num) W17_le
  have u10 := rho_upper 10 _ _ L10 (by norm_num) W19_le
  have l6 := rho_lower 6 _ _ L6 (by norm_num) W11_ge
  have l7 := rho_lower 7 _ _ L7 (by norm_num) W13_ge
  have l8 := rho_lower 8 _ _ L8 (by norm_num) W15_ge
  have l9 := rho_lower 9 _ _ L9 (by norm_num) W17_ge
  have l10 := rho_lower 10 _ _ L10 (by norm_num) W19_ge
  have l11 := rho_lower 11 _ _ L11 (by norm_num) W21_ge
  push_cast at u5 u6 u7 u8 u9 u10 l6 l7 l8 l9 l10 l11
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [show (31479 : ℝ) / 86955 < 527310 / 1396395 by norm_num]
  · linarith [show (553140 : ℝ) / 1396395 < 9227009 / 22362795 by norm_num]
  · linarith [show (9641268 : ℝ) / 22362795 < 156700263 / 357886635 by norm_num]
  · linarith [show (162635700 : ℝ) / 357886635 < 2610897506 / 5726513835 by norm_num]
  · linarith [show (2669910768 : ℝ) / 5726513835 < 42953569015 / 91625532075 by norm_num]
  · linarith [show (43768473840 : ℝ) / 91625532075 < 700635858598 / 1466013756075 by norm_num]

/-- **ASY-7 (iv).** ρ₂ = ρ₃ < ρ₄ < ρ₅ < … < ρ₁₁. -/
theorem rho_strict_chain :
    rho 2 = rho 3 ∧ rho 3 < rho 4 ∧ rho 4 < rho 5 ∧ rho 5 < rho 6 ∧ rho 6 < rho 7 ∧ rho 7 < rho 8 ∧
      rho 8 < rho 9 ∧ rho 9 < rho 10 ∧ rho 10 < rho 11 := by
  obtain ⟨h1, h2, h3, h4⟩ := rho_chain
  obtain ⟨c5, c6, c7, c8, c9, c10⟩ := rho_chain_ext
  exact ⟨h1, h2, lt_of_le_of_lt h3 h4, c5, c6, c7, c8, c9, c10⟩

end PauliCtx.Spectral
