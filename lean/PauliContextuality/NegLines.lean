/-
NegLines.lean — blueprint ASY-6, Corollary 1, and Target A without the monotonicity hypothesis.

  * `sum_P_eq_kron` : Σ_a P_a = t^{⊗N}, where t = I + X + Y + Z = [[2, 1−i], [1+i, 0]].
  * `trace_kron_mul` : traces of products of Kronecker powers factorise.
  * `viol_zero`    : the all-(+1) assignment violates exactly |L_N|/2 − (10^N − 3·4^N + 2)/12 lines.
  * `neg_lines`    : #{ℓ ∈ W(2N−1,2) : χ(ℓ) = −1} = (16^N + 4^N − 2·10^N)/24.
  * `rho_lt_half`  : ρ_N < 1/2 for every N.
  * `rho_strict_jumps` : **Target A** — ρ_N < ρ_{N+1} for infinitely many N (no monotonicity needed).
-/
import PauliContextuality.SpectralW

open Matrix Complex Filter Topology

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-! ### Kronecker powers in the `Fin N → F` encoding -/

/-- the `N`-fold Kronecker power of a `2×2` matrix -/
def kron (u : Matrix F F ℂ) : Matrix (Bas N) (Bas N) ℂ := Matrix.of fun r c => ∏ k, u (r k) (c k)

theorem kron_mul (u v : Matrix F F ℂ) : (kron u : Matrix (Bas N) (Bas N) ℂ) * kron v = kron (u * v) := by
  ext r c
  simp only [kron, mul_apply, of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.prod_mul_distrib]

theorem trace_kron (u : Matrix F F ℂ) : (kron u : Matrix (Bas N) (Bas N) ℂ).trace = u.trace ^ N := by
  simp only [Matrix.trace, diag, kron, of_apply]
  rw [← Fintype.prod_sum (fun (_ : Fin N) (w : F) => u w w)]
  simp

/-! ### the sum of all Pauli matrices -/

theorem iPow_zero : iPow 0 = 1 := by simp [iPow]

theorem iPow_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 4) :
    iPow (∑ i ∈ s, f i) = ∏ i ∈ s, iPow (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, iPow_add, ih]

/-- the one-qubit matrix `I + X + Y + Z`, entrywise -/
def tt : Matrix F F ℂ :=
  Matrix.of fun r c => ∑ w : F, iPow ((if r + c = 1 ∧ w = 1 then 1 else 0) + dbl (w * c))

theorem ycount_cast (x z : Fin N → F) :
    ((ycount ((x, z) : V N) : ℕ) : ZMod 4) = ∑ k, (if x k = 1 ∧ z k = 1 then (1 : ZMod 4) else 0) := by
  unfold ycount
  rw [Finset.card_filter]
  push_cast
  rfl

theorem sum_P_eq_kron : (∑ a : V N, P a) = kron tt := by
  ext r c
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  have hx : ∀ z : Fin N → F, ∑ x : Fin N → F, P ((x, z) : V N) r c =
      iPow (((ycount ((r + c, z) : V N) : ℕ) : ZMod 4) + dbl (dot z c)) := by
    intro z
    rw [Finset.sum_eq_single (r + c)]
    · simp only [P, of_apply]
      rw [if_pos]
      rw [add_comm r c, ← add_assoc, add_self_V'', zero_add]
    · intro x _ hx
      simp only [P, of_apply]
      rw [if_neg]
      intro h; apply hx; rw [h, add_comm c x, add_assoc, add_self_V'', add_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun z _ => hx z)]
  simp only [kron, tt, of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← iPow_sum, ycount_cast]
  unfold dot
  rw [dbl_sum, ← Finset.sum_add_distrib]
  rfl

/-! ### the one-qubit traces -/

theorem univF : (Finset.univ : Finset F) = {0, 1} := by decide

theorem iPow_one : iPow 1 = I := by
  have := iPow_natCast 1; simpa using this

theorem iPow_three : iPow 3 = -I := by
  have h := iPow_natCast 3
  have h3 : ((3 : ℕ) : ZMod 4) = 3 := by norm_num
  rw [h3] at h
  rw [h, pow_succ, I_sq]; ring

theorem tt00 : tt 0 0 = 2 := by
  simp only [tt, of_apply, univF]
  rw [Finset.sum_pair (by decide)]
  rw [show ((if (0 : F) + 0 = 1 ∧ (0 : F) = 1 then (1 : ZMod 4) else 0) + dbl (0 * 0)) = 0 by decide,
    show ((if (0 : F) + 0 = 1 ∧ (1 : F) = 1 then (1 : ZMod 4) else 0) + dbl (1 * 0)) = 0 by decide,
    iPow_zero]; norm_num

theorem tt01 : tt 0 1 = 1 - I := by
  simp only [tt, of_apply, univF]
  rw [Finset.sum_pair (by decide)]
  rw [show ((if (0 : F) + 1 = 1 ∧ (0 : F) = 1 then (1 : ZMod 4) else 0) + dbl (0 * 1)) = 0 by decide,
    show ((if (0 : F) + 1 = 1 ∧ (1 : F) = 1 then (1 : ZMod 4) else 0) + dbl (1 * 1)) = 3 by decide,
    iPow_zero, iPow_three]; ring

theorem tt10 : tt 1 0 = 1 + I := by
  simp only [tt, of_apply, univF]
  rw [Finset.sum_pair (by decide)]
  rw [show ((if (1 : F) + 0 = 1 ∧ (0 : F) = 1 then (1 : ZMod 4) else 0) + dbl (0 * 0)) = 0 by decide,
    show ((if (1 : F) + 0 = 1 ∧ (1 : F) = 1 then (1 : ZMod 4) else 0) + dbl (1 * 0)) = 1 by decide,
    iPow_zero, iPow_one]

theorem tt11 : tt 1 1 = 0 := by
  simp only [tt, of_apply, univF]
  rw [Finset.sum_pair (by decide)]
  rw [show ((if (1 : F) + 1 = 1 ∧ (0 : F) = 1 then (1 : ZMod 4) else 0) + dbl (0 * 1)) = 0 by decide,
    show ((if (1 : F) + 1 = 1 ∧ (1 : F) = 1 then (1 : ZMod 4) else 0) + dbl (1 * 1)) = 2 by decide,
    iPow_zero, iPow_two]; ring

theorem sumF (f : F → ℂ) : ∑ w : F, f w = f 0 + f 1 := by
  rw [univF, Finset.sum_pair (by decide)]

theorem trace_tt : tt.trace = 2 := by
  simp only [Matrix.trace, diag, sumF, tt00, tt11]; ring

theorem trace_tt2 : (tt * tt).trace = 8 := by
  simp only [Matrix.trace, diag, mul_apply, sumF, tt00, tt01, tt10, tt11]
  ring_nf; rw [I_sq]; ring

theorem trace_tt3 : (tt * tt * tt).trace = 20 := by
  simp only [Matrix.trace, diag, mul_apply, sumF, tt00, tt01, tt10, tt11]
  ring_nf; rw [I_sq]; norm_num

/-! ### the all-(+1) assignment on W(2N−1,2) -/

theorem Mg_ones : Mg (Wpts N) (gOf (fun _ => 0)) = kron tt - 1 := by
  rw [← sum_P_eq_kron, ← P_zero]
  unfold Mg Wpts gOf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V N))]
  simp [pm]

theorem trace_cube_ones :
    (Mg (Wpts N) (gOf (fun _ => 0)) * Mg (Wpts N) (gOf (fun _ => 0)) *
      Mg (Wpts N) (gOf (fun _ => 0))).trace = 20 ^ N - 3 * 8 ^ N + 2 * 2 ^ N := by
  rw [Mg_ones]
  set A : Matrix (Bas N) (Bas N) ℂ := kron tt
  have h : (A - 1) * (A - 1) * (A - 1) = A * A * A - (A * A + A * A + A * A) + (A + A + A) - 1 := by
    noncomm_ring
  rw [h, trace_sub, trace_add, trace_sub, trace_add, trace_add, trace_add, trace_add, trace_one]
  simp only [A, kron_mul, trace_kron, trace_tt, trace_tt2, trace_tt3]
  rw [show (Fintype.card (Bas N) : ℂ) = 2 ^ N from card_bas]
  ring

/-- The number of lines violated by the all-zero (all-(+1)) assignment:
12 |V(0)| = 6 |L_N| − (10^N − 3·4^N + 2). -/
theorem viol_zero (N : ℕ) :
    (12 * ((W N).violated (fun _ => 0)).card : ℤ) =
      6 * (W N).lines.card - (10 ^ N - 3 * 4 ^ N + 2) := by
  have h := trace_cube_viol (Wpts N) (zero_not_mem_W N) (fun _ => 0)
  rw [trace_cube_ones] at h
  have h2 : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero _ two_ne_zero
  have key : ((12 * ((W N).violated (fun _ => 0)).card : ℤ) : ℂ) =
      ((6 * (W N).lines.card - (10 ^ N - 3 * 4 ^ N + 2) : ℤ) : ℂ) := by
    apply mul_left_cancel₀ h2
    unfold W
    push_cast
    have e20 : (20 : ℂ) ^ N = 2 ^ N * 10 ^ N := by rw [← mul_pow]; norm_num
    have e8 : (8 : ℂ) ^ N = 2 ^ N * 4 ^ N := by rw [← mul_pow]; norm_num
    rw [e20, e8] at h
    linear_combination h
  exact_mod_cast key

/-- a line is violated by the all-zero assignment iff its sign is negative -/
theorem violated_zero_iff (l : Finset (V N)) :
    (W N).Violated (fun _ => 0) l ↔ (W N).sign l ≠ 0 := by
  unfold Violated; simp

/-- **ASY-6, Corollary 1.** 24·#{negative lines of W(2N−1,2)} = 16^N + 4^N − 2·10^N. -/
theorem neg_lines (N : ℕ) (hN : 1 ≤ N) :
    24 * ((W N).lines.filter (fun l => (W N).sign l ≠ 0)).card + 2 * 10 ^ N = 16 ^ N + 4 ^ N := by
  have hv := viol_zero N
  have hL := lines_W N hN
  have hfilt : (W N).violated (fun _ => 0) = (W N).lines.filter (fun l => (W N).sign l ≠ 0) := by
    unfold violated
    exact Finset.filter_congr (fun l _ => violated_zero_iff l)
  rw [hfilt] at hv
  have h4 : 4 ≤ 4 ^ N := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have h16 : (16 : ℕ) ^ N = 4 ^ N * 4 ^ N := by rw [← mul_pow]; norm_num
  have hLz : (12 * (W N).lines.card : ℤ) = ((4 ^ N : ℕ) - 1 : ℤ) * ((4 ^ N : ℕ) - 4) := by
    have : ((12 * (W N).lines.card : ℕ) : ℤ) = (((4 ^ N - 1) * (4 ^ N - 4) : ℕ) : ℤ) := by rw [hL]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 4 ^ N), Nat.cast_sub h4] at this
    exact_mod_cast this
  have goal : ((24 * ((W N).lines.filter (fun l => (W N).sign l ≠ 0)).card + 2 * 10 ^ N : ℕ) : ℤ) =
      ((16 ^ N + 4 ^ N : ℕ) : ℤ) := by
    rw [h16]; push_cast at hLz hv ⊢
    linear_combination 2 * hv + hLz
  exact_mod_cast goal

/-- the degree bound coming from the all-(+1) assignment -/
theorem deg_W_le (N : ℕ) :
    (12 * (W N).deg : ℤ) ≤ 6 * (W N).lines.card - (10 ^ N - 3 * 4 ^ N + 2) := by
  have h := (W N).deg_le (fun _ => 0)
  have := viol_zero N
  have h' : (12 * (W N).deg : ℤ) ≤ 12 * ((W N).violated (fun _ => 0)).card := by
    exact_mod_cast Nat.mul_le_mul_left 12 h
  linarith

theorem three_four_le_ten (N : ℕ) (hN : 2 ≤ N) : 3 * 4 ^ N ≤ 10 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ, pow_succ]; omega

theorem lines_W_eq_zero (N : ℕ) (hN : N ≤ 1) : (W N).lines.card = 0 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have h1 := six_mul_card (Wpts 0) (zero_not_mem_W 0)
    have h2 : (OP (Wpts 0)).card = 0 := by
      have hW : Wpts 0 = ∅ := Finset.card_eq_zero.1 (by rw [card_Wpts]; rfl)
      simp [OP, hW]
    unfold W; omega
  · have hN1 : N = 1 := by omega
    subst hN1
    have := lines_W 1 le_rfl
    have h3 : (4 : ℕ) ^ 1 - 4 = 0 := by norm_num
    rw [h3, mul_zero] at this; omega

/-- ρ_N ≤ 1/2 − (10^N − 3·4^N + 2)/(12 |L_N|). -/
theorem rho_le_explicit (N : ℕ) (hL : 0 < (W N).lines.card) :
    rho N ≤ 1 / 2 - ((10 : ℝ) ^ N - 3 * 4 ^ N + 2) / (12 * (W N).lines.card) := by
  have h := deg_W_le N
  have hR : (12 * (W N).deg : ℝ) ≤ 6 * (W N).lines.card - (10 ^ N - 3 * 4 ^ N + 2) := by
    exact_mod_cast h
  unfold rho
  have hLr : (0 : ℝ) < (W N).lines.card := by exact_mod_cast hL
  rw [div_le_iff₀ hLr]
  have : (1 / 2 - ((10 : ℝ) ^ N - 3 * 4 ^ N + 2) / (12 * (W N).lines.card)) * (W N).lines.card =
      (W N).lines.card / 2 - ((10 : ℝ) ^ N - 3 * 4 ^ N + 2) / 12 := by
    field_simp
  rw [this]; linarith

/-- **ρ_N < 1/2 for every N** (ASY-6, the elementary strictness). -/
theorem rho_lt_half (N : ℕ) : rho N < 1 / 2 := by
  rcases Nat.eq_zero_or_pos (W N).lines.card with h0 | hpos
  · unfold rho; rw [h0]; norm_num
  · have hN : 2 ≤ N := by
      by_contra h; push Not at h
      have := lines_W_eq_zero N (by omega); omega
    have h := rho_le_explicit N hpos
    have h3 : (3 : ℝ) * 4 ^ N ≤ 10 ^ N := by exact_mod_cast three_four_le_ten N hN
    have hpos' : (0 : ℝ) < ((10 : ℝ) ^ N - 3 * 4 ^ N + 2) / (12 * (W N).lines.card) := by
      apply div_pos (by linarith)
      have : (0 : ℝ) < (W N).lines.card := by exact_mod_cast hpos
      linarith
    linarith

/-- **Target A.** ρ_N < ρ_{N+1} for infinitely many N. The proof uses only ρ_N < 1/2 and
ρ_N → 1/2; monotonicity is not needed. -/
theorem rho_strict_jumps : ∀ N₀, ∃ N ≥ N₀, rho N < rho (N + 1) := by
  intro N₀
  by_contra h
  push Not at h
  have hle : ∀ N ≥ N₀, rho N ≤ rho N₀ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (h k hk).trans ih
  have : (1 : ℝ) / 2 ≤ rho N₀ :=
    le_of_tendsto rho_tendsto_half (eventually_atTop.2 ⟨N₀, hle⟩)
  linarith [rho_lt_half N₀]

/-- ρ is not eventually constant; in fact every value is eventually exceeded. -/
theorem rho_eventually_gt (N₀ : ℕ) : ∀ᶠ N in atTop, rho N₀ < rho N :=
  rho_tendsto_half.eventually (lt_mem_nhds (rho_lt_half N₀))

/-- the unconditional form of the strict-jump statement of `Spectral.lean`. -/
theorem rho_not_eventually_const : ¬ ∃ c N₀, ∀ N ≥ N₀, rho N = c := by
  rintro ⟨c, N₀, h⟩
  obtain ⟨N, hN⟩ := (rho_eventually_gt N₀ |>.and (eventually_ge_atTop N₀)).exists
  rw [h N hN.2, h N₀ le_rfl] at hN
  exact lt_irrefl _ hN.1

end PauliCtx.Spectral
