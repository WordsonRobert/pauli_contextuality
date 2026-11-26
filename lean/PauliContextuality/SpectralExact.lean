/-
SpectralExact.lean — exact values from the spectral bound (blueprint ASY-4):
  * `W5_eq_63`     : deg W(5,2) = 63   (TQ-1; ASY-2 is tight for N = 3: Λ = 21, F = 504).
  * `Qplus7_eq_315`: deg Q⁺(7,2) = 315 (ASY-4 b; Λ = 45, F = 2160; witness `witness_Qp7_2.txt`).
Finite counts (numbers of points and ordered commuting pairs, violated pairs of the witnesses) are
evaluated with `native_decide`.
-/
import PauliContextuality.SpectralW

namespace PauliCtx.Spectral

open Config

/-! ### witnesses in `certify.py` point order -/

/-- `certify.py` order: lexicographic in (x₁..x_N, z₁..z_N) -/
def decodeLex (N : ℕ) (key : ℕ) : V N :=
  (fun k => if key.testBit (2 * N - 1 - k.val) then 1 else 0,
   fun k => if key.testBit (N - 1 - k.val) then 1 else 0)

def lexKeyV {N : ℕ} (p : V N) : ℕ :=
  (∑ k : Fin N, (p.1 k).val * 2 ^ (2 * N - 1 - k.val)) + ∑ k : Fin N, (p.2 k).val * 2 ^ (N - 1 - k.val)

/-- the assignment given by a witness list over the points `{p : P p}` in `certify.py` order -/
def witnessAssign (N : ℕ) (P : V N → Bool) (w : List Bool) (p : V N) : F :=
  let keys := (List.range (4 ^ N)).filter (fun key => key ≠ 0 && P (decodeLex N key))
  if w.getD (keys.idxOf (lexKeyV p)) false then 1 else 0

def witnessW5 : List Bool := [true, false, true, true, false, true, false, true, false, true, true, false, false, false, false, false, false, true, false, false, true, false, true, true, false, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, false, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false]
def witnessQp7 : List Bool := [false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, false, false, false, false, true, true, false, false, true, true, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, false, true, false, false, true, false, false]

/-! ### W(5,2) -/

theorem W5_ge_63 : 63 ≤ (W 3).deg := by
  have hL : (W 3).lines.card = 315 := by have := lines_W 3 (by norm_num); norm_num at this; omega
  have hne : (Wpts 3).Nonempty := Finset.card_pos.1 (by rw [card_Wpts]; norm_num)
  have h := spectral_lower (Wpts 3) (zero_not_mem_W 3) hne (by norm_num)
  simp only at h
  change ((W 3).lines.card : ℝ) / 2 - _ ≤ (W 3).deg at h
  rw [hL, card_Wpts] at h
  have hs : Real.sqrt (((4 ^ 3 - 1 : ℕ) : ℝ) * (2 ^ 3 - 1)) = 21 := by
    rw [show (((4 ^ 3 - 1 : ℕ) : ℝ) * (2 ^ 3 - 1)) = 21 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs] at h
  have : (63 : ℝ) ≤ (W 3).deg := by
    generalize ((W 3).deg : ℝ) = D at h ⊢
    norm_num at h
    linarith
  exact_mod_cast this

theorem W5_witness : ((OP (Wpts 3)).filter (violP (witnessAssign 3 (fun _ => true) witnessW5))).card
    = 378 := by native_decide

theorem W5_le_63 : (W 3).deg ≤ 63 := by
  have h := six_mul_viol (Wpts 3) (zero_not_mem_W 3) (witnessAssign 3 (fun _ => true) witnessW5)
  rw [W5_witness] at h
  have : ((W 3).violated (witnessAssign 3 (fun _ => true) witnessW5)).card = 63 := by
    unfold W; omega
  rw [← this]; exact (W 3).deg_le _

/-- TQ-1 / ASY-4 (a): deg W(5,2) = 63. -/
theorem W5_eq_63 : (W 3).deg = 63 := le_antisymm W5_le_63 W5_ge_63

/-! ### Q⁺(7,2) -/

/-- the hyperbolic quadric Q⁺(7,2): symmetric non-identity 4-qubit Paulis (even number of Y) -/
def QP : Finset (V 4) := Finset.univ.filter (fun p => p ≠ 0 ∧ qplus p = 0)

theorem zero_not_mem_QP : (0 : V 4) ∉ QP := by simp [QP]

noncomputable def Qplus7 : Config (V 4) := configX QP zero_not_mem_QP

theorem card_QP : QP.card = 135 := by native_decide

theorem card_OP_QP : (OP QP).card = 9450 := by native_decide

theorem Qplus7_lines : Qplus7.lines.card = 1575 := by
  have := six_mul_card QP zero_not_mem_QP
  rw [card_OP_QP] at this
  unfold Qplus7; omega

theorem Qplus7_ge_315 : 315 ≤ Qplus7.deg := by
  have hne : QP.Nonempty := Finset.card_pos.1 (by rw [card_QP]; norm_num)
  have h := spectral_lower QP zero_not_mem_QP hne (by norm_num)
  simp only at h
  change (Qplus7.lines.card : ℝ) / 2 - _ ≤ Qplus7.deg at h
  rw [Qplus7_lines, card_QP] at h
  have hs : Real.sqrt (((135 : ℕ) : ℝ) * (2 ^ 4 - 1)) = 45 := by
    rw [show (((135 : ℕ) : ℝ) * (2 ^ 4 - 1)) = 45 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs] at h
  have : (315 : ℝ) ≤ Qplus7.deg := by
    generalize (Qplus7.deg : ℝ) = D at h ⊢
    norm_num at h
    linarith
  exact_mod_cast this

def isQP (p : V 4) : Bool := decide (qplus p = 0)

theorem Qplus7_witness : ((OP QP).filter (violP (witnessAssign 4 isQP witnessQp7))).card = 1890 := by
  native_decide

theorem Qplus7_le_315 : Qplus7.deg ≤ 315 := by
  have h := six_mul_viol QP zero_not_mem_QP (witnessAssign 4 isQP witnessQp7)
  rw [Qplus7_witness] at h
  have : (Qplus7.violated (witnessAssign 4 isQP witnessQp7)).card = 315 := by
    unfold Qplus7; omega
  rw [← this]; exact Qplus7.deg_le _

/-- ASY-4 (b): deg Q⁺(7,2) = 315, so ρ(Q⁺(7,2)) = 1/5. -/
theorem Qplus7_eq_315 : Qplus7.deg = 315 := le_antisymm Qplus7_le_315 Qplus7_ge_315

end PauliCtx.Spectral
