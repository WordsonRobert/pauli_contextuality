/-
GeoBounds.lean — 4- and 5-qubit geometries (blueprint GEO-3, GEO-4, GEO-5, GEO-6, TQ-1 doily).

  * `W7_ge_1080`  (GEO-4)   : deg W(7,2) ≥ 1080, by TR-5 transfer from deg Q⁻(7,2) ≥ 216.
  * `W7_ge_1451`  (ASY-2)   : deg W(7,2) ≥ 1451 (spectral bound).
  * `W9_ge_28786`           : deg W(9,2) ≥ 28786 (spectral), hence ≥ 17538 (GEO-4).
  * `Qp9_ge_6426`           : deg Q⁺(9,2) ≥ 6426 (spectral), hence ≥ 4783 (GEO-3, refutes |L|/5 = 4743).
  * `Qm9_ge_4873`           : deg Q⁻(9,2) ≥ 4873 (spectral), hence ≥ 3960 (GEO-4).
  * GEO-5 witnesses ⚙       : W(7,2) ≤ 1575, W(9,2) ≤ 31479, Q⁺(9,2) ≤ 6975, Q⁻(9,2) ≤ 7087.
  * `W3_eq_3`     (TQ-1) ⚙  : deg W(3,2) = 3: the Peres–Mermin grid is an odd cycle (CERT-1), TR-5
                              transfer gives 15·1 ≤ 6·deg; the all-(+1) assignment violates 3 lines.
  * `rho_chain`   (GEO-6)   : ρ₂ = ρ₃ = 1/5 < ρ₄ ≤ 5/17 < ρ₅.
-/
import PauliContextuality.Transfer
import PauliContextuality.QminusBridge

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-! ### generic tools -/

theorem OP_filter (P : V N → Prop) [DecidablePred P] :
    OP (Finset.univ.filter P) = ((Finset.univ.filter P) ×ˢ (Finset.univ.filter P)).filter
      (fun p => omega p.1 p.2 = 0 ∧ P (p.1 + p.2)) := by
  unfold OP; refine Finset.filter_congr fun p _ => ?_; simp

theorem Wpts_eq (N : ℕ) : Wpts N = Finset.univ.filter (fun p : V N => p ≠ 0) := by
  ext p; simp [Wpts]

/-- the degree depends only on the lines and their signs -/
theorem deg_congr {α : Type} [Fintype α] [DecidableEq α] (C C' : Config α) (hl : C.lines = C'.lines)
    (hs : ∀ l ∈ C.lines, C.sign l = C'.sign l) : C.deg = C'.deg := by
  have hv : ∀ s, C.violated s = C'.violated s := by
    intro s; unfold violated; rw [← hl]
    exact Finset.filter_congr (fun l hl' => by unfold Violated; rw [hs l hl'])
  apply le_antisymm
  · obtain ⟨s, hs'⟩ := C'.exists_opt; rw [← hs', ← hv]; exact C.deg_le s
  · obtain ⟨s, hs'⟩ := C.exists_opt; rw [← hs', hv]; exact C'.deg_le s

theorem OP_mono {X Y : Finset (V N)} (h : X ⊆ Y) : OP X ⊆ OP Y := by
  intro p hp
  rw [mem_OP] at hp ⊢
  exact ⟨h hp.1, h hp.2.1, hp.2.2.1, h hp.2.2.2⟩

theorem configX_lines_mono {X Y : Finset (V N)} (hX : (0 : V N) ∉ X) (hY : (0 : V N) ∉ Y) (h : X ⊆ Y) :
    (configX X hX).lines ⊆ (configX Y hY).lines :=
  Finset.image_subset_image (OP_mono h)

/-- an induced sub-configuration of `configX Y` has the degree of `configX X` -/
theorem deg_sub_configX {X Y : Finset (V N)} (hX : (0 : V N) ∉ X) (hY : (0 : V N) ∉ Y) (h : X ⊆ Y) :
    ((configX Y hY).sub _ (configX_lines_mono hX hY h)).deg = (configX X hX).deg := by
  refine deg_congr _ _ rfl fun l hl => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
  show (configX Y hY).sign (tri p) = (configX X hX).sign (tri p)
  rw [configX_sign hY (OP_mono h hp), configX_sign hX hp]

/-- ASY-2 with an explicit lower estimate `Λ₀ ≤ √(n(2^N−1))`:
deg ≥ |L|/2 − n²(2^N − 2)/(12 Λ₀). -/
theorem spectral_lower' (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N)
    (Λ₀ : ℝ) (hΛ₀ : 0 < Λ₀) (hle : Λ₀ ^ 2 ≤ (X.card : ℝ) * (2 ^ N - 1)) :
    ((configX X h0).lines.card : ℝ) / 2 - (X.card : ℝ) ^ 2 * (2 ^ N - 2) / (12 * Λ₀) ≤
      (configX X h0).deg := by
  have h := spectral_lower X h0 hX hN
  simp only at h
  set d : ℝ := 2 ^ N with hd
  set n : ℝ := (X.card : ℝ) with hn
  have hd2 : (2 : ℝ) ≤ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.card_pos.2 hX).ne'
  set Λ := Real.sqrt (n * (d - 1)) with hΛ
  have hΛpos : 0 < Λ := Real.sqrt_pos.2 (by nlinarith)
  have hΛ2 : Λ ^ 2 = n * (d - 1) := Real.sq_sqrt (by nlinarith)
  have hdef : (Λ * (d * n) - (d * n) ^ 2 / (d * Λ)) / (12 * d) = n ^ 2 * (d - 2) / (12 * Λ) := by
    field_simp
    rw [hΛ2]; ring
  rw [hdef] at h
  have hΛ₀Λ : Λ₀ ≤ Λ := Real.le_sqrt_of_sq_le hle
  have : n ^ 2 * (d - 2) / (12 * Λ) ≤ n ^ 2 * (d - 2) / (12 * Λ₀) :=
    div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by linarith)
  linarith

theorem card_lines_W4 : (W 4).lines.card = 5355 := by
  have h := lines_W 4 (by norm_num)
  have e : (4 ^ 4 - 1) * (4 ^ 4 - 4) = 12 * 5355 := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem card_lines_W5 : (W 5).lines.card = 86955 := by
  have h := lines_W 5 (by norm_num)
  have e : (4 ^ 5 - 1) * (4 ^ 5 - 4) = 12 * 86955 := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem card_lines_W2 : (W 2).lines.card = 15 := by
  have h := lines_W 2 (by norm_num)
  have e : (4 ^ 2 - 1) * (4 ^ 2 - 4) = 12 * 15 := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

/-! ### W(7,2): transfer from Q⁻(7,2) and the spectral bound -/

theorem QM_sub_W : Qm7.QM ⊆ Wpts 4 := by
  intro p hp; rw [mem_Wpts]; exact (Finset.mem_filter.1 hp).2.1

theorem card_OP_QM : (OP Qm7.QM).card = 6426 := by
  unfold Qm7.QM; rw [OP_filter]; native_decide

theorem Qminus7_lines_card : Qm7.Qminus7.lines.card = 1071 := by
  have := six_mul_card Qm7.QM Qm7.zero_not_mem_QM
  rw [card_OP_QM] at this
  unfold Qm7.Qminus7; omega

/-- **GEO-4.** deg W(7,2) ≥ 1080, transferred from deg Q⁻(7,2) ≥ 216 (TR-5). -/
theorem W7_ge_1080 : 1080 ≤ (W 4).deg := by
  have hsub := configX_lines_mono Qm7.zero_not_mem_QM (zero_not_mem_W 4) QM_sub_W
  have h := rho_max _ hsub
  have hdeg := deg_sub_configX Qm7.zero_not_mem_QM (zero_not_mem_W 4) QM_sub_W
  change (W 4).lines.card * ((W 4).sub _ hsub).deg ≤ _ at h
  rw [show ((W 4).sub _ hsub).deg = Qm7.Qminus7.deg from hdeg] at h
  have h216 := Qm7.Qminus7_ge_216
  rw [card_lines_W4, show (configX Qm7.QM Qm7.zero_not_mem_QM).lines.card = 1071 from
    Qminus7_lines_card] at h
  omega

/-- **ASY-2 for N = 4.** deg W(7,2) ≥ 1451. -/
theorem W7_ge_1451 : 1451 ≤ (W 4).deg := by
  have hne : (Wpts 4).Nonempty := Finset.card_pos.1 (by rw [card_Wpts]; norm_num)
  have h := spectral_lower' (Wpts 4) (zero_not_mem_W 4) hne (by norm_num) (6184 / 100) (by norm_num)
    (by rw [card_Wpts]; norm_num)
  change ((W 4).lines.card : ℝ) / 2 - _ ≤ (W 4).deg at h
  rw [card_lines_W4, card_Wpts] at h
  have : (1450 : ℝ) < (W 4).deg := by
    generalize ((W 4).deg : ℝ) = D at h ⊢
    norm_num at h
    linarith
  have : 1450 < (W 4).deg := by exact_mod_cast this
  omega

/-- **ASY-2 for N = 5.** deg W(9,2) ≥ 28786. -/
theorem W9_ge_28786 : 28786 ≤ (W 5).deg := by
  have hne : (Wpts 5).Nonempty := Finset.card_pos.1 (by rw [card_Wpts]; norm_num)
  have h := spectral_lower' (Wpts 5) (zero_not_mem_W 5) hne (by norm_num) (17808 / 100) (by norm_num)
    (by rw [card_Wpts]; norm_num)
  change ((W 5).lines.card : ℝ) / 2 - _ ≤ (W 5).deg at h
  rw [card_lines_W5, card_Wpts] at h
  have : (28785 : ℝ) < (W 5).deg := by
    generalize ((W 5).deg : ℝ) = D at h ⊢
    norm_num at h
    linarith
  have : 28785 < (W 5).deg := by exact_mod_cast this
  omega

/-- GEO-4: deg W(9,2) ≥ 17538 (here as a corollary of the spectral bound). -/
theorem W9_ge_17538 : 17538 ≤ (W 5).deg := le_trans (by norm_num) W9_ge_28786

/-! ### the 5-qubit quadrics -/

/-- Q⁺(9,2): non-zero singular points of `q⁺ = x·z` on 5 qubits -/
def QP9 : Finset (V 5) := Finset.univ.filter (fun p => p ≠ 0 ∧ qplus p = 0)
/-- Q⁻(9,2): non-zero singular points of `q⁻ = x·z + x₁ + z₁` on 5 qubits -/
def QM9 : Finset (V 5) := Finset.univ.filter (fun p => p ≠ 0 ∧ qminus p = 0)

theorem zero_not_mem_QP9 : (0 : V 5) ∉ QP9 := by simp [QP9]
theorem zero_not_mem_QM9 : (0 : V 5) ∉ QM9 := by simp [QM9]

noncomputable def Qplus9 : Config (V 5) := configX QP9 zero_not_mem_QP9
noncomputable def Qminus9 : Config (V 5) := configX QM9 zero_not_mem_QM9

theorem card_QP9 : QP9.card = 527 := by native_decide
theorem card_QM9 : QM9.card = 495 := by native_decide

theorem card_OP_QP9 : (OP QP9).card = 142290 := by unfold QP9; rw [OP_filter]; native_decide
theorem card_OP_QM9 : (OP QM9).card = 117810 := by unfold QM9; rw [OP_filter]; native_decide

theorem Qplus9_lines : Qplus9.lines.card = 23715 := by
  have := six_mul_card QP9 zero_not_mem_QP9
  rw [card_OP_QP9] at this
  unfold Qplus9; omega

theorem Qminus9_lines : Qminus9.lines.card = 19635 := by
  have := six_mul_card QM9 zero_not_mem_QM9
  rw [card_OP_QM9] at this
  unfold Qminus9; omega

/-- **ASY-2 for Q⁺(9,2):** deg ≥ 6426. -/
theorem Qp9_ge_6426 : 6426 ≤ Qplus9.deg := by
  have hne : QP9.Nonempty := Finset.card_pos.1 (by rw [card_QP9]; norm_num)
  have h := spectral_lower' QP9 zero_not_mem_QP9 hne (by norm_num) (127816 / 1000) (by norm_num)
    (by rw [card_QP9]; norm_num)
  change (Qplus9.lines.card : ℝ) / 2 - _ ≤ Qplus9.deg at h
  rw [Qplus9_lines, card_QP9] at h
  have : (6425 : ℝ) < Qplus9.deg := by
    generalize (Qplus9.deg : ℝ) = D at h ⊢
    norm_num at h
    linarith
  have : 6425 < Qplus9.deg := by exact_mod_cast this
  omega

/-- **GEO-3.** deg Q⁺(9,2) ≥ 4783 > 4743 = |L|/5. -/
theorem Qp9_ge_4783 : 4783 ≤ Qplus9.deg := le_trans (by norm_num) Qp9_ge_6426

/-- Q⁺(9,2) beats the three-qubit ratio 1/5. -/
theorem Qp9_gt_fifth : Qplus9.lines.card < 5 * Qplus9.deg := by
  rw [Qplus9_lines]; have := Qp9_ge_4783; omega

/-- **ASY-2 for Q⁻(9,2):** deg ≥ 4873. -/
theorem Qm9_ge_4873 : 4873 ≤ Qminus9.deg := by
  have hne : QM9.Nonempty := Finset.card_pos.1 (by rw [card_QM9]; norm_num)
  have h := spectral_lower' QM9 zero_not_mem_QM9 hne (by norm_num) (123874 / 1000) (by norm_num)
    (by rw [card_QM9]; norm_num)
  change (Qminus9.lines.card : ℝ) / 2 - _ ≤ Qminus9.deg at h
  rw [Qminus9_lines, card_QM9] at h
  have : (4872 : ℝ) < Qminus9.deg := by
    generalize (Qminus9.deg : ℝ) = D at h ⊢
    norm_num at h
    linarith
  have : 4872 < Qminus9.deg := by exact_mod_cast this
  omega

/-- GEO-4: deg Q⁻(9,2) ≥ 3960. -/
theorem Qm9_ge_3960 : 3960 ≤ Qminus9.deg := le_trans (by norm_num) Qm9_ge_4873

/-! ### GEO-5: explicit assignments -/

/-- a witness list (in `certify.py` point order) written into an array indexed by `lexKeyV` -/
def witArr (N : ℕ) (P : V N → Bool) (w : List Bool) : Array Bool :=
  let keys := (List.range (4 ^ N)).filter (fun key => key ≠ 0 && P (decodeLex N key))
  (keys.zip w).foldl (fun a kb => a.set! kb.1 kb.2) (Array.replicate (4 ^ N) false)

def arrAssign {N : ℕ} (arr : Array Bool) (p : V N) : F := if arr.getD (lexKeyV p) false then 1 else 0

def witnessW7 : List Bool := [false, true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false, true, true, true, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false, true, true, false, false, true, true, true, true, true, false, true, true, true, false, false, false, true, false, true, true, false, false, true, true, false, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false, true, true, false, false, false, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, false, true]
def witnessW9 : List Bool := [true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, false, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true, true, true, false, false, false, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, true, false, false, true, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false, true, false, false, true, true, false, false, true, false, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, true, false, false, false, true, true, true, true, false, false, true, false, true, false, false, true, false, true, false, false, true, false, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, true, false, false, false, false, true, false, true, true, true, true, true, false, false, false, true, false, true, true, false, false, true, true, true, true, true, true, true, false, true, true, true, true, true, false, false, true, true, false, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, false, true, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false, false, false, false, true, true, false, false, true, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, true, false, false, true, false, true, true, false, false, false, false, false, false, true, true, true, false, true, false, false, true, false, true, true, true, false, false, false, false, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, false, false, false, false, false, false, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, false, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, true, false, false, true, true, true, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false, false, false, false, false, true, false, true, false, false, true, true, false, true, false, false, false, true, true, true, false, false, true, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, false, true, false, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, true, false, false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true, true, true, true, false, false, true, false, false, false]
def witnessQp9 : List Bool := [true, false, true, false, false, true, false, false, true, true, false, true, false, true, false, false, true, false, true, false, true, true, false, false, false, true, false, false, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false, true, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true, false, true, false, true, false, false, true, true, false, false, true, true, true, false, true, true, false, false, false, false, false, false, true, false, true, false, false, true, true, true, false, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false, false, false, true, false, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, false]
def witnessQm9 : List Bool := [true, false, true, false, true, true, false, true, false, false, true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, false, true, false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, false, false, true, false, true, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false, false, true, false, false, false, true, false, true, false, true, false, true, false, false, true, true, false, true, true, false, false, false, false, false, false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, true, false, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, true, false, false, false, true, true, false, false, false, false, false, true, false, true, false, true, true, false, true, false, false, false, false, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, true, false, true, false, true, true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false, true, false, true, true, false, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true, false, false, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false, true, false, true, false, false, true, true, true, true, true, false, true, false, false, false, true, false, true, false, true, false, true, true, true, false, true, false, false, false, true, false, true, false, true, true, true, false, false, false, false, true, true, true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true]

def isQP9 (p : V 5) : Bool := decide (qplus p = 0)
def isQM9 (p : V 5) : Bool := decide (qminus p = 0)

def arrW7 : Array Bool := witArr 4 (fun _ => true) witnessW7
def arrW9 : Array Bool := witArr 5 (fun _ => true) witnessW9
def arrQp9 : Array Bool := witArr 5 isQP9 witnessQp9
def arrQm9 : Array Bool := witArr 5 isQM9 witnessQm9

theorem W7_witness : ((OP (Wpts 4)).filter (violP (arrAssign arrW7))).card = 9450 := by
  rw [Wpts_eq, OP_filter]; native_decide

theorem W9_witness : ((OP (Wpts 5)).filter (violP (arrAssign arrW9))).card = 188874 := by
  rw [Wpts_eq, OP_filter]; native_decide

theorem Qp9_witness : ((OP QP9).filter (violP (arrAssign arrQp9))).card = 41850 := by
  unfold QP9; rw [OP_filter]; native_decide

theorem Qm9_witness : ((OP QM9).filter (violP (arrAssign arrQm9))).card = 42522 := by
  unfold QM9; rw [OP_filter]; native_decide

theorem deg_le_of_pairs (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (s : V N → F) (k : ℕ)
    (h : ((OP X).filter (violP s)).card = 6 * k) : (configX X h0).deg ≤ k := by
  have h6 := six_mul_viol X h0 s
  have : ((configX X h0).violated s).card = k := by omega
  rw [← this]; exact deg_le _ _

/-- **GEO-5.** deg W(7,2) ≤ 1575. -/
theorem W7_le_1575 : (W 4).deg ≤ 1575 := deg_le_of_pairs _ _ _ _ W7_witness
/-- **GEO-5.** deg W(9,2) ≤ 31479. -/
theorem W9_le_31479 : (W 5).deg ≤ 31479 := deg_le_of_pairs _ _ _ _ W9_witness
/-- **GEO-5.** deg Q⁺(9,2) ≤ 6975. -/
theorem Qp9_le_6975 : Qplus9.deg ≤ 6975 := deg_le_of_pairs _ _ _ _ Qp9_witness
/-- **GEO-5.** deg Q⁻(9,2) ≤ 7087. -/
theorem Qm9_le_7087 : Qminus9.deg ≤ 7087 := deg_le_of_pairs _ _ _ _ Qm9_witness

/-! ### TQ-1: the Peres–Mermin grid and the doily -/

/-- the labels of the Peres–Mermin square -/
def XI : V 2 := (![1, 0], ![0, 0])
def IX : V 2 := (![0, 1], ![0, 0])
def XX : V 2 := (![1, 1], ![0, 0])
def ZI : V 2 := (![0, 0], ![1, 0])
def IZ : V 2 := (![0, 0], ![0, 1])
def ZZ : V 2 := (![0, 0], ![1, 1])
def XZ : V 2 := (![1, 0], ![0, 1])
def ZX : V 2 := (![0, 1], ![1, 0])
def YY : V 2 := (![1, 1], ![1, 1])

/-- rows and columns of the square, as ordered commuting pairs -/
def gridPairs : Finset (V 2 × V 2) :=
  {(XI, IX), (IZ, ZI), (XZ, ZX), (XI, IZ), (IX, ZI), (XX, ZZ)}

/-- the Peres–Mermin grid: six lines of W(3,2) -/
def grid : Finset (Finset (V 2)) := gridPairs.image tri

theorem gridPairs_OP : gridPairs ⊆ OP (Wpts 2) := by
  rw [Wpts_eq, OP_filter]; native_decide

theorem grid_card : grid.card = 6 := by native_decide

theorem grid_sub : grid ⊆ (W 2).lines := Finset.image_subset_image gridPairs_OP

theorem grid_cycle : IsCycle grid := by
  unfold IsCycle; native_decide

theorem grid_sgn : ∑ p ∈ gridPairs, sgnF p = 1 := by native_decide

theorem grid_odd : ∑ l ∈ grid, (W 2).sign l = 1 := by
  have hinj : Set.InjOn tri (gridPairs : Set (V 2 × V 2)) := by
    have h : (gridPairs.image tri).card = gridPairs.card := by native_decide
    exact Finset.card_image_iff.1 h
  rw [grid, Finset.sum_image hinj, ← grid_sgn]
  refine Finset.sum_congr rfl fun p hp => ?_
  unfold W; exact configX_sign _ (gridPairs_OP hp)

/-- deg W(3,2) ≥ 3: TR-5 transfer from the grid, 15·1 ≤ 6·deg, so deg ≥ 3. -/
theorem W3_ge_3 : 3 ≤ (W 2).deg := by
  have h := rho_max grid grid_sub
  rw [card_lines_W2, grid_card] at h
  -- the grid has degree ≥ 1 (odd cycle, CERT-1)
  have hg : 1 ≤ ((W 2).sub grid grid_sub).deg := by
    obtain ⟨s, hs⟩ := ((W 2).sub grid grid_sub).exists_opt
    rw [← hs, violated_sub]
    exact odd_cycle_forces_violation (W 2) grid grid_sub grid_cycle grid_odd s
  omega

theorem W3_le_3 : (W 2).deg ≤ 3 := by
  have h := neg_lines 2 (by norm_num)
  have hv : (W 2).violated (fun _ => 0) = (W 2).lines.filter (fun l => (W 2).sign l ≠ 0) := by
    unfold violated; exact Finset.filter_congr (fun l _ => violated_zero_iff l)
  have : ((W 2).violated (fun _ => 0)).card = 3 := by
    rw [hv]; generalize ((W 2).lines.filter (fun l => (W 2).sign l ≠ 0)).card = c at h ⊢
    norm_num at h; omega
  rw [← this]; exact deg_le _ _

/-- **TQ-1.** deg W(3,2) = 3 (the doily). -/
theorem W3_eq_3 : (W 2).deg = 3 := le_antisymm W3_le_3 W3_ge_3

/-! ### GEO-6: the first values of ρ -/

theorem rho_two : rho 2 = 1 / 5 := by
  unfold rho; rw [W3_eq_3, card_lines_W2]; norm_num

theorem rho_three : rho 3 = 1 / 5 := by
  unfold rho; rw [W5_eq_63, card_lines_W3]; norm_num

theorem rho_four_bounds : (1451 : ℝ) / 5355 ≤ rho 4 ∧ rho 4 ≤ 5 / 17 := by
  unfold rho; rw [card_lines_W4]; push_cast
  constructor
  · have : (1451 : ℝ) ≤ (W 4).deg := by exact_mod_cast W7_ge_1451
    exact div_le_div_of_nonneg_right this (by norm_num)
  · have : ((W 4).deg : ℝ) ≤ 1575 := by exact_mod_cast W7_le_1575
    rw [div_le_iff₀ (by norm_num)]; linarith

theorem rho_five_bounds : (28786 : ℝ) / 86955 ≤ rho 5 ∧ rho 5 ≤ 31479 / 86955 := by
  unfold rho; rw [card_lines_W5]; push_cast
  constructor
  · have : (28786 : ℝ) ≤ (W 5).deg := by exact_mod_cast W9_ge_28786
    exact div_le_div_of_nonneg_right this (by norm_num)
  · have : ((W 5).deg : ℝ) ≤ 31479 := by exact_mod_cast W9_le_31479
    exact div_le_div_of_nonneg_right this (by norm_num)

/-- **GEO-6 / ASY-7 (iv), first steps.** ρ₂ = ρ₃ = 1/5 < ρ₄ ≤ 5/17 < ρ₅. -/
theorem rho_chain : rho 2 = rho 3 ∧ rho 3 < rho 4 ∧ rho 4 ≤ 5 / 17 ∧ (5 : ℝ) / 17 < rho 5 := by
  obtain ⟨h4l, h4u⟩ := rho_four_bounds
  obtain ⟨h5l, -⟩ := rho_five_bounds
  refine ⟨by rw [rho_two, rho_three], ?_, h4u, ?_⟩
  · rw [rho_three]; linarith [show (1 : ℝ) / 5 < 1451 / 5355 by norm_num]
  · linarith [show (5 : ℝ) / 17 < 28786 / 86955 by norm_num]

end PauliCtx.Spectral
