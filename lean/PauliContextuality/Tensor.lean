/-
Tensor.lean — blueprint ASY-6: tensor products, multiplicativity of τ, explicit upper bounds.

For an assignment `s : V N → F` with `s 0 = 0` put `h = (−1)^s` and `m_h = Σ_{all a} h(a) P_a`.
  * `trace_cube_mh` : tr m_h³ = 2^N · τ(s),  τ(s) := 6|L_N| − 12|V(s)| + 3·4^N − 2.
  * `P_join`, `mh_join` : P_{(a₁,a₂)} = P_{a₁} ⊗ P_{a₂} and m_{h₁⊗h₂} = m_{h₁} ⊗ m_{h₂}.
  * `tau_mul` : **τ(s₁ ⊗ s₂) = τ(s₁) τ(s₂).**
  * `deg_W_le_tau` : 12·deg W(2N−1,2) ≤ 6|L_N| − τ(s) + 3·4^N − 2.
  * Corollary 2 ⚙ : τ₃ = 1324, τ₄ = 13996 (from the witnesses), hence
      deg W(11,2) ≤ 553140, deg W(13,2) ≤ 9641268, deg W(15,2) ≤ 162635700, deg W(17,2) ≤ 2669910768.
-/
import PauliContextuality.GeoBounds

open Matrix Complex

namespace PauliCtx.Spectral

open Config

/-! ### Kronecker structure along `Fin.append` -/

section Prod

variable {N₁ N₂ : ℕ}

/-- `A` is the Kronecker product of `A₁` and `A₂` (indices split by `Fin.append`). -/
def IsProd (A : Matrix (Bas (N₁ + N₂)) (Bas (N₁ + N₂)) ℂ) (A₁ : Matrix (Bas N₁) (Bas N₁) ℂ)
    (A₂ : Matrix (Bas N₂) (Bas N₂) ℂ) : Prop :=
  ∀ r₁ c₁ r₂ c₂, A (Fin.append r₁ r₂) (Fin.append c₁ c₂) = A₁ r₁ c₁ * A₂ r₂ c₂

theorem sum_bas_add (f : Bas (N₁ + N₂) → ℂ) :
    ∑ m, f m = ∑ m₁ : Bas N₁, ∑ m₂ : Bas N₂, f (Fin.append m₁ m₂) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.appendEquiv N₁ N₂) _ _ (fun p => rfl)).symm

theorem IsProd.mul {A B : Matrix (Bas (N₁ + N₂)) (Bas (N₁ + N₂)) ℂ} {A₁ B₁ : Matrix (Bas N₁) (Bas N₁) ℂ}
    {A₂ B₂ : Matrix (Bas N₂) (Bas N₂) ℂ} (hA : IsProd A A₁ A₂) (hB : IsProd B B₁ B₂) :
    IsProd (A * B) (A₁ * B₁) (A₂ * B₂) := by
  intro r₁ c₁ r₂ c₂
  rw [mul_apply, sum_bas_add, mul_apply, mul_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
  show A (Fin.append r₁ r₂) (Fin.append m₁ m₂) * B (Fin.append m₁ m₂) (Fin.append c₁ c₂) = _
  rw [hA, hB]; ring

theorem IsProd.trace {A : Matrix (Bas (N₁ + N₂)) (Bas (N₁ + N₂)) ℂ} {A₁ : Matrix (Bas N₁) (Bas N₁) ℂ}
    {A₂ : Matrix (Bas N₂) (Bas N₂) ℂ} (hA : IsProd A A₁ A₂) : A.trace = A₁.trace * A₂.trace := by
  unfold Matrix.trace
  rw [sum_bas_add, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
  exact hA m₁ m₁ m₂ m₂

/-! ### joining labels -/

/-- `(a₁, a₂) ↦ a₁ ⊗ a₂` -/
def joinV (a₁ : V N₁) (a₂ : V N₂) : V (N₁ + N₂) := (Fin.append a₁.1 a₂.1, Fin.append a₁.2 a₂.2)

/-- the bijection `V N₁ × V N₂ ≃ V (N₁ + N₂)` -/
def joinE : V N₁ × V N₂ ≃ V (N₁ + N₂) :=
  (Equiv.prodProdProdComm _ _ _ _).trans (Equiv.prodCongr (Fin.appendEquiv N₁ N₂) (Fin.appendEquiv N₁ N₂))

theorem joinE_apply (p : V N₁ × V N₂) : joinE p = joinV p.1 p.2 := rfl

theorem joinE_symm_joinV (a₁ : V N₁) (a₂ : V N₂) : joinE.symm (joinV a₁ a₂) = (a₁, a₂) :=
  joinE.symm_apply_apply (a₁, a₂)

theorem sum_V_add (f : V (N₁ + N₂) → ℂ) : ∑ a, f a = ∑ a₁ : V N₁, ∑ a₂ : V N₂, f (joinV a₁ a₂) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv joinE _ _ (fun p => rfl)).symm

theorem append_add (c₁ x₁ : Bas N₁) (c₂ x₂ : Bas N₂) :
    Fin.append c₁ c₂ + Fin.append x₁ x₂ = Fin.append (c₁ + x₁) (c₂ + x₂) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]

theorem append_eq_iff (r₁ u₁ : Bas N₁) (r₂ u₂ : Bas N₂) :
    Fin.append r₁ r₂ = Fin.append u₁ u₂ ↔ r₁ = u₁ ∧ r₂ = u₂ := by
  have := (Fin.appendEquiv (α := F) N₁ N₂).injective.eq_iff (a := (r₁, r₂)) (b := (u₁, u₂))
  rw [Prod.mk.injEq] at this
  exact this

theorem joinV_zero : joinV (0 : V N₁) (0 : V N₂) = 0 := by
  unfold joinV
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]

theorem ycount_join (a₁ : V N₁) (a₂ : V N₂) : ycount (joinV a₁ a₂) = ycount a₁ + ycount a₂ := by
  unfold ycount joinV
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem dot_append (z₁ c₁ : Bas N₁) (z₂ c₂ : Bas N₂) :
    dot (Fin.append z₁ z₂) (Fin.append c₁ c₂) = dot z₁ c₁ + dot z₂ c₂ := by
  unfold dot; rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

/-- **ASY-6 (multiplicativity of Paulis).** `P_{a₁ ⊗ a₂} = P_{a₁} ⊗ P_{a₂}`. -/
theorem P_join (a₁ : V N₁) (a₂ : V N₂) : IsProd (P (joinV a₁ a₂)) (P a₁) (P a₂) := by
  intro r₁ c₁ r₂ c₂
  have hx : (joinV a₁ a₂).1 = Fin.append a₁.1 a₂.1 := rfl
  have hz : (joinV a₁ a₂).2 = Fin.append a₁.2 a₂.2 := rfl
  simp only [P, of_apply, hx, hz, append_add, append_eq_iff, ycount_join, dot_append]
  by_cases h₁ : r₁ = c₁ + a₁.1
  · by_cases h₂ : r₂ = c₂ + a₂.1
    · rw [if_pos ⟨h₁, h₂⟩, if_pos h₁, if_pos h₂, ← iPow_add]
      congr 1; push_cast; rw [dbl_add]; ring
    · rw [if_neg (fun h => h₂ h.2), if_neg h₂, mul_zero]
  · rw [if_neg (fun h => h₁ h.1), if_neg h₁, zero_mul]

/-! ### m_h and its cube trace -/

/-- `m_h = Σ_{all a} h(a) P_a` -/
noncomputable def mh {N : ℕ} (h : V N → ℤ) : Matrix (Bas N) (Bas N) ℂ := ∑ a, (h a : ℂ) • P a

/-- the product sign pattern `h₁ ⊗ h₂` -/
def hjoin (h₁ : V N₁ → ℤ) (h₂ : V N₂ → ℤ) : V (N₁ + N₂) → ℤ :=
  fun a => h₁ (joinE.symm a).1 * h₂ (joinE.symm a).2

theorem mh_join (h₁ : V N₁ → ℤ) (h₂ : V N₂ → ℤ) : IsProd (mh (hjoin h₁ h₂)) (mh h₁) (mh h₂) := by
  intro r₁ c₁ r₂ c₂
  simp only [mh, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [sum_V_add, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
  rw [P_join a₁ a₂ r₁ c₁ r₂ c₂]
  simp only [hjoin, joinE_symm_joinV]
  push_cast; ring

theorem trace_cube_join (h₁ : V N₁ → ℤ) (h₂ : V N₂ → ℤ) :
    (mh (hjoin h₁ h₂) * mh (hjoin h₁ h₂) * mh (hjoin h₁ h₂)).trace =
      (mh h₁ * mh h₁ * mh h₁).trace * (mh h₂ * mh h₂ * mh h₂).trace :=
  (((mh_join h₁ h₂).mul (mh_join h₁ h₂)).mul (mh_join h₁ h₂)).trace

end Prod

/-! ### τ and violations -/

variable {N : ℕ}

/-- τ(s) = 6|L_N| − 12|V(s)| + 3·4^N − 2 -/
noncomputable def tauW (s : V N → F) : ℤ :=
  6 * (W N).lines.card - 12 * ((W N).violated s).card + 3 * 4 ^ N - 2

theorem mh_eq (s : V N → F) (hs : s 0 = 0) : mh (gOf s) = 1 + Mg (Wpts N) (gOf s) := by
  unfold mh Mg Wpts
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V N))]
  simp [gOf, hs, pm, P_zero]

theorem trace_cube_mh (s : V N → F) (hs : s 0 = 0) :
    (mh (gOf s) * mh (gOf s) * mh (gOf s)).trace = 2 ^ N * (tauW s : ℂ) := by
  rw [mh_eq s hs]
  set M := Mg (Wpts N) (gOf s)
  have e : (1 + M) * (1 + M) * (1 + M) = 1 + (M + M + M) + (M * M + M * M + M * M) + M * M * M := by
    noncomm_ring
  have h3 := trace_cube_viol (Wpts N) (zero_not_mem_W N) s
  have h2 := trace_Mg_sq (Wpts N) (gOf s) (gOf_pm s)
  have h1 := trace_Mg (Wpts N) (zero_not_mem_W N) (gOf s)
  rw [e, trace_add, trace_add, trace_add, trace_add, trace_add, trace_add, trace_add, trace_one,
    h1, h2, h3, card_Wpts]
  rw [show (Fintype.card (Bas N) : ℂ) = 2 ^ N from card_bas]
  have h4 : 1 ≤ 4 ^ N := Nat.one_le_pow _ _ (by norm_num)
  unfold tauW
  push_cast [Nat.cast_sub h4]
  change (2 : ℂ) ^ N + (0 + 0 + 0) + _ + 2 ^ N * (6 * ((configX (Wpts N) _).lines.card : ℂ) - _) = _
  unfold W
  ring

/-- the product assignment `s₁ ⊗ s₂` -/
def sjoin {N₁ N₂ : ℕ} (s₁ : V N₁ → F) (s₂ : V N₂ → F) : V (N₁ + N₂) → F :=
  fun a => s₁ (joinE.symm a).1 + s₂ (joinE.symm a).2

theorem gOf_sjoin {N₁ N₂ : ℕ} (s₁ : V N₁ → F) (s₂ : V N₂ → F) :
    gOf (sjoin s₁ s₂) = hjoin (gOf s₁) (gOf s₂) := by
  funext a; simp only [gOf, sjoin, hjoin, pm_add]

theorem sjoin_zero {N₁ N₂ : ℕ} {s₁ : V N₁ → F} {s₂ : V N₂ → F} (h₁ : s₁ 0 = 0) (h₂ : s₂ 0 = 0) :
    sjoin s₁ s₂ 0 = 0 := by
  unfold sjoin
  rw [← joinV_zero, joinE_symm_joinV]
  simp [h₁, h₂]

/-- **ASY-6.** τ(s₁ ⊗ s₂) = τ(s₁) τ(s₂). -/
theorem tau_mul {N₁ N₂ : ℕ} (s₁ : V N₁ → F) (s₂ : V N₂ → F) (h₁ : s₁ 0 = 0) (h₂ : s₂ 0 = 0) :
    tauW (sjoin s₁ s₂) = tauW s₁ * tauW s₂ := by
  have h := trace_cube_mh (sjoin s₁ s₂) (sjoin_zero h₁ h₂)
  rw [gOf_sjoin, trace_cube_join, trace_cube_mh s₁ h₁, trace_cube_mh s₂ h₂] at h
  have hp : (2 : ℂ) ^ (N₁ + N₂) ≠ 0 := pow_ne_zero _ two_ne_zero
  have : ((tauW (sjoin s₁ s₂) : ℤ) : ℂ) = ((tauW s₁ * tauW s₂ : ℤ) : ℂ) := by
    apply mul_left_cancel₀ hp
    rw [← h, pow_add]; push_cast; ring
  exact_mod_cast this

/-- the degree bound from any assignment, in τ form -/
theorem deg_W_le_tau (s : V N → F) :
    (12 * (W N).deg : ℤ) ≤ 6 * (W N).lines.card - tauW s + 3 * 4 ^ N - 2 := by
  have := (W N).deg_le s
  have h : (12 * (W N).deg : ℤ) ≤ 12 * ((W N).violated s).card := by exact_mod_cast Nat.mul_le_mul_left 12 this
  unfold tauW; linarith

/-! ### Corollary 2: certified block values and product bounds -/

theorem witW5_zero : witnessAssign 3 (fun _ => true) witnessW5 0 = 0 := by native_decide
theorem witW7_zero : arrAssign (N := 4) arrW7 0 = 0 := by native_decide

/-- τ₃ = 1324 (the Hoggar pattern) -/
theorem tau3 : tauW (witnessAssign 3 (fun _ => true) witnessW5) = 1324 := by
  have h := six_mul_viol (Wpts 3) (zero_not_mem_W 3) (witnessAssign 3 (fun _ => true) witnessW5)
  rw [W5_witness] at h
  have hv : ((W 3).violated (witnessAssign 3 (fun _ => true) witnessW5)).card = 63 := by unfold W; omega
  unfold tauW; rw [hv, card_lines_W3]; norm_num

/-- τ₄ = 13996 (from the W(7,2) witness) -/
theorem tau4 : tauW (arrAssign (N := 4) arrW7) = 13996 := by
  have h := six_mul_viol (Wpts 4) (zero_not_mem_W 4) (arrAssign arrW7)
  rw [W7_witness] at h
  have hv : ((W 4).violated (arrAssign arrW7)).card = 1575 := by unfold W; omega
  unfold tauW; rw [hv, card_lines_W4]; norm_num

theorem lines_W_int (N : ℕ) (hN : 1 ≤ N) (L : ℕ) (hL : 12 * L = (4 ^ N - 1) * (4 ^ N - 4)) :
    (W N).lines.card = L := by
  have := lines_W N hN; omega

/-- **ASY-6, Corollary 2, N = 6 (3+3).** deg W(11,2) ≤ 553140. -/
theorem W11_le : (W 6).deg ≤ 553140 := by
  have ht := tau_mul _ _ witW5_zero witW5_zero
  rw [tau3] at ht
  have h := deg_W_le_tau (N := 3 + 3) (sjoin (witnessAssign 3 (fun _ => true) witnessW5)
    (witnessAssign 3 (fun _ => true) witnessW5))
  rw [ht, lines_W_int (3 + 3) (by norm_num) 1396395 (by decide)] at h
  change (W (3 + 3)).deg ≤ _
  generalize (W (3 + 3)).deg = D at h ⊢
  norm_num at h
  omega

/-- **N = 7 (3+4).** deg W(13,2) ≤ 9641268. -/
theorem W13_le : (W 7).deg ≤ 9641268 := by
  have ht := tau_mul _ _ witW5_zero witW7_zero
  rw [tau3, tau4] at ht
  have h := deg_W_le_tau (N := 3 + 4) (sjoin (witnessAssign 3 (fun _ => true) witnessW5)
    (arrAssign (N := 4) arrW7))
  rw [ht, lines_W_int (3 + 4) (by norm_num) 22362795 (by decide)] at h
  change (W (3 + 4)).deg ≤ _
  generalize (W (3 + 4)).deg = D at h ⊢
  norm_num at h
  omega

/-- **N = 8 (4+4).** deg W(15,2) ≤ 162635700. -/
theorem W15_le : (W 8).deg ≤ 162635700 := by
  have ht := tau_mul _ _ witW7_zero witW7_zero
  rw [tau4] at ht
  have h := deg_W_le_tau (N := 4 + 4) (sjoin (arrAssign (N := 4) arrW7) (arrAssign (N := 4) arrW7))
  rw [ht, lines_W_int (4 + 4) (by norm_num) 357886635 (by decide)] at h
  change (W (4 + 4)).deg ≤ _
  generalize (W (4 + 4)).deg = D at h ⊢
  norm_num at h
  omega

/-- **N = 9 (3+3+3).** deg W(17,2) ≤ 2669910768. -/
theorem W17_le : (W 9).deg ≤ 2669910768 := by
  set w := witnessAssign 3 (fun _ => true) witnessW5
  have h6 := tau_mul w w witW5_zero witW5_zero
  have h9 := tau_mul (sjoin w w) w (sjoin_zero witW5_zero witW5_zero) witW5_zero
  rw [h6, tau3] at h9
  have h := deg_W_le_tau (N := 3 + 3 + 3) (sjoin (sjoin w w) w)
  rw [h9, lines_W_int (3 + 3 + 3) (by norm_num) 5726513835 (by decide)] at h
  change (W (3 + 3 + 3)).deg ≤ _
  generalize (W (3 + 3 + 3)).deg = D at h ⊢
  norm_num at h
  omega

end PauliCtx.Spectral
