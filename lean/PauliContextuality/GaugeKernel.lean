/-
GaugeKernel.lean — blueprint 11, TIGHT-2 (the gauge kernel of W(5,2)).

  * `kerW N` : the gauge space {s : V N → F | s 0 = 0, s(a+b) = s(a) + s(b) for commuting a, b}.
    `mem_kerW_iff_lines`: for s(0) = 0 this is exactly "every line of W(2N−1,2) has s-sum 0",
    i.e. the kernel of the incidence matrix.
  * `qplus_mem_kerW`, `qplus_not_linear` : the quadratic form y(a) mod 2 lies in the kernel and is not
    linear (the quadratic gauge; it is complex conjugation, ⟨P_a⟩_{ψ̄} = (−1)^{y(a)}⟨P_a⟩_ψ).
  * `finrank_kerW3` ⚙ : dim kerW 3 = 7 (6 linear functionals + y(a) mod 2), via the evaluation at
    T = {X₁, X₂, X₃, Z₁, Z₂, Z₃, Y₁}: injective by a 56-step propagation certificate (each step
    is a line with two known points), surjective by explicit kernel elements.
  * `rank_incW3` ⚙ : the 315 × 63 incidence matrix of W(5,2) over F₂ has rank 56.
  * `violated_eq_iff`, `card_fiber_violated` : two assignments have the same violated set iff their
    difference is in the kernel; so every violated set is attained by exactly 2^7 = 128 normalised
    (s(0) = 0) assignments of W(5,2).  With the 120 optimal violated sets of `certify_asym.py` X5
    this gives 120·128 = 15360 optimal assignments (the 120 itself is not formalised).
-/
import PauliContextuality.Transfer

open Module

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-! ### the gauge space -/

/-- the gauge space of W(2N−1,2) -/
def kerW (N : ℕ) : Submodule F (V N → F) where
  carrier := {s | s 0 = 0 ∧ ∀ a b : V N, omega a b = 0 → s (a + b) = s a + s b}
  add_mem' := by
    rintro s t ⟨hs0, hs⟩ ⟨ht0, ht⟩
    refine ⟨by simp [hs0, ht0], fun a b h => ?_⟩
    simp only [Pi.add_apply, hs a b h, ht a b h]; ring
  zero_mem' := ⟨rfl, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro c s ⟨hs0, hs⟩
    refine ⟨by simp [hs0], fun a b h => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hs a b h]; ring

theorem mem_kerW {s : V N → F} :
    s ∈ kerW N ↔ s 0 = 0 ∧ ∀ a b : V N, omega a b = 0 → s (a + b) = s a + s b := Iff.rfl

theorem sum_tri_W {a b : V N} (h : IsLine a b (a + b)) (s : V N → F) :
    ∑ p ∈ tri (a, b), s p = s a + s b + s (a + b) := by
  simp [tri, Finset.sum_insert, h.ne_ab, h.ne_ac, h.ne_bc, add_assoc]

/-- for normalised assignments the gauge space is the kernel of the incidence matrix -/
theorem mem_kerW_iff_lines (s : V N → F) (hs : s 0 = 0) :
    s ∈ kerW N ↔ ∀ l ∈ (W N).lines, ∑ p ∈ l, s p = 0 := by
  constructor
  · rintro ⟨-, hadd⟩ l hl
    obtain ⟨a, b, h, rfl⟩ := mem_W_lines.1 hl
    rw [sum_tri_W h, hadd a b h.comm]
    have : ∀ x y : F, x + y + (x + y) = 0 := by decide
    exact this _ _
  · intro hl
    refine ⟨hs, fun a b hab => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp [hs]
    by_cases hb : b = 0
    · subst hb; simp [hs]
    by_cases hab' : a = b
    · subst hab'; rw [add_self_V, hs, add_self_F]
    have hc : a + b ≠ 0 := by
      intro h; apply hab'
      have := congrArg (· + b) h; simpa [add_assoc, add_self_V] using this
    have hL : IsLine a b (a + b) := by
      refine ⟨hab', ?_, ?_, ha, hb, hc, add_self_V _, hab⟩
      · intro h; apply hb; have := congrArg (a + ·) h; simpa [add_cancel_left', add_self_V] using this.symm
      · intro h; apply ha; have := congrArg (· + b) h; simpa [add_cancel_right', add_self_V] using this.symm
    have := hl _ (tri_mem_W hL)
    rw [sum_tri_W hL] at this
    have key : ∀ x y z : F, x + y + z = 0 → z = x + y := by decide
    exact key _ _ _ this

/-- the coordinate functionals -/
def cx (i : Fin N) : V N → F := fun a => a.1 i
def cz (i : Fin N) : V N → F := fun a => a.2 i

theorem cx_mem (i : Fin N) : cx i ∈ kerW N := ⟨rfl, fun _ _ _ => rfl⟩
theorem cz_mem (i : Fin N) : cz i ∈ kerW N := ⟨rfl, fun _ _ _ => rfl⟩

/-- **TIGHT-2.** the quadratic form y(a) mod 2 is a gauge -/
theorem qplus_mem_kerW : (qplus : V N → F) ∈ kerW N := by
  refine ⟨by simp [qplus], fun a b h => ?_⟩
  rw [qplus_add, h, add_zero]

/-- … and it is not linear (N ≥ 1) -/
theorem qplus_not_linear (hN : 1 ≤ N) : ¬ ∃ f : V N →ₗ[F] F, ∀ a, f a = qplus a := by
  rintro ⟨f, hf⟩
  set i : Fin N := ⟨0, hN⟩
  set x : V N := (Pi.single i 1, 0)
  set z : V N := (0, Pi.single i 1)
  have h1 : qplus (x + z) = 1 := by
    unfold qplus; rw [Finset.sum_eq_single i]
    · simp [x, z]
    · intro j _ hj; simp [x, z, hj]
    · simp
  have h2 : qplus x = 0 := by unfold qplus; simp [x]
  have h3 : qplus z = 0 := by unfold qplus; simp [z]
  have := map_add f x z
  rw [hf, hf, hf, h1, h2, h3] at this
  exact one_ne_zero (this.trans (add_zero 0))

/-! ### the propagation certificate for N = 3 -/

/-- bit-packed decoding: x | (z << N), qubit i ↔ bit i -/
def decN (N : ℕ) (k : ℕ) : V N :=
  (fun i => if k.testBit i.val then 1 else 0, fun i => if k.testBit (N + i.val) then 1 else 0)

/-- each step (a, b): a and b are known and commute, so a + b becomes known -/
def checkSteps : List (V N) → List (ℕ × ℕ) → Bool
  | known, [] => decide (∀ p : V N, p ∈ known)
  | known, (a, b) :: st =>
      (decide (decN N a ∈ known) && decide (decN N b ∈ known) &&
        decide (omega (decN N a) (decN N b) = 0)) &&
      checkSteps ((decN N a + decN N b) :: known) st

theorem checkSteps_sound (s : V N → F) (hs : s ∈ kerW N) :
    ∀ (st : List (ℕ × ℕ)) (known : List (V N)), (∀ p ∈ known, s p = 0) →
      checkSteps known st = true → ∀ p, s p = 0 := by
  intro st
  induction st with
  | nil =>
    intro known hk h p
    simp only [checkSteps, decide_eq_true_eq] at h
    exact hk p (h p)
  | cons ab st ih =>
    obtain ⟨a, b⟩ := ab
    intro known hk h
    simp only [checkSteps, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ha, hb⟩, hω⟩, hrest⟩ := h
    refine ih _ (fun p hp => ?_) hrest
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [hs.2 _ _ hω, hk _ ha, hk _ hb, add_zero]
    · exact hk p hp

def T7 : Fin 7 → V 3 := ![decN 3 1, decN 3 2, decN 3 4, decN 3 8, decN 3 16, decN 3 32, decN 3 9]

def steps7 : List (ℕ × ℕ) :=
  [(1, 2), (1, 4), (1, 16), (1, 32), (2, 4), (2, 5), (2, 8), (2, 9), (2, 32), (2, 33), (4, 8), (4, 9),
   (4, 10), (4, 11), (4, 16), (4, 17), (8, 16), (8, 20), (8, 32), (8, 34), (9, 16), (9, 20), (9, 32),
   (9, 34), (10, 17), (10, 21), (10, 25), (10, 29), (11, 17), (11, 21), (12, 26), (12, 30), (12, 33),
   (12, 35), (12, 41), (12, 43), (13, 33), (13, 35), (16, 32), (16, 33), (16, 37), (16, 40), (16, 41),
   (16, 44), (16, 45), (17, 37), (17, 42), (17, 43), (17, 46), (17, 47), (17, 53), (18, 32), (18, 33),
   (18, 36), (18, 37), (20, 50)]

/-- ⚙ the 56-step propagation from {0} ∪ T reaches every label of V 3 -/
theorem steps7_ok : checkSteps (0 :: List.ofFn T7) steps7 = true := by native_decide

theorem kerW3_eq_zero (s : V 3 → F) (hs : s ∈ kerW 3) (hT : ∀ j, s (T7 j) = 0) : s = 0 := by
  funext p
  refine checkSteps_sound s hs steps7 _ (fun q hq => ?_) steps7_ok p
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hs.1
  · obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hq
    exact hT j

/-- evaluation at T -/
def res7 : kerW 3 →ₗ[F] (Fin 7 → F) where
  toFun s j := (s : V 3 → F) (T7 j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res7_injective : Function.Injective res7 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  have h := kerW3_eq_zero s s.2 (fun j => congrFun hs j)
  exact Subtype.ext h

/-- explicit kernel elements hitting the standard basis of F^T -/
def kv (j : Fin 7) : V 3 → F :=
  match j with
  | 0 => cx 0 + qplus
  | 1 => cx 1
  | 2 => cx 2
  | 3 => cz 0 + qplus
  | 4 => cz 1
  | 5 => cz 2
  | 6 => qplus

theorem kv_mem (j : Fin 7) : kv j ∈ kerW 3 := by
  fin_cases j
  · exact (kerW 3).add_mem (cx_mem 0) qplus_mem_kerW
  · exact cx_mem 1
  · exact cx_mem 2
  · exact (kerW 3).add_mem (cz_mem 0) qplus_mem_kerW
  · exact cz_mem 1
  · exact cz_mem 2
  · exact qplus_mem_kerW

theorem kv_T : ∀ j i : Fin 7, kv j (T7 i) = if j = i then 1 else 0 := by decide

theorem res7_surjective : Function.Surjective res7 := by
  intro u
  refine ⟨∑ j, u j • ⟨kv j, kv_mem j⟩, ?_⟩
  funext i
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ j, (res7 ⟨kv j, kv_mem j⟩) i = if j = i then 1 else 0 := fun j => kv_T j i
  simp_rw [this, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]

noncomputable def kerW3_equiv : kerW 3 ≃ₗ[F] (Fin 7 → F) :=
  LinearEquiv.ofBijective res7 ⟨res7_injective, res7_surjective⟩

/-- ⚙ **TIGHT-2.** the gauge space of W(5,2) has dimension 7 -/
theorem finrank_kerW3 : finrank F (kerW 3) = 7 := by
  rw [kerW3_equiv.finrank_eq, Module.finrank_fin_fun]

theorem card_kerW3 : Nat.card (kerW 3) = 128 := by
  rw [Nat.card_congr kerW3_equiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]; norm_num

/-! ### the incidence matrix -/

/-- the non-zero labels -/
abbrev Vstar (N : ℕ) := {p : V N // p ≠ 0}

/-- extension by zero -/
def ext0 (s : Vstar N → F) (p : V N) : F := if h : p = 0 then 0 else s ⟨p, h⟩

/-- the incidence map F^{V*} → F^{L}, s ↦ (Σ_{p∈ℓ} s(p))_ℓ -/
def incW (N : ℕ) : (Vstar N → F) →ₗ[F] ((W N).lines → F) where
  toFun s l := ∑ p ∈ l.1, ext0 s p
  map_add' s t := by
    funext l; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold ext0; split_ifs <;> simp
  map_smul' c s := by
    funext l; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold ext0; split_ifs <;> simp

theorem ext0_mem_kerW (s : Vstar N → F) (hs : s ∈ LinearMap.ker (incW N)) : ext0 s ∈ kerW N := by
  rw [mem_kerW_iff_lines _ (by simp [ext0])]
  intro l hl
  exact congrFun (LinearMap.mem_ker.1 hs) ⟨l, hl⟩

/-- the kernel of the incidence map is the gauge space -/
noncomputable def kerInc_equiv (N : ℕ) : LinearMap.ker (incW N) ≃ₗ[F] kerW N where
  toFun s := ⟨ext0 s.1, ext0_mem_kerW s.1 s.2⟩
  invFun k := ⟨fun p => (k : V N → F) p.1, by
    rw [LinearMap.mem_ker]
    funext l
    have hk := (mem_kerW_iff_lines _ k.2.1).1 k.2 l.1 l.2
    show ∑ p ∈ l.1, ext0 (fun p => (k : V N → F) p.1) p = 0
    rw [← hk]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold ext0; split_ifs with h
    · rw [h]; exact k.2.1.symm
    · rfl⟩
  map_add' s t := by
    apply Subtype.ext; funext p; simp only [Submodule.coe_add, Pi.add_apply]
    unfold ext0; split_ifs <;> simp
  map_smul' c s := by
    apply Subtype.ext; funext p; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    unfold ext0; split_ifs <;> simp
  left_inv s := by
    apply Subtype.ext; funext p
    simp [ext0, p.2]
  right_inv k := by
    apply Subtype.ext; funext p
    simp only [ext0]
    split_ifs with h
    · rw [h]; exact k.2.1.symm
    · rfl

theorem card_Vstar (N : ℕ) : Fintype.card (Vstar N) = 4 ^ N - 1 := by
  rw [Fintype.card_subtype_compl, card_V]; simp

/-- ⚙ **TIGHT-2.** the incidence matrix of W(5,2) over F₂ has rank 56 (kernel dimension 7) -/
theorem rank_incW3 : finrank F (LinearMap.range (incW 3)) = 56 ∧
    finrank F (LinearMap.ker (incW 3)) = 7 := by
  have hk : finrank F (LinearMap.ker (incW 3)) = 7 := by
    rw [(kerInc_equiv 3).finrank_eq, finrank_kerW3]
  have h := LinearMap.finrank_range_add_finrank_ker (incW 3)
  rw [Module.finrank_fintype_fun_eq_card, card_Vstar, hk] at h
  exact ⟨by norm_num at h; omega, hk⟩

/-! ### fibres of the violated-set map -/

/-- two assignments have the same violated set iff they have the same line sums -/
theorem violated_eq_iff {α : Type} {_ : Fintype α} {_ : DecidableEq α} (C : Config α) (s t : α → F) :
    C.violated s = C.violated t ↔ ∀ l ∈ C.lines, ∑ p ∈ l, s p = ∑ p ∈ l, t p := by
  constructor
  · intro h l hl
    have hiff : C.Violated s l ↔ C.Violated t l := by
      have := congrArg (l ∈ ·) h
      simp only [violated, Finset.mem_filter, hl, true_and, eq_iff_iff] at this
      exact this
    unfold Violated at hiff
    have key : ∀ x y e : F, ((x + e ≠ 0) ↔ (y + e ≠ 0)) → x = y := by decide
    exact key _ _ _ hiff
  · intro h
    ext l
    simp only [violated, Finset.mem_filter]
    constructor <;> rintro ⟨hl, hv⟩ <;> refine ⟨hl, ?_⟩ <;> unfold Violated at hv ⊢
    · rwa [← h l hl]
    · rwa [h l hl]

/-- the normalised assignments of W(5,2) with a given violated set form a coset of the gauge
space; so each attained violated set has exactly 128 of them -/
theorem fiber_to_ker (s₀ : V N → F) (hs₀ : s₀ 0 = 0) (s : V N → F) (h0 : s 0 = 0)
    (hv : (W N).violated s = (W N).violated s₀) : s + s₀ ∈ kerW N := by
  have h00 : (s + s₀) 0 = 0 := by rw [Pi.add_apply, h0, hs₀, add_zero]
  rw [mem_kerW_iff_lines _ h00]
  intro l hl
  have := (violated_eq_iff (W N) s s₀).1 hv l hl
  rw [show ∑ p ∈ l, (s + s₀) p = ∑ p ∈ l, s p + ∑ p ∈ l, s₀ p from Finset.sum_add_distrib, this,
    add_self_F]

theorem ker_to_fiber (s₀ : V N → F) (hs₀ : s₀ 0 = 0) (k : V N → F) (hk : k ∈ kerW N) :
    (k + s₀) 0 = 0 ∧ (W N).violated (k + s₀) = (W N).violated s₀ := by
  refine ⟨by rw [Pi.add_apply, hk.1, hs₀, add_zero], (violated_eq_iff (W N) _ s₀).2 fun l hl => ?_⟩
  have := (mem_kerW_iff_lines _ hk.1).1 hk l hl
  rw [show ∑ p ∈ l, (k + s₀) p = ∑ p ∈ l, k p + ∑ p ∈ l, s₀ p from Finset.sum_add_distrib, this,
    zero_add]

/-- the normalised assignments with the violated set of `s₀` ≃ the gauge space -/
def fiberEquiv (s₀ : V N → F) (hs₀ : s₀ 0 = 0) :
    {s : V N → F // s 0 = 0 ∧ (W N).violated s = (W N).violated s₀} ≃ kerW N where
  toFun s := ⟨s.1 + s₀, fiber_to_ker s₀ hs₀ s.1 s.2.1 s.2.2⟩
  invFun k := ⟨k.1 + s₀, ker_to_fiber s₀ hs₀ k.1 k.2⟩
  left_inv s := Subtype.ext (by funext p; simp only [Pi.add_apply, add_assoc, add_self_F, add_zero])
  right_inv k := Subtype.ext (by funext p; simp only [Pi.add_apply, add_assoc, add_self_F, add_zero])

/-- **TIGHT-2.** every violated set of W(5,2) that is attained is attained by exactly 128
normalised assignments (a coset of the gauge space) -/
theorem card_fiber_violated (s₀ : V 3 → F) (hs₀ : s₀ 0 = 0) :
    Nat.card {s : V 3 → F // s 0 = 0 ∧ (W 3).violated s = (W 3).violated s₀} = 128 := by
  rw [Nat.card_congr (fiberEquiv s₀ hs₀), card_kerW3]

end PauliCtx.Spectral
