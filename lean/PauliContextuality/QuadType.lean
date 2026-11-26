/-
QuadType.lean — blueprint 06, CONE-3: the degree of a non-degenerate quadric depends only on its type.

Every quadratic form q on V N polarising to ω is qplus + ω(c,·) for a unique c (`quad_eq_qplus_add`);
its type is qplus(c) ∈ F₂ (this is the Arf invariant of q relative to qplus, Arf(q) = qplus(c)).
  * `tvL d` : the symplectic tvLection x ↦ x + ω(d,x) d (linear, ω-preserving, an involution).
  * `quad_tvL` : if q(d) = 0 then q ∘ T_d = q + ω(d,·).
  * `deg_secQ_shift` : hence the quadrics of q and of q + ω(d,·) have the same degree.
  * `deg_secQ_type` : **every non-degenerate quadric has the degree of Q⁺ = {qplus = 0} if qplus(c) = 0,
      and of Q⁻ = {qplus + ω(c₀,·) = 0} (any c₀ with qplus(c₀) = 1) if qplus(c) = 1.**
      No normal form is needed: one tvLection does it.
  * `deg_secQ_qminus` : on V (n+1) the second form is `qminus` (c₀ = Y on qubit 0).
  * `deg_quad5` : every quadratic form on V 3 polarising to ω has quadric of degree 21 (type 0) or 9
      (type 1); `deg_quad7_plus` : of degree 315 on V 4 when of type 0.
-/
import PauliContextuality.ConeQuad
import PauliContextuality.Quadrics5

open Module

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-! ### the linear part of a quadratic form -/

/-- every linear functional on V N is ω(c, ·) -/
theorem omegaB_surjective : Function.Surjective (omegaB N) := by
  have hinj : Function.Injective (omegaB N) := LinearMap.ker_eq_bot.1 ker_omegaB
  have hdim : finrank F (V N) = finrank F (Module.Dual F (V N)) :=
    (Subspace.dual_finrank_eq).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj

/-- q − qplus is additive, hence ω(c, ·) -/
theorem quad_eq_qplus_add {q : V N → F} (hq : IsQuad q) : ∃ c, ∀ x, q x = qplus x + omega c x := by
  let ℓ : V N →ₗ[F] F :=
    { toFun := fun x => q x + qplus x
      map_add' := by
        intro a b
        rw [hq a b, qplus_add]
        have : omega a b + omega a b = 0 := CharTwo.add_self_eq_zero _
        linear_combination this
      map_smul' := by
        intro c x
        rcases F_cases c with rfl | rfl
        · simp [hq.map_zero, (qplus_isQuad (N := N)).map_zero]
        · simp }
  obtain ⟨c, hc⟩ := omegaB_surjective ℓ
  refine ⟨c, fun x => ?_⟩
  have h := LinearMap.congr_fun hc x
  rw [omegaB_apply] at h
  rw [h]
  show q x = qplus x + (q x + qplus x)
  rw [← add_assoc, add_comm (qplus x), add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem isQuad_add_omega {q : V N → F} (hq : IsQuad q) (c : V N) :
    IsQuad (fun x => q x + omega c x) := by
  intro a b
  simp only
  rw [hq a b, omega_add_right]
  ring

/-! ### tvLections -/

/-- the symplectic tvLection x ↦ x + ω(d,x) d -/
def tvL (d : V N) : V N →ₗ[F] V N where
  toFun x := x + omega d x • d
  map_add' x y := by rw [omega_add_right, add_smul]; abel
  map_smul' c x := by
    simp only [omega_smul_right, smul_add, smul_smul, RingHom.id_apply]

theorem tvL_apply (d x : V N) : tvL d x = x + omega d x • d := rfl

theorem tvL_omega (d x y : V N) : omega (tvL d x) (tvL d y) = omega x y := by
  simp only [tvL_apply, omega_add_left, omega_add_right, omega_smul_left, omega_smul_right,
    omega_self]
  rw [omega_comm x d]
  generalize omega d x = A
  generalize omega d y = B
  generalize omega x y = C
  revert A B C; decide

theorem tvL_tvL (d x : V N) : tvL d (tvL d x) = x := by
  rw [tvL_apply, tvL_apply, omega_add_right, omega_smul_right, omega_self, mul_zero, add_zero,
    add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem tvL_injective (d : V N) : Function.Injective (tvL d) := fun x y h => by
  rw [← tvL_tvL d x, h, tvL_tvL]

theorem quad_tvL {q : V N → F} (hq : IsQuad q) {d : V N} (hd : q d = 0) (x : V N) :
    q (tvL d x) = q x + omega d x := by
  have hsm : ∀ c : F, q (c • d) = 0 := fun c => by
    rcases F_cases c with rfl | rfl
    · rw [zero_smul, hq.map_zero]
    · rw [one_smul, hd]
  rw [tvL_apply, hq, hsm, add_zero, omega_smul_right, omega_comm x d]
  congr 1
  generalize omega d x = A
  revert A; decide

/-- the quadric of q + ω(d,·) is the image of the quadric of q under T_d -/
theorem secQ_shift {q : V N → F} (hq : IsQuad q) {d : V N} (hd : q d = 0) :
    secQ (fun x => q x + omega d x) ⊤ = (secQ q ⊤).image (tvL d) := by
  ext x
  rw [Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨hx0, -, hqx⟩ := mem_secQ.1 hx
    refine ⟨tvL d x, mem_secQ.2 ⟨fun h => hx0 ?_, Submodule.mem_top, ?_⟩, tvL_tvL d x⟩
    · rw [← tvL_tvL d x, h, map_zero]
    · rw [quad_tvL hq hd]; exact hqx
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy0, -, hqy⟩ := mem_secQ.1 hy
    refine mem_secQ.2 ⟨fun h => hy0 (tvL_injective d (by rw [h, map_zero])), Submodule.mem_top, ?_⟩
    show q (tvL d y) + omega d (tvL d y) = 0
    rw [← quad_tvL hq hd (tvL d y), tvL_tvL]
    exact hqy

theorem zero_not_mem_image_tvL {q : V N → F} (d : V N) :
    (0 : V N) ∉ (secQ q ⊤).image (tvL d) := by
  intro h
  obtain ⟨y, hy, hy0⟩ := Finset.mem_image.1 h
  exact (mem_secQ.1 hy).1 (tvL_injective d (by rw [hy0, map_zero]))

/-- **shifting a quadratic form by ω(d,·) with q(d) = 0 does not change the degree** -/
theorem deg_secQ_shift {q : V N → F} (hq : IsQuad q) {d : V N} (hd : q d = 0) :
    (configX (secQ (fun x => q x + omega d x) ⊤) (zero_not_mem_secQ _ ⊤)).deg =
      (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg := by
  rw [configX_deg_congr (secQ_shift hq hd) _ (zero_not_mem_image_tvL d)]
  exact deg_configX_map (secQ q ⊤) (zero_not_mem_secQ _ _) (tvL d)
    (fun a _ b _ => tvL_omega d a b)
    (fun x _ y _ h => tvL_injective d h) _

theorem secQ_congr {q q' : V N → F} (h : ∀ x, q x = q' x) :
    (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg =
      (configX (secQ q' ⊤) (zero_not_mem_secQ q' ⊤)).deg := by
  obtain rfl : q = q' := funext h
  rfl

/-! ### the type of a quadratic form decides the degree -/

/-- **CONE-3, type classification.** Write q = qplus + ω(c,·). If qplus(c) = 0 the quadric of q has the
degree of Q⁺ = {qplus = 0}; if qplus(c) = 1 it has the degree of {qplus + ω(c₀,·) = 0} for any c₀ with
qplus(c₀) = 1. -/
theorem deg_secQ_type {q : V N → F} {c : V N} (hc : ∀ x, q x = qplus x + omega c x)
    {c₀ : V N} (hc₀ : qplus c₀ = 1) :
    (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg =
      if qplus c = 0 then (configX (secQ (qplus : V N → F) ⊤) (zero_not_mem_secQ _ ⊤)).deg
      else (configX (secQ (fun x => qplus x + omega c₀ x) ⊤) (zero_not_mem_secQ _ ⊤)).deg := by
  split_ifs with h
  · rw [secQ_congr hc]
    exact deg_secQ_shift qplus_isQuad h
  · have h1 : qplus c = 1 := F_eq_one h
    set qm : V N → F := fun x => qplus x + omega c₀ x
    have hqm : IsQuad qm := isQuad_add_omega qplus_isQuad c₀
    have hd : qm (c + c₀) = 0 := by
      show qplus (c + c₀) + omega c₀ (c + c₀) = 0
      rw [qplus_add, h1, hc₀, omega_add_right, omega_self, add_zero, omega_comm c₀ c]
      generalize omega c c₀ = A
      revert A; decide
    have hq : ∀ x, q x = qm x + omega (c + c₀) x := by
      intro x
      show q x = qplus x + omega c₀ x + omega (c + c₀) x
      rw [hc, omega_add_left]
      generalize omega c x = A
      generalize omega c₀ x = B
      generalize qplus x = C
      revert A B C; decide
    rw [secQ_congr hq]
    exact deg_secQ_shift hqm hd

/-- qminus is qplus shifted by Y on qubit 0 -/
theorem qminus_eq (n : ℕ) (x : V (n + 1)) :
    qminus x = qplus x + omega (Pi.single 0 1, Pi.single 0 1) x := by
  unfold qminus omega
  rw [Finset.sum_eq_single (0 : Fin (n + 1)) (fun j _ hj => by simp [hj]) (by simp)]
  simp only [Pi.single_eq_same, one_mul]
  ring

theorem qplus_Y0 (n : ℕ) : qplus ((Pi.single 0 1, Pi.single 0 1) : V (n + 1)) = 1 := by
  unfold qplus
  rw [Finset.sum_eq_single (0 : Fin (n + 1)) (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **CONE-3, type classification on V (n+1).** Every quadratic form polarising to ω has, on all of
V (n+1), the degree of Q⁺(2n+1,2) or of Q⁻(2n+1,2), according to its type. -/
theorem deg_secQ_qminus {n : ℕ} {q : V (n + 1) → F} {c : V (n + 1)}
    (hc : ∀ x, q x = qplus x + omega c x) :
    (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg =
      if qplus c = 0 then (configX (secQ (qplus : V (n + 1) → F) ⊤) (zero_not_mem_secQ _ ⊤)).deg
      else (configX (secQ (qminus : V (n + 1) → F) ⊤) (zero_not_mem_secQ _ ⊤)).deg := by
  rw [deg_secQ_type hc (qplus_Y0 n), secQ_congr (q := qminus) (qminus_eq n)]

/-! ### concrete instances -/

theorem secQ_qplus3 : secQ (qplus : V 3 → F) ⊤ = QP5 := by
  ext x; simp [mem_secQ, QP5]

theorem secQ_qminus3 : secQ (qminus : V 3 → F) ⊤ = QM5 := by
  ext x; simp [mem_secQ, QM5]

theorem secQ_qplus4 : secQ (qplus : V 4 → F) ⊤ = QP := by
  ext x; simp [mem_secQ, QP]

/-- **Every non-degenerate quadric of W(5,2)** has degree 21 (type qplus(c) = 0, Q⁺(5,2)) or 9
(type 1, Q⁻(5,2)). -/
theorem deg_quad5 {q : V 3 → F} {c : V 3} (hc : ∀ x, q x = qplus x + omega c x) :
    (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg = if qplus c = 0 then 21 else 9 := by
  have h := deg_secQ_qminus (n := 2) hc
  rw [configX_deg_congr secQ_qplus3 _ zero_not_mem_QP5,
    configX_deg_congr secQ_qminus3 _ zero_not_mem_QM5] at h
  split_ifs at h ⊢
  · rw [h]; exact Qp5_eq_21
  · rw [h]; exact Qm5_eq_9

theorem deg_quad5' {q : V 3 → F} (hq : IsQuad q) :
    (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg = 21 ∨
      (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg = 9 := by
  obtain ⟨c, hc⟩ := quad_eq_qplus_add hq
  rw [deg_quad5 hc]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- every quadric of type 0 in W(7,2) has degree 315 = deg Q⁺(7,2) -/
theorem deg_quad7_plus {q : V 4 → F} {c : V 4} (hc : ∀ x, q x = qplus x + omega c x)
    (h0 : qplus c = 0) : (configX (secQ q ⊤) (zero_not_mem_secQ q ⊤)).deg = 315 := by
  have h := deg_secQ_qminus (n := 3) hc
  rw [if_pos h0, configX_deg_congr secQ_qplus4 _ zero_not_mem_QP] at h
  rw [h]; exact Qplus7_eq_315

end PauliCtx.Spectral
