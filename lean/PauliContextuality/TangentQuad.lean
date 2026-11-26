/-
TangentQuad.lean — blueprint 06, CONE-3 corollaries: the exact tangent values 84, 36, 1260.

`tangent_quad_degree` (ConeSub) says that a tangent hyperplane section a^⊥ ∩ Q (q a = 0) is a cone over a
non-degenerate quadric Q₀ of one qubit less, deg = 4 · deg Q₀; which type Q₀ has is read off from the
number of points:
  * `card_XY` : the cone Y ⊗ ⟨Z⟩^t has 2^t (|Y| + 1) − 1 points, so |a^⊥ ∩ Q| = 2(|Q₀| + 1) − 1;
  * `card_secQ_type` : |Q₀| depends only on the type (one transvection, as for the degree);
  * on V 3 the two types have 35 and 27 points, on V 4 135 and 119 (`card_QP5`, `card_QM5`, `card_QP` (SpectralExact),
    `card_QM4`);
  * the tangent sections of Q⁺(7,2), Q⁻(7,2), Q⁺(9,2) have 71, 55, 271 points (computed for every a).
Results: `tangent_Qplus7` (84), `tangent_Qminus7` (36), `tangent_Qplus9` (1260 = 4 · 315).
-/
import PauliContextuality.ConeSub

open Module

namespace PauliCtx.Spectral

open Config

/-! ### the number of points of a cone -/

section CardCone

variable {k : ℕ} (Y : Finset (V k)) (hY : (0 : V k) ∉ Y) (t : ℕ)

theorem XY_eq_map : XY Y t = (Finset.univ.erase ((none, 0) : CP (PtX Y) t)).map (EYE hY) := by
  ext p
  rw [Finset.mem_map]
  constructor
  · intro hp
    obtain ⟨u, σ, rfl⟩ := XY_split hp
    obtain ⟨hne, hu⟩ := mem_XY_join.1 hp
    by_cases hu0 : u = 0
    · subst hu0
      refine ⟨(none, σ), Finset.mem_erase.2 ⟨fun h => hne ⟨rfl, congrArg Prod.snd h⟩,
        Finset.mem_univ _⟩, rfl⟩
    · exact ⟨(some ⟨u, hu.resolve_left hu0⟩, σ), Finset.mem_erase.2 ⟨by simp, Finset.mem_univ _⟩, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact EY_mem hY (Finset.mem_erase.1 hq).1

include hY in
theorem card_XY : (XY Y t).card = (Y.card + 1) * 2 ^ t - 1 := by
  rw [XY_eq_map Y hY t, Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  congr 1
  rw [Fintype.card_prod, Fintype.card_option, Fintype.card_coe, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

end CardCone

/-! ### the number of points of a quadric depends only on its type -/

section CardType

variable {N : ℕ}

theorem secQ_eq_of {q q' : V N → F} (h : ∀ x, q x = q' x) : secQ q ⊤ = secQ q' ⊤ := by
  obtain rfl : q = q' := funext h
  rfl

theorem card_secQ_shift {q : V N → F} (hq : IsQuad q) {d : V N} (hd : q d = 0) :
    (secQ (fun x => q x + omega d x) ⊤).card = (secQ q ⊤).card := by
  rw [secQ_shift hq hd, Finset.card_image_of_injective _ (tvL_injective d)]

theorem card_secQ_type {q : V N → F} {c : V N} (hc : ∀ x, q x = qplus x + omega c x)
    {c₀ : V N} (hc₀ : qplus c₀ = 1) :
    (secQ q ⊤).card = if qplus c = 0 then (secQ (qplus : V N → F) ⊤).card
      else (secQ (fun x => qplus x + omega c₀ x) ⊤).card := by
  split_ifs with h
  · rw [secQ_eq_of hc]
    exact card_secQ_shift qplus_isQuad h
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
    rw [secQ_eq_of hq]
    exact card_secQ_shift hqm hd

theorem card_secQ_qminus {n : ℕ} {q : V (n + 1) → F} {c : V (n + 1)}
    (hc : ∀ x, q x = qplus x + omega c x) :
    (secQ q ⊤).card = if qplus c = 0 then (secQ (qplus : V (n + 1) → F) ⊤).card
      else (secQ (qminus : V (n + 1) → F) ⊤).card := by
  rw [card_secQ_type hc (qplus_Y0 n), secQ_eq_of (q := qminus) (qminus_eq n)]

end CardType

/-! ### tangent sections: degree and number of points -/

theorem tangent_quad_card {n : ℕ} {q : V (n + 1) → F} (hq : IsQuad q) {a : V (n + 1)} (ha0 : a ≠ 0)
    (ha : q a = 0) :
    ∃ q₀ : V n → F, IsQuad q₀ ∧
      (configX (secQ q (hyp a)) (zero_not_mem_secQ q _)).deg =
        4 * (configX (secQ q₀ ⊤) (zero_not_mem_secQ q₀ ⊤)).deg ∧
      (secQ q (hyp a)).card = ((secQ q₀ ⊤).card + 1) * 2 - 1 := by
  have hR : ∀ r ∈ radical (hyp a), q r = 0 := by
    intro r hr
    rw [radical_hyp_eq ha0, Submodule.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    rcases F_cases c with rfl | rfl
    · rw [zero_smul, hq.map_zero]
    · rw [one_smul, ha]
  obtain ⟨k', t', ⟨D⟩⟩ := exists_sympData (hyp a)
  have e1 : t' = 1 := by rw [← finrank_radical_hyp ha0, finrank_radical_of_sympData D]
  subst e1
  have e2 : k' = n := by have := finrank_of_sympData D; rw [finrank_hyp ha0] at this; omega
  subst e2
  refine ⟨qInd q D, qInd_isQuad hq D, by rw [secQ_deg_of_sympData hq D hR, pow_one], ?_⟩
  have hXS : ∀ p ∈ XY (secQ (qInd q D) ⊤) 1, p ∈ Sstd k' 1 := fun p hp => Xstd_sub k' 1 (XY_sub_Xstd hp)
  rw [secQ_eq_image_XY hq D hR, Finset.card_image_of_injOn (fun x hx y hy h =>
    psiMap_injOn D (hXS x hx) (hXS y hy) h), card_XY _ (zero_not_mem_secQ _ ⊤), pow_one]

/-! ### concrete counts (finite computations) -/

theorem card_QP5 : QP5.card = 35 := by native_decide
theorem card_QM5 : QM5.card = 27 := by native_decide

def QM4 : Finset (V 4) := Finset.univ.filter (fun p => p ≠ 0 ∧ qminus p = 0)
theorem card_QM4 : QM4.card = 119 := by native_decide

theorem secQ_qminus4 : secQ (qminus : V 4 → F) ⊤ = QM4 := by
  ext x; simp [mem_secQ, QM4]

theorem secQ_hyp_eq {N : ℕ} (q : V N → F) (a : V N) :
    secQ q (hyp a) = Finset.univ.filter (fun x => x ≠ 0 ∧ omega a x = 0 ∧ q x = 0) := by
  ext x; simp [mem_secQ, mem_hyp]

theorem tan_count_plus7 : ∀ a : V 4, a ≠ 0 → qplus a = 0 →
    (Finset.univ.filter (fun x : V 4 => x ≠ 0 ∧ omega a x = 0 ∧ qplus x = 0)).card = 71 := by
  native_decide

theorem tan_count_minus7 : ∀ a : V 4, a ≠ 0 → qminus a = 0 →
    (Finset.univ.filter (fun x : V 4 => x ≠ 0 ∧ omega a x = 0 ∧ qminus x = 0)).card = 55 := by
  native_decide

theorem tan_count_plus9 : ∀ a : V 5, a ≠ 0 → qplus a = 0 →
    (Finset.univ.filter (fun x : V 5 => x ≠ 0 ∧ omega a x = 0 ∧ qplus x = 0)).card = 271 := by
  native_decide

/-! ### the tangent values -/

/-- **Tangent hyperplane sections of Q⁺(7,2)**: degree 84 = 4 · deg Q⁺(5,2). -/
theorem tangent_Qplus7 {a : V 4} (ha0 : a ≠ 0) (ha : qplus a = 0) :
    (configX (secQ qplus (hyp a)) (zero_not_mem_secQ _ _)).deg = 84 := by
  obtain ⟨q₀, hq₀, hdeg, hcard⟩ := tangent_quad_card (n := 3) qplus_isQuad ha0 ha
  rw [secQ_hyp_eq, tan_count_plus7 a ha0 ha] at hcard
  obtain ⟨c, hc⟩ := quad_eq_qplus_add hq₀
  rw [card_secQ_qminus (n := 2) hc, secQ_qplus3, secQ_qminus3, card_QP5, card_QM5] at hcard
  rw [hdeg, deg_quad5 hc]
  split_ifs at hcard ⊢
  · rfl
  · omega

/-- **Tangent hyperplane sections of Q⁻(7,2)**: degree 36 = 4 · deg Q⁻(5,2). -/
theorem tangent_Qminus7 {a : V 4} (ha0 : a ≠ 0) (ha : qminus a = 0) :
    (configX (secQ qminus (hyp a)) (zero_not_mem_secQ _ _)).deg = 36 := by
  obtain ⟨q₀, hq₀, hdeg, hcard⟩ := tangent_quad_card (n := 3) qminus_isQuad ha0 ha
  rw [secQ_hyp_eq, tan_count_minus7 a ha0 ha] at hcard
  obtain ⟨c, hc⟩ := quad_eq_qplus_add hq₀
  rw [card_secQ_qminus (n := 2) hc, secQ_qplus3, secQ_qminus3, card_QP5, card_QM5] at hcard
  rw [hdeg, deg_quad5 hc]
  split_ifs at hcard ⊢
  · omega
  · rfl

/-- **Tangent hyperplane sections of Q⁺(9,2)**: degree 1260 = 4 · deg Q⁺(7,2). -/
theorem tangent_Qplus9 {a : V 5} (ha0 : a ≠ 0) (ha : qplus a = 0) :
    (configX (secQ qplus (hyp a)) (zero_not_mem_secQ _ _)).deg = 1260 := by
  obtain ⟨q₀, hq₀, hdeg, hcard⟩ := tangent_quad_card (n := 4) qplus_isQuad ha0 ha
  rw [secQ_hyp_eq, tan_count_plus9 a ha0 ha] at hcard
  obtain ⟨c, hc⟩ := quad_eq_qplus_add hq₀
  rw [card_secQ_qminus (n := 3) hc, secQ_qplus4, secQ_qminus4, card_QP, card_QM4] at hcard
  by_cases h0 : qplus c = 0
  · rw [hdeg, deg_quad7_plus hc h0]
  · rw [if_neg h0] at hcard; omega

end PauliCtx.Spectral
