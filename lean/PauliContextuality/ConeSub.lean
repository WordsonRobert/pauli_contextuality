/-
ConeSub.lean — blueprint 06, CONE-3 (a): quadric sections whose form vanishes on the radical.

  Part 1 (cone over an arbitrary point set). For Y ⊆ V k with 0 ∉ Y let
      XY Y t := { v ⊗ Z^σ ≠ 0 : v = 0 or v ∈ Y } ⊆ V (k+t).
    Its commuting zero-sum triples are exactly the images of the lines of Cone_t(configX Y), with the
    cone signs, so `std_sub_degree` : deg XY = 4^t · deg configX Y (CONE-1).  This is the argument of
    `std_section_degree` (Section.lean) with W(2k−1,2) replaced by any induced configuration; no closure
    property of Y is needed, because both sides are induced configurations.
  Part 2 (CONE-3 (a)). If q polarises to ω and vanishes on rad U, then with the normal form ψ of U
    (`exists_sympData`), q₀(v) := q(ψ(v ⊗ 1)) is a quadratic form on V k polarising to ω, and
    U ∩ Q = ψ(XY (Q₀) t).  Hence `Q_section_degree_a` : deg (U ∩ Q) = 4^t · deg Q₀, and with the type
    classification of QuadType, `Q_section_degree_a'` : deg (U ∩ Q) = 4^t · deg Q^±(2k−1,2).
-/
import PauliContextuality.QuadType

open Module

namespace PauliCtx.Spectral

open Config

/-! ### Part 1: the cone over an induced configuration -/

section Sub

variable {k : ℕ} (Y : Finset (V k)) (hY : (0 : V k) ∉ Y) (t : ℕ)

theorem splitL_join (u : V k) (x : V t) : splitL (joinV u x) = u := by
  unfold splitL joinV
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [Fin.append_left]

/-- the cone points v ⊗ Z^σ with v ∈ Y ∪ {0} -/
noncomputable def XY : Finset (V (k + t)) :=
  (Xstd k t).filter (fun p => splitL p = 0 ∨ splitL p ∈ Y)

theorem zero_not_mem_XY : (0 : V (k + t)) ∉ XY Y t := fun h =>
  zero_not_mem_Xstd k t (Finset.mem_filter.1 h).1

variable {Y t}

theorem mem_XY_join {u : V k} {σ : Fin t → F} :
    joinV u (0, σ) ∈ XY Y t ↔ ¬ (u = 0 ∧ σ = 0) ∧ (u = 0 ∨ u ∈ Y) := by
  unfold XY
  rw [Finset.mem_filter, mem_Xstd_join, splitL_join]

theorem XY_sub_Xstd {p : V (k + t)} (hp : p ∈ XY Y t) : p ∈ Xstd k t := (Finset.mem_filter.1 hp).1

variable (Y)

/-- the induced configuration of Y on its point subtype -/
noncomputable def GY : Config (PtX Y) :=
  (configX Y hY).comap (Function.Embedding.subtype _) (linesSub Y hY)
    (fun l hl => by rw [lines_eq_linesSub Y hY]; exact Finset.mem_image_of_mem _ hl)

theorem GY_deg : (GY Y hY).deg = (configX Y hY).deg := by
  unfold GY
  exact deg_comap _ _ _ _ (lines_eq_linesSub Y hY)

/- as in Section.lean, the instances on `Option (PtX Y) × (Fin t → F)` exceed the default
instance-size budget; we synthesise them once with a larger budget. -/
set_option synthInstance.maxSize 1024 in
instance instDecEqCPY (t : ℕ) : DecidableEq (CP (PtX Y) t) := inferInstance

set_option synthInstance.maxSize 1024 in
instance instFintypeCPY (t : ℕ) : Fintype (CP (PtX Y) t) := inferInstance

variable {Y}

/-- the base label of a cone point -/
def baseY : Option (PtX Y) → V k
  | none => 0
  | some u => u.1

/-- (v, τ) ↦ v ⊗ Z^τ -/
def EY (q : CP (PtX Y) t) : V (k + t) := joinV (baseY q.1) (0, q.2)

include hY in
theorem baseY_ne_zero (u : PtX Y) : baseY (some u) ≠ 0 := fun h => hY (h ▸ u.2)

include hY in
theorem EY_inj : Function.Injective (EY (Y := Y) (t := t)) := by
  rintro ⟨o, τ⟩ ⟨o', τ'⟩ h
  obtain ⟨h1, h2⟩ := joinV_inj.1 h
  have hτ : τ = τ' := congrArg Prod.snd h2
  subst hτ
  congr 1
  rcases o with _ | u <;> rcases o' with _ | u'
  · rfl
  · exact absurd h1.symm (baseY_ne_zero hY u')
  · exact absurd h1 (baseY_ne_zero hY u)
  · simp only [baseY] at h1; rw [Subtype.ext h1]

/-- the cone embedding -/
def EYE : CP (PtX Y) t ↪ V (k + t) := ⟨EY, EY_inj hY⟩

theorem ph_EY (q q' : CP (PtX Y) t) : ph (EY q) (EY q') = ph (baseY q.1) (baseY q'.1) :=
  ph_join _ _ _ _

theorem omega_EY (q q' : CP (PtX Y) t) :
    omega (EY q) (EY q') = omega (baseY q.1) (baseY q'.1) := by
  unfold EY; rw [omega_join]; simp [omega]

theorem EY_add (q q' : CP (PtX Y) t) :
    EY q + EY q' = joinV (baseY q.1 + baseY q'.1) (0, q.2 + q'.2) := by
  unfold EY; rw [joinV_add]; congr 1

include hY in
theorem EY_mem {q : CP (PtX Y) t} (hq : q ≠ (none, 0)) : EY q ∈ XY Y t := by
  unfold EY
  rw [mem_XY_join]
  rcases q with ⟨_ | u, σ⟩
  · refine ⟨?_, Or.inl rfl⟩
    rintro ⟨-, h2⟩; apply hq; simp only at h2; rw [h2]
  · exact ⟨fun h => baseY_ne_zero hY u h.1, Or.inr u.2⟩

theorem cone_sub_line_image {L : Finset (CP (PtX Y) t)} (hL : L ∈ (cone t (GY Y hY)).lines) :
    ∃ pq ∈ OP (XY Y t), L.map (EYE hY) = tri pq ∧ sgnF pq = (cone t (GY Y hY)).sign L := by
  rcases Finset.mem_union.1 hL with hl | hvi
  · -- a lift
    simp only [lifts, liftsOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hl
    obtain ⟨ℓ, hℓ, τ, hτ, rfl⟩ := hl
    have hℓW : ℓ.map (Function.Embedding.subtype _) ∈ (configX Y hY).lines := by
      rw [lines_eq_linesSub Y hY]; exact Finset.mem_image_of_mem _ hℓ
    obtain ⟨⟨a, b⟩, hab, habl⟩ := Finset.mem_image.1 hℓW
    have hline := isLine_of_OP hY hab
    obtain ⟨ha, hb, hω, hc⟩ := mem_OP.1 hab
    simp only at ha hb hω hc
    set a' : PtX Y := ⟨a, ha⟩
    set b' : PtX Y := ⟨b, hb⟩
    set c' : PtX Y := ⟨a + b, hc⟩
    have hℓeq : ℓ = {a', b', c'} := by
      apply Finset.map_injective (Function.Embedding.subtype (· ∈ Y))
      rw [← habl]; simp [tri, a', b', c']
    have hne : a' ≠ b' ∧ a' ≠ c' ∧ b' ≠ c' := by
      refine ⟨fun h => hline.ne_ab (congrArg Subtype.val h), fun h => hline.ne_ac (congrArg Subtype.val h),
        fun h => hline.ne_bc (congrArg Subtype.val h)⟩
    have hτc : τ c' = τ a' + τ b' := by
      rw [hℓeq, Finset.sum_insert (by simp [hne.1, hne.2.1]), Finset.sum_insert (by simp [hne.2.2]),
        Finset.sum_singleton, ← add_assoc] at hτ
      exact third_fun t hτ
    refine ⟨(EY (some a', τ a'), EY (some b', τ b')), ?_, ?_, ?_⟩
    · refine mem_OP.2 ⟨EY_mem hY (by simp), EY_mem hY (by simp), ?_, ?_⟩
      · simp only; rw [omega_EY]; exact hω
      · simp only; rw [EY_add]; simp only [baseY]
        rw [mem_XY_join]; exact ⟨fun h => hline.nz_c h.1, Or.inr hc⟩
    · rw [hℓeq]
      simp only [lift, Finset.image_insert, Finset.image_singleton, Finset.map_insert,
        Finset.map_singleton, tri]
      rw [EY_add]
      simp only [EYE, Function.Embedding.coeFn_mk, baseY, hτc]
      rfl
    · rw [cone_sign_lift t hℓ hτ]
      show sgnF (EY (some a', τ a'), EY (some b', τ b')) =
        (configX Y hY).sign (ℓ.map (Function.Embedding.subtype _))
      rw [← habl, configX_sign _ hab]
      unfold sgnF; simp only; rw [ph_EY]; rfl
  · have hnot : L ∉ lifts t (GY Y hY) := vline_not_lift t hvi
    have hsign : (cone t (GY Y hY)).sign L = 0 := by
      show (if L ∈ lifts t (GY Y hY) then _ else 0) = 0; rw [if_neg hnot]
    rw [hsign]
    rcases Finset.mem_union.1 hvi with hv | hi
    · obtain ⟨⟨v, τ, τ'⟩, hx, rfl⟩ := Finset.mem_image.1 hv
      have hne : τ ≠ τ' := (Finset.mem_filter.1 hx).2
      have hττ : τ + τ' ≠ 0 := by
        intro h; apply hne; have := congrArg (τ + ·) h; simpa [← add_assoc, add_self_fun] using this.symm
      refine ⟨(EY (some v, τ), EY (Y := Y) (none, τ + τ')), ?_, ?_, ?_⟩
      · refine mem_OP.2 ⟨EY_mem hY (by simp), EY_mem hY (by simp [hττ]), ?_, ?_⟩
        · simp only; rw [omega_EY]; simp [baseY, omega]
        · simp only; rw [EY_add]; simp only [baseY, add_zero]
          rw [mem_XY_join]; exact ⟨fun h => baseY_ne_zero hY v h.1, Or.inr v.2⟩
      · simp only [Finset.map_insert, Finset.map_singleton, tri, EYE, Function.Embedding.coeFn_mk]
        rw [EY_add]
        simp only [baseY, add_zero]
        have e : τ + (τ + τ') = τ' := by rw [← add_assoc, add_self_fun, zero_add]
        rw [e]
        show {EY (some v, τ), EY (some v, τ'), EY (Y := Y) (none, τ + τ')} =
          ({EY (some v, τ), EY (Y := Y) (none, τ + τ'), EY (some v, τ')} : Finset _)
        rw [fs3_132]
      · unfold sgnF; simp only; rw [ph_EY]; simp only [baseY]
        rw [if_pos]; unfold ph; simp [dot, ycount]
    · obtain ⟨⟨σ, σ'⟩, hx, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hx).2
      have h12 : σ + σ' ≠ 0 := by
        intro h; apply h3; have := congrArg (σ + ·) h; simpa [← add_assoc, add_self_fun] using this.symm
      refine ⟨(EY (Y := Y) (none, σ), EY (Y := Y) (none, σ')), ?_, ?_, ?_⟩
      · refine mem_OP.2 ⟨EY_mem hY (by simp [h1]), EY_mem hY (by simp [h2]), ?_, ?_⟩
        · simp only; rw [omega_EY]; simp [baseY, omega]
        · simp only; rw [EY_add]; simp only [baseY, add_zero]
          rw [mem_XY_join]; exact ⟨fun h => h12 h.2, Or.inl rfl⟩
      · simp only [Finset.map_insert, Finset.map_singleton, tri, EYE, Function.Embedding.coeFn_mk]
        rw [EY_add]
        simp only [baseY, add_zero]
        rfl
      · unfold sgnF; simp only; rw [ph_EY]; simp only [baseY]
        rw [if_pos]; unfold ph; simp [dot, ycount]

theorem XY_split {p : V (k + t)} (hp : p ∈ XY Y t) :
    ∃ u : V k, ∃ σ : Fin t → F, p = joinV u (0, σ) := Xstd_split (XY_sub_Xstd hp)

/-- every commuting zero-sum triple of XY comes from a cone line -/
theorem OP_XY_cone {pq : V (k + t) × V (k + t)} (hpq : pq ∈ OP (XY Y t)) :
    ∃ L ∈ (cone t (GY Y hY)).lines, L.map (EYE hY) = tri pq := by
  obtain ⟨hp, hq, hω, hpq'⟩ := mem_OP.1 hpq
  have hline := isLine_of_OP (zero_not_mem_XY Y t) hpq
  obtain ⟨u, σ, hu⟩ := XY_split hp
  obtain ⟨u', σ', hu'⟩ := XY_split hq
  obtain ⟨p, q⟩ := pq
  simp only at hu hu' hp hq hω hpq' hline
  subst hu hu'
  have hω' : omega u u' = 0 := by rw [omega_join] at hω; simpa [omega] using hω
  have hsum : joinV u (0, σ) + joinV u' (0, σ') = joinV (u + u') (0, σ + σ') := by
    rw [joinV_add]; congr 1
  obtain ⟨hpne, hpY⟩ := mem_XY_join.1 hp
  obtain ⟨hqne, hqY⟩ := mem_XY_join.1 hq
  have hs := hpq'
  rw [hsum, mem_XY_join] at hs
  obtain ⟨hsne, hsY⟩ := hs
  have hne : ¬ (u = u' ∧ σ = σ') := by
    rintro ⟨rfl, rfl⟩; exact hline.ne_ab rfl
  have trieq : tri (joinV u (0, σ), joinV u' (0, σ')) =
      {joinV u (0, σ), joinV u' (0, σ'), joinV (u + u') (0, σ + σ')} := by
    simp only [tri]; rw [hsum]
  by_cases hu0 : u = 0
  · subst hu0
    have hσ : σ ≠ 0 := fun h => hpne ⟨rfl, h⟩
    by_cases hu'0 : u' = 0
    · subst hu'0
      have hσ' : σ' ≠ 0 := fun h => hqne ⟨rfl, h⟩
      have hσσ : σ ≠ σ' := fun h => hne ⟨rfl, h⟩
      refine ⟨{(none, σ), (none, σ'), (none, σ + σ')}, ?_, ?_⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.2
          ⟨(σ, σ'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ, hσ', hσσ⟩, rfl⟩))
      · rw [trieq]; simp [EYE, EY, baseY]
    · have hσσ : σ' ≠ σ + σ' := by
        intro h; apply hσ; have := congrArg (· + σ') h; simpa [add_assoc, add_self_fun] using this.symm
      set v : PtX Y := ⟨u', hqY.resolve_left hu'0⟩
      refine ⟨{(some v, σ'), (some v, σ + σ'), (none, σ' + (σ + σ'))}, ?_, ?_⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.2
          ⟨(v, σ', σ + σ'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hσσ⟩, rfl⟩))
      · rw [trieq]
        have e : σ' + (σ + σ') = σ := by
          rw [add_comm σ σ', ← add_assoc, add_self_fun, zero_add]
        simp only [Finset.map_insert, Finset.map_singleton, EYE, Function.Embedding.coeFn_mk, EY,
          baseY, e, zero_add, v]
        rw [fs3_231]
  · by_cases hu'0 : u' = 0
    · subst hu'0
      have hσ' : σ' ≠ 0 := fun h => hqne ⟨rfl, h⟩
      have hσσ : σ ≠ σ + σ' := by
        intro h; apply hσ'; have := congrArg (σ + ·) h; simpa [← add_assoc, add_self_fun] using this.symm
      set v : PtX Y := ⟨u, hpY.resolve_left hu0⟩
      refine ⟨{(some v, σ), (some v, σ + σ'), (none, σ + (σ + σ'))}, ?_, ?_⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.2
          ⟨(v, σ, σ + σ'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hσσ⟩, rfl⟩))
      · rw [trieq]
        have e : σ + (σ + σ') = σ' := by rw [← add_assoc, add_self_fun, zero_add]
        simp only [Finset.map_insert, Finset.map_singleton, EYE, Function.Embedding.coeFn_mk, EY,
          baseY, e, add_zero, v]
        rw [fs3_132]
    · by_cases huu : u + u' = 0
      · have hueq : u = u' := by
          have := congrArg (u + ·) huu; simpa [← add_assoc, add_self_V] using this.symm
        subst hueq
        have hσσ : σ ≠ σ' := fun h => hne ⟨rfl, h⟩
        set v : PtX Y := ⟨u, hpY.resolve_left hu0⟩
        refine ⟨{(some v, σ), (some v, σ'), (none, σ + σ')}, ?_, ?_⟩
        · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.2
            ⟨(v, σ, σ'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hσσ⟩, rfl⟩))
        · rw [trieq, huu]
          simp [EYE, EY, baseY, v]
      · -- a lift of the base line {u, u', u + u'}
        set a' : PtX Y := ⟨u, hpY.resolve_left hu0⟩
        set b' : PtX Y := ⟨u', hqY.resolve_left hu'0⟩
        set c' : PtX Y := ⟨u + u', hsY.resolve_left huu⟩
        have hab : (u, u') ∈ OP Y :=
          mem_OP.2 ⟨a'.2, b'.2, hω', c'.2⟩
        have hbl := isLine_of_OP hY hab
        set ℓ : Finset (PtX Y) := {a', b', c'}
        have hℓ : ℓ ∈ (GY Y hY).lines := by
          show ℓ ∈ linesSub Y hY
          refine Finset.mem_image.2 ⟨tri (u, u'), Finset.mem_image_of_mem _ hab, ?_⟩
          ext x; simp [tri, ℓ, a', b', c', Subtype.ext_iff]
        set τ : PtX Y → (Fin t → F) := fun x =>
          if x.1 = u then σ else if x.1 = u' then σ' else σ + σ'
        have hτa : τ a' = σ := by simp [τ, a']
        have hτb : τ b' = σ' := by simp [τ, b', hbl.ne_ab.symm]
        have hτc : τ c' = σ + σ' := by simp [τ, c', hbl.ne_ac.symm, hbl.ne_bc.symm]
        have hne' : a' ≠ b' ∧ a' ≠ c' ∧ b' ≠ c' :=
          ⟨fun h => hbl.ne_ab (congrArg Subtype.val h), fun h => hbl.ne_ac (congrArg Subtype.val h),
            fun h => hbl.ne_bc (congrArg Subtype.val h)⟩
        have hτ : ∑ x ∈ ℓ, τ x = 0 := by
          rw [Finset.sum_insert (by simp [hne'.1, hne'.2.1]), Finset.sum_insert (by simp [hne'.2.2]),
            Finset.sum_singleton, hτa, hτb, hτc, ← add_assoc, add_self_fun]
        refine ⟨lift t ℓ τ, Finset.mem_union_left _ ?_, ?_⟩
        · simp only [lifts, liftsOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact ⟨ℓ, hℓ, τ, hτ, rfl⟩
        · rw [trieq]
          simp only [lift, ℓ, Finset.image_insert, Finset.image_singleton, Finset.map_insert,
            Finset.map_singleton, EYE, Function.Embedding.coeFn_mk, EY, baseY, hτa, hτb, hτc]
          rfl

theorem lines_XY :
    (configX (XY Y t) (zero_not_mem_XY Y t)).lines =
      (cone t (GY Y hY)).lines.image (fun L => L.map (EYE hY)) := by
  ext m
  constructor
  · intro hm
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨L, hL, he⟩ := OP_XY_cone hY hpq
    exact Finset.mem_image.2 ⟨L, hL, he⟩
  · intro hm
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨pq, hpq, he, -⟩ := cone_sub_line_image hY hL
    rw [he]; exact Finset.mem_image_of_mem _ hpq

theorem cone_sub_lines_mem :
    ∀ L ∈ (cone t (GY Y hY)).lines,
      L.map (EYE hY) ∈ (configX (XY Y t) (zero_not_mem_XY Y t)).lines :=
  fun L hL => by rw [lines_XY hY]; exact Finset.mem_image_of_mem _ hL

theorem deg_XY_cone :
    (configX (XY Y t) (zero_not_mem_XY Y t)).deg = (cone t (GY Y hY)).deg := by
  rw [← deg_comap _ (EYE hY) _ (cone_sub_lines_mem hY) (lines_XY hY)]
  refine deg_congr _ _ rfl fun L hL => ?_
  obtain ⟨pq, hpq, he, hs⟩ := cone_sub_line_image hY hL
  show (configX (XY Y t) (zero_not_mem_XY Y t)).sign (L.map (EYE hY)) = _
  rw [he, configX_sign (zero_not_mem_XY Y t) hpq, hs]

theorem deg_cone_GY : (cone t (GY Y hY)).deg = 4 ^ t * (configX Y hY).deg := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hYe : Y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx; exact hY (Subsingleton.elim x 0 ▸ hx)
    have h0 : (GY Y hY).deg = 0 := by
      have := (GY Y hY).deg_le_half
      have hL : (GY Y hY).lines.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro l hl
        have h3 := (GY Y hY).three l hl
        have : l = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x _; exact (Finset.notMem_empty x.1) (hYe ▸ x.2)
        rw [this] at h3; simp at h3
      omega
    have := cone_deg_le t (GY Y hY)
    rw [h0] at this
    rw [← GY_deg Y hY, h0]
    omega
  · rw [← GY_deg Y hY]
    refine cone_degree_pauli t (GY Y hY) hk (fun x => x.1) ?_ ?_
    · intro ℓ hℓ
      have hW : ℓ.map (Function.Embedding.subtype _) ∈ (configX Y hY).lines := by
        rw [lines_eq_linesSub Y hY]; exact Finset.mem_image_of_mem _ hℓ
      obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.1 hW
      have h := isLine_of_OP hY hab
      have : ∑ p ∈ ℓ, p.1 = ∑ x ∈ ℓ.map (Function.Embedding.subtype _), x := by
        rw [Finset.sum_map]; rfl
      rw [this, ← he]
      simp only [tri]
      rw [Finset.sum_insert (by simp [h.ne_ab, h.ne_ac]), Finset.sum_insert (by simp [h.ne_bc]),
        Finset.sum_singleton, ← add_assoc, add_self_V]
    · intro ℓ _ a _ b _ hab
      exact ⟨fun h => hab (Subtype.ext h), fun h => hY (h ▸ a.2), fun h => hY (h ▸ b.2)⟩

/-- **CONE-1 for an induced configuration.** deg (Y ⊗ ⟨Z⟩^t ∪ ⟨Z⟩^t) = 4^t · deg Y. -/
theorem std_sub_degree :
    (configX (XY Y t) (zero_not_mem_XY Y t)).deg = 4 ^ t * (configX Y hY).deg := by
  rw [deg_XY_cone hY, deg_cone_GY hY]

end Sub

/-! ### Part 2: CONE-3 (a) -/

section Quad

variable {N : ℕ} {U : Submodule F (V N)} {k t : ℕ}

theorem cX_join (u : V k) (σ : Fin t → F) : cX (joinV u (0, σ)) = u.1 := by
  funext i; simp [cX, joinV, Fin.append_left]

theorem cZ_join (u : V k) (σ : Fin t → F) : cZ (joinV u (0, σ)) = u.2 := by
  funext i; simp [cZ, joinV, Fin.append_left]

theorem cR_join (u : V k) (σ : Fin t → F) : cR (joinV u (0, σ)) = σ := by
  funext j; simp [cR, joinV, Fin.append_right]

theorem psiMap_join (D : SympData U k t) (u : V k) (σ : Fin t → F) :
    psiMap D (joinV u (0, σ)) = comb D.e D.f D.r u.1 u.2 σ := by
  show comb D.e D.f D.r (cX _) (cZ _) (cR _) = _
  rw [cX_join, cZ_join, cR_join]

theorem comb_zero (D : SympData U k t) : comb D.e D.f D.r 0 0 0 = 0 := by
  simp [comb]

theorem comb_split (D : SympData U k t) (c d : Fin k → F) (g : Fin t → F) :
    comb D.e D.f D.r c d g = comb D.e D.f D.r c d 0 + comb D.e D.f D.r 0 0 g := by
  rw [comb_add]; simp

theorem comb_rad_mem (D : SympData U k t) (g : Fin t → F) : comb D.e D.f D.r 0 0 g ∈ radical U := by
  refine mem_radical.2 ⟨comb_mem D _ _ _, fun v hv => ?_⟩
  obtain ⟨c, d, g', rfl⟩ := D.span v hv
  rw [omega_comb]; simp

/-- the induced form on the non-degenerate part: q₀(v) = q(ψ(v ⊗ 1)) -/
def qInd (q : V N → F) (D : SympData U k t) (u : V k) : F := q (comb D.e D.f D.r u.1 u.2 0)

theorem qInd_isQuad {q : V N → F} (hq : IsQuad q) (D : SympData U k t) : IsQuad (qInd q D) := by
  intro a b
  unfold qInd
  have e : comb D.e D.f D.r (a + b).1 (a + b).2 0 =
      comb D.e D.f D.r a.1 a.2 0 + comb D.e D.f D.r b.1 b.2 0 := by
    rw [comb_add]; simp
  rw [e, hq, omega_comb]
  rfl

theorem q_psiMap_join {q : V N → F} (hq : IsQuad q) (D : SympData U k t)
    (hR : ∀ r ∈ radical U, q r = 0) (u : V k) (σ : Fin t → F) :
    q (psiMap D (joinV u (0, σ))) = qInd q D u := by
  rw [psiMap_join, comb_split, hq, hR _ (comb_rad_mem D σ), omega_comb]
  simp [qInd]

theorem secQ_eq_image_XY {q : V N → F} (hq : IsQuad q) (D : SympData U k t)
    (hR : ∀ r ∈ radical U, q r = 0) :
    secQ q U = (XY (secQ (qInd q D) ⊤) t).image (psiMap D) := by
  ext x
  rw [mem_secQ, Finset.mem_image]
  constructor
  · rintro ⟨hx0, hxU, hqx⟩
    have hx : x ∈ secX U := mem_secX.2 ⟨hx0, hxU⟩
    rw [secX_eq_image D, Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨u, σ, rfl⟩ := Xstd_split hp
    refine ⟨joinV u (0, σ), mem_XY_join.2 ⟨mem_Xstd_join.1 hp, ?_⟩, rfl⟩
    by_cases hu : u = 0
    · exact Or.inl hu
    · refine Or.inr (mem_secQ.2 ⟨hu, Submodule.mem_top, ?_⟩)
      rw [← q_psiMap_join hq D hR]; exact hqx
  · rintro ⟨p, hp, rfl⟩
    have hpX := XY_sub_Xstd hp
    have hx : psiMap D p ∈ secX U := by
      rw [secX_eq_image D]; exact Finset.mem_image_of_mem _ hpX
    obtain ⟨hx0, hxU⟩ := mem_secX.1 hx
    refine ⟨hx0, hxU, ?_⟩
    obtain ⟨u, σ, rfl⟩ := Xstd_split hpX
    rw [q_psiMap_join hq D hR]
    rcases (mem_XY_join.1 hp).2 with hu | hu
    · subst hu
      show q (comb D.e D.f D.r 0 0 0) = 0
      rw [comb_zero, hq.map_zero]
    · exact (mem_secQ.1 hu).2.2

theorem secQ_deg_of_sympData {q : V N → F} (hq : IsQuad q) (D : SympData U k t)
    (hR : ∀ r ∈ radical U, q r = 0) :
    (configX (secQ q U) (zero_not_mem_secQ q U)).deg =
      4 ^ t * (configX (secQ (qInd q D) ⊤) (zero_not_mem_secQ _ ⊤)).deg := by
  set X := XY (secQ (qInd q D) ⊤) t
  have hXS : ∀ p ∈ X, p ∈ Sstd k t := fun p hp => Xstd_sub k t (XY_sub_Xstd hp)
  have hspan : Submodule.span F (X : Set (V (k + t))) ≤ Sstd k t := Submodule.span_le.2 hXS
  have hinj : Set.InjOn (psiMap D) (Submodule.span F (X : Set (V (k + t)))) :=
    (psiMap_injOn D).mono hspan
  have hω : ∀ a ∈ X, ∀ b ∈ X, omega (psiMap D a) (psiMap D b) = omega a b :=
    fun a ha b hb => psiMap_omega D (hXS a ha) (hXS b hb)
  have h0' := zero_not_mem_image X (zero_not_mem_XY _ t) (psiMap D) hinj
  rw [configX_deg_congr (secQ_eq_image_XY hq D hR) _ h0',
    deg_configX_map X (zero_not_mem_XY _ t) (psiMap D) hω hinj h0',
    std_sub_degree (zero_not_mem_secQ _ ⊤)]

/-- **CONE-3 (a).** If dim U = 2k + t, dim rad U = t and the quadratic form q (polarising to ω)
vanishes on rad U, then U ∩ Q is a t-fold cone over a non-degenerate quadric Q₀ of V k:
deg (U ∩ Q) = 4^t · deg Q₀, where Q₀ is the quadric of a quadratic form q₀ on V k polarising to ω
(q₀ is q on the non-degenerate part of U, in the normal-form coordinates). -/
theorem Q_section_degree_a {q : V N → F} (hq : IsQuad q) (U : Submodule F (V N)) (k t : ℕ)
    (hk : finrank F U = 2 * k + t) (ht : finrank F (radical U) = t)
    (hR : ∀ r ∈ radical U, q r = 0) :
    ∃ q₀ : V k → F, IsQuad q₀ ∧
      (configX (secQ q U) (zero_not_mem_secQ q U)).deg =
        4 ^ t * (configX (secQ q₀ ⊤) (zero_not_mem_secQ q₀ ⊤)).deg := by
  obtain ⟨k', t', ⟨D⟩⟩ := exists_sympData U
  have e1 : t' = t := by rw [← ht, finrank_radical_of_sympData D]
  subst e1
  have e2 : k' = k := by have := finrank_of_sympData D; omega
  subst e2
  exact ⟨qInd q D, qInd_isQuad hq D, secQ_deg_of_sympData hq D hR⟩

/-- **CONE-3 (a) with the type.** On V (n+1)-coordinates (k = n+1) the cone base is Q⁺(2n+1,2) or
Q⁻(2n+1,2): deg (U ∩ Q) = 4^t · deg Q^δ(2k−1,2) with δ ∈ F₂ the type of q₀. -/
theorem Q_section_degree_a' {q : V N → F} (hq : IsQuad q) (U : Submodule F (V N)) (n t : ℕ)
    (hk : finrank F U = 2 * (n + 1) + t) (ht : finrank F (radical U) = t)
    (hR : ∀ r ∈ radical U, q r = 0) :
    ∃ δ : F, (configX (secQ q U) (zero_not_mem_secQ q U)).deg =
      4 ^ t * (if δ = 0 then (configX (secQ (qplus : V (n + 1) → F) ⊤) (zero_not_mem_secQ _ ⊤)).deg
        else (configX (secQ (qminus : V (n + 1) → F) ⊤) (zero_not_mem_secQ _ ⊤)).deg) := by
  obtain ⟨q₀, hq₀, h⟩ := Q_section_degree_a hq U (n + 1) t hk ht hR
  obtain ⟨c, hc⟩ := quad_eq_qplus_add hq₀
  exact ⟨qplus c, by rw [h, deg_secQ_qminus hc]⟩

/-- the radical of a tangent hyperplane a^⊥ is ⟨a⟩ -/
theorem radical_hyp_eq {a : V N} (ha : a ≠ 0) : radical (hyp a) = Submodule.span F {a} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (mem_radical_hyp_self a)
  · rw [finrank_span_singleton ha, finrank_radical_hyp ha]

/-- **CONE-3, tangent hyperplanes.** If q a = 0 (a ≠ 0), a^⊥ ∩ Q is a cone over a non-degenerate
quadric Q₀ of V n: deg (a^⊥ ∩ Q) = 4 · deg Q₀. -/
theorem tangent_quad_degree {n : ℕ} {q : V (n + 1) → F} (hq : IsQuad q) {a : V (n + 1)} (ha0 : a ≠ 0)
    (ha : q a = 0) :
    ∃ q₀ : V n → F, IsQuad q₀ ∧
      (configX (secQ q (hyp a)) (zero_not_mem_secQ q _)).deg =
        4 * (configX (secQ q₀ ⊤) (zero_not_mem_secQ q₀ ⊤)).deg := by
  have hR : ∀ r ∈ radical (hyp a), q r = 0 := by
    intro r hr
    rw [radical_hyp_eq ha0, Submodule.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    rcases F_cases c with rfl | rfl
    · rw [zero_smul, hq.map_zero]
    · rw [one_smul, ha]
  have := Q_section_degree_a hq (hyp a) n 1 (by rw [finrank_hyp ha0]; omega)
    (finrank_radical_hyp ha0) hR
  simpa using this

/-- **Tangent hyperplane sections of a quadric of W(7,2)** have degree 84 or 36
(= 4 · deg Q^±(5,2)). -/
theorem tangent_quad7 {q : V 4 → F} (hq : IsQuad q) {a : V 4} (ha0 : a ≠ 0) (ha : q a = 0) :
    (configX (secQ q (hyp a)) (zero_not_mem_secQ q _)).deg = 84 ∨
      (configX (secQ q (hyp a)) (zero_not_mem_secQ q _)).deg = 36 := by
  obtain ⟨q₀, hq₀, h⟩ := tangent_quad_degree (n := 3) hq ha0 ha
  rw [h]
  rcases deg_quad5' hq₀ with h' | h'
  · left; rw [h']
  · right; rw [h']

end Quad

end PauliCtx.Spectral
