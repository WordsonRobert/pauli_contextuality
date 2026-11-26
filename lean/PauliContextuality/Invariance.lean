/-
Invariance.lean — ALG-1b (duality) and ALG-3 (invariance of the degree), 01_algebra.md.

  * `incidence`             : the incidence map H : F^P → F^L.
  * `mem_range_of_cycles`   : ALG-1b. A vector orthogonal to every cycle lies in Im H
                              (via `Submodule.forall_mem_dualAnnihilator_apply_eq_zero_iff`).
  * `deg_eq_of_cycles`      : ALG-1 + ALG-1b. Configurations with the same lines and the same
                              parity on every cycle have the same degree.
  * `deg_invariant`         : ALG-3. Two Pauli realisations of the same configuration whose labels
                              have the same pairwise ω have the same degree (uses ALG-2).
  * `deg_invariant_equiv`   : ALG-3 along a bijection of point sets.
-/
import PauliContextuality.CycleSign
import PauliContextuality.Bounds
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Field.ZMod

namespace PauliCtx

instance fact_prime_two' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

namespace Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-- the incidence map `H : F^P → F^L`, `(Hs)_ℓ = Σ_{p∈ℓ} s p` -/
def incidence (L : Finset (Finset α)) : (α → F) →ₗ[F] (L → F) where
  toFun s := fun l => ∑ p ∈ (l : Finset α), s p
  map_add' := by intro s t; ext l; simp [Finset.sum_add_distrib]
  map_smul' := by intro c s; ext l; simp [Finset.mul_sum]

theorem dual_apply_eq_sum {L : Finset (Finset α)} (φ : Module.Dual F (L → F)) (u : L → F) :
    φ u = ∑ l, u l * φ (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : Pi.single l (u l) = u l • (Pi.single l 1 : L → F) := by
    ext m; by_cases h : m = l
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [this, map_smul, smul_eq_mul]

theorem natCast_eq_zero_iff_even (k : ℕ) : (k : F) = 0 ↔ Even k := by
  exact ZMod.natCast_eq_zero_iff_even

/-- ALG-1b (duality). If `v` (a function on lines) sums to zero over every cycle, then `v = Hs`. -/
theorem mem_range_of_cycles (L : Finset (Finset α)) (v : Finset α → F)
    (hv : ∀ Y ⊆ L, IsCycle Y → ∑ l ∈ Y, v l = 0) :
    ∃ t : α → F, ∀ l ∈ L, ∑ p ∈ l, t p = v l := by
  let vL : L → F := fun l => v l
  have hmem : vL ∈ LinearMap.range (incidence L) := by
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (K := F) (V := L → F)
      (LinearMap.range (incidence L)) vL).1 ?_
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    -- the cycle defined by φ
    let yf : Finset α → F := fun l => if h : l ∈ L then φ (Pi.single ⟨l, h⟩ 1) else 0
    let Y : Finset (Finset α) := L.filter (fun l => yf l = 1)
    have hyf : ∀ l, yf l = 0 ∨ yf l = 1 := fun l => by
      generalize yf l = t; revert t; decide
    have hsumY : ∀ f : Finset α → F, ∑ l ∈ Y, f l = ∑ l ∈ L, yf l * f l := by
      intro f
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun l _ => ?_
      rcases hyf l with h | h <;> simp [h]
    have hφu : ∀ u : L → F, φ u = ∑ l ∈ L, yf l * (if h : l ∈ L then u ⟨l, h⟩ else 0) := by
      intro u
      rw [dual_apply_eq_sum, ← Finset.sum_coe_sort L]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [yf, dif_pos l.2, Subtype.coe_eta]
      ring
    have hcyc : IsCycle Y := by
      intro p
      rw [← natCast_eq_zero_iff_even, Finset.card_filter, Nat.cast_sum]
      have h0 := hφ (incidence L (Pi.single p 1)) (LinearMap.mem_range_self _ _)
      rw [hφu] at h0
      rw [← h0]
      have := hsumY (fun l => ((if p ∈ l then 1 else 0 : ℕ) : F))
      rw [this]
      refine Finset.sum_congr rfl fun l hl => ?_
      congr 1
      rw [dif_pos hl]
      simp only [incidence, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_pi_single']
      split_ifs <;> simp
    have h1 := hv Y (Finset.filter_subset _ _) hcyc
    rw [hφu, ← h1, hsumY]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [dif_pos hl]
  obtain ⟨t, ht⟩ := hmem
  refine ⟨t, fun l hl => ?_⟩
  have := congrFun ht ⟨l, hl⟩
  simpa [incidence] using this

/-- ALG-1 + ALG-1b: the degree only depends on the parities of the signs on cycles. -/
theorem deg_eq_of_cycles (C C' : Config α) (hl : C.lines = C'.lines)
    (hcyc : ∀ Y ⊆ C.lines, IsCycle Y → ∑ l ∈ Y, C.sign l = ∑ l ∈ Y, C'.sign l) :
    C.deg = C'.deg := by
  obtain ⟨t, ht⟩ := mem_range_of_cycles C.lines (fun l => C.sign l + C'.sign l) (by
    intro Y hY hY'
    rw [Finset.sum_add_distrib, hcyc Y hY hY', add_self_F])
  refine deg_gauge C C' hl t fun l hl' => ?_
  rw [ht l hl', ← add_assoc, add_self_F, zero_add]

/-- transport of a configuration along a bijection of points -/
def mapEquiv {β : Type} [Fintype β] [DecidableEq β] (C : Config α) (π : α ≃ β) : Config β where
  lines := C.lines.image (fun l => l.map π.toEmbedding)
  sign := fun l => C.sign (l.map π.symm.toEmbedding)
  three := by
    intro l hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
    rw [Finset.card_map]
    exact C.three m hm

theorem map_symm_map {β : Type} (π : α ≃ β) (m : Finset α) :
    (m.map π.toEmbedding).map π.symm.toEmbedding = m := by
  ext x; simp

theorem deg_mapEquiv {β : Type} [Fintype β] [DecidableEq β] (C : Config α) (π : α ≃ β) :
    (C.mapEquiv π).deg = C.deg := by
  have key : ∀ s : α → F, ((C.mapEquiv π).violated (s ∘ π.symm)).card = (C.violated s).card := by
    intro s
    have hsum : ∀ m : Finset α, ∑ x ∈ m.map π.toEmbedding, (s ∘ π.symm) x = ∑ p ∈ m, s p := by
      intro m; rw [Finset.sum_map]; simp
    have : (C.mapEquiv π).violated (s ∘ π.symm) =
        (C.violated s).image (fun l => l.map π.toEmbedding) := by
      ext l
      simp only [violated, mapEquiv, Violated, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨m, hm, rfl⟩, hv⟩
        refine ⟨m, ⟨hm, ?_⟩, rfl⟩
        rw [hsum, map_symm_map] at hv; exact hv
      · rintro ⟨m, ⟨hm, hv⟩, rfl⟩
        refine ⟨⟨m, hm, rfl⟩, ?_⟩
        rw [hsum, map_symm_map]; exact hv
    rw [this, Finset.card_image_of_injective _ (Finset.map_injective _)]
  apply le_antisymm
  · obtain ⟨s, hs⟩ := C.exists_opt
    rw [← hs, ← key s]; exact deg_le _ _
  · obtain ⟨s, hs⟩ := (C.mapEquiv π).exists_opt
    have := key (s ∘ π)
    have e : (s ∘ π) ∘ π.symm = s := by ext x; simp
    rw [e, hs] at this
    rw [this]; exact deg_le _ _

end Config

/-! ### Pauli realisations -/

variable {n n' : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- `ι` realises `C` by Pauli labels: every line is `{a,b,c}` with `ι a, ι b, ι c` a line whose
Pauli sign is the configuration's sign. -/
structure PauliRealization (C : Config α) (ι : α → V n) : Prop where
  inj : Function.Injective ι
  lines : ∀ l ∈ C.lines, ∃ a b c : α, l = {a, b, c} ∧ IsLine (ι a) (ι b) (ι c) ∧
    C.sign l = sign (ι a) (ι b) (ι c)

theorem signK_perm' {a b c : V n} (h : IsLine a b c) :
    signK b a c = signK a b c ∧ signK a c b = signK a b c ∧ signK b c a = signK a b c ∧
    signK c a b = signK a b c ∧ signK c b a = signK a b c := by
  have e1 := signK_swap12 h
  have e2 := signK_swap23 h
  have e3 := signK_swap23 h.swap12
  have e4 := signK_swap12 h.swap23
  have e5 := signK_swap23 h.swap23.swap12
  exact ⟨e1.symm, e2.symm, by rw [← e3, ← e1], by rw [← e4, ← e2], by rw [← e5, ← e4, ← e2]⟩

/-- the sign of a line does not depend on the ordering of its points -/
theorem sign_of_perm {a b c a' b' c' : V n} (h : IsLine a b c) (h' : IsLine a' b' c')
    (ha : a' = a ∨ a' = b ∨ a' = c) (hb : b' = a ∨ b' = b ∨ b' = c) (hc : c' = a ∨ c' = b ∨ c' = c) :
    sign a' b' c' = sign a b c := by
  have hp := signK_perm' h
  unfold sign
  have hne1 := h'.ne_ab; have hne2 := h'.ne_ac; have hne3 := h'.ne_bc
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
    | rfl
    | rw [hp.1] | rw [hp.2.1] | rw [hp.2.2.1] | rw [hp.2.2.2.1] | rw [hp.2.2.2.2]

theorem sum_triple {β : Type} [AddCommMonoid β] {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : α → β) : ∑ x ∈ ({a, b, c} : Finset α), f x = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]), Finset.sum_singleton,
    add_assoc]

/-- If `ι'` realises `C'` and `{a,b,c}` is a line of `C'` with `ι' a, ι' b` commuting, then
`(ι' a, ι' b, ι' c)` is a line with the sign of `C'`. -/
theorem realization_any_order {C' : Config α} {ι' : α → V n'} (hC' : PauliRealization C' ι')
    {l : Finset α} (hl : l ∈ C'.lines) {a b c : α} (hlabc : l = {a, b, c}) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hω : omega (ι' a) (ι' b) = 0) :
    IsLine (ι' a) (ι' b) (ι' c) ∧ C'.sign l = sign (ι' a) (ι' b) (ι' c) := by
  obtain ⟨a', b', c', hl', hline, hsign⟩ := hC'.lines l hl
  have hinj := hC'.inj
  have mem : ∀ x, x ∈ l → x = a' ∨ x = b' ∨ x = c' := fun x hx => by
    rw [hl'] at hx; simpa using hx
  have mem' : ∀ x, x ∈ l → x = a ∨ x = b ∨ x = c := fun x hx => by
    rw [hlabc] at hx; simpa using hx
  have hne' : a' ≠ b' ∧ a' ≠ c' ∧ b' ≠ c' :=
    ⟨fun h => hline.ne_ab (by rw [h]), fun h => hline.ne_ac (by rw [h]), fun h => hline.ne_bc (by rw [h])⟩
  have hsum : ι' a + ι' b + ι' c = ι' a' + ι' b' + ι' c' := by
    have e1 := sum_triple hab hac hbc ι'
    have e2 := sum_triple hne'.1 hne'.2.1 hne'.2.2 ι'
    rw [← hlabc] at e1; rw [← hl'] at e2
    rw [← e1, ← e2]
  have nz : ∀ x ∈ l, ι' x ≠ 0 := by
    intro x hx
    rcases mem x hx with rfl | rfl | rfl
    exacts [hline.nz_a, hline.nz_b, hline.nz_c]
  have hal : a ∈ l := by rw [hlabc]; simp
  have hbl : b ∈ l := by rw [hlabc]; simp
  have hcl : c ∈ l := by rw [hlabc]; simp
  have hL : IsLine (ι' a) (ι' b) (ι' c) :=
    { ne_ab := fun h => hab (hinj h), ne_ac := fun h => hac (hinj h), ne_bc := fun h => hbc (hinj h),
      nz_a := nz a hal, nz_b := nz b hbl, nz_c := nz c hcl,
      sum_zero := by rw [hsum]; exact hline.sum_zero, comm := hω }
  refine ⟨hL, ?_⟩
  rw [hsign]
  symm
  apply sign_of_perm hline hL
  · rcases mem a hal with h | h | h <;> simp [h]
  · rcases mem b hbl with h | h | h <;> simp [h]
  · rcases mem c hcl with h | h | h <;> simp [h]

/-! #### compatible orders -/

/-- the sort key: the points `ι a` come first, in the order of `Fintype.equivFin α` -/
noncomputable def keyV (ι : α → V n) (v : V n) : ℕ ×ₗ ℕ :=
  toLex (if h : ∃ a, ι a = v then (0, (Fintype.equivFin α (Classical.choose h)).val)
    else (1, (Fintype.equivFin (V n) v).val))

theorem keyV_inj (ι : α → V n) : Function.Injective (keyV ι) := by
  intro v w hvw
  unfold keyV at hvw
  simp only [toLex_inj] at hvw
  by_cases hv : ∃ a, ι a = v <;> by_cases hw : ∃ a, ι a = w
  · rw [dif_pos hv, dif_pos hw, Prod.mk.injEq] at hvw
    have := (Fintype.equivFin α).injective (Fin.ext hvw.2)
    rw [← Classical.choose_spec hv, ← Classical.choose_spec hw, this]
  · rw [dif_pos hv, dif_neg hw, Prod.mk.injEq] at hvw; exact absurd hvw.1 (by norm_num)
  · rw [dif_neg hv, dif_pos hw, Prod.mk.injEq] at hvw; exact absurd hvw.1 (by norm_num)
  · rw [dif_neg hv, dif_neg hw, Prod.mk.injEq] at hvw
    exact (Fintype.equivFin (V n)).injective (Fin.ext hvw.2)

/-- an order on `V n` in which the points `ι a` come first, in the order of `α` -/
noncomputable def ordV (ι : α → V n) (_hι : Function.Injective ι) : LinearOrder (V n) :=
  LinearOrder.lift' (keyV ι) (keyV_inj ι)

theorem ordV_lt (ι : α → V n) (hι : Function.Injective ι) (p q : α) :
    (ordV ι hι).lt (ι q) (ι p) ↔ (Fintype.equivFin α q).val < (Fintype.equivFin α p).val := by
  have hq : ∃ a, ι a = ι q := ⟨q, rfl⟩
  have hp : ∃ a, ι a = ι p := ⟨p, rfl⟩
  have eq : Classical.choose hq = q := hι (Classical.choose_spec hq)
  have ep : Classical.choose hp = p := hι (Classical.choose_spec hp)
  show keyV ι (ι q) < keyV ι (ι p) ↔ _
  unfold keyV
  rw [dif_pos hq, dif_pos hp, eq, ep, Prod.Lex.toLex_lt_toLex]
  simp

/-- inversion count of a word over `α` w.r.t. the order of `Fintype.equivFin α` -/
noncomputable def invα (ι : α → V n) : List α → F
  | [] => 0
  | p :: ps => ((ps.filter (fun q => (Fintype.equivFin α q).val < (Fintype.equivFin α p).val)).map
      (fun q => omega (ι p) (ι q))).sum + invα ι ps

theorem invSign_map (ι : α → V n) (hι : Function.Injective ι) (w : List α) :
    @invSign n (ordV ι hι) (w.map ι) = invα ι w := by
  letI := ordV ι hι
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [List.map_cons, invSign, invα, ih]
    have hf : List.filter ((fun q => decide (q < ι p)) ∘ ι) w =
        List.filter (fun q => decide ((Fintype.equivFin α q).val < (Fintype.equivFin α p).val)) w :=
      List.filter_congr (fun q _ => by
        simp only [Function.comp_apply, decide_eq_decide]; exact ordV_lt ι hι p q)
    rw [List.filter_map, List.map_map, hf]
    rfl

theorem invα_congr (ι : α → V n) (ι' : α → V n') (hω : ∀ p q, omega (ι' p) (ι' q) = omega (ι p) (ι q))
    (w : List α) : invα ι' w = invα ι w := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [invα, ih, hω]

/-! #### ALG-3 -/

/-- the word of a list of triples over `α` -/
def wordα (L : List (α × α × α)) : List α := L.flatMap (fun t => [t.1, t.2.1, t.2.2])

theorem tripleWord_map (ι : α → V n) (L : List (α × α × α)) :
    tripleWord (L.map (fun t => (ι t.1, ι t.2.1, ι t.2.2))) = (wordα L).map ι := by
  induction L with
  | nil => rfl
  | cons t L ih => simp [tripleWord, wordα] at ih ⊢; exact ih

theorem count_wordα (L : List (α × α × α)) (hL : ∀ t ∈ L, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
    (p : α) : (wordα L).count p = L.countP (fun t => p ∈ ({t.1, t.2.1, t.2.2} : Finset α)) := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    simp only [wordα, List.flatMap_cons, List.count_append] at ih ⊢
    rw [ih (fun s hs => hL s (List.mem_cons_of_mem _ hs)), List.countP_cons]
    simp only [List.count_cons, List.count_nil, beq_iff_eq, Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨h1, h2, h3⟩ := ht
    by_cases e1 : p = t.1 <;> by_cases e2 : p = t.2.1 <;> by_cases e3 : p = t.2.2 <;>
      simp_all [eq_comm] <;> omega

/-- ALG-3 (same point set). Two Pauli realisations `ι`, `ι'` of configurations `C`, `C'` with the
same lines and the same pairwise symplectic products have the same degree. -/
theorem deg_invariant (C C' : Config α) (ι : α → V n) (ι' : α → V n')
    (hC : PauliRealization C ι) (hC' : PauliRealization C' ι') (hl : C.lines = C'.lines)
    (hω : ∀ p q, omega (ι' p) (ι' q) = omega (ι p) (ι q)) : C.deg = C'.deg := by
  apply Config.deg_eq_of_cycles C C' hl
  intro Y hY hcyc
  -- choose a triple for every line of Y
  have hT : ∀ l : Y, ∃ t : α × α × α, (l : Finset α) = {t.1, t.2.1, t.2.2} ∧
      IsLine (ι t.1) (ι t.2.1) (ι t.2.2) ∧ C.sign l = sign (ι t.1) (ι t.2.1) (ι t.2.2) := by
    intro l
    obtain ⟨a, b, c, h1, h2, h3⟩ := hC.lines l (hY l.2)
    exact ⟨(a, b, c), h1, h2, h3⟩
  choose T hT1 hT2 hT3 using hT
  set Lα : List (α × α × α) := Y.attach.toList.map T
  have hdist : ∀ t ∈ Lα, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
    intro t ht
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
    have h := hT2 l
    exact ⟨fun e => h.ne_ab (by rw [e]), fun e => h.ne_ac (by rw [e]), fun e => h.ne_bc (by rw [e])⟩
  -- the word has even multiplicities
  have hevenα : ∀ p : α, Even ((wordα Lα).count p) := by
    intro p
    rw [count_wordα Lα hdist]
    have : Lα.countP (fun t => p ∈ ({t.1, t.2.1, t.2.2} : Finset α)) = (Y.filter (fun l => p ∈ l)).card := by
      simp only [Lα, List.countP_map]
      have e1 : (Y.attach.toList.countP ((fun t : α × α × α => decide (p ∈ ({t.1, t.2.1, t.2.2} : Finset α))) ∘ T))
          = (Y.attach.filter (fun l => p ∈ l.1)).card := by
        have hfun : ((fun t : α × α × α => decide (p ∈ ({t.1, t.2.1, t.2.2} : Finset α))) ∘ T) =
            (fun l : Y => decide (p ∈ l.1)) := by
          funext l; simp only [Function.comp_apply, ← hT1 l]
        rw [hfun, ← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter]
        rfl
      rw [e1, Finset.card_filter, Finset.card_filter]
      exact Finset.sum_attach Y (fun l => if p ∈ l then 1 else 0)
    rw [this]; exact hcyc p
  have heven_map : ∀ (κ : α → V n) (hκ : Function.Injective κ) (v : V n),
      Even (((wordα Lα).map κ).count v) := by
    intro κ hκ v
    by_cases hv : ∃ p, κ p = v
    · obtain ⟨p, rfl⟩ := hv; rw [List.count_map_of_injective _ _ hκ]; exact hevenα p
    · rw [List.count_eq_zero.2]
      · exact ⟨0, rfl⟩
      · intro hm; obtain ⟨p, _, hp⟩ := List.mem_map.1 hm; exact hv ⟨p, hp⟩
  have heven_map' : ∀ (κ : α → V n') (hκ : Function.Injective κ) (v : V n'),
      Even (((wordα Lα).map κ).count v) := by
    intro κ hκ v
    by_cases hv : ∃ p, κ p = v
    · obtain ⟨p, rfl⟩ := hv; rw [List.count_map_of_injective _ _ hκ]; exact hevenα p
    · rw [List.count_eq_zero.2]
      · exact ⟨0, rfl⟩
      · intro hm; obtain ⟨p, _, hp⟩ := List.mem_map.1 hm; exact hv ⟨p, hp⟩
  -- the C'-triples are lines with the C'-sign
  have hT' : ∀ l : Y, IsLine (ι' (T l).1) (ι' (T l).2.1) (ι' (T l).2.2) ∧
      C'.sign l = sign (ι' (T l).1) (ι' (T l).2.1) (ι' (T l).2.2) := by
    intro l
    have h := hT2 l
    refine realization_any_order hC' (hl ▸ hY l.2) (hT1 l) (fun e => h.ne_ab (by rw [e]))
      (fun e => h.ne_ac (by rw [e])) (fun e => h.ne_bc (by rw [e])) ?_
    rw [hω]; exact h.comm
  -- both sides are inversion counts
  have hsum : ∀ (f : Finset α → F), ∑ l ∈ Y, f l = (Y.attach.toList.map (fun l => f l.1)).sum := by
    intro f; rw [Finset.sum_map_toList]; exact (Finset.sum_attach Y f).symm
  have lhs : ∑ l ∈ Y, C.sign l = invα ι (wordα Lα) := by
    letI := ordV ι hC.inj
    rw [hsum, ← invSign_map ι hC.inj, ← tripleWord_map]
    rw [← cycle_parity_eq_inversions]
    · simp only [Lα, List.map_map]
      congr 1
      exact List.map_congr_left (fun l _ => hT3 l)
    · intro t ht
      simp only [Lα, List.map_map, List.mem_map] at ht
      obtain ⟨l, -, rfl⟩ := ht
      exact hT2 l
    · rw [tripleWord_map]; exact heven_map ι hC.inj
  have rhs : ∑ l ∈ Y, C'.sign l = invα ι' (wordα Lα) := by
    letI := ordV ι' hC'.inj
    rw [hsum, ← invSign_map ι' hC'.inj, ← tripleWord_map]
    rw [← cycle_parity_eq_inversions]
    · simp only [Lα, List.map_map]
      congr 1
      exact List.map_congr_left (fun l _ => (hT' l).2)
    · intro t ht
      simp only [Lα, List.map_map, List.mem_map] at ht
      obtain ⟨l, -, rfl⟩ := ht
      exact (hT' l).1
    · rw [tripleWord_map]; exact heven_map' ι' hC'.inj
  rw [lhs, rhs, invα_congr ι ι' hω]

/-- ALG-3 along a bijection: if `π : α ≃ β` maps the lines of `C` onto the lines of `C'` and
preserves ω of the realising labels, then `deg C = deg C'`. -/
theorem deg_invariant_equiv {β : Type} [Fintype β] [DecidableEq β] (C : Config α) (C' : Config β)
    (π : α ≃ β) (ι : α → V n) (ι' : β → V n')
    (hC : PauliRealization C ι) (hC' : PauliRealization C' ι')
    (hl : C'.lines = C.lines.image (fun l => l.map π.toEmbedding))
    (hω : ∀ p q, omega (ι' (π p)) (ι' (π q)) = omega (ι p) (ι q)) : C.deg = C'.deg := by
  have hdeg := Config.deg_mapEquiv C' π.symm
  rw [← hdeg]
  refine deg_invariant C (C'.mapEquiv π.symm) ι (ι' ∘ π) hC ?_ ?_ (fun p q => hω p q)
  · refine ⟨hC'.inj.comp π.injective, fun l hl' => ?_⟩
    simp only [Config.mapEquiv, Finset.mem_image] at hl'
    obtain ⟨m, hm, rfl⟩ := hl'
    obtain ⟨a, b, c, h1, h2, h3⟩ := hC'.lines m hm
    refine ⟨π.symm a, π.symm b, π.symm c, ?_, by simpa using h2, ?_⟩
    · rw [h1]; ext x; simp [Equiv.symm_apply_eq]
    · show C'.sign ((m.map π.symm.toEmbedding).map π.symm.symm.toEmbedding) = _
      rw [show π.symm.symm = π from rfl]
      have : (m.map π.symm.toEmbedding).map π.toEmbedding = m := by ext x; simp
      rw [this, h3]; simp
  · show C.lines = (C'.lines).image (fun l => l.map π.symm.toEmbedding)
    rw [hl, Finset.image_image]
    have : (fun l : Finset α => (l.map π.toEmbedding).map π.symm.toEmbedding) = id := by
      funext l; exact Config.map_symm_map π l
    rw [Function.comp_def, this, Finset.image_id]

end PauliCtx
