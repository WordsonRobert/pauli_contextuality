/-
Tractable.lean — blueprint HARD-12 (tractable class).

If every point lies on at most two lines, let `G` be the graph on the lines in which two lines are
adjacent when they share a point. Call a connected component *closed* if none of its points lies
on only one line, and *odd* if its signs sum to 1. Then

    deg C = #{closed odd components}.               (`deg_two_points`)

Lower bound: a closed component is a cycle (CERT-1). Upper bound: in an optimal assignment, two
violated lines of one component could both be repaired by flipping the shared points along a walk
between them; a violated line in a component with a pendant point could be repaired alone; and
in a closed component the number of violated lines has the parity of its sign sum.
-/
import PauliContextuality.Cover
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace PauliCtx.Config

open Classical

variable {α : Type} [Fintype α] [DecidableEq α] (C : Config α)

/-- lines as a type -/
abbrev LV := {l // l ∈ C.lines}

/-- the line graph: two distinct lines are adjacent if they share a point -/
def lineGraph : SimpleGraph (LV C) := SimpleGraph.fromRel (fun ℓ ℓ' => ∃ p, p ∈ ℓ.1 ∧ p ∈ ℓ'.1)

theorem lineGraph_adj {ℓ ℓ' : LV C} :
    (lineGraph C).Adj ℓ ℓ' ↔ ℓ ≠ ℓ' ∧ ∃ p, p ∈ ℓ.1 ∧ p ∈ ℓ'.1 := by
  rw [lineGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩⟩
    · exact ⟨h, p, h1, h2⟩
    · exact ⟨h, p, h2, h1⟩
  · rintro ⟨h, hp⟩; exact ⟨h, Or.inl hp⟩

/-- the number of lines through a point -/
noncomputable def degP (p : α) : ℕ := (C.lines.filter (fun l => p ∈ l)).card

/-- the defect of a line: violated iff ≠ 0 -/
def dfct (s : α → F) (l : Finset α) : F := (∑ p ∈ l, s p) + C.sign l

/-- the parity change of a line under flipping `T` -/
def eff (T : α → F) (l : Finset α) : F := ∑ p ∈ l, T p

variable {C}

theorem two_lines (h2 : ∀ p, C.degP p ≤ 2) {p : α} {ℓ₀ ℓ₁ : LV C} (hne : ℓ₀ ≠ ℓ₁) (h0 : p ∈ ℓ₀.1)
    (h1 : p ∈ ℓ₁.1) (ℓ : LV C) : p ∈ ℓ.1 ↔ ℓ = ℓ₀ ∨ ℓ = ℓ₁ := by
  have hne' : ℓ₀.1 ≠ ℓ₁.1 := fun h => hne (Subtype.ext h)
  have hsub : ({ℓ₀.1, ℓ₁.1} : Finset (Finset α)) ⊆ C.lines.filter (fun l => p ∈ l) := by
    intro l hl
    rw [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact Finset.mem_filter.2 ⟨ℓ₀.2, h0⟩
    · exact Finset.mem_filter.2 ⟨ℓ₁.2, h1⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_pair hne']; exact h2 p)
  constructor
  · intro hp
    have : ℓ.1 ∈ ({ℓ₀.1, ℓ₁.1} : Finset (Finset α)) := heq ▸ Finset.mem_filter.2 ⟨ℓ.2, hp⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl) <;> assumption

theorem one_line {p : α} {m : LV C} (hdeg : C.degP p = 1) (hm : p ∈ m.1) (ℓ : LV C) :
    p ∈ ℓ.1 ↔ ℓ = m := by
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 hdeg
  have hmem : ∀ ℓ : LV C, p ∈ ℓ.1 → ℓ.1 = l := by
    intro ℓ hp
    have : ℓ.1 ∈ C.lines.filter (fun l => p ∈ l) := Finset.mem_filter.2 ⟨ℓ.2, hp⟩
    rw [hl] at this; exact Finset.mem_singleton.1 this
  constructor
  · intro hp; exact Subtype.ext ((hmem ℓ hp).trans (hmem m hm).symm)
  · rintro rfl; exact hm

theorem eff_single (p : α) (l : Finset α) :
    eff (fun q => if q = p then 1 else 0) l = if p ∈ l then 1 else 0 := by
  unfold eff; rw [Finset.sum_ite_eq']

theorem ite_eq_F (P : Prop) [Decidable P] : ((if P then 1 else 0 : F)) = if P then 1 else 0 := rfl

/-- flipping along a walk changes exactly its two ends -/
theorem walk_toggle (h2 : ∀ p, C.degP p ≤ 2) {u v : LV C} (w : (lineGraph C).Walk u v) :
    ∃ T : α → F, ∀ ℓ : LV C, eff T ℓ.1 = (if ℓ = u then 1 else 0) + (if ℓ = v then 1 else 0) := by
  induction w with
  | nil =>
    refine ⟨0, fun ℓ => ?_⟩
    unfold eff; simp only [Pi.zero_apply, Finset.sum_const_zero]
    split_ifs <;> decide
  | @cons u x v hadj w ih =>
    obtain ⟨T', hT'⟩ := ih
    obtain ⟨hne, p, hpu, hpx⟩ := (lineGraph_adj _).1 hadj
    refine ⟨fun q => (if q = p then 1 else 0) + T' q, fun ℓ => ?_⟩
    have : eff (fun q => (if q = p then 1 else 0) + T' q) ℓ.1 =
        eff (fun q => if q = p then 1 else 0) ℓ.1 + eff T' ℓ.1 := by
      unfold eff; rw [Finset.sum_add_distrib]
    rw [this, eff_single, hT' ℓ]
    have hiff := two_lines h2 hne hpu hpx ℓ
    by_cases h1 : ℓ = u
    · have hx : ¬ ℓ = x := fun h => hne (h1.symm.trans h)
      have hp : p ∈ ℓ.1 := hiff.2 (Or.inl h1)
      rw [if_pos hp, if_pos h1, if_neg hx]
      generalize (if ℓ = v then (1 : F) else 0) = t; revert t; decide
    · by_cases h3 : ℓ = x
      · have hp : p ∈ ℓ.1 := hiff.2 (Or.inr h3)
        rw [if_pos hp, if_neg h1, if_pos h3]
        generalize (if ℓ = v then (1 : F) else 0) = t; revert t; decide
      · have : p ∉ ℓ.1 := fun h => (hiff.1 h).elim h1 h3
        rw [if_neg this, if_neg h1, if_neg h3]; ring

theorem dfct_flip (s T : α → F) (l : Finset α) : C.dfct (s + T) l = C.dfct s l + eff T l := by
  unfold dfct eff; simp only [Pi.add_apply, Finset.sum_add_distrib]; ring

theorem violated_iff_dfct (s : α → F) (l : Finset α) : C.Violated s l ↔ C.dfct s l ≠ 0 := Iff.rfl

theorem F_ne_zero {x : F} (h : x ≠ 0) : x = 1 := by revert x; decide

/-- an improving flip contradicts optimality -/
theorem no_improve {s : α → F} (hs : (C.violated s).card = C.deg) (T : α → F) (ℓ₁ : LV C)
    (h1 : eff T ℓ₁.1 ≠ 0) (hT : ∀ ℓ : LV C, eff T ℓ.1 ≠ 0 → C.Violated s ℓ.1) : False := by
  have hsub : C.violated (s + T) ⊆ (C.violated s).erase ℓ₁.1 := by
    intro l hl
    obtain ⟨hlC, hv⟩ := Finset.mem_filter.1 hl
    rw [violated_iff_dfct, dfct_flip] at hv
    by_cases he : eff T l = 0
    · rw [he, add_zero] at hv
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨hlC, hv⟩⟩
      rintro rfl; exact h1 he
    · exfalso
      have hvs := hT ⟨l, hlC⟩ he
      rw [violated_iff_dfct] at hvs
      apply hv
      rw [F_ne_zero hvs, F_ne_zero he]; decide
  have hmem : ℓ₁.1 ∈ C.violated s := Finset.mem_filter.2 ⟨ℓ₁.2, hT ℓ₁ h1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at hle
  have hpos : 0 < (C.violated s).card := Finset.card_pos.2 ⟨_, hmem⟩
  have := C.deg_le (s + T)
  omega

/-! ### components -/

/-- the lines of a component -/
noncomputable def compLines (K : (lineGraph C).ConnectedComponent) : Finset (LV C) :=
  Finset.univ.filter (fun ℓ => (lineGraph C).connectedComponentMk ℓ = K)

/-- the component as a family of lines of `C` -/
noncomputable def compFam (K : (lineGraph C).ConnectedComponent) : Finset (Finset α) :=
  (compLines K).map (Function.Embedding.subtype _)

/-- no point of the component lies on only one line -/
def Closed (K : (lineGraph C).ConnectedComponent) : Prop :=
  ∀ ℓ ∈ compLines K, ∀ p ∈ ℓ.1, C.degP p ≠ 1

/-- the signs of the component sum to 1 -/
def Odd' (K : (lineGraph C).ConnectedComponent) : Prop := ∑ l ∈ compFam K, C.sign l = 1

theorem degP_pos {p : α} {ℓ : LV C} (hp : p ∈ ℓ.1) : 1 ≤ C.degP p :=
  Finset.card_pos.2 ⟨ℓ.1, Finset.mem_filter.2 ⟨ℓ.2, hp⟩⟩

/-- a closed component is a cycle -/
theorem closed_cycle (h2 : ∀ p, C.degP p ≤ 2) {K : (lineGraph C).ConnectedComponent} (hK : Closed K) :
    IsCycle (compFam K) := by
  intro p
  by_cases hex : ∃ ℓ ∈ compLines K, p ∈ ℓ.1
  · obtain ⟨ℓ, hℓK, hp⟩ := hex
    have hd : C.degP p = 2 := by
      have := h2 p; have := degP_pos hp; have := hK ℓ hℓK p hp; omega
    -- the two lines through p
    obtain ⟨a, b, hab, hfil⟩ := Finset.card_eq_two.1 hd
    have ha' : a ∈ C.lines.filter (fun l => p ∈ l) := by rw [hfil]; simp
    have hb' : b ∈ C.lines.filter (fun l => p ∈ l) := by rw [hfil]; simp
    have ha : a ∈ C.lines ∧ p ∈ a := Finset.mem_filter.1 ha'
    have hb : b ∈ C.lines ∧ p ∈ b := Finset.mem_filter.1 hb'
    have hadj : (lineGraph C).Adj ⟨a, ha.1⟩ ⟨b, hb.1⟩ :=
      (lineGraph_adj _).2 ⟨fun h => hab (congrArg Subtype.val h), p, ha.2, hb.2⟩
    have hsame : (lineGraph C).connectedComponentMk ⟨a, ha.1⟩ =
        (lineGraph C).connectedComponentMk ⟨b, hb.1⟩ :=
      SimpleGraph.ConnectedComponent.eq.2 hadj.reachable
    -- ℓ is one of a, b, so both lie in K
    have hℓ : ℓ.1 = a ∨ ℓ.1 = b := by
      have : ℓ.1 ∈ C.lines.filter (fun l => p ∈ l) := Finset.mem_filter.2 ⟨ℓ.2, hp⟩
      rw [hfil] at this; simpa using this
    have hKℓ : (lineGraph C).connectedComponentMk ℓ = K := (Finset.mem_filter.1 hℓK).2
    have haK : (lineGraph C).connectedComponentMk ⟨a, ha.1⟩ = K := by
      rcases hℓ with h | h
      · rw [← hKℓ]; congr 1; exact Subtype.ext h.symm
      · rw [hsame, ← hKℓ]; congr 1; exact Subtype.ext h.symm
    have hbK : (lineGraph C).connectedComponentMk ⟨b, hb.1⟩ = K := hsame ▸ haK
    have : (compFam K).filter (fun l => p ∈ l) = {a, b} := by
      ext l
      simp only [compFam, compLines, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨ℓ', -, rfl⟩, hp'⟩
        have : ℓ'.1 ∈ C.lines.filter (fun l => p ∈ l) := Finset.mem_filter.2 ⟨ℓ'.2, hp'⟩
        rw [hfil] at this; simpa using this
      · rintro (rfl | rfl)
        · exact ⟨⟨⟨l, ha.1⟩, haK, rfl⟩, ha.2⟩
        · exact ⟨⟨⟨l, hb.1⟩, hbK, rfl⟩, hb.2⟩
    rw [this, Finset.card_pair hab]; exact ⟨1, rfl⟩
  · push Not at hex
    have : (compFam K).filter (fun l => p ∈ l) = ∅ := by
      ext l
      simp only [compFam, Finset.mem_filter, Finset.mem_map, Function.Embedding.coe_subtype,
        Finset.notMem_empty, iff_false, not_and]
      rintro ⟨ℓ, hℓ, rfl⟩; exact hex ℓ hℓ
    rw [this, Finset.card_empty]; exact ⟨0, rfl⟩

theorem compFam_sub (K : (lineGraph C).ConnectedComponent) : compFam K ⊆ C.lines := by
  intro l hl
  obtain ⟨ℓ, -, rfl⟩ := Finset.mem_map.1 hl
  exact ℓ.2

/-- the violated lines of `s` inside a component -/
noncomputable def violIn (s : α → F) (K : (lineGraph C).ConnectedComponent) : ℕ :=
  ((compLines K).filter (fun ℓ => C.Violated s ℓ.1)).card

theorem violIn_eq (s : α → F) (K : (lineGraph C).ConnectedComponent) :
    violIn s K = (C.violated s ∩ compFam K).card := by
  unfold violIn
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext l
  simp only [Finset.mem_map, Finset.mem_filter, Function.Embedding.coe_subtype, Finset.mem_inter,
    violated, compFam]
  constructor
  · rintro ⟨ℓ, ⟨hℓ, hv⟩, rfl⟩; exact ⟨⟨ℓ.2, hv⟩, ℓ, hℓ, rfl⟩
  · rintro ⟨⟨hl, hv⟩, ℓ, hℓ, rfl⟩; exact ⟨ℓ, ⟨hℓ, hv⟩, rfl⟩

/-- the violated set is partitioned by components -/
theorem card_violated_comp (s : α → F) :
    (C.violated s).card = ∑ K : (lineGraph C).ConnectedComponent, violIn s K := by
  have h1 : (C.violated s).card = (Finset.univ.filter (fun ℓ : LV C => C.Violated s ℓ.1)).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1; ext l
    simp only [violated, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hl, hv⟩; exact ⟨⟨l, hl⟩, hv, rfl⟩
    · rintro ⟨ℓ, hv, rfl⟩; exact ⟨ℓ.2, hv⟩
  rw [h1, Finset.card_eq_sum_card_fiberwise (f := (lineGraph C).connectedComponentMk)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun K _ => ?_
  unfold violIn compLines
  congr 1; ext ℓ; simp [and_comm]

/-- **local structure of an optimal assignment** -/
theorem violIn_opt (h2 : ∀ p, C.degP p ≤ 2) {s : α → F} (hs : (C.violated s).card = C.deg)
    (K : (lineGraph C).ConnectedComponent) : violIn s K = if Closed K ∧ Odd' K then 1 else 0 := by
  -- at most one violated line per component
  have hle1 : violIn s K ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hcon
    obtain ⟨huK, huV⟩ := Finset.mem_filter.1 hu
    obtain ⟨hvK, hvV⟩ := Finset.mem_filter.1 hv
    have hreach : (lineGraph C).Reachable u v := by
      rw [← SimpleGraph.ConnectedComponent.eq]
      rw [(Finset.mem_filter.1 huK).2, (Finset.mem_filter.1 hvK).2]
    obtain ⟨w⟩ := hreach
    obtain ⟨T, hT⟩ := walk_toggle h2 w
    refine no_improve hs T u ?_ ?_
    · rw [hT u]; simp [huv]
    · intro ℓ hℓ
      rw [hT ℓ] at hℓ
      by_cases h1 : ℓ = u
      · rw [h1]; exact huV
      · by_cases h3 : ℓ = v
        · rw [h3]; exact hvV
        · simp [h1, h3] at hℓ
  by_cases hcl : Closed K
  · -- parity in a closed component
    have hcyc := closed_cycle h2 hcl
    have hpar : (violIn s K : F) = ∑ l ∈ compFam K, C.sign l := by
      rw [violIn_eq]
      have := Finset.card_filter (C.Violated s) (compFam K)
      have hfi : C.violated s ∩ compFam K = (compFam K).filter (C.Violated s) := by
        ext l; simp only [Finset.mem_inter, violated, Finset.mem_filter]
        constructor
        · rintro ⟨⟨-, hv⟩, hl⟩; exact ⟨hl, hv⟩
        · rintro ⟨hl, hv⟩; exact ⟨⟨compFam_sub K hl, hv⟩, hl⟩
      rw [hfi, Finset.card_filter, Nat.cast_sum]
      have hsc := sum_sum_cycle (compFam K) hcyc s
      have : ∀ l ∈ compFam K, (((if C.Violated s l then 1 else 0 : ℕ)) : F) = (∑ p ∈ l, s p) + C.sign l := by
        intro l _
        by_cases hv : C.Violated s l
        · rw [if_pos hv, Nat.cast_one]; exact (F_ne_zero hv).symm
        · rw [if_neg hv, Nat.cast_zero]; unfold Violated at hv; push Not at hv; exact hv.symm
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hsc, zero_add]
    by_cases hodd : Odd' K
    · rw [if_pos ⟨hcl, hodd⟩]
      unfold Odd' at hodd
      rw [hodd] at hpar
      rcases Nat.lt_or_ge (violIn s K) 1 with h | h
      · have : violIn s K = 0 := by omega
        rw [this, Nat.cast_zero] at hpar; exact absurd hpar (by decide)
      · omega
    · rw [if_neg (fun h => hodd h.2)]
      have heven : ∑ l ∈ compFam K, C.sign l = 0 := by
        unfold Odd' at hodd
        generalize ∑ l ∈ compFam K, C.sign l = x at hodd ⊢; revert x; decide
      rw [heven] at hpar
      rcases Nat.lt_or_ge (violIn s K) 1 with h | h
      · omega
      · have : violIn s K = 1 := by omega
        rw [this, Nat.cast_one] at hpar; exact absurd hpar (by decide)
  · -- a pendant point allows repairing any single violation
    rw [if_neg (fun h => hcl h.1)]
    unfold Closed at hcl
    push Not at hcl
    obtain ⟨m, hmK, p, hpm, hp1⟩ := hcl
    by_contra hne
    have hpos : 0 < violIn s K := Nat.pos_of_ne_zero hne
    obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
    obtain ⟨huK, huV⟩ := Finset.mem_filter.1 hu
    have hreach : (lineGraph C).Reachable u m := by
      rw [← SimpleGraph.ConnectedComponent.eq, (Finset.mem_filter.1 huK).2, (Finset.mem_filter.1 hmK).2]
    obtain ⟨w⟩ := hreach
    obtain ⟨T', hT'⟩ := walk_toggle h2 w
    let T : α → F := fun q => T' q + (if q = p then 1 else 0)
    have hT : ∀ ℓ : LV C, eff T ℓ.1 = if ℓ = u then 1 else 0 := by
      intro ℓ
      have : eff T ℓ.1 = eff T' ℓ.1 + eff (fun q => if q = p then 1 else 0) ℓ.1 := by
        unfold eff; rw [← Finset.sum_add_distrib]
      rw [this, hT' ℓ, eff_single]
      have hiff := one_line hp1 hpm ℓ
      by_cases h3 : ℓ = m
      · have : p ∈ ℓ.1 := hiff.2 h3
        rw [if_pos this, if_pos h3]
        split_ifs <;> decide
      · have : p ∉ ℓ.1 := fun h => h3 (hiff.1 h)
        rw [if_neg this, if_neg h3]; simp
    refine no_improve hs T u ?_ ?_
    · rw [hT u]; simp
    · intro ℓ hℓ
      rw [hT ℓ] at hℓ
      by_cases h1 : ℓ = u
      · rw [h1]; exact huV
      · simp [h1] at hℓ

/-- **HARD-12.** If every point lies on at most two lines, the degree is the number of closed odd
components of the line graph. -/
theorem deg_two_points (h2 : ∀ p, C.degP p ≤ 2) :
    C.deg = (Finset.univ.filter (fun K : (lineGraph C).ConnectedComponent => Closed K ∧ Odd' K)).card := by
  obtain ⟨s, hs⟩ := C.exists_opt
  rw [← hs, card_violated_comp, Finset.sum_congr rfl (fun K _ => violIn_opt h2 hs K),
    Finset.sum_boole]
  simp

end PauliCtx.Config
