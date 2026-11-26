/-
Hardness.lean — HARD-1, HARD-2, HARD-8 (02_hardness.md): the value identities of the XOR-system
reductions. Complexity-theoretic consequences stay on paper.

  * `chain_lemma`        : HARD-1. For a chain F_0..F_{t−1} with private links w, the minimum number of
                           violated equations is [Σ violated].
  * `triangle_local`     : the cyclic chain of length 3 (finite check).
  * `split_opt`          : HARD-2 (a). The ordered triangle split preserves OPT.
  * `split_share`, `split_middle` : HARD-2 (b), (c).
  * `one_equation_min_*` : HARD-8, the final two-case minimisations.
-/
import PauliContextuality.Cover

namespace PauliCtx.Hardness

/-- XOR system with `m` equations in `N` variables, each equation a finset of variables. -/
structure XorSys (N m : ℕ) where
  eqs : Fin m → Finset (Fin N)
  rhs : Fin m → F

def XorSys.viol {N m} (S : XorSys N m) (x : Fin N → F) : ℕ :=
  (Finset.univ.filter (fun j => (∑ v ∈ S.eqs j, x v) + S.rhs j ≠ 0)).card

noncomputable def XorSys.opt {N m} (S : XorSys N m) : ℕ :=
  (Finset.univ : Finset (Fin N → F)).inf' Finset.univ_nonempty S.viol

/-! ### HARD-1: the chain lemma -/

/-- the (indicator of) violation of chain equation `i`: `a_i + w_i + w_{i+1} ≠ 0`. -/
def chainViol (t : ℕ) (a w : ℕ → F) : ℕ :=
  ((Finset.range t).filter (fun i => a i + w i + w (i + 1) ≠ 0)).card

theorem telescope (t : ℕ) (a w : ℕ → F) :
    ∑ i ∈ Finset.range t, (a i + w i + w (i + 1)) = (∑ i ∈ Finset.range t, a i) + w 0 + w t := by
  induction t with
  | zero => simp [add_self_F]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h := add_self_F (w t)
    linear_combination h

theorem parity_card (s : Finset ℕ) (f : ℕ → F) :
    ((s.filter (fun i => f i ≠ 0)).card : F) = ∑ i ∈ s, f i := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize f i = x; revert x; decide

/-- HARD-1 (lower bound and parity): with fixed ends `w 0 = w t = 0`, the number of violated chain
equations has the parity of `Σ a`, so it is ≥ 1 when `Σ a ≠ 0`. -/
theorem chain_parity (t : ℕ) (a w : ℕ → F) (h0 : w 0 = 0) (ht : w t = 0) :
    (chainViol t a w : F) = ∑ i ∈ Finset.range t, a i := by
  unfold chainViol
  rw [parity_card, telescope, h0, ht, add_zero, add_zero]

/-- the greedy links `w_{i+1} = a_i + w_i` (prefix sums) -/
def greedy (t : ℕ) (a : ℕ → F) (i : ℕ) : F := if i < t then ∑ j ∈ Finset.range i, a j else 0

/-- HARD-1 (chain lemma). -/
theorem chain_lemma (t : ℕ) (ht : 1 ≤ t) (a : ℕ → F) :
    (∀ w : ℕ → F, w 0 = 0 → w t = 0 →
      (if ∑ i ∈ Finset.range t, a i = 0 then 0 else 1) ≤ chainViol t a w) ∧
    ∃ w : ℕ → F, w 0 = 0 ∧ w t = 0 ∧
      chainViol t a w = if ∑ i ∈ Finset.range t, a i = 0 then 0 else 1 := by
  constructor
  · intro w h0 hwt
    split_ifs with h
    · exact Nat.zero_le _
    · by_contra hlt
      push Not at hlt
      have hz : chainViol t a w = 0 := by omega
      have := chain_parity t a w h0 hwt
      rw [hz, Nat.cast_zero] at this
      exact h this.symm
  · refine ⟨greedy t a, by simp [greedy], by simp [greedy], ?_⟩
    -- only the last equation can be violated
    have hfilt : (Finset.range t).filter (fun i => a i + greedy t a i + greedy t a (i + 1) ≠ 0) =
        if ∑ i ∈ Finset.range t, a i = 0 then ∅ else {t - 1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hi, hv⟩
        by_cases hlast : i + 1 < t
        · exfalso; apply hv
          simp only [greedy, if_pos (by omega : i < t), if_pos hlast, Finset.sum_range_succ]
          have h := add_self_F (∑ j ∈ Finset.range i, a j)
          have h2 := add_self_F (a i)
          linear_combination h + h2
        · have hi' : i = t - 1 := by omega
          have hval : a i + greedy t a i + greedy t a (i + 1) = ∑ j ∈ Finset.range t, a j := by
            simp only [greedy, if_pos hi, if_neg hlast, add_zero]
            have : t = i + 1 := by omega
            rw [this, Finset.sum_range_succ, add_comm]
          rw [hval] at hv
          rw [if_neg hv]; exact Finset.mem_singleton.2 hi'
      · intro h
        split_ifs at h with hs
        · simp at h
        · rw [Finset.mem_singleton] at h
          subst h
          refine ⟨by omega, ?_⟩
          have hval : a (t - 1) + greedy t a (t - 1) + greedy t a (t - 1 + 1) = ∑ j ∈ Finset.range t, a j := by
            have e : t - 1 + 1 = t := by omega
            simp only [greedy, if_pos (by omega : t - 1 < t), e, lt_irrefl, if_false, add_zero]
            conv_rhs => rw [← e, Finset.sum_range_succ]
            ring
          rw [hval]; exact hs
    unfold chainViol
    rw [hfilt]
    split_ifs <;> simp

/-! ### HARD-2: ordered triangle split -/

/-- the cyclic chain of length 3: equations `(w₂,a,w₁)`, `(w₃,b,w₂)`, `(w₁,c,w₃)` with right-hand
sides `0, 0, β`. Its minimum over `w` is `[a+b+c ≠ β]`. -/
def triCost (a b c β w₁ w₂ w₃ : F) : ℕ :=
  (if w₂ + a + w₁ ≠ 0 then 1 else 0) + (if w₃ + b + w₂ ≠ 0 then 1 else 0) +
    (if w₁ + c + w₃ + β ≠ 0 then 1 else 0)

theorem triangle_local (a b c β : F) :
    (∀ w₁ w₂ w₃, (if a + b + c + β ≠ 0 then 1 else 0) ≤ triCost a b c β w₁ w₂ w₃) ∧
    triCost a b c β 0 a (a + b) = if a + b + c + β ≠ 0 then 1 else 0 := by
  revert a b c β; decide

/-- A general XOR system on a finite variable type `ν` and equation type `ε`. -/
structure GSys (ν ε : Type) [Fintype ν] [Fintype ε] where
  eqs : ε → Finset ν
  rhs : ε → F

variable {ν ε : Type} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε]

def GSys.viol (S : GSys ν ε) (x : ν → F) : ℕ :=
  (Finset.univ.filter (fun j => (∑ v ∈ S.eqs j, x v) + S.rhs j ≠ 0)).card

noncomputable def GSys.opt (S : GSys ν ε) : ℕ :=
  (Finset.univ : Finset (ν → F)).inf' Finset.univ_nonempty S.viol

theorem GSys.opt_le (S : GSys ν ε) (x : ν → F) : S.opt ≤ S.viol x :=
  Finset.inf'_le _ (Finset.mem_univ x)

theorem GSys.exists_opt (S : GSys ν ε) : ∃ x, S.viol x = S.opt := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (ν → F)))
    Finset.univ_nonempty S.viol
  exact ⟨x, hx.symm⟩

/-- An E3 system: every equation has three distinct variables. -/
structure E3 (ν ε : Type) where
  var : ε → Fin 3 → ν
  inj : ∀ e, Function.Injective (var e)
  rhs : ε → F

def E3.toSys (S : E3 ν ε) : GSys ν ε where
  eqs e := {S.var e 0, S.var e 1, S.var e 2}
  rhs := S.rhs

/-- HARD-2: the ordered triangle split. New variables `w_{e,i}` (`i = 0,1,2` for w₁,w₂,w₃);
equation `(e,0) = (w₂, a, w₁)`, `(e,1) = (w₃, b, w₂)`, `(e,2) = (w₁, c, w₃)`. -/
def E3.split (S : E3 ν ε) : E3 (ν ⊕ (ε × Fin 3)) (ε × Fin 3) where
  var p := ![Sum.inr (p.1, p.2 + 1), Sum.inl (S.var p.1 p.2), Sum.inr (p.1, p.2)]
  inj p := by
    intro i j h
    have hne : p.2 + 1 ≠ p.2 := by generalize p.2 = k; revert k; decide
    fin_cases i <;> fin_cases j
    all_goals try simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    all_goals first
      | rfl
      | exact absurd h Sum.inl_ne_inr
      | exact absurd h Sum.inr_ne_inl
      | exact absurd (congrArg Prod.snd (Sum.inr_injective h)) hne
      | exact absurd (congrArg Prod.snd (Sum.inr_injective h)).symm hne
  rhs p := if p.2 = 2 then S.rhs p.1 else 0

theorem sum_three (S : E3 ν ε) (e : ε) (x : ν → F) :
    ∑ v ∈ S.toSys.eqs e, x v = x (S.var e 0) + x (S.var e 1) + x (S.var e 2) := by
  have h01 : S.var e 0 ≠ S.var e 1 := fun h => by have := S.inj e h; exact absurd this (by decide)
  have h02 : S.var e 0 ≠ S.var e 2 := fun h => by have := S.inj e h; exact absurd this (by decide)
  have h12 : S.var e 1 ≠ S.var e 2 := fun h => by have := S.inj e h; exact absurd this (by decide)
  simp only [E3.toSys]
  rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]), Finset.sum_singleton,
    add_assoc]

theorem split_viol (S : E3 ν ε) (x : ν ⊕ (ε × Fin 3) → F) :
    S.split.toSys.viol x = ∑ e, triCost (x (Sum.inl (S.var e 0))) (x (Sum.inl (S.var e 1)))
      (x (Sum.inl (S.var e 2))) (S.rhs e) (x (Sum.inr (e, 0))) (x (Sum.inr (e, 1))) (x (Sum.inr (e, 2))) := by
  unfold GSys.viol
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.sum_univ_three]
  simp only [sum_three, triCost]
  simp [E3.split, E3.toSys]

/-- HARD-2 (a): the ordered triangle split preserves OPT. -/
theorem split_opt (S : E3 ν ε) : S.split.toSys.opt = S.toSys.opt := by
  apply le_antisymm
  · -- upper bound: an optimal assignment, links chosen greedily
    obtain ⟨y, hy⟩ := S.toSys.exists_opt
    let x : ν ⊕ (ε × Fin 3) → F := Sum.elim y (fun p => match p.2 with
      | 0 => 0
      | 1 => y (S.var p.1 0)
      | 2 => y (S.var p.1 0) + y (S.var p.1 1))
    refine le_trans (S.split.toSys.opt_le x) (le_of_eq ?_)
    rw [split_viol, ← hy]
    unfold GSys.viol
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := (triangle_local (y (S.var e 0)) (y (S.var e 1)) (y (S.var e 2)) (S.rhs e)).2
    simp only [x, Sum.elim_inl, Sum.elim_inr]
    rw [this, sum_three]
    simp [E3.toSys, add_assoc]
  · -- lower bound: each triangle costs at least its original equation
    obtain ⟨x, hx⟩ := S.split.toSys.exists_opt
    refine le_trans (S.toSys.opt_le (fun v => x (Sum.inl v))) ?_
    rw [← hx, split_viol]
    unfold GSys.viol
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun e _ => ?_
    have := (triangle_local (x (Sum.inl (S.var e 0))) (x (Sum.inl (S.var e 1)))
      (x (Sum.inl (S.var e 2))) (S.rhs e)).1 (x (Sum.inr (e, 0))) (x (Sum.inr (e, 1))) (x (Sum.inr (e, 2)))
    rw [sum_three]
    simpa [E3.toSys, add_assoc] using this

/-- HARD-2 (c): in every ordered triple of the split, the middle variable is original and the outer
two are new. -/
theorem split_middle (S : E3 ν ε) (p : ε × Fin 3) :
    S.split.var p 1 = Sum.inl (S.var p.1 p.2) ∧ (∃ q, S.split.var p 0 = Sum.inr q) ∧
      (∃ q, S.split.var p 2 = Sum.inr q) := by
  simp [E3.split]

theorem mem_split_eqs (S : E3 ν ε) (p : ε × Fin 3) (u : ν ⊕ (ε × Fin 3)) :
    u ∈ S.split.toSys.eqs p ↔
      u = Sum.inl (S.var p.1 p.2) ∨ ∃ k, u = Sum.inr (p.1, k) ∧ (k = p.2 ∨ k = p.2 + 1) := by
  simp only [E3.toSys, E3.split, Finset.mem_insert, Finset.mem_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  constructor
  · rintro (h | h | h)
    · exact Or.inr ⟨_, h, Or.inr rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, h, Or.inl rfl⟩
  · rintro (h | ⟨k, h, hk | hk⟩)
    · exact Or.inr (Or.inl h)
    · subst hk; exact Or.inr (Or.inr h)
    · subst hk; exact Or.inl h

/-- HARD-2 (b): two distinct equations of the split share at most one variable. -/
theorem split_share (S : E3 ν ε) (p q : ε × Fin 3) (hpq : p ≠ q) :
    (S.split.toSys.eqs p ∩ S.split.toSys.eqs q).card ≤ 1 := by
  have key : ∀ i j k k' : Fin 3, i ≠ j → (k = i ∨ k = i + 1) → (k = j ∨ k = j + 1) →
      (k' = i ∨ k' = i + 1) → (k' = j ∨ k' = j + 1) → k = k' := by decide
  rw [Finset.card_le_one]
  intro u hu u' hu'
  rw [Finset.mem_inter, mem_split_eqs, mem_split_eqs] at hu hu'
  obtain ⟨e, i⟩ := p
  obtain ⟨e', j⟩ := q
  simp only at hu hu'
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hu1', hu2'⟩ := hu'
  rcases hu1 with h1 | ⟨k1, h1, hk1⟩
  · rcases hu2 with h2 | ⟨k2, h2, hk2⟩
    · rcases hu1' with h3 | ⟨k3, h3, hk3⟩
      · rw [h1, h3]
      · rcases hu2' with h4 | ⟨k4, h4, hk4⟩
        · exact absurd (h3.symm.trans h4) Sum.inr_ne_inl
        · have he : e = e' := (Prod.mk.inj (Sum.inr_injective (h3.symm.trans h4))).1
          subst he
          have hij : i = j := (S.inj e).eq_iff.1 (Sum.inl_injective (h1.symm.trans h2))
          exact absurd (by rw [hij]) hpq
    · exact absurd (h1.symm.trans h2) Sum.inl_ne_inr
  · rcases hu2 with h2 | ⟨k2, h2, hk2⟩
    · exact absurd (h1.symm.trans h2) Sum.inr_ne_inl
    · have he : e = e' := (Prod.mk.inj (Sum.inr_injective (h1.symm.trans h2))).1
      have hk12 : k1 = k2 := (Prod.mk.inj (Sum.inr_injective (h1.symm.trans h2))).2
      subst he
      have hij : i ≠ j := fun h => hpq (by rw [h])
      rcases hu1' with h3 | ⟨k3, h3, hk3⟩
      · rcases hu2' with h4 | ⟨k4, h4, hk4⟩
        · exact absurd ((S.inj e).eq_iff.1 (Sum.inl_injective (h3.symm.trans h4))) hij
        · exact absurd (h3.symm.trans h4) Sum.inl_ne_inr
      · rcases hu2' with h4 | ⟨k4, h4, hk4⟩
        · exact absurd (h3.symm.trans h4) Sum.inr_ne_inl
        · have hk34 : k3 = k4 := (Prod.mk.inj (Sum.inr_injective (h3.symm.trans h4))).2
          subst hk12
          subst hk34
          rw [h1, h3, key i j k1 k3 hij hk1 hk2 hk3 hk4]

/-! ### HARD-8: the final two-case minimisations -/

/-- `b_E = 0`: `min_τ ([τ ≠ Y] + [τ ≠ 0]) = [Y ≠ 0]`. -/
theorem one_equation_b0 (Y : F) :
    (∀ τ : F, (if Y ≠ 0 then 1 else 0) ≤ (if τ ≠ Y then 1 else 0) + (if τ ≠ 0 then 1 else 0)) ∧
    ∃ τ : F, (if τ ≠ Y then 1 else 0) + (if τ ≠ 0 then 1 else 0) = (if Y ≠ 0 then 1 else 0) := by
  revert Y; decide

/-- `b_E = 1` in Φ_ind: `min_τ ([τ ≠ Y] + [τ ≠ 0] + 2[τ ≠ 1]) = [Y ≠ 1] + 1`. -/
theorem one_equation_ind (Y : F) :
    (∀ τ : F, (if Y ≠ 1 then 1 else 0) + 1 ≤
      (if τ ≠ Y then 1 else 0) + (if τ ≠ 0 then 1 else 0) + 2 * (if τ ≠ 1 then 1 else 0)) ∧
    ∃ τ : F, (if τ ≠ Y then 1 else 0) + (if τ ≠ 0 then 1 else 0) + 2 * (if τ ≠ 1 then 1 else 0) =
      (if Y ≠ 1 then 1 else 0) + 1 := by
  revert Y; decide

/-- `b_E = 1` in Φ_sub: `min_τ ([τ ≠ Y] + [τ ≠ 1]) = [Y ≠ 1]`. -/
theorem one_equation_sub (Y : F) :
    (∀ τ : F, (if Y ≠ 1 then 1 else 0) ≤ (if τ ≠ Y then 1 else 0) + (if τ ≠ 1 then 1 else 0)) ∧
    ∃ τ : F, (if τ ≠ Y then 1 else 0) + (if τ ≠ 1 then 1 else 0) = (if Y ≠ 1 then 1 else 0) := by
  revert Y; decide

end PauliCtx.Hardness
