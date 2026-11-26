/-
ToE3.lean — blueprint HARD-3 (arbitrary XOR system → E3 system with the same OPT).

Construction (all rows non-empty):
  1. every variable v is replaced by three copies (v,0), (v,1), (v,2) in every row; a row with
     k variables becomes a row of length L = 3k ≥ 3 (the map copies ↦ sum is onto, so OPT is kept);
  2. the row a₀ + … + a_{L−1} = b is split into the chain of L − 2 three-variable equations
       (a₀, a₁, w₀), (w₀, a₂, w₁), …, (w_{L−4}, a_{L−2}, a_{L−1}) with right-hand sides 0, …, 0, b
     and fresh variables w (HARD-1).

  * `toE3_opt` : OPT(toE3 S) = OPT(S).
-/
import PauliContextuality.Hardness

namespace PauliCtx.Hardness

open Classical

variable {ν ε : Type} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε]

section
variable (S : GSys ν ε)

/-- the length of the tripled row -/
noncomputable def len (e : ε) : ℕ := (S.eqs e).card * 3

/-- the `i`-th variable of the tripled row `e` -/
noncomputable def pos (e : ε) (i : Fin (len S e)) : ν × Fin 3 :=
  (((S.eqs e).equivFin.symm (finProdFinEquiv.symm i).1).1, (finProdFinEquiv.symm i).2)

theorem pos_inj (e : ε) : Function.Injective (pos S e) := by
  intro i j h
  simp only [pos, Prod.mk.injEq] at h
  apply finProdFinEquiv.symm.injective
  exact Prod.ext ((S.eqs e).equivFin.symm.injective (Subtype.ext h.1)) h.2

theorem sum_pos (e : ε) (x : ν × Fin 3 → F) :
    ∑ i : Fin (len S e), x (pos S e i) = ∑ v ∈ S.eqs e, ∑ r : Fin 3, x (v, r) := by
  rw [← Finset.sum_coe_sort (S.eqs e)]
  rw [show (∑ i : Fin (len S e), x (pos S e i)) =
      ∑ q : Fin (S.eqs e).card × Fin 3, x (((S.eqs e).equivFin.symm q.1).1, q.2) from
    (Fintype.sum_equiv finProdFinEquiv _ _ (fun q => by simp [pos])).symm]
  rw [Fintype.sum_prod_type]
  exact Fintype.sum_equiv (S.eqs e).equivFin.symm _ _ (fun q => rfl)

/-- bound on the fresh variables -/
noncomputable def Mb (ν : Type) [Fintype ν] : ℕ := 3 * Fintype.card ν

theorem len_le (e : ε) : len S e ≤ Mb ν := by
  unfold len Mb; rw [mul_comm]
  exact Nat.mul_le_mul_left 3 (Finset.card_le_univ _)

/-- equations of the E3 system: `(e, j)` with `j < len e − 2` -/
abbrev Eq3 := {p : ε × Fin (Mb ν) // p.2.val + 2 < len S p.1}

variable {S}

/-- the three variables of chain equation `(e, j)` -/
noncomputable def var3 (p : Eq3 S) : Fin 3 → (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) :=
  ![if h : p.1.2.val = 0 then Sum.inl (pos S p.1.1 ⟨0, by have := p.2; omega⟩)
      else Sum.inr (p.1.1, ⟨p.1.2.val - 1, by have := p.1.2.2; omega⟩),
    Sum.inl (pos S p.1.1 ⟨p.1.2.val + 1, by have := p.2; omega⟩),
    if h : p.1.2.val + 3 = len S p.1.1 then Sum.inl (pos S p.1.1 ⟨len S p.1.1 - 1, by have := p.2; omega⟩)
      else Sum.inr (p.1.1, ⟨p.1.2.val, p.1.2.2⟩)]

theorem var3_inj (p : Eq3 S) : Function.Injective (var3 p) := by
  have hp := p.2
  have key01 : var3 p 0 ≠ var3 p 1 := by
    simp only [var3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    split_ifs with h
    · intro h'; have := pos_inj S _ (Sum.inl_injective h'); simp [Fin.ext_iff] at this; all_goals omega
    · exact Sum.inr_ne_inl
  have key12 : var3 p 1 ≠ var3 p 2 := by
    simp only [var3, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    split_ifs with h
    · intro h'; have := pos_inj S _ (Sum.inl_injective h'); simp [Fin.ext_iff] at this; all_goals omega
    · exact Sum.inl_ne_inr
  have key02 : var3 p 0 ≠ var3 p 2 := by
    simp only [var3, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    split_ifs with h1 h2 h2
    · intro h'; have := pos_inj S _ (Sum.inl_injective h'); simp [Fin.ext_iff] at this; all_goals omega
    · exact Sum.inl_ne_inr
    · exact Sum.inr_ne_inl
    · intro h'; have := congrArg Prod.snd (Sum.inr_injective h'); simp [Fin.ext_iff] at this; all_goals omega
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd h key01
    | exact absurd h.symm key01
    | exact absurd h key12
    | exact absurd h.symm key12
    | exact absurd h key02
    | exact absurd h.symm key02

variable (S)

/-- **HARD-3.** the E3 system -/
noncomputable def toE3 : E3 ((ν × Fin 3) ⊕ (ε × Fin (Mb ν))) (Eq3 S) where
  var := var3
  inj := var3_inj
  rhs p := if p.1.2.val + 3 = len S p.1.1 then S.rhs p.1.1 else 0

end

/-! ### the chain of one row -/

section
variable {S : GSys ν ε}

/-- copy part and fresh part of an assignment -/
def cpart (x : (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) → F) : ν × Fin 3 → F := fun q => x (Sum.inl q)

/-- the chain data of row `e`: inputs `A` and links `W` (`W 0 = W t = 0`) -/
noncomputable def chA (S : GSys ν ε) (e : ε) (c : ν × Fin 3 → F) (j : ℕ) : F :=
  (if j = 0 then (if h : 0 < len S e then c (pos S e ⟨0, h⟩) else 0) else 0) +
  (if h : j + 1 < len S e then c (pos S e ⟨j + 1, h⟩) else 0) +
  (if j + 3 = len S e then (if h : 0 < len S e then c (pos S e ⟨len S e - 1, by omega⟩) else 0) + S.rhs e
    else 0)

noncomputable def chW (S : GSys ν ε) (e : ε) (x : (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) → F) (i : ℕ) : F :=
  if h : 0 < i ∧ i + 2 < len S e then x (Sum.inr (e, ⟨i - 1, by have := len_le S e; omega⟩)) else 0

theorem linesum_chain (x : (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) → F) (p : Eq3 S) :
    x ((toE3 S).var p 0) + x ((toE3 S).var p 1) + x ((toE3 S).var p 2) + (toE3 S).rhs p =
      chA S p.1.1 (cpart x) p.1.2.val + chW S p.1.1 x p.1.2.val + chW S p.1.1 x (p.1.2.val + 1) := by
  have hp := p.2
  obtain ⟨⟨e, j⟩, hj⟩ := p
  simp only [toE3, var3, chA, chW, cpart, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  simp only at hj
  by_cases h0 : j.val = 0
  · by_cases h3 : j.val + 3 = len S e
    · simp [h0, show 3 = len S e by omega, show 0 < len S e by omega, show 1 < len S e by omega]
      all_goals ring
    · simp [h0, show ¬ 3 = len S e by omega, show 0 < len S e by omega, show 1 < len S e by omega,
        show 3 < len S e by omega]
      all_goals ring
  · by_cases h3 : j.val + 3 = len S e
    · simp [h0, h3, show 0 < len S e by omega, show j.val + 1 < len S e by omega,
        show 0 < j.val by omega, show j.val + 2 < len S e by omega,
        show ¬ (j.val + 1 + 2 < len S e) by omega]
      all_goals ring
    · simp [h0, h3, show 0 < len S e by omega, show j.val + 1 < len S e by omega,
        show 0 < j.val by omega, show j.val + 2 < len S e by omega,
        show j.val + 1 + 2 < len S e by omega]
      all_goals ring

/-- the copies of row `e` as a function on ℕ -/
noncomputable def gRow (S : GSys ν ε) (e : ε) (c : ν × Fin 3 → F) (i : ℕ) : F :=
  if h : i < len S e then c (pos S e ⟨i, h⟩) else 0

theorem chA_eq (e : ε) (c : ν × Fin 3 → F) (j : ℕ) (hL : 3 ≤ len S e) :
    chA S e c j = (if j = 0 then gRow S e c 0 else 0) + gRow S e c (j + 1) +
      (if j + 3 = len S e then gRow S e c (len S e - 1) + S.rhs e else 0) := by
  unfold chA gRow
  simp only [dif_pos (show 0 < len S e by omega), dif_pos (show len S e - 1 < len S e by omega)]

/-- the sum of the chain inputs is the row parity of the copies plus the right-hand side -/
theorem sum_chA (e : ε) (c : ν × Fin 3 → F) (hL : 3 ≤ len S e) :
    ∑ j ∈ Finset.range (len S e - 2), chA S e c j = (∑ i : Fin (len S e), c (pos S e i)) + S.rhs e := by
  have hfin : (∑ i : Fin (len S e), c (pos S e i)) = ∑ i ∈ Finset.range (len S e), gRow S e c i := by
    rw [Finset.sum_range (fun i => gRow S e c i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold gRow; rw [dif_pos i.2]
  rw [hfin, Finset.sum_congr rfl (fun j _ => chA_eq e c j hL)]
  generalize gRow S e c = g
  obtain ⟨n, hn⟩ : ∃ n, len S e = n + 3 := ⟨len S e - 3, by omega⟩
  rw [hn, show n + 3 - 2 = n + 1 by omega, show n + 3 - 1 = n + 2 by omega]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (n + 1)) 0,
    if_pos (Finset.mem_range.2 (by omega))]
  have h3 : ∑ j ∈ Finset.range (n + 1), (if j + 3 = n + 3 then g (n + 2) + S.rhs e else 0) =
      g (n + 2) + S.rhs e := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro j hj hjn; rw [if_neg]; intro h; exact hjn (by omega)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  rw [h3, Finset.sum_range_succ (fun i => g i) (n + 2), Finset.sum_range_succ' (fun i => g i) (n + 1)]
  ring

theorem chW_zero (e : ε) (x : (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) → F) : chW S e x 0 = 0 := by
  unfold chW; rw [dif_neg (fun h => absurd h.1 (lt_irrefl 0))]

theorem chW_top (e : ε) (x : (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) → F) :
    chW S e x (len S e - 2) = 0 := by
  unfold chW; rw [dif_neg (fun h => by omega)]

theorem chainViol_congr (t : ℕ) (a w w' : ℕ → F) (h : ∀ i ≤ t, w i = w' i) :
    chainViol t a w = chainViol t a w' := by
  unfold chainViol
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [h i (by omega), h (i + 1) (by omega)]

end

/-! ### OPT is preserved -/

variable (S : GSys ν ε)

/-- the number of violated E3 equations is the sum over rows of the chain violations -/
theorem viol_toE3 (x : (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) → F) :
    (toE3 S).toSys.viol x = ∑ e, chainViol (len S e - 2) (chA S e (cpart x)) (chW S e x) := by
  unfold GSys.viol
  have hrow : ∀ p : Eq3 S, (∑ v ∈ (toE3 S).toSys.eqs p, x v) + (toE3 S).toSys.rhs p =
      chA S p.1.1 (cpart x) p.1.2.val + chW S p.1.1 x p.1.2.val + chW S p.1.1 x (p.1.2.val + 1) := by
    intro p
    rw [sum_three]
    exact linesum_chain x p
  simp_rw [hrow]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Eq3 S => p.1.1) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold chainViol
  refine Finset.card_bij' (fun p _ => p.1.2.val)
    (fun j hj => ⟨(e, ⟨j, by
      have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1; have := len_le S e; omega⟩), by
      have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1; simp only; omega⟩) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hpe⟩ := Finset.mem_filter.1 hp
    obtain ⟨-, hv⟩ := Finset.mem_filter.1 hp1
    have := p.2
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ?_⟩
    · rw [← hpe]; omega
    · rw [← hpe]; exact hv
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hj2⟩, rfl⟩
  · intro p hp
    obtain ⟨-, hpe⟩ := Finset.mem_filter.1 hp
    apply Subtype.ext; exact Prod.ext hpe.symm (Fin.ext rfl)
  · intro j hj; rfl

theorem viol_rows (z : ν → F) :
    S.viol z = ∑ e, (if (∑ v ∈ S.eqs e, z v) + S.rhs e = 0 then 0 else 1) := by
  unfold GSys.viol
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp_all

theorem len_ge (hne : ∀ e, (S.eqs e).Nonempty) (e : ε) : 3 ≤ len S e := by
  unfold len; have := Finset.card_pos.2 (hne e); omega

/-- **HARD-3.** The E3 system `toE3 S` has the same OPT as `S` (all rows non-empty). -/
theorem toE3_opt (hne : ∀ e, (S.eqs e).Nonempty) : (toE3 S).toSys.opt = S.opt := by
  apply le_antisymm
  · -- upper bound
    obtain ⟨x₀, hx₀⟩ := S.exists_opt
    let c : ν × Fin 3 → F := fun q => if q.2 = 0 then x₀ q.1 else 0
    have hw : ∀ e, ∃ w : ℕ → F, w 0 = 0 ∧ w (len S e - 2) = 0 ∧
        chainViol (len S e - 2) (chA S e c) w =
          if ∑ i ∈ Finset.range (len S e - 2), chA S e c i = 0 then 0 else 1 :=
      fun e => (chain_lemma (len S e - 2) (by have := len_ge S hne e; omega) (chA S e c)).2
    choose w hw0 hwt hwv using hw
    let x : (ν × Fin 3) ⊕ (ε × Fin (Mb ν)) → F := Sum.elim c (fun p => w p.1 (p.2.val + 1))
    have hcx : cpart x = c := rfl
    have hW : ∀ e, ∀ i ≤ len S e - 2, chW S e x i = w e i := by
      intro e i hi
      unfold chW
      split_ifs with h
      · simp only [x, Sum.elim_inr]; congr 1; omega
      · by_cases h0 : i = 0
        · rw [h0, hw0]
        · have : i = len S e - 2 := by omega
          rw [this, hwt]
    have := (toE3 S).toSys.opt_le x
    rw [viol_toE3] at this
    refine le_trans this (le_of_eq ?_)
    rw [← hx₀, viol_rows]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hcx, chainViol_congr _ _ _ _ (hW e), hwv e, sum_chA e c (len_ge S hne e), sum_pos]
    have : ∀ v, ∑ r : Fin 3, c (v, r) = x₀ v := by
      intro v; simp [c, Fin.sum_univ_three]
    simp only [this]
  · -- lower bound
    obtain ⟨x, hx⟩ := (toE3 S).toSys.exists_opt
    rw [← hx, viol_toE3]
    let z : ν → F := fun v => ∑ r : Fin 3, cpart x (v, r)
    refine le_trans (S.opt_le z) ?_
    rw [viol_rows]
    refine Finset.sum_le_sum fun e _ => ?_
    have h1 := (chain_lemma (len S e - 2) (by have := len_ge S hne e; omega) (chA S e (cpart x))).1
      (chW S e x) (chW_zero e x) (chW_top e x)
    rw [sum_chA e _ (len_ge S hne e), sum_pos] at h1
    exact h1

end PauliCtx.Hardness
