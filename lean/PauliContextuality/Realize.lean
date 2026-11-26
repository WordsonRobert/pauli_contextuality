/-
Realize.lean — blueprint HARD-5 (well-definedness) and HARD-6 (closure lemma) for the Pauli
realisation of Φ_ind.

Qubits: a block of 3 qubits per variable and, per equation E, two registers of 2 qubits.
Labels (`lab`):
  * copies c_{v,r} = Z^{λ_r} on block v;
  * the private points of E are the model labels of GadgetModel.lean, transported by the embedding
    Ψ_E of the 13 model qubits (blocks of v₀, v₁, v₂ and the two registers of E).
The used points `U` are the copies, the aux points and the path points of the negative equations.

  * `lab_injOn`, `lab_ne_zero`   (HARD-5): the labels of `U` are distinct and non-zero.
  * `line_sum`, `line_comm`, `line_sgn` (HARD-5): every line of Φ_ind is a commuting zero-sum triple
      with the sign of Φ.
  * `closure`                    (HARD-6): every zero-sum triple of distinct labels of `U` is a line
      of Φ_ind.
The hypotheses on the E3 system are those produced by the triangle split (HARD-2 (b), (c)):
two equations share at most one variable, and in every equation (v₀, v₁, v₂) the middle variable is
original and the two ends are not.
-/
import PauliContextuality.GadgetModel

namespace PauliCtx.Hardness

open Model

variable {ν ε : Type} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε]

/-- qubits: blocks (v, j) and registers (E, t, j) -/
abbrev Qb (ν ε : Type) := (ν × Fin 3) ⊕ (ε × Fin 2 × Fin 2)
/-- labels (x | z) on these qubits -/
abbrev LQ (ν ε : Type) := (Qb ν ε → F) × (Qb ν ε → F)

/-- the shape of a split E3 system (HARD-2 (b), (c)) -/
structure Shape (S : E3 ν ε) (orig : ν → Prop) : Prop where
  share : ∀ E E' (i j i' j' : Fin 3), i ≠ j → S.var E i = S.var E' i' → S.var E j = S.var E' j' → E = E'
  mid : ∀ E, orig (S.var E 1)
  ends : ∀ E, ¬ orig (S.var E 0) ∧ ¬ orig (S.var E 2)

variable (S : E3 ν ε)

/-! ### the embedding of the model of one equation -/

/-- model qubits ↪ qubits, for equation E -/
def emb (E : ε) : Qm → Qb ν ε
  | .inl (i, j) => .inl (S.var E i, j)
  | .inr (t, j) => .inr (E, t, j)

theorem emb_inj (E : ε) : Function.Injective (emb S E) := by
  intro a b h
  rcases a with ⟨i, j⟩ | ⟨t, j⟩ <;> rcases b with ⟨i', j'⟩ | ⟨t', j'⟩ <;> simp only [emb] at h
  · simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    rw [S.inj E h.1, h.2]
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    rw [h.2.1, h.2.2]

/-- Ψ_E: transport of a model label (zero off the image of the model qubits) -/
noncomputable def Psi (E : ε) (m : LM) : LQ ν ε :=
  (Function.extend (emb S E) m.1 0, Function.extend (emb S E) m.2 0)

theorem Psi_fst_emb (E : ε) (m : LM) (q : Qm) : (Psi S E m).1 (emb S E q) = m.1 q :=
  (emb_inj S E).extend_apply _ _ _
theorem Psi_snd_emb (E : ε) (m : LM) (q : Qm) : (Psi S E m).2 (emb S E q) = m.2 q :=
  (emb_inj S E).extend_apply _ _ _

theorem Psi_off (E : ε) (m : LM) (q : Qb ν ε) (hq : ¬ ∃ a, emb S E a = q) :
    (Psi S E m).1 q = 0 ∧ (Psi S E m).2 q = 0 := by
  unfold Psi
  simp only [Function.extend_apply' _ _ _ hq, Pi.zero_apply, and_self]

theorem Psi_add (E : ε) (m m' : LM) : Psi S E (m + m') = Psi S E m + Psi S E m' := by
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · by_cases hq : ∃ a, emb S E a = q
    · obtain ⟨a, rfl⟩ := hq
      simp only [Prod.fst_add, Pi.add_apply, Psi_fst_emb]
    · simp only [Prod.fst_add, Pi.add_apply, (Psi_off S E _ q hq).1, add_zero]
  · by_cases hq : ∃ a, emb S E a = q
    · obtain ⟨a, rfl⟩ := hq
      simp only [Prod.snd_add, Pi.add_apply, Psi_snd_emb]
    · simp only [Prod.snd_add, Pi.add_apply, (Psi_off S E _ q hq).2, add_zero]

theorem Psi_zero (E : ε) : Psi S E 0 = 0 := by
  have h := Psi_add S E 0 0
  rw [add_zero] at h
  have : Psi S E 0 + Psi S E 0 = 0 := by
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_) <;> exact add_self_F _
  rw [← h] at this; exact this

theorem Psi_inj (E : ε) {m m' : LM} (h : Psi S E m = Psi S E m') : m = m' := by
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · have := congrArg (fun L => L.1 (emb S E q)) h
    simpa only [Psi_fst_emb] using this
  · have := congrArg (fun L => L.2 (emb S E q)) h
    simpa only [Psi_snd_emb] using this

/-- sums over the qubits of functions of transported labels reduce to the model -/
theorem sum_Psi (E : ε) (m m' : LM) (f : F → F → F → F → F) (hf : f 0 0 0 0 = 0) :
    ∑ q : Qb ν ε, f ((Psi S E m).1 q) ((Psi S E m).2 q) ((Psi S E m').1 q) ((Psi S E m').2 q) =
      ∑ q : Qm, f (m.1 q) (m.2 q) (m'.1 q) (m'.2 q) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (emb S E)))]
  · rw [Finset.sum_image (fun a _ b _ h => emb_inj S E h)]
    simp only [Psi_fst_emb, Psi_snd_emb]
  · intro q _ hq
    have hq' : ¬ ∃ a, emb S E a = q := by
      rintro ⟨a, rfl⟩; exact hq (Finset.mem_image_of_mem _ (Finset.mem_univ a))
    rw [(Psi_off S E m q hq').1, (Psi_off S E m q hq').2, (Psi_off S E m' q hq').1,
      (Psi_off S E m' q hq').2, hf]

/-! ### Pauli data on labels -/

def omegaQ (a b : LQ ν ε) : F := ∑ q, (a.1 q * b.2 q + a.2 q * b.1 q)
def ycountQ (a : LQ ν ε) : ℕ := (Finset.univ.filter (fun q => a.1 q = 1 ∧ a.2 q = 1)).card
def zxQ (a b : LQ ν ε) : F := ∑ q, a.2 q * b.1 q
def phQ (a b : LQ ν ε) : ZMod 4 := (ycountQ a : ZMod 4) + ycountQ b + dbl (zxQ a b) - ycountQ (a + b)
def sgnQ (a b : LQ ν ε) : F := if phQ a b = 0 then 0 else 1

theorem omega_Psi (E : ε) (m m' : LM) : omegaQ (Psi S E m) (Psi S E m') = omegaM m m' := by
  unfold omegaQ omegaM
  exact sum_Psi S E m m' (fun x z x' z' => x * z' + z * x') (by simp)

theorem zx_Psi (E : ε) (m m' : LM) : zxQ (Psi S E m) (Psi S E m') = zxM m m' := by
  unfold zxQ zxM
  exact sum_Psi S E m m' (fun _ z x' _ => z * x') (by simp)

theorem ycount_Psi (E : ε) (m : LM) : ycountQ (Psi S E m) = ycountM m := by
  unfold ycountQ ycountM
  rw [Finset.card_filter, Finset.card_filter]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (emb S E)))]
  · rw [Finset.sum_image (fun a _ b _ h => emb_inj S E h)]
    simp only [Psi_fst_emb, Psi_snd_emb]
  · intro q _ hq
    have hq' : ¬ ∃ a, emb S E a = q := by
      rintro ⟨a, rfl⟩; exact hq (Finset.mem_image_of_mem _ (Finset.mem_univ a))
    rw [(Psi_off S E m q hq').1, (Psi_off S E m q hq').2]; decide

theorem ph_Psi (E : ε) (m m' : LM) : phQ (Psi S E m) (Psi S E m') = phM m m' := by
  unfold phQ phM
  rw [ycount_Psi, ycount_Psi, zx_Psi, ← Psi_add, ycount_Psi]

theorem sgn_Psi (E : ε) (m m' : LM) : sgnQ (Psi S E m) (Psi S E m') = sgnM m m' := by
  unfold sgnQ sgnM; rw [ph_Psi]

/-! ### the labels -/

/-- the label of a copy: Z^{λ_r} on block v -/
def cLab (v : ν) (r : Fin 4) : LQ ν ε :=
  (0, fun q => match q with
    | .inl (v', j) => if v' = v then lam r j else 0
    | .inr _ => 0)

/-- the labels of the points of Φ -/
noncomputable def lab : Pt ν ε → LQ ν ε
  | .inl (v, r) => cLab v r
  | .inr (E, k) => Psi S E (mlab (.inr k))

/-- the local points of equation E -/
def locPt (E : ε) : Lx → Pt ν ε
  | .inl (i, r) => .inl (S.var E i, r)
  | .inr k => .inr (E, k)

theorem locPt_inj (E : ε) : Function.Injective (locPt S E) := by
  intro a b h
  rcases a with ⟨i, r⟩ | k <;> rcases b with ⟨i', r'⟩ | k' <;> simp only [locPt] at h
  · simp only [Sum.inl.injEq, Prod.mk.injEq] at h; rw [S.inj E h.1, h.2]
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; rw [h.2]

theorem cLab_Psi (E : ε) (i : Fin 3) (r : Fin 4) : cLab (S.var E i) r = Psi S E (mlab (.inl (i, r))) := by
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · by_cases hq : ∃ a, emb S E a = q
    · obtain ⟨a, rfl⟩ := hq
      rw [Psi_fst_emb]
      have := A_x (.inl (i, r)) trivial
      rw [this]; rfl
    · rw [(Psi_off S E _ q hq).1]; rfl
  · by_cases hq : ∃ a, emb S E a = q
    · obtain ⟨a, rfl⟩ := hq
      rw [Psi_snd_emb]
      rcases a with ⟨i', j⟩ | ⟨t, j⟩
      · have hb := congrFun (bc_copy i r i') j
        simp only [bcM] at hb
        rw [hb]
        show (if S.var E i' = S.var E i then lam r j else 0) = _
        by_cases h : i' = i
        · subst h; simp
        · rw [if_neg (fun h' => h (S.inj E h')), if_neg h]; rfl
      · exact ((reg_A (.inl (i, r)) trivial t j).2).symm
    · rw [(Psi_off S E _ q hq).2]
      rcases q with ⟨v, j⟩ | ⟨E', t, j⟩
      · simp only [cLab]
        rw [if_neg]
        rintro rfl; exact hq ⟨.inl (i, j), rfl⟩
      · rfl

theorem lab_loc (E : ε) (x : Lx) : lab S (locPt S E x) = Psi S E (mlab x) := by
  rcases x with ⟨i, r⟩ | k
  · exact cLab_Psi S E i r
  · rfl

theorem lineOf_loc (E : ε) (K : Fin 20) : lineOf S E K = (lline K).image (locPt S E) := by
  unfold lineOf lline
  rw [Finset.image_union, Finset.map_eq_image, Finset.map_eq_image, Finset.image_image,
    Finset.image_image]
  rfl

/-! ### the used points -/

/-- type-A points: copies and aux points -/
def IsA : Pt ν ε → Prop
  | .inl _ => True
  | .inr (_, k) => k.val < 9

/-- the used points of Φ_ind -/
def InU : Pt ν ε → Prop
  | .inl _ => True
  | .inr (E, k) => k.val < 9 ∨ S.rhs E = 1

/-! ### registers and blocks -/

/-- vanishing on the register (E, t) -/
def regZ (E : ε) (t : Fin 2) (L : LQ ν ε) : Prop := ∀ j, L.1 (.inr (E, t, j)) = 0 ∧ L.2 (.inr (E, t, j)) = 0

theorem regZ_add {E : ε} {t : Fin 2} {L L' : LQ ν ε} (h : regZ E t L) (h' : regZ E t L') :
    regZ E t (L + L') := fun j => ⟨by simp [(h j).1, (h' j).1], by simp [(h j).2, (h' j).2]⟩

theorem regZ_Psi_iff (E : ε) (t : Fin 2) (m : LM) : regZ E t (Psi S E m) ↔ regZero t m := by
  constructor
  · intro h j
    have := h j
    rw [show (Sum.inr (E, t, j) : Qb ν ε) = emb S E (.inr (t, j)) from rfl, Psi_fst_emb, Psi_snd_emb] at this
    exact this
  · intro h j
    rw [show (Sum.inr (E, t, j) : Qb ν ε) = emb S E (.inr (t, j)) from rfl, Psi_fst_emb, Psi_snd_emb]
    exact h j

theorem regZ_Psi_other {E E' : ε} (hE : E' ≠ E) (t : Fin 2) (m : LM) : regZ E' t (Psi S E m) := by
  intro j
  have hq : ¬ ∃ a, emb S E a = (Sum.inr (E', t, j) : Qb ν ε) := by
    rintro ⟨a, ha⟩
    rcases a with ⟨i, j'⟩ | ⟨t', j'⟩
    · exact Sum.inl_ne_inr ha
    · simp only [emb, Sum.inr.injEq, Prod.mk.injEq] at ha; exact hE ha.1.symm
  exact Psi_off S E m _ hq

theorem regZ_cLab (E : ε) (t : Fin 2) (v : ν) (r : Fin 4) : regZ E t (cLab v r : LQ ν ε) :=
  fun _ => ⟨rfl, rfl⟩

/-- the block content of block v -/
def bcQ (L : LQ ν ε) (v : ν) : Fin 3 → F := fun j => L.2 (.inl (v, j))

/-- block support -/
def suppQ (L : LQ ν ε) : Finset ν := Finset.univ.filter (fun v => bcQ L v ≠ 0)

theorem bcQ_add (L L' : LQ ν ε) (v : ν) : bcQ (L + L') v = bcQ L v + bcQ L' v := rfl

theorem bcQ_Psi_var (E : ε) (m : LM) (i : Fin 3) : bcQ (Psi S E m) (S.var E i) = bcM m i := by
  funext j
  show (Psi S E m).2 (emb S E (.inl (i, j))) = _
  rw [Psi_snd_emb]; rfl

theorem bcQ_Psi_off (E : ε) (m : LM) (v : ν) (hv : ∀ i, S.var E i ≠ v) : bcQ (Psi S E m) v = 0 := by
  funext j
  have hq : ¬ ∃ a, emb S E a = (Sum.inl (v, j) : Qb ν ε) := by
    rintro ⟨a, ha⟩
    rcases a with ⟨i, j'⟩ | ⟨t, j'⟩
    · simp only [emb, Sum.inl.injEq, Prod.mk.injEq] at ha; exact hv i ha.1
    · exact Sum.inr_ne_inl ha
  exact (Psi_off S E m _ hq).2

theorem suppQ_Psi (E : ε) (m : LM) : suppQ (Psi S E m) = (suppM m).image (S.var E) := by
  ext v
  simp only [suppQ, suppM, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    by_cases hv : ∃ i, S.var E i = v
    · obtain ⟨i, rfl⟩ := hv
      exact ⟨i, by rwa [bcQ_Psi_var] at h, rfl⟩
    · push Not at hv; exact absurd (bcQ_Psi_off S E m v hv) h
  · rintro ⟨i, hi, rfl⟩; rwa [bcQ_Psi_var]

theorem suppQ_cLab (v : ν) (r : Fin 4) : suppQ (cLab v r : LQ ν ε) = {v} := by
  ext w
  simp only [suppQ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; by_contra hw; apply h; funext j
    show (if w = v then lam r j else 0) = 0
    rw [if_neg hw]
  · rintro rfl h
    apply lam_ne r; funext j
    have := congrFun h j
    change (if w = w then lam r j else 0) = 0 at this
    rw [if_pos rfl] at this; exact this

/-- the variables of an equation -/
def varsE (E : ε) : Finset ν := Finset.univ.image (S.var E)

theorem suppQ_aux (E : ε) (k : Fin 21) (hk : k.val < 9) :
    suppQ (lab S (.inr (E, k))) ⊆ varsE S E ∧ 2 ≤ (suppQ (lab S (.inr (E, k)))).card := by
  show suppQ (Psi S E (mlab (.inr k))) ⊆ varsE S E ∧ 2 ≤ (suppQ (Psi S E (mlab (.inr k)))).card
  rw [suppQ_Psi, supp_aux k hk]
  refine ⟨Finset.image_subset_image (Finset.subset_univ _), ?_⟩
  rw [Finset.card_image_of_injective _ (S.inj E)]
  split_ifs <;> decide

/-! ### HARD-5: lines -/

theorem Psi_sum (E : ε) (T : Finset Lx) : ∑ x ∈ T, Psi S E (mlab x) = Psi S E (∑ x ∈ T, mlab x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Psi_zero]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Psi_add]

/-- (HARD-5) every line of Φ is a zero-sum triple of labels -/
theorem line_sum (E : ε) (K : Fin 20) : ∑ p ∈ lineOf S E K, lab S p = 0 := by
  rw [lineOf_loc, Finset.sum_image (fun x _ y _ h => locPt_inj S E h)]
  simp only [lab_loc]
  rw [Psi_sum, lline_sum, Psi_zero]

/-- (HARD-5) the labels of a line pairwise commute -/
theorem line_comm (E : ε) (K : Fin 20) :
    ∀ p ∈ lineOf S E K, ∀ q ∈ lineOf S E K, omegaQ (lab S p) (lab S q) = 0 := by
  rw [lineOf_loc]
  intro p hp q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
  rw [lab_loc, lab_loc, omega_Psi]; exact lline_comm K x hx y hy

/-- (HARD-5) the Pauli sign of a line is the sign of Φ -/
theorem line_sgn (E : ε) (K : Fin 20) :
    ∀ p ∈ lineOf S E K, ∀ q ∈ lineOf S E K, p ≠ q → sgnQ (lab S p) (lab S q) = sgnT K := by
  rw [lineOf_loc]
  intro p hp q hq hpq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
  rw [lab_loc, lab_loc, sgn_Psi]
  exact lline_sign K x hx y hy (fun h => hpq (by rw [h]))

/-! ### registers and supports of the global labels -/

def tOf (k : Fin 21) (hk : ¬ k.val < 9) : Fin 2 := ⟨(k.val - 9) / 6, by omega⟩

theorem regOf_path (k : Fin 21) (hk : ¬ k.val < 9) : regOf (.inr k) = some (tOf k hk) := by
  simp [regOf, hk, tOf]

theorem regZ_A {p : Pt ν ε} (hp : IsA p) (E : ε) (t : Fin 2) : regZ E t (lab S p) := by
  rcases p with ⟨v, r⟩ | ⟨E', k⟩
  · exact regZ_cLab E t v r
  · by_cases hE : E = E'
    · subst hE; exact (regZ_Psi_iff S E t _).2 (reg_A (.inr k) hp t)
    · exact regZ_Psi_other S hE t _

theorem not_regZ_path {E : ε} {k : Fin 21} (hk : ¬ k.val < 9) :
    ¬ regZ E (tOf k hk) (lab S (.inr (E, k))) := by
  show ¬ regZ E _ (Psi S E (mlab (.inr k)))
  rw [regZ_Psi_iff]; exact reg_path (.inr k) _ (regOf_path k hk)

/-- every point other than a path point of (E,t) vanishes on the register (E,t) -/
theorem regZ_or_path (E : ε) (t : Fin 2) (p : Pt ν ε) :
    regZ E t (lab S p) ∨ ∃ k : Fin 21, ∃ hk : ¬ k.val < 9, tOf k hk = t ∧ p = .inr (E, k) := by
  rcases p with ⟨v, r⟩ | ⟨E', k⟩
  · exact Or.inl (regZ_cLab E t v r)
  · by_cases hE : E = E'
    · subst hE
      by_cases hk : k.val < 9
      · exact Or.inl ((regZ_Psi_iff S E t _).2 (reg_A (.inr k) hk t))
      · by_cases ht : tOf k hk = t
        · exact Or.inr ⟨k, hk, ht, rfl⟩
        · exact Or.inl ((regZ_Psi_iff S E t _).2 (reg_other (.inr k) _ t (regOf_path k hk) (Ne.symm ht)))
    · exact Or.inl (regZ_Psi_other S hE t _)

theorem regZ_zero (E : ε) (t : Fin 2) : regZ E t (0 : LQ ν ε) := fun _ => ⟨rfl, rfl⟩

theorem regZ_of_sum {E : ε} {t : Fin 2} {L L' : LQ ν ε} (h : regZ E t L') (h' : regZ E t (L + L')) :
    regZ E t L := by
  intro j
  have a := h j; have b := h' j
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a.1, a.2, add_zero] at b
  exact b

theorem suppQ_zero : suppQ (0 : LQ ν ε) = ∅ := by
  ext v; simp [suppQ, bcQ]; rfl

theorem supp_lab_copy (v : ν) (r : Fin 4) : suppQ (lab S (.inl (v, r))) = {v} := suppQ_cLab v r

theorem supp_lab_aux (E : ε) (k : Fin 21) (hk : k.val < 9) :
    suppQ (lab S (.inr (E, k))) = if k.val = 0 then {S.var E 0, S.var E 1}
      else if k.val = 8 then {S.var E 1, S.var E 2} else varsE S E := by
  show suppQ (Psi S E (mlab (.inr k))) = _
  rw [suppQ_Psi, supp_aux k hk]
  split_ifs <;> simp [varsE, Finset.image_insert]

theorem bc_lab_copy (v : ν) (r : Fin 4) : bcQ (lab S (.inl (v, r))) v = lam r := by
  funext j; show (if v = v then lam r j else 0) = _; simp

/-- the cover property of a zero-sum triple: every block lies in at least two supports -/
theorem cover {L₁ L₂ L₃ : LQ ν ε} (h : L₁ + L₂ + L₃ = 0) {v : ν} (hv : v ∈ suppQ L₁) :
    v ∈ suppQ L₂ ∨ v ∈ suppQ L₃ := by
  by_contra hc
  push Not at hc
  simp only [suppQ, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hc hv
  apply hv
  have := congrArg (fun L => bcQ L v) h
  simp only [bcQ_add] at this
  rw [hc.1, hc.2, add_zero, add_zero] at this
  exact this

theorem inter_le_one {orig : ν → Prop} (hS : Shape S orig) {E E' : ε} (hE : E ≠ E') :
    (varsE S E ∩ varsE S E').card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [varsE, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
  obtain ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩ := ha
  obtain ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩ := hb
  by_contra hab
  have hij : i ≠ j := by rintro rfl; exact hab (hi.symm.trans hj)
  exact hE (hS.share E E' i j i' j' hij (hi.trans hi'.symm) (hj.trans hj'.symm))

theorem supp_aux_sub (E : ε) (k : Fin 21) (hk : k.val < 9) :
    suppQ (lab S (.inr (E, k))) ⊆ varsE S E := (suppQ_aux S E k hk).1

theorem supp_aux_two (E : ε) (k : Fin 21) (hk : k.val < 9) :
    2 ≤ (suppQ (lab S (.inr (E, k)))).card := (suppQ_aux S E k hk).2

/-- a size-2 support is {original, non-original} -/
theorem supp_two {orig : ν → Prop} (hS : Shape S orig) (E : ε) (k : Fin 21) (hk : k.val < 9)
    (h2 : (suppQ (lab S (.inr (E, k)))).card ≤ 2) :
    ∃ o n, suppQ (lab S (.inr (E, k))) = {o, n} ∧ orig o ∧ ¬ orig n := by
  rw [supp_lab_aux S E k hk] at h2 ⊢
  split_ifs at h2 ⊢ with h0 h8
  · exact ⟨S.var E 1, S.var E 0, Finset.pair_comm _ _, hS.mid E, (hS.ends E).1⟩
  · exact ⟨S.var E 1, S.var E 2, rfl, hS.mid E, (hS.ends E).2⟩
  · exfalso
    have : (varsE S E).card = 3 := by
      unfold varsE; rw [Finset.card_image_of_injective _ (S.inj E)]; rfl
    omega

/-- the parity argument on a triangle of size-2 supports -/
theorem triangle {orig : ν → Prop} {A B C : Finset ν}
    (hA : ∃ o n, A = {o, n} ∧ orig o ∧ ¬ orig n) (hB : ∃ o n, B = {o, n} ∧ orig o ∧ ¬ orig n)
    (hC : ∃ o n, C = {o, n} ∧ orig o ∧ ¬ orig n)
    (cA : ∀ v ∈ A, v ∈ B ∨ v ∈ C) (cB : ∀ v ∈ B, v ∈ A ∨ v ∈ C) (hAB : (A ∩ B).card ≤ 1) : False := by
  obtain ⟨oA, nA, rfl, hoA, hnA⟩ := hA
  obtain ⟨oB, nB, rfl, hoB, hnB⟩ := hB
  obtain ⟨oC, nC, rfl, hoC, hnC⟩ := hC
  have memo : ∀ {o n x : ν}, orig x → x ∈ ({o, n} : Finset ν) → ¬ orig n → x = o := by
    intro o n x hx hm hn
    rcases Finset.mem_insert.1 hm with h | h
    · exact h
    · rw [Finset.mem_singleton] at h; exact absurd (h ▸ hx) hn
  have memn : ∀ {o n x : ν}, ¬ orig x → x ∈ ({o, n} : Finset ν) → orig o → x = n := by
    intro o n x hx hm ho
    rcases Finset.mem_insert.1 hm with h | h
    · exact absurd (h ▸ ho) hx
    · exact Finset.mem_singleton.1 h
  have hAo : oA ∈ ({oA, nA} : Finset ν) := by simp
  have hAn : nA ∈ ({oA, nA} : Finset ν) := by simp
  have hBo : oB ∈ ({oB, nB} : Finset ν) := by simp
  have hBn : nB ∈ ({oB, nB} : Finset ν) := by simp
  have hoAB : oA = oB := by
    rcases cA oA hAo with h | h
    · exact memo hoA h hnB
    · have e1 := memo hoA h hnC
      rcases cB oB hBo with h' | h'
      · exact (memo hoB h' hnA).symm
      · exact e1.trans (memo hoB h' hnC).symm
  have hnAB : nA = nB := by
    rcases cA nA hAn with h | h
    · exact memn hnA h hoB
    · have e1 := memn hnA h hoC
      rcases cB nB hBn with h' | h'
      · exact (memn hnB h' hoA).symm
      · exact e1.trans (memn hnB h' hoC).symm
  rw [← hoAB, ← hnAB, Finset.inter_self] at hAB
  have hne : oA ≠ nA := fun h => hnA (h ▸ hoA)
  rw [Finset.card_pair hne] at hAB
  omega

/-! ### HARD-5: injectivity -/

variable {orig : ν → Prop}

theorem lab_ne_zero (p : Pt ν ε) : lab S p ≠ 0 := by
  rcases p with ⟨v, r⟩ | ⟨E, k⟩
  · intro h
    have := supp_lab_copy S v r
    rw [h, suppQ_zero] at this
    exact absurd this.symm (Finset.singleton_ne_empty v)
  · by_cases hk : k.val < 9
    · intro h
      have := supp_aux_two S E k hk
      rw [h, suppQ_zero] at this; simp at this
    · intro h
      apply not_regZ_path S hk
      rw [h]; exact regZ_zero E _

/-- (HARD-5) distinct points have distinct labels -/
theorem lab_inj (hS : Shape S orig) {a b : Pt ν ε} (h : lab S a = lab S b) : a = b := by
  rcases a with ⟨v, r⟩ | ⟨E, k⟩ <;> rcases b with ⟨v', r'⟩ | ⟨E', k'⟩
  · have hs := congrArg suppQ h
    rw [show suppQ (lab S (.inl (v, r))) = {v} from supp_lab_copy S v r,
      show suppQ (lab S (.inl (v', r'))) = {v'} from supp_lab_copy S v' r'] at hs
    have hv : v = v' := Finset.singleton_injective hs
    subst hv
    have := congrArg (fun L => bcQ L v) h
    simp only [bc_lab_copy] at this
    rw [lam_inj r r' this]
  · exfalso
    by_cases hk : k'.val < 9
    · have h2 := supp_aux_two S E' k' hk
      rw [← h, supp_lab_copy] at h2; simp at h2
    · apply not_regZ_path S hk; rw [← h]; exact regZ_cLab _ _ v r
  · exfalso
    by_cases hk : k.val < 9
    · have h2 := supp_aux_two S E k hk
      rw [h, supp_lab_copy] at h2; simp at h2
    · apply not_regZ_path S hk; rw [h]; exact regZ_cLab _ _ v' r'
  · by_cases hE : E = E'
    · subst hE
      have := mlab_inj _ _ (Psi_inj S E h)
      simp only [Sum.inr.injEq] at this; rw [this]
    · exfalso
      by_cases hk : k.val < 9
      · by_cases hk' : k'.val < 9
        · have h1 := supp_aux_sub S E k hk
          have h2 := supp_aux_sub S E' k' hk'
          have h3 := supp_aux_two S E k hk
          rw [h] at h1 h3
          have := Finset.card_le_card (Finset.subset_inter h1 h2)
          have := inter_le_one S hS (Ne.symm hE)
          rw [Finset.inter_comm] at this
          omega
        · apply not_regZ_path S hk'
          rw [← h]; exact regZ_Psi_other S (Ne.symm hE) _ _
      · apply not_regZ_path S hk
        rw [h]; exact regZ_Psi_other S hE _ _

/-! ### HARD-6: closure -/

/-- the presence of a line all of whose points are used -/
theorem pres_path : ∀ K : Fin 20, 10 ≤ K.val → ∃ k ∈ privPart K, 9 ≤ k.val := by decide
theorem pres_true1 : ∀ K : Fin 20, present true 1 K = true := by decide
theorem pres_lt : ∀ (b : F) (K : Fin 20), K.val < 10 → present true b K = true := by decide

theorem locPt_mem_lline {E : ε} {K : Fin 20} {k : Fin 21} (hk : k ∈ privPart K) :
    (Sum.inr k : Lx) ∈ lline K := by
  unfold lline; simp [hk]

/-- all three points local to one equation -/
theorem closure_local (E : ε) {x y z : Lx} (hx : InU S (locPt S E x)) (hy : InU S (locPt S E y))
    (hz : InU S (locPt S E z)) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsum : lab S (locPt S E x) + lab S (locPt S E y) + lab S (locPt S E z) = 0) :
    ∃ K, present true (S.rhs E) K = true ∧
      lineOf S E K = {locPt S E x, locPt S E y, locPt S E z} := by
  rw [lab_loc, lab_loc, lab_loc, ← Psi_add, ← Psi_add, ← Psi_zero S E] at hsum
  obtain ⟨K, hK⟩ := local_closure x y z hxy hxz hyz (Psi_inj S E hsum)
  refine ⟨K, ?_, ?_⟩
  · by_cases hK10 : K.val < 10
    · exact pres_lt _ K hK10
    · obtain ⟨k, hk, hk9⟩ := pres_path K (by omega)
      have hmem := locPt_mem_lline (E := E) hk
      rw [hK] at hmem
      have hU : InU S (locPt S E (.inr k)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h <;> rw [h] <;> assumption
      have : S.rhs E = 1 := by
        rcases hU with h | h
        · omega
        · exact h
      rw [this]; exact pres_true1 K
  · rw [lineOf_loc, hK]; simp [Finset.image_insert]

/-- `p` is a point of equation E (a copy of one of its variables, or one of its private points) -/
def IsLoc (E : ε) (p : Pt ν ε) : Prop := ∃ x, locPt S E x = p

theorem isLoc_copy {E : ε} {v : ν} {r : Fin 4} (h : v ∈ varsE S E) : IsLoc S E (.inl (v, r)) := by
  simp only [varsE, Finset.mem_image, Finset.mem_univ, true_and] at h
  obtain ⟨i, rfl⟩ := h
  exact ⟨.inl (i, r), rfl⟩

theorem isLoc_priv (E : ε) (k : Fin 21) : IsLoc S E (.inr (E, k)) := ⟨.inr k, rfl⟩

/-- the closure statement, as a predicate on a triple -/
def Closes (a b c : Pt ν ε) : Prop :=
  ∃ E K, present true (S.rhs E) K = true ∧ lineOf S E K = {a, b, c}

theorem closes_local {E : ε} {a b c : Pt ν ε} (ha : IsLoc S E a) (hb : IsLoc S E b) (hc : IsLoc S E c)
    (hua : InU S a) (hub : InU S b) (huc : InU S c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsum : lab S a + lab S b + lab S c = 0) : Closes S a b c := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; obtain ⟨z, rfl⟩ := hc
  obtain ⟨K, hK, hl⟩ := closure_local S E hua hub huc (fun h => hab (by rw [h]))
    (fun h => hac (by rw [h])) (fun h => hbc (by rw [h])) hsum
  exact ⟨E, K, hK, hl⟩

theorem closes_perm12 {a b c : Pt ν ε} (h : Closes S b a c) : Closes S a b c := by
  obtain ⟨E, K, hK, hl⟩ := h; exact ⟨E, K, hK, by rw [hl, Finset.insert_comm]⟩
theorem closes_perm23 {a b c : Pt ν ε} (h : Closes S a c b) : Closes S a b c := by
  obtain ⟨E, K, hK, hl⟩ := h; exact ⟨E, K, hK, by rw [hl, Finset.pair_comm]⟩

theorem sum_perm12 {a b c : LQ ν ε} (h : a + b + c = 0) : b + a + c = 0 := by rw [add_comm b a]; exact h
theorem sum_perm23 {a b c : LQ ν ε} (h : a + b + c = 0) : a + c + b = 0 := by
  rw [add_assoc, add_comm c b, ← add_assoc]; exact h

theorem sum_rot {a b c : LQ ν ε} (h : a + b + c = 0) : c + a + b = 0 := by
  rw [add_comm c a, add_assoc, add_comm c b, ← add_assoc]; exact h

theorem eq_add_of_sum {a b c : LQ ν ε} (h : a + b + c = 0) : c = a + b := by
  have : c = -(a + b) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  rw [this, neg_eq_iff_add_eq_zero]
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_) <;> exact add_self_F _

/-- the path case: a is a path point of (E, t) -/
theorem closure_path (hS : Shape S orig) {E : ε} {k : Fin 21} (hk : ¬ k.val < 9) {b c : Pt ν ε}
    (hua : InU S (.inr (E, k))) (hub : InU S b) (huc : InU S c)
    (hab : (.inr (E, k) : Pt ν ε) ≠ b) (hac : (.inr (E, k) : Pt ν ε) ≠ c) (hbc : b ≠ c)
    (hsum : lab S (.inr (E, k)) + lab S b + lab S c = 0) : Closes S (.inr (E, k)) b c := by
  set t := tOf k hk
  -- one of b, c is a path point of (E, t)
  have key : ∀ {b c : Pt ν ε}, InU S b → InU S c → (.inr (E, k) : Pt ν ε) ≠ b →
      (.inr (E, k) : Pt ν ε) ≠ c → b ≠ c → lab S (.inr (E, k)) + lab S b + lab S c = 0 →
      (∃ k' : Fin 21, ∃ hk' : ¬ k'.val < 9, tOf k' hk' = t ∧ b = .inr (E, k')) →
      Closes S (.inr (E, k)) b c := by
    intro b c hub huc hab hac hbc hsum ⟨k', hk', ht', hb⟩
    subst hb
    by_cases hcl : IsLoc S E c
    · exact closes_local S (isLoc_priv S E k) (isLoc_priv S E k') hcl hua hub huc hab hac hbc hsum
    · exfalso
      have hc := eq_add_of_sum hsum
      rcases c with ⟨w, r⟩ | ⟨E', k''⟩
      · -- a copy: register (E,t) vanishes, so the pair of path points sums to a type-A label
        have hr : regZ E t (lab S (.inr (E, k)) + lab S (.inr (E, k'))) := by
          rw [← hc]; exact regZ_cLab E t w r
        change regZ E t (Psi S E (mlab (.inr k)) + Psi S E (mlab (.inr k'))) at hr
        rw [← Psi_add, regZ_Psi_iff] at hr
        obtain ⟨z, hzA, hz⟩ := path_pair (.inr k) (.inr k') t (regOf_path k hk)
          (by rw [regOf_path k' hk', ht']) (fun h => hab (by simp only [Sum.inr.injEq] at h; rw [h])) hr
        have hlz : lab S (locPt S E z) = lab S (.inl (w, r)) := by
          rw [lab_loc, hz, Psi_add, hc]; rfl
        exact hcl ⟨z, lab_inj S hS hlz⟩
      · by_cases hE : E' = E
        · exact hcl (hE ▸ isLoc_priv S E' k'')
        · by_cases hk'' : k''.val < 9
          · have hr : regZ E t (lab S (.inr (E, k)) + lab S (.inr (E, k'))) := by
              rw [← hc]; exact regZ_A S (p := .inr (E', k'')) hk'' E t
            change regZ E t (Psi S E (mlab (.inr k)) + Psi S E (mlab (.inr k'))) at hr
            rw [← Psi_add, regZ_Psi_iff] at hr
            obtain ⟨z, hzA, hz⟩ := path_pair (.inr k) (.inr k') t (regOf_path k hk)
              (by rw [regOf_path k' hk', ht']) (fun h => hab (by simp only [Sum.inr.injEq] at h; rw [h])) hr
            have hlz : lab S (locPt S E z) = lab S (.inr (E', k'')) := by
              rw [lab_loc, hz, Psi_add, hc]; rfl
            exact hcl ⟨z, lab_inj S hS hlz⟩
          · apply not_regZ_path S (E := E') hk''
            rw [hc]
            exact regZ_add (regZ_Psi_other S hE _ _) (regZ_Psi_other S hE _ _)
  rcases regZ_or_path S E t b with hb | hb
  · rcases regZ_or_path S E t c with hc | hc
    · exfalso
      apply not_regZ_path S (E := E) hk
      have := eq_add_of_sum (sum_rot (sum_rot hsum))
      rw [this]; exact regZ_add hb hc
    · exact closes_perm23 S (key huc hub hac hab (Ne.symm hbc) (sum_perm23 hsum) hc)
  · exact key hub huc hab hac hbc hsum hb

/-- all three copies: impossible -/
theorem no_copies {v v' v'' : ν} {r r' r'' : Fin 4}
    (hab : (.inl (v, r) : Pt ν ε) ≠ .inl (v', r')) (hac : (.inl (v, r) : Pt ν ε) ≠ .inl (v'', r''))
    (hbc : (.inl (v', r') : Pt ν ε) ≠ .inl (v'', r''))
    (hsum : lab S (.inl (v, r)) + lab S (.inl (v', r')) + lab S (.inl (v'', r'')) = 0) : False := by
  have s1 := supp_lab_copy S v r; have s2 := supp_lab_copy S v' r'; have s3 := supp_lab_copy S v'' r''
  have c1 := cover hsum (v := v) (by rw [s1]; simp)
  have c2 := cover (sum_perm12 hsum) (v := v') (by rw [s2]; simp)
  rw [s2, s3] at c1; rw [s1, s3] at c2
  simp only [Finset.mem_singleton] at c1 c2
  have hv : v = v' ∧ v = v'' := by
    rcases c1 with h | h
    · refine ⟨h, ?_⟩
      have c3 := cover (sum_perm12 (sum_perm23 hsum)) (v := v'') (by rw [s3]; simp)
      rw [s1, s2] at c3; simp only [Finset.mem_singleton] at c3
      rcases c3 with h' | h'
      · exact h'.symm
      · exact h.trans h'.symm
    · refine ⟨?_, h⟩
      rcases c2 with h' | h'
      · exact h'.symm
      · exact h.trans h'.symm
  obtain ⟨rfl, rfl⟩ := hv
  have := congrArg (fun L => bcQ L v) hsum
  simp only [bcQ_add, bc_lab_copy] at this
  refine lam_three r r' r'' (fun h => hab (by rw [h])) (fun h => hac (by rw [h]))
    (fun h => hbc (by rw [h])) this

/-- an aux point of E together with a type-A point not belonging to E: impossible -/
theorem no_nonlocal (hS : Shape S orig) {E : ε} {k : Fin 21} (hk : k.val < 9) {b c : Pt ν ε}
    (hbA : IsA b) (hcA : IsA c) (hbl : ¬ IsLoc S E b)
    (hsum : lab S (.inr (E, k)) + lab S b + lab S c = 0) : False := by
  set A := suppQ (lab S (.inr (E, k)))
  have hAsub : A ⊆ varsE S E := supp_aux_sub S E k hk
  have hA2 : 2 ≤ A.card := supp_aux_two S E k hk
  have cA : ∀ v ∈ A, v ∈ suppQ (lab S b) ∨ v ∈ suppQ (lab S c) := fun v hv => cover hsum hv
  have cB : ∀ v ∈ suppQ (lab S b), v ∈ A ∨ v ∈ suppQ (lab S c) :=
    fun v hv => cover (sum_perm12 hsum) hv
  have cC : ∀ v ∈ suppQ (lab S c), v ∈ A ∨ v ∈ suppQ (lab S b) :=
    fun v hv => cover (sum_perm12 (sum_perm23 hsum)) hv
  rcases b with ⟨w, r⟩ | ⟨E', k'⟩
  · -- b is a copy of w ∉ E
    have hw : w ∉ varsE S E := fun h => hbl (isLoc_copy S h)
    rw [supp_lab_copy] at cA cB
    have hwC : w ∈ suppQ (lab S c) := by
      rcases cB w (Finset.mem_singleton_self w) with h | h
      · exact absurd (hAsub h) hw
      · exact h
    rcases c with ⟨w', r'⟩ | ⟨E'', k''⟩
    · rw [supp_lab_copy] at hwC cA
      obtain ⟨v, hv⟩ := Finset.card_pos.1 (by omega : 0 < A.card)
      rcases cA v hv with h | h <;> rw [Finset.mem_singleton] at h
      · exact hw (h ▸ hAsub hv)
      · rw [Finset.mem_singleton] at hwC; exact hw (hwC ▸ h ▸ hAsub hv)
    · have hk'' : k''.val < 9 := hcA
      have hCsub := supp_aux_sub S E'' k'' hk''
      have hAsub' : A ⊆ varsE S E'' := by
        intro v hv
        rcases cA v hv with h | h
        · rw [Finset.mem_singleton] at h; exact absurd (h ▸ hAsub hv) hw
        · exact hCsub h
      by_cases hE : E = E''
      · subst hE; exact hw (hCsub hwC)
      · have := Finset.card_le_card (Finset.subset_inter hAsub hAsub')
        have := inter_le_one S hS hE
        omega
  · -- b is an aux point of E' ≠ E
    have hk' : k'.val < 9 := hbA
    have hE' : E ≠ E' := fun h => hbl (h ▸ isLoc_priv S E k')
    set B := suppQ (lab S (.inr (E', k')))
    have hBsub : B ⊆ varsE S E' := supp_aux_sub S E' k' hk'
    have hB2 : 2 ≤ B.card := supp_aux_two S E' k' hk'
    have hAB : (A ∩ B).card ≤ 1 :=
      le_trans (Finset.card_le_card (Finset.inter_subset_inter hAsub hBsub)) (inter_le_one S hS hE')
    rcases c with ⟨x, r⟩ | ⟨E'', k''⟩
    · rw [supp_lab_copy] at cA cB
      obtain ⟨v, hvA, hvB⟩ : ∃ v ∈ A, v ∉ B := by
        by_contra h; push Not at h
        have : A ⊆ A ∩ B := fun v hv => Finset.mem_inter.2 ⟨hv, h v hv⟩
        have := Finset.card_le_card this; omega
      obtain ⟨u, huB, huA⟩ : ∃ u ∈ B, u ∉ A := by
        by_contra h; push Not at h
        have : B ⊆ A ∩ B := fun u hu => Finset.mem_inter.2 ⟨h u hu, hu⟩
        have := Finset.card_le_card this; omega
      have h1 : v = x := by
        rcases cA v hvA with h | h
        · exact absurd h hvB
        · exact Finset.mem_singleton.1 h
      have h2 : u = x := by
        rcases cB u huB with h | h
        · exact absurd h huA
        · exact Finset.mem_singleton.1 h
      exact hvB (h1 ▸ h2 ▸ huB)
    · have hk'' : k''.val < 9 := hcA
      set C := suppQ (lab S (.inr (E'', k'')))
      have hCsub : C ⊆ varsE S E'' := supp_aux_sub S E'' k'' hk''
      have hC2 : 2 ≤ C.card := supp_aux_two S E'' k'' hk''
      by_cases h1 : E'' = E
      · subst h1
        have : B ⊆ varsE S E'' ∩ varsE S E' := fun v hv => Finset.mem_inter.2
          ⟨(cB v hv).elim (fun h => hAsub h) (fun h => hCsub h), hBsub hv⟩
        have := Finset.card_le_card this
        have := inter_le_one S hS hE'; omega
      · by_cases h2 : E'' = E'
        · subst h2
          have : A ⊆ varsE S E ∩ varsE S E'' := fun v hv => Finset.mem_inter.2
            ⟨hAsub hv, (cA v hv).elim (fun h => hBsub h) (fun h => hCsub h)⟩
          have := Finset.card_le_card this
          have := inter_le_one S hS hE'; omega
        · -- three distinct equations: a triangle of size-2 supports
          have hAC : (A ∩ C).card ≤ 1 :=
            le_trans (Finset.card_le_card (Finset.inter_subset_inter hAsub hCsub))
              (inter_le_one S hS (Ne.symm h1))
          have hBC : (B ∩ C).card ≤ 1 :=
            le_trans (Finset.card_le_card (Finset.inter_subset_inter hBsub hCsub))
              (inter_le_one S hS (Ne.symm h2))
          have two : ∀ {X Y Z : Finset ν}, (∀ v ∈ X, v ∈ Y ∨ v ∈ Z) → (X ∩ Y).card ≤ 1 →
              (X ∩ Z).card ≤ 1 → X.card ≤ 2 := by
            intro X Y Z hc hxy hxz
            have : X ⊆ (X ∩ Y) ∪ (X ∩ Z) := fun v hv =>
              (hc v hv).elim (fun h => Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, h⟩))
                (fun h => Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, h⟩))
            have := Finset.card_le_card this
            have := Finset.card_union_le (X ∩ Y) (X ∩ Z)
            omega
          have hA' := supp_two S hS E k hk (two cA hAB hAC)
          have hB' := supp_two S hS E' k' hk' (two cB (by rw [Finset.inter_comm]; exact hAB) hBC)
          have hC' := supp_two S hS E'' k'' hk''
            (two cC (by rw [Finset.inter_comm]; exact hAC) (by rw [Finset.inter_comm]; exact hBC))
          exact triangle hA' hB' hC' cA cB hAB

/-- **HARD-6 (closure lemma).** Every zero-sum triple of distinct labels of used points is a line of
Φ_ind. -/
theorem closure (hS : Shape S orig) {a b c : Pt ν ε} (hua : InU S a) (hub : InU S b) (huc : InU S c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hsum : lab S a + lab S b + lab S c = 0) :
    Closes S a b c := by
  classical
  -- path points first
  have path_first : ∀ {a b c : Pt ν ε}, InU S a → InU S b → InU S c → a ≠ b → a ≠ c → b ≠ c →
      lab S a + lab S b + lab S c = 0 → ¬ IsA a → Closes S a b c := by
    intro a b c hua hub huc hab hac hbc hsum ha
    rcases a with ⟨v, r⟩ | ⟨E, k⟩
    · exact absurd trivial ha
    · exact closure_path S hS ha hua hub huc hab hac hbc hsum
  by_cases ha : IsA a
  · by_cases hb : IsA b
    · by_cases hc : IsA c
      · -- all of type A
        have aux_first : ∀ {a b c : Pt ν ε}, InU S a → InU S b → InU S c → a ≠ b → a ≠ c → b ≠ c →
            lab S a + lab S b + lab S c = 0 → IsA b → IsA c →
            ∀ E k, k.val < 9 → a = .inr (E, k) → Closes S a b c := by
          intro a b c hua hub huc hab hac hbc hsum hb hc E k hk ha
          subst ha
          by_cases hbl : IsLoc S E b
          · by_cases hcl : IsLoc S E c
            · exact closes_local S (isLoc_priv S E k) hbl hcl hua hub huc hab hac hbc hsum
            · exact absurd (no_nonlocal S hS hk hc hb hcl (sum_perm23 hsum)) id
          · exact absurd (no_nonlocal S hS hk hb hc hbl hsum) id
        rcases a with ⟨v, r⟩ | ⟨E, k⟩
        · rcases b with ⟨v', r'⟩ | ⟨E', k'⟩
          · rcases c with ⟨v'', r''⟩ | ⟨E'', k''⟩
            · exact absurd (no_copies S hab hac hbc hsum) id
            · exact closes_perm23 S (closes_perm12 S
                (aux_first huc hua hub (Ne.symm hac) (Ne.symm hbc) hab (sum_rot hsum) ha hb E'' k'' hc rfl))
          · exact closes_perm12 S (aux_first hub hua huc (Ne.symm hab) hbc hac (sum_perm12 hsum)
              ha hc E' k' hb rfl)
        · exact aux_first hua hub huc hab hac hbc hsum hb hc E k ha rfl
      · exact closes_perm23 S (closes_perm12 S
          (path_first huc hua hub (Ne.symm hac) (Ne.symm hbc) hab (sum_rot hsum) hc))
    · exact closes_perm12 S (path_first hub hua huc (Ne.symm hab) hbc hac (sum_perm12 hsum) hb)
  · exact path_first hua hub huc hab hac hbc hsum ha

end PauliCtx.Hardness
