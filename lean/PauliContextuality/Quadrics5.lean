/-
Quadrics5.lean — blueprint TQ-2 (equality cases) and TQ-3 for the 3-qubit quadrics:

  * `Qp5_eq_21` : **deg Q⁺(5,2) = 21**  (35 points, 105 lines; ratio 1/5).
  * `Qm5_eq_9`  : **deg Q⁻(5,2) = 9**   (27 points, 45 lines;  ratio 1/5).
  * `Qp5_rigid`, `Qm5_rigid` (TQ-3): every optimal assignment of W(5,2) violates exactly 21 (resp. 9)
      lines of every Sp(6,2)-translate of Q⁺(5,2) (resp. Q⁻(5,2)).

Lower bound (TR-1 with the orthogonal group, as in the blueprint):
  1. the parabolic section a₀^⊥ ∩ Q (a₀ = Y₁ for Q⁺, a₀ = X₁ for Q⁻) is the doily: the map
     r ↦ Y₁^{q⁺(r)} ⊗ r (resp. X₁^{q⁺(r)} ⊗ r) sends the lines of W(3,2) onto its lines and preserves
     ω, so by ALG-3 its degree is deg W(3,2) = 3;
  2. the orthogonal group O(q) (symplectic permutations preserving q) contains the reflections
     x ↦ x + ω(x,a)a with q(a) = 1, and these move a base line to every line of the quadric
     (explicit words of length ≤ 3, checked by computation);
  3. TR-1: |L(Q)|·3 ≤ 15·deg Q, i.e. deg Q⁺(5,2) ≥ 105·3/15 = 21 and deg Q⁻(5,2) ≥ 45·3/15 = 9.
Upper bounds: the W(5,2) witness restricted to the quadric violates 21 (resp. 9) lines.
-/
import PauliContextuality.GeoBounds
import PauliContextuality.ThreeQubit

namespace PauliCtx.Spectral

open Config

/-! ### the quadrics -/

/-- Q⁺(5,2): non-zero singular points of `q⁺ = x·z` on 3 qubits -/
def QP5 : Finset (V 3) := Finset.univ.filter (fun p => p ≠ 0 ∧ qplus p = 0)
/-- Q⁻(5,2): non-zero singular points of `q⁻ = x·z + x₁ + z₁` on 3 qubits -/
def QM5 : Finset (V 3) := Finset.univ.filter (fun p => p ≠ 0 ∧ qminus p = 0)

theorem zero_not_mem_QP5 : (0 : V 3) ∉ QP5 := by simp [QP5]
theorem zero_not_mem_QM5 : (0 : V 3) ∉ QM5 := by simp [QM5]

noncomputable def Qplus5 : Config (V 3) := configX QP5 zero_not_mem_QP5
noncomputable def Qminus5 : Config (V 3) := configX QM5 zero_not_mem_QM5

theorem card_OP_QP5 : (OP QP5).card = 630 := by unfold QP5; rw [OP_filter]; native_decide
theorem card_OP_QM5 : (OP QM5).card = 270 := by unfold QM5; rw [OP_filter]; native_decide

theorem Qplus5_lines : Qplus5.lines.card = 105 := by
  have := six_mul_card QP5 zero_not_mem_QP5; rw [card_OP_QP5] at this; unfold Qplus5; omega
theorem Qminus5_lines : Qminus5.lines.card = 45 := by
  have := six_mul_card QM5 zero_not_mem_QM5; rw [card_OP_QM5] at this; unfold Qminus5; omega

/-- computable mirrors of the lines and of a parabolic section -/
def linesC {N : ℕ} (X : Finset (V N)) : Finset (Finset (V N)) := (OP X).image tri

def secL {N : ℕ} (L : Finset (Finset (V N))) (a : V N) : Finset (Finset (V N)) :=
  L.filter (fun l => ∀ p ∈ l, omega a p = 0)

/-! ### upper bounds -/

theorem Qp5_witness : ((OP QP5).filter (violP (witnessAssign 3 (fun _ => true) witnessW5))).card = 126 := by
  unfold QP5; rw [OP_filter]; native_decide

theorem Qm5_witness : ((OP QM5).filter (violP (witnessAssign 3 (fun _ => true) witnessW5))).card = 54 := by
  unfold QM5; rw [OP_filter]; native_decide

theorem Qp5_le_21 : Qplus5.deg ≤ 21 := deg_le_of_pairs _ _ _ _ Qp5_witness
theorem Qm5_le_9 : Qminus5.deg ≤ 9 := deg_le_of_pairs _ _ _ _ Qm5_witness

/-! ### the orthogonal group and its reflections -/

theorem qminus_add (p q : V 3) : qminus (p + q) = qminus p + qminus q + omega p q := by
  unfold qminus; rw [qplus_add]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring

/-- the orthogonal group of a quadratic form `Q` (with polar form ω), inside Sp(6,2) -/
def OG (Q : V 3 → F) : Subgroup (Equiv.Perm (V 3)) where
  carrier := {φ | IsSymp φ ∧ ∀ x, Q (φ x) = Q x}
  mul_mem' := fun {a b} ha hb => ⟨IsSymp.mul ha.1 hb.1, fun x => by
    simp only [Equiv.Perm.mul_apply]; rw [ha.2, hb.2]⟩
  one_mem' := ⟨IsSymp.one, fun _ => rfl⟩
  inv_mem' := fun {a} ha => ⟨IsSymp.inv ha.1, fun x => by
    have h := ha.2 (a⁻¹ x)
    rw [show a (a⁻¹ x) = x by simp] at h
    exact h.symm⟩

theorem mem_OG {Q : V 3 → F} {φ : Equiv.Perm (V 3)} : φ ∈ OG Q ↔ IsSymp φ ∧ ∀ x, Q (φ x) = Q x :=
  Iff.rfl

instance (Q : V 3 → F) : DecidablePred (· ∈ OG Q) := fun φ =>
  decidable_of_iff (IsSymp φ ∧ ∀ x, Q (φ x) = Q x) mem_OG.symm

/-- a reflection in a non-singular vector is orthogonal -/
theorem transvP_mem_OG {Q : V 3 → F} (hQ : ∀ p q, Q (p + q) = Q p + Q q + omega p q) (hQ0 : Q 0 = 0)
    {a : V 3} (ha : Q a = 1) : transvP a ∈ OG Q := by
  refine ⟨transvP_symp a, fun x => ?_⟩
  rw [transvP_apply, hQ]
  rcases F_cases (omega x a) with h | h
  · rw [h, zero_smul, hQ0]; simp [omega]
  · rw [h, one_smul, ha, h, add_assoc, show (1 : F) + 1 = 0 by decide, add_zero]

/-- orthogonal maps preserve the lines of the quadric -/
theorem OG_map_lines {Q : V 3 → F} {X : Finset (V 3)} (h0 : (0 : V 3) ∉ X)
    (hX : ∀ p, p ∈ X ↔ p ≠ 0 ∧ Q p = 0) :
    ∀ g ∈ OG Q, ∀ l ∈ (configX X h0).lines, l.map g.toEmbedding ∈ (configX X h0).lines := by
  intro g hg l hl
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
  have hs : IsSymp g := hg.1
  rw [show tri p = tri (p.1, p.2) from rfl, tri_map hs.1]
  refine Finset.mem_image.2 ⟨(g p.1, g p.2), ?_, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := mem_OP.1 hp
  have mem : ∀ x ∈ X, g x ∈ X := by
    intro x hx
    obtain ⟨hx0, hxQ⟩ := (hX x).1 hx
    exact (hX _).2 ⟨hs.ne_zero hx0, by rw [hg.2]; exact hxQ⟩
  refine mem_OP.2 ⟨mem _ h1, mem _ h2, by rw [hs.2]; exact h3, ?_⟩
  rw [← hs.1]; exact mem _ h4

/-! ### words of reflections -/

def dec3 (k : ℕ) : V 3 := decodeLex 3 k

/-- apply the reflections of a word, first letter first -/
def imgW : List ℕ → V 3 → V 3
  | [] => fun x => x
  | a :: w => fun x => imgW w (transv (dec3 a) x)

noncomputable def permW : List ℕ → Equiv.Perm (V 3)
  | [] => 1
  | a :: w => permW w * transvP (dec3 a)

theorem permW_apply (w : List ℕ) (x : V 3) : permW w x = imgW w x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => simp only [permW, imgW, Equiv.Perm.mul_apply, ih]; rfl

theorem permW_mem {Q : V 3 → F} (hQ : ∀ p q, Q (p + q) = Q p + Q q + omega p q) (hQ0 : Q 0 = 0)
    (w : List ℕ) (hw : ∀ a ∈ w, Q (dec3 a) = 1) : permW w ∈ OG Q := by
  induction w with
  | nil => exact (OG Q).one_mem
  | cons a w ih =>
    exact (OG Q).mul_mem (ih fun b hb => hw b (List.mem_cons_of_mem a hb))
      (transvP_mem_OG hQ hQ0 (hw a List.mem_cons_self))

/-- the base line {Z₃, Z₂, Z₂Z₃} -/
def l0 : Finset (V 3) := {dec3 1, dec3 2, dec3 3}

def wordsQp : List (List ℕ) := [[], [9], [13], [18], [22], [25], [29], [41], [44], [50], [52], [57], [60], [9, 13], [9, 18], [9, 19], [9, 22], [9, 23], [9, 41], [9, 50], [9, 51], [9, 52], [9, 53], [13, 18], [13, 19], [13, 22], [13, 23], [13, 44], [13, 50], [13, 51], [13, 52], [13, 53], [18, 22], [18, 41], [18, 43], [18, 44], [18, 46], [18, 50], [22, 41], [22, 43], [22, 44], [22, 46], [22, 52], [25, 29], [25, 41], [25, 43], [25, 44], [25, 46], [25, 57], [29, 41], [29, 43], [29, 44], [29, 46], [29, 60], [41, 44], [50, 52], [57, 60], [9, 13, 18], [9, 13, 19], [9, 13, 25], [9, 13, 26], [9, 13, 50], [9, 13, 51], [9, 13, 57], [9, 13, 58], [9, 18, 22], [9, 18, 41], [9, 18, 43], [9, 18, 50], [9, 19, 23], [9, 19, 41], [9, 19, 43], [9, 19, 51], [9, 22, 41], [9, 22, 43], [9, 22, 52], [9, 23, 41], [9, 23, 43], [9, 23, 53], [9, 50, 52], [9, 51, 53], [13, 18, 44], [13, 18, 46], [13, 18, 51], [13, 19, 44], [13, 19, 46], [13, 19, 50], [13, 22, 44], [13, 22, 46], [13, 22, 53], [13, 23, 44], [13, 23, 46], [13, 23, 52], [18, 22, 41], [18, 22, 43], [18, 22, 57], [18, 22, 58], [18, 41, 44], [18, 43, 46], [25, 29, 41], [25, 29, 43], [25, 29, 50], [25, 29, 51], [25, 41, 46], [25, 43, 44]]
def wordsQm : List (List ℕ) := [[], [9], [12], [18], [20], [25], [28], [40], [44], [48], [52], [56], [60], [9, 18], [9, 19], [9, 20], [9, 21], [9, 48], [9, 49], [9, 52], [9, 53], [12, 18], [12, 19], [12, 20], [12, 21], [12, 48], [12, 49], [12, 52], [12, 53], [18, 40], [18, 42], [18, 44], [18, 46], [20, 40], [20, 42], [20, 44], [20, 46], [25, 40], [25, 42], [25, 44], [25, 46], [28, 40], [28, 42], [28, 44], [28, 46]]

theorem wordsQp_ok : ∀ w ∈ wordsQp, ∀ a ∈ w, qplus (dec3 a) = 1 := by native_decide
theorem wordsQm_ok : ∀ w ∈ wordsQm, ∀ a ∈ w, qminus (dec3 a) = 1 := by native_decide

/-- the images of the base line under the words (computed once) -/
def imgsOf (ws : List (List ℕ)) : List (Finset (V 3)) := ws.map (fun w => l0.image (imgW w))
def imgsQp : List (Finset (V 3)) := imgsOf wordsQp
def imgsQm : List (Finset (V 3)) := imgsOf wordsQm

theorem coverQp' : ∀ l ∈ linesC QP5, l ∈ imgsQp := by
  unfold QP5 linesC; rw [OP_filter]; native_decide
theorem coverQm' : ∀ l ∈ linesC QM5, l ∈ imgsQm := by
  unfold QM5 linesC; rw [OP_filter]; native_decide

theorem cover_of {X : Finset (V 3)} {ws : List (List ℕ)} (h : ∀ l ∈ linesC X, l ∈ imgsOf ws) :
    ∀ l ∈ linesC X, ∃ w ∈ ws, l0.image (imgW w) = l := by
  intro l hl
  obtain ⟨w, hw, he⟩ := List.mem_map.1 (h l hl)
  exact ⟨w, hw, he⟩

theorem coverQp : ∀ l ∈ linesC QP5, ∃ w ∈ wordsQp, l0.image (imgW w) = l := cover_of coverQp'
theorem coverQm : ∀ l ∈ linesC QM5, ∃ w ∈ wordsQm, l0.image (imgW w) = l := cover_of coverQm'

theorem l0_Qp : l0 ∈ linesC QP5 := by unfold QP5 linesC; rw [OP_filter]; native_decide
theorem l0_Qm : l0 ∈ linesC QM5 := by unfold QM5 linesC; rw [OP_filter]; native_decide

/-- line-transitivity from words reaching every line from `l0` -/
theorem trans_of_words {Q : V 3 → F} (hQ : ∀ p q, Q (p + q) = Q p + Q q + omega p q) (hQ0 : Q 0 = 0)
    {X : Finset (V 3)} (h0 : (0 : V 3) ∉ X) (ws : List (List ℕ))
    (hw : ∀ w ∈ ws, ∀ a ∈ w, Q (dec3 a) = 1)
    (hcov : ∀ l ∈ linesC X, ∃ w ∈ ws, l0.image (imgW w) = l) :
    ∀ l ∈ (configX X h0).lines, ∀ l' ∈ (configX X h0).lines, ∃ g ∈ OG Q, l.map g.toEmbedding = l' := by
  have reach : ∀ l ∈ (configX X h0).lines, ∃ g ∈ OG Q, l0.map g.toEmbedding = l := by
    intro l hl
    obtain ⟨w, hwm, hw'⟩ := hcov l hl
    refine ⟨permW w, permW_mem hQ hQ0 w (hw w hwm), ?_⟩
    rw [Finset.map_eq_image, ← hw']
    exact Finset.image_congr (fun x _ => permW_apply w x)
  intro l hl l' hl'
  obtain ⟨g, hg, rfl⟩ := reach l hl
  obtain ⟨g', hg', rfl⟩ := reach l' hl'
  refine ⟨g' * g⁻¹, (OG Q).mul_mem hg' ((OG Q).inv_mem hg), ?_⟩
  rw [Finset.map_map]; congr 1; exact Function.Embedding.ext fun x => by simp

/-! ### the section a₀^⊥ is the doily -/

/-- realisation of a sub-family of an induced configuration by the identity -/
theorem real_subX {N : ℕ} {X : Finset (V N)} (h0 : (0 : V N) ∉ X) (L : Finset (Finset (V N)))
    (hL : L ⊆ (configX X h0).lines) : PauliRealization ((configX X h0).sub L hL) id := by
  refine ⟨Function.injective_id, fun l hl => ?_⟩
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (hL hl)
  have h := isLine_of_OP h0 hp
  refine ⟨p.1, p.2, p.1 + p.2, rfl, h, ?_⟩
  show (configX X h0).sign (tri p) = _
  rw [configX_sign h0 hp]; exact sgnF_eq_sign h

/-- Sp-translates of a sub-family have the same degree (ALG-3) -/
theorem deg_imgLX {N : ℕ} {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {g : Equiv.Perm (V N)} (hg : IsSymp g)
    (L : Finset (Finset (V N))) (hL : L ⊆ (configX X h0).lines)
    (hL' : imgL g L ⊆ (configX X h0).lines) :
    ((configX X h0).sub (imgL g L) hL').deg = ((configX X h0).sub L hL).deg := by
  symm
  exact deg_invariant_equiv _ _ g id id (real_subX h0 L hL) (real_subX h0 _ hL') rfl
    (fun p q => hg.2 p q)

/-- the embedding of the doily: r ↦ (x₀ ⊗ r) with x-bit `cx r`, z-bit `cz r` on the new first qubit -/
def doilyE (cx cz : V 2 → F) (r : V 2) : V 3 := (Fin.cons (cx r) r.1, Fin.cons (cz r) r.2)

theorem doilyE_inj (cx cz : V 2 → F) : Function.Injective (doilyE cx cz) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [doilyE] at h1 h2
  exact Prod.ext (Fin.cons_injective2 h1).2 (Fin.cons_injective2 h2).2

theorem omega_doilyE (cx cz : V 2 → F) (hcomm : ∀ p q, cx p * cz q + cz p * cx q = 0) (p q : V 2) :
    omega (doilyE cx cz p) (doilyE cx cz q) = omega p q := by
  unfold omega doilyE
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hcomm, zero_add]

/-- the doily inside a quadric: degree 3 (ALG-3 against W(3,2)) -/
theorem section_deg {X : Finset (V 3)} (h0 : (0 : V 3) ∉ X) (cx cz : V 2 → F)
    (hcomm : ∀ p q, cx p * cz q + cz p * cx q = 0)
    (hadd : ∀ a b : V 2, omega a b = 0 → doilyE cx cz (a + b) = doilyE cx cz a + doilyE cx cz b)
    (hmemX : ∀ r : V 2, r ≠ 0 → doilyE cx cz r ∈ X)
    {S0 : Finset (Finset (V 3))} (hsub : S0 ⊆ (configX X h0).lines)
    (hsec : S0 = (W 2).lines.image (fun l => l.image (doilyE cx cz))) :
    ((configX X h0).sub S0 hsub).deg = 3 ∧ S0.card = 15 := by
  set e : V 2 ↪ V 3 := ⟨doilyE cx cz, doilyE_inj cx cz⟩
  have hS0 : S0 = (W 2).lines.image (fun l => l.map e) := by
    rw [hsec]; congr 1; funext l; rw [Finset.map_eq_image]; rfl
  refine ⟨?_, ?_⟩
  · have hmem : ∀ l ∈ (W 2).lines, l.map e ∈ ((configX X h0).sub S0 hsub).lines := fun l hl => by
      show l.map e ∈ S0; rw [hS0]; exact Finset.mem_image_of_mem _ hl
    have hW : PauliRealization (W 2) id := by
      have := real_sub (W 2).lines (subset_refl _); rwa [Config.sub_self] at this
    have hinv : (W 2).deg = (((configX X h0).sub S0 hsub).comap e (W 2).lines hmem).deg := by
      refine deg_invariant (W 2) _ id (doilyE cx cz) hW ?_ rfl
        (fun p q => omega_doilyE cx cz hcomm p q)
      refine ⟨doilyE_inj cx cz, fun l hl => ?_⟩
      obtain ⟨a, b, h, rfl⟩ := mem_W_lines.1 hl
      have hab := hadd a b h.comm
      have hnz : ∀ r : V 2, r ≠ 0 → doilyE cx cz r ≠ 0 := fun r hr h' =>
        h0 (h' ▸ hmemX r hr)
      have hL : IsLine (doilyE cx cz a) (doilyE cx cz b) (doilyE cx cz a + doilyE cx cz b) := by
        refine ⟨(doilyE_inj cx cz).ne h.ne_ab, ?_, ?_, hnz a h.nz_a, hnz b h.nz_b, ?_, add_self_V _, ?_⟩
        · rw [← hab]; exact (doilyE_inj cx cz).ne h.ne_ac
        · rw [← hab]; exact (doilyE_inj cx cz).ne h.ne_bc
        · rw [← hab]; exact hnz _ h.nz_c
        · rw [omega_doilyE cx cz hcomm]; exact h.comm
      have hp : (doilyE cx cz a, doilyE cx cz b) ∈ OP X :=
        mem_OP.2 ⟨hmemX a h.nz_a, hmemX b h.nz_b, hL.comm, by rw [← hab]; exact hmemX _ h.nz_c⟩
      refine ⟨a, b, a + b, rfl, by rw [hab]; exact hL, ?_⟩
      show (configX X h0).sign ((tri (a, b)).map e) = _
      have : (tri (a, b)).map e = tri (doilyE cx cz a, doilyE cx cz b) := by
        simp [tri, Finset.map_insert, e, hab]
      rw [this, configX_sign h0 hp, sgnF_eq_sign hL, hab]
    calc ((configX X h0).sub S0 hsub).deg
        = (((configX X h0).sub S0 hsub).comap e (W 2).lines hmem).deg := (deg_comap _ e _ hmem hS0).symm
      _ = 3 := by rw [← hinv, W3_eq_3]
  · rw [hS0, Finset.card_image_of_injective _ (Finset.map_injective e), card_lines_W2]

/-- **TR-1 for a quadric with its orthogonal group** -/
theorem quad_transfer {Q : V 3 → F} (hQ : ∀ p q, Q (p + q) = Q p + Q q + omega p q) (hQ0 : Q 0 = 0)
    {X : Finset (V 3)} (h0 : (0 : V 3) ∉ X) (hX : ∀ p, p ∈ X ↔ p ≠ 0 ∧ Q p = 0)
    (ws : List (List ℕ)) (hw : ∀ w ∈ ws, ∀ a ∈ w, Q (dec3 a) = 1)
    (hcov : ∀ l ∈ linesC X, ∃ w ∈ ws, l0.image (imgW w) = l)
    {S0 : Finset (Finset (V 3))} (hsub : S0 ⊆ (configX X h0).lines)
    (hdeg : ((configX X h0).sub S0 hsub).deg = 3) :
    (configX X h0).lines.card * 3 ≤ S0.card * (configX X h0).deg := by
  have hmap := OG_map_lines h0 hX
  refine Config.transfer (configX X h0) (OG Q) S0 hsub hmap (trans_of_words hQ hQ0 h0 ws hw hcov) 3 ?_
  intro g hg s
  have hL' : imgL g S0 ⊆ (configX X h0).lines := by
    intro l hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
    exact hmap g hg m (hsub hm)
  have h1 := deg_imgLX h0 hg.1 S0 hsub hL'
  have h2 := deg_le ((configX X h0).sub (imgL g S0) hL') s
  rw [violated_sub] at h2
  omega

theorem qplus_zero : qplus (0 : V 3) = 0 := by simp [qplus]
theorem qminus_zero : qminus (0 : V 3) = 0 := by simp [qminus, qplus]

theorem mem_QP5 (p : V 3) : p ∈ QP5 ↔ p ≠ 0 ∧ qplus p = 0 := by simp [QP5]
theorem mem_QM5 (p : V 3) : p ∈ QM5 ↔ p ≠ 0 ∧ qminus p = 0 := by simp [QM5]

theorem qplus_cons (a b : F) (r : V 2) :
    qplus ((Fin.cons a r.1, Fin.cons b r.2) : V 3) = a * b + qplus r := by
  unfold qplus; rw [Fin.sum_univ_succ]; simp

theorem F_mul_self (x : F) : x * x = x := by revert x; decide

theorem secQp_eq : secL (linesC QP5) (dec3 36) =
    (linesC (Wpts 2)).image (fun l => l.image (doilyE qplus qplus)) := by
  unfold QP5 linesC; rw [Wpts_eq]; simp only [OP_filter]; native_decide

theorem secQm_eq : secL (linesC QM5) (dec3 32) =
    (linesC (Wpts 2)).image (fun l => l.image (doilyE qplus (fun _ => 0))) := by
  unfold QM5 linesC; rw [Wpts_eq]; simp only [OP_filter]; native_decide

theorem doilyE_add (cx cz : V 2 → F) (hx : ∀ a b, omega a b = 0 → cx (a + b) = cx a + cx b)
    (hz : ∀ a b, omega a b = 0 → cz (a + b) = cz a + cz b) (a b : V 2) (h : omega a b = 0) :
    doilyE cx cz (a + b) = doilyE cx cz a + doilyE cx cz b := by
  unfold doilyE
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · refine Fin.cases ?_ (fun j => ?_) i <;> simp [hx a b h, hz a b h]

theorem qplus_add_comm (a b : V 2) (h : omega a b = 0) : qplus (a + b) = qplus a + qplus b := by
  rw [qplus_add, h, add_zero]

/-- **TQ-2 equality case.** deg Q⁺(5,2) ≥ 21. -/
theorem Qp5_ge_21 : 21 ≤ Qplus5.deg := by
  have hsub : secL (linesC QP5) (dec3 36) ⊆ (configX QP5 zero_not_mem_QP5).lines :=
    Finset.filter_subset _ _
  obtain ⟨hdeg, hcard⟩ := section_deg zero_not_mem_QP5 qplus qplus
    (fun p q => add_self_F _)
    (doilyE_add _ _ qplus_add_comm qplus_add_comm)
    (fun r hr => by
      rw [mem_QP5]
      refine ⟨fun h => hr ?_, ?_⟩
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        simp only [doilyE] at h1 h2
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · have := congrFun h1 i.succ; simpa using this
        · have := congrFun h2 i.succ; simpa using this
      · unfold doilyE; rw [qplus_cons, F_mul_self]; exact add_self_F _)
    hsub secQp_eq
  have h := quad_transfer qplus_add qplus_zero zero_not_mem_QP5 mem_QP5 wordsQp wordsQp_ok coverQp
    hsub hdeg
  have hl : (configX QP5 zero_not_mem_QP5).lines.card = 105 := Qplus5_lines
  rw [hcard, hl] at h
  show 21 ≤ (configX QP5 zero_not_mem_QP5).deg
  omega

theorem qminus_cons (a b : F) (r : V 2) :
    qminus ((Fin.cons a r.1, Fin.cons b r.2) : V 3) = a * b + qplus r + a + b := by
  unfold qminus; rw [qplus_cons]; simp

/-- **TQ-2 equality case.** deg Q⁻(5,2) ≥ 9. -/
theorem Qm5_ge_9 : 9 ≤ Qminus5.deg := by
  have hsub : secL (linesC QM5) (dec3 32) ⊆ (configX QM5 zero_not_mem_QM5).lines :=
    Finset.filter_subset _ _
  obtain ⟨hdeg, hcard⟩ := section_deg zero_not_mem_QM5 qplus (fun _ => 0)
    (fun p q => by simp)
    (doilyE_add _ _ qplus_add_comm (fun _ _ _ => by simp))
    (fun r hr => by
      rw [mem_QM5]
      refine ⟨fun h => hr ?_, ?_⟩
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        simp only [doilyE] at h1 h2
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · have := congrFun h1 i.succ; simpa using this
        · have := congrFun h2 i.succ; simpa using this
      · unfold doilyE; rw [qminus_cons, mul_zero, zero_add, add_zero]; exact add_self_F _)
    hsub secQm_eq
  have h := quad_transfer qminus_add qminus_zero zero_not_mem_QM5 mem_QM5 wordsQm wordsQm_ok coverQm
    hsub hdeg
  have hl : (configX QM5 zero_not_mem_QM5).lines.card = 45 := Qminus5_lines
  rw [hcard, hl] at h
  show 9 ≤ (configX QM5 zero_not_mem_QM5).deg
  omega

/-- **TQ-2 equality case.** deg Q⁺(5,2) = 21. -/
theorem Qp5_eq_21 : Qplus5.deg = 21 := le_antisymm Qp5_le_21 Qp5_ge_21
/-- **TQ-2 equality case.** deg Q⁻(5,2) = 9. -/
theorem Qm5_eq_9 : Qminus5.deg = 9 := le_antisymm Qm5_le_9 Qm5_ge_9

/-! ### TQ-3 for the quadrics -/

theorem QP5_sub_W : QP5 ⊆ Wpts 3 := by
  intro p hp; rw [mem_Wpts]; exact (Finset.mem_filter.1 hp).2.1
theorem QM5_sub_W : QM5 ⊆ Wpts 3 := by
  intro p hp; rw [mem_Wpts]; exact (Finset.mem_filter.1 hp).2.1

/-- **TQ-3 (Q⁺(5,2)).** Every optimal assignment of W(5,2) violates exactly 21 lines of every
Sp(6,2)-translate of Q⁺(5,2). -/
theorem Qp5_rigid (s : V 3 → F) (hs : ((W 3).violated s).card = (W 3).deg) :
    ∀ g ∈ Sp 3, ((W 3).violated s ∩ imgL g Qplus5.lines).card = 21 := by
  have hsub : Qplus5.lines ⊆ (W 3).lines := configX_lines_mono zero_not_mem_QP5 (zero_not_mem_W 3) QP5_sub_W
  have hdeg : ((W 3).sub Qplus5.lines hsub).deg = Qplus5.deg :=
    deg_sub_configX zero_not_mem_QP5 (zero_not_mem_W 3) QP5_sub_W
  have hne : Qplus5.lines.Nonempty := Finset.card_pos.1 (by rw [Qplus5_lines]; norm_num)
  have heq : (W 3).lines.card * ((W 3).sub Qplus5.lines hsub).deg = Qplus5.lines.card * (W 3).deg := by
    rw [hdeg, Qp5_eq_21, Qplus5_lines, card_lines_W3, W5_eq_63]
  intro g hg
  have := rho_rigid Qplus5.lines hsub hne heq s hs g hg
  rw [this, hdeg]; exact Qp5_eq_21

/-- **TQ-3 (Q⁻(5,2)).** Every optimal assignment of W(5,2) violates exactly 9 lines of every
Sp(6,2)-translate of Q⁻(5,2). -/
theorem Qm5_rigid (s : V 3 → F) (hs : ((W 3).violated s).card = (W 3).deg) :
    ∀ g ∈ Sp 3, ((W 3).violated s ∩ imgL g Qminus5.lines).card = 9 := by
  have hsub : Qminus5.lines ⊆ (W 3).lines := configX_lines_mono zero_not_mem_QM5 (zero_not_mem_W 3) QM5_sub_W
  have hdeg : ((W 3).sub Qminus5.lines hsub).deg = Qminus5.deg :=
    deg_sub_configX zero_not_mem_QM5 (zero_not_mem_W 3) QM5_sub_W
  have hne : Qminus5.lines.Nonempty := Finset.card_pos.1 (by rw [Qminus5_lines]; norm_num)
  have heq : (W 3).lines.card * ((W 3).sub Qminus5.lines hsub).deg = Qminus5.lines.card * (W 3).deg := by
    rw [hdeg, Qm5_eq_9, Qminus5_lines, card_lines_W3, W5_eq_63]
  intro g hg
  have := rho_rigid Qminus5.lines hsub hne heq s hs g hg
  rw [this, hdeg]; exact Qm5_eq_9

end PauliCtx.Spectral
