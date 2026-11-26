/-
RealizeDeg.lean — HARD-9 for the Pauli realisation (blueprint HARD-5, HARD-6, HARD-9).

The labels of Realize.lean, transported to `V n` (n = number of qubits), give a set X of Paulis.
  * `lines_configX` : the induced configuration `configX X` has exactly the lines of Φ_ind
      (HARD-5 for ⊇, the closure lemma HARD-6 for ⊆), with the same signs;
  * `realized_degree`  : **deg (configX X) = OPT(S) + |b|** for every E3 system with the shape of a
      triangle split;
  * `realized_sub_degree` : the sub-configuration on the lines of Φ_sub has degree OPT(S);
  * `induced_reduction` : for every XOR system with non-empty rows there is an induced Pauli
      configuration of degree OPT + |b'| and a sub-configuration of it of degree OPT.
-/
import PauliContextuality.Realize
import PauliContextuality.ToE3
import PauliContextuality.Transfer
import PauliContextuality.GeoBounds

set_option synthInstance.maxSize 2048

namespace PauliCtx.Hardness

open Config Spectral Model Classical

variable {ν ε : Type} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε]

/-! ### transport to `V n` -/

/-- the number of qubits -/
noncomputable def nq (ν ε : Type) [Fintype ν] [Fintype ε] : ℕ := Fintype.card (Qb ν ε)

noncomputable def qe : Fin (nq ν ε) ≃ Qb ν ε := (Fintype.equivFin (Qb ν ε)).symm

/-- a label as a Pauli label of `V n` -/
noncomputable def toV (L : LQ ν ε) : V (nq ν ε) := (L.1 ∘ qe, L.2 ∘ qe)

theorem toV_add (L L' : LQ ν ε) : toV (L + L') = toV L + toV L' := rfl

theorem toV_inj : Function.Injective (toV (ν := ν) (ε := ε)) := by
  intro L L' h
  have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · have := congrFun h1 (qe.symm q); simpa [toV] using this
  · have := congrFun h2 (qe.symm q); simpa [toV] using this

theorem LQ_add_self (L : LQ ν ε) : L + L = 0 :=
  Prod.ext (funext fun _ => add_self_F _) (funext fun _ => add_self_F _)

theorem toV_zero : toV (0 : LQ ν ε) = 0 := rfl

theorem omega_toV (L L' : LQ ν ε) : omega (toV L) (toV L') = omegaQ L L' := by
  unfold omega omegaQ toV
  exact Fintype.sum_equiv qe _ _ (fun _ => rfl)

theorem dot_toV (L L' : LQ ν ε) : dot (toV L).2 (toV L').1 = zxQ L L' := by
  unfold dot zxQ toV
  exact Fintype.sum_equiv qe _ _ (fun _ => rfl)

theorem ycount_toV (L : LQ ν ε) : ycount (toV L) = ycountQ L := by
  unfold ycount ycountQ toV
  rw [Finset.card_filter, Finset.card_filter]
  exact Fintype.sum_equiv qe _ _ (fun _ => rfl)

theorem sgnF_toV (L L' : LQ ν ε) : sgnF (toV L, toV L') = sgnQ L L' := by
  unfold sgnF sgnQ phQ ph
  simp only
  rw [ycount_toV, ycount_toV, dot_toV, ← toV_add, ycount_toV]

/-! ### the realised configuration -/

variable (S : E3 ν ε)

/-- the realisation map -/
noncomputable def fR (p : Pt ν ε) : V (nq ν ε) := toV (lab S p)

/-- the used points -/
noncomputable def Ufin : Finset (Pt ν ε) := Finset.univ.filter (InU S)

/-- the realised point set -/
noncomputable def XR : Finset (V (nq ν ε)) := (Ufin S).image (fR S)

theorem zero_not_mem_XR : (0 : V (nq ν ε)) ∉ XR S := by
  intro h
  obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
  exact lab_ne_zero S p (toV_inj (hp.trans toV_zero.symm))

/-- the induced Pauli configuration -/
noncomputable def DR : Config (V (nq ν ε)) := configX (XR S) (zero_not_mem_XR S)

variable {orig : ν → Prop}

theorem fR_inj (hS : Shape S orig) : Function.Injective (fR S) :=
  fun a b h => lab_inj S hS (toV_inj h)

noncomputable def fE (hS : Shape S orig) : Pt ν ε ↪ V (nq ν ε) := ⟨fR S, fR_inj S hS⟩

theorem present_InU : ∀ (b : F) (K : Fin 20), present true b K = true →
    ∀ i ∈ privPart K, i.val < 9 ∨ b = 1 := by decide

theorem lineOf_InU {E : ε} {K : Fin 20} (hK : present true (S.rhs E) K = true) :
    ∀ p ∈ lineOf S E K, InU S p := by
  intro p hp
  rw [lineOf_loc] at hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  rcases x with ⟨i, r⟩ | k
  · trivial
  · have : k ∈ privPart K := by unfold lline at hx; simpa using hx
    exact present_InU _ K hK k this

theorem mem_Phi {l : Finset (Pt ν ε)} :
    l ∈ (Phi S true).lines ↔ ∃ E K, present true (S.rhs E) K = true ∧ lineOf S E K = l := by
  simp only [Phi, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, presentSet,
    Finset.mem_filter]

theorem lineOf_three (E : ε) (K : Fin 20) :
    ∃ a b c, lineOf S E K = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a, b, c, hab, hac, hbc, h⟩ := Finset.card_eq_three.1 (card_lineOf S E K)
  exact ⟨a, b, c, h, hab, hac, hbc⟩

/-- **HARD-5 + HARD-6.** The induced configuration on the labels has exactly the lines of Φ_ind. -/
theorem lines_DR (hS : Shape S orig) :
    (DR S).lines = (Phi S true).lines.image (fun l => l.map (fE S hS)) := by
  ext m
  constructor
  · intro hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
    have hL := isLine_of_OP (zero_not_mem_XR S) hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_OP.1 hp
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 h1
    obtain ⟨b, hb, hfb⟩ := Finset.mem_image.1 h2
    obtain ⟨c, hc, hfc⟩ := Finset.mem_image.1 h4
    have hsum : lab S a + lab S b + lab S c = 0 := by
      have e : fR S c = fR S a + fR S b := by rw [hfc, hfa, hfb]
      have : lab S c = lab S a + lab S b := toV_inj (by
        show fR S c = toV (lab S a + lab S b); rw [e, toV_add]; rfl)
      rw [this]; exact LQ_add_self _
    have hab : a ≠ b := fun h => hL.ne_ab (by rw [← hfa, ← hfb, h])
    have hac : a ≠ c := fun h => hL.ne_ac (by rw [← hfc, ← hfa, h])
    have hbc : b ≠ c := fun h => hL.ne_bc (by rw [← hfc, ← hfb, h])
    obtain ⟨E, K, hK, hl⟩ := closure S hS (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
      (Finset.mem_filter.1 hc).2 hab hac hbc hsum
    refine Finset.mem_image.2 ⟨lineOf S E K, (mem_Phi S).2 ⟨E, K, hK, rfl⟩, ?_⟩
    rw [hl]
    simp only [Finset.map_insert, Finset.map_singleton, tri]
    show ({fR S a, fR S b, fR S c} : Finset _) = _
    rw [hfa, hfb, hfc]
  · intro hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨E, K, hK, rfl⟩ := (mem_Phi S).1 hl
    obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := lineOf_three S E K
    have hU := lineOf_InU S hK
    have ha : a ∈ lineOf S E K := by rw [habc]; simp
    have hb : b ∈ lineOf S E K := by rw [habc]; simp
    have hc : c ∈ lineOf S E K := by rw [habc]; simp
    have hsum := line_sum S E K
    rw [habc, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, ← add_assoc] at hsum
    have hc' : fR S c = fR S a + fR S b := by
      unfold fR; rw [← toV_add, eq_add_of_sum hsum]
    have mem : ∀ p ∈ lineOf S E K, fR S p ∈ XR S := fun p hp =>
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hU p hp⟩)
    refine Finset.mem_image.2 ⟨(fR S a, fR S b), mem_OP.2 ⟨mem a ha, mem b hb, ?_, ?_⟩, ?_⟩
    · show omega (toV (lab S a)) (toV (lab S b)) = 0
      rw [omega_toV]; exact line_comm S E K a ha b hb
    · rw [← hc']; exact mem c hc
    · rw [habc]
      simp only [Finset.map_insert, Finset.map_singleton, tri]
      show _ = ({fR S a, fR S b, fR S c} : Finset _)
      rw [hc']

/-- the signs agree -/
theorem sign_DR (hS : Shape S orig) {l : Finset (Pt ν ε)} (hl : l ∈ (Phi S true).lines) :
    (DR S).sign (l.map (fE S hS)) = (Phi S true).sign l := by
  obtain ⟨E, K, hK, rfl⟩ := (mem_Phi S).1 hl
  obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := lineOf_three S E K
  have hU := lineOf_InU S hK
  have ha : a ∈ lineOf S E K := by rw [habc]; simp
  have hb : b ∈ lineOf S E K := by rw [habc]; simp
  have hc : c ∈ lineOf S E K := by rw [habc]; simp
  have hsum := line_sum S E K
  rw [habc, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, ← add_assoc] at hsum
  have hc' : fR S c = fR S a + fR S b := by unfold fR; rw [← toV_add, eq_add_of_sum hsum]
  have mem : ∀ p ∈ lineOf S E K, fR S p ∈ XR S := fun p hp =>
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hU p hp⟩)
  have hp : (fR S a, fR S b) ∈ OP (XR S) := mem_OP.2 ⟨mem a ha, mem b hb,
    by show omega (toV (lab S a)) (toV (lab S b)) = 0; rw [omega_toV]; exact line_comm S E K a ha b hb,
    by rw [← hc']; exact mem c hc⟩
  have hmap : (lineOf S E K).map (fE S hS) = tri (fR S a, fR S b) := by
    rw [habc]; simp only [Finset.map_insert, Finset.map_singleton, tri]
    show ({fR S a, fR S b, fR S c} : Finset _) = _
    rw [hc']
  rw [hmap]
  show (configX (XR S) (zero_not_mem_XR S)).sign _ = _
  rw [configX_sign _ hp, Phi_sign]
  show sgnF (toV (lab S a), toV (lab S b)) = sgnT K
  rw [sgnF_toV]; exact line_sgn S E K a ha b hb hab

/-- **HARD-9 (Pauli realisation).** deg of the induced Pauli configuration = OPT + |b|. -/
theorem realized_degree (hS : Shape S orig) : (DR S).deg = S.toSys.opt + nNeg S := by
  have hmem : ∀ l ∈ (Phi S true).lines, l.map (fE S hS) ∈ (DR S).lines := fun l hl => by
    rw [lines_DR S hS]; exact Finset.mem_image_of_mem _ hl
  rw [← deg_comap (DR S) (fE S hS) _ hmem (lines_DR S hS), ← induced_degree S]
  exact deg_congr _ _ rfl (fun l hl => sign_DR S hS hl)

theorem present_sub : ∀ (b : F) (K : Fin 20), present false b K = true → present true b K = true := by
  decide

/-- the lines of Φ_sub inside the realised configuration -/
noncomputable def LsubR (hS : Shape S orig) : Finset (Finset (V (nq ν ε))) :=
  (Phi S false).lines.image (fun l => l.map (fE S hS))

theorem Phi_sub_lines : (Phi S false).lines ⊆ (Phi S true).lines := by
  intro l hl
  simp only [Phi, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, presentSet,
    Finset.mem_filter] at hl ⊢
  obtain ⟨E, K, hK, rfl⟩ := hl
  exact ⟨E, K, present_sub _ K hK, rfl⟩

theorem LsubR_sub (hS : Shape S orig) : LsubR S hS ⊆ (DR S).lines := by
  rw [lines_DR S hS]; exact Finset.image_subset_image (Phi_sub_lines S)

/-- **HARD-9 (sub-configuration).** The sub-configuration on the lines of Φ_sub has degree OPT. -/
theorem realized_sub_degree (hS : Shape S orig) :
    ((DR S).sub (LsubR S hS) (LsubR_sub S hS)).deg = S.toSys.opt := by
  have hmem : ∀ l ∈ (Phi S false).lines, l.map (fE S hS) ∈ ((DR S).sub (LsubR S hS) (LsubR_sub S hS)).lines :=
    fun l hl => Finset.mem_image_of_mem _ hl
  rw [← deg_comap _ (fE S hS) _ hmem rfl, ← sub_degree S]
  refine deg_congr _ _ rfl (fun l hl => ?_)
  show (DR S).sign (l.map (fE S hS)) = (Phi S false).sign l
  rw [sign_DR S hS (Phi_sub_lines S hl)]
  rfl

/-! ### the split system has the right shape -/

theorem split_shape (S : E3 ν ε) : Shape S.split (fun u => ∃ v, u = Sum.inl v) where
  share := by
    intro E E' i j i' j' hij h1 h2
    by_contra hE
    have hsh := split_share S E E' hE
    have hne : S.split.var E i ≠ S.split.var E j := fun h => hij (S.split.inj E h)
    have m1 : S.split.var E i ∈ S.split.toSys.eqs E ∩ S.split.toSys.eqs E' := by
      rw [Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · fin_cases i <;> simp [E3.toSys]
      · rw [h1]; fin_cases i' <;> simp [E3.toSys]
    have m2 : S.split.var E j ∈ S.split.toSys.eqs E ∩ S.split.toSys.eqs E' := by
      rw [Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · fin_cases j <;> simp [E3.toSys]
      · rw [h2]; fin_cases j' <;> simp [E3.toSys]
    have := Finset.card_le_one.1 hsh _ m1 _ m2
    exact hne this
  mid := fun E => ⟨_, (split_middle S E).1⟩
  ends := by
    intro E
    obtain ⟨-, ⟨q0, h0⟩, ⟨q2, h2⟩⟩ := split_middle S E
    refine ⟨?_, ?_⟩
    · rintro ⟨v, hv⟩; rw [h0] at hv; exact Sum.inr_ne_inl hv
    · rintro ⟨v, hv⟩; rw [h2] at hv; exact Sum.inr_ne_inl hv

/-- **HARD-3 + HARD-2 + HARD-5/6 + HARD-9.** For every XOR system S with non-empty rows, the
induced Pauli configuration built from split(toE3 S) has degree OPT(S) + |b'|, and its
sub-configuration on the lines of Φ_sub has degree OPT(S). -/
theorem induced_reduction (S : GSys ν ε) (hne : ∀ e, (S.eqs e).Nonempty) :
    (DR (toE3 S).split).deg = S.opt + nNeg (toE3 S).split ∧
    ((DR (toE3 S).split).sub (LsubR _ (split_shape (toE3 S))) (LsubR_sub _ (split_shape (toE3 S)))).deg
      = S.opt := by
  refine ⟨?_, ?_⟩
  · rw [realized_degree _ (split_shape (toE3 S)), split_opt, toE3_opt S hne]
  · rw [realized_sub_degree _ (split_shape (toE3 S)), split_opt, toE3_opt S hne]

end PauliCtx.Hardness
