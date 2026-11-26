/-
Section.lean — blueprint 06, CONE-2: all subspace sections of W(2N−1,2).

For a subspace U ⊆ F^{2N} with radical R = U ∩ U^⊥ of dimension t and dim U = 2k + t:
      deg W(U) = 4^t · deg W(2k−1,2),        W(U) := configX (U ∖ {0}).

  Part 1 (standard section). `Xstd k t ⊆ V (k+t)`: the non-zero labels with no X on the last t qubits,
    i.e. V k ⊗ ⟨Z_{k+1}, …, Z_{k+t}⟩.  Its commuting zero-sum triples are exactly the images of the
    lines of Cone_t(W(2k−1,2)) under (v, τ) ↦ v ⊗ Z^τ (`lines_Xstd`), with the cone signs
    (`sign_Xstd`), so `std_section_degree` : deg = deg Cone_t(W k) = 4^t deg W k (CONE-1).
  Part 2 (normal form, no Witt theorem). `exists_sympData`: every subspace U has a basis
    e₁..e_k, f₁..f_k, r₁..r_t with ω(e_i, f_j) = δ_ij, ω(e,e) = ω(f,f) = 0 and r_j ∈ rad U, built by
    induction on dim U (split off a hyperbolic pair).  The map ψ : V (k+t) → V N sending
    X_i ↦ e_i, Z_i ↦ f_i, Z_{k+j} ↦ r_j is ω-preserving and injective on the standard subspace and
    maps it onto U, so DEN-1′ (`deg_configX_map`) transports the degree (`W_section_degree`).
-/
import PauliContextuality.Den3
import PauliContextuality.Tensor
import PauliContextuality.Cone
import PauliContextuality.GaugeKernel

open Module

namespace PauliCtx.Spectral

open Config

/-! ### joined labels -/

section Join

variable {N₁ N₂ : ℕ}

theorem joinV_add (a b : V N₁) (a' b' : V N₂) : joinV a a' + joinV b b' = joinV (a + b) (a' + b') := by
  unfold joinV
  refine Prod.ext ?_ ?_
  · exact append_add _ _ _ _
  · exact append_add _ _ _ _

theorem joinV_inj {a b : V N₁} {a' b' : V N₂} : joinV a a' = joinV b b' ↔ a = b ∧ a' = b' := by
  constructor
  · intro h
    have := congrArg joinE.symm h
    rw [joinE_symm_joinV, joinE_symm_joinV] at this
    exact Prod.mk.inj this
  · rintro ⟨rfl, rfl⟩; rfl

theorem joinV_eq_zero {a : V N₁} {a' : V N₂} : joinV a a' = 0 ↔ a = 0 ∧ a' = 0 := by
  rw [← joinV_zero, joinV_inj]

theorem omega_join (a b : V N₁) (a' b' : V N₂) :
    omega (joinV a a') (joinV b b') = omega a b + omega a' b' := by
  unfold omega joinV
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem ycount_zt (σ : Fin N₂ → F) : ycount ((0, σ) : V N₂) = 0 := by simp [ycount]

theorem ph_join (a b : V N₁) (σ σ' : Fin N₂ → F) :
    ph (joinV a (0, σ)) (joinV b (0, σ')) = ph a b := by
  unfold ph
  rw [joinV_add, ycount_join, ycount_join, ycount_join, ycount_zt, ycount_zt]
  have e1 : ((0, σ) : V N₂) + (0, σ') = (0, σ + σ') := by ext <;> simp
  rw [e1, ycount_zt]
  have e2 : dot (joinV a ((0 : Fin N₂ → F), σ)).2 (joinV b ((0 : Fin N₂ → F), σ')).1 = dot a.2 b.1 := by
    unfold joinV; simp only; rw [dot_append]; simp [dot]
  rw [e2]; push_cast; ring

/-- every label splits as `joinV` of its two parts -/
def splitL (p : V (N₁ + N₂)) : V N₁ := (fun i => p.1 (Fin.castAdd N₂ i), fun i => p.2 (Fin.castAdd N₂ i))
def splitR (p : V (N₁ + N₂)) : V N₂ := (fun j => p.1 (Fin.natAdd N₁ j), fun j => p.2 (Fin.natAdd N₁ j))

theorem join_split (p : V (N₁ + N₂)) : joinV (splitL p) (splitR p) = p := by
  unfold joinV splitL splitR
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]

end Join

section Perm
variable {α : Type} [DecidableEq α]
theorem fs3_132 (a b c : α) : ({a, c, b} : Finset α) = {a, b, c} := by rw [Finset.pair_comm]
theorem fs3_213 (a b c : α) : ({b, a, c} : Finset α) = {a, b, c} := Finset.insert_comm _ _ _
theorem fs3_231 (a b c : α) : ({b, c, a} : Finset α) = {a, b, c} := by
  rw [Finset.pair_comm c a, Finset.insert_comm]
theorem fs3_312 (a b c : α) : ({c, a, b} : Finset α) = {a, b, c} := by
  rw [Finset.insert_comm c a, Finset.pair_comm c b]
end Perm

/-! ### Part 1: the standard section V k ⊗ ⟨Z⟩^t and the cone -/

section Std

variable (k t : ℕ)

/-- the standard subspace: no X on the last t qubits -/
def Sstd : Submodule F (V (k + t)) where
  carrier := {p | ∀ j : Fin t, p.1 (Fin.natAdd k j) = 0}
  add_mem' := by intro p q hp hq j; simp [hp j, hq j]
  zero_mem' := by intro j; rfl
  smul_mem' := by intro c p hp j; simp [hp j]

/-- its non-zero points -/
def Xstd : Finset (V (k + t)) :=
  Finset.univ.filter (fun p => p ≠ 0 ∧ ∀ j : Fin t, p.1 (Fin.natAdd k j) = 0)

theorem zero_not_mem_Xstd : (0 : V (k + t)) ∉ Xstd k t := by simp [Xstd]

theorem Xstd_sub : (Xstd k t : Set (V (k + t))) ⊆ Sstd k t := fun p hp =>
  (Finset.mem_filter.1 hp).2.2

variable {k t}

theorem mem_Xstd_join {u : V k} {σ : Fin t → F} :
    joinV u (0, σ) ∈ Xstd k t ↔ ¬ (u = 0 ∧ σ = 0) := by
  simp only [Xstd, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, -⟩ ⟨rfl, rfl⟩; exact h (by rw [show ((0 : Fin t → F)) = (0 : V t).2 from rfl]; exact joinV_zero)
  · intro h
    refine ⟨fun h0 => h ?_, fun j => ?_⟩
    · obtain ⟨h1, h2⟩ := joinV_eq_zero.1 h0
      exact ⟨h1, congrArg Prod.snd h2⟩
    · simp [joinV, Fin.append_right]

theorem Xstd_split {p : V (k + t)} (hp : p ∈ Xstd k t) :
    ∃ u : V k, ∃ σ : Fin t → F, p = joinV u (0, σ) := by
  refine ⟨splitL p, (splitR p).2, ?_⟩
  have h : (splitR p).1 = 0 := funext fun j => (Finset.mem_filter.1 hp).2.2 j
  conv_lhs => rw [← join_split p]
  congr 1
  exact Prod.ext h rfl

/-- the base points: non-zero labels of `V k` -/
abbrev Bpt (k : ℕ) := PtX (Wpts k)

/-- W(2k−1,2) on its point subtype -/
noncomputable def Gk (k : ℕ) : Config (Bpt k) :=
  (W k).comap (Function.Embedding.subtype _) (linesSub (Wpts k) (zero_not_mem_W k))
    (fun l hl => by
      unfold W; rw [lines_eq_linesSub (Wpts k) (zero_not_mem_W k)]; exact Finset.mem_image_of_mem _ hl)

/- The instances on `Option (Bpt k) × (Fin t → F)` exceed the default instance-size budget
(the same happens in RealizeDeg.lean); we synthesise them once with a larger budget. -/
set_option synthInstance.maxSize 1024 in
instance instDecEqCPB (k t : ℕ) : DecidableEq (CP (Bpt k) t) := inferInstance

set_option synthInstance.maxSize 1024 in
instance instFintypeCPB (k t : ℕ) : Fintype (CP (Bpt k) t) := inferInstance

theorem Gk_deg (k : ℕ) : (Gk k).deg = (W k).deg := by
  unfold Gk
  exact deg_comap _ _ _ _ (by unfold W; exact lines_eq_linesSub (Wpts k) (zero_not_mem_W k))

/-- the base label of a cone point -/
def baseOf : Option (Bpt k) → V k
  | none => 0
  | some u => u.1

/-- (v, τ) ↦ v ⊗ Z^τ -/
def Estd (q : CP (Bpt k) t) : V (k + t) := joinV (baseOf q.1) (0, q.2)

theorem Estd_inj : Function.Injective (Estd (k := k) (t := t)) := by
  rintro ⟨o, τ⟩ ⟨o', τ'⟩ h
  obtain ⟨h1, h2⟩ := joinV_inj.1 h
  have hτ : τ = τ' := congrArg Prod.snd h2
  subst hτ
  congr 1
  rcases o with _ | ⟨u, hu⟩ <;> rcases o' with _ | ⟨u', hu'⟩ <;> simp only [baseOf] at h1
  · rfl
  · exact absurd h1.symm ((Finset.mem_erase.1 hu').1)
  · exact absurd h1 ((Finset.mem_erase.1 hu).1)
  · simp [h1]

def EstdE : CP (Bpt k) t ↪ V (k + t) := ⟨Estd, Estd_inj⟩

theorem ph_Estd (q q' : CP (Bpt k) t) : ph (Estd q) (Estd q') = ph (baseOf q.1) (baseOf q'.1) :=
  ph_join _ _ _ _

theorem omega_Estd (q q' : CP (Bpt k) t) :
    omega (Estd q) (Estd q') = omega (baseOf q.1) (baseOf q'.1) := by
  unfold Estd; rw [omega_join]; simp [omega]

theorem Estd_add (q q' : CP (Bpt k) t) :
    Estd q + Estd q' = joinV (baseOf q.1 + baseOf q'.1) (0, q.2 + q'.2) := by
  unfold Estd; rw [joinV_add]; congr 1

theorem Estd_mem {q : CP (Bpt k) t} (hq : q ≠ (none, 0)) : Estd q ∈ Xstd k t := by
  unfold Estd
  rw [mem_Xstd_join]
  rintro ⟨h1, h2⟩
  apply hq
  rcases q with ⟨_ | ⟨u, hu⟩, σ⟩
  · simp only at h2; rw [h2]
  · exact absurd h1 ((Finset.mem_erase.1 hu).1)

theorem baseOf_ne_zero (u : Bpt k) : baseOf (some u) ≠ 0 := (Finset.mem_erase.1 u.2).1

/-- every cone line maps to a commuting zero-sum triple of the standard section, with the cone sign -/
theorem cone_line_image {L : Finset (CP (Bpt k) t)} (hL : L ∈ (cone t (Gk k)).lines) :
    ∃ pq ∈ OP (Xstd k t), L.map EstdE = tri pq ∧ sgnF pq = (cone t (Gk k)).sign L := by
  rcases Finset.mem_union.1 hL with hl | hvi
  · -- a lift
    simp only [lifts, liftsOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hl
    obtain ⟨ℓ, hℓ, τ, hτ, rfl⟩ := hl
    have hℓW : ℓ.map (Function.Embedding.subtype _) ∈ (W k).lines := by
      unfold W; rw [lines_eq_linesSub (Wpts k) (zero_not_mem_W k)]; exact Finset.mem_image_of_mem _ hℓ
    obtain ⟨⟨a, b⟩, hab, habl⟩ := Finset.mem_image.1 hℓW
    have hline := isLine_of_OP (zero_not_mem_W k) hab
    obtain ⟨ha, hb, hω, hc⟩ := mem_OP.1 hab
    simp only at ha hb hω hc
    set a' : Bpt k := ⟨a, ha⟩
    set b' : Bpt k := ⟨b, hb⟩
    set c' : Bpt k := ⟨a + b, hc⟩
    have hℓeq : ℓ = {a', b', c'} := by
      apply Finset.map_injective (Function.Embedding.subtype (· ∈ Wpts k))
      rw [← habl]; simp [tri, a', b', c']
    have hne : a' ≠ b' ∧ a' ≠ c' ∧ b' ≠ c' := by
      refine ⟨fun h => hline.ne_ab (congrArg Subtype.val h), fun h => hline.ne_ac (congrArg Subtype.val h),
        fun h => hline.ne_bc (congrArg Subtype.val h)⟩
    have hτc : τ c' = τ a' + τ b' := by
      rw [hℓeq, Finset.sum_insert (by simp [hne.1, hne.2.1]), Finset.sum_insert (by simp [hne.2.2]),
        Finset.sum_singleton, ← add_assoc] at hτ
      exact third_fun t hτ
    refine ⟨(Estd (some a', τ a'), Estd (some b', τ b')), ?_, ?_, ?_⟩
    · refine mem_OP.2 ⟨Estd_mem (by simp), Estd_mem (by simp), ?_, ?_⟩
      · simp only; rw [omega_Estd]; exact hω
      · simp only; rw [Estd_add]; simp only [baseOf]
        rw [mem_Xstd_join]; rintro ⟨h, -⟩; exact hline.nz_c h
    · rw [hℓeq]
      simp only [lift, Finset.image_insert, Finset.image_singleton, Finset.map_insert,
        Finset.map_singleton, tri]
      rw [Estd_add]
      simp only [EstdE, Function.Embedding.coeFn_mk, baseOf, hτc]
      rfl
    · rw [cone_sign_lift t hℓ hτ]
      show sgnF (Estd (some a', τ a'), Estd (some b', τ b')) =
        (configX (Wpts k) (zero_not_mem_W k)).sign (ℓ.map (Function.Embedding.subtype _))
      rw [← habl, configX_sign _ hab]
      unfold sgnF; simp only; rw [ph_Estd]; rfl
  · have hnot : L ∉ lifts t (Gk k) := vline_not_lift t hvi
    have hsign : (cone t (Gk k)).sign L = 0 := by
      show (if L ∈ lifts t (Gk k) then _ else 0) = 0; rw [if_neg hnot]
    rw [hsign]
    rcases Finset.mem_union.1 hvi with hv | hi
    · obtain ⟨⟨v, τ, τ'⟩, hx, rfl⟩ := Finset.mem_image.1 hv
      have hne : τ ≠ τ' := (Finset.mem_filter.1 hx).2
      have hττ : τ + τ' ≠ 0 := by
        intro h; apply hne; have := congrArg (τ + ·) h; simpa [← add_assoc, add_self_fun] using this.symm
      refine ⟨(Estd (some v, τ), Estd (none, τ + τ')), ?_, ?_, ?_⟩
      · refine mem_OP.2 ⟨Estd_mem (by simp), Estd_mem (by simp [hττ]), ?_, ?_⟩
        · simp only; rw [omega_Estd]; simp [baseOf, omega]
        · simp only; rw [Estd_add]; simp only [baseOf, add_zero]
          rw [mem_Xstd_join]; rintro ⟨h, -⟩; exact baseOf_ne_zero v h
      · simp only [Finset.map_insert, Finset.map_singleton, tri, EstdE, Function.Embedding.coeFn_mk]
        rw [Estd_add]
        simp only [baseOf, add_zero]
        have e : τ + (τ + τ') = τ' := by rw [← add_assoc, add_self_fun, zero_add]
        rw [e]
        show {Estd (some v, τ), Estd (some v, τ'), Estd (none, τ + τ')} =
          ({Estd (some v, τ), Estd (none, τ + τ'), Estd (some v, τ')} : Finset _)
        rw [fs3_132]
      · unfold sgnF; simp only; rw [ph_Estd]; simp only [baseOf]
        rw [if_pos]; unfold ph; simp [dot, ycount]
    · obtain ⟨⟨σ, σ'⟩, hx, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hx).2
      have h12 : σ + σ' ≠ 0 := by
        intro h; apply h3; have := congrArg (σ + ·) h; simpa [← add_assoc, add_self_fun] using this.symm
      refine ⟨(Estd (none, σ), Estd (none, σ')), ?_, ?_, ?_⟩
      · refine mem_OP.2 ⟨Estd_mem (by simp [h1]), Estd_mem (by simp [h2]), ?_, ?_⟩
        · simp only; rw [omega_Estd]; simp [baseOf, omega]
        · simp only; rw [Estd_add]; simp only [baseOf, add_zero]
          rw [mem_Xstd_join]; rintro ⟨-, h⟩; exact h12 h
      · simp only [Finset.map_insert, Finset.map_singleton, tri, EstdE, Function.Embedding.coeFn_mk]
        rw [Estd_add]
        simp only [baseOf, add_zero]
        rfl
      · unfold sgnF; simp only; rw [ph_Estd]; simp only [baseOf]
        rw [if_pos]; unfold ph; simp [dot, ycount]

/-- every commuting zero-sum triple of the standard section comes from a cone line -/
theorem OP_Xstd_cone {pq : V (k + t) × V (k + t)} (hpq : pq ∈ OP (Xstd k t)) :
    ∃ L ∈ (cone t (Gk k)).lines, L.map EstdE = tri pq := by
  obtain ⟨hp, hq, hω, hpq'⟩ := mem_OP.1 hpq
  have hline := isLine_of_OP (zero_not_mem_Xstd k t) hpq
  obtain ⟨u, σ, hu⟩ := Xstd_split hp
  obtain ⟨u', σ', hu'⟩ := Xstd_split hq
  obtain ⟨p, q⟩ := pq
  simp only at hu hu' hp hq hω hpq' hline
  subst hu hu'
  have hω' : omega u u' = 0 := by rw [omega_join] at hω; simpa [omega] using hω
  have hsum : joinV u (0, σ) + joinV u' (0, σ') = joinV (u + u') (0, σ + σ') := by
    rw [joinV_add]; congr 1
  have hpne := (mem_Xstd_join.1 hp)
  have hqne := (mem_Xstd_join.1 hq)
  have hsne : ¬ (u + u' = 0 ∧ σ + σ' = 0) := by rw [← mem_Xstd_join, ← hsum]; exact hpq'
  have hne : ¬ (u = u' ∧ σ = σ') := by
    rintro ⟨rfl, rfl⟩; exact hline.ne_ab rfl
  have mk : ∀ x : V k, x ≠ 0 → x ∈ Wpts k := fun x hx => Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩
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
      · rw [trieq]; simp [EstdE, Estd, baseOf]
    · have hσσ : σ' ≠ σ + σ' := by
        intro h; apply hσ; have := congrArg (· + σ') h; simpa [add_assoc, add_self_fun] using this.symm
      set v : Bpt k := ⟨u', mk u' hu'0⟩
      refine ⟨{(some v, σ'), (some v, σ + σ'), (none, σ' + (σ + σ'))}, ?_, ?_⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.2
          ⟨(v, σ', σ + σ'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hσσ⟩, rfl⟩))
      · rw [trieq]
        have e : σ' + (σ + σ') = σ := by
          rw [add_comm σ σ', ← add_assoc, add_self_fun, zero_add]
        simp only [Finset.map_insert, Finset.map_singleton, EstdE, Function.Embedding.coeFn_mk, Estd,
          baseOf, e, zero_add]
        rw [fs3_231]
  · by_cases hu'0 : u' = 0
    · subst hu'0
      have hσ' : σ' ≠ 0 := fun h => hqne ⟨rfl, h⟩
      have hσσ : σ ≠ σ + σ' := by
        intro h; apply hσ'; have := congrArg (σ + ·) h; simpa [← add_assoc, add_self_fun] using this.symm
      set v : Bpt k := ⟨u, mk u hu0⟩
      refine ⟨{(some v, σ), (some v, σ + σ'), (none, σ + (σ + σ'))}, ?_, ?_⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.2
          ⟨(v, σ, σ + σ'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hσσ⟩, rfl⟩))
      · rw [trieq]
        have e : σ + (σ + σ') = σ' := by rw [← add_assoc, add_self_fun, zero_add]
        simp only [Finset.map_insert, Finset.map_singleton, EstdE, Function.Embedding.coeFn_mk, Estd,
          baseOf, e, add_zero]
        rw [fs3_132]
    · by_cases huu : u + u' = 0
      · have hueq : u = u' := by
          have := congrArg (u + ·) huu; simpa [← add_assoc, add_self_V] using this.symm
        subst hueq
        have hσσ : σ ≠ σ' := fun h => hne ⟨rfl, h⟩
        set v : Bpt k := ⟨u, mk u hu0⟩
        refine ⟨{(some v, σ), (some v, σ'), (none, σ + σ')}, ?_, ?_⟩
        · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.2
            ⟨(v, σ, σ'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hσσ⟩, rfl⟩))
        · rw [trieq, huu]
          simp [EstdE, Estd, baseOf, v]
      · -- a lift of the base line {u, u', u + u'}
        set a' : Bpt k := ⟨u, mk u hu0⟩
        set b' : Bpt k := ⟨u', mk u' hu'0⟩
        set c' : Bpt k := ⟨u + u', mk _ huu⟩
        have hab : (u, u') ∈ OP (Wpts k) := mem_OP.2 ⟨mk u hu0, mk u' hu'0, hω', mk _ huu⟩
        have hbl := isLine_of_OP (zero_not_mem_W k) hab
        set ℓ : Finset (Bpt k) := {a', b', c'}
        have hℓ : ℓ ∈ (Gk k).lines := by
          show ℓ ∈ linesSub (Wpts k) (zero_not_mem_W k)
          refine Finset.mem_image.2 ⟨tri (u, u'), Finset.mem_image_of_mem _ hab, ?_⟩
          ext x; simp [tri, ℓ, a', b', c', Subtype.ext_iff]
        set τ : Bpt k → (Fin t → F) := fun x =>
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
            Finset.map_singleton, EstdE, Function.Embedding.coeFn_mk, Estd, baseOf, hτa, hτb, hτc]
          rfl

theorem lines_Xstd :
    (configX (Xstd k t) (zero_not_mem_Xstd k t)).lines =
      (cone t (Gk k)).lines.image (fun L => L.map EstdE) := by
  ext m
  constructor
  · intro hm
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨L, hL, he⟩ := OP_Xstd_cone hpq
    exact Finset.mem_image.2 ⟨L, hL, he⟩
  · intro hm
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨pq, hpq, he, -⟩ := cone_line_image hL
    rw [he]; exact Finset.mem_image_of_mem _ hpq

theorem cone_lines_mem :
    ∀ L ∈ (cone t (Gk k)).lines, L.map EstdE ∈ (configX (Xstd k t) (zero_not_mem_Xstd k t)).lines :=
  fun L hL => by rw [lines_Xstd]; exact Finset.mem_image_of_mem _ hL

/-- the standard section has the degree of the cone -/
theorem deg_Xstd_cone :
    (configX (Xstd k t) (zero_not_mem_Xstd k t)).deg = (cone t (Gk k)).deg := by
  rw [← deg_comap _ EstdE _ cone_lines_mem lines_Xstd]
  refine deg_congr _ _ rfl fun L hL => ?_
  obtain ⟨pq, hpq, he, hs⟩ := cone_line_image hL
  show (configX (Xstd k t) (zero_not_mem_Xstd k t)).sign (L.map EstdE) = _
  rw [he, configX_sign (zero_not_mem_Xstd k t) hpq, hs]

theorem deg_cone_Gk : (cone t (Gk k)).deg = 4 ^ t * (W k).deg := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : (W 0).deg = 0 := by
      have := (W 0).deg_le_half
      have hL : (W 0).lines.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro l hl
        obtain ⟨a, b, h, -⟩ := mem_W_lines.1 hl
        exact h.nz_a (Subsingleton.elim _ _)
      omega
    have := cone_deg_le t (Gk 0)
    rw [Gk_deg, h0] at this
    rw [h0]
    omega
  · rw [← Gk_deg]
    refine cone_degree_pauli t (Gk k) hk (fun x => x.1) ?_ ?_
    · intro ℓ hℓ
      have hW : ℓ.map (Function.Embedding.subtype _) ∈ (W k).lines := by
        unfold W; rw [lines_eq_linesSub (Wpts k) (zero_not_mem_W k)]; exact Finset.mem_image_of_mem _ hℓ
      obtain ⟨a, b, h, he⟩ := mem_W_lines.1 hW
      have : ∑ p ∈ ℓ, p.1 = ∑ x ∈ ℓ.map (Function.Embedding.subtype _), x := by
        rw [Finset.sum_map]; rfl
      rw [this, he]
      simp only [tri]
      rw [Finset.sum_insert (by simp [h.ne_ab, h.ne_ac]), Finset.sum_insert (by simp [h.ne_bc]),
        Finset.sum_singleton, ← add_assoc, add_self_V]
    · intro ℓ _ a _ b _ hab
      exact ⟨fun h => hab (Subtype.ext h), (Finset.mem_erase.1 a.2).1, (Finset.mem_erase.1 b.2).1⟩

/-- **CONE-2, standard form.** deg W(V k ⊗ ⟨Z⟩^t) = 4^t deg W(2k−1,2). -/
theorem std_section_degree :
    (configX (Xstd k t) (zero_not_mem_Xstd k t)).deg = 4 ^ t * (W k).deg := by
  rw [deg_Xstd_cone, deg_cone_Gk]

end Std

/-! ### Part 2: the symplectic normal form of a subspace (by induction, no Witt theorem) -/

section Normal

variable {N : ℕ}

theorem omega_sum_left' {β : Type} (s : Finset β) (f : β → V N) (q : V N) :
    omega (∑ i ∈ s, f i) q = ∑ i ∈ s, omega (f i) q := by
  rw [omega_comm, omega_sum_right]; exact Finset.sum_congr rfl fun i _ => omega_comm _ _

/-- the combination Σ_i (c_i e_i + d_i f_i) + Σ_j g_j r_j -/
def comb {k t : ℕ} (e f : Fin k → V N) (r : Fin t → V N) (c d : Fin k → F) (g : Fin t → F) : V N :=
  ∑ i, (c i • e i + d i • f i) + ∑ j, g j • r j

theorem comb_add {k t : ℕ} (e f : Fin k → V N) (r : Fin t → V N) (c d c' d' : Fin k → F)
    (g g' : Fin t → F) :
    comb e f r c d g + comb e f r c' d' g' = comb e f r (c + c') (d + d') (g + g') := by
  unfold comb
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem comb_smul {k t : ℕ} (e f : Fin k → V N) (r : Fin t → V N) (a : F) (c d : Fin k → F)
    (g : Fin t → F) : a • comb e f r c d g = comb e f r (a • c) (a • d) (a • g) := by
  unfold comb
  simp only [smul_add, Finset.smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]

/-- a symplectic basis adapted to the radical -/
structure SympData (U : Submodule F (V N)) (k t : ℕ) where
  e : Fin k → V N
  f : Fin k → V N
  r : Fin t → V N
  he : ∀ i, e i ∈ U
  hf : ∀ i, f i ∈ U
  hr : ∀ j, r j ∈ U
  ee : ∀ i j, omega (e i) (e j) = 0
  ff : ∀ i j, omega (f i) (f j) = 0
  ef : ∀ i j, omega (e i) (f j) = if i = j then 1 else 0
  rad : ∀ j, ∀ u ∈ U, omega (r j) u = 0
  indep : ∀ c d g, comb e f r c d g = 0 → c = 0 ∧ d = 0 ∧ g = 0
  span : ∀ u ∈ U, ∃ c d g, comb e f r c d g = u

theorem comb_mem {U : Submodule F (V N)} {k t : ℕ} (D : SympData U k t) (c d : Fin k → F)
    (g : Fin t → F) : comb D.e D.f D.r c d g ∈ U := by
  unfold comb
  refine U.add_mem (U.sum_mem fun i _ => U.add_mem (U.smul_mem _ (D.he i)) (U.smul_mem _ (D.hf i)))
    (U.sum_mem fun j _ => U.smul_mem _ (D.hr j))

/-- totally isotropic subspaces: k = 0, the radical is everything -/
noncomputable def isoData (U : Submodule F (V N)) (hU : ∀ a ∈ U, ∀ b ∈ U, omega a b = 0) :
    SympData U 0 (finrank F U) where
  e := Fin.elim0
  f := Fin.elim0
  r := fun j => ((Module.finBasis F U) j : V N)
  he := fun i => i.elim0
  hf := fun i => i.elim0
  hr := fun j => ((Module.finBasis F U) j).2
  ee := fun i => i.elim0
  ff := fun i => i.elim0
  ef := fun i => i.elim0
  rad := fun j u hu => hU _ ((Module.finBasis F U) j).2 u hu
  indep := by
    intro c d g h
    refine ⟨funext fun i => i.elim0, funext fun i => i.elim0, ?_⟩
    simp only [comb, Finset.univ_eq_empty, Finset.sum_empty, zero_add] at h
    have h' : ∑ j, g j • (Module.finBasis F U) j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa using h
    exact funext ((Fintype.linearIndependent_iff.1 (Module.finBasis F U).linearIndependent) g h')
  span := by
    intro u hu
    refine ⟨Fin.elim0, Fin.elim0, fun j => (Module.finBasis F U).repr ⟨u, hu⟩ j, ?_⟩
    simp only [comb, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    have := congrArg Subtype.val ((Module.finBasis F U).sum_repr ⟨u, hu⟩)
    rw [Submodule.coe_sum] at this
    simpa using this

theorem sympData_iso (U : Submodule F (V N)) (hU : ∀ a ∈ U, ∀ b ∈ U, omega a b = 0) :
    Nonempty (SympData U 0 (finrank F U)) := ⟨isoData U hU⟩

/-- the orthogonal complement of a hyperbolic pair inside U -/
def perpPair (U : Submodule F (V N)) (a b : V N) : Submodule F (V N) :=
  U ⊓ (LinearMap.ker (omegaB N a) ⊓ LinearMap.ker (omegaB N b))

theorem mem_perpPair {U : Submodule F (V N)} {a b u : V N} :
    u ∈ perpPair U a b ↔ u ∈ U ∧ omega a u = 0 ∧ omega b u = 0 := by
  simp [perpPair, Submodule.mem_inf, LinearMap.mem_ker]

theorem F_eq_one_of_ne {x : F} (h : x ≠ 0) : x = 1 := by revert x h; decide

/-- the projection u ↦ u + ω(u,b)a + ω(u,a)b onto the complement of ⟨a, b⟩ -/
theorem proj_mem {U : Submodule F (V N)} {a b u : V N} (ha : a ∈ U) (hb : b ∈ U) (hu : u ∈ U)
    (hab : omega a b = 1) : u + omega u b • a + omega u a • b ∈ perpPair U a b := by
  have hba : omega b a = 1 := by rw [omega_comm]; exact hab
  rw [mem_perpPair]
  refine ⟨U.add_mem (U.add_mem hu (U.smul_mem _ ha)) (U.smul_mem _ hb), ?_, ?_⟩
  · rw [omega_add_right, omega_add_right, omega_smul_right, omega_smul_right, omega_self, hab,
      omega_comm a u]
    have : ∀ x y : F, x + y * 0 + x * 1 = 0 := by decide
    exact this _ _
  · rw [omega_add_right, omega_add_right, omega_smul_right, omega_smul_right, omega_self, hba,
      omega_comm b u]
    have : ∀ x y : F, x + x * 1 + y * 0 = 0 := by decide
    exact this _ _

theorem proj_add_eq (a b u : V N) : u + omega u b • a + omega u a • b + omega u b • a + omega u a • b = u := by
  have h1 : omega u b • a + omega u b • a = 0 := by rw [← add_smul, add_self_F, zero_smul]
  have h2 : omega u a • b + omega u a • b = 0 := by rw [← add_smul, add_self_F, zero_smul]
  calc u + omega u b • a + omega u a • b + omega u b • a + omega u a • b
      = u + (omega u b • a + omega u b • a) + (omega u a • b + omega u a • b) := by abel
    _ = u := by rw [h1, h2, add_zero, add_zero]

theorem sum_cons_succ {k : ℕ} (x : V N) (v : Fin k → V N) (c : Fin (k + 1) → F) :
    ∑ i, c i • (Fin.cons x v : Fin (k + 1) → V N) i = c 0 • x + ∑ i, c i.succ • v i := by
  rw [Fin.sum_univ_succ]; simp

/-- split off one hyperbolic pair -/
theorem sympData_step (U : Submodule F (V N)) (a b : V N) (ha : a ∈ U) (hb : b ∈ U)
    (hab : omega a b = 1) {k t : ℕ} (D : SympData (perpPair U a b) k t) :
    Nonempty (SympData U (k + 1) t) := by
  have hba : omega b a = 1 := by rw [omega_comm]; exact hab
  have mU : ∀ {u}, u ∈ perpPair U a b → u ∈ U := fun h => (mem_perpPair.1 h).1
  have mA : ∀ {u}, u ∈ perpPair U a b → omega a u = 0 := fun h => (mem_perpPair.1 h).2.1
  have mB : ∀ {u}, u ∈ perpPair U a b → omega b u = 0 := fun h => (mem_perpPair.1 h).2.2
  have mA' : ∀ {u}, u ∈ perpPair U a b → omega u a = 0 := fun h => by rw [omega_comm]; exact mA h
  have mB' : ∀ {u}, u ∈ perpPair U a b → omega u b = 0 := fun h => by rw [omega_comm]; exact mB h
  -- the combination splits
  have hsplit : ∀ (c d : Fin (k + 1) → F) (g : Fin t → F),
      comb (Fin.cons a D.e) (Fin.cons b D.f) D.r c d g =
        c 0 • a + d 0 • b + comb D.e D.f D.r (fun i => c i.succ) (fun i => d i.succ) g := by
    intro c d g
    unfold comb
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    abel
  refine ⟨⟨Fin.cons a D.e, Fin.cons b D.f, D.r, ?_, ?_, fun j => mU (D.hr j), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i; refine Fin.cases ?_ (fun i => ?_) i
    · exact ha
    · exact mU (D.he i)
  · intro i; refine Fin.cases ?_ (fun i => ?_) i
    · exact hb
    · exact mU (D.hf i)
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact omega_self a
    · exact mA (D.he j)
    · exact mA' (D.he i)
    · exact D.ee i j
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact omega_self b
    · exact mB (D.hf j)
    · exact mB' (D.hf i)
    · exact D.ff i j
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hab
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [if_neg (Fin.succ_ne_zero j).symm]; exact mA (D.hf j)
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [if_neg (Fin.succ_ne_zero i)]; exact mB' (D.he i)
    · simp only [Fin.cons_succ, Fin.succ_inj]; exact D.ef i j
  · intro j u hu
    have hp := proj_mem ha hb hu hab
    have h1 := D.rad j _ hp
    rw [← proj_add_eq a b u, omega_add_right, omega_add_right, h1, omega_smul_right,
      omega_smul_right, mA' (D.hr j), mB' (D.hr j)]
    simp
  · intro c d g h
    rw [hsplit] at h
    have hR := comb_mem D (fun i => c i.succ) (fun i => d i.succ) g
    have hc0 : c 0 = 0 := by
      have := congrArg (omega b) h
      rw [omega_add_right, omega_add_right, omega_smul_right, omega_smul_right, hba, omega_self,
        mB hR] at this
      simpa [omega] using this
    have hd0 : d 0 = 0 := by
      have := congrArg (omega a) h
      rw [omega_add_right, omega_add_right, omega_smul_right, omega_smul_right, hab, omega_self,
        mA hR] at this
      simpa [omega] using this
    rw [hc0, hd0, zero_smul, zero_smul, zero_add, zero_add] at h
    obtain ⟨h1, h2, h3⟩ := D.indep _ _ _ h
    refine ⟨funext fun i => Fin.cases hc0 (fun i => congrFun h1 i) i,
      funext fun i => Fin.cases hd0 (fun i => congrFun h2 i) i, h3⟩
  · intro u hu
    obtain ⟨c, d, g, hcomb⟩ := D.span _ (proj_mem ha hb hu hab)
    refine ⟨Fin.cons (omega u b) c, Fin.cons (omega u a) d, g, ?_⟩
    rw [hsplit]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have e : (fun i => (Fin.cons (omega u b) c : Fin (k + 1) → F) i.succ) = c := funext fun i => rfl
    have e' : (fun i => (Fin.cons (omega u a) d : Fin (k + 1) → F) i.succ) = d := funext fun i => rfl
    first | rw [e, e', hcomb] | rw [hcomb]
    calc omega u b • a + omega u a • b + (u + omega u b • a + omega u a • b)
        = u + (omega u b • a + omega u b • a) + (omega u a • b + omega u a • b) := by abel
      _ = u := by rw [add_self_V, add_self_V, add_zero, add_zero]

/-- **normal form.** every subspace has a symplectic basis adapted to its radical -/
theorem exists_sympData_aux : ∀ (n : ℕ) (U : Submodule F (V N)), finrank F U = n →
    ∃ k t, Nonempty (SympData U k t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hn
    by_cases hiso : ∀ a ∈ U, ∀ b ∈ U, omega a b = 0
    · exact ⟨0, _, sympData_iso U hiso⟩
    · push Not at hiso
      obtain ⟨a, ha, b, hb, hab⟩ := hiso
      have hab1 := F_eq_one_of_ne hab
      have hlt : finrank F (perpPair U a b) < n := by
        rw [← hn]
        apply Submodule.finrank_lt_finrank_of_lt
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        have : a ∈ perpPair U a b := by rw [heq]; exact ha
        have h2 := (mem_perpPair.1 this).2.2
        rw [omega_comm, hab1] at h2
        exact one_ne_zero h2
      obtain ⟨k, t, ⟨D⟩⟩ := ih _ hlt _ rfl
      exact ⟨k + 1, t, sympData_step U a b ha hb hab1 D⟩

theorem exists_sympData (U : Submodule F (V N)) : ∃ k t, Nonempty (SympData U k t) :=
  exists_sympData_aux _ U rfl

variable {U : Submodule F (V N)} {k t : ℕ}

/-- ω on combinations -/
theorem omega_comb (D : SympData U k t) (c d c' d' : Fin k → F) (g g' : Fin t → F) :
    omega (comb D.e D.f D.r c d g) (comb D.e D.f D.r c' d' g') = ∑ i, (c i * d' i + d i * c' i) := by
  have hr : ∀ x ∈ U, ∀ j, omega x (D.r j) = 0 := fun x hx j => by rw [omega_comm]; exact D.rad j x hx
  have hrx : ∀ (x : V N), x ∈ U → omega x (∑ j, g' j • D.r j) = 0 := by
    intro x hx; rw [omega_sum_right]
    exact Finset.sum_eq_zero fun j _ => by rw [omega_smul_right, hr x hx j, mul_zero]
  have hrl : ∀ (x : V N), x ∈ U → omega (∑ j, g j • D.r j) x = 0 := by
    intro x hx; rw [omega_comm, omega_sum_right]
    exact Finset.sum_eq_zero fun j _ => by rw [omega_smul_right, hr x hx j, mul_zero]
  have hmemS : ∀ (c d : Fin k → F), ∑ i, (c i • D.e i + d i • D.f i) ∈ U := fun c d =>
    U.sum_mem fun i _ => U.add_mem (U.smul_mem _ (D.he i)) (U.smul_mem _ (D.hf i))
  have hmemR : ∀ g : Fin t → F, ∑ j, g j • D.r j ∈ U := fun g => U.sum_mem fun j _ => U.smul_mem _ (D.hr j)
  unfold comb
  rw [omega_add_left, omega_add_right, omega_add_right, hrx _ (hmemS c d), hrl _ (hmemS c' d'),
    hrl _ (hmemR g'), add_zero, add_zero, add_zero]
  rw [omega_sum_left']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [omega_add_left, omega_sum_right, omega_sum_right, ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i]
  · rw [omega_add_right, omega_add_right, omega_smul_left, omega_smul_left, omega_smul_left,
      omega_smul_left, omega_smul_right, omega_smul_right, omega_smul_right, omega_smul_right,
      D.ee, D.ff, D.ef, omega_comm (D.f i), D.ef, if_pos rfl]
    ring
  · intro j _ hji
    rw [omega_add_right, omega_add_right, omega_smul_left, omega_smul_left, omega_smul_left,
      omega_smul_left, omega_smul_right, omega_smul_right, omega_smul_right, omega_smul_right,
      D.ee, D.ff, D.ef, omega_comm (D.f i), D.ef, if_neg (Ne.symm hji), if_neg hji]
    ring
  · simp

/-- the coordinates of a label of `V (k + t)` -/
def cX (p : V (k + t)) : Fin k → F := fun i => p.1 (Fin.castAdd t i)
def cZ (p : V (k + t)) : Fin k → F := fun i => p.2 (Fin.castAdd t i)
def cR (p : V (k + t)) : Fin t → F := fun j => p.2 (Fin.natAdd k j)

/-- ψ : X_i ↦ e_i, Z_i ↦ f_i, Z_{k+j} ↦ r_j (X on the last t qubits ↦ 0) -/
def psiMap (D : SympData U k t) : V (k + t) →ₗ[F] V N where
  toFun p := comb D.e D.f D.r (cX p) (cZ p) (cR p)
  map_add' p q := by rw [comb_add]; rfl
  map_smul' a p := by simp only [RingHom.id_apply]; rw [comb_smul]; rfl

theorem psiMap_mem (D : SympData U k t) (p : V (k + t)) : psiMap D p ∈ U := comb_mem D _ _ _

theorem omega_split (p q : V (k + t)) :
    omega p q = ∑ i, (cX p i * cZ q i + cZ p i * cX q i) +
      ∑ j, (p.1 (Fin.natAdd k j) * q.2 (Fin.natAdd k j) + p.2 (Fin.natAdd k j) * q.1 (Fin.natAdd k j)) := by
  unfold omega; rw [Fin.sum_univ_add]; rfl

/-- ψ preserves ω on the standard subspace -/
theorem psiMap_omega (D : SympData U k t) {p q : V (k + t)} (hp : p ∈ Sstd k t) (hq : q ∈ Sstd k t) :
    omega (psiMap D p) (psiMap D q) = omega p q := by
  show omega (comb D.e D.f D.r _ _ _) (comb D.e D.f D.r _ _ _) = _
  rw [omega_comb, omega_split]
  have : ∑ j : Fin t, (p.1 (Fin.natAdd k j) * q.2 (Fin.natAdd k j) +
      p.2 (Fin.natAdd k j) * q.1 (Fin.natAdd k j)) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hp j, hq j]; ring
  rw [this, add_zero]

theorem std_ext {p q : V (k + t)} (hp : p ∈ Sstd k t) (hq : q ∈ Sstd k t) (h1 : cX p = cX q)
    (h2 : cZ p = cZ q) (h3 : cR p = cR q) : p = q := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun i => congrFun h1 i) (fun j => ?_) i
    rw [hp j, hq j]
  · refine Fin.addCases (fun i => congrFun h2 i) (fun j => congrFun h3 j) i

theorem psiMap_injOn (D : SympData U k t) : Set.InjOn (psiMap D) (Sstd k t) := by
  intro p hp q hq h
  have h' : comb D.e D.f D.r (cX p + cX q) (cZ p + cZ q) (cR p + cR q) = 0 := by
    rw [← comb_add]; change psiMap D p + psiMap D q = 0; rw [h, add_self_V]
  obtain ⟨h1, h2, h3⟩ := D.indep _ _ _ h'
  have sub : ∀ {m : ℕ} (x y : Fin m → F), x + y = 0 → x = y := fun x y h => by
    funext i; have := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at this
    have key : ∀ a b : F, a + b = 0 → a = b := by decide
    exact key _ _ this
  exact std_ext hp hq (sub _ _ h1) (sub _ _ h2) (sub _ _ h3)

/-- the standard label with given coordinates -/
def stdOf (c d : Fin k → F) (g : Fin t → F) : V (k + t) := (Fin.append c 0, Fin.append d g)

theorem stdOf_mem (c d : Fin k → F) (g : Fin t → F) : stdOf c d g ∈ Sstd k t := fun j => by
  simp [stdOf, Fin.append_right]

theorem psiMap_stdOf (D : SympData U k t) (c d : Fin k → F) (g : Fin t → F) :
    psiMap D (stdOf c d g) = comb D.e D.f D.r c d g := by
  show comb D.e D.f D.r (cX _) (cZ _) (cR _) = _
  congr 1 <;> funext i <;> simp [cX, cZ, cR, stdOf, Fin.append_left, Fin.append_right]

theorem psiMap_surj (D : SympData U k t) {u : V N} (hu : u ∈ U) :
    ∃ p ∈ Sstd k t, psiMap D p = u := by
  obtain ⟨c, d, g, h⟩ := D.span u hu
  exact ⟨stdOf c d g, stdOf_mem c d g, by rw [psiMap_stdOf, h]⟩

/-! ### dimension and radical -/

theorem finrank_of_sympData (D : SympData U k t) : finrank F U = 2 * k + t := by
  let φ : ((Fin k → F) × (Fin k → F) × (Fin t → F)) →ₗ[F] U :=
    { toFun := fun x => ⟨comb D.e D.f D.r x.1 x.2.1 x.2.2, comb_mem D _ _ _⟩
      map_add' := fun x y => Subtype.ext (by simp only [Submodule.coe_add]; rw [comb_add]; rfl)
      map_smul' := fun a x => Subtype.ext (by
        simp only [Submodule.coe_smul, RingHom.id_apply]; rw [comb_smul]; rfl) }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨h1, h2, h3⟩ := D.indep _ _ _ (congrArg Subtype.val hx)
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    obtain ⟨c, d, g, h⟩ := D.span u hu
    exact ⟨(c, d, g), Subtype.ext h⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp only [Module.finrank_prod, Module.finrank_fin_fun]
  ring

/-- the radical U ∩ U^⊥ -/
def radical (U : Submodule F (V N)) : Submodule F (V N) := U ⊓ (omegaB N).orthogonal U

theorem mem_radical {u : V N} : u ∈ radical U ↔ u ∈ U ∧ ∀ v ∈ U, omega v u = 0 := by
  simp only [radical, Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff,
    LinearMap.BilinForm.IsOrtho, omegaB_apply]

theorem finrank_radical_of_sympData (D : SympData U k t) : finrank F (radical U) = t := by
  have hmem : ∀ g : Fin t → F, comb D.e D.f D.r 0 0 g ∈ radical U := by
    intro g
    refine mem_radical.2 ⟨comb_mem D _ _ _, fun v hv => ?_⟩
    obtain ⟨c, d, g', rfl⟩ := D.span v hv
    rw [omega_comb]; simp
  let φ : (Fin t → F) →ₗ[F] radical U :=
    { toFun := fun g => ⟨comb D.e D.f D.r 0 0 g, hmem g⟩
      map_add' := fun x y => Subtype.ext (by
        simp only [Submodule.coe_add]; rw [comb_add]; simp)
      map_smul' := fun a x => Subtype.ext (by
        simp only [Submodule.coe_smul, RingHom.id_apply]; rw [comb_smul]; simp) }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact (D.indep _ _ _ (congrArg Subtype.val hx)).2.2
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    obtain ⟨huU, horth⟩ := mem_radical.1 hu
    obtain ⟨c, d, g, h⟩ := D.span u huU
    have hc : c = 0 := by
      funext i
      have := horth (D.f i) (D.hf i)
      have hf : D.f i = comb D.e D.f D.r 0 (Pi.single i 1) 0 := by
        unfold comb; simp [Pi.single_apply, Finset.sum_ite_eq']
      rw [← h, hf, omega_comb] at this
      simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
    have hd : d = 0 := by
      funext i
      have := horth (D.e i) (D.he i)
      have he : D.e i = comb D.e D.f D.r (Pi.single i 1) 0 0 := by
        unfold comb; simp [Pi.single_apply, Finset.sum_ite_eq']
      rw [← h, he, omega_comb] at this
      simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
    refine ⟨g, Subtype.ext ?_⟩
    show comb D.e D.f D.r 0 0 g = u
    rw [← h, hc, hd]
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fin_fun]

/-! ### CONE-2 -/

open Classical in
/-- the non-zero points of a subspace -/
noncomputable def secX (U : Submodule F (V N)) : Finset (V N) :=
  Finset.univ.filter (fun p => p ≠ 0 ∧ p ∈ U)

theorem zero_not_mem_secX (U : Submodule F (V N)) : (0 : V N) ∉ secX U := by simp [secX]

theorem mem_secX {U : Submodule F (V N)} {p : V N} : p ∈ secX U ↔ p ≠ 0 ∧ p ∈ U := by
  simp [secX]

theorem secX_eq_image (D : SympData U k t) : secX U = (Xstd k t).image (psiMap D) := by
  ext u
  rw [mem_secX, Finset.mem_image]
  constructor
  · rintro ⟨hu0, hu⟩
    obtain ⟨p, hp, rfl⟩ := psiMap_surj D hu
    refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => hu0 (by rw [h, map_zero]), hp⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hpS := Xstd_sub k t hp
    refine ⟨fun h => (Finset.mem_filter.1 hp).2.1 ?_, psiMap_mem D p⟩
    exact psiMap_injOn D hpS (Sstd k t).zero_mem (by rw [h, map_zero])

theorem configX_deg_congr {X Y : Finset (V N)} (h : X = Y) (hX : (0 : V N) ∉ X) (hY : (0 : V N) ∉ Y) :
    (configX X hX).deg = (configX Y hY).deg := by subst h; rfl

theorem section_deg_of_sympData (D : SympData U k t) :
    (configX (secX U) (zero_not_mem_secX U)).deg = 4 ^ t * (W k).deg := by
  have hspan : Submodule.span F (Xstd k t : Set (V (k + t))) ≤ Sstd k t :=
    Submodule.span_le.2 (Xstd_sub k t)
  have hinj : Set.InjOn (psiMap D) (Submodule.span F (Xstd k t : Set (V (k + t)))) :=
    (psiMap_injOn D).mono hspan
  have hω : ∀ a ∈ Xstd k t, ∀ b ∈ Xstd k t, omega (psiMap D a) (psiMap D b) = omega a b :=
    fun a ha b hb => psiMap_omega D (Xstd_sub k t ha) (Xstd_sub k t hb)
  have h0' := zero_not_mem_image (Xstd k t) (zero_not_mem_Xstd k t) (psiMap D) hinj
  rw [configX_deg_congr (secX_eq_image D) _ h0',
    deg_configX_map (Xstd k t) (zero_not_mem_Xstd k t) (psiMap D) hω hinj h0', std_section_degree]

/-- **CONE-2.** For a subspace U ⊆ F^{2N} whose radical U ∩ U^⊥ has dimension t and with
dim U = 2k + t, the induced configuration on U ∖ {0} has degree 4^t · deg W(2k−1,2). -/
theorem W_section_degree (U : Submodule F (V N)) (k t : ℕ) (hk : finrank F U = 2 * k + t)
    (ht : finrank F (radical U) = t) :
    (configX (secX U) (zero_not_mem_secX U)).deg = 4 ^ t * (W k).deg := by
  obtain ⟨k', t', ⟨D⟩⟩ := exists_sympData U
  have ht' := finrank_radical_of_sympData D
  have hk' := finrank_of_sympData D
  have e1 : t' = t := by rw [← ht, ht']
  subst e1
  have e2 : k' = k := by omega
  subst e2
  exact section_deg_of_sympData D

/-- **CONE-2 (existence form).** every subspace section of W is a cone over some W(2k−1,2) -/
theorem W_section_degree' (U : Submodule F (V N)) :
    ∃ k t, finrank F U = 2 * k + t ∧ finrank F (radical U) = t ∧
      (configX (secX U) (zero_not_mem_secX U)).deg = 4 ^ t * (W k).deg := by
  obtain ⟨k, t, ⟨D⟩⟩ := exists_sympData U
  exact ⟨k, t, finrank_of_sympData D, finrank_radical_of_sympData D, section_deg_of_sympData D⟩

end Normal

end PauliCtx.Spectral
