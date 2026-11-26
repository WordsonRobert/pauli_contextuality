/-
Transfer.lean — blueprint TR-1 (group version), TR-5 (extremality, monotonicity), TQ-2.

  * `Config.transfer` (TR-1): Γ ≤ Perm(P) line-transitive, every translate of S has degree ≥ d
      ⟹ |L(G)|·d ≤ |L(S)|·deg G.
  * `Sp N` : the symplectic permutations of F^{2N} (additive and ω-preserving), as a subgroup.
  * `Sp_trans_lines` : Sp(2N,2) is transitive on the lines of W(2N−1,2). The proof uses explicit
      transvections x ↦ x + ω(x,w)w (no Witt theorem).
  * `rho_max` (TR-5.1) : every N-qubit configuration S ⊆ W(2N−1,2) has deg S/|L(S)| ≤ ρ_N.
  * `rho_mono` (TR-5.2) : ρ_N ≤ ρ_{N+1}.
  * `transfer_rigid`, `rho_rigid` (TR-2) : equality forces tightness on every translate.
  * `three_qubit_bound` (TQ-2) : every configuration on ≤ 3 qubits has deg S ≤ |L(S)|/5.
-/
import PauliContextuality.NegLines
import PauliContextuality.Invariance
import PauliContextuality.Cover
import PauliContextuality.SpectralExact

open Matrix

namespace PauliCtx

namespace Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-- the image of a family of lines under a permutation of the points -/
def imgL (g : Equiv.Perm α) (L : Finset (Finset α)) : Finset (Finset α) :=
  L.image (fun m => m.map g.toEmbedding)

theorem mem_imgL {g : Equiv.Perm α} {L : Finset (Finset α)} {l : Finset α} :
    l ∈ imgL g L ↔ l.map g.symm.toEmbedding ∈ L := by
  unfold imgL
  constructor
  · intro h
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 h
    rwa [map_symm_map]
  · intro h
    refine Finset.mem_image.2 ⟨_, h, ?_⟩
    have := map_symm_map g.symm l
    rwa [Equiv.symm_symm] at this

theorem card_imgL (g : Equiv.Perm α) (L : Finset (Finset α)) : (imgL g L).card = L.card :=
  Finset.card_image_of_injective _ (Finset.map_injective _)

theorem map_mul_symm (h g : Equiv.Perm α) (l : Finset α) :
    l.map (h * g).symm.toEmbedding = (l.map h.symm.toEmbedding).map g.symm.toEmbedding := by
  ext x; simp [Finset.mem_map_equiv, Equiv.Perm.mul_apply]

/-- **TR-1 (transfer, group version).** If a group `H` of permutations maps lines to lines and is
transitive on the lines of `C`, and every translate of the sub-family `L` meets every violated set
in at least `d` lines, then `|L(C)|·d ≤ |L|·deg C`, i.e. `d/|L| ≤ deg C/|L(C)|`. -/
theorem transfer (C : Config α) (H : Subgroup (Equiv.Perm α)) [Fintype H]
    (L : Finset (Finset α)) (hL : L ⊆ C.lines)
    (hmap : ∀ g ∈ H, ∀ l ∈ C.lines, l.map g.toEmbedding ∈ C.lines)
    (htrans : ∀ l ∈ C.lines, ∀ l' ∈ C.lines, ∃ g ∈ H, l.map g.toEmbedding = l')
    (d : ℕ) (hdeg : ∀ g ∈ H, ∀ s : α → F, d ≤ (C.violated s ∩ imgL g L).card) :
    C.lines.card * d ≤ L.card * C.deg := by
  rcases L.eq_empty_or_nonempty with h0 | ⟨m, hm⟩
  · have := hdeg 1 H.one_mem (fun _ => 0)
    simp [h0, imgL] at this
    simp [this]
  set fam : H → Finset (Finset α) := fun g => imgL g L with hfam
  have hsub : ∀ g : H, fam g ⊆ C.lines := by
    intro g l hl
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hl
    exact hmap g g.2 m' (hL hm')
  set cnt : Finset α → ℕ := fun l => (Finset.univ.filter (fun g : H => l ∈ fam g)).card with hcnt
  have huni : ∀ l ∈ C.lines, cnt l = cnt m := by
    intro l hl
    obtain ⟨h, hh, hml⟩ := htrans m (hL hm) l hl
    have key : ∀ g : Equiv.Perm α, l ∈ imgL (h * g) L ↔ m ∈ imgL g L := by
      intro g
      rw [mem_imgL, mem_imgL, map_mul_symm, ← hml, map_symm_map]
    symm
    refine Finset.card_nbij' (fun g => ⟨h * g, H.mul_mem hh g.2⟩)
      (fun g => ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) g.2⟩) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
      exact (key g).2 hg
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
      have := (key (h⁻¹ * g)).1
      rw [mul_inv_cancel_left] at this
      exact this hg
    · intro g _; apply Subtype.ext; simp
    · intro g _; apply Subtype.ext; simp
  have hc : 0 < cnt m := by
    apply Finset.card_pos.2
    refine ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    show m ∈ imgL 1 L
    rw [mem_imgL]
    have : m.map (1 : Equiv.Perm α).symm.toEmbedding = m := by ext x; simp
    rwa [this]
  have hcov : ∀ l ∈ C.lines, (Finset.univ.filter (fun g : H => l ∈ fam g)).card = cnt m := huni
  have hdeg' : ∀ (g : H) (s : α → F), d ≤ (C.violated s ∩ fam g).card := fun g s => hdeg g g.2 s
  obtain ⟨s, hs⟩ := C.exists_opt
  have hu := uniform_cover C fam hsub (cnt m) d hc hcov hdeg' s
  rw [hs] at hu
  -- double counting: |H|·|L| = c·|L(C)|
  have hdc : Fintype.card H * L.card = cnt m * C.lines.card := by
    have h1 : ∑ g : H, (fam g).card = ∑ l ∈ C.lines, cnt l := by
      have : ∀ g : H, (fam g).card = ∑ l ∈ C.lines, (if l ∈ fam g then 1 else 0) := by
        intro g
        rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsub g)]
        simp
      rw [Finset.sum_congr rfl (fun g _ => this g), Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_boole]; simp [hcnt]
    rw [Finset.sum_congr rfl (fun l hl => huni l hl)] at h1
    simp only [hfam, card_imgL, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
    rw [h1, mul_comm]
  have : cnt m * (C.lines.card * d) ≤ cnt m * (L.card * C.deg) := by
    calc cnt m * (C.lines.card * d) = (cnt m * C.lines.card) * d := by ring
      _ = (Fintype.card H * L.card) * d := by rw [hdc]
      _ = L.card * (Fintype.card H * d) := by ring
      _ ≤ L.card * (cnt m * C.deg) := Nat.mul_le_mul_left _ hu
      _ = cnt m * (L.card * C.deg) := by ring
  exact Nat.le_of_mul_le_mul_left this hc

/-- The counting data behind TR-1: under a line-transitive group every line lies in the same number
`c > 0` of translates of `L`, and `|H|·|L| = c·|L(C)|`. -/
theorem transfer_cover (C : Config α) (H : Subgroup (Equiv.Perm α)) [Fintype H]
    (L : Finset (Finset α)) (hL : L ⊆ C.lines) (hne : L.Nonempty)
    (hmap : ∀ g ∈ H, ∀ l ∈ C.lines, l.map g.toEmbedding ∈ C.lines)
    (htrans : ∀ l ∈ C.lines, ∀ l' ∈ C.lines, ∃ g ∈ H, l.map g.toEmbedding = l') :
    ∃ c, 0 < c ∧ (∀ l ∈ C.lines, (Finset.univ.filter (fun g : H => l ∈ imgL g L)).card = c) ∧
      Fintype.card H * L.card = c * C.lines.card := by
  obtain ⟨m, hm⟩ := hne
  set fam : H → Finset (Finset α) := fun g => imgL g L with hfam
  have hsub : ∀ g : H, fam g ⊆ C.lines := by
    intro g l hl
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hl
    exact hmap g g.2 m' (hL hm')
  set cnt : Finset α → ℕ := fun l => (Finset.univ.filter (fun g : H => l ∈ fam g)).card with hcnt
  have huni : ∀ l ∈ C.lines, cnt l = cnt m := by
    intro l hl
    obtain ⟨h, hh, hml⟩ := htrans m (hL hm) l hl
    have key : ∀ g : Equiv.Perm α, l ∈ imgL (h * g) L ↔ m ∈ imgL g L := by
      intro g
      rw [mem_imgL, mem_imgL, map_mul_symm, ← hml, map_symm_map]
    symm
    refine Finset.card_nbij' (fun g => ⟨h * g, H.mul_mem hh g.2⟩)
      (fun g => ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) g.2⟩) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
      exact (key g).2 hg
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
      have := (key (h⁻¹ * g)).1
      rw [mul_inv_cancel_left] at this
      exact this hg
    · intro g _; apply Subtype.ext; simp
    · intro g _; apply Subtype.ext; simp
  have hc : 0 < cnt m := by
    apply Finset.card_pos.2
    refine ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    show m ∈ imgL 1 L
    rw [mem_imgL]
    have : m.map (1 : Equiv.Perm α).symm.toEmbedding = m := by ext x; simp
    rwa [this]
  refine ⟨cnt m, hc, huni, ?_⟩
  have h1 : ∑ g : H, (fam g).card = ∑ l ∈ C.lines, cnt l := by
    have : ∀ g : H, (fam g).card = ∑ l ∈ C.lines, (if l ∈ fam g then 1 else 0) := by
      intro g
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsub g)]
      simp
    rw [Finset.sum_congr rfl (fun g _ => this g), Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_boole]; simp [hcnt]
  rw [Finset.sum_congr rfl (fun l hl => huni l hl)] at h1
  simp only [hfam, card_imgL, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  rw [h1, mul_comm]

/-- **TR-2 (rigidity, group version).** If equality holds in TR-1, `|L(C)|·d = |L|·deg C`, then every
optimal assignment meets every translate of `L` in exactly `d` violated lines. -/
theorem transfer_rigid (C : Config α) (H : Subgroup (Equiv.Perm α)) [Fintype H]
    (L : Finset (Finset α)) (hL : L ⊆ C.lines) (hne : L.Nonempty)
    (hmap : ∀ g ∈ H, ∀ l ∈ C.lines, l.map g.toEmbedding ∈ C.lines)
    (htrans : ∀ l ∈ C.lines, ∀ l' ∈ C.lines, ∃ g ∈ H, l.map g.toEmbedding = l')
    (d : ℕ) (hdeg : ∀ g ∈ H, ∀ s : α → F, d ≤ (C.violated s ∩ imgL g L).card)
    (heq : C.lines.card * d = L.card * C.deg)
    (s : α → F) (hs : (C.violated s).card = C.deg) :
    ∀ g ∈ H, (C.violated s ∩ imgL g L).card = d := by
  obtain ⟨c, hc, hcov, hdc⟩ := transfer_cover C H L hL hne hmap htrans
  have hex := uniform_cover_excess C (fun g : H => imgL g L)
    (fun g l hl => by
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hl
      exact hmap g g.2 m' (hL hm')) c hcov s
  rw [hs] at hex
  have hLpos : 0 < L.card := Finset.card_pos.2 hne
  -- |H|·d = c·deg
  have hHd : Fintype.card H * d = c * C.deg := by
    have : L.card * (Fintype.card H * d) = L.card * (c * C.deg) := by
      calc L.card * (Fintype.card H * d) = (Fintype.card H * L.card) * d := by ring
        _ = c * (C.lines.card * d) := by rw [hdc]; ring
        _ = c * (L.card * C.deg) := by rw [heq]
        _ = L.card * (c * C.deg) := by ring
    exact Nat.eq_of_mul_eq_mul_left hLpos this
  have hsum : ∑ g : H, (C.violated s ∩ imgL g L).card = ∑ _g : H, d := by
    rw [hex, Finset.sum_const, Finset.card_univ, smul_eq_mul, hHd]
  have hall := (Finset.sum_eq_sum_iff_of_le (fun (g : H) (_ : g ∈ Finset.univ) => hdeg g g.2 s)).1 hsum.symm
  intro g hg
  exact (hall ⟨g, hg⟩ (Finset.mem_univ _)).symm

/-! ### pulling a configuration back along an injection -/

variable {β : Type} [Fintype β] [DecidableEq β]

/-- the pull-back of `D` along `e` to the line family `L` (whose images are lines of `D`) -/
def comap (D : Config β) (e : α ↪ β) (L : Finset (Finset α)) (hL : ∀ l ∈ L, l.map e ∈ D.lines) :
    Config α where
  lines := L
  sign := fun l => D.sign (l.map e)
  three := fun l hl => by rw [← Finset.card_map e]; exact D.three _ (hL l hl)

theorem violated_comap (D : Config β) (e : α ↪ β) (L : Finset (Finset α))
    (hL : ∀ l ∈ L, l.map e ∈ D.lines) (hD : D.lines = L.image (fun l => l.map e)) (s : β → F) :
    D.violated s = ((D.comap e L hL).violated (s ∘ e)).image (fun l => l.map e) := by
  ext l
  constructor
  · intro hl
    rw [violated, Finset.mem_filter] at hl
    obtain ⟨hl1, hl2⟩ := hl
    rw [hD] at hl1
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl1
    refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
    rw [violated, Finset.mem_filter]
    refine ⟨hm, ?_⟩
    unfold Violated at hl2 ⊢
    simpa [Finset.sum_map, comap] using hl2
  · intro hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
    rw [violated, Finset.mem_filter] at hm ⊢
    refine ⟨by rw [hD]; exact Finset.mem_image_of_mem _ hm.1, ?_⟩
    have h2 := hm.2
    unfold Violated at h2 ⊢
    simpa [Finset.sum_map, comap] using h2

theorem deg_comap (D : Config β) (e : α ↪ β) (L : Finset (Finset α))
    (hL : ∀ l ∈ L, l.map e ∈ D.lines) (hD : D.lines = L.image (fun l => l.map e)) :
    (D.comap e L hL).deg = D.deg := by
  have key : ∀ s : β → F, ((D.comap e L hL).violated (s ∘ e)).card = (D.violated s).card := by
    intro s
    rw [violated_comap D e L hL hD s, Finset.card_image_of_injective _ (Finset.map_injective _)]
  apply le_antisymm
  · obtain ⟨s, hs⟩ := D.exists_opt
    rw [← hs, ← key s]
    exact deg_le _ _
  · obtain ⟨t, ht⟩ := (D.comap e L hL).exists_opt
    have hte : (Function.extend e t 0) ∘ e = t := by
      funext x; exact e.injective.extend_apply t 0 x
    rw [← ht, ← hte, key]
    exact deg_le _ _

theorem sub_self (C : Config α) : C.sub C.lines (subset_refl _) = C := by
  cases C; rfl

end Config

namespace Spectral

open Config

variable {N : ℕ}

/-! ### the symplectic group as permutations -/

/-- `φ` is additive and preserves ω -/
def IsSymp (φ : Equiv.Perm (V N)) : Prop :=
  (∀ a b, φ (a + b) = φ a + φ b) ∧ ∀ a b, omega (φ a) (φ b) = omega a b

instance (φ : Equiv.Perm (V N)) : Decidable (IsSymp φ) := by unfold IsSymp; infer_instance

theorem IsSymp.map_zero {φ : Equiv.Perm (V N)} (h : IsSymp φ) : φ 0 = 0 := by
  have := h.1 0 0
  rw [add_zero, add_self_V] at this
  exact this

theorem IsSymp.one : IsSymp (1 : Equiv.Perm (V N)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem IsSymp.mul {φ ψ : Equiv.Perm (V N)} (hφ : IsSymp φ) (hψ : IsSymp ψ) : IsSymp (φ * ψ) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [Equiv.Perm.mul_apply]; rw [hψ.1, hφ.1]
  · simp only [Equiv.Perm.mul_apply]; rw [hφ.2, hψ.2]

theorem IsSymp.inv {φ : Equiv.Perm (V N)} (hφ : IsSymp φ) : IsSymp φ⁻¹ := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · apply φ.injective
    rw [hφ.1]; simp
  · rw [← hφ.2]; simp

/-- the symplectic group Sp(2N,2), as a subgroup of the permutations of the labels -/
def Sp (N : ℕ) : Subgroup (Equiv.Perm (V N)) where
  carrier := {φ | IsSymp φ}
  mul_mem' := fun ha hb => IsSymp.mul ha hb
  one_mem' := IsSymp.one
  inv_mem' := fun ha => IsSymp.inv ha

theorem mem_Sp {φ : Equiv.Perm (V N)} : φ ∈ Sp N ↔ IsSymp φ := Iff.rfl

instance : DecidablePred (· ∈ Sp N) := fun φ => decidable_of_iff _ mem_Sp.symm

/-! ### transvections -/

theorem omega_add_left (p q r : V N) : omega (p + q) r = omega p r + omega q r := by
  rw [omega_comm, omega_add_right, omega_comm r, omega_comm r]

theorem omega_smul_left (t : F) (p q : V N) : omega (t • p) q = t * omega p q := by
  unfold omega; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

theorem omega_smul_right (t : F) (p q : V N) : omega p (t • q) = t * omega p q := by
  rw [omega_comm, omega_smul_left, omega_comm]

/-- the transvection `x ↦ x + ω(x,w) w` -/
def transv (w : V N) (x : V N) : V N := x + omega x w • w

theorem transv_transv (w x : V N) : transv w (transv w x) = x := by
  unfold transv
  rw [omega_add_left, omega_smul_left, omega_self, mul_zero, add_zero, add_assoc, ← add_smul,
    add_self_F, zero_smul, add_zero]

/-- the transvection as a permutation -/
def transvP (w : V N) : Equiv.Perm (V N) where
  toFun := transv w
  invFun := transv w
  left_inv := transv_transv w
  right_inv := transv_transv w

theorem transvP_apply (w x : V N) : transvP w x = x + omega x w • w := rfl

theorem F_cases (x : F) : x = 0 ∨ x = 1 := by revert x; decide

theorem transvP_symp (w : V N) : IsSymp (transvP w) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [transvP_apply, omega_add_left, add_smul]; abel
  · simp only [transvP_apply, omega_add_left, omega_add_right, omega_smul_left, omega_smul_right,
      omega_self]
    rw [omega_comm w b]
    have : ∀ u v : F, u * v + v * u = 0 := by decide
    have h := this (omega a w) (omega b w)
    linear_combination h

theorem transvP_map {x y : V N} (h : omega x y = 1) : transvP (x + y) x = y := by
  rw [transvP_apply, omega_add_right, omega_self, h, zero_add, one_smul, add_cancel_left']

theorem transvP_fix {a w : V N} (h : omega a w = 0) : transvP w a = a := by
  rw [transvP_apply, h, zero_smul, add_zero]

/-! ### solving ω-equations (nondegeneracy) -/

theorem exists_omega_one {a : V N} (ha : a ≠ 0) : ∃ c, omega a c = 1 := by
  by_cases h1 : a.1 = 0
  · have h2 : a.2 ≠ 0 := fun h => ha (Prod.ext h1 h)
    obtain ⟨k, hk⟩ : ∃ k, a.2 k ≠ 0 := by by_contra h; push Not at h; exact h2 (funext h)
    refine ⟨(Pi.single k 1, 0), ?_⟩
    unfold omega
    rw [Finset.sum_eq_single k]
    · simp; rcases F_cases (a.2 k) with h | h
      · exact absurd h hk
      · exact h
    · intro j _ hj; simp [h1, hj]
    · simp
  · obtain ⟨k, hk⟩ : ∃ k, a.1 k ≠ 0 := by by_contra h; push Not at h; exact h1 (funext h)
    refine ⟨(0, Pi.single k 1), ?_⟩
    unfold omega
    rw [Finset.sum_eq_single k]
    · simp; rcases F_cases (a.1 k) with h | h
      · exact absurd h hk
      · exact h
    · intro j _ hj; simp [hj]
    · simp

theorem add_ne_zero_of_ne {a b : V N} (h : a ≠ b) : a + b ≠ 0 := by
  intro h'; apply h
  have := congrArg (· + b) h'
  simpa [add_assoc, add_self_V] using this

/-- (S2) two non-zero labels: a common `c` with ω = 1 for both -/
theorem exists_omega_one_one {a b : V N} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c, omega a c = 1 ∧ omega b c = 1 := by
  obtain ⟨c1, h1⟩ := exists_omega_one ha
  rcases F_cases (omega b c1) with hb1 | hb1
  · obtain ⟨c2, h2⟩ := exists_omega_one hb
    rcases F_cases (omega a c2) with ha2 | ha2
    · refine ⟨c1 + c2, ?_, ?_⟩
      · rw [omega_add_right, h1, ha2, add_zero]
      · rw [omega_add_right, hb1, h2, zero_add]
    · exact ⟨c2, ha2, h2⟩
  · exact ⟨c1, h1, hb1⟩

/-- (S3) independent `a, b`: some `c` with ω(a,c) = 0, ω(b,c) = 1 -/
theorem exists_omega_zero_one {a b : V N} (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ c, omega a c = 0 ∧ omega b c = 1 := by
  obtain ⟨c0, h0⟩ := exists_omega_one (add_ne_zero_of_ne hab)
  rw [omega_add_left] at h0
  rcases F_cases (omega a c0) with ha0 | ha0
  · rw [ha0, zero_add] at h0; exact ⟨c0, ha0, h0⟩
  · have hb0 : omega b c0 = 0 := by
      rw [ha0] at h0; rcases F_cases (omega b c0) with h | h
      · exact h
      · rw [h] at h0; exact absurd h0 (by decide)
    obtain ⟨c1, h1⟩ := exists_omega_one hb
    rcases F_cases (omega a c1) with ha1 | ha1
    · exact ⟨c1, ha1, h1⟩
    · refine ⟨c0 + c1, ?_, ?_⟩
      · rw [omega_add_right, ha0, ha1]; decide
      · rw [omega_add_right, hb0, h1, zero_add]

/-- (S5) three independent labels: values (0, 0, 1) -/
theorem exists_omega_001 {a b b' : V N} (hb' : b' ≠ 0) (hab' : a ≠ b') (hbb' : b ≠ b')
    (hind : b' ≠ a + b) : ∃ c, omega a c = 0 ∧ omega b c = 0 ∧ omega b' c = 1 := by
  obtain ⟨c1, ha1, hb'1⟩ := exists_omega_zero_one hb' hab'
  rcases F_cases (omega b c1) with hb1 | hb1
  · exact ⟨c1, ha1, hb1, hb'1⟩
  · have hne : a ≠ b + b' := by
      intro h; apply hind; rw [h, add_comm b b', add_assoc, add_self_V, add_zero]
    obtain ⟨c2, ha2, hs2⟩ := exists_omega_zero_one (add_ne_zero_of_ne hbb') hne
    rw [omega_add_left] at hs2
    rcases F_cases (omega b c2) with hb2 | hb2
    · rw [hb2, zero_add] at hs2; exact ⟨c2, ha2, hb2, hs2⟩
    · have hb'2 : omega b' c2 = 0 := by
        rw [hb2] at hs2; rcases F_cases (omega b' c2) with h | h
        · exact h
        · rw [h] at hs2; exact absurd hs2 (by decide)
      refine ⟨c1 + c2, ?_, ?_, ?_⟩
      · rw [omega_add_right, ha1, ha2, add_zero]
      · rw [omega_add_right, hb1, hb2]; decide
      · rw [omega_add_right, hb'1, hb'2, add_zero]

/-- (S4) three independent labels: values (0, 1, 1) -/
theorem exists_omega_011 {a b b' : V N} (hb : b ≠ 0) (hb' : b' ≠ 0) (hab : a ≠ b) (hab' : a ≠ b')
    (hbb' : b ≠ b') (hind : b' ≠ a + b) :
    ∃ c, omega a c = 0 ∧ omega b c = 1 ∧ omega b' c = 1 := by
  obtain ⟨c1, ha1, hb1⟩ := exists_omega_zero_one hb hab
  rcases F_cases (omega b' c1) with hb'1 | hb'1
  · obtain ⟨c2, ha2, hb2, hb'2⟩ := exists_omega_001 hb' hab' hbb' hind
    refine ⟨c1 + c2, ?_, ?_, ?_⟩
    · rw [omega_add_right, ha1, ha2, add_zero]
    · rw [omega_add_right, hb1, hb2, add_zero]
    · rw [omega_add_right, hb'1, hb'2, zero_add]
  · exact ⟨c1, ha1, hb1, hb'1⟩

/-! ### transitivity -/

/-- Sp is transitive on non-zero labels -/
theorem Sp_trans_vec {a a' : V N} (ha : a ≠ 0) (ha' : a' ≠ 0) : ∃ φ ∈ Sp N, φ a = a' := by
  by_cases he : a = a'
  · exact ⟨1, (Sp N).one_mem, by rw [he]; rfl⟩
  rcases F_cases (omega a a') with h0 | h1
  · obtain ⟨c, hac, ha'c⟩ := exists_omega_one_one ha ha'
    refine ⟨transvP (c + a') * transvP (a + c), (Sp N).mul_mem (transvP_symp _) (transvP_symp _), ?_⟩
    rw [Equiv.Perm.mul_apply, transvP_map hac, transvP_map (by rw [omega_comm]; exact ha'c)]
  · exact ⟨transvP (a + a'), transvP_symp _, transvP_map h1⟩

/-- the stabiliser of `a` is transitive on the labels commuting with `a` (other than 0, a) -/
theorem Sp_trans_stab {a b b' : V N} (hb : b ≠ 0) (hb' : b' ≠ 0) (hab : a ≠ b) (hab' : a ≠ b')
    (hω : omega a b = 0) (hω' : omega a b' = 0) : ∃ φ ∈ Sp N, φ a = a ∧ φ b = b' := by
  by_cases he : b = b'
  · exact ⟨1, (Sp N).one_mem, rfl, by rw [he]; rfl⟩
  rcases F_cases (omega b b') with h0 | h1
  · obtain ⟨c, hac, hbc, hb'c⟩ : ∃ c, omega a c = 0 ∧ omega b c = 1 ∧ omega b' c = 1 := by
      by_cases hind : b' = a + b
      · obtain ⟨c, h1, h2⟩ := exists_omega_zero_one hb hab
        refine ⟨c, h1, h2, ?_⟩
        rw [hind, omega_add_left, h1, h2, zero_add]
      · exact exists_omega_011 hb hb' hab hab' he hind
    refine ⟨transvP (c + b') * transvP (b + c),
      (Sp N).mul_mem (transvP_symp _) (transvP_symp _), ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply,
        transvP_fix (a := a) (w := b + c) (by rw [omega_add_right, hω, hac, add_zero]),
        transvP_fix (a := a) (w := c + b') (by rw [omega_add_right, hac, hω', add_zero])]
    · rw [Equiv.Perm.mul_apply, transvP_map hbc, transvP_map (by rw [omega_comm]; exact hb'c)]
  · refine ⟨transvP (b + b'), transvP_symp _, ?_, transvP_map h1⟩
    exact transvP_fix (by rw [omega_add_right, hω, hω', add_zero])

theorem IsSymp.ne_zero {φ : Equiv.Perm (V N)} (h : IsSymp φ) {x : V N} (hx : x ≠ 0) : φ x ≠ 0 := by
  intro h'; apply hx; apply φ.injective; rw [h', h.map_zero]

/-- Sp is transitive on ordered commuting pairs spanning a line -/
theorem Sp_trans_pairs {a b a' b' : V N} (h : IsLine a b (a + b)) (h' : IsLine a' b' (a' + b')) :
    ∃ φ ∈ Sp N, φ a = a' ∧ φ b = b' := by
  obtain ⟨φ1, hφ1, e1⟩ := Sp_trans_vec h.nz_a h'.nz_a
  have hs1 : IsSymp φ1 := hφ1
  obtain ⟨φ2, hφ2, e2, e3⟩ := Sp_trans_stab (a := a') (b := φ1 b) (b' := b')
    (hs1.ne_zero h.nz_b) h'.nz_b (by rw [← e1]; exact φ1.injective.ne h.ne_ab) h'.ne_ab
    (by rw [← e1, hs1.2]; exact h.comm) h'.comm
  refine ⟨φ2 * φ1, (Sp N).mul_mem hφ2 hφ1, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, e1, e2]
  · rw [Equiv.Perm.mul_apply, e3]

/-! ### lines of W under Sp -/

theorem mem_Wpts {x : V N} : x ∈ Wpts N ↔ x ≠ 0 := by simp [Wpts]

theorem tri_mem_W {a b : V N} (h : IsLine a b (a + b)) : tri (a, b) ∈ (W N).lines :=
  Finset.mem_image.2 ⟨(a, b), mem_OP.2 ⟨mem_Wpts.2 h.nz_a, mem_Wpts.2 h.nz_b, h.comm,
    mem_Wpts.2 h.nz_c⟩, rfl⟩

theorem mem_W_lines {l : Finset (V N)} :
    l ∈ (W N).lines ↔ ∃ a b : V N, IsLine a b (a + b) ∧ l = tri (a, b) := by
  constructor
  · intro hl
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
    exact ⟨p.1, p.2, isLine_of_OP (zero_not_mem_W N) hp, rfl⟩
  · rintro ⟨a, b, h, rfl⟩; exact tri_mem_W h

theorem tri_map {φ : Equiv.Perm (V N)} (hφ : ∀ a b, φ (a + b) = φ a + φ b) (a b : V N) :
    (tri (a, b)).map φ.toEmbedding = tri (φ a, φ b) := by
  simp [tri, Finset.map_insert, hφ]

theorem IsSymp.isLine {φ : Equiv.Perm (V N)} (hφ : IsSymp φ) {a b : V N} (h : IsLine a b (a + b)) :
    IsLine (φ a) (φ b) (φ a + φ b) := by
  have hc : φ a + φ b = φ (a + b) := (hφ.1 a b).symm
  refine ⟨φ.injective.ne h.ne_ab, ?_, ?_, hφ.ne_zero h.nz_a, hφ.ne_zero h.nz_b, ?_, ?_, ?_⟩
  · rw [hc]; exact φ.injective.ne h.ne_ac
  · rw [hc]; exact φ.injective.ne h.ne_bc
  · rw [hc]; exact hφ.ne_zero h.nz_c
  · exact add_self_V _
  · rw [hφ.2]; exact h.comm

theorem Sp_map_lines : ∀ g ∈ Sp N, ∀ l ∈ (W N).lines, l.map g.toEmbedding ∈ (W N).lines := by
  intro g hg l hl
  obtain ⟨a, b, h, rfl⟩ := mem_W_lines.1 hl
  have hs : IsSymp g := hg
  rw [tri_map hs.1]
  exact tri_mem_W (hs.isLine h)

/-- **Sp(2N,2) is transitive on the lines of W(2N−1,2).** -/
theorem Sp_trans_lines :
    ∀ l ∈ (W N).lines, ∀ l' ∈ (W N).lines, ∃ g ∈ Sp N, l.map g.toEmbedding = l' := by
  intro l hl l' hl'
  obtain ⟨a, b, h, rfl⟩ := mem_W_lines.1 hl
  obtain ⟨a', b', h', rfl⟩ := mem_W_lines.1 hl'
  obtain ⟨φ, hφ, e1, e2⟩ := Sp_trans_pairs h h'
  refine ⟨φ, hφ, ?_⟩
  have hs : IsSymp φ := hφ
  rw [tri_map hs.1, e1, e2]

/-! ### Pauli realisations of sub-configurations of W -/

theorem sgnF_eq_sign {a b : V N} (h : IsLine a b (a + b)) : sgnF (a, b) = sign a b (a + b) := by
  unfold sgnF sign
  simp only
  rw [ph_eq_signK]
  rcases signK_even h with h0 | h2
  · rw [h0]; decide
  · rw [h2]; decide

theorem W_sign_tri {a b : V N} (h : IsLine a b (a + b)) : (W N).sign (tri (a, b)) = sign a b (a + b) := by
  have hp : (a, b) ∈ OP (Wpts N) := mem_OP.2 ⟨mem_Wpts.2 h.nz_a, mem_Wpts.2 h.nz_b, h.comm,
    mem_Wpts.2 h.nz_c⟩
  unfold W; rw [configX_sign _ hp, sgnF_eq_sign h]

theorem real_sub (L : Finset (Finset (V N))) (hL : L ⊆ (W N).lines) :
    PauliRealization ((W N).sub L hL) id := by
  refine ⟨Function.injective_id, fun l hl => ?_⟩
  obtain ⟨a, b, h, rfl⟩ := mem_W_lines.1 (hL hl)
  exact ⟨a, b, a + b, rfl, h, W_sign_tri h⟩

theorem imgL_sub {g : Equiv.Perm (V N)} (hg : g ∈ Sp N) {L : Finset (Finset (V N))}
    (hL : L ⊆ (W N).lines) : imgL g L ⊆ (W N).lines := by
  intro l hl
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
  exact Sp_map_lines g hg m (hL hm)

/-- translates of a sub-configuration by Sp have the same degree (ALG-3) -/
theorem deg_imgL {g : Equiv.Perm (V N)} (hg : g ∈ Sp N) (L : Finset (Finset (V N)))
    (hL : L ⊆ (W N).lines) :
    ((W N).sub (imgL g L) (imgL_sub hg hL)).deg = ((W N).sub L hL).deg := by
  have hs : IsSymp g := hg
  symm
  exact deg_invariant_equiv ((W N).sub L hL) ((W N).sub (imgL g L) (imgL_sub hg hL)) g id id
    (real_sub L hL) (real_sub _ _) rfl (fun p q => hs.2 p q)

/-- **TR-5.1.** Every N-qubit configuration S ⊆ W(2N−1,2) satisfies deg S / |L(S)| ≤ ρ_N, in the
form |L_N|·deg S ≤ |L(S)|·deg W(2N−1,2). -/
theorem rho_max (L : Finset (Finset (V N))) (hL : L ⊆ (W N).lines) :
    (W N).lines.card * ((W N).sub L hL).deg ≤ L.card * (W N).deg := by
  refine transfer (W N) (Sp N) L hL Sp_map_lines Sp_trans_lines _ ?_
  intro g hg s
  rw [← violated_sub _ _ (imgL_sub hg hL), ← deg_imgL hg L hL]
  exact deg_le _ _

/-- **TR-2 for W(2N−1,2).** If S ⊆ W(2N−1,2) attains ρ(S) = ρ_N, then every optimal assignment of
W(2N−1,2) violates exactly deg S lines of every Sp-translate of S. -/
theorem rho_rigid (L : Finset (Finset (V N))) (hL : L ⊆ (W N).lines) (hne : L.Nonempty)
    (heq : (W N).lines.card * ((W N).sub L hL).deg = L.card * (W N).deg)
    (s : V N → F) (hs : ((W N).violated s).card = (W N).deg) :
    ∀ g ∈ Sp N, ((W N).violated s ∩ imgL g L).card = ((W N).sub L hL).deg := by
  refine transfer_rigid (W N) (Sp N) L hL hne Sp_map_lines Sp_trans_lines _ ?_ heq s hs
  intro g hg s'
  rw [← violated_sub _ _ (imgL_sub hg hL), ← deg_imgL hg L hL]
  exact deg_le _ _

/-! ### padding with an extra qubit -/

/-- `a ↦ a ⊗ I` -/
def pad (a : V N) : V (N + 1) := (Fin.snoc (α := fun _ => F) a.1 0, Fin.snoc (α := fun _ => F) a.2 0)

theorem pad_add (a b : V N) : pad (a + b) = pad a + pad b := by
  unfold pad
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem pad_zero : pad (0 : V N) = 0 := by
  unfold pad
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem pad_inj : Function.Injective (pad (N := N)) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := congrFun h1 (Fin.castSucc i); simpa [pad] using this
  · have := congrFun h2 (Fin.castSucc i); simpa [pad] using this

theorem omega_pad (a b : V N) : omega (pad a) (pad b) = omega a b := by
  unfold omega; rw [Fin.sum_univ_castSucc]; simp [pad]

theorem ycount_pad (a : V N) : ycount (pad a) = ycount a := by
  unfold ycount; rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]; simp [pad]

theorem signK_pad (a b c : V N) : signK (pad a) (pad b) (pad c) = signK a b c := by
  rw [signK_eq, signK_eq, ycount_pad, ycount_pad, ycount_pad, Fin.sum_univ_castSucc]; simp [pad]

theorem sign_pad (a b c : V N) : sign (pad a) (pad b) (pad c) = sign a b c := by
  unfold sign; rw [signK_pad]

def padE : V N ↪ V (N + 1) := ⟨pad, pad_inj⟩

theorem pad_isLine {a b : V N} (h : IsLine a b (a + b)) : IsLine (pad a) (pad b) (pad a + pad b) := by
  have hc : pad a + pad b = pad (a + b) := (pad_add a b).symm
  have nz : ∀ x : V N, x ≠ 0 → pad x ≠ 0 := fun x hx h' => hx (pad_inj (h'.trans pad_zero.symm))
  refine ⟨pad_inj.ne h.ne_ab, ?_, ?_, nz _ h.nz_a, nz _ h.nz_b, ?_, add_self_V _, ?_⟩
  · rw [hc]; exact pad_inj.ne h.ne_ac
  · rw [hc]; exact pad_inj.ne h.ne_bc
  · rw [hc]; exact nz _ h.nz_c
  · rw [omega_pad]; exact h.comm

theorem tri_pad (a b : V N) : (tri (a, b)).map padE = tri (pad a, pad b) := by
  simp [tri, Finset.map_insert, padE, pad_add]

theorem padL_sub {L : Finset (Finset (V N))} (hL : L ⊆ (W N).lines) :
    L.image (fun l => l.map padE) ⊆ (W (N + 1)).lines := by
  intro l hl
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
  obtain ⟨a, b, h, rfl⟩ := mem_W_lines.1 (hL hm)
  rw [tri_pad]; exact tri_mem_W (pad_isLine h)

/-- Padding an N-qubit configuration by an identity factor preserves its degree and line count. -/
theorem deg_pad (L : Finset (Finset (V N))) (hL : L ⊆ (W N).lines) :
    ((W (N + 1)).sub _ (padL_sub hL)).deg = ((W N).sub L hL).deg ∧
      (L.image (fun l => l.map padE)).card = L.card := by
  refine ⟨?_, Finset.card_image_of_injective _ (Finset.map_injective _)⟩
  set S := (W (N + 1)).sub _ (padL_sub hL)
  have hmem : ∀ l ∈ L, l.map padE ∈ S.lines := fun l hl => Finset.mem_image_of_mem _ hl
  rw [← deg_comap S padE L hmem rfl]
  symm
  refine deg_invariant ((W N).sub L hL) (S.comap padE L hmem) id pad (real_sub L hL) ?_ rfl
    (fun p q => omega_pad p q)
  refine ⟨pad_inj, fun l hl => ?_⟩
  obtain ⟨a, b, h, rfl⟩ := mem_W_lines.1 (hL hl)
  refine ⟨a, b, a + b, rfl, by rw [pad_add]; exact pad_isLine h, ?_⟩
  show (W (N + 1)).sign ((tri (a, b)).map padE) = _
  rw [tri_pad, W_sign_tri (pad_isLine h), pad_add]

theorem rho_nonneg (N : ℕ) : 0 ≤ rho N := by unfold rho; positivity

/-- **TR-5.2.** ρ_N ≤ ρ_{N+1}. -/
theorem rho_mono_succ (N : ℕ) : rho N ≤ rho (N + 1) := by
  rcases Nat.eq_zero_or_pos (W N).lines.card with h0 | hpos
  · unfold rho; rw [h0]; simp only [Nat.cast_zero, div_zero]; exact rho_nonneg _
  obtain ⟨hdeg, hcard⟩ := deg_pad (W N).lines (subset_refl _)
  have h := rho_max _ (padL_sub (subset_refl (W N).lines))
  rw [hdeg, hcard, Config.sub_self] at h
  have hsub := Finset.card_le_card (padL_sub (subset_refl (W N).lines))
  rw [hcard] at hsub
  unfold rho
  have hp1 : (0 : ℝ) < (W N).lines.card := by exact_mod_cast hpos
  have hp2 : (0 : ℝ) < (W (N + 1)).lines.card := by exact_mod_cast (lt_of_lt_of_le hpos hsub)
  rw [div_le_div_iff₀ hp1 hp2]
  have : ((W (N + 1)).lines.card * (W N).deg : ℝ) ≤ (W N).lines.card * (W (N + 1)).deg := by
    exact_mod_cast h
  linarith

/-- **TR-5.2.** ρ is non-decreasing. -/
theorem rho_mono : Monotone rho := monotone_nat_of_le_succ rho_mono_succ

/-- Target A again, now via the monotone version in `Spectral.lean`. -/
theorem rho_strict_jumps' : ∀ N₀, ∃ N ≥ N₀, rho N < rho (N + 1) :=
  infinitely_many_strict_jumps rho rho_mono rho_lt_half rho_tendsto_half

theorem card_lines_W3 : (W 3).lines.card = 315 := by
  have h := lines_W 3 (by norm_num)
  have e : (4 ^ 3 - 1) * (4 ^ 3 - 4) = 12 * 315 := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

/-- **TQ-2 (universal 1/5 bound), 3 qubits.** Every configuration S ⊆ W(5,2) has 5·deg S ≤ |L(S)|.
(Stated with `N = 3` as a hypothesis.) -/
theorem three_qubit_bound (N : ℕ) (hN : N = 3) (L : Finset (Finset (V N))) (hL : L ⊆ (W N).lines) :
    5 * ((W N).sub L hL).deg ≤ L.card := by
  have h := rho_max L hL
  have hL3 : (W N).lines.card = 315 := hN ▸ card_lines_W3
  have hd : (W N).deg = 63 := hN ▸ W5_eq_63
  rw [hL3, hd] at h
  have h' : 63 * (5 * ((W N).sub L hL).deg) ≤ 63 * L.card := by linarith
  exact Nat.le_of_mul_le_mul_left h' (by norm_num)

/-- **TQ-2 on ≤ 3 qubits.** Every configuration on N ≤ 3 qubits has 5·deg S ≤ |L(S)|. -/
theorem three_qubit_bound_le (N : ℕ) (hN : N ≤ 3) (L : Finset (Finset (V N))) (hL : L ⊆ (W N).lines) :
    5 * ((W N).sub L hL).deg ≤ L.card := by
  interval_cases N
  · obtain ⟨d1, c1⟩ := deg_pad L hL
    obtain ⟨d2, c2⟩ := deg_pad _ (padL_sub hL)
    obtain ⟨d3, c3⟩ := deg_pad _ (padL_sub (padL_sub hL))
    have := three_qubit_bound _ rfl _ (padL_sub (padL_sub (padL_sub hL)))
    rw [d3, d2, d1, c3, c2, c1] at this; exact this
  · obtain ⟨d1, c1⟩ := deg_pad L hL
    obtain ⟨d2, c2⟩ := deg_pad _ (padL_sub hL)
    have := three_qubit_bound _ rfl _ (padL_sub (padL_sub hL))
    rw [d2, d1, c2, c1] at this; exact this
  · obtain ⟨d1, c1⟩ := deg_pad L hL
    have := three_qubit_bound _ rfl _ (padL_sub hL)
    rw [d1, c1] at this; exact this
  · exact three_qubit_bound 3 rfl L hL

end Spectral
end PauliCtx
