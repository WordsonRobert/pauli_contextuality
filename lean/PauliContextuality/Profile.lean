/-
Profile.lean — blueprint TR-4 (profile bound).

Let `H` be a group of permutations mapping lines to lines, `orb m` the `H`-orbit of the line `m`,
and `L` a family of lines such that every translate `g·L` meets every violated set `V(s)` in at least
`d` lines. Then for every assignment

    d ≤ Σ_{m ∈ L} |V(s) ∩ orb m| / |orb m|.

Grouping the lines of `L` by orbit this is the blueprint's  Σ_i a_ij n_i/|O_i| ≥ d_j, where
`a_ij = |L_j ∩ O_i|` and `n_i = |V ∩ O_i|` is the profile of `s`.
The averaging uses orbit–stabiliser: for `ℓ ∈ orb m`, exactly `|H|/|orb m|` group elements map `m` to `ℓ`.
-/
import PauliContextuality.Transfer

namespace PauliCtx.Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-- the `H`-orbit of a line, inside the lines of `C` -/
noncomputable def orb (C : Config α) (H : Subgroup (Equiv.Perm α)) (m : Finset α) : Finset (Finset α) :=
  by classical exact C.lines.filter (fun l => ∃ g ∈ H, m.map g.toEmbedding = l)

theorem mem_orb {C : Config α} {H : Subgroup (Equiv.Perm α)} {m l : Finset α} :
    l ∈ orb C H m ↔ l ∈ C.lines ∧ ∃ g ∈ H, m.map g.toEmbedding = l := by
  classical
  unfold orb; simp [Finset.mem_filter]

theorem map_mul (h g : Equiv.Perm α) (m : Finset α) :
    m.map (h * g).toEmbedding = (m.map g.toEmbedding).map h.toEmbedding := by
  ext x
  simp only [Finset.mem_map_equiv, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

/-- **orbit–stabiliser count.** For `ℓ` in the orbit of `m`, the number of `g ∈ H` with `g·m = ℓ`
times `|orb m|` is `|H|`. -/
theorem orbit_count (C : Config α) (H : Subgroup (Equiv.Perm α)) [Fintype H]
    (hmap : ∀ g ∈ H, ∀ l ∈ C.lines, l.map g.toEmbedding ∈ C.lines) {m : Finset α} (hm : m ∈ C.lines)
    {l : Finset α} (hl : l ∈ orb C H m) :
    (orb C H m).card * (Finset.univ.filter (fun g : H => m.map (g : Equiv.Perm α).toEmbedding = l)).card
      = Fintype.card H := by
  classical
  set st := fun l' => (Finset.univ.filter (fun g : H => m.map (g : Equiv.Perm α).toEmbedding = l')).card
  -- the count is constant on the orbit
  have hconst : ∀ l' ∈ orb C H m, st l' = st l := by
    have key : ∀ l' ∈ orb C H m, st l' = st m := by
      intro l' hl'
      obtain ⟨-, h, hh, hml⟩ := mem_orb.1 hl'
      refine Finset.card_nbij' (fun g => ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) g.2⟩)
        (fun g => ⟨h * g, H.mul_mem hh g.2⟩) ?_ ?_ ?_ ?_
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        rw [map_mul, hg, ← hml, ← map_mul, inv_mul_cancel]; ext x; simp [Equiv.Perm.one_def]
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        rw [map_mul, hg, hml]
      · intro g _; apply Subtype.ext; simp
      · intro g _; apply Subtype.ext; simp
    intro l' hl'; rw [key l' hl', key l hl]
  -- every g maps m into its orbit
  have hsum : Fintype.card H = ∑ l' ∈ orb C H m, st l' := by
    rw [← Finset.card_univ]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun g : H => m.map (g : Equiv.Perm α).toEmbedding)
      (t := orb C H m)]
    intro g _
    exact mem_orb.2 ⟨hmap g g.2 m hm, g, g.2, rfl⟩
  rw [hsum, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]

/-- **TR-4 (profile bound).** -/
theorem profile_bound (C : Config α) (H : Subgroup (Equiv.Perm α)) [Fintype H]
    (L : Finset (Finset α)) (hL : L ⊆ C.lines)
    (hmap : ∀ g ∈ H, ∀ l ∈ C.lines, l.map g.toEmbedding ∈ C.lines)
    (d : ℕ) (s : α → F) (hdeg : ∀ g ∈ H, d ≤ (C.violated s ∩ imgL g L).card) :
    (d : ℝ) ≤ ∑ m ∈ L, ((C.violated s ∩ orb C H m).card : ℝ) / (orb C H m).card := by
  classical
  set V := C.violated s
  have hVsub : V ⊆ C.lines := Finset.filter_subset _ _
  have hHpos : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  -- |V ∩ g·L| = #{m ∈ L : g·m ∈ V}
  have hcard : ∀ g : Equiv.Perm α, (V ∩ imgL g L).card = (L.filter (fun m => m.map g.toEmbedding ∈ V)).card := by
    intro g
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, imgL, Finset.filter_image,
      Finset.card_image_of_injective _ (Finset.map_injective _)]
  -- for each m: #{g : g·m ∈ V} = |V ∩ orb m| · |H| / |orb m|
  have hm : ∀ m ∈ L, ((Finset.univ.filter (fun g : H => m.map (g : Equiv.Perm α).toEmbedding ∈ V)).card : ℝ)
      = (V ∩ orb C H m).card * Fintype.card H / (orb C H m).card := by
    intro m hmL
    have hmC := hL hmL
    have horb_pos : 0 < (orb C H m).card :=
      Finset.card_pos.2 ⟨m, mem_orb.2 ⟨hmC, 1, H.one_mem, by ext x; simp [Equiv.Perm.one_def]⟩⟩
    have hfib : (Finset.univ.filter (fun g : H => m.map (g : Equiv.Perm α).toEmbedding ∈ V)).card =
        ∑ l ∈ V ∩ orb C H m, (Finset.univ.filter (fun g : H => m.map (g : Equiv.Perm α).toEmbedding = l)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun g : H => m.map (g : Equiv.Perm α).toEmbedding)
        (t := V ∩ orb C H m)]
      · refine Finset.sum_congr rfl fun l hl => ?_
        congr 1; ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h; refine ⟨?_, h⟩; rw [h]; exact (Finset.mem_inter.1 hl).1
      · intro g hg
        have hg' := (Finset.mem_filter.1 hg).2
        exact Finset.mem_inter.2 ⟨hg', mem_orb.2 ⟨hmap g g.2 m hmC, g, g.2, rfl⟩⟩
    have hst : ∀ l ∈ V ∩ orb C H m, ((Finset.univ.filter
        (fun g : H => m.map (g : Equiv.Perm α).toEmbedding = l)).card : ℝ) = Fintype.card H / (orb C H m).card := by
      intro l hl
      have := orbit_count C H hmap hmC (Finset.mem_inter.1 hl).2
      rw [eq_div_iff (by exact_mod_cast horb_pos.ne')]
      exact_mod_cast (by rw [mul_comm]; exact this)
    rw [hfib]; push_cast
    rw [Finset.sum_congr rfl hst, Finset.sum_const, nsmul_eq_mul]; ring
  -- double counting
  have hdc : (∑ g : H, ((V ∩ imgL (g : Equiv.Perm α) L).card : ℝ)) =
      ∑ m ∈ L, ((Finset.univ.filter (fun g : H => m.map (g : Equiv.Perm α).toEmbedding ∈ V)).card : ℝ) := by
    simp_rw [hcard, Finset.card_filter]; push_cast
    exact Finset.sum_comm
  have hlow : (Fintype.card H : ℝ) * d ≤ ∑ g : H, ((V ∩ imgL (g : Equiv.Perm α) L).card : ℝ) := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun (g : H) _ =>
      (by exact_mod_cast hdeg g g.2 : (d : ℝ) ≤ ((V ∩ imgL (g : Equiv.Perm α) L).card : ℝ)))
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  rw [hdc, Finset.sum_congr rfl hm] at hlow
  have : ∑ m ∈ L, ((V ∩ orb C H m).card : ℝ) * Fintype.card H / (orb C H m).card =
      Fintype.card H * ∑ m ∈ L, ((V ∩ orb C H m).card : ℝ) / (orb C H m).card := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
  rw [this] at hlow
  exact le_of_mul_le_mul_left hlow hHpos

end PauliCtx.Config
