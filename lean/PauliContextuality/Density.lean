/-
Density.lean — blueprint 11 (round 3), the density theorem.

  * DEN-1  `den1`, `den1_weak`, `den1_gap` : for every induced configuration X ⊆ V*(N) with n points,
        deg X ≥ |L_X|/2 − n^{3/2}(2^N − 2)/(12√(2^N − 1)) ≥ |L_X|/2 − n^{3/2} 2^{N/2}/12
      (n^{3/2} is written `n * √n`).  A corollary of `spectral_lower`.
  * DEN-1′ `deg_configX_map`, `card_lines_configX_map`, `den1_embed` : a linear map
      φ : V N → V N' that preserves ω on X and is injective on span X carries the induced configuration of X onto the
      induced configuration of φ(X) (lines ↔ lines), with the same degree (ALG-3, `deg_invariant`).
      Hence DEN-1 holds with N replaced by any N' admitting such an embedding.
  * DEN-2  `condExp_avg`, `greedy_le`, `greedy_half` : the method of conditional expectations.
      `condExp C T s` is the expected number of violated lines when the points of T are fixed by s
      and the other points are uniform.  Fixing one more point, one of the two values does not
      increase it (`condExp_avg`), so the greedy assignment (`greedy`) violates ≤ |L|/2 lines.
      `den2` : if n^{3/2}2^{N/2} ≤ 12 ε |L|, then (1/2 − ε)|L| ≤ deg ≤ |L|/2 and the greedy
      assignment is a 1/(1 − 2ε)-approximation.
-/
import PauliContextuality.Transfer

open Matrix

namespace PauliCtx.Spectral

open Config

variable {N N' : ℕ}

/-! ### DEN-1 -/

/-- the ASY-2 deficit written as `n^{3/2}(d − 2)/(12 √(d − 1))` -/
theorem deficit_eq (n d : ℝ) (hn : 0 < n) (hd : 2 ≤ d) :
    (Real.sqrt (n * (d - 1)) * (d * n) - (d * n) ^ 2 / (d * Real.sqrt (n * (d - 1)))) / (12 * d) =
      n * Real.sqrt n * (d - 2) / (12 * Real.sqrt (d - 1)) := by
  have hd1 : 0 < d - 1 := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsd : 0 < Real.sqrt (d - 1) := Real.sqrt_pos.2 hd1
  have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hsd2 : Real.sqrt (d - 1) ^ 2 = d - 1 := Real.sq_sqrt hd1.le
  rw [Real.sqrt_mul hn.le]
  have hdpos : 0 < d := by linarith
  field_simp
  rw [hsn2, hsd2]; ring

/-- **DEN-1.** deg X ≥ |L_X|/2 − n^{3/2}(2^N − 2)/(12√(2^N − 1)). -/
theorem den1 (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N) :
    ((configX X h0).lines.card : ℝ) / 2 -
        (X.card : ℝ) * Real.sqrt X.card * (2 ^ N - 2) / (12 * Real.sqrt (2 ^ N - 1)) ≤
      (configX X h0).deg := by
  have h := spectral_lower X h0 hX hN
  simp only at h
  have hd2 : (2 : ℝ) ≤ 2 ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hn : (0 : ℝ) < X.card := by exact_mod_cast Finset.card_pos.2 hX
  rwa [deficit_eq _ _ hn hd2] at h

/-- `(d − 2)/√(d − 1) ≤ √d` for `d ≥ 2` -/
theorem ratio_le_sqrt (d : ℝ) (hd : 2 ≤ d) : (d - 2) / Real.sqrt (d - 1) ≤ Real.sqrt d := by
  have hd1 : 0 < d - 1 := by linarith
  have hsd : 0 < Real.sqrt (d - 1) := Real.sqrt_pos.2 hd1
  rw [div_le_iff₀ hsd, ← Real.sqrt_mul (by linarith)]
  have h2 : d - 2 = Real.sqrt ((d - 2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
  rw [h2]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- **DEN-1 (weak form).** deg X ≥ |L_X|/2 − n^{3/2} 2^{N/2}/12. -/
theorem den1_weak (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N) :
    ((configX X h0).lines.card : ℝ) / 2 - (X.card : ℝ) * Real.sqrt X.card * Real.sqrt (2 ^ N) / 12 ≤
      (configX X h0).deg := by
  have h := den1 X h0 hX hN
  have hd2 : (2 : ℝ) ≤ 2 ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hr := ratio_le_sqrt _ hd2
  have hnn : 0 ≤ (X.card : ℝ) * Real.sqrt X.card := by positivity
  have : (X.card : ℝ) * Real.sqrt X.card * (2 ^ N - 2) / (12 * Real.sqrt (2 ^ N - 1)) ≤
      (X.card : ℝ) * Real.sqrt X.card * Real.sqrt (2 ^ N) / 12 := by
    rw [show (X.card : ℝ) * Real.sqrt X.card * (2 ^ N - 2) / (12 * Real.sqrt (2 ^ N - 1)) =
        (X.card : ℝ) * Real.sqrt X.card * ((2 ^ N - 2) / Real.sqrt (2 ^ N - 1)) / 12 by ring]
    gcongr
  linarith

/-- **DEN-1 (density form).** 1/2 − deg X/|L_X| ≤ 1/(12 D(X)), D(X) = |L_X|/(n^{3/2}2^{N/2}). -/
theorem den1_gap (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hN : 1 ≤ N)
    (hL : 0 < (configX X h0).lines.card) :
    1 / 2 - ((configX X h0).deg : ℝ) / (configX X h0).lines.card ≤
      (X.card : ℝ) * Real.sqrt X.card * Real.sqrt (2 ^ N) / (12 * (configX X h0).lines.card) := by
  have hX : X.Nonempty := by
    obtain ⟨l, hl⟩ := Finset.card_pos.1 hL
    obtain ⟨p, hp, -⟩ := Finset.mem_image.1 hl
    exact ⟨p.1, (mem_OP.1 hp).1⟩
  have h := den1_weak X h0 hX hN
  have hLr : (0 : ℝ) < (configX X h0).lines.card := by exact_mod_cast hL
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 12 * (configX X h0).lines.card)]
  have : (1 / 2 - ((configX X h0).deg : ℝ) / (configX X h0).lines.card) *
      (12 * (configX X h0).lines.card) = 6 * (configX X h0).lines.card - 12 * (configX X h0).deg := by
    field_simp; ring
  rw [this]
  linarith

/-! ### DEN-1′: transport along an ω-preserving embedding -/

/-- a configuration pulled back from an induced configuration along an embedding is Pauli-realised
by that embedding -/
theorem real_comap_configX {α : Type} [Fintype α] [DecidableEq α] {Y : Finset (V N)}
    (h0 : (0 : V N) ∉ Y) (e : α ↪ V N) (L : Finset (Finset α))
    (hL : ∀ l ∈ L, l.map e ∈ (configX Y h0).lines) :
    PauliRealization ((configX Y h0).comap e L hL) e := by
  refine ⟨e.injective, fun l hl => ?_⟩
  obtain ⟨p, hp, hpl⟩ := Finset.mem_image.1 (hL l hl)
  have hline := isLine_of_OP h0 hp
  have mem : ∀ x ∈ tri p, ∃ y ∈ l, e y = x := fun x hx => by
    rw [hpl] at hx; simpa using hx
  obtain ⟨a, ha, hea⟩ := mem p.1 (by simp [tri])
  obtain ⟨b, hb, heb⟩ := mem p.2 (by simp [tri])
  obtain ⟨c, hc, hec⟩ := mem (p.1 + p.2) (by simp [tri])
  have hl' : l = {a, b, c} := by
    apply Finset.map_injective e
    rw [← hpl]
    simp [tri, Finset.map_insert, hea, heb, hec]
  refine ⟨a, b, c, hl', ?_, ?_⟩
  · rw [hea, heb, hec]; exact hline
  · show (configX Y h0).sign (l.map e) = _
    rw [← hpl, configX_sign h0 hp, hea, heb, hec]
    exact sgnF_eq_sign hline

/-- the subtype of the points of `X` -/
abbrev PtX (X : Finset (V N)) := {x // x ∈ X}

/-- the lines of `configX X`, as subsets of the point subtype -/
noncomputable def linesSub (X : Finset (V N)) (h0 : (0 : V N) ∉ X) : Finset (Finset (PtX X)) :=
  (configX X h0).lines.image (fun l => l.subtype (· ∈ X))

theorem lines_sub_X {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {l : Finset (V N)}
    (hl : l ∈ (configX X h0).lines) : ∀ x ∈ l, x ∈ X := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
  obtain ⟨h1, h2, -, h3⟩ := mem_OP.1 hp
  intro x hx
  simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem map_linesSub {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {l : Finset (V N)}
    (hl : l ∈ (configX X h0).lines) : (l.subtype (· ∈ X)).map (Function.Embedding.subtype _) = l :=
  Finset.subtype_map_of_mem (lines_sub_X h0 hl)

variable (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (φ : V N →ₗ[F] V N')
  (hω : ∀ a ∈ X, ∀ b ∈ X, omega (φ a) (φ b) = omega a b)
  (hinj : Set.InjOn φ (Submodule.span F (X : Set (V N))))

include hinj in
theorem injOn_X : Set.InjOn φ (X : Set (V N)) :=
  hinj.mono Submodule.subset_span

include h0 hinj in
theorem zero_not_mem_image : (0 : V N') ∉ X.image φ := by
  intro h
  obtain ⟨a, ha, hφa⟩ := Finset.mem_image.1 h
  have : a = 0 := hinj (Submodule.subset_span ha) (Submodule.zero_mem _) (by rw [hφa, map_zero])
  exact h0 (this ▸ ha)

/-- the embedding of the point subtype through φ -/
noncomputable def embφ : PtX X ↪ V N' :=
  ⟨fun x => φ x.1, fun x y h => Subtype.ext (injOn_X X φ hinj x.2 y.2 h)⟩

include hω hinj in
/-- the lines of `configX (φ X)` are exactly the images of the lines of `configX X` -/
theorem lines_image (h0' : (0 : V N') ∉ X.image φ) :
    (configX (X.image φ) h0').lines = (linesSub X h0).image (fun l => l.map (embφ X φ hinj)) := by
  have hmapl : ∀ l ∈ (configX X h0).lines,
      (l.subtype (· ∈ X)).map (embφ X φ hinj) = l.image φ := by
    intro l hl
    ext y
    simp only [Finset.mem_map, Finset.mem_image, Finset.mem_subtype, embφ,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨x, hx⟩, hxl, rfl⟩; exact ⟨x, hxl, rfl⟩
    · rintro ⟨x, hxl, rfl⟩; exact ⟨⟨x, lines_sub_X h0 hl x hxl⟩, hxl, rfl⟩
  ext m
  constructor
  · intro hm
    obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨h1, h2, hωq, h3⟩ := mem_OP.1 hq
    simp only at h1 h2 hωq h3
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h2
    obtain ⟨c, hc, hcab⟩ := Finset.mem_image.1 h3
    have hab : a + b = c := by
      refine hinj (Submodule.add_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb))
        (Submodule.subset_span hc) ?_
      rw [map_add, hcab]
    have hp : (a, b) ∈ OP X := mem_OP.2 ⟨ha, hb, by rw [← hω a ha b hb]; exact hωq, hab ▸ hc⟩
    have hl : tri (a, b) ∈ (configX X h0).lines := Finset.mem_image_of_mem _ hp
    refine Finset.mem_image.2 ⟨(tri (a, b)).subtype (· ∈ X), Finset.mem_image_of_mem _ hl, ?_⟩
    rw [hmapl _ hl]
    simp [tri, Finset.image_insert, map_add]
  · intro hm
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hl'
    rw [hmapl _ hl]
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨h1, h2, hωp, h3⟩ := mem_OP.1 hp
    have hq : (φ p.1, φ p.2) ∈ OP (X.image φ) :=
      mem_OP.2 ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2,
        by rw [hω _ h1 _ h2]; exact hωp,
        by rw [← map_add]; exact Finset.mem_image_of_mem _ h3⟩
    refine Finset.mem_image.2 ⟨_, hq, ?_⟩
    simp [tri, Finset.image_insert, map_add]

theorem lines_eq_linesSub :
    (configX X h0).lines = (linesSub X h0).image (fun l => l.map (Function.Embedding.subtype _)) := by
  unfold linesSub
  rw [Finset.image_image]
  exact ((Finset.image_congr (g := id) fun l hl => map_linesSub h0 hl).trans Finset.image_id).symm

include hω hinj in
/-- **DEN-1′ (invariance).** If φ : V N → V N' preserves ω on X and is injective on span X, then the
induced configurations of X and of φ(X) have the same degree. -/
theorem deg_configX_map (h0' : (0 : V N') ∉ X.image φ) :
    (configX (X.image φ) h0').deg = (configX X h0).deg := by
  have hD₁ := lines_eq_linesSub X h0
  have hD₂ := lines_image X h0 φ hω hinj h0'
  have hm₁ : ∀ l ∈ linesSub X h0, l.map (Function.Embedding.subtype _) ∈ (configX X h0).lines :=
    fun l hl => by rw [hD₁]; exact Finset.mem_image_of_mem _ hl
  have hm₂ : ∀ l ∈ linesSub X h0, l.map (embφ X φ hinj) ∈ (configX (X.image φ) h0').lines :=
    fun l hl => by rw [hD₂]; exact Finset.mem_image_of_mem _ hl
  rw [← deg_comap _ _ _ hm₁ hD₁, ← deg_comap _ _ _ hm₂ hD₂]
  symm
  exact deg_invariant _ _ _ _ (real_comap_configX h0 _ _ hm₁) (real_comap_configX h0' _ _ hm₂) rfl
    (fun p q => hω p.1 p.2 q.1 q.2)

include hω hinj in
theorem card_lines_configX_map (h0' : (0 : V N') ∉ X.image φ) :
    (configX (X.image φ) h0').lines.card = (configX X h0).lines.card := by
  rw [lines_image X h0 φ hω hinj h0', lines_eq_linesSub X h0,
    Finset.card_image_of_injective _ (Finset.map_injective _),
    Finset.card_image_of_injective _ (Finset.map_injective _)]

include hinj in
theorem card_image_X : (X.image φ).card = X.card :=
  Finset.card_image_of_injOn (injOn_X X φ hinj)

include hω hinj in
/-- **DEN-1 with the intrinsic qubit number.** If X embeds ω-isometrically (injectively on its span)
into N' qubits, DEN-1 holds with N' in place of N. -/
theorem den1_embed (hX : X.Nonempty) (hN' : 1 ≤ N') :
    ((configX X h0).lines.card : ℝ) / 2 -
        (X.card : ℝ) * Real.sqrt X.card * (2 ^ N' - 2) / (12 * Real.sqrt (2 ^ N' - 1)) ≤
      (configX X h0).deg := by
  have h0' := zero_not_mem_image X h0 φ hinj
  have h := den1 (X.image φ) h0' (hX.image φ) hN'
  rwa [deg_configX_map X h0 φ hω hinj h0', card_lines_configX_map X h0 φ hω hinj h0',
    card_image_X X φ hinj] at h

include hω hinj in
theorem den1_embed_weak (hX : X.Nonempty) (hN' : 1 ≤ N') :
    ((configX X h0).lines.card : ℝ) / 2 - (X.card : ℝ) * Real.sqrt X.card * Real.sqrt (2 ^ N') / 12 ≤
      (configX X h0).deg := by
  have h0' := zero_not_mem_image X h0 φ hinj
  have h := den1_weak (X.image φ) h0' (hX.image φ) hN'
  rwa [deg_configX_map X h0 φ hω hinj h0', card_lines_configX_map X h0 φ hω hinj h0',
    card_image_X X φ hinj] at h

end PauliCtx.Spectral

/-! ### DEN-2: the method of conditional expectations (any configuration) -/

namespace PauliCtx.Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-- the expected number of violated lines when the points of `T` are fixed by `s` and the other
points are uniform: lines inside `T` count 0/1, every other line counts 1/2 -/
def condExp (C : Config α) (T : Finset α) (s : α → F) : ℚ :=
  ∑ l ∈ C.lines, if l ⊆ T then (if C.Violated s l then 1 else 0) else 1 / 2

theorem condExp_univ (C : Config α) (s : α → F) : C.condExp Finset.univ s = (C.violated s).card := by
  unfold condExp violated
  rw [Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun l _ => by rw [if_pos (Finset.subset_univ l)]

theorem condExp_empty (C : Config α) (s : α → F) : C.condExp ∅ s = (C.lines.card : ℚ) / 2 := by
  unfold condExp
  rw [Finset.sum_congr rfl fun l hl => if_neg (fun h => ?_)]
  · rw [Finset.sum_const, nsmul_eq_mul]; ring
  · have := C.three l hl
    rw [Finset.subset_empty.1 h] at this
    simp at this

theorem violated_update_of_not_mem (C : Config α) (s : α → F) (p : α) (v : F) (l : Finset α)
    (hp : p ∉ l) : C.Violated (Function.update s p v) l ↔ C.Violated s l := by
  unfold Violated
  have : ∑ q ∈ l, Function.update s p v q = ∑ q ∈ l, s q :=
    Finset.sum_congr rfl fun q hq => Function.update_of_ne (fun h : q = p => hp (h ▸ hq)) v s
  rw [this]

omit [Fintype α] in
theorem update_one_eq_flip (s : α → F) (p : α) :
    Function.update s p 1 = flip p (Function.update s p 0) := by
  unfold flip
  simp

/-- **DEN-2, one step.** Averaging over the value of one more point. -/
theorem condExp_avg (C : Config α) (T : Finset α) (s : α → F) (p : α) (hp : p ∉ T) :
    C.condExp (insert p T) (Function.update s p 0) + C.condExp (insert p T) (Function.update s p 1) =
      2 * C.condExp T s := by
  unfold condExp
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hT : l ⊆ T
  · have hpl : p ∉ l := fun h => hp (hT h)
    simp only [if_pos (hT.trans (Finset.subset_insert _ _)), if_pos hT,
      violated_update_of_not_mem C s p 0 l hpl, violated_update_of_not_mem C s p 1 l hpl]
    split_ifs <;> norm_num
  · rw [if_neg hT]
    by_cases hT' : l ⊆ insert p T
    · have hpl : p ∈ l := by
        by_contra h
        exact hT fun x hx => (Finset.mem_insert.1 (hT' hx)).resolve_left (fun e => h (e ▸ hx))
      simp only [if_pos hT', update_one_eq_flip, violated_flip C l p hpl]
      split_ifs <;> norm_num
    · rw [if_neg hT', if_neg hT']; norm_num

/-- one greedy step: fix `p` to the value with the smaller conditional expectation -/
def greedyStep (C : Config α) (T : Finset α) (s : α → F) (p : α) : α → F :=
  if C.condExp (insert p T) (Function.update s p 0) ≤ C.condExp (insert p T) (Function.update s p 1)
  then Function.update s p 0 else Function.update s p 1

theorem greedyStep_le (C : Config α) (T : Finset α) (s : α → F) (p : α) (hp : p ∉ T) :
    C.condExp (insert p T) (C.greedyStep T s p) ≤ C.condExp T s := by
  have h := condExp_avg C T s p hp
  unfold greedyStep
  split_ifs with hle
  · linarith
  · push Not at hle; linarith

/-- the greedy assignment along an enumeration of the points (computable) -/
def greedy (C : Config α) : List α → Finset α → (α → F) → (α → F)
  | [], _, s => s
  | p :: ps, T, s => greedy C ps (insert p T) (C.greedyStep T s p)

theorem greedy_le (C : Config α) (ps : List α) :
    ∀ (T : Finset α) (s : α → F), ps.Nodup → (∀ p ∈ ps, p ∉ T) →
      C.condExp (T ∪ ps.toFinset) (C.greedy ps T s) ≤ C.condExp T s := by
  induction ps with
  | nil => intro T s _ _; simp [greedy]
  | cons p ps ih =>
    intro T s hnd hT
    rw [List.nodup_cons] at hnd
    have hpT : p ∉ T := hT p (List.mem_cons_self)
    have h1 := ih (insert p T) (C.greedyStep T s p) hnd.2 (fun q hq hqT => by
      rcases Finset.mem_insert.1 hqT with rfl | h
      · exact hnd.1 hq
      · exact hT q (List.mem_cons_of_mem _ hq) h)
    have h2 := greedyStep_le C T s p hpT
    have e : insert p T ∪ ps.toFinset = T ∪ (p :: ps).toFinset := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
      tauto
    simp only [greedy]
    rw [← e]
    linarith

/-- **DEN-2.** Along any enumeration of the points, the greedy (conditional-expectation)
assignment violates at most |L|/2 lines. -/
theorem greedy_half (C : Config α) (ps : List α) (hnd : ps.Nodup) (hall : ∀ p, p ∈ ps) (s : α → F) :
    2 * (C.violated (C.greedy ps ∅ s)).card ≤ C.lines.card := by
  have h := greedy_le C ps ∅ s hnd (fun _ _ h => Finset.notMem_empty _ h)
  have e : (∅ : Finset α) ∪ ps.toFinset = Finset.univ := by
    ext x; simp [hall x]
  rw [e, condExp_univ, condExp_empty] at h
  have : (2 * (C.violated (C.greedy ps ∅ s)).card : ℚ) ≤ C.lines.card := by linarith
  exact_mod_cast this

end PauliCtx.Config

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-- **DEN-2 (dense regime).** If n^{3/2} 2^{N/2} ≤ 12 ε |L_X| (i.e. D(X) ≥ 1/(12ε)), then
(1/2 − ε)|L_X| ≤ deg X ≤ |L_X|/2, and the greedy assignment s₀ satisfies (1 − 2ε)|V(s₀)| ≤ deg X,
i.e. it is a 1/(1−2ε)-approximation. -/
theorem den2 (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N) (ε : ℝ)
    (hdense : (X.card : ℝ) * Real.sqrt X.card * Real.sqrt (2 ^ N) ≤ 12 * ε * (configX X h0).lines.card)
    (ps : List (V N)) (hnd : ps.Nodup) (hall : ∀ p, p ∈ ps) (s : V N → F) :
    (1 / 2 - ε) * (configX X h0).lines.card ≤ (configX X h0).deg ∧
      2 * (configX X h0).deg ≤ (configX X h0).lines.card ∧
      (1 - 2 * ε) * ((configX X h0).violated ((configX X h0).greedy ps ∅ s)).card ≤
        (configX X h0).deg := by
  have h1 := den1_weak X h0 hX hN
  have hlow : (1 / 2 - ε) * (configX X h0).lines.card ≤ (configX X h0).deg := by linarith
  refine ⟨hlow, (configX X h0).deg_le_half, ?_⟩
  have hg := greedy_half (configX X h0) ps hnd hall s
  have hg' : (2 * ((configX X h0).violated ((configX X h0).greedy ps ∅ s)).card : ℝ) ≤
      (configX X h0).lines.card := by exact_mod_cast hg
  have hv : (0 : ℝ) ≤ ((configX X h0).violated ((configX X h0).greedy ps ∅ s)).card := by positivity
  have hd : (0 : ℝ) ≤ (configX X h0).deg := by positivity
  rcases le_or_gt 0 (1 - 2 * ε) with h2 | h2
  · have := mul_le_mul_of_nonneg_left hg' h2
    linarith
  · have := mul_nonpos_of_nonpos_of_nonneg h2.le hv
    linarith

end PauliCtx.Spectral
