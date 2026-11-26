/-
Cone.lean — CONE-1 (06_cones_sections.md): deg Cone_t(G) = 4^t · deg G.

Abstract formulation (no Pauli operators needed once signs are known): the cone on a base
configuration `G` (points `α`) has points `(v, τ)`, `v ∈ Option α` (`none` = the vertex), `τ ∈ F^t`, and
  (a) lifts      {(a,τ_a),(b,τ_b),(c,τ_c)}  for {a,b,c} ∈ L(G) and τ_a+τ_b+τ_c = 0 (base sign);
  (b) vertex lines {(v,τ),(v,τ'),(·,τ+τ')} for v ∈ α, τ ≠ τ' (sign 0);
  (c) lines inside the vertex {(·,τ),(·,τ'),(·,τ+τ')} (sign 0).

  * `cone_deg_le`  : deg Cone ≤ 4^t deg G (lift an optimal assignment, vertex gets 0).
  * `cone_deg_ge`  : deg Cone ≥ 4^t deg G, given a family of line-compatible maps φ_i : α → F^t
                     covering every lift uniformly (TR-1').
  * `cone_degree_pauli` : for a base configuration realised by Pauli labels in V n, the maps
                     p ↦ (ω(w_i, ι p))_i, W ∈ (V n)^t, form such a family (character sums), hence
                     deg Cone_t(G) = 4^t deg G.
-/
import PauliContextuality.SpectralW

namespace PauliCtx
namespace Config

variable {α : Type} [Fintype α] [DecidableEq α] (t : ℕ)

abbrev CP (α : Type) (t : ℕ) := Option α × (Fin t → F)

theorem add_self_fun (x : Fin t → F) : x + x = 0 := by ext i; exact add_self_F _

theorem third_fun {x y z : Fin t → F} (h : x + y + z = 0) : z = x + y := by
  ext i
  have := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  revert this; generalize x i = a; generalize y i = b; generalize z i = c
  revert a b c; decide

/-- the lift of a base line with heights `τ` -/
def lift (ℓ : Finset α) (τ : α → (Fin t → F)) : Finset (CP α t) := ℓ.image (fun p => (some p, τ p))

def liftsOf (ℓ : Finset α) : Finset (Finset (CP α t)) :=
  (Finset.univ.filter (fun τ : α → (Fin t → F) => ∑ p ∈ ℓ, τ p = 0)).image (lift t ℓ)

def lifts (G : Config α) : Finset (Finset (CP α t)) := G.lines.biUnion (liftsOf t)

def vlines : Finset (Finset (CP α t)) :=
  (((Finset.univ : Finset α) ×ˢ (Finset.univ : Finset ((Fin t → F) × (Fin t → F)))).filter
    (fun x => x.2.1 ≠ x.2.2)).image
    (fun x => {(some x.1, x.2.1), (some x.1, x.2.2), (none, x.2.1 + x.2.2)})

def ilines : Finset (Finset (CP α t)) :=
  ((Finset.univ : Finset ((Fin t → F) × (Fin t → F))).filter (fun x => x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.1 ≠ x.2)).image
    (fun x => {(none, x.1), (none, x.2), (none, x.1 + x.2)})

/-- the base points of a cone line -/
def proj (L : Finset (CP α t)) : Finset α := Finset.univ.filter (fun p => ∃ τ, (some p, τ) ∈ L)

theorem proj_lift (ℓ : Finset α) (τ : α → (Fin t → F)) : proj t (lift t ℓ τ) = ℓ := by
  ext p; simp [proj, lift]

theorem mem_lift {ℓ : Finset α} {τ : α → (Fin t → F)} {q : CP α t} :
    q ∈ lift t ℓ τ ↔ ∃ p ∈ ℓ, q = (some p, τ p) := by
  simp [lift, eq_comm]

theorem lift_eq {ℓ ℓ' : Finset α} {τ τ' : α → (Fin t → F)} (h : lift t ℓ τ = lift t ℓ' τ') :
    ℓ = ℓ' ∧ ∀ p ∈ ℓ, τ p = τ' p := by
  have hl : ℓ = ℓ' := by rw [← proj_lift t ℓ τ, h, proj_lift]
  refine ⟨hl, fun p hp => ?_⟩
  have : (some p, τ p) ∈ lift t ℓ' τ' := h ▸ (mem_lift t).2 ⟨p, hp, rfl⟩
  obtain ⟨p', _, hp'⟩ := (mem_lift t).1 this
  simp only [Prod.mk.injEq, Option.some.injEq] at hp'
  rw [hp'.2, hp'.1]

theorem card_lift (ℓ : Finset α) (τ : α → (Fin t → F)) : (lift t ℓ τ).card = ℓ.card :=
  Finset.card_image_of_injective _ (fun p q h => by simpa using congrArg Prod.fst h)

theorem sum_lift (ℓ : Finset α) (τ : α → (Fin t → F)) (s : CP α t → F) :
    ∑ q ∈ lift t ℓ τ, s q = ∑ p ∈ ℓ, s (some p, τ p) :=
  Finset.sum_image (fun p _ q _ h => by simpa using congrArg Prod.fst h)

theorem vline_not_lift {G : Config α} {L : Finset (CP α t)} (hL : L ∈ vlines t ∪ ilines t) :
    L ∉ lifts t G := by
  intro h
  simp only [lifts, liftsOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at h
  obtain ⟨ℓ, -, τ, -, rfl⟩ := h
  -- every vertex / in-vertex line contains a point `(none, _)`
  have : ∃ σ, ((none : Option α), σ) ∈ lift t ℓ τ := by
    rcases Finset.mem_union.1 hL with hv | hi
    · obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hv
      exact ⟨x.2.1 + x.2.2, by rw [← hx]; simp⟩
    · obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hi
      exact ⟨x.1, by rw [← hx]; simp⟩
  obtain ⟨σ, hσ⟩ := this
  obtain ⟨p, -, hp⟩ := (mem_lift t).1 hσ
  simp at hp

/-- The cone `Cone_t(G)`. -/
def cone (G : Config α) : Config (CP α t) where
  lines := lifts t G ∪ (vlines t ∪ ilines t)
  sign L := if L ∈ lifts t G then G.sign (proj t L) else 0
  three := by
    intro L hL
    rcases Finset.mem_union.1 hL with h | h
    · simp only [lifts, liftsOf, Finset.mem_biUnion, Finset.mem_image] at h
      obtain ⟨ℓ, hℓ, τ, -, rfl⟩ := h
      rw [card_lift, G.three ℓ hℓ]
    · rcases Finset.mem_union.1 h with hv | hi
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
        have hne : x.2.1 ≠ x.2.2 := (Finset.mem_filter.1 hx).2
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp
        · simp [hne]
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hx).2
        have e1 : x.1 ≠ x.1 + x.2 := fun h => h2 (by
          have := congrArg (x.1 + ·) h; simpa [← add_assoc, add_self_fun] using this.symm)
        have e2 : x.2 ≠ x.1 + x.2 := fun h => h1 (by
          have := congrArg (· + x.2) h; simpa [add_assoc, add_self_fun] using this.symm)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [e2]
        · simp [h3, e1]

theorem cone_sign_lift {G : Config α} {ℓ : Finset α} (hℓ : ℓ ∈ G.lines) {τ : α → (Fin t → F)}
    (hτ : ∑ p ∈ ℓ, τ p = 0) : (cone t G).sign (lift t ℓ τ) = G.sign ℓ := by
  have : lift t ℓ τ ∈ lifts t G := by
    simp only [lifts, liftsOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨ℓ, hℓ, τ, hτ, rfl⟩
  show (if lift t ℓ τ ∈ lifts t G then G.sign (proj t (lift t ℓ τ)) else 0) = G.sign ℓ
  rw [if_pos this, proj_lift]

/-! ### upper bound -/

theorem card_liftsOf_le {ℓ : Finset α} (h3 : ℓ.card = 3) : (liftsOf t ℓ).card ≤ 4 ^ t := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h3
  let τ0 : (Fin t → F) × (Fin t → F) → α → (Fin t → F) := fun xy p =>
    if p = a then xy.1 else if p = b then xy.2 else xy.1 + xy.2
  have hsub : liftsOf t {a, b, c} ⊆ (Finset.univ : Finset ((Fin t → F) × (Fin t → F))).image
      (fun xy => lift t {a, b, c} (τ0 xy)) := by
    intro L hL
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hL
    have hsum : τ a + τ b + τ c = 0 := by
      have := (Finset.mem_filter.1 hτ).2
      rwa [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton, ← add_assoc] at this
    have hc : τ c = τ a + τ b := third_fun t hsum
    refine Finset.mem_image.2 ⟨(τ a, τ b), Finset.mem_univ _, ?_⟩
    ext q
    simp only [lift, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      rcases hp with rfl | rfl | rfl
      · simp [τ0]
      · simp [τ0, Ne.symm hab]
      · simp [τ0, Ne.symm hac, Ne.symm hbc, hc]
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      rcases hp with rfl | rfl | rfl
      · simp [τ0]
      · simp [τ0, Ne.symm hab]
      · simp [τ0, Ne.symm hac, Ne.symm hbc, hc]
  calc (liftsOf t {a, b, c}).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin t → F) × (Fin t → F))).card := Finset.card_image_le
    _ = 4 ^ t := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
        ← mul_pow]
      norm_num

/-- CONE-1, upper bound. -/
theorem cone_deg_le (G : Config α) : (cone t G).deg ≤ 4 ^ t * G.deg := by
  obtain ⟨y, hy⟩ := G.exists_opt
  let s : CP α t → F := fun q => match q.1 with
    | some p => y p
    | none => 0
  have hsub : (cone t G).violated s ⊆ (G.violated y).biUnion (liftsOf t) := by
    intro L hL
    simp only [violated, Finset.mem_filter] at hL
    obtain ⟨hmem, hv⟩ := hL
    rcases Finset.mem_union.1 hmem with hl | hvi
    · simp only [lifts, Finset.mem_biUnion] at hl
      obtain ⟨ℓ, hℓ, hL'⟩ := hl
      refine Finset.mem_biUnion.2 ⟨ℓ, ?_, hL'⟩
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hL'
      refine Finset.mem_filter.2 ⟨hℓ, ?_⟩
      unfold Violated at hv ⊢
      rw [sum_lift, cone_sign_lift t hℓ (Finset.mem_filter.1 hτ).2] at hv
      exact hv
    · exfalso
      apply hv
      have hns := vline_not_lift (G := G) t hvi
      show (∑ q ∈ L, s q) + (if L ∈ lifts t G then G.sign (proj t L) else 0) = 0
      rw [if_neg hns, add_zero]
      rcases Finset.mem_union.1 hvi with hv' | hi
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv'
        have hne : x.2.1 ≠ x.2.2 := (Finset.mem_filter.1 hx).2
        rw [Finset.sum_insert (by simp [hne]), Finset.sum_insert (by simp), Finset.sum_singleton]
        simp [s, add_self_F]
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
        refine Finset.sum_eq_zero fun q hq => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl <;> rfl
  calc (cone t G).deg ≤ ((cone t G).violated s).card := deg_le _ _
    _ ≤ ((G.violated y).biUnion (liftsOf t)).card := Finset.card_le_card hsub
    _ ≤ ∑ ℓ ∈ G.violated y, (liftsOf t ℓ).card := Finset.card_biUnion_le
    _ ≤ ∑ _ℓ ∈ G.violated y, 4 ^ t := Finset.sum_le_sum fun ℓ hℓ =>
        card_liftsOf_le t (G.three ℓ (Finset.mem_filter.1 hℓ).1)
    _ = 4 ^ t * G.deg := by rw [Finset.sum_const, smul_eq_mul, hy, mul_comm]

/-! ### lower bound -/

/-- CONE-1, lower bound (TR-1' with the copies Σ_φ). -/
theorem cone_deg_ge (G : Config α) {ι : Type} [Fintype ι] (φ : ι → α → (Fin t → F)) (c : ℕ)
    (hc : 0 < c)
    (hlin : ∀ i, ∀ ℓ ∈ G.lines, ∑ p ∈ ℓ, φ i p = 0)
    (hcov : ∀ ℓ ∈ G.lines, ∀ τ : α → (Fin t → F),
      (Finset.univ.filter (fun i => ∀ p ∈ ℓ, φ i p = τ p)).card ≤ c)
    (hsize : Fintype.card ι = 4 ^ t * c) :
    4 ^ t * G.deg ≤ (cone t G).deg := by
  obtain ⟨s, hs⟩ := (cone t G).exists_opt
  set V := (cone t G).violated s
  let Sg : ι → Finset (Finset (CP α t)) := fun i => G.lines.image (fun ℓ => lift t ℓ (φ i))
  -- each copy carries at least deg G violations
  have hdeg : ∀ i, G.deg ≤ (V ∩ Sg i).card := by
    intro i
    let si : α → F := fun p => s (some p, φ i p)
    have : V ∩ Sg i = (G.violated si).image (fun ℓ => lift t ℓ (φ i)) := by
      ext L
      simp only [V, Sg, violated, Finset.mem_inter, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨-, hv⟩, ℓ, hℓ, rfl⟩
        refine ⟨ℓ, ⟨hℓ, ?_⟩, rfl⟩
        unfold Violated at hv ⊢
        rwa [sum_lift, cone_sign_lift t hℓ (hlin i ℓ hℓ)] at hv
      · rintro ⟨ℓ, ⟨hℓ, hv⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, ℓ, hℓ, rfl⟩
        · refine Finset.mem_union.2 (Or.inl ?_)
          simp only [lifts, liftsOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact ⟨ℓ, hℓ, φ i, hlin i ℓ hℓ, rfl⟩
        · unfold Violated at hv ⊢
          rwa [sum_lift, cone_sign_lift t hℓ (hlin i ℓ hℓ)]
    rw [this, Finset.card_image_of_injOn (fun ℓ _ ℓ' _ h => (lift_eq t h).1)]
    exact G.deg_le si
  -- coverage
  have hcov' : ∀ L ∈ V, (Finset.univ.filter (fun i => L ∈ Sg i)).card ≤ c := by
    intro L _
    by_cases hL : ∃ i, L ∈ Sg i
    · obtain ⟨i0, hi0⟩ := hL
      obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hi0
      refine le_trans (Finset.card_le_card ?_) (hcov ℓ hℓ (φ i0))
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sg, Finset.mem_image] at hi ⊢
      obtain ⟨ℓ', _, h⟩ := hi
      obtain ⟨e, he⟩ := lift_eq t h
      subst e
      exact he
    · push Not at hL
      rw [Finset.filter_false_of_mem (fun i _ => hL i)]
      simp
  have key := sum_inter_le (Finset.univ : Finset ι) Sg V c hcov'
  have hlow : Fintype.card ι * G.deg ≤ ∑ i, (V ∩ Sg i).card := by
    rw [Fintype.card, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => hdeg i
  rw [hsize] at hlow
  have : c * (4 ^ t * G.deg) ≤ c * V.card := by nlinarith
  rw [← hs]
  exact Nat.le_of_mul_le_mul_left this hc

/-- CONE-1 (abstract form). -/
theorem cone_degree (G : Config α) {ι : Type} [Fintype ι] (φ : ι → α → (Fin t → F)) (c : ℕ)
    (hc : 0 < c) (hlin : ∀ i, ∀ ℓ ∈ G.lines, ∑ p ∈ ℓ, φ i p = 0)
    (hcov : ∀ ℓ ∈ G.lines, ∀ τ : α → (Fin t → F),
      (Finset.univ.filter (fun i => ∀ p ∈ ℓ, φ i p = τ p)).card ≤ c)
    (hsize : Fintype.card ι = 4 ^ t * c) :
    (cone t G).deg = 4 ^ t * G.deg :=
  le_antisymm (cone_deg_le t G) (cone_deg_ge t G φ c hc hlin hcov hsize)

end Config

/-! ### Pauli realisation: the family of linear maps p ↦ (ω(w_i, p))_i -/

open Spectral

variable {n : ℕ}

theorem omega_sum_right {β : Type} (p : V n) (s : Finset β) (f : β → V n) :
    omega p (∑ x ∈ s, f x) = ∑ x ∈ s, omega p (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [omega]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, omega_add_right, ih]

theorem indicator_eq (t : F) : ((if t = 0 then 1 else 0 : ℕ) : ℂ) * 2 = 1 + iPow (dbl t) := by
  rw [Spectral.one_add_iPow_dbl]; split_ifs <;> norm_num

/-- `#{w : ω(w,u) = x ∧ ω(w,v) = y} = 4^(n−1)` for `u, v, u+v ≠ 0`. -/
theorem card_omega_two {u v : V n} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (x y : F) :
    4 * (Finset.univ.filter (fun w : V n => omega w u = x ∧ omega w v = y)).card = 4 ^ n := by
  have huv' : u + v ≠ 0 := by
    intro h; apply huv; have := congrArg (· + v) h; simpa [add_assoc, add_self_V] using this
  have hc : ∀ a : V n, a ≠ 0 → ∑ w : V n, iPow (dbl (omega w a)) = 0 := by
    intro a ha
    simp_rw [omega_comm _ a]
    exact sum_char_omega ha
  have key : (4 : ℂ) * (Finset.univ.filter (fun w : V n => omega w u = x ∧ omega w v = y)).card =
      ∑ w : V n, (1 + iPow (dbl (omega w u + x))) * (1 + iPow (dbl (omega w v + y))) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← indicator_eq, ← indicator_eq]
    have e1 : (omega w u = x) ↔ (omega w u + x = 0) := by
      constructor
      · intro h; rw [h, add_self_F]
      · intro h; have := congrArg (· + x) h; simpa [add_assoc, add_self_F] using this
    have e2 : (omega w v = y) ↔ (omega w v + y = 0) := by
      constructor
      · intro h; rw [h, add_self_F]
      · intro h; have := congrArg (· + y) h; simpa [add_assoc, add_self_F] using this
    by_cases h1 : omega w u + x = 0 <;> by_cases h2 : omega w v + y = 0 <;>
      simp [h1, h2, e1, e2] <;> norm_num
  have hexp : ∑ w : V n, (1 + iPow (dbl (omega w u + x))) * (1 + iPow (dbl (omega w v + y))) =
      (4 ^ n : ℂ) + iPow (dbl x) * ∑ w : V n, iPow (dbl (omega w u)) +
        iPow (dbl y) * ∑ w : V n, iPow (dbl (omega w v)) +
        iPow (dbl (x + y)) * ∑ w : V n, iPow (dbl (omega w (u + v))) := by
    have h4 : (4 ^ n : ℂ) = ∑ _w : V n, (1 : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, card_V, nsmul_eq_mul, mul_one]; push_cast; ring
    rw [h4, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [omega_add_right, dbl_add, iPow_add]
    ring
  rw [hexp, hc u hu, hc v hv, hc (u + v) huv'] at key
  simp only [mul_zero, add_zero] at key
  exact_mod_cast key

/-- CONE-1 for a Pauli-realised base configuration. -/
theorem cone_degree_pauli {α : Type} [Fintype α] [DecidableEq α] (t : ℕ) (G : Config α) (hn : 1 ≤ n)
    (ι0 : α → V n) (hsum : ∀ ℓ ∈ G.lines, ∑ p ∈ ℓ, ι0 p = 0)
    (hind : ∀ ℓ ∈ G.lines, ∀ a ∈ ℓ, ∀ b ∈ ℓ, a ≠ b → ι0 a ≠ ι0 b ∧ ι0 a ≠ 0 ∧ ι0 b ≠ 0) :
    (Config.cone t G).deg = 4 ^ t * G.deg := by
  let φ : (Fin t → V n) → α → (Fin t → F) := fun W p i => omega (W i) (ι0 p)
  refine Config.cone_degree t G φ ((4 ^ (n - 1)) ^ t) (by positivity) ?_ ?_ ?_
  · intro W ℓ hℓ
    ext i
    simp only [φ, Finset.sum_apply, Pi.zero_apply]
    rw [← omega_sum_right, hsum ℓ hℓ]
    simp [omega]
  · intro ℓ hℓ τ
    obtain ⟨a, b, c, hab, hac, hbc, hl⟩ := Finset.card_eq_three.1 (G.three ℓ hℓ)
    have ha : a ∈ ℓ := by rw [hl]; simp
    have hb : b ∈ ℓ := by rw [hl]; simp
    obtain ⟨h1, h2, h3⟩ := hind ℓ hℓ a ha b hb hab
    calc (Finset.univ.filter (fun W => ∀ p ∈ ℓ, φ W p = τ p)).card
        ≤ (Finset.univ.filter (fun W : Fin t → V n => ∀ i, omega (W i) (ι0 a) = τ a i ∧
            omega (W i) (ι0 b) = τ b i)).card := by
          apply Finset.card_le_card
          intro W hW
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
          intro i
          exact ⟨congrFun (hW a ha) i, congrFun (hW b hb) i⟩
      _ = ∏ i : Fin t, (Finset.univ.filter (fun w : V n => omega w (ι0 a) = τ a i ∧
            omega w (ι0 b) = τ b i)).card := by
          rw [← Fintype.card_piFinset]
          congr 1
          ext W
          simp [Fintype.mem_piFinset]
      _ = ∏ _i : Fin t, 4 ^ (n - 1) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          have := card_omega_two h2 h3 h1 (τ a i) (τ b i)
          have e : 4 ^ n = 4 * 4 ^ (n - 1) := by
            rw [← pow_succ']; congr 1; omega
          omega
      _ = (4 ^ (n - 1)) ^ t := by simp
  · rw [Fintype.card_fun, card_V, Fintype.card_fin, ← mul_pow]
    congr 1
    rw [← pow_succ']; congr 1; omega

end PauliCtx
