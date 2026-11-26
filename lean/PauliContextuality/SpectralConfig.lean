/-
SpectralConfig.lean — the induced configuration of a label set X and the spectral lower bound on its
degree (ASY-1 in line form, ASY-2).

  * `configX X`     : the configuration whose lines are all commuting triples {a, b, a+b} ⊆ X,
                      with the Pauli-product sign.
  * `six_mul_card`  : every line comes from exactly 6 ordered commuting pairs.
  * `trace_cube_viol` : tr M_g³ = 2^N (6|L| − 12|V(s)|)   for g = (−1)^s.  (ASY-1)
  * `spectral_lower`  : deg ≥ |L|/2 − (ΛF − F²/(dΛ))/(12d).                (ASY-2)
-/
import PauliContextuality.Spectral
import PauliContextuality.Bounds

open Matrix Complex

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-- the point set of the ordered pair `(a, b)` -/
def tri (p : V N × V N) : Finset (V N) := {p.1, p.2, p.1 + p.2}

/-- ordered commuting pairs spanning a line of X -/
def OP (X : Finset (V N)) : Finset (V N × V N) :=
  (X ×ˢ X).filter (fun p => omega p.1 p.2 = 0 ∧ p.1 + p.2 ∈ X)

/-- the sign bit of an ordered commuting pair -/
def sgnF (p : V N × V N) : F := if ph p.1 p.2 = 0 then 0 else 1

/-- `(−1)^x` -/
def pm (x : F) : ℤ := if x = 0 then 1 else -1

theorem pm_add (x y : F) : pm (x + y) = pm x * pm y := by
  revert x y; decide

theorem chi_eq_pm (p : V N × V N) : chi p.1 p.2 = pm (sgnF p) := by
  unfold chi pm sgnF; split_ifs <;> simp_all

theorem mem_OP {X : Finset (V N)} {p : V N × V N} :
    p ∈ OP X ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ omega p.1 p.2 = 0 ∧ p.1 + p.2 ∈ X := by
  simp [OP, and_assoc]

theorem add_cancel_left' (a b : V N) : a + (a + b) = b := by
  rw [← add_assoc, add_self_V, zero_add]

theorem add_cancel_right' (a b : V N) : a + b + b = a := by
  rw [add_assoc, add_self_V, add_zero]

/-- a pair of `OP X` spans a line in the sense of Basic.lean -/
theorem isLine_of_OP {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {p : V N × V N} (hp : p ∈ OP X) :
    IsLine p.1 p.2 (p.1 + p.2) := by
  rw [mem_OP] at hp
  obtain ⟨ha, hb, hω, hc⟩ := hp
  have nz : ∀ x ∈ X, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  refine ⟨?_, ?_, ?_, nz _ ha, nz _ hb, nz _ hc, ?_, hω⟩
  · intro h; apply nz _ hc; rw [h, add_self_V]
  · intro h; apply nz _ hb; have := congrArg (p.1 + ·) h; simpa [add_cancel_left', add_self_V] using this.symm
  · intro h; apply nz _ ha; have := congrArg (· + p.2) h; simpa [add_cancel_right', add_self_V] using this.symm
  · exact add_self_V _

/-- all six orderings of a line have the same `signK` -/
theorem signK_perm {a b c : V N} (h : IsLine a b c) :
    signK b a c = signK a b c ∧ signK a c b = signK a b c ∧ signK b c a = signK a b c ∧
    signK c a b = signK a b c ∧ signK c b a = signK a b c := by
  have e1 := signK_swap12 h
  have e2 := signK_swap23 h
  have e3 := signK_swap23 h.swap12
  have e4 := signK_swap12 h.swap23
  have e5 := signK_swap23 h.swap23.swap12
  refine ⟨e1.symm, e2.symm, ?_, ?_, ?_⟩
  · rw [← e3, ← e1]
  · rw [← e4, ← e2]
  · rw [← e5, ← e4, ← e2]

theorem third_of_line {a b c : V N} (h : IsLine a b c) : a + b = c := (third_eq h.sum_zero).symm

theorem sum_eq_third {a b c : V N} (h : IsLine a b c) :
    b + a = c ∧ a + c = b ∧ c + a = b ∧ b + c = a ∧ c + b = a := by
  have hc := third_eq h.sum_zero
  subst hc
  refine ⟨add_comm b a, add_cancel_left' a b, ?_, ?_, add_cancel_right' a b⟩
  · rw [add_comm, add_cancel_left']
  · rw [add_comm a b, add_cancel_left']

/-- The fiber of `tri` over the line of `p` consists of the 6 orderings. -/
theorem fiber_eq {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {p : V N × V N} (hp : p ∈ OP X) :
    (OP X).filter (fun q => tri q = tri p) =
      {(p.1, p.2), (p.2, p.1), (p.1, p.1 + p.2), (p.1 + p.2, p.1), (p.2, p.1 + p.2),
        (p.1 + p.2, p.2)} := by
  have hl := isLine_of_OP h0 hp
  obtain ⟨e1, e2, e3, e4, e5⟩ := sum_eq_third hl
  have hp' := mem_OP.1 hp
  obtain ⟨ha, hb, hω, hc⟩ := hp'
  set a := p.1; set b := p.2
  have hl12 := hl.swap12; have hl23 := hl.swap23
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, ht⟩
    have hql := isLine_of_OP h0 hq
    have m1 : q.1 ∈ tri p := ht ▸ (by simp [tri])
    have m2 : q.2 ∈ tri p := ht ▸ (by simp [tri])
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at m1 m2
    have hne := hql.ne_ab
    rcases m1 with h1 | h1 | h1 <;> rcases m2 with h2 | h2 | h2
    all_goals first
      | exact absurd (h1.trans h2.symm) hne
      | (left; exact Prod.ext h1 h2)
      | (right; left; exact Prod.ext h1 h2)
      | (right; right; left; exact Prod.ext h1 h2)
      | (right; right; right; left; exact Prod.ext h1 h2)
      | (right; right; right; right; left; exact Prod.ext h1 h2)
      | (right; right; right; right; right; exact Prod.ext h1 h2)
  · have hω' : ∀ x y : V N, omega x y = 0 → omega y x = 0 := fun x y h => by rw [omega_comm]; exact h
    have hac : omega a (a + b) = 0 := hl23.comm
    have hbc : omega b (a + b) = 0 := hl.swap12.swap23.comm
    have tri_eq : ∀ x y : V N, ({x, y, x + y} : Finset (V N)) = {a, b, a + b} →
        tri (x, y) = tri p := fun x y h => h
    rintro (h | h | h | h | h | h) <;> subst h <;> refine ⟨?_, ?_⟩
    · exact hp
    · rfl
    · exact mem_OP.2 ⟨hb, ha, hω' _ _ hω, by rw [e1]; exact hc⟩
    · apply tri_eq; simp only [e1]; ext x; simp; tauto
    · exact mem_OP.2 ⟨ha, hc, hac, by rw [e2]; exact hb⟩
    · apply tri_eq; simp only [e2]; ext x; simp; tauto
    · exact mem_OP.2 ⟨hc, ha, hω' _ _ hac, by rw [e3]; exact hb⟩
    · apply tri_eq; simp only [e3]; ext x; simp; tauto
    · exact mem_OP.2 ⟨hb, hc, hbc, by rw [e4]; exact ha⟩
    · apply tri_eq; simp only [e4]; ext x; simp; tauto
    · exact mem_OP.2 ⟨hc, hb, hω' _ _ hbc, by rw [e5]; exact ha⟩
    · apply tri_eq; simp only [e5]; ext x; simp; tauto

theorem card_fiber {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {p : V N × V N} (hp : p ∈ OP X) :
    ((OP X).filter (fun q => tri q = tri p)).card = 6 := by
  rw [fiber_eq h0 hp]
  have hl := isLine_of_OP h0 hp
  have h1 := hl.ne_ab; have h2 := hl.ne_ac; have h3 := hl.ne_bc
  have h2' := h2.symm; have h3' := h3.symm; have h1' := h1.symm
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
  simp [Prod.ext_iff, h1, h2, h3, h1', h2', h3']

/-- the sign bit is constant on fibers -/
theorem sgnF_fiber {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {p q : V N × V N} (hp : p ∈ OP X)
    (hq : q ∈ (OP X).filter (fun q => tri q = tri p)) : sgnF q = sgnF p := by
  rw [fiber_eq h0 hp] at hq
  have hl := isLine_of_OP h0 hp
  obtain ⟨e1, e2, e3, e4, e5⟩ := sum_eq_third hl
  obtain ⟨f1, f2, f3, f4, f5⟩ := signK_perm hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  unfold sgnF
  rcases hq with h | h | h | h | h | h <;> subst h <;> simp only [ph_eq_signK]
  · rw [e1, f1]
  · rw [e2, f2]
  · rw [e3, f4]
  · rw [e4, f3]
  · rw [e5, f5]

/-- the configuration induced on `X` -/
noncomputable def configX (X : Finset (V N)) (h0 : (0 : V N) ∉ X) : Config (V N) where
  lines := (OP X).image tri
  sign := fun l => if h : ∃ p ∈ OP X, tri p = l then sgnF (Classical.choose h) else 0
  three := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
    have hl := isLine_of_OP h0 hp
    simp [tri, Finset.card_insert_of_notMem, hl.ne_ab, hl.ne_ac, hl.ne_bc]

theorem configX_sign {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {p : V N × V N} (hp : p ∈ OP X) :
    (configX X h0).sign (tri p) = sgnF p := by
  have h : ∃ q ∈ OP X, tri q = tri p := ⟨p, hp, rfl⟩
  show (if h : ∃ q ∈ OP X, tri q = tri p then sgnF (Classical.choose h) else 0) = sgnF p
  rw [dif_pos h]
  obtain ⟨hq, hqt⟩ := Classical.choose_spec h
  exact sgnF_fiber h0 hp (Finset.mem_filter.2 ⟨hq, hqt⟩)

theorem sum_tri {X : Finset (V N)} (h0 : (0 : V N) ∉ X) {p : V N × V N} (hp : p ∈ OP X)
    (s : V N → F) : ∑ x ∈ tri p, s x = s p.1 + s p.2 + s (p.1 + p.2) := by
  have hl := isLine_of_OP h0 hp
  simp [tri, Finset.sum_insert, hl.ne_ab, hl.ne_ac, hl.ne_bc, add_assoc]

/-- violation of a pair -/
def violP (s : V N → F) (p : V N × V N) : Prop := s p.1 + s p.2 + s (p.1 + p.2) + sgnF p ≠ 0

instance (s : V N → F) (p : V N × V N) : Decidable (violP s p) := by unfold violP; infer_instance

/-- double counting through the 6-to-1 map `tri` -/
theorem sum_OP_eq {X : Finset (V N)} (h0 : (0 : V N) ∉ X) (f : Finset (V N) → ℕ) :
    ∑ p ∈ OP X, f (tri p) = 6 * ∑ l ∈ (OP X).image tri, f l := by
  rw [Finset.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
  rw [card_fiber h0 hp, smul_eq_mul]

theorem six_mul_card (X : Finset (V N)) (h0 : (0 : V N) ∉ X) :
    (OP X).card = 6 * (configX X h0).lines.card := by
  have := sum_OP_eq h0 (fun _ => 1)
  rw [show (configX X h0).lines = (OP X).image tri from rfl]
  simpa using this

theorem six_mul_viol (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (s : V N → F) :
    ((OP X).filter (violP s)).card = 6 * ((configX X h0).violated s).card := by
  have key := sum_OP_eq h0 (fun l => if (configX X h0).Violated s l then 1 else 0)
  have lhs : ∑ p ∈ OP X, (if (configX X h0).Violated s (tri p) then 1 else 0) =
      ((OP X).filter (violP s)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    have : (configX X h0).Violated s (tri p) ↔ violP s p := by
      unfold Violated violP
      rw [sum_tri h0 hp, configX_sign h0 hp]
    simp only [this]
  rw [lhs] at key
  rw [key, ← Finset.card_filter]
  rfl

/-- the ±1 version of an assignment -/
def gOf (s : V N → F) : V N → ℤ := fun a => pm (s a)

theorem gOf_pm (s : V N → F) : IsPM (gOf s) := by
  intro a; unfold gOf pm; split_ifs <;> simp

theorem chi_prod (s : V N → F) (p : V N × V N) :
    chi p.1 p.2 * gOf s p.1 * gOf s p.2 * gOf s (p.1 + p.2) = if violP s p then -1 else 1 := by
  unfold gOf
  rw [chi_eq_pm, ← pm_add, ← pm_add, ← pm_add]
  by_cases h : violP s p
  · rw [if_pos h]; unfold violP at h; unfold pm; rw [if_neg]; intro h'; apply h; rw [← h']; ring
  · rw [if_neg h]; unfold violP at h; push Not at h; unfold pm; rw [if_pos]; rw [← h]; ring

/-- ASY-1 in line form: tr M³ = 2^N (6|L| − 12|V(s)|). -/
theorem trace_cube_viol (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (s : V N → F) :
    (Mg X (gOf s) * Mg X (gOf s) * Mg X (gOf s)).trace =
      2 ^ N * (6 * ((configX X h0).lines.card : ℂ) - 12 * ((configX X h0).violated s).card) := by
  rw [trace_cube_comm]
  congr 1
  have : ∑ a ∈ X, ∑ b ∈ X, (if omega a b = 0 ∧ a + b ∈ X then
        ((chi a b * gOf s a * gOf s b * gOf s (a + b) : ℤ) : ℂ) else 0) =
      ∑ p ∈ OP X, ((chi p.1 p.2 * gOf s p.1 * gOf s p.2 * gOf s (p.1 + p.2) : ℤ) : ℂ) := by
    rw [OP, Finset.sum_filter, Finset.sum_product]
  rw [this]
  simp_rw [chi_prod]
  have h1 := six_mul_card X h0
  have h2 := six_mul_viol X h0 s
  have hsplit : ∑ p ∈ OP X, (((if violP s p then -1 else 1 : ℤ)) : ℂ) =
      (OP X).card - 2 * ((OP X).filter (violP s)).card := by
    have : ∀ p ∈ OP X, (((if violP s p then -1 else 1 : ℤ)) : ℂ) =
        1 - 2 * (if violP s p then 1 else 0) := by
      intro p _; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp
  rw [hsplit, h1, h2]
  push_cast; ring

/-- ASY-2: the spectral lower bound on the number of violated lines of any assignment. -/
theorem spectral_viol (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N)
    (s : V N → F) :
    let d : ℝ := 2 ^ N
    let n : ℝ := X.card
    let Λ := Real.sqrt (n * (d - 1))
    let Fv := d * n
    ((configX X h0).lines.card : ℝ) / 2 - (Λ * Fv - Fv ^ 2 / (d * Λ)) / (12 * d) ≤
      ((configX X h0).violated s).card := by
  intro d n Λ Fv
  have hd2 : (2 : ℝ) ≤ d := by
    show (2 : ℝ) ≤ 2 ^ N
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hn : (1 : ℝ) ≤ n := by
    simp only [n]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.card_pos.2 hX).ne'
  have hΛ : 0 < Λ := Real.sqrt_pos.2 (by nlinarith)
  have hcard : ((Fintype.card (Bas N) : ℕ) : ℝ) = d := by
    simp [d, Fintype.card_fun, ZMod.card]
  have hb := cubic_trace_bound (Mg X (gOf s)) (Mg_hermitian X (gOf s)) Λ Fv hΛ
    (rayleigh X h0 (gOf s) (gOf_pm s)) (trace_Mg X h0 (gOf s))
    (by rw [trace_Mg_sq X (gOf s) (gOf_pm s)]; simp [Fv, d, n])
  rw [hcard, trace_cube_viol X h0 s] at hb
  have hre : ((2 : ℂ) ^ N * (6 * ((configX X h0).lines.card : ℂ) - 12 * ((configX X h0).violated s).card)).re
      = d * (6 * (configX X h0).lines.card - 12 * ((configX X h0).violated s).card) := by
    rw [show ((2 : ℂ) ^ N * (6 * ((configX X h0).lines.card : ℂ) - 12 * ((configX X h0).violated s).card))
        = (((2 : ℝ) ^ N * (6 * ((configX X h0).lines.card : ℝ) - 12 * ((configX X h0).violated s).card) : ℝ) : ℂ)
        by push_cast; ring, Complex.ofReal_re]
  rw [hre] at hb
  have hdpos : 0 < d := by linarith
  rw [div_sub_div _ _ (by norm_num) (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [hb]

/-- ASY-2 for the degree. -/
theorem spectral_lower (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (hN : 1 ≤ N) :
    let d : ℝ := 2 ^ N
    let n : ℝ := X.card
    let Λ := Real.sqrt (n * (d - 1))
    let Fv := d * n
    ((configX X h0).lines.card : ℝ) / 2 - (Λ * Fv - Fv ^ 2 / (d * Λ)) / (12 * d) ≤
      (configX X h0).deg := by
  obtain ⟨s, hs⟩ := (configX X h0).exists_opt
  have := spectral_viol X h0 hX hN s
  rw [hs] at this
  exact this

end PauliCtx.Spectral
