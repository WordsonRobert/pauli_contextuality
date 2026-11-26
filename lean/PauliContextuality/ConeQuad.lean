/-
ConeQuad.lean — blueprint 06, CONE-3 (b): sections of quadrics whose form is non-zero on the radical.

  * `deg_configX_fun` : DEN-1′ transport along an arbitrary (not necessarily linear) map θ that is
      injective on X, preserves ω on X and is additive on the lines of X (and reflects them).
      The degree only sees lines and commutation (`deg_invariant`), so linearity is not needed.
  * `IsQuad q` : q polarises to ω, q(a+b) = q a + q b + ω(a,b); `qplus_isQuad`, `qminus_isQuad`.
  * `secQ q U` : the singular non-zero points of U.
  * `Q_section_degree_b` : **CONE-3 (b).** If dim U = 2k + t, dim rad U = t and q is non-zero on rad U,
      then deg (U ∩ Q) = 4^{t−1} · deg W(2k−1,2).
      Proof (blueprint 06): pick r₀ ∈ rad U with q r₀ = 1 and s with ω(s, r₀) = 1, put U' = U ∩ s^⊥
      (dim 2k + t − 1, radical rad U ∩ s^⊥ of dim t − 1); then x ↦ x + q(x) r₀ is a bijection from
      U' ∖ 0 onto the singular points of U ∖ 0 satisfying the hypotheses of `deg_configX_fun`, and
      CONE-2 (`W_section_degree`) gives deg (U' ∖ 0) = 4^{t−1} deg W(2k−1,2).
  * `nontangent_degree` : a non-tangent hyperplane a^⊥ (q a = 1) of a quadric Q in V N has
      deg (a^⊥ ∩ Q) = deg W(2N−3,2); `Qminus7_nontangent`, `Qplus7_nontangent` : = 63 for Q^±(7,2).
-/
import PauliContextuality.SectionCor

open Module

namespace PauliCtx.Spectral

open Config

variable {N N' : ℕ}

/-! ### transport along a map that is additive on lines -/

section transport

variable (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (θ : V N → V N')
  (hinj : Set.InjOn θ (X : Set (V N)))
  (hω : ∀ a ∈ X, ∀ b ∈ X, omega (θ a) (θ b) = omega a b)
  (hadd : ∀ a ∈ X, ∀ b ∈ X, omega a b = 0 → a + b ∈ X → θ (a + b) = θ a + θ b)
  (hrev : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, θ c = θ a + θ b → a + b = c)

/-- the embedding of the point subtype through θ -/
noncomputable def embθ : PtX X ↪ V N' :=
  ⟨fun x => θ x.1, fun x y h => Subtype.ext (hinj x.2 y.2 h)⟩

include hω hadd hrev in
theorem lines_image_fun (h0' : (0 : V N') ∉ X.image θ) :
    (configX (X.image θ) h0').lines = (linesSub X h0).image (fun l => l.map (embθ X θ hinj)) := by
  have hmapl : ∀ l ∈ (configX X h0).lines,
      (l.subtype (· ∈ X)).map (embθ X θ hinj) = l.image θ := by
    intro l hl
    ext y
    simp only [Finset.mem_map, Finset.mem_image, Finset.mem_subtype, embθ,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨x, hx⟩, hxl, rfl⟩; exact ⟨x, hxl, rfl⟩
    · rintro ⟨x, hxl, rfl⟩; exact ⟨⟨x, lines_sub_X h0 hl x hxl⟩, hxl, rfl⟩
  have htri : ∀ p ∈ OP X, (tri p).image θ = tri (θ p.1, θ p.2) := by
    intro p hp
    obtain ⟨h1, h2, hωp, h3⟩ := mem_OP.1 hp
    simp only [tri, Finset.image_insert, Finset.image_singleton]
    rw [hadd _ h1 _ h2 hωp h3]
  ext m
  constructor
  · intro hm
    obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨h1, h2, hωq, h3⟩ := mem_OP.1 hq
    simp only at h1 h2 hωq h3
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h2
    obtain ⟨c, hc, hcab⟩ := Finset.mem_image.1 h3
    have hab : a + b = c := hrev a ha b hb c hc hcab
    have hp : (a, b) ∈ OP X := mem_OP.2 ⟨ha, hb, by rw [← hω a ha b hb]; exact hωq, hab ▸ hc⟩
    have hl : tri (a, b) ∈ (configX X h0).lines := Finset.mem_image_of_mem _ hp
    refine Finset.mem_image.2 ⟨(tri (a, b)).subtype (· ∈ X), Finset.mem_image_of_mem _ hl, ?_⟩
    rw [hmapl _ hl, htri _ hp]
  · intro hm
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hl'
    rw [hmapl _ hl]
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨h1, h2, hωp, h3⟩ := mem_OP.1 hp
    have hq : (θ p.1, θ p.2) ∈ OP (X.image θ) :=
      mem_OP.2 ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2,
        by rw [hω _ h1 _ h2]; exact hωp,
        by rw [← hadd _ h1 _ h2 hωp h3]; exact Finset.mem_image_of_mem _ h3⟩
    refine Finset.mem_image.2 ⟨_, hq, ?_⟩
    rw [htri _ hp]

include hinj hω hadd hrev in
/-- **DEN-1′ for non-linear maps.** -/
theorem deg_configX_fun (h0' : (0 : V N') ∉ X.image θ) :
    (configX (X.image θ) h0').deg = (configX X h0).deg := by
  have hD₁ := lines_eq_linesSub X h0
  have hD₂ := lines_image_fun X h0 θ hinj hω hadd hrev h0'
  have hm₁ : ∀ l ∈ linesSub X h0, l.map (Function.Embedding.subtype _) ∈ (configX X h0).lines :=
    fun l hl => by rw [hD₁]; exact Finset.mem_image_of_mem _ hl
  have hm₂ : ∀ l ∈ linesSub X h0, l.map (embθ X θ hinj) ∈ (configX (X.image θ) h0').lines :=
    fun l hl => by rw [hD₂]; exact Finset.mem_image_of_mem _ hl
  rw [← deg_comap _ _ _ hm₁ hD₁, ← deg_comap _ _ _ hm₂ hD₂]
  symm
  exact deg_invariant _ _ _ _ (real_comap_configX h0 _ _ hm₁) (real_comap_configX h0' _ _ hm₂) rfl
    (fun p q => hω p.1 p.2 q.1 q.2)

end transport

/-! ### quadratic forms and quadric sections -/

/-- q is a quadratic form whose polarisation is ω -/
def IsQuad (q : V N → F) : Prop := ∀ a b, q (a + b) = q a + q b + omega a b

theorem qplus_isQuad : IsQuad (qplus : V N → F) := qplus_add

theorem qminus_isQuad : IsQuad (qminus : V (N + 1) → F) := by
  intro a b
  unfold qminus
  rw [qplus_add]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

theorem IsQuad.map_zero {q : V N → F} (hq : IsQuad q) : q 0 = 0 := by
  have h := hq 0 0
  rw [add_zero, omega_self, add_zero] at h
  have : q 0 + q 0 = 0 := CharTwo.add_self_eq_zero _
  rw [← h] at this
  simpa using this

theorem F_eq_one {x : F} (h : x ≠ 0) : x = 1 := by
  rcases F_cases x with rfl | rfl
  · exact absurd rfl h
  · rfl

theorem IsQuad.smul {q : V N → F} (hq : IsQuad q) (c : F) (r : V N) (hr : q r = 1) :
    q (c • r) = c := by
  rcases F_cases c with rfl | rfl
  · rw [zero_smul, hq.map_zero]
  · rw [one_smul, hr]

/-- the quadric section: singular non-zero points of U -/
noncomputable def secQ (q : V N → F) (U : Submodule F (V N)) : Finset (V N) :=
  (secX U).filter (fun x => q x = 0)

theorem zero_not_mem_secQ (q : V N → F) (U : Submodule F (V N)) : (0 : V N) ∉ secQ q U := by
  simp [secQ, secX]

theorem mem_secQ {q : V N → F} {U : Submodule F (V N)} {x : V N} :
    x ∈ secQ q U ↔ x ≠ 0 ∧ x ∈ U ∧ q x = 0 := by
  simp [secQ, secX, and_assoc]

/-! ### CONE-3 (b) -/

section coneB

variable {q : V N → F} (hq : IsQuad q) {U : Submodule F (V N)} {r s : V N}
  (hrR : r ∈ radical U) (hqr : q r = 1) (hsr : omega s r = 1)

/-- the complement U' = U ∩ s^⊥ of ⟨r⟩ -/
def compl' (U : Submodule F (V N)) (s : V N) : Submodule F (V N) := U ⊓ hyp s

/-- the twist x ↦ x + q(x) r -/
def twist (q : V N → F) (r : V N) (x : V N) : V N := x + q x • r

include hsr in
theorem omega_twist_s (x : V N) (hx : omega s x = 0) : omega s (twist q r x) = q x := by
  rw [twist, omega_add_right, omega_smul_right, hx, hsr, zero_add, mul_one]

include hrR in
theorem omega_r_left {u : V N} (hu : u ∈ U) : omega r u = 0 := by
  rw [omega_comm]; exact (mem_radical.1 hrR).2 u hu

include hrR in
theorem omega_r_right {u : V N} (hu : u ∈ U) : omega u r = 0 := (mem_radical.1 hrR).2 u hu

/-- the projection u ↦ u + ω(s,u) r onto U' -/
def projR (r s : V N) (u : V N) : V N := u + omega s u • r

include hsr in
theorem omega_projR (u : V N) : omega s (projR r s u) = 0 := by
  rw [projR, omega_add_right, omega_smul_right, hsr, mul_one]
  exact CharTwo.add_self_eq_zero _

include hrR hsr in
theorem projR_mem {u : V N} (hu : u ∈ U) : projR r s u ∈ compl' U s :=
  Submodule.mem_inf.2 ⟨U.add_mem hu (U.smul_mem _ (mem_radical.1 hrR).1),
    mem_hyp.2 (omega_projR hsr u)⟩

include hsr in
theorem smul_r_mem_hyp {c : F} (h : c • r ∈ hyp s) : c = 0 := by
  have := mem_hyp.1 h
  rwa [omega_smul_right, hsr, mul_one] at this

include hrR hsr in
theorem compl_sup : compl' U s ⊔ Submodule.span F {r} = U := by
  apply le_antisymm
  · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_radical.1 hrR).1)
  · intro u hu
    have : u = projR r s u + omega s u • r := by
      rw [projR, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
    rw [this]
    exact Submodule.add_mem_sup (projR_mem hrR hsr hu) (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self r))

include hsr in
theorem hyp_inf_span (M : Submodule F (V N)) (hW : M ≤ hyp s) :
    M ⊓ Submodule.span F {r} = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx2
  rw [smul_r_mem_hyp hsr (hW hx1), zero_smul]
  exact Submodule.zero_mem _

theorem r_ne_zero (hqr : q r = 1) (hq : IsQuad q) : r ≠ 0 := by
  rintro rfl; rw [hq.map_zero] at hqr; exact zero_ne_one hqr

include hq hqr hsr in
theorem finrank_compl_add (M : Submodule F (V N)) (hW : M ≤ hyp s) :
    finrank F ↥(M ⊔ Submodule.span F {r}) = finrank F M + 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq M (Submodule.span F {r})
  rw [hyp_inf_span hsr M hW, finrank_bot, add_zero, finrank_span_singleton (r_ne_zero hqr hq)] at h
  exact h

include hrR hsr in
theorem radical_compl : radical (compl' U s) = radical U ⊓ hyp s := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxU', hxo⟩ := mem_radical.1 hx
    obtain ⟨hxU, hxs⟩ := Submodule.mem_inf.1 hxU'
    refine Submodule.mem_inf.2 ⟨mem_radical.2 ⟨hxU, fun v hv => ?_⟩, hxs⟩
    have hv' : v = projR r s v + omega s v • r := by
      rw [projR, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
    rw [hv', omega_add_left, omega_smul_left, hxo _ (projR_mem hrR hsr hv), omega_r_left hrR hxU,
      mul_zero, add_zero]
  · intro hx
    obtain ⟨hxR, hxs⟩ := Submodule.mem_inf.1 hx
    obtain ⟨hxU, hxo⟩ := mem_radical.1 hxR
    exact mem_radical.2 ⟨Submodule.mem_inf.2 ⟨hxU, hxs⟩,
      fun v hv => hxo v (Submodule.mem_inf.1 hv).1⟩

include hrR hsr in
theorem radical_compl_sup : radical U ⊓ hyp s ⊔ Submodule.span F {r} = radical U := by
  apply le_antisymm
  · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).2 hrR)
  · intro u hu
    have hu' : u = projR r s u + omega s u • r := by
      rw [projR, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
    rw [hu']
    refine Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨?_, mem_hyp.2 (omega_projR hsr u)⟩)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r))
    exact (radical U).add_mem hu ((radical U).smul_mem _ hrR)

include hq hrR hqr in
theorem q_projR {u : V N} (hu : u ∈ U) : q (projR r s u) = q u + omega s u := by
  rw [projR, hq, hq.smul _ _ hqr, omega_smul_right, omega_r_right hrR hu, mul_zero, add_zero]

include hq hrR hqr in
theorem twist_projR {u : V N} (hu : u ∈ U) (hqu : q u = 0) : twist q r (projR r s u) = u := by
  rw [twist, q_projR hq hrR hqr hu, hqu, zero_add, projR, add_assoc, ← add_smul,
    CharTwo.add_self_eq_zero, zero_smul, add_zero]

include hq hrR hqr hsr in
theorem secQ_eq_image :
    secQ q U = (secX (compl' U s)).image (twist q r) := by
  ext x
  rw [mem_secQ, Finset.mem_image]
  constructor
  · rintro ⟨hx0, hxU, hqx⟩
    refine ⟨projR r s x, mem_secX.2 ⟨?_, projR_mem hrR hsr hxU⟩, twist_projR hq hrR hqr hxU hqx⟩
    intro h
    have h1 : x = omega s x • r := by
      have : x + omega s x • r = 0 := h
      calc x = x + omega s x • r + omega s x • r := by
              rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
        _ = omega s x • r := by rw [this, zero_add]
    have h2 : q x = omega s x := by rw [h1, hq.smul _ _ hqr]; rw [← h1]
    apply hx0
    rw [h1, ← h2, hqx, zero_smul]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha0, haU'⟩ := mem_secX.1 ha
    obtain ⟨haU, has⟩ := Submodule.mem_inf.1 haU'
    have has' : omega s a = 0 := mem_hyp.1 has
    refine ⟨fun h => ?_, U.add_mem haU (U.smul_mem _ (mem_radical.1 hrR).1), ?_⟩
    · have h1 := omega_twist_s (q := q) hsr a has'
      have h1' : q a = 0 := by rw [← h1, h]; simp [omega]
      apply ha0
      have : a + q a • r = 0 := h
      rw [h1', zero_smul, add_zero] at this
      exact this
    · rw [twist, hq, hq.smul _ _ hqr, omega_smul_right, omega_r_right hrR haU, mul_zero, add_zero]
      exact CharTwo.add_self_eq_zero _

include hq hrR hqr hsr in
theorem secQ_deg :
    (configX (secQ q U) (zero_not_mem_secQ q U)).deg =
      (configX (secX (compl' U s)) (zero_not_mem_secX _)).deg := by
  set X := secX (compl' U s)
  have hXs : ∀ a ∈ X, omega s a = 0 := fun a ha =>
    mem_hyp.1 (Submodule.mem_inf.1 (mem_secX.1 ha).2).2
  have hXU : ∀ a ∈ X, a ∈ U := fun a ha => (Submodule.mem_inf.1 (mem_secX.1 ha).2).1
  have hqθ : ∀ a ∈ X, omega s (twist q r a) = q a := fun a ha => omega_twist_s hsr a (hXs a ha)
  have hinj : Set.InjOn (twist q r) (X : Set (V N)) := by
    intro a ha b hb h
    have e : q a = q b := by rw [← hqθ a ha, ← hqθ b hb, h]
    have : a + q a • r = b + q b • r := h
    rw [e] at this
    exact add_right_cancel this
  have hω : ∀ a ∈ X, ∀ b ∈ X, omega (twist q r a) (twist q r b) = omega a b := by
    intro a ha b hb
    simp only [twist, omega_add_left, omega_add_right, omega_smul_left, omega_smul_right,
      omega_self, omega_r_left hrR (hXU b hb), omega_r_right hrR (hXU a ha)]
    ring
  have hadd : ∀ a ∈ X, ∀ b ∈ X, omega a b = 0 → a + b ∈ X →
      twist q r (a + b) = twist q r a + twist q r b := by
    intro a _ b _ hab _
    simp only [twist, hq a b, hab, add_zero, add_smul]
    abel
  have hrev : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, twist q r c = twist q r a + twist q r b → a + b = c := by
    intro a ha b hb c hc h
    have e : q c = q a + q b := by
      rw [← hqθ a ha, ← hqθ b hb, ← hqθ c hc, h, omega_add_right]
    have : c + q c • r = a + q a • r + (b + q b • r) := h
    rw [e, add_smul] at this
    have : c = a + b := by
      have h2 : c + (q a • r + q b • r) = (a + b) + (q a • r + q b • r) := by rw [this]; abel
      exact add_right_cancel h2
    exact this.symm
  have himg := secQ_eq_image hq hrR hqr hsr (U := U)
  have h0' : (0 : V N) ∉ X.image (twist q r) := by rw [← himg]; exact zero_not_mem_secQ q U
  rw [configX_deg_congr himg _ h0', deg_configX_fun X (zero_not_mem_secX _) _ hinj hω hadd hrev h0']

end coneB

/-- **CONE-3 (b).** If dim U = 2k + t, dim rad U = t, and the quadratic form q (polarising to ω) is
non-zero on rad U, then the quadric section U ∩ Q has degree 4^{t−1} · deg W(2k−1,2). -/
theorem Q_section_degree_b {q : V N → F} (hq : IsQuad q) (U : Submodule F (V N)) (k t : ℕ)
    (hk : finrank F U = 2 * k + t) (ht : finrank F (radical U) = t)
    (hr : ∃ r ∈ radical U, q r = 1) :
    (configX (secQ q U) (zero_not_mem_secQ q U)).deg = 4 ^ (t - 1) * (W k).deg := by
  obtain ⟨r, hrR, hqr⟩ := hr
  have hr0 : r ≠ 0 := r_ne_zero hqr hq
  obtain ⟨s, hs⟩ : ∃ s, omega s r = 1 := by
    have h := omegaB_ne_zero hr0
    by_contra hcon
    push Not at hcon
    apply h
    refine LinearMap.ext fun v => ?_
    have : omega v r = 0 := by
      rcases F_cases (omega v r) with h' | h'
      · exact h'
      · exact absurd h' (hcon v)
    rw [omegaB_apply, omega_comm]
    simpa using this
  rw [secQ_deg hq hrR hqr hs]
  have hU' : finrank F (compl' U s) + 1 = 2 * k + t := by
    have h := finrank_compl_add hq hqr hs (compl' U s) inf_le_right
    rw [compl_sup hrR hs] at h
    omega
  have hR' : finrank F (radical (compl' U s)) + 1 = t := by
    have h := finrank_compl_add hq hqr hs (radical U ⊓ hyp s) inf_le_right
    rw [radical_compl_sup hrR hs] at h
    rw [radical_compl hrR hs]
    omega
  exact W_section_degree (compl' U s) k (t - 1) (by omega) (by omega)

/-- a non-zero vector lies in the radical of its own hyperplane -/
theorem mem_radical_hyp_self (a : V N) : a ∈ radical (hyp a) := by
  refine mem_radical.2 ⟨mem_hyp.2 (omega_self a), fun v hv => ?_⟩
  rw [omega_comm]; exact mem_hyp.1 hv

/-- **CONE-3, non-tangent hyperplanes.** If q a = 1, deg (a^⊥ ∩ Q) = deg W(2N−3,2). -/
theorem nontangent_degree {q : V N → F} (hq : IsQuad q) {a : V N} (ha : q a = 1) :
    (configX (secQ q (hyp a)) (zero_not_mem_secQ q _)).deg = (W (N - 1)).deg := by
  have ha0 : a ≠ 0 := r_ne_zero ha hq
  have hN : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this
    exact ha0 (Subsingleton.elim _ _)
  have := Q_section_degree_b hq (hyp a) (N - 1) 1 (by rw [finrank_hyp ha0]; omega)
    (finrank_radical_hyp ha0) ⟨a, mem_radical_hyp_self a, ha⟩
  rw [this, Nat.sub_self, pow_zero, one_mul]

/-- **Non-tangent hyperplane sections of Q⁺(7,2)** (N = 4): degree 63. -/
theorem Qplus7_nontangent {N : ℕ} (hN : N = 4) {a : V N} (ha : qplus a = 1) :
    (configX (secQ qplus (hyp a)) (zero_not_mem_secQ _ _)).deg = 63 := by
  rw [nontangent_degree qplus_isQuad ha, deg_W_pred (k := 3) (by omega), W5_eq_63]

/-- **Non-tangent hyperplane sections of Q⁻(7,2)** (N = 4): degree 63. -/
theorem Qminus7_nontangent {N : ℕ} (hN : N = 3) {a : V (N + 1)} (ha : qminus a = 1) :
    (configX (secQ qminus (hyp a)) (zero_not_mem_secQ _ _)).deg = 63 := by
  rw [nontangent_degree qminus_isQuad ha, deg_W_pred (k := 3) (by omega), W5_eq_63]

end PauliCtx.Spectral
