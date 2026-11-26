/-
Intrinsic.lean — blueprint 11, DEN-1′: the intrinsic qubit number.

Let U = span X with dim U = 2k + t and dim(U ∩ U^⊥) = t (k, t as in the normal form of Section.lean),
and N_X := k + t = (u + r)/2.
  * `den1_intrinsic` : X is realised on N_X qubits (the normal form ψ : V (k+t) → V N of
      `exists_sympData`, transported by `deg_configX_map`), so DEN-1 holds with N replaced by N_X:
        deg X ≥ |L_X|/2 − n^{3/2}(2^{N_X} − 2)/(12√(2^{N_X} − 1)).
  * `intrinsic_min` : no smaller symplectic space works: every linear φ : V N → V N' that preserves ω
      on X and is injective on span X has N' ≥ N_X.
-/
import PauliContextuality.Section

open Module

namespace PauliCtx.Spectral

open Config

variable {N N' : ℕ}

/-- ω-preservation on X extends to span X (bilinearity) -/
theorem omega_span (φ : V N →ₗ[F] V N') (X : Set (V N))
    (hω : ∀ a ∈ X, ∀ b ∈ X, omega (φ a) (φ b) = omega a b) :
    ∀ a ∈ Submodule.span F X, ∀ b ∈ Submodule.span F X, omega (φ a) (φ b) = omega a b := by
  have h1 : ∀ a ∈ X, ∀ b ∈ Submodule.span F X, omega (φ a) (φ b) = omega a b := by
    intro a ha b hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact hω a ha x hx
    | zero => simp [omega]
    | add x y _ _ hx hy => rw [map_add, omega_add_right, omega_add_right, hx, hy]
    | smul c x _ hx => rw [map_smul, omega_smul_right, omega_smul_right, hx]
  intro a ha b hb
  induction ha using Submodule.span_induction with
  | mem x hx => exact h1 x hx b hb
  | zero => simp [omega]
  | add x y _ _ hx hy => rw [map_add, omega_add_left, omega_add_left, hx, hy]
  | smul c x _ hx => rw [map_smul, omega_smul_left, omega_smul_left, hx]

/-- **DEN-1 with the intrinsic qubit number N_X = k + t.** -/
theorem den1_intrinsic (X : Finset (V N)) (h0 : (0 : V N) ∉ X) (hX : X.Nonempty) (k t : ℕ)
    (hk : finrank F (Submodule.span F (X : Set (V N))) = 2 * k + t)
    (ht : finrank F (radical (Submodule.span F (X : Set (V N)))) = t) :
    ((configX X h0).lines.card : ℝ) / 2 -
        (X.card : ℝ) * Real.sqrt X.card * (2 ^ (k + t) - 2) / (12 * Real.sqrt (2 ^ (k + t) - 1)) ≤
      (configX X h0).deg := by
  set U := Submodule.span F (X : Set (V N))
  obtain ⟨k', t', ⟨D⟩⟩ := exists_sympData U
  have e1 : t' = t := by rw [← ht, finrank_radical_of_sympData D]
  subst e1
  have e2 : k' = k := by have := finrank_of_sympData D; omega
  subst e2
  -- the preimage of X in the standard section
  set X' : Finset (V (k' + t')) := (Xstd k' t').filter (fun p => psiMap D p ∈ X)
  have hX'sub : X' ⊆ Xstd k' t' := Finset.filter_subset _ _
  have h0' : (0 : V (k' + t')) ∉ X' := fun h => zero_not_mem_Xstd k' t' (hX'sub h)
  have hspan : Submodule.span F (X' : Set (V (k' + t'))) ≤ Sstd k' t' :=
    Submodule.span_le.2 fun p hp => Xstd_sub k' t' (hX'sub hp)
  have hinj : Set.InjOn (psiMap D) (Submodule.span F (X' : Set (V (k' + t')))) :=
    (psiMap_injOn D).mono hspan
  have hω : ∀ a ∈ X', ∀ b ∈ X', omega (psiMap D a) (psiMap D b) = omega a b :=
    fun a ha b hb => psiMap_omega D (Xstd_sub k' t' (hX'sub ha)) (Xstd_sub k' t' (hX'sub hb))
  have himg : X'.image (psiMap D) = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      exact (Finset.mem_filter.1 hp).2
    · intro hx
      obtain ⟨p, hpS, hpx⟩ := psiMap_surj D (Submodule.subset_span hx : x ∈ U)
      have hp0 : p ≠ 0 := by
        rintro rfl; rw [map_zero] at hpx; exact h0 (hpx ▸ hx)
      refine Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_filter.2
        ⟨Finset.mem_univ _, hp0, hpS⟩, hpx ▸ hx⟩, hpx⟩
  have h0'' := zero_not_mem_image X' h0' (psiMap D) hinj
  have hdeg : (configX X h0).deg = (configX X' h0').deg := by
    rw [configX_deg_congr himg.symm h0 h0'', deg_configX_map X' h0' (psiMap D) hω hinj h0'']
  have hlines : (configX X h0).lines.card = (configX X' h0').lines.card := by
    have := card_lines_configX_map X' h0' (psiMap D) hω hinj h0''
    rw [← this]
    have e : ∀ (Y Z : Finset (V N)) (h : Y = Z) (hY : (0 : V N) ∉ Y) (hZ : (0 : V N) ∉ Z),
        (configX Y hY).lines.card = (configX Z hZ).lines.card := by
      intro Y Z h hY hZ; subst h; rfl
    exact e _ _ himg.symm _ _
  have hcard : X.card = X'.card := by
    rw [← card_image_X X' (psiMap D) hinj, himg]
  have hne : X'.Nonempty := by
    rw [← Finset.card_pos, ← hcard]; exact Finset.card_pos.2 hX
  have hN : 1 ≤ k' + t' := by
    obtain ⟨p, hp⟩ := hne
    by_contra h
    have hk0 : k' = 0 := by omega
    have ht0 : t' = 0 := by omega
    subst hk0 ht0
    apply (Finset.mem_filter.1 (hX'sub hp)).2.1
    exact Prod.ext (funext fun i => absurd i.2 (by omega)) (funext fun i => absurd i.2 (by omega))
  have h := den1 X' h0' hne hN
  rw [hdeg, hlines, hcard]
  exact h

/-- **DEN-1′ (minimality).** Every linear map that preserves ω on X and is injective on span X maps
into at least N_X = k + t qubits. -/
theorem intrinsic_min (X : Finset (V N)) (φ : V N →ₗ[F] V N')
    (hω : ∀ a ∈ X, ∀ b ∈ X, omega (φ a) (φ b) = omega a b)
    (hinj : Set.InjOn φ (Submodule.span F (X : Set (V N)))) (k t : ℕ)
    (hk : finrank F (Submodule.span F (X : Set (V N))) = 2 * k + t)
    (ht : finrank F (radical (Submodule.span F (X : Set (V N)))) = t) : k + t ≤ N' := by
  set U := Submodule.span F (X : Set (V N))
  have hωU := omega_span φ (X : Set (V N)) hω
  -- dim φ(U) = dim U
  have hinjU : Function.Injective (φ.domRestrict U) := fun x y h =>
    Subtype.ext (hinj x.2 y.2 h)
  have hW : finrank F (U.map φ) = 2 * k + t := by
    rw [← hk, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinjU]
  -- φ(rad U) ⊆ rad W, of dimension t
  set R := radical U
  have hRU : R ≤ U := inf_le_left
  have hRmap : R.map φ ≤ radical (U.map φ) := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrU, hrorth⟩ := mem_radical.1 hr
    refine mem_radical.2 ⟨Submodule.mem_map_of_mem hrU, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [hωU u hu r hrU]; exact hrorth u hu
  have hinjR : Function.Injective (φ.domRestrict R) := fun x y h =>
    Subtype.ext (hinj (hRU x.2) (hRU y.2) h)
  have hRdim : finrank F (R.map φ) = t := by
    rw [← ht, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinjR]
  -- dim W + dim W^⊥ = 2N'
  have hsum := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := omegaB N') (U.map φ)
  have hker : (omegaB N').ker = ⊥ := ker_omegaB
  rw [hker, inf_bot_eq, finrank_bot, add_zero, finrank_V] at hsum
  have h1 : finrank F (R.map φ) ≤ finrank F ((omegaB N').orthogonal (U.map φ)) :=
    Submodule.finrank_mono (hRmap.trans inf_le_right)
  omega

end PauliCtx.Spectral
