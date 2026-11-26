/-
Den3.lean — blueprint 11, DEN-3: the hard instances are exponentially sparse.

  * `omegaB`, `ker_omegaB`, `isotropic_finrank_le` : ω as a non-degenerate symmetric bilinear form on
    V N; an isotropic subspace has dimension ≤ N (via `finrank_add_finrank_orthogonal'`).
  * `six_mul_lines_le` : 6|L(configX X)| ≤ |X|².
  * `den3_qubits` : for the Pauli realisation X = XR S of Φ_ind(S) (HARD-5/6, RealizeDeg.lean), every
    linear map φ : V n → V N' preserving ω on X and injective on span X has N' ≥ 3k, k = #variables:
    the copies Z^{e_j} on the k blocks span an isotropic subspace of dimension 3k.  In particular
    the intrinsic qubit number N_X (DEN-1′) is ≥ 3k (≥ 3k/2 as in the blueprint).
  * `den3_density` : D(X) = |L_X|/(n^{3/2} 2^{N'/2}) ≤ √n/(6·2^{3k/2}) for every such embedding, so the
    DEN-1 gap term n^{3/2}2^{N'/2}/(12|L|) is ≥ 2^{3k/2}/(2√n): DEN-1 says nothing on these instances.
-/
import PauliContextuality.RealizeDeg
import PauliContextuality.Density
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open Module

namespace PauliCtx.Spectral

open Config

variable {N N' : ℕ}

/-! ### ω as a bilinear form -/

/-- the symplectic form as a bilinear form -/
def omegaB (N : ℕ) : LinearMap.BilinForm F (V N) :=
  LinearMap.mk₂ F omega omega_add_left omega_smul_left omega_add_right omega_smul_right

@[simp] theorem omegaB_apply (p q : V N) : omegaB N p q = omega p q := rfl

theorem ker_omegaB : LinearMap.ker (omegaB N) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have h : ∀ w, omega v w = 0 := fun w => LinearMap.congr_fun hv w
  rw [Submodule.mem_bot]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := h (0, Pi.single i 1)
    unfold omega at this
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at this
    simpa using this
  · have := h (Pi.single i 1, 0)
    unfold omega at this
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at this
    simpa using this

theorem finrank_V (N : ℕ) : finrank F (V N) = 2 * N := by
  rw [Module.finrank_prod, Module.finrank_fin_fun]; ring

/-- an isotropic subspace of V N has dimension ≤ N -/
theorem isotropic_finrank_le (W : Submodule F (V N)) (hW : ∀ a ∈ W, ∀ b ∈ W, omega a b = 0) :
    finrank F W ≤ N := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := omegaB N) W
  have hker : (omegaB N).ker = ⊥ := ker_omegaB
  rw [hker, inf_bot_eq, finrank_bot, add_zero, finrank_V] at h
  have hle : W ≤ (omegaB N).orthogonal W := fun a ha b hb => by
    show omegaB N b a = 0
    exact hW b hb a ha
  have := Submodule.finrank_mono hle
  omega

/-! ### lines are sparse -/

theorem six_mul_lines_le (X : Finset (V N)) (h0 : (0 : V N) ∉ X) :
    6 * (configX X h0).lines.card ≤ X.card ^ 2 := by
  rw [← six_mul_card, sq, ← Finset.card_product]
  exact Finset.card_filter_le _ _

/-! ### DEN-3 for the Pauli realisation of Φ_ind -/

section Gadget

open Hardness Model

variable {ν ε : Type} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε] (S : E3 ν ε)

/-- the copies Z^{e_j}, j = 0, 1, 2, on the block of each variable -/
noncomputable def zcop (p : ν × Fin 3) : V (nq ν ε) := fR S (.inl (p.1, p.2.castSucc))

omit [DecidableEq ε] in
theorem zcop_mem (p : ν × Fin 3) : zcop S p ∈ XR S :=
  Finset.mem_image.2 ⟨.inl (p.1, p.2.castSucc), by simp [Ufin, InU], rfl⟩

theorem lam_castSucc (j j' : Fin 3) : lam j.castSucc j' = if j' = j then 1 else 0 := by
  revert j j'; decide

omit [DecidableEq ε] in
theorem zcop_eq (p : ν × Fin 3) :
    zcop S p = (0, Pi.single (qe.symm (.inl p)) 1) := by
  unfold zcop fR lab cLab toV
  refine Prod.ext rfl (funext fun q => ?_)
  simp only [Function.comp_apply]
  rcases h : qe q with ⟨v, j⟩ | ⟨E, t, j⟩
  · simp only [lam_castSucc]
    by_cases hv : v = p.1
    · by_cases hj : j = p.2
      · have hq : q = qe.symm (.inl p) := by rw [← Equiv.symm_apply_apply qe q, h, hv, hj]
        rw [if_pos hv, if_pos hj, hq, Pi.single_eq_same]
      · have : q ≠ qe.symm (.inl p) := by
          intro e; rw [e, Equiv.apply_symm_apply] at h
          exact hj (by injection h with h; exact (Prod.ext_iff.1 h).2.symm)
        rw [if_pos hv, if_neg hj, Pi.single_eq_of_ne this]
    · have : q ≠ qe.symm (.inl p) := by
        intro e; rw [e, Equiv.apply_symm_apply] at h
        exact hv (by injection h with h; exact (Prod.ext_iff.1 h).1.symm)
      rw [if_neg hv, Pi.single_eq_of_ne this]
  · have : q ≠ qe.symm (.inl p) := by
      intro e; rw [e, Equiv.apply_symm_apply] at h; exact Sum.inl_ne_inr h
    rw [Pi.single_eq_of_ne this]

omit [DecidableEq ε] in
theorem zcop_linIndep : LinearIndependent F (zcop S) := by
  have h1 : LinearIndependent F (fun p : ν × Fin 3 => (Pi.single (qe.symm (.inl p)) (1 : F) :
      Fin (nq ν ε) → F)) := by
    have := (Pi.basisFun F (Fin (nq ν ε))).linearIndependent.comp
      (fun p : ν × Fin 3 => qe.symm (.inl p)) (fun a b h => by simpa using h)
    simpa [Function.comp_def] using this
  refine LinearIndependent.of_comp (LinearMap.snd F (Fin (nq ν ε) → F) (Fin (nq ν ε) → F)) ?_
  convert h1 using 1
  funext p
  simp [zcop_eq]

omit [DecidableEq ε] in
theorem omega_zcop (p q : ν × Fin 3) : omega (zcop S p) (zcop S q) = 0 := by
  rw [zcop_eq, zcop_eq]; simp [omega]

omit [DecidableEq ε] in
/-- **DEN-3 (qubit count).** Any ω-preserving linear map that is injective on the span of the
realised point set needs at least 3k qubits. -/
theorem den3_qubits (φ : V (nq ν ε) →ₗ[F] V N')
    (hω : ∀ a ∈ XR S, ∀ b ∈ XR S, omega (φ a) (φ b) = omega a b)
    (hinj : Set.InjOn φ (Submodule.span F (XR S : Set (V (nq ν ε))))) :
    3 * Fintype.card ν ≤ N' := by
  have hspan : Submodule.span F (Set.range (zcop S)) ≤ Submodule.span F (XR S : Set _) :=
    Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact zcop_mem S p)
  have hli : LinearIndependent F (φ ∘ zcop S) := by
    refine (zcop_linIndep S).map ?_
    rw [Submodule.disjoint_def]
    intro x hx hker
    rw [LinearMap.mem_ker] at hker
    exact hinj (hspan hx) (Submodule.zero_mem _) (by rw [hker, map_zero])
  set U := Submodule.span F (Set.range (φ ∘ zcop S))
  have hU : finrank F U = Fintype.card (ν × Fin 3) := finrank_span_eq_card hli
  -- U is isotropic
  have hgen : ∀ p, ∀ b ∈ U, omega ((φ ∘ zcop S) p) b = 0 := by
    intro p b hb
    have : U ≤ LinearMap.ker (omegaB N' ((φ ∘ zcop S) p)) := by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, omegaB_apply, Function.comp_apply, Function.comp_apply,
        hω _ (zcop_mem S p) _ (zcop_mem S q), omega_zcop]
    exact this hb
  have hiso : ∀ a ∈ U, ∀ b ∈ U, omega a b = 0 := by
    intro a ha b hb
    have : U ≤ LinearMap.ker ((omegaB N').flip b) := by
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change omega ((φ ∘ zcop S) p) b = 0
      exact hgen p b hb
    have h := LinearMap.mem_ker.1 (this ha)
    change omega a b = 0 at h
    exact h
  have := isotropic_finrank_le U hiso
  rw [hU, Fintype.card_prod, Fintype.card_fin] at this
  omega

/-- **DEN-3 (density).** For every such embedding into N' qubits,
D(X) = |L_X|/(n^{3/2} 2^{N'/2}) ≤ √n/(6 · 2^{3k/2}). -/
theorem den3_density (φ : V (nq ν ε) →ₗ[F] V N')
    (hω : ∀ a ∈ XR S, ∀ b ∈ XR S, omega (φ a) (φ b) = omega a b)
    (hinj : Set.InjOn φ (Submodule.span F (XR S : Set (V (nq ν ε))))) :
    ((DR S).lines.card : ℝ) / ((XR S).card * Real.sqrt (XR S).card * Real.sqrt (2 ^ N')) ≤
      Real.sqrt (XR S).card / (6 * Real.sqrt (2 ^ (3 * Fintype.card ν))) := by
  have hq := den3_qubits S φ hω hinj
  have hL : 6 * ((DR S).lines.card : ℝ) ≤ ((XR S).card : ℝ) ^ 2 := by
    have := six_mul_lines_le (XR S) (zero_not_mem_XR S)
    exact_mod_cast this
  set n : ℝ := ((XR S).card : ℝ)
  have hD : Real.sqrt (2 ^ (3 * Fintype.card ν)) ≤ Real.sqrt (2 ^ N') :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) hq)
  have hD0 : 0 < Real.sqrt ((2 : ℝ) ^ (3 * Fintype.card ν)) := Real.sqrt_pos.2 (by positivity)
  rcases (show (0 : ℝ) ≤ n from Nat.cast_nonneg _).eq_or_lt with hn | hn
  · rw [← hn]; simp
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hLnn : (0 : ℝ) ≤ (DR S).lines.card := Nat.cast_nonneg _
  calc ((DR S).lines.card : ℝ) * (6 * Real.sqrt (2 ^ (3 * Fintype.card ν)))
      ≤ ((DR S).lines.card : ℝ) * (6 * Real.sqrt (2 ^ N')) := by gcongr
    _ = 6 * ((DR S).lines.card : ℝ) * Real.sqrt (2 ^ N') := by ring
    _ ≤ n ^ 2 * Real.sqrt (2 ^ N') := by gcongr
    _ = Real.sqrt n * (n * Real.sqrt n * Real.sqrt (2 ^ N')) := by
        rw [show n ^ 2 = Real.sqrt n ^ 2 * n by rw [hsn2]; ring]; ring

end Gadget

end PauliCtx.Spectral
