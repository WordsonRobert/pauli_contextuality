/-
SectionCor.lean — blueprint 06, corollaries of CONE-2: tangent hyperplane sections of W(2N−1,2).

  * `finrank_hyp`, `finrank_radical_hyp` : for a ≠ 0 the hyperplane a^⊥ has dimension 2N − 1 and
      radical ⟨a⟩ of dimension 1.
  * `tangent_degree` : deg W(a^⊥) = 4 · deg W(2N−3,2).
  * `W5_tangent`, `W7_tangent` : the concrete values 12 and 252 for W(5,2) and W(7,2).  They are stated
      for a general N with a hypothesis N = 3 (resp. 4): elaborating `configX` at a numeral N directly
      hits an instance-unification recursion, while rewriting only the index `N - 1` (`deg_W_pred`) does not.
-/
import PauliContextuality.Intrinsic

open Module

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

/-- the hyperplane a^⊥ -/
def hyp (a : V N) : Submodule F (V N) := LinearMap.ker (omegaB N a)

theorem mem_hyp {a v : V N} : v ∈ hyp a ↔ omega a v = 0 := by
  simp [hyp, LinearMap.mem_ker]

theorem omegaB_ne_zero {a : V N} (ha : a ≠ 0) : omegaB N a ≠ 0 := by
  intro h0; apply ha
  have : a ∈ LinearMap.ker (omegaB N) := by rw [LinearMap.mem_ker, h0]
  rw [ker_omegaB] at this
  exact (Submodule.mem_bot F).1 this

theorem finrank_hyp {a : V N} (ha : a ≠ 0) : finrank F (hyp a) = 2 * N - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (omegaB N a)
  have h1 : finrank F (LinearMap.range (omegaB N a)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (omegaB N a))
    simpa using this
  have h2 : finrank F (LinearMap.range (omegaB N a)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    exact omegaB_ne_zero ha
  rw [finrank_V] at h
  unfold hyp
  omega

theorem finrank_radical_hyp {a : V N} (ha : a ≠ 0) : finrank F (radical (hyp a)) = 1 := by
  apply le_antisymm
  · have hsum := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := omegaB N) (hyp a)
    have hker : (omegaB N).ker = ⊥ := ker_omegaB
    rw [hker, inf_bot_eq, finrank_bot, add_zero, finrank_V, finrank_hyp ha] at hsum
    have hle : finrank F (radical (hyp a)) ≤ finrank F ((omegaB N).orthogonal (hyp a)) :=
      Submodule.finrank_mono inf_le_right
    have hN : 1 ≤ N := by
      by_contra h
      have : N = 0 := by omega
      subst this
      exact ha (Subsingleton.elim _ _)
    omega
  · have ha' : a ∈ radical (hyp a) := by
      refine mem_radical.2 ⟨mem_hyp.2 (omega_self a), fun v hv => ?_⟩
      rw [omega_comm]; exact mem_hyp.1 hv
    have : Submodule.span F {a} ≤ radical (hyp a) := (Submodule.span_singleton_le_iff_mem _ _).2 ha'
    have h1 := Submodule.finrank_mono this
    rw [finrank_span_singleton ha] at h1
    exact h1

/-- **CONE-2, tangent hyperplanes.** For a ≠ 0, deg W(a^⊥) = 4 · deg W(2N−3,2). -/
theorem tangent_degree {a : V N} (ha : a ≠ 0) :
    (configX (secX (hyp a)) (zero_not_mem_secX _)).deg = 4 * (W (N - 1)).deg := by
  have hN : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this
    exact ha (Subsingleton.elim _ _)
  have := W_section_degree (hyp a) (N - 1) 1 (by rw [finrank_hyp ha]; omega) (finrank_radical_hyp ha)
  rw [this, pow_one]

theorem deg_W_pred {N k : ℕ} (h : N - 1 = k) : (W (N - 1)).deg = (W k).deg := by
  subst h; rfl

/-- **Tangent hyperplane section of W(5,2)** (N = 3): degree 12 = 4 · deg W(3,2). -/
theorem W5_tangent {N : ℕ} (hN : N = 3) {a : V N} (ha : a ≠ 0) :
    (configX (secX (hyp a)) (zero_not_mem_secX _)).deg = 12 := by
  rw [tangent_degree ha, deg_W_pred (k := 2) (by omega), W3_eq_3]

/-- **Tangent hyperplane section of W(7,2)** (N = 4): degree 252 = 4 · deg W(5,2). -/
theorem W7_tangent {N : ℕ} (hN : N = 4) {a : V N} (ha : a ≠ 0) :
    (configX (secX (hyp a)) (zero_not_mem_secX _)).deg = 252 := by
  rw [tangent_degree ha, deg_W_pred (k := 3) (by omega), W5_eq_63]

end PauliCtx.Spectral
