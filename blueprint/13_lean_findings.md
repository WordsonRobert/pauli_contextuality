# 13. Findings from the Lean formalisation (round 3)

This file records what the Lean work found when the blueprint statements were turned into theorems:
statements that had to be sharpened or corrected, things the blueprint does not prove, and the items that are
still missing in Lean, with the reason. The Lean names refer to `lean/README.md`.

Nothing in the blueprint turned out to be **false**. The items below are refinements, corrections of
presentation, and gaps.

## A. Statements proved in a sharper or slightly different form

1. **DEN-1′ (intrinsic qubit number), hypotheses.** The blueprint asks for a linear map φ that "preserves ω".
   Lean (`deg_configX_map`) only needs φ to preserve ω **on the points of X** and to be injective on span X.
   This weaker hypothesis is what CONE-2 needs: the normal-form map ψ of `Section.lean` is an isometry only on
   the standard subspace, not on all of V(k+t).

2. **DEN-3, the qubit count.** The blueprint derives N_X ≥ 3k/2 from u ≥ 3k. Lean (`den3_qubits`) proves the
   stronger N' ≥ 3k for every embedding: the 3k copies Z^{e_j} span a **totally isotropic** subspace of dimension
   3k, and an isotropic subspace of V N' has dimension ≤ N' (`isotropic_finrank_le`). The density bound
   `den3_density` therefore reads D(X) ≤ √n / (6·2^{3k/2}) (blueprint: n^{1/2}·2^{−3k/4}). Both are 2^{−Ω(k)}.

3. **GAME-1, the definition of the classical value.** `classicalValue C` is defined as the maximum over
   deterministic strategies, and `mixture_le` proves that any finite mixture (shared randomness) does no better.
   The winning probability is the uniform-line, uniform-point average (wins/(3|L|)). The key lemma is
   `agree_le_of_violated`: an answer satisfying a line differs from a violating assignment in ≥ 1 position.

4. **TIGHT-1, both directions.** (ii) ⇒ (i) is `tight_of_flat`, with the sign pattern `signOf ψ` (sign of
   ⟨ψ|P_a|ψ⟩, 0 ↦ +1) as the optimal assignment; it uses the exact Pauli expansion
   Σ_a ⟨v|P_a|v⟩ P_a = 2^N |v⟩⟨v| (`pauli_expand`), hence γM_g = 2^N|ψ⟩⟨ψ| − I and γ³ tr M_g³ = d(d−1)(d−2).
   (i) ⇒ (ii) is `tight_converse` (equivalence: `tight_iff`). The blueprint's eigenvalue argument is replaced
   by trace arguments: tr(B(ΛI−M)B) = 0 with ΛI−M ⪰ 0 forces (ΛI−M)(M+μI) = 0 (`cubic_eq_case`), so
   R = (M+μI)/(Λ+μ) is a Hermitian idempotent of trace 1, hence |ψ⟩⟨ψ| (`rank_one_of_idem`); no spectral
   theorem and no multiplicity count are needed (tr R = 1 follows from Λ² = n(d−1) directly). For every
   optimal assignment s the state satisfies ⟨ψ|P_a|ψ⟩ = γ(−1)^{s(a)} on X, γ = √(n(d−1))/n.

5. **TIGHT-2, the gauge kernel.** Proved: the gauge space of W(5,2) has dimension 7 and the 315×63 incidence
   matrix has rank 56 (`finrank_kerW3`, `rank_incW3`); the quadratic form y(a) mod 2 is a gauge and is not linear
   (`qplus_mem_kerW`, `qplus_not_linear`); every attained violated set is attained by exactly 2^7 = 128 normalised
   assignments (`card_fiber_violated`). The certificate is a 56-step propagation from
   T = {X₁, X₂, X₃, Z₁, Z₂, Z₃, Y₁}: each step is a line with two already-determined points.

6. **NEG-1.** Lean proves the structural part: B(Λ) = ΛF − F²/(dΛ) is increasing (`B_mono`), ASY-2 holds with any
   valid Λ (`spectral_lower_of_valid`), a valid Λ is ≥ every Rayleigh quotient ⟨v|M_g|v⟩ (`valid_ge_rayleigh`),
   and one explicit pair (g, v) caps the method (`ceiling`). The numbers 297 and 1488 need λ_max of explicit
   16×16 matrices with irrational entries (21 + 16√6 etc.); they stay in `certificates/certify_asym.py` (X17).

7. **ASY-7 (iv).** The chain ρ₃ < ρ₄ < … < ρ₁₁ is proved (`rho_strict_chain`). One new product bound was needed:
   deg W(19,2) ≤ 43768473840 from τ₄τ₃τ₃ (`W19_le`). The lower bounds for N+1 = 6..11 use ASY-2 with the integer
   Λ₀ = ⌊√((4^{N+1}−1)(2^{N+1}−1))⌋; no rational approximation finer than the integer part was needed.

8. **CONE-2.** Proved without Witt's theorem (`W_section_degree`): an explicit symplectic basis adapted to the
   radical is built by induction on dim U, splitting off one hyperbolic pair at a time (`exists_sympData`).
   The degree identity then goes through DEN-1′ and an explicit identification of the standard section
   V k ⊗ ⟨Z⟩^t with Cone_t(W(2k−1,2)) (lines `lines_Xstd`, signs `deg_Xstd_cone`). The tangent values
   12 and 252 (`W5_tangent`, `W7_tangent`) are stated for V N with a hypothesis N = 3 (resp. 4), because
   elaborating `configX` at a literal numeral N triggers an instance-unification recursion; the statement is
   the same.

9. **DEN-3 depends on computation.** `den3_density` uses the realised gadget degree of RealizeDeg, which
   rests on the `native_decide` certificates `Model.reg_path` and `Model.supp_aux`; it is therefore in the ⚙
   list of the audit. `den3_qubits` (N′ ≥ 3k) is axiom-clean.

10. **CONE-3 (b).** Proved as stated (`Q_section_degree_b`), for any q with q(a+b) = q(a)+q(b)+ω(a,b). The
    blueprint's map y ↦ x (singular points of ⟨r₀⟩ ⊕ X₀ onto X₀∖0) is not linear, so DEN-1′ as proved
    (`deg_configX_map`, linear φ) does not apply. Lean adds `deg_configX_fun`: any map θ that is injective on
    X, preserves ω on X and is additive on lines (θ(a+b) = θa + θb for commuting a, b with a+b ∈ X, and
    θc = θa + θb ⇒ c = a+b) preserves the degree, because the degree depends only on lines and
    commutation (`deg_invariant`). The complement of ⟨r₀⟩ is taken as U ∩ s^⊥ with ω(s, r₀) = 1, and its
    radical is rad U ∩ s^⊥ of dimension t − 1, so CONE-2 applies to it. Corollary: non-tangent hyperplane
    sections have degree deg W(2N−3,2) (`nontangent_degree`), = 63 for Q^±(7,2).

11. **CONE-3, the type of a quadric, without Arf normal forms.** The blueprint uses the classification of
    non-degenerate quadratic forms over F₂ (Arf invariant). For the degree, one transvection suffices
    (`deg_secQ_type`): every q polarising to ω is qplus + ω(c,·) (`quad_eq_qplus_add`, nondegeneracy of ω),
    and if q(d) = 0 the transvection T_d x = x + ω(d,x)d satisfies q∘T_d = q + ω(d,·) (`quad_tvL`). So
    q has the degree of Q⁺ if qplus(c) = 0, and of qplus + ω(c₀,·) for any fixed c₀ with qplus(c₀) = 1
    otherwise (shift by d = c + c₀). On V (n+1), c₀ = Y₁ gives exactly `qminus` (`deg_secQ_qminus`). The
    type qplus(c) is the Arf invariant of q; Lean does not need that name. Concretely, every quadric of
    W(5,2) has degree 21 or 9 (`deg_quad5`).

12. **CONE-3 (a) and the tangent values.** Proved (`Q_section_degree_a`, `Q_section_degree_a'`). The cone step
    is CONE-2's standard-section argument with W(2k−1,2) replaced by an arbitrary induced configuration Y
    (`std_sub_degree`): deg(Y ⊗ ⟨Z⟩^t) = 4^t deg Y, with no closure hypothesis on Y, because both sides
    are induced configurations. In normal-form coordinates, q(ψ(v ⊗ Z^σ)) = q₀(v) whenever q = 0 on rad U
    (`q_psiMap_join`), so U ∩ Q = ψ(Q₀ ⊗ ⟨Z⟩^t). The blueprint's δ, "the type of q|X₀", appears as
    the type of the induced form q₀ = `qInd q D`. For the exact tangent values, Lean reads the type of Q₀
    off the number of points: |a^⊥ ∩ Q| = 2(|Q₀| + 1) − 1 (`card_XY`), and |Q₀| = 35 / 27 on V 3 and
    135 / 119 on V 4 according to the type (`card_secQ_type`). Counting |a^⊥ ∩ Q| for every a (⚙) gives
    71, 55, 271, hence 84 (Q⁺(7,2)), 36 (Q⁻(7,2)) and 1260 = 4·315 (Q⁺(9,2)). This replaces the Witt-type
    statement "the complement has the same type as q", which the blueprint uses implicitly.

## B. Small corrections to the blueprint text

1. **blueprint/11 TIGHT-1 examples, X₄₉₆.** The degree 480 does not depend on the numerical flat state: the
   spectral bound is *exactly* 480 because Λ = √(496·31) = 124 is an integer, and the witness g = sign⟨P⟩ is
   counted directly (`X496_eq_480`). The flatness of the stored state is numerical only (|⟨P⟩| = 1/4 ± 10⁻⁴),
   so TIGHT-1 cannot be applied to it in exact arithmetic; it is not needed.

2. **blueprint/11 TIGHT-2.** The count 15360 = 120 × 128 rests on the number 120 of optimal violated sets, which
   the blueprint takes from the Sp(6,2)-orbit computation (X5) together with the SIC classification. Lean proves
   the factor 128 (every attained violated set has exactly 128 normalised assignments), not the factor 120. That
   every optimal violated set lies in the one orbit of size 120 needs the (i) ⇒ (ii) direction of TIGHT-1 plus
   the classification of 3-qubit Pauli-covariant SIC fiducials (Godsil–Roy); neither is formalised.

3. **GAME-1, quantum side.** Proved in full for every induced configuration (`quantum_perfect`): with the
   EPR identity ⟨Φ|A⊗Bᵀ|Φ⟩ = tr(AB)/d, Alice's outcome triples violating the line have probability 0 and
   Σ_o ⟨Φ|Π_o ⊗ (Π_{x}^{o_x})ᵀ|Φ⟩ = 1 for each point x of the line.

4. **lean/README (before this round).** The status table listed Realize/RealizeDeg (HARD-5/6/9 for genuine
   Pauli configurations) and Quadrics5 (deg Q^±(5,2)) as done, and they are: work items C1 and C4 of the round-3
   plan were already complete, with headline theorems `lines_DR`, `realized_degree`, `realized_sub_degree`,
   `induced_reduction`, `Qp5_eq_21`, `Qm5_eq_9`. The plan's request "restate reduction_ind/reduction_sub for
   genuine Pauli configurations" is `induced_reduction`.

## C. Not formalised, with reasons

| Item | Status | Reason |
|---|---|---|
| TIGHT-2 count 120, SIC correspondence | missing | see B.2 |
| DEN-2 running time O(n·\|L\|) | not stated | complexity statement; the algorithm `greedy` is computable and `greedy_half` is its correctness |
| GAME-2 lower side 5/6 + κ(2^{N−2})/6, GAME-3 | missing | uses ASY-5′ (Kendall τ of Gamma variables) |
| GAME-4, OP-1 | missing | noise model and Azuma–Hoeffding (probability theory) |
| NEG-1 numerical ceilings 297, 1488 | Python | λ_max of explicit matrices with irrational spectrum |
| ASY-5 (Haar), ASY-5′ | paper only | continuous probability (Dirichlet/Beta/Gamma, Lukacs, local limit); ASY-5 is formalised with a finite phase-state ensemble instead (PhaseStates.lean) |
| CONJ-1..4 | open | conjectures |
| HARD-10 | paper only | complexity theory, by design |
