# 06. Cones and sections

## CONE-1 (cone theorem) — `cone_degree`
**Definition.** Let G' be a configuration on n qubits, t ≥ 1, and P' ⊇ P(G') a finite point set. Cone_t(G') lives on
n+t qubits, with points v⊗Z^τ. Its lines are:
(a) lifts {a⊗Z^α, b⊗Z^β, c⊗Z^{α+β}} for {a,b,c} ∈ L(G') and α, β ∈ F^t;
(b) vertex lines {v⊗Z^τ, v⊗Z^{τ'}, I⊗Z^{τ+τ'}} for v ∈ P', τ ≠ τ';
(c) lines inside the vertex {Z^τ, Z^{τ'}, Z^{τ+τ'}}.
**Statement.** deg Cone_t(G') = 4^t deg G'.
**Steps.**
1. Signs: P(v⊗Z^τ) = P(v)⊗Z^τ (no new Y's). A lift has the base sign, and types (b) and (c) have sign 0. In the group
   law of ALG-0 the extra qubits contribute only Z's, which have no x-part, so no extra phase arises.
2. Upper bound: x(v⊗Z^τ) = y(v) with y optimal for G' (extended by 0 to P'), and x(Z^τ) = 0. Types (b) and (c) are
   satisfied, and a lift is violated iff its base line is. Total 4^t deg G'.
3. Lower bound (uniform cover, TR-1'): let U = span P(G'), d = dim U ≥ 2. For each linear φ : U → F^t,
   Σ_φ := {lifts with α = φ(a), β = φ(b)} is a copy of G' (v ↦ v⊗Z^{φ(v)} is ω-preserving and line-preserving), so
   deg Σ_φ = deg G' (ALG-3). Each lift lies in exactly 2^{t(d−2)} of the 2^{td} sets Σ_φ, because a and b are
   independent. Hence #violated lifts ≥ 4^t deg G'.
**Lean.** Step 3 needs a count of linear maps with prescribed values on two independent vectors. Mathlib: extend
to a basis (`Basis.extend`); the count is |Hom(F^{d−2}, F^t)|.

## CONE-2 (sections of W) — `W_section_degree`
For a subspace X ⊆ F^{2N} with radical R (dim t) and dim X − t = 2k: deg W(X) = 4^t deg W(2k−1,2), where
deg W(1,2) = 0.
**Steps.**
1. Write X = R ⊕ X₀ with X₀ non-degenerate. Map X isometrically onto F^{2k} ⊕ ⟨Z_{k+1..k+t}⟩ using a symplectic basis
   of X₀ and any basis of R.
2. Commuting zero-sum triples of the image: write each point as u⊗Z^τ. Then u₁+u₂+u₃ = 0, so either all u's vanish,
   or two coincide and the third vanishes, or the u's form a line of W(2k−1).
3. Hence the image is Cone_t(W(2k−1)) with P' = all non-zero vectors. Conclude with ALG-3 and CONE-1.

## CONE-3 (sections of quadrics) — `Q_section_degree`
Let X have radical R (dim t), so that q|_R is linear. (a) If q|_R = 0, deg = 4^t deg Q^δ(2k−1) with δ the type of
q|_{X₀}. (b) If q|_R ≠ 0, deg = 4^{t−1} deg W(2k−1).
**Steps.** (a) The singular points are r+y with y singular or 0. The isometry onto the standard cone is as in CONE-2,
with P' = singular points of X₀.
(b) Let R_s = ker q|_R, r₀ with q(r₀) = 1, and Y = ⟨r₀⟩ ⊕ X₀. Singular y ∈ Y are exactly εr₀ + x with ε = q(x), and
y ↦ x is a bijection onto X₀∖0. It preserves ω and lines: commuting singular y₁, y₂ have y₁+y₂ singular, which is
the unique lift of x₁+x₂. So the singular part of Y is ≅ W(2k−1), and X∩Q ≅ Cone_{t−1} of it.
**Corollaries.**
- Tangent hyperplane: 4·deg Q^ε(2N−3). Non-tangent hyperplane: deg W(2N−3).
- Exact values: W(7,2) tangent 252; Q⁺(7,2) tangent 84; Q⁻(7,2) tangent 36; Q^±(7,2) non-tangent 63; Q⁺(9,2) tangent
  1260 (uses deg Q⁺(7,2) = 315, Li–Gupta–Ganesh).
