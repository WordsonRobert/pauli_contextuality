# 00. Conventions and basic objects

Every later file uses these definitions. Lean names that are suggested (in `lean/`) appear in `code font`.

## Vectors and Paulis
- `F := ZMod 2`. An **n-qubit Pauli label** is p = (x | z) ∈ F^n × F^n, i.e. `V n := (Fin n → F) × (Fin n → F)`.
- **Symplectic form**: ω(p, q) = Σ_i (x_i z'_i + z_i x'_i) ∈ F, written `omega`. It is bilinear, symmetric and
  alternating (ω(p, p) = 0).
- **Point**: a non-zero p.
- **Y-count**: y(p) = #{ i : x_i = z_i = 1 } ∈ ℕ.
- **Canonical operator**: P(p) = i^{y(p)} X^x Z^z. For the formalisation we do NOT need matrices. Use the
  **Pauli group law** on pairs (k, p), k ∈ ZMod 4:

      (k1, p) · (k2, q) = (k1 + k2 + 2·⟦z_p · x_q⟧, p + q)

  where ⟦z_p·x_q⟧ ∈ ZMod 4 is the integer dot product Σ_i z_p,i x_q,i (computed in ℕ, then cast). The canonical
  element is P(p) = (⟦y(p)⟧, p). This is the Heisenberg–Weyl group. Associativity reduces to an identity in ZMod 4,
  and (k, 0) is central. A product of elements whose labels sum to 0 is (k, 0). It equals ±I when k ∈ {0, 2}.
  (Matrix model: (k, (x|z)) ↦ i^k X^x Z^z. This is only for intuition.)
- **Commutation**: P(p)P(q) = (−1)^{ω(p,q)} P(q)P(p), i.e. the two products differ by (2·ω, 0).

## Lines, signs, configurations
- **Line**: a 3-set {a, b, c} of distinct points with a + b + c = 0 and ω(a, b) = 0. Then all three pairwise
  commute.
- **Sign** e({a,b,c}) ∈ F: P(a)P(b)P(c) = (2·e, 0) in the group law above. It is independent of the order of the
  three factors because they commute.
  Explicit formula (used by every script): with k = y(a) + y(b) + y(c) + 2(z_a·x_b + (z_a + z_b)·x_c) ∈ ZMod 4, we have
  k ∈ {0, 2} and e = k/2.
- **Configuration** C: a finite set of lines L(C). Its points are P(C) = ∪ lines, and each line carries its sign.
  Abstractly (enough for most theorems): a finite point set, a finite set of 3-subsets ("lines"), and a sign
  function L → F.
- **Assignment**: s : P(C) → F. A line ℓ = {a,b,c} is **violated** by s iff s(a) + s(b) + s(c) ≠ e(ℓ).
- **Degree**: deg(C) = min over s of #violated lines. **Ratio**: ρ(C) = deg(C)/|L(C)|.
- **Incidence matrix**: H ∈ F^{L×P}, H_{ℓ,p} = [p ∈ ℓ]. The violated set of s has indicator Hs + e.
- **Cycle**: y ⊆ L with every point in an even number of lines of y, i.e. Hᵀ y = 0. It is **odd** if Σ_{ℓ∈y} e(ℓ) = 1.

## Geometries used
- W(2n−1, 2): all lines of F^{2n} (all commuting zero-sum triples of points).
- Quadratic forms polarising to ω: q⁺(x|z) = x·z mod 2 (hyperbolic; its points are the real Paulis, i.e. those with
  an even number of Y's), q⁻(x|z) = x·z + x₁ + z₁ mod 2 (elliptic). A quadric Q^±(2n−1,2) consists of the points
  with q(p) = 0 and the lines all of whose points satisfy q = 0.
- Counts (verified): W(3,2) 15/15, W(5,2) 63/315, W(7,2) 255/5355, W(9,2) 1023/86955; Q⁺(5,2) 35/105,
  Q⁻(5,2) 27/45, Q⁺(7,2) 135/1575, Q⁻(7,2) 119/1071, Q⁺(9,2) 527/23715, Q⁻(9,2) 495/19635 (points/lines).
- **Doily**: a configuration isomorphic to W(3,2) (15 points, 15 lines, 3 lines per point).
- **Grid** (Peres–Mermin square): 9 points and 6 lines, in two parallel classes of 3 disjoint lines.

## Embeddings and symmetry
- **Embedding** π : C → G: an injective map on points that preserves ω and sends lines to lines.
- Aut(G): the symplectic maps g ∈ Sp(2n,2) that permute L(G). For quadrics, O(q) ≤ Sp. Reflections
  t_c(x) = x + ω(x,c)c with q(c) = 1 lie in O(q).
