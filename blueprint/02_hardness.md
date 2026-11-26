# 02. Hardness

Source problem. An XOR system is (H, b) with H ∈ F^{m×N}, b ∈ F^m. OPT(H,b) = min_x |Hx + b|. An E3 system has exactly
three 1's per row.

## HARD-1 (chain lemma) — `chain_lemma`
**Statement.** Let F₁,…,F_t be equations over variables A ∪ {w₁,…,w_{t−1}}, where w_i occurs exactly in F_i and
F_{i+1}, and ΣF_i = T is an equation over A. For each assignment of A,
min_w #{i : F_i violated} = [T violated].
**Steps.**
1. Lower bound: summing gives Σ(LHS_i + RHS_i) = LHS_T + RHS_T, since each w appears twice. So the number of violated
   F_i is ≡ [T violated] (mod 2); in particular it is ≥ 1 when T is violated.
2. Upper bound: choose w₁ to satisfy F₁, then w₂ to satisfy F₂, and so on. Then F_t holds iff T holds.
**Lean.** Induction on t. Parity via `Finset.sum` in ZMod 2.

## HARD-2 (ordered triangle split) — `triangle_split`
**Statement.** Replace each equation x_a+x_b+x_c=β by (w₂,a,w₁), (w₃,b,w₂), (w₁,c,w₃) with right-hand sides 0, 0, β
and fresh w's. Then: (a) OPT is preserved and |b'| = |b|; (b) two distinct equations share ≤ 1 variable;
(c) in each ordered triple (v₀,v₁,v₂), v₁ is original and v₀, v₂ are new.
**Steps.** (a) HARD-1 with the cyclic chain (t = 3; the w's are private to their triangle). (b) Within a triangle,
equations pairwise share exactly one w. Across triangles they share only original variables, and each equation has
exactly one. (c) Read off the triples.

## HARD-3 (arbitrary → E3) — `to_E3`
**Steps.**
1. Replace every variable v occurring in a row of length ≤ 2 by v'+v''+v''' in every row. This keeps OPT, because
   (v',v'',v''') ↦ sum is onto.
2. Split each row of length L > 3 into a chain of L−2 three-variable equations with fresh w's (HARD-1).

## Construction Φ (input: an E3 system satisfying HARD-2 (b),(c))
- Qubits: a block B_v of 3 qubits per variable v. For each E with b_E = 1, two registers R^E_1, R^E_2 of 2 qubits.
- **Copies**: c_{v,r} = Z^{λ_r} on B_v with λ₁=100, λ₂=010, λ₃=001, λ₄=111.
- **Chain of E = (v₀,v₁,v₂)**: s_{3(r−1)+i+1} = c_{v_i,r} (r = 1..4, i = 0..2), u_k = s₁+…+s_{k+1} (k = 1..9). Lines are
  ℓ₁ = {s₁,s₂,u₁}, ℓ_k = {u_{k−1}, s_{k+1}, u_k} for k = 2..9, and ℓ₁₀ = {u₉, s₁₁, s₁₂}.
- **Odd path** (b_E = 1, t ∈ {1,2}): α = s₁₁, β = s₁₂, γ = u₉. q_α is the first qubit of B_{v₁} and q_β the first
  qubit of B_{v₂}. The linear map φ is X₁↦X_{q_α}, X₂↦X_{q_β}, Z₁↦α, Z₂↦β, with private qubits ↦ R^E_t. The template
  rows are
  (ZI,IZ,ZZ)⊗II / (IX⊗IZ, XI⊗ZI, XX⊗ZZ) / (ZX⊗IZ, XZ⊗ZI, YY⊗ZZ).
  The path Π^E_t consists of rows 2 and 3 and the three columns of φ(template).
- Φ_ind = all chain lines + both paths of each negative E. Φ_sub = chain lines minus ℓ₁₀ of each negative E, plus
  path 1.

## Finite facts (certificates; all `decide`-sized)
T1 template rows and columns are lines. T2 9 template points distinct. T3 the template grid is an odd cycle.
T4 the register parts of path points are non-zero, constant on each column and distinct across columns.
T5 of the 8 one-per-column selections, only the two full rows sum to 0. T6 every path point has an even number of Y's.
C1 λ's: distinct, non-zero, sum to 0, no three sum to 0. C2 the 21 type-A points of one equation are distinct.
C3 the chain triples sum to 0. C4 the zero-sum triples among those 21 points are exactly the 10 chain lines.
C5 auxiliary supports: |supp u_k| = 3 except supp u₁ = {v₀,v₁} and supp u₉ = {v₁,v₂}.

## HARD-5 (well-definedness) — `construction_welldef`
**Statement.** All points of Φ_ind are non-zero and distinct, all designated triples are lines, and every point
has an even number of Y's. Hence everything lies on Q⁺.
**Steps.**
1. Type A points (copies and aux) are Z-type with no register part. Type B points (path points) have a non-zero
   register part (T4).
2. Distinctness of A vs B: the register parts differ.
3. B vs B: points on different registers differ. On the same register they are distinct by injectivity of φ and T2.
4. A vs A: copies are distinct by construction. Copies have support size 1 and aux points have support ≥ 2 (C5).
   Aux points of the same E are distinct (C2). Aux points of E ≠ E' cannot be equal: equal labels give equal
   supports of size ≥ 2 inside vars(E) ∩ vars(E'), contradicting HARD-2(b).
5. Chain lines are Z-type (they commute) and sum to 0 by the definition of u_k and C3.
6. Path lines: φ is linear and preserves ω (check ω(X_{q_α}, α) = 1, ω(X_{q_α}, β) = 0, etc.), so T1 transports.
7. Y-count: φ(T) has a Y only at q_α (resp. q_β), and exactly when T's first (resp. second) virtual factor is Y. Then T6.

## HARD-6 (closure lemma) — `closure`
**Statement.** Every zero-sum triple of distinct points of Φ_ind is a designated line.
**Steps.**
1. *Triple contains a type-B point.* Register parts must cancel. Path points have non-zero register parts, and only
   points of the same path share a register. Case (i): exactly two points share a register and the third has none.
   Equal register parts mean the same column (T4), so the third point is p₂ⱼ+p₃ⱼ = φ(T₁ⱼ) = hⱼ and the triple is a
   column. Case (ii): all three points lie on one register, so one per column, and T5 leaves only the two rows.
2. *All three points of type A.* Each block in the union of supports must lie in ≥ 2 of the supports.
   - (a) Only copies: they lie in one block, and three distinct λ's never sum to 0 (C1). Impossible.
   - (b) The triple lies inside Π(E), the 21 type-A points of one equation (they vanish off E's blocks): by C4 it is
     a chain line.
   - (c) Otherwise there is an aux u of E and a point r ∉ Π(E):
     - r is a copy of w ∉ E. Then block w needs the third point q. If q is a copy of w, supp u is uncovered.
       If q is an aux of E' ∋ w, then supp u ⊆ supp q gives |E∩E'| ≥ 2, so E = E', contradicting w ∉ E.
     - r is an aux of E' ≠ E. Then |supp u ∩ supp r| ≤ 1.
       - If q is a copy, both set differences are non-empty and only q's single block can cover them. Impossible.
       - If q is an aux of E (or of E'), then r = u+q is supported in E, so supp r ⊆ E∩E', which has size ≤ 1.
         Impossible.
       - If q is an aux of a third equation E'', the supports pairwise meet in ≤ 1 block and cover every block twice.
         So they form a triangle {x,y},{y,z},{z,x}. Supports of size 2 are first or last pairs, each of which
         contains exactly one original variable (HARD-2(c)). That makes the triangle bipartite, which is impossible.
**Lean.** This is the longest proof. Formalise supports as `Finset` of blocks. Steps 2(b) and 1 reduce to `decide`
on the generic gadgets (T4, T5, C4).

## HARD-7 (odd path lemma) — `odd_path`
**Statement.** For fixed values on α, β, γ with τ = s(α)+s(β)+s(γ), the minimum over the path points of the number
of violated path lines is [τ ≠ 1].
**Steps.**
1. The grid (ℓ₁₀ plus the path) is a cycle. By ALG-2 its parity equals the template's parity, which is 1 (T3).
   e(ℓ₁₀) = 0 because ℓ₁₀ is Z-type. Hence the path signs sum to 1.
2. The path lines sum to {α,β,γ}, so τ ≠ 1 forces at least one violation.
3. If τ = 1: choose s(p₂₁), s(p₂₂) freely and s(p₂₃) to satisfy row 2, then the p₃ⱼ from the columns. Row 3 then
   holds by summation.

## HARD-8 (one equation) — `one_equation`
**Statement.** With z_v = Σ_r s(c_{v,r}) and Y_E = Σ_{v∈E} z_v: the minimum over the private points of E of its
violated lines is [Y_E ≠ b_E] + b_E in Φ_ind, and [Y_E ≠ b_E] in Φ_sub.
**Steps.** Fix s(u₉) and put τ = s(u₉)+s(α)+s(β). The lines ℓ₁..ℓ₉ form a chain in u₁..u₈ with sum
"s(u₉) = Σ_{i≤10}s(s_i)", so by HARD-1 they contribute [τ ≠ Y_E]. The remaining lines contribute g(τ), where:
- b=0: g(τ) = [τ≠0] (from ℓ₁₀);
- b=1 in Φ_ind: g(τ) = [τ≠0] + 2[τ≠1];
- b=1 in Φ_sub: g(τ) = [τ≠1].
Minimising over τ gives the claim (a two-case check).

## HARD-9 (main theorems) — `induced_degree`, `sub_degree`
**Statement.** deg Φ_ind = OPT + |b|, and by HARD-6 Φ_ind is induced. deg Φ_sub = OPT.
**Steps.** Lines are partitioned by equation, and only copies are shared. For fixed copies, sum HARD-8 over E. The
map s ↦ z (sum of the 4 copies) is onto F^N. Then use HARD-2(a).
**Projection to the source**: z restricted to the original variables violates ≤ |H'z+b'| original equations, since
each original equation is the sum of its triangle (HARD-1 lower bound).

## HARD-10 (complexity) — informal in Lean (no complexity library)
NP membership. Exact NP-hardness and the (2−δ) gap for induced configurations: pre-flip b by b+Hs with |b+Hs| ≤ m/2,
found by conditional expectations; then Håstad. Any constant for sub-configurations; W[1]-hardness and
W[1]-hardness of approximation in k (DFVW 1999; Bhattacharyya et al., Thm 5.1, in whatever reduction model it
uses): the reduction preserves OPT exactly.
**Lean scope.** Formalise only the value identities HARD-9 and the size bounds. The complexity consequences stay
on paper.

## HARD-11 (no deletion; unavoidable constant) — `no_deletion`
1. In an induced configuration, if a set A of lines sums to a commuting triple {a,b,c}, then a+b+c = 0, so it is a
   line inside P and therefore present.
2. If the retained line h (sign e) interacts with its gadget only through the parity t, the cost is
   [t≠e] + g(t). Flipping needs 1 + g(e+1) < g(e), so the minimum is 1 + g(e+1) ≥ 1.

## HARD-12 (tractable class) — `deg_two_points`
If every point lies on ≤ 2 lines, the cycle space is spanned by the components (of the line-adjacency graph) that
contain no point of degree 1. These components are disjoint, so deg = the number of odd components.
