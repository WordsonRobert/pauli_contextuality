# 03. Transfer, rigidity, stability, profile bound

Throughout: G is a configuration, Γ a finite group acting on P(G) by ω-preserving maps that permute L(G), and S is
embedded in G by π. Translates gπ(S) inherit G's signs, and deg(gπ(S)) = deg S by ALG-3.

## TR-1' (uniform-cover lemma) — `uniform_cover` (recommended Lean core, no groups)
**Statement.** Let F be a finite family (multiset) of sub-configurations of G such that every line of G lies in
exactly c ≥ 1 members, and every member has deg ≥ d. Then deg G ≥ ⌈|F|·d / c⌉.
**Steps.**
1. Let V be the violated set of an optimal s. For each S ∈ F, the restriction of s violates V ∩ L(S), so
   |V ∩ L(S)| ≥ d.
2. Σ_{S∈F} |V ∩ L(S)| = Σ_{ℓ∈V} #{S ∋ ℓ} = c|V| (double counting).
3. Hence c|V| ≥ |F|d. Since |V| is an integer, |V| ≥ ⌈|F|d/c⌉.
**Lean.** `Finset.sum_comm` and `Finset.card_eq_sum_ones`. The ceiling step is `Nat.div_le_iff` / `Nat.ceil`.

## TR-1 (transfer, group version) — `transfer`
**Statement.** If Γ is transitive on L(G), then deg G ≥ ⌈|L(G)|·deg S/|L(S)|⌉.
**Steps.** Apply TR-1' to the family F = (gπ(S))_{g∈Γ} (a multiset of size |Γ|). By transitivity each line lies in
c = |Γ||L(S)|/|L(G)| members: orbit–stabiliser gives |{g : gm = ℓ}| = |Γ|/|L(G)|. Then |F|d/c =
|L(G)|·deg S/|L(S)|.

## TR-2 (equality ⇔ rigidity) — `rigidity`
**Statement.** Call s S-tight if |V ∩ gπ(S)| = deg S for all g. Then: ρ(G) = ρ(S) ⇔ every optimal s is S-tight ⇔
some s is S-tight. Every S-tight s is optimal. If |L(G)|deg S/|L(S)| ∉ ℤ, then ρ(G) > ρ(S).
**Steps.** In TR-1' each term is ≥ d and the sum is fixed. Equality in the sum ⇔ every term equals d. The last
sentence follows from integrality.

## TR-3 (stability) — `stability`
**Statement.** For any s, put Δ_g = |V∩gπS| − deg S and D = |V| − ρ(S)|L(G)|. Then
(1/|Γ|)ΣΔ_g = (|L(S)|/|L(G)|)·D, and the fraction τ of non-tight translates satisfies
(|L(S)|/|L(G)|)·D/(|L(S)|−deg S) ≤ τ ≤ (|L(S)|/|L(G)|)·D.
**Steps.** The identity is TR-1' step 2 with transitivity, without assuming optimality. For the bounds use
1 ≤ Δ_g ≤ |L(S)|−deg S on the non-tight translates.
**Corollaries.** (i) If |V| ≤ deg G + t, then τ ≤ (|L(S)|/|L(G)|)(deg G − ρ(S)|L(G)| + t).
(ii) Every s is non-tight on at least a fraction (|L(S)|/|L(G)|)(⌈ρ(S)|L(G)|⌉ − ρ(S)|L(G)|)/(|L(S)|−deg S) of
the translates.

## TR-4 (profile bound) — `profile_bound`
**Statement.** Let Γ have line orbits O₁..O_r, let S_j (j = 1..k) be embedded with d_j = deg S_j and
a_ij = |π_j(L(S_j)) ∩ O_i|. Then the profile n_i = |V ∩ O_i| of any assignment satisfies
Σ_i a_ij n_i/|O_i| ≥ d_j for all j. So deg G ≥ IP := min{Σn_i : n ∈ ℤ, 0 ≤ n_i ≤ |O_i|, constraints} ≥ LP, and
LP = max{Σ_j W_j d_j : W ≥ 0, Σ_j a_ij W_j ≤ |O_i|} by duality.
**Steps.** Averaging over Γ: for m, ℓ ∈ O_i, |{g : gm = ℓ}| = |Γ|/|O_i|. So
avg_g |V ∩ gπ_j(S_j)| = Σ_i a_ij n_i/|O_i|, and each term is ≥ d_j.
**Multi-orbit rigidity** (`profile_rigidity`): if deg G = LP and W* is optimal, then every optimal assignment is
tight on all translates of S_j whenever W*_j > 0.
Steps: deg G = Σn_i ≥ Σ_i n_i Σ_j a_ij W*_j/|O_i| = Σ_j W*_j A_j ≥ Σ_j W*_j d_j = LP. Equality forces A_j = d_j.

## TR-5 (extremality) — `rho_max`, `rho_mono`, `quadric_ladder`
1. Every N-qubit configuration S is a sub-configuration of W(2N−1,2) (same signs). Sp(2N,2) is transitive on its lines
   (Witt). So ρ(S) ≤ ρ_N := ρ(W(2N−1,2)).
2. Monotonicity: pad W(2N−1) into N+1 qubits and apply 1.
3. 1/5 ≤ ρ_N ≤ 1/2: the lower bound is the doily (TQ-1). For the upper bound, a random s violates each line with
   probability 1/2.
4. Quadric ladder: (F^{2N+2}, q^ε) = (complement plane of type εδ) ⊥ (F^{2N}, q^δ), using Arf additivity. This gives
   an embedding Q^δ(2N−1) → Q^ε(2N+1), and O(q) is line-transitive (Witt).
**Lean note.** Witt's extension theorem is not in Mathlib. Avoid it: use TR-1' with an explicit family whose uniform
coverage is checked by computation (see 07, 09).
