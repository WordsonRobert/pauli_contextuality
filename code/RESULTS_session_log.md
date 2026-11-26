# Contextuality degree of Pauli configurations — research log

Notation: a configuration is a set of n-qubit Pauli points with 3-point contexts (lines {a, b, a+b}, pairwise
commuting); deg = min over ±1 assignments of #violated lines; ρ(C) = deg(C)/#lines.
W_N = W(2N-1,2) (all lines), Q±_N = hyperbolic/elliptic quadric (points with x·z = 0, resp. x·z + x1 + z1 = 0).

## A. Complexity (all lines-only, verified by randomised tests against brute force)

| # | Statement | Status |
|---|-----------|--------|
| A1 | deg = min_x |Hx + e| (MIN-UNSAT of 3-XOR); max ratio over N-qubit configs is ρ(W_N) | proof |
| A2 | Observables in ≤ 2 contexts: deg = # odd components (linear time) | proof + 2000 tests |
| A3 | Line sign-flip gadget (magic square, deletion type) | proof + 30 tests |
| A4 | Deg of sub-configurations of one hyperbolic quadric is NP-complete, NP-hard to approximate within any constant; W[1]-hard (and W[1]-hard to approximate) in k = deg; in XP. Linear size, Θ(log n) qubits | proof + 79 tests |
| A5 | **Closure lemma**: in an induced configuration (contexts = all lines in the point set) any set of lines whose boundary is a commuting triple re-creates that triple as a line ⇒ deletion gadgets are impossible | proof |
| A6 | **Induced hardness**: for an arbitrary set of even-Y Pauli observables with ALL their lines as contexts, deg is NP-hard (deg = OPT + f), NP-hard to approximate within 3/2 − δ. Uses two odd "grid paths" (magic square through the line) per negative equation + ordered triangle split | proof sketch (block-support case analysis + finite template check) + 26 tests, closure == designated in every test |

Induced construction: `induced_red.py` (template search `grid_template.py`, tests `test_induced*.py`).

## B. Fixed geometries ("bridge")

**Transfer lemma (B1).** If Aut(G) (symplectic maps preserving G) is transitive on lines of G and S is symplectically
embeddable as a sub-configuration of G, then ρ(G) ≥ ρ(S).  Proof: average |V ∩ gS| ≥ deg(S) over g ∈ Aut(G);
degree is a hypergram invariant (Muller–Giorgetti).

Corollaries (rigorous):
* B2. ρ_N := ρ(W_N) is the maximum ratio over all configurations on ≤ N qubits; ρ_N is non-decreasing.
* B3. **Every configuration on ≤ 3 qubits has deg ≤ ⌊#lines/5⌋** (ρ_3 = 63/315 = 1/5); tight (doily, grids…).
* B4. Every 4-qubit configuration has deg ≤ (5/17)·#lines (explicit witness for W(7,2) with 1575 violations).
  Every 5-qubit configuration has deg ≤ 0.36201·#lines (witness 31479 for W(9,2)).
* B5. Quadric ladder: ρ(Q±_N) ≤ ρ_N; ρ(Q+_{N+1}), ρ(Q−_{N+1}) ≥ max(ρ(Q+_N), ρ(Q−_N)).
* B6. **Unconditional (integrality + transfer)**: deg Q−(7,2) ≥ ⌈1071/5⌉ = 215 (doily averaging), and Q−(7,2) is the
  section of Q+(9,2) by E^⊥, E = ⟨Y5, X5·Y4⟩ anisotropic (checked: 119 points, 1071 lines, embed_check.py). Hence
  **deg Q+(9,2) ≥ ⌈23715·215/1071⌉ = 4761 > 4743 = L/5**: the answer to Li–Gupta–Ganesh's question
  "is deg Q+(9,2) = 4743?" is **no**, and their conjecture "deg Q+(2N−1,2) = L/5 whenever 5 | L" fails at N = 5.
  Also deg W(7,2) ≥ 1075 (was 1071), deg W(9,2) ≥ 17457 (from Q+(9,2)), deg Q−(9,2) ≥ 3942.
* B7. **Collapse**: any lower bound d on deg Q−(7,2) gives deg W(7,2) ≥ 5d and deg Q+(9,2) ≥ ⌈23715 d/1071⌉.
  In particular deg Q−(7,2) = 315 ⇒ deg W(7,2) = 1575 and deg Q+(9,2) = 6975 ≠ 4743
  (would answer Li–Gupta–Ganesh's question negatively). Q−(7,2) ≥ 216 alone already refutes 4743.

Atlas (witnesses in data/witnesses, recounted by verify_witness.py):

| N | W_N lines / deg | Q+_N lines / deg | Q−_N lines / deg |
|---|---|---|---|
| 2 | 15 / 3 | 6 / 1 | 0 |
| 3 | 315 / 63 | 105 / 21 (SAT-proved here) | 45 / 9 (SAT-proved here) |
| 4 | 5355 / [**1075**, 1575] | 1575 / 315 | 1071 / [215, 315] |
| 5 | 86955 / [**17457**, 31479] | 23715 / [**4761**, 6975] | 19635 / [**3942**, 7087] |

Observation: the three upper bounds W(7,2), Q−(7,2), Q+(9,2) are all exactly 5/17 of the lines; tabu search from
independent seeds hits them immediately and never improves. Conjecture: ρ_4 = ρ(Q−_4) = ρ(Q+_5) = 5/17.

Structure found: Q−(7,2) ≅ {x ∈ GF(256)* : Tr_{16/2}(x^17) = 0}; μ17 acts freely (119 = 7·17 points, 63 line orbits).

## C. Attempts that did not close (for the paper's "methods tried")
* Quadratic-form assignments: optimum = #negative lines (no gain) for W, Q± with N ≤ 3.
* Hyperplane-section / quadric flip-sets are not optimal coset representatives.
* Tangent-cone sections have ratio < 1/5; norm-class unions max ≈ 0.272; two-part line partitions sum < 315.
* Sub-configurations with (heuristic) ratio > 1/5 exist down to ~70 points (S73: 226 lines, tabu 50; S78: 271 lines,
  tabu 64), but exact certification (CryptoMiniSat + cardinality, CP-SAT, RC2) did not finish in ~50 min on 2 cores.
  **Certifying deg(S73) ≥ 46 would unconditionally give deg Q+(9,2) ≥ 4827 > 4743, W(7,2) ≥ 1090, Q−(7,2) ≥ 218.**

Note: scripts expect instance/witness files in the working directory; copy from data/ before running.
