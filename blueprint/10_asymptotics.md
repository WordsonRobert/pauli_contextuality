# 10. Asymptotics of the contextuality ratio: the spectral method

**Round-2 targets:**

- **A.** Infinitely many strict jumps of ρ_N, and a construction that carries an improved ratio to larger geometries.
- **B.** A universal asymptotic upper or lower bound: lim inf / lim sup of ρ_N.
- **C.** Decide whether lim ρ_N = 1/2.

**Outcome.** All three are **resolved**.

- **C.** lim ρ_N = 1/2.
- **B.** Both lim inf and lim sup equal 1/2. The rate is exactly 2^{−N/2} up to constants:
  0.2679·2^{−N/2} ≤ 1/2 − ρ_N ≤ 2^{−N/2} for N ≥ 6. ASY-5′ improves the asymptotic constant to
  (2/π)^{3/2} ≈ 0.508 ≤ lim inf (1/2 − ρ_N)·2^{N/2} ≤ lim sup ≤ 1.
- **A.** ρ_N is non-decreasing (transfer). It has a strict jump in every window of 4 steps from N = 6 on, and it is
  strictly increasing on 3 ≤ N ≤ 11.

The tool is a new exact **trace formula**: the degree equals |L|/2 minus a cubic trace of a ±1 combination of Pauli
operators. It has several by-products:

- new lower bounds: deg W(7,2) ≥ 1451 (was 1080) and deg W(9,2) ≥ 28786 (was 17538);
- a one-line proof that deg W(5,2) = 63;
- the first proof that deg Q⁺(7,2) = 315;
- the identification of the optimal W(5,2) assignments with Hoggar SICs.

Code: `code/asym/`. Checks: `certificates/certify.py`, group X (X1–X10).

---

## ASY-0. Setup

**Notation.**

- N qubits, d = 2^N.
- Labels a = (x|z) ∈ F₂^{2N}, with canonical Hermitian Pauli P_a = i^{x·z} X^x Z^z.
- V* = F₂^{2N} \ {0}.
- For commuting a, b, define χ(a,b) ∈ {±1} by P_a P_b = χ(a,b) P_{a+b}.
  - Equivalently, P_a P_b P_{a+b} = χ I. This is the line sign: χ = (−1)^e in the notation of `00_conventions`.
  - χ is symmetric in a and b. For a line ℓ = {a, b, c}, every ordered pair taken from ℓ gives the same value.
  - So χ(ℓ) is well defined.
- An **induced configuration** is a set X ⊆ V* whose lines are *all* commuting triples {a, b, a+b} ⊆ X.
  - Examples: W(2N−1,2) (X = V*), the quadrics Q^±(2N−1,2), and all subspace sections.
  - For a quadric this is automatic: q(a+b) = q(a) + q(b) + ω(a,b).
- **Assignment** g : X → {±1}. Line ℓ is violated iff χ(ℓ) g(a) g(b) g(c) = −1.
- M_g := Σ_{a∈X} g(a) P_a, a d×d Hermitian matrix.
- **Ratio and deficit.** |L_N| = (4^N−1)(4^{N−1}−1)/3 is the number of lines of W(2N−1,2).
  ρ_N = deg W(2N−1,2)/|L_N| and δ_N = 1/2 − ρ_N. Note 12|L_N| = (4^N−1)(4^N−4).

**Lemma ASY-0 (trivial upper bound).** deg X ≤ |L_X|/2 for every configuration.

*Proof.* Average the number of violated lines over all 2^{|X|} assignments. For a fixed line, exactly half of the
assignments violate it. Hence the average is |L|/2, and the minimum is at most the average. ∎

Lean: `deg_le_half` (Finset double counting; no matrices).

---

## ASY-1. Trace formula — `trace_formula` (exact)

**Theorem.** For every induced configuration X and every g:

  Σ_{ℓ∈L_X} χ(ℓ) g(a)g(b)g(c) = tr(M_g³)/(6d).

Hence

  viol(g) = |L_X|/2 − tr(M_g³)/(12d),   deg X = |L_X|/2 − max_g tr(M_g³)/(12d).

**Proof steps.**

1. Expand: tr(M³) = Σ_{a,b,c∈X} g(a)g(b)g(c)·tr(P_a P_b P_c).
2. P_a P_b is a phase times P_{a+b}, so P_a P_b P_c is a phase times P_{a+b+c}.
   - tr P_v = 0 for v ≠ 0, and tr I = d.
   - So only triples with c = a + b contribute. Then a ≠ b, and c ∈ X with c ≠ 0.
3. Case ω(a,b) = 1 (anticommuting).
   - P_a P_b = ±i P_{a+b}, so tr(P_a P_b P_{a+b}) = ±i·d.
   - The ordered pair (b,a) gives P_b P_a = −P_a P_b, so the two terms cancel. Their g-weight g(a)g(b)g(a+b) is the same.
4. Case ω(a,b) = 0. Then {a, b, a+b} is a line of X, because X is induced.
   - tr(P_a P_b P_{a+b}) = d·χ(a,b).
   - Each line arises from exactly 6 ordered pairs (a,b), all with the same χ and the same g-product.
5. So tr(M³) = 6d Σ_ℓ χ(ℓ) g g g. Finally Σ_ℓ χ g g g = |L| − 2 viol(g). ∎

**Check X1.** Random g on W, Q⁺ and Q⁻ for N = 2, 3, 4: the identity holds exactly (`code/asym/spectral.py`).

**Variant with the identity (used for products).**

- For h : F₂^{2N} → {±1} with h(0) = +1, put m_h = Σ_{all a} h(a) P_a = I + M_g, where g = h|_{V*}.
- Define τ(h) := tr(m_h³)/d.
- tr m = d and tr m² = d·4^N. Expanding (M+I)³ gives the exact relation

    Σ_{lines of W} χ g g g = (τ(h) − 3·4^N + 2)/6,   so   viol(g) = |L_N|/2 − (τ(h) − 3·4^N + 2)/12.

**Lean.** `PauliMat N a : Matrix (Fin (2^N)) (Fin (2^N)) ℂ` as a Kronecker product. Needed lemmas:

- `pauli_mul`: P_a P_b = i^{β(a,b)} P_{a+b}, with β from the ALG-0 group law;
- `trace_pauli`: tr P_a = if a = 0 then d else 0.

The rest is `Finset.sum` manipulation: pair (a,b) with (b,a) in step 3, and group by lines in step 4 (each line ↔ 6
ordered pairs). This is the first matrix-level milestone.

---

## ASY-2. Spectral lower bound for induced configurations — `spectral_lower`

**Theorem.** For every induced configuration X ⊆ V* on N qubits, with n = |X|:

  deg X ≥ |L_X|/2 − (Λ F − F²/(dΛ))/(12d),   where F = d·n and Λ = √(n(d−1)).

**Proof steps.**

1. **Rayleigh bound** (λ_max(M_g) ≤ Λ). Take a unit vector v and write e_a = ⟨v|P_a|v⟩ ∈ ℝ.
   - ⟨v|M_g|v⟩ = Σ_{a∈X} g(a) e_a ≤ Σ_{a∈X} |e_a| ≤ √n·(Σ_{a∈X} e_a²)^{1/2} (Cauchy–Schwarz).
   - **Pauli completeness:** Σ_{all a} e_a² = d·|v|⁴ = d. This holds because ρ = |v⟩⟨v| = d^{−1} Σ_a e_a P_a, so
     tr ρ² = d^{−1} Σ e_a² = 1.
   - e_0 = 1, so Σ_{a∈X} e_a² ≤ d − 1.
   - Hence ΛI − M_g ⪰ 0.
2. **Trace facts.** tr M_g = 0, because 0 ∉ X and tr P_a = 0. Also tr M_g² = d·n = F, because tr(P_a P_b) = d·[a = b].
3. **Cubic inequality (no eigenvalues needed).** For any real μ:
   - (M + μI)² ⪰ 0 and ΛI − M ⪰ 0, so tr[(ΛI − M)(M + μI)²] ≥ 0.
     (Write it as tr[B(ΛI − M)B] with B = M + μI Hermitian; B A B ⪰ 0.)
   - Expanding and using step 2: tr M³ ≤ (Λ − 2μ)F + dΛμ².
4. Take μ = F/(dΛ). This gives tr M³ ≤ ΛF − F²/(dΛ).
5. Insert into ASY-1. ∎

**Equality.** It requires (Λ − λ)(λ + μ)² = 0 for every eigenvalue λ, so the spectrum lies in {Λ, −μ}. If k
eigenvalues equal Λ, then tr = 0 gives kΛ = (d−k)μ, and tr M² = F gives kΛ² + (d−k)μ² = F. For W and for Q⁺(7,2)
these force k = 1, so the spectrum is {Λ¹, (−μ)^{d−1}}.
Equality in step 1 also forces |e_a| = const on X and e_a = 0 off X ∪ {0} for the top eigenvector. See ASY-4.

**Lean.** Needs `Matrix.PosSemidef`, `Matrix.PosSemidef.conjTranspose_mul_mul_same`, `Matrix.PosSemidef.trace_nonneg`,
`inner_mul_le_norm_mul_norm` (or `Finset.sum_mul_sq_le_sq_mul_sq`), and `Pauli_completeness`. Prove the last one by
induction on N via Kronecker products, or from orthogonality tr(P_a P_b) = d δ_ab (the P_a form an orthogonal basis of
M_d(ℂ)). No spectral theorem is needed. Everything is a trace inequality.

---

## ASY-3. The full symplectic space: lower bound and the limit — `W_lower`, `rho_tendsto_half`

**Theorem.** With n = 4^N − 1 in ASY-2:

  deg W(2N−1,2) ≥ |L_N|/2 − (4^N−1)^{3/2}(2^N−2) / (12√(2^N−1)),

equivalently δ_N ≤ √(4^N−1)(2^N−2) / ((4^N−4)√(2^N−1)) ≤ 2^{−N/2}.

**Proof steps.**

1. Here Λ² = (4^N−1)(d−1) and F = d(4^N−1), so F/(dΛ²) = 1/(d−1).
   - ΛF − F²/(dΛ) = ΛF(1 − 1/(d−1)) = d(4^N−1)^{3/2}(d−2)/√(d−1).
   - Divide by 12d to get the bound.
2. **Last inequality.** Put t = d. Need (t²−1)(t−2)²t ≤ (t²−4)²(t−1), i.e. t(t+1) ≤ (t+2)². This is true.
3. **Corollary (Target C).** 1/2 − 2^{−N/2} ≤ ρ_N ≤ 1/2 by ASY-0. Hence **lim ρ_N = 1/2.** ∎

**Numbers** (`code/asym/bounds.py`, check X3):

| N | \|L_N\| | lower bound (new) | previous lower | best upper | ρ_N ∈ |
|---|---|---|---|---|---|
| 2 | 15 | 2 | 3 (exact) | 3 | 0.2 |
| 3 | 315 | **63 (tight!)** | 63 | 63 | 0.2 |
| 4 | 5355 | **1451** | 1080 | 1575 | [0.2710, 0.2941] |
| 5 | 86955 | **28786** | 17538 | 31479 | [0.3310, 0.3620] |
| 6 | 1396395 | 527621 | — | 553140 | [0.3778, 0.3961] |
| 7 | 22362795 | 9227609 | — | 9641268 | [0.4126, 0.4311] |
| 8 | 357886635 | 156705492 | — | 162635700 | [0.4379, 0.4544] |

Upper bounds: N = 4, 5 from the tabu witnesses (GEO-5); N ≥ 6 from ASY-6 products.

---

## ASY-4. Equality cases: Hoggar lines and a real flat state — `W5_eq_hoggar`, `Qplus7_eq_315`

**Theorem (a). deg W(5,2) = 63 follows in one line from ASY-3.**

- For N = 3 the bound evaluates to exactly 157.5 − 94.5 = 63.
- So every optimal assignment attains equality. Its spectrum is {21¹, (−3)⁷}, and M_g = 24|ψ⟩⟨ψ| − 3I.
- Reading off coefficients, g(a) = d^{−1} tr(M_g P_a) = 3⟨ψ|P_a|ψ⟩. So |⟨ψ|P_a|ψ⟩|² = 1/9 = 1/(d+1) for all 63
  non-identity Paulis.
- That is, ψ is a fiducial of a **SIC-POVM covariant under the 3-qubit Pauli group (the Hoggar lines)**.
- Conversely, every such fiducial ψ gives g = 3⟨P_a⟩_ψ ∈ {±1} (the expectations are real and ±1/3), and g is optimal.

**Corollary.** The bijections are:

- {optimal assignments of W(5,2)} ↔ {Pauli-covariant SIC fiducial projectors in ℂ⁸};
- {optimal violated sets} ↔ {conjugate pairs {SIC, SIC*}}. **Correction (round 3, TIGHT-2):** the gauge kernel has
  dimension 7 (linear *and* quadratic forms; the quadratic gauge is complex conjugation). So there are 15360 optimal
  assignments = 15360 fiducial projectors, and the 120 violated sets ↔ 120 conjugate pairs among the 240 Pauli-covariant SICs.

Gauge ↔ Pauli conjugation. Two optimal assignments have the same violated set iff they differ by a character
(−1)^{ω(·,b)}, and P_b ψ realises exactly this.

**Computed** (checks X4 and X5; `code/asym/w5_orbit.py`, `w5_sics.py`):

- the witness spectrum is {21, −3⁷};
- the top eigenvector has |⟨P⟩|² = 1/9 on all 63 non-identity Paulis;
- the Sp(6,2)-orbit of the optimal violated set has size **120**, with stabiliser of order **12096** (= |G₂(2)|);
- 944 random-restart SIC searches found exactly these 120 SICs.

This extends TQ-3 (rigidity) and fits Godsil–Roy: Pauli-covariant SICs exist only for N = 1 and N = 3. So equality in
ASY-3 is impossible for N ≠ 1, 3.

**Theorem (b). deg Q⁺(7,2) = 315** (new proof; previously only bounds were recorded in this project).

- Q⁺(7,2) is realised as the 135 symmetric non-identity 4-qubit Paulis (y even), with 1575 lines.
- ASY-2 gives exactly ≥ 315: Λ = 45, F = 2160, μ = 3.
- The tabu witness `certificates/witness_Qp7_2.txt` violates 315 lines.
- The equality structure: spectrum {45¹, (−3)¹⁵}, and M = 48|ψ⟩⟨ψ| − 3I with ψ a **real** 4-qubit state satisfying
  |⟨P⟩| = 1/3 on all 135 symmetric Paulis and ⟨P⟩ = 0 on all 120 antisymmetric ones (check X6).
- Hence ρ(Q⁺(7,2)) = 1/5 exactly.

**Lean.** (a) is ASY-2 instantiated, plus the TQ-1 witness. (b) is ASY-2 plus a `native_decide` count of the witness.
The SIC correspondence is a remark (not needed for the bounds).

---

## ASY-5. Random magic states: the rate is exactly 2^{−N/2} — `haar_upper`

**Theorem.** For every N ≥ 2,

  δ_N ≥ φ(c_N)·√(d(4^N−1))/(4^N−4),   φ(c) = c³ − (1−c²)^{3/2},   c_N² = (4^N−1) w_m²/d,

where m = d/2 and w_m = C(2m,m)/4^m. For N ≥ 6 this gives **δ_N ≥ 0.2679·2^{−N/2}**, and δ_N·2^{N/2} ≥ 0.2888 in
the limit.

**Proof steps.**

1. **Haar expectation.** For ψ Haar-random in ℂ^d and any fixed non-identity Pauli P (eigenvalues ±1, each of
   multiplicity m), ⟨ψ|P|ψ⟩ ~ 2B − 1 with B ~ Beta(m, m).
   - Reason: the squared moduli of the coordinates are uniform on the simplex, i.e. Dirichlet(1,…,1).
   - E|2B − 1| = (Γ(2m)/Γ(m)²)·4^{1−m}/(2m) = C(2m,m)/4^m = w_m.
   - Substitute t = 2x − 1, so x(1−x) = (1−t²)/4, and use ∫₀¹ t(1−t²)^{m−1} dt = 1/(2m).
2. By linearity, E Σ_{a≠0} |⟨P_a⟩| = (4^N−1) w_m. Fix ψ with Σ_{a≠0} |⟨P_a⟩| ≥ (4^N−1) w_m =: λ.
3. Put g(a) = sign⟨ψ|P_a|ψ⟩ (choose +1 at zeros). Then λ_1 := λ_max(M_g) ≥ ⟨ψ|M_g|ψ⟩ = Σ|⟨P_a⟩| ≥ λ.
4. tr M³ ≥ λ_1³ − Σ_{i≥2} |λ_i|³ ≥ λ_1³ − (F − λ_1²)^{3/2}, using Σ|λ_i|³ ≤ (Σλ_i²)^{3/2}.
   - The right side is increasing in λ_1 on [0, √F], so it is ≥ F^{3/2} φ(c) with c = λ/√F.
5. ASY-1: δ_N ≥ tr M³/(12d|L_N|) ≥ φ(c)·√(d(4^N−1))/(4^N−4) ≥ φ(c)·√(1−4^{−N})·2^{−N/2}.
6. **Constants.**
   - Wallis gives w_m ≥ 1/√(π(m + 1/2)), so c_N² ≥ 2(d−1)/(πd). This is increasing in N.
   - At N = 6: c ≥ 0.7916 and φ ≥ 0.2680. Limit: c → √(2/π), φ → (2/π)^{3/2} − (1 − 2/π)^{3/2} = 0.28890.
   - Hence δ_N ≥ 0.2679·2^{−N/2} for N ≥ 6. ∎

**Corollary (Target B, sharp form).**

- **0.2679·2^{−N/2} ≤ 1/2 − ρ_N ≤ 2^{−N/2}** for N ≥ 6.
- So lim inf ρ_N = lim sup ρ_N = 1/2, and lim (1/2 − ρ_N)^{1/N} = 2^{−1/2}.
- In terms of size: 1/2 − ρ_N = Θ(|L_N|^{−1/8}) = Θ(|P_N|^{−1/4}).

**Checks.** X7: exact Beta formula, Wallis bounds, and the constants for N = 2..80 (`code/asym/haar_constants.py`).

**Lean.** This is the only analytic (measure-theoretic) step. Options:

- (i) Formalise the Dirichlet/Beta computation in Mathlib's measure theory. This is heavy.
- (ii) **Avoid it.** Target C and "infinitely many jumps" need only ASY-3 plus ASY-6 (below), which are finite or
  algebraic. ASY-5 is needed only for the exact rate and the window-4 statement. For fixed N, explicit witnesses
  replace it.

---

## ASY-5′. Exact line correlation of the "measure-and-assign" strategy — `haar_line_corr` (round 2b)

This sharpens ASY-5 from φ = 0.2889 to the constant (2/π)^{3/2} = 0.5079. It also gives a universal bound for every
N-qubit configuration directly, without transfer.

**Strategy.** Draw ψ Haar-random and assign g(a) = sign⟨ψ|P_a|ψ⟩ ("measure the state, assign the sign of the
expectation").

**Theorem.** For every line ℓ = {a, b, c} of W(2N−1,2), N ≥ 2:

  E_ψ[χ(ℓ) g(a) g(b) g(c)] = κ(k),   k = 2^{N−2},

where κ(k) := E[sgn(S₁ − S₂)·sgn(S₁R₁ − S₂R₂)]. Here S_i ~ Gamma(2k), R_i = |2B_i − 1| with B_i ~ Beta(k,k), all
independent. Equivalently, κ(k) is Kendall's τ of the pair (|X−Y|, X+Y) for X, Y iid Gamma(k).

**Consequences.**

- **(i) Universal bound.** For *every* configuration C of N-qubit Paulis with 3-element contexts:
    deg C ≤ (1 − κ(2^{N−2}))·|L(C)|/2.
  - Signs may be arbitrary realisable signs; any subset of the lines of W(2N−1,2) is allowed.
- **(ii)** δ_N ≥ κ(2^{N−2})/2 for every N.
- **(iii)** κ(k) > 0 for all k ≥ 1, and **κ(k)√k → (2/π)^{3/2}**. Hence **lim inf δ_N 2^{N/2} ≥ (2/π)^{3/2} ≈ 0.5079**,
  which improves ASY-5's 0.2889. Together with ASY-3: 0.5079 ≤ lim inf ≤ lim sup δ_N 2^{N/2} ≤ 1.
- **(iv)** Since (2/π)^{3/2} > 1/2, the next step gives ρ_{N+2} > ρ_N for all sufficiently large N. The proof does
  not say how large, because it uses only the limit (no rate).

**Proof steps.**

1. **Joint eigenspaces.** P_a and P_b commute and are independent, so they have 4 joint eigenspaces E_{st}
   (s, t = ±), each of dimension k = d/4. Moreover P_c = χ P_a P_b acts on E_{st} as χ·st.
2. **Dirichlet weights.** For Haar ψ, the weights w_{st} = ‖Π_{st}ψ‖² are Dirichlet(k,k,k,k) (block sums of the
   Dirichlet(1,…,1) squared moduli). Then:
   - e_a = w₊₊ + w₊₋ − w₋₊ − w₋₋,
   - e_b = w₊₊ − w₊₋ + w₋₊ − w₋₋,
   - e_c = χ(w₊₊ − w₊₋ − w₋₊ + w₋₋).
   So χ·sgn(e_a)sgn(e_b)sgn(e_c) = sgn(A)sgn(B)sgn(C), with A, B, C the three "pairings" of the w's. χ drops out
   because χ² = 1.
3. **Remove the normalisation.** Signs are invariant under normalisation, so replace w by iid G_i ~ Gamma(k).
   - Put p = G₁ − G₄ and q = G₂ − G₃. Then A = p + q and B = p − q, so sgn(A)sgn(B) = sgn(|p| − |q|).
   - Also C = (G₁ + G₄) − (G₂ + G₃).
   - Hence E = E[sgn(D₁ − D₂) sgn(S₁ − S₂)] with (D, S) = (|X−Y|, X+Y), i.e. Kendall's τ.
4. **Lukacs.** X + Y ~ Gamma(2k) is independent of X/(X+Y) ~ Beta(k,k). So D = S·R, with R independent of S.
5. **Positivity formula.** Let Δ_S = log(S₁/S₂) and Δ_R = log(R₂/R₁). Both are symmetric and independent. Then
     κ = 2·E[F_k(|Δ_S|)],   F_k(x) = P(0 < Δ_R ≤ x).
   - Derivation: discordant ⇔ 0 < Δ_S < Δ_R or Δ_R < Δ_S < 0; then use the symmetry of Δ_R.
   - Hence κ(k) > 0.
6. **Limit.**
   - √k·Δ_S → N(0,1), so E√k|Δ_S| → √(2/π), and the family is uniformly integrable (variance bound).
   - √(2k)R → |Z| with locally uniform convergence of densities (Beta local limit), so Δ_R has density
     h_k → h_∞(y) = 1/(π cosh y), uniformly near 0, with sup_k ‖h_k‖_∞ < ∞.
   - So √k·F_k(u/√k) → u/π locally uniformly, with domination F_k(x) ≤ C x.
   - Therefore √k·κ(k) → 2·(1/π)·√(2/π) = (2/π)^{3/2}. ∎
7. For (i): the expected number of violated contexts is |L(C)|(1 − κ)/2, so some ψ does at least this well.

**Exact values (dyadic rationals).** Computed with mpmath (45 digits) and identified as exact dyadic rationals:

- κ(1) = 1/2,
- κ(2) = 23/64,
- κ(4) = 133519/2¹⁹,
- κ(8) = 50649838284767/2⁴⁸.

Float64 quadrature for N ≤ 19 gives κ(k)√k = 0.50823 (N=3), 0.50933, 0.50896, …, 0.5079491. That is: monotone
decreasing from N = 4, always above (2/π)^{3/2} = 0.5079490, with excess ≈ c/k. Monte Carlo on actual Pauli lines
(N = 2..5) agrees to 3 decimals (check X11).

| N | κ(2^{N−2}) | universal bound ρ ≤ (1−κ)/2 | compare: best upper bound on ρ_N |
|---|---|---|---|
| 2 | 1/2 | 0.25 | 0.2 |
| 3 | 23/64 | 0.3203 | 0.2 |
| 4 | 0.254667 | 0.3727 | 0.2941 |
| 5 | 0.179944 | 0.4100 | 0.3620 |
| 8 | 0.063514 | 0.4682 | 0.4544 |
| ≥ 21 | ≈ 0.508·2^{−N/2+1} | ≈ 1/2 − 0.508·2^{−N/2} | products are worse from about N = 20 |

**CONJ-4.** κ(k)√k ≥ (2/π)^{3/2} for all k ≥ 2 (equivalently, the excess is positive and decreasing from k = 4).

- This would give δ_N ≥ (2/π)^{3/2} 2^{−N/2} for all N ≥ 3.
- Since (2/π)^{3/2} > 1/2, it would also give ρ_{N+2} > ρ_N for all N ≥ 3.
- Verified numerically for N ≤ 19.
- A rigorous route: an explicit Edgeworth/Berry–Esseen remainder in step 6, or a closed formula for the dyadic
  rationals κ(k).

Scripts: `code/asym/kendall.py` (mpmath), `kendall_exact.py` (dyadic identification), `kendall_fast.py` (N ≤ 19),
`kendall_mc.py` (Monte Carlo on Pauli lines).

---

## ASY-6. Tensor products, a closed formula for negative lines, explicit upper bounds — `tau_mul`

**Lemma (multiplicativity).**

- P_{(a₁,a₂)} = P_{a₁} ⊗ P_{a₂} (the canonical phase i^{x·z} factorises).
- Hence m_{h₁⊗h₂} = m_{h₁} ⊗ m_{h₂} and **τ(h₁⊗h₂) = τ(h₁)τ(h₂)**.
- So τ_N := max_h τ(h) is supermultiplicative.

**Corollary 1 (number of negative lines).**

- h ≡ 1 on one qubit gives m = I + X + Y + Z with eigenvalues 1 ± √3, so τ = 20/2 = 10. Then τ(1^{⊗N}) = 10^N.
- The all-(+1) assignment violates exactly the negative lines. Therefore

    #{ℓ ∈ W(2N−1,2) : χ(ℓ) = −1} = (16^N + 4^N − 2·10^N)/24.

- Values for N = 2, 3, … : 3, 90, 1908, … Verified by direct count for N ≤ 7 (check X8).
- In particular ρ_N ≤ 1/2 − (10^N − 3·4^N + 2)/(12|L_N|) < 1/2 for every N ≥ 2. This is the elementary,
  measure-free strictness used in ASY-7.

**Corollary 2 (explicit upper bounds).** Certified block values:

- τ₁ = 10 (single qubit);
- τ₃ = 1324 (the Hoggar pattern, from witness_W5_2);
- τ₄ = 13996 (witness_W7_2, 1575);
- τ₅ = 147052 (witness_W9_2, 31479).

Products give deg W(2N−1,2) ≤ |L_N|/2 − (Π τ − 3·4^N + 2)/12. Best partitions:

- N = 6: 3+3, giving 553140;
- N = 7: 3+4, giving 9641268;
- N = 8: 4+4, giving 162635700;
- N = 9: 3+3+3, giving 2669910768.

These products are counted line by line for N ≤ 7 (check X8, `code/asym/best_products.py --count`, `product_witness.py`).

**Remark.** The products give δ_N ≈ (τ₃^{1/3}/16)^N = (10.98/16)^N. This is weaker than ASY-5's (11.31/16)^N
asymptotically, but better for N ≤ ~25.

---

## ASY-7. Monotonicity and strict jumps (Target A) — `rho_mono`, `rho_strict_infinitely_often`

**Theorem.**

- (i) ρ_{N+1} ≥ ρ_N for all N (TR-5 transfer; W(2N−1,2) is a nondegenerate section of W(2N+1,2) and Sp is
  line-transitive). Group-free: uniform cover by all nondegenerate codimension-2 sections, using ALG-3.
- (ii) **ρ_N is not eventually constant.** It has infinitely many strict jumps.
- (iii) **Quantitative window.** For every N ≥ 6, ρ_{N+4} > ρ_N.
- (iv) **Strict chain.** ρ₂ = ρ₃ = 1/5 < ρ₄ < ρ₅ < … < ρ₁₁ (check X9).

**Proof steps.**

- (ii) ρ_N < 1/2 for each N (ASY-6, Corollary 1), and ρ_N → 1/2 (ASY-3). A non-decreasing sequence that is eventually
  constant at a value c < 1/2 cannot tend to 1/2.
  - **This proof is fully finite/algebraic: ASY-1, ASY-2, ASY-6 and TR-5.**
- (iii) ρ_N ≤ 1/2 − 0.2679·2^{−N/2} (ASY-5) < 1/2 − 2^{−(N+4)/2} ≤ ρ_{N+4} (ASY-3), since 2^{−2} = 0.25 < 0.2679.
- (iv) For N = 3..10: (best upper bound on ρ_N) < (ASY-3 lower bound on ρ_{N+1}), with exact arithmetic
  (`code/asym/chain.py`).

**The improving construction asked for in A** is the pair transfer + tensor product:

- Transfer: if a configuration S on N qubits has ratio r, then ρ_M ≥ r for all M ≥ N (S ⊆ W(2N−1,2) ⊆ W(2M−1,2)).
- Tensor product: a pattern with deficit-weight τ on k qubits yields τ^j on jk qubits.

**Open.** Is ρ_N strictly increasing for all N ≥ 3? Proven for 3 ≤ N ≤ 11. It would follow if
κ_N := δ_N 2^{N/2} satisfies κ_{N+1} < √2 κ_N.

---

## ASY-8. Universal statements — `universal_upper`

1. **Every N-qubit KS configuration S** (any set of lines of W(2N−1,2), not necessarily induced) satisfies
   deg S ≤ ρ_N |L(S)| (TR-5).
   - For N ≥ 6 this is ≤ (1/2 − 0.2679·2^{−N/2})|L(S)|.
   - So some noncontextual assignment satisfies at least a (1/2 + 0.2679·2^{−N/2}) fraction of the contexts of *any*
     N-qubit configuration.
   - For N ≤ 11, use the table bounds instead.
2. **Density criterion for induced configurations (ASY-2).** 1/2 − ρ(X) ≤ |X|^{3/2}(2^N−1)^{1/2}/(12|L_X|).
   - So any family of induced configurations with |L_X| ≫ |X|^{3/2}2^{N/2} has ratio → 1/2.
   - Contrapositive: an induced configuration with ratio ≤ 1/2 − ε must be *sparse*: |L_X| ≤ |X|^{3/2}2^{N/2}/(12ε).

---

## ASY-9. Quadric families

ASY-2 with X = Q^±(2N−1,2) (`code/asym/quadric_bounds.py`):

| geometry | points | lines | spectral lower | previous lower | upper |
|---|---|---|---|---|---|
| Q⁺(7,2) | 135 | 1575 | **315 (tight)** | — | 315 |
| Q⁻(7,2) | 119 | 1071 | 145 | **216** (GEO-2) | 315 |
| Q⁺(9,2) | 527 | 23715 | **6426** | 4783 | 6975 |
| Q⁻(9,2) | 495 | 19635 | **4873** | 3960 | 7087 |
| Q⁺(11,2) | 2079 | 365211 | 120901 | — | — |
| Q⁻(11,2) | 2015 | 332475 | 107360 | — | — |

- (1/2 − ρ)·2^{N/2} → √2 for the bound.
- **So ρ(Q^±(2N−1,2)) → 1/2** as well, with 1/2 − ρ = O(2^{−N/2}).
- Note: Q⁻(7,2) remains the one place where the combinatorial certificate (216) beats the spectral bound (145).
- A matching *upper* rate for quadrics is not proved: the Haar argument gives c² → 1/π < 1/2, so φ < 0. This is open.

---

## Conjectures and open problems (new)

- **CONJ-3 (magic conjecture).** Optimal assignments of W(2N−1,2) are sign patterns g = sign⟨ψ|P_a|ψ⟩ of states ψ that
  maximise the Pauli L1-norm Σ_a |⟨P_a⟩_ψ| (maximal "stabilizer-1/2-Rényi magic").
  - Evidence: the alternating ascent ψ ↦ g = sign⟨P⟩ ↦ top eigenvector reproduces the best known values exactly for
    N = 2, 3, 4, 5 (3, 63, 1575, 31479), with λ_max = 3 + 2√3, 21, 21 + 16√6 and 168.90 respectively.
  - It is proved for N = 3 (ASY-4: Hoggar).
  - For N ≥ 6 the plain ascent is worse than products, so either the conjecture fails or the search is weak.
  - Quadrics (restricted ascent, `code/asym/l1sub.py`): Q⁺(5,2) → 21, Q⁺(7,2) → 315, Q⁺(9,2) → 6975, Q⁻(5,2) → 9,
    Q⁻(7,2) → 315. These all equal the best known values. Q⁻(9,2) → 7176, worse than the known 7087.
  - For Q⁺(9,2), 300 real restarts reach λ_max = 124.196 < cap 127.816. So no real flat state was found, and the
    spectral bound 6426 is probably not tight.
- **Conditional bounds (reduction to a 16-dimensional continuous problem).** If the numerically observed maxima of
  the Pauli L1 norm are the true maxima, then ASY-2 with Λ replaced by them gives:
  - W(7,2) ≥ 1488 (Λ = 21 + 16√6);
  - Q⁻(7,2) ≥ 298 (Λ = 28.1833, the restricted maximum over Q⁻).

  Proving such a Λ bound rigorously would be a new route to CONJ-1. Note that a weighted version (weights constant on
  Q⁻ and on its complement) gives no gain over uniform weights (`weighted_lp.py`).
- **Constant.** Does κ = lim δ_N 2^{N/2} exist? Known: κ ∈ [0.5079, 1] in lim inf / lim sup form (ASY-5′; the
  earlier heuristic is now a theorem).
  - Numerics from witnesses: κ₄ ≥ 0.82, κ₅ ≥ 0.78, κ₆ ≥ 0.83, κ₇ ≥ 0.78, κ₈ ≥ 0.73.
  - κ = 1 would require asymptotically Pauli-flat states (near-SICs for the Pauli group).
- **deg W(7,2) ∈ [1451, 1575].** CONJ-1 predicts 1575 via the Q⁻(7,2) transfer. The 1575 witness has spectrum
  {21 ± 16√6, (−3)¹⁴}: M + 3I has rank 2. A rank-2 analogue of ASY-4 might give a proof.
