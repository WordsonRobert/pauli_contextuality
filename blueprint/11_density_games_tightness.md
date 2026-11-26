# 11. Round 3: density, nonlocal games, spectral tightness, operational meaning

This round responds to the referee-style roadmap (density dichotomy, sharp rate, Q⁻(7,2), operational hook). Every
item is labelled by what it actually is:

- **P**: proof written here.
- **P+C**: proof plus a finite check (`certificates/certify_asym.py`, X12–X17).
- **E**: numerical evidence only.
- **Open**: not settled.

Correction relative to the roadmap text: **the rate is already pinned.** 1/2 − ρ_N = Θ(2^{−N/2}) (ASY-3 + ASY-5/5′).
The "(5/8)^N" upper side in the roadmap came from the all-plus assignment and is superseded. The remaining open
question is the **constant**: (2/π)^{3/2} ≈ 0.508 ≤ lim inf (1/2−ρ_N)2^{N/2} ≤ lim sup ≤ 1.

---

## DEN — the density theorem and the hardness/density boundary

### DEN-1 (explicit spectral density bound) — P

For every set X of n non-identity N-qubit Pauli labels, with L_X the set of all commuting triples {a, b, a+b} ⊆ X:

  deg X ≥ |L_X|/2 − n^{3/2}(2^N − 2) / (12 √(2^N − 1)) ≥ |L_X|/2 − n^{3/2} 2^{N/2} / 12.

**Steps.**

1. ASY-2 with F = dn and Λ = √(n(d−1)).
2. ΛF − F²/(dΛ) = dn(Λ² − n)/Λ = dn·n(d−2)/√(n(d−1)) = d·n^{3/2}(d−2)/√(d−1).
3. Divide by 12d. The second inequality uses (d−2)/√(d−1) ≤ √d.

**Lean:** a one-line corollary of `spectral_lower` (`SpectralConfig.lean`); pure real arithmetic.

**Constant.** The constant is **1/12**, not 1/6 as in the roadmap.

### DEN-1′ (intrinsic qubit number) — P

Let U = span X, u = dim U, and r = dim(U ∩ U^⊥). Then U embeds isometrically into a symplectic space of dimension
u + r, and no smaller one. So X is realised on **N_X = (u + r)/2 qubits**, and DEN-1 holds with N replaced by N_X.

**Steps.**

1. Write U = R ⊕ U₀ with U₀ non-degenerate. Map a symplectic basis of U₀ to standard pairs. Map R into the isotropic
   span of fresh Z's, with fresh X partners outside the image.
2. The map is linear and preserves ω, so it maps commuting triples to commuting triples (a+b = c is linear). It
   therefore induces a bijection of the induced line sets.
3. ALG-3 then gives equal degrees. The signs may change, but cycle parities are invariant by ALG-2.

**Definition.** The *spectral density* of X is D(X) := |L_X| / (n^{3/2} 2^{N_X/2}). DEN-1 says

  **1/2 − deg X/|L_X| ≤ 1/(12 D(X)).**

### DEN-2 (the dense regime is trivially approximable) — P

If D(X) ≥ 1/(12ε), then (1/2 − ε)|L_X| ≤ deg X ≤ |L_X|/2.

- The method of conditional expectations (fix points one at a time, keeping the conditional expectation of the
  violated count ≤ |L|/2) outputs, in time O(n·|L_X|), an assignment with ≤ |L_X|/2 violations.
- That assignment is a 1/(1−2ε)-approximation. Approximating deg X within any factor > 1 is therefore easy on
  families with D(X) → ∞.

### DEN-3 (the hard instances are exponentially sparse) — P (sizes) / Lean: counting lemma TBD

For the induced construction Φ_ind(S) of an E3-LIN instance S with k variables and m equations (blueprint 02):

- n = O(k + m) = poly(k) points, and trivially |L| ≤ n²/6;
- the 4 copies of each variable live in their own 3-qubit block with λ ∈ {100, 010, 001, 111}, so they span 3
  dimensions per variable. The span U contains 3k independent Z-type (isotropic) vectors, so u ≥ 3k and
  N_X = (u+r)/2 ≥ 3k/2.

Hence D(Φ_ind(S)) ≤ n^{1/2}·2^{−3k/4} = 2^{−Ω(k)}. Since m ≤ k³, this is 2^{−Ω(n^{1/3})} in general, and 2^{−Ω(n)}
for bounded-occurrence E3-LIN, where Håstad's 2 − δ hardness still holds with occurrence bound B(δ). The same holds
for Φ_sub.

**Statement (honest dichotomy).**

- **(a)** On every family with D(X) → ∞, deg X/|L_X| → 1/2. The trivial value |L_X|/2 (and the conditional-
  expectation assignment) approximates deg within 1 + o(1).
- **(b)** For every δ > 0 it is NP-hard to approximate deg within 2 − δ on induced Pauli configurations with
  D(X) ≤ 2^{−Ω(n)} (bounded occurrence; HARD-9/10). This needs the Pauli realisation HARD-5/6, which is on paper and not yet in Lean.
- **(c) Open (the middle regime).** Is approximating deg within 1 + c hard for some family with D(X) = Ω(1/poly(n))?
  Cones keep D roughly constant: the lifts give 4^t|L|, while n and 2^{N/2} grow by 2^t·2^{t/2} each in the
  n^{3/2}2^{N/2} term. So cones cannot push hard instances into the dense regime. A different padding is needed.

**What not to claim.** The results do *not* say "hard exactly when sparse". They say: *hard instances exist only
below* the density scale, and *everything above* it is easy.

---

## TIGHT — when the spectral bound is exact: Pauli-flat states

### TIGHT-1 (characterisation) — P

For X ⊆ V*(N) with n points, the following are equivalent:

- (i) deg X equals the ASY-2 bound |L_X|/2 − n^{3/2}(d−2)/(12√(d−1));
- (ii) there is a pure state ψ with |⟨ψ|P_a|ψ⟩| = γ := √((d−1)/n) for all a ∈ X, and ⟨ψ|P_a|ψ⟩ = 0 for all
  a ∉ X ∪ {0}.

Moreover, the optimal assignments are exactly g = sign⟨P_a⟩_ψ (equivalently g = γ^{−1}⟨P_a⟩_ψ) over all such ψ.

**Steps.**

- **(ii) ⇒ (i).**
  1. dρ = I + Σ_{a∈X} e_a P_a, so M_g = Σ_X (e_a/γ)P_a = (d|ψ⟩⟨ψ| − I)/γ.
  2. The spectrum is {(d−1)/γ¹, (−1/γ)^{d−1}}, so tr M³ = (d−1)d(d−2)/γ³.
  3. Substitute γ² = (d−1)/n into ASY-1: viol(g) equals the bound, and the bound is ≤ deg ≤ viol(g).
- **(i) ⇒ (ii).**
  1. An optimal g attains equality in ASY-2. Equality in (Λ−λ)(λ+μ)² ≥ 0 forces the spectrum {Λ, −μ}. Trace and
     Frobenius constraints force multiplicities (1, d−1), as in blueprint 10 ASY-2.
  2. So M_g = (Λ+μ)|ψ⟩⟨ψ| − μI.
  3. Taking Pauli coefficients: g_a = (Λ+μ)e_a/d for a ∈ X, and 0 = (Λ+μ)e_a/d for a ∉ X ∪ {0}.
  4. Since g_a = ±1, |e_a| is constant on X. Pauli completeness then gives the value γ.

**Integrality corollary.** Tightness forces the bound to be an integer. In particular n(d−1)/m² must be compatible
with (d−2)n^{3/2}/(12√(d−1)) ∈ ½ℤ. For example, with d − 1 prime (d = 8, 32, 128, …), n must be (d−1)·k².

**Examples (all certified, check X12–X14).**

| X | N | n | \|L_X\| | deg (exact) | flat state |
|---|---|---|---|---|---|
| stabiliser group minus I | any | 2^N − 1 | (d−1)(d−2)/6 | 0 | stabiliser state |
| **W(5,2)** (all of V*) | 3 | 63 | 315 | **63** | Hoggar SIC fiducials, γ = 1/3 |
| **Q⁺(7,2)** (symmetric Paulis) | 4 | 135 | 1575 | **315** | **ψ ∝ \|+⟩^{⊗4} − \|0⟩^{⊗4}** (real), γ = 1/3 |
| **X₄₉₆** (new) | 5 | 496 | 10880 | **480** | a 5-qubit state with γ = 1/4 (numerical, `certificates/flat5_496.json`) |

Notes on the examples:

- The closed form for the Q⁺(7,2) state is new here. Cieśliński (2026) found the same support numerically, as the
  vector (−3, 1, …, 1)/√24. The optimal Q⁺(7,2) assignment is thus the sign pattern of a superposition of two
  stabiliser states.
- X₄₉₆ is a new exactly-solved 5-qubit configuration. The bound is exactly rational: 496^{3/2}·30/(12√31) = 4960, so
  deg = 5440 − 4960 = 480. The witness g = sign⟨P⟩ is counted directly.
  - Its points lie on 60, 64 or 68 lines, so it is not a homogeneous geometry. The state is one numerical solution;
    nicer members of its family may exist.

**Corollary (W is never tight beyond 3 qubits).** W(2N−1,2) is spectrally tight iff a pure state is Pauli-flat on
all 4^N − 1 Paulis, i.e. a Pauli-covariant SIC fiducial. These exist only for N = 1 and 3 (Godsil–Roy 2009; see
also Cieśliński 2026). Hence for N ≥ 4, deg W(2N−1,2) > ASY-3 bound (strictly, as reals).

### TIGHT-2 (W(5,2): the exact count) — P+C (corrects blueprint 10, ASY-4)

- The F₂-kernel of the W(5,2) incidence matrix has **dimension 7**, not 6. It consists of the 64 linear functionals
  and the 64 quadratic forms with polarisation ω. A quadratic q satisfies q(a) + q(b) + q(a+b) = ω(a,b) = 0 on every
  line.
- So each optimal violated set has 128 optimal assignments, giving **120 × 128 = 15360 optimal assignments**. This
  equals the number of Pauli-covariant SIC fiducial projectors in ℂ⁸: 240 SICs × 64, matching the 15,360 maximal-magic
  three-qubit states of the lattice classification (arXiv:2506.11725).
- The quadratic gauge q(a) = y(a) mod 2 is exactly complex conjugation, since ⟨P_a⟩_{ψ̄} = (−1)^{y(a)}⟨P_a⟩_ψ. So:
  - the 120 optimal violated sets ↔ the 120 conjugate pairs {SIC, SIC*} among the 240 Pauli-covariant SICs;
  - optimal assignments ↔ SIC fiducial projectors, bijectively.

---

## NEG — limits of the single-moment spectral method (why Q⁻(7,2) is special)

### NEG-1 (ceiling of ASY-2) — P+C

ASY-2 with any valid Λ (i.e. Λ ≥ λ_max(M_g) for all g) is at most

  |L|/2 − B(Λ*)/(12d),   B(Λ) = ΛF − F²/(dΛ) (increasing),   Λ* := max_g λ_max(M_g) = max_ψ Σ_{a∈X} |⟨P_a⟩_ψ|.

An explicit g with large λ_max(M_g) therefore *caps* what the method can ever prove:

| X | Cauchy–Schwarz cap → bound | explicit Λ* ≥ | ceiling of ASY-2 | conjectured deg |
|---|---|---|---|---|
| Q⁻(7,2) | 42.25 → 145 | 28.18 | **≤ 297** | 315 |
| W(7,2) | 61.85 → 1451 | 21 + 16√6 = 60.19 | **≤ 1488** | 1575 |
| Q⁺(9,2) | 127.8 → 6426 | 124.20 | ≤ 6589 | 6975 |
| W(9,2) | 178.1 → 28786 | 168.90 | ≤ 29594 | 31479 |

**Interpretation.** On Q⁻(7,2) the best state reaches only 0.667 of the Cauchy–Schwarz cap, against 0.973 on W(7,2)
and 1.000 on Q⁺(7,2). Elliptic quadrics admit no near-flat states, and the spectral method cannot see the
obstruction that the 216 cascade certificate exploits.

**Weighted variants (E).** Two-class weights (Q⁻ ∩ a^⊥ versus the rest), and Q⁻ versus its complement in W(7,2),
combined by LP with the combinatorial bounds, give **no gain**: 215 and 1451 (`code/asym/weighted_qm7.py`,
`weighted_lp.py`). Cauchy–Schwarz-weighted bounds are dominated by the uniform ones.

**Open (the real target).** Prove a non-trivial *upper* bound on Λ* (the maximal Pauli L1 norm restricted to X). For
example, Λ*(Q⁻(7,2)) ≤ 28.19 would give deg Q⁻(7,2) ≥ 298, beating 216. This is a 16-dimensional continuous
optimisation problem (a polynomial optimisation over the sphere) and is amenable to SOS/moment certificates.
Reaching 315 needs more than one eigenvalue: the conjectured optimum has M + 3I of rank 2.

---

## GAME — linear-system nonlocal games (the device-independent hook)

### GAME-1 (exact classical value) — P+C

Take any configuration C of N-qubit Paulis with 3-element contexts. Its linear-system game (Cleve–Mittal) works as
follows:

- the referee sends Alice a uniformly random line ℓ, and Bob a uniformly random point p ∈ ℓ;
- Alice answers 3 bits satisfying x_a + x_b + x_c = e(ℓ); Bob answers 1 bit;
- they win iff Bob's bit equals Alice's bit for p.

Then:

- ω_q(G_C) = 1 with N EPR pairs: Alice measures the commuting P_a, P_b, P_c; Bob measures P_p^T.
- **ω_c(G_C) = 1 − deg C / (3|L(C)|).**

**Steps (classical value).**

1. Shared randomness does not help (convexity), so fix Bob's assignment x.
2. On a line satisfied by x, Alice answers x|ℓ and wins with probability 1.
3. On a violated line, every satisfying triple differs from x|ℓ in an odd number of places, hence ≥ 1. Alice
   answers one at distance 1 and wins with probability 2/3.
4. So the value is 1 − viol(x)/(3|L|), and the best x gives 1 − deg/(3|L|).

(Check X15 verifies this on the doily and the Peres–Mermin square by brute force over Alice's and Bob's strategies.)

### GAME-2 (the full Pauli game is asymptotically optimal) — P

- **Universal bound.** Every 3-variable linear-system game has ω_c ≥ 5/6, because some assignment satisfies at least
  half of the equations. This is folklore (Håstad 2001; stated explicitly in Taller–Vidick 2025).
- **The W family.** For the game of W(2N−1,2), played with N EPR pairs and Pauli measurements:

    ω_c(G_N) = 5/6 + δ_N/3,   so   5/6 + κ(2^{N−2})/6 ≤ ω_c(G_N) ≤ 5/6 + 2^{−N/2}/3.

  So **ω_c(G_N) ↓ 5/6**, the minimum possible for any 3-variable LCS game, while ω_q = 1. The classical–quantum gap
  tends to **1/6**, the maximum possible in this game class.
- Values:
  - N = 2: 14/15;
  - N = 3: 14/15;
  - N = 4: ω_c ∈ [0.9020, 0.9097];
  - N = 5: ω_c ∈ [0.8793, 0.8897].

### GAME-3 (dimension–gap trade-off for Pauli strategies) — P

Every linear-system game whose perfect strategy uses an N-qubit Pauli operator solution with 3-term equations has

  1 − ω_c ≤ 1/6 − κ(2^{N−2})/6 ≈ 1/6 − 0.169·2^{−N/2}.

This follows from ASY-5′ (i) applied to the configuration of the game.

The W(2N−1,2) game achieves 1 − ω_c ≥ 1/6 − 2^{−N/2}/3. **The optimal gap with N EPR pairs is 1/6 − Θ(2^{−N/2}).**

### GAME-4 (noise) — P

With the shared state v|Φ⁺⟩⟨Φ⁺|^{⊗N} + (1−v)I/d², Alice's outcomes still satisfy her equation. Bob agrees with
probability (1+v)/2. So the win probability is (1+v)/2.

- **Nonlocal (device-independent) threshold:** v > 1 − 2ρ/3 → 2/3.
- **Single-system contextuality (parity) test:** score v against the noncontextual bound 1 − 2ρ. The threshold is
  v* = 1 − 2ρ_N ≤ 2^{1−N/2}, which is exponentially small. It assumes outcome noncontextuality, i.e. compatible,
  non-disturbing sequential measurements (the "compatibility loophole").

Both statements are correct, but they belong to different operational models. Keep them separate in the paper.

### OP-1 (sampling theorem: constant rounds) — P

Play T rounds, each with fresh uniformly random questions. Let W_T be the empirical win rate. Against *any*
classical strategy, even one adapting across rounds with memory, the per-round win probability given the past is
≤ ω_c. Azuma–Hoeffding then gives

  Pr[W_T ≥ ω_c + ε] ≤ exp(−2Tε²).

- For G_N with ideal devices, ε = 1/6 − 2^{−N/2}/3 − η suffices. So **T = O(log(1/δ)) rounds, independent of N
  and of the number of contexts.** Each round needs N EPR pairs and one 3-Pauli context measurement (a Clifford
  circuit).
- The same argument applies to the single-system parity test against noncontextual models *without memory*.
  Memory-assisted models are the known loophole (Kleinmann et al.).
- **Remark (fixed sub-configurations).** If instead m contexts are fixed in advance, Hoeffding plus a union bound
  over 2^n assignments gives deg(S)/m ≥ 1/2 − O(2^{−N/2}) − O(√(n/m)). That needs m ≳ n·2^N. This is the
  roadmap's concern, and it is the wrong experimental design: fresh questions each round avoid it entirely.

---

## Status of the roadmap items

| Item | Status |
|---|---|
| 1. Density dichotomy | DEN-1/1′/2/3 proved. Middle regime **open**. "Hard exactly when sparse" is *not* claimed. |
| 2. Sharp rate | **Done** (Θ(2^{−N/2})). Constant ∈ [0.508, 1]: open. N = 6, 7 heuristics: products give κ₆ ≥ 0.83, κ₇ ≥ 0.78. |
| 3. Q⁻(7,2) | Negative result NEG-1: ASY-2 can never exceed 297. Weighted variants give no gain. The path forward is an SOS bound on Λ*, or rank-2 structure. **Open.** |
| 4. Operational | GAME-1..4 and OP-1. This is the strongest new hook: optimal 3-LIN game family, constant-round test. |
| Tightness | TIGHT-1/2 (new): exact characterisation, the 15360 = SIC fiducial count, Q⁺(7,2) closed form, a new 5-qubit exact degree. |
