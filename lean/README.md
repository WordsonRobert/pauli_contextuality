# Lean 4 formalisation (Mathlib v4.31.0)

Status: **compiles, no `sorry`**. Every theorem listed below is proved. The only non-standard axiom
is the compiler trust of `native_decide` (`Lean.ofReduceBool`), used solely for finite computations
(marked ⚙ below). Everything else depends only on `propext`, `Classical.choice`, `Quot.sound`.

Toolchain: `leanprover/lean4:v4.31.0`, Mathlib tag `v4.31.0` (see `lean-toolchain`, `lakefile.lean`).

    lake exe cache get     # prebuilt Mathlib
    lake build             # builds PauliData (compiled to native code) and PauliContextuality

`PauliData/Qm7Data.lean` imports only Lean core and is built with `precompileModules := true`, so the
`native_decide` certificate (≈10⁹ elementary operations) runs natively in about a minute. In Lean's
interpreter it would take hours. `PauliData/Flat5Data.lean` (core only) holds the points of the 5-qubit
configuration X₄₉₆ and its witness assignment (`certificates/flat5_496.json`).

**Alternative check.** If a Mathlib v4.31.0 is already built in another Lake project, `scripts/check_all.sh`
compiles every module against it (about 10 minutes), compiles the data module to a shared library, loads it with
`--load-dynlib`, checks that no module contains `sorry`, and writes the axiom audit:

    MATHLIB_PROJ=/path/to/project/with/built/mathlib ./scripts/check_all.sh

## What is proved (blueprint label → Lean name)

| Blueprint | Statement | Lean | File |
|---|---|---|---|
| ALG-0 | Pauli group law: associativity, identity, inverse, central phases, commutation rule, P(p)² = 1 | `mulPG_assoc`, `mulPG_inv`, `mulPG_central`, `comm_rule`, `canon_sq` | Basic |
| 00 | line signs are in {0,2}, independent of the order | `signK_even`, `sign_symm`, `signK_eq` | Basic |
| ALG-1 | degree depends only on the sign coset (gauge invariance) | `Config.deg_gauge` | Bounds |
| ALG-1b | vectors orthogonal to all cycles lie in Im H; equal cycle parities ⇒ equal degree | `Config.mem_range_of_cycles`, `Config.deg_eq_of_cycles` | Invariance |
| ALG-2 | cycle-sign lemma Σ e(ℓ) = inversion count | `prod_canon_even`, `cycle_parity_eq_inversions` | CycleSign |
| ALG-3 | invariance of the degree under ω-preserving line bijections | `deg_invariant`, `deg_invariant_equiv` | Invariance |
| ALG-4 | noncontextual inequality β ≤ m − 2deg (attained; mixtures; attenuation) | `Config.nc_bound`, `nc_bound_attained`, `nc_bound_mixture`, `attenuation_iff` | Bounds |
| CERT-1 | odd cycle forces a violation | `Config.odd_cycle_forces_violation` | Cover |
| TR-1′ | uniform-cover lemma, degree form | `Config.uniform_cover`, `uniform_cover_deg` | Cover |
| TR-2 | rigidity in the equality case | `Config.uniform_cover_rigid` | Cover |
| TR-3 | stability identity; #non-tight members ≤ excess | `Config.uniform_cover_excess`, `card_nontight_le` | Cover, Bounds |
| CERT-2 (a,b) | fractional packings ≤ deg; ≤ r·\|L\| | `Config.packing_le_deg`, `packing_le_ratio` | Bounds |
| ASY-0 | deg ≤ \|L\|/2 | `Config.deg_le_half` | Bounds |
| GEO-1, GEO-2 ⚙ | **deg Q⁻(7,2) ≥ 216** (and ≥ 215) | `Qm7.qm7_ge_216`, `qm7_ge_215` | Qminus |
| GEO-5 ⚙ | deg Q⁻(7,2) ≤ 315 (witness `witness_Qm7_2.txt`) | `Qm7.qm7_le_315`, `qm7_bounds` | Qminus |
| (bridge) ⚙ | the same bounds for Q⁻(7,2) **defined from first principles** (all commuting triples of singular points of `qminus`) | `Qm7.Qminus7_bounds` | QminusBridge |
| ASY-1 | Pauli matrices: product law, traces, Hermitian, commutation, completeness Σ\|⟨P_a⟩\|² = 2^N‖v‖⁴ | `pauli_mul`, `trace_pauli`, `trace_pauli_mul`, `pauli_hermitian`, `pauli_comm`, `pauli_completeness` | PauliMatrix |
| ASY-1 | trace formula tr M_g³ = 2^N(6\|L\| − 12\|V(s)\|) | `Spectral.trace_cube_comm`, `trace_cube_viol` | Spectral, SpectralConfig |
| ASY-2 | Rayleigh bound ΛI − M ⪰ 0; cubic trace inequality; spectral lower bound for every induced configuration | `rayleigh`, `cubic_trace_bound`, `spectral_lower` | Spectral, SpectralConfig |
| ASY-3 | 12\|L_N\| = (4^N−1)(4^N−4); **ρ_N ≥ 1/2 − 2^{−N/2}**; ρ_N ≤ 1/2 | `lines_W`, `W_lower`, `rho_le_half` | SpectralW |
| Target C | **lim ρ_N = 1/2** | `Spectral.rho_tendsto_half` | SpectralW |
| ASY-4 / TQ-1 ⚙ | **deg W(5,2) = 63**, **deg Q⁺(7,2) = 315** | `W5_eq_63`, `Qplus7_eq_315` | SpectralExact |
| ASY-7 (ii) | a monotone sequence < 1/2 tending to 1/2 has infinitely many strict jumps | `infinitely_many_strict_jumps` | Spectral |
| CONE-1 | **deg Cone_t(G) = 4^t deg G** (abstract; and for every Pauli-realised base G) | `Config.cone_degree`, `cone_degree_pauli` | Cone |
| HARD-1 | chain lemma | `Hardness.chain_lemma`, `chain_parity` | Hardness |
| HARD-2 | ordered triangle split preserves OPT; (b) two equations share ≤ 1 variable; (c) middle variable original | `split_opt`, `split_share`, `split_middle` | Hardness |
| HARD-8 | the one-equation minimisations | `one_equation_b0`, `one_equation_ind`, `one_equation_sub` | Hardness |
| ASY-6 Cor. 1 | **#negative lines of W(2N−1,2) = (16^N + 4^N − 2·10^N)/24**; ρ_N ≤ 1/2 − (10^N − 3·4^N + 2)/(12\|L_N\|) | `neg_lines`, `rho_le_explicit` | NegLines |
| ASY-6 | **ρ_N < 1/2 for every N** | `rho_lt_half` | NegLines |
| **Target A** | **ρ_N < ρ_{N+1} for infinitely many N** (unconditional; also ρ not eventually constant) | `rho_strict_jumps`, `rho_strict_jumps'`, `rho_not_eventually_const` | NegLines, Transfer |
| TR-1 | transfer, group version: \|L(G)\|·deg S ≤ \|L(S)\|·deg G for line-transitive Γ | `Config.transfer`, `transfer_cover` | Transfer |
| TR-2 | rigidity, group version | `Config.transfer_rigid`, `rho_rigid` | Transfer |
| (TR-5 tool) | **Sp(2N,2) is transitive on the lines of W(2N−1,2)** (explicit transvections, no Witt) | `Sp_trans_lines`, `Sp_trans_pairs` | Transfer |
| TR-5.1 | every N-qubit configuration S ⊆ W(2N−1,2) has deg S/\|L(S)\| ≤ ρ_N | `rho_max` | Transfer |
| TR-5.2 | **ρ_N ≤ ρ_{N+1}** (ρ monotone) | `rho_mono_succ`, `rho_mono` | Transfer |
| TR-4 | profile bound d ≤ Σ_{m∈L} \|V ∩ orb m\|/\|orb m\| (orbit–stabiliser) | `Config.profile_bound`, `orbit_count` | Profile |
| TQ-1 ⚙ | Peres–Mermin grid is an odd cycle; **deg W(3,2) = 3** | `grid_cycle`, `grid_odd`, `W3_eq_3` | GeoBounds |
| TQ-2 ⚙ | **every configuration on ≤ 3 qubits has deg S ≤ \|L(S)\|/5** | `three_qubit_bound`, `three_qubit_bound_le` | Transfer |
| TQ-3 ⚙ | every optimal assignment of W(5,2) violates exactly 3 lines of every Sp(6,2)-translate of the doily | `doily_rigid` | ThreeQubit |
| CERT-2 (c) | uniform weights on an orbit are a packing of value \|L(C)\|·deg S/\|L(S)\| | `Config.packing_orbit` | Packing |
| CERT-3 ⚙ | three-qubit barrier: packing value ≤ \|L(C)\|/5 | `three_qubit_barrier` | Packing |
| GEO-4 ⚙ | deg W(7,2) ≥ 1080 (transfer from Q⁻(7,2) ≥ 216), W(9,2) ≥ 17538, Q⁻(9,2) ≥ 3960 | `W7_ge_1080`, `W9_ge_17538`, `Qm9_ge_3960` | GeoBounds |
| GEO-3 ⚙ | **deg Q⁺(9,2) ≥ 4783 > \|L\|/5** (in fact ≥ 6426, spectral) | `Qp9_ge_4783`, `Qp9_ge_6426`, `Qp9_gt_fifth` | GeoBounds |
| ASY-2 ⚙ | deg W(7,2) ≥ 1451, deg W(9,2) ≥ 28786, deg Q⁻(9,2) ≥ 4873 | `W7_ge_1451`, `W9_ge_28786`, `Qm9_ge_4873` | GeoBounds |
| GEO-5 ⚙ | W(7,2) ≤ 1575, W(9,2) ≤ 31479, Q⁺(9,2) ≤ 6975, Q⁻(9,2) ≤ 7087 | `W7_le_1575`, `W9_le_31479`, `Qp9_le_6975`, `Qm9_le_7087` | GeoBounds |
| GEO-6 ⚙ | ρ₂ = ρ₃ = 1/5 < ρ₄ ≤ 5/17 < ρ₅ | `rho_chain`, `rho_four_bounds`, `rho_five_bounds` | GeoBounds |
| ASY-6 | P_{a⊗b} = P_a ⊗ P_b; **τ(s₁⊗s₂) = τ(s₁)τ(s₂)** | `P_join`, `mh_join`, `tau_mul` | Tensor |
| ASY-6 Cor. 2 ⚙ | τ₃ = 1324, τ₄ = 13996; deg W(11,2) ≤ 553140, W(13,2) ≤ 9641268, W(15,2) ≤ 162635700, W(17,2) ≤ 2669910768 | `tau3`, `tau4`, `W11_le`, `W13_le`, `W15_le`, `W17_le` | Tensor |
| HARD-7, HARD-8 | odd-path lemma (parity of the path cycle) and the one-equation minimum (explicit optimal private points) | `path1_lb`, `local_lower`, `local_upper` | Gadget |
| HARD-9 | **deg Φ_ind = OPT + \|b\|, deg Φ_sub = OPT** (abstract configuration Φ) | `induced_degree`, `sub_degree`, `deg_phi` | Gadget |
| HARD-3 | every XOR system with non-empty rows → E3 system with the same OPT (tripling + chains) | `toE3`, `toE3_opt` | ToE3 |
| HARD-3+2+9 | **deg Φ_sub(split(toE3 S)) = OPT(S)**, deg Φ_ind(…) = OPT(S) + \|b′\| | `reduction_sub`, `reduction_ind` | HardMain |
| HARD-11 | no deletion in induced configurations; the unavoidable constant | `no_deletion`, `unavoidable` | NoDeletion |
| HARD-12 | **points on ≤ 2 lines ⇒ deg = #closed odd components** of the line graph | `Config.deg_two_points` | Tractable |
| TQ-2 (equality cases) ⚙ | **deg Q⁺(5,2) = 21**, **deg Q⁻(5,2) = 9** (section a^⊥ ≅ doily by ALG-3; orthogonal group line-transitive via reflection words; TR-1; witness restriction) | `Qp5_eq_21`, `Qm5_eq_9` | Quadrics5 |
| TQ-3 ⚙ | every optimal assignment of W(5,2) violates exactly 21 / 9 lines of every Sp(6,2)-translate of Q⁺(5,2) / Q⁻(5,2) | `Qp5_rigid`, `Qm5_rigid` | Quadrics5 |
| T1–T6, C1–C5 ⚙ | the finite gadget facts, on a 13-qubit model (table proved equal to the construction) | `mlab_spec`, `mlab_inj`, `lline_sum`, `lline_comm`, `lline_sign`, `local_closure`, `reg_*`, `path_pair`, `supp_*`, `lam_three` | GadgetModel |
| HARD-5 ⚙ | the Pauli labels of Φ_ind are distinct and non-zero; every line is a commuting zero-sum triple with the sign of Φ | `lab_inj`, `lab_ne_zero`, `line_sum`, `line_comm`, `line_sgn` | Realize |
| HARD-6 ⚙ | **closure lemma**: every zero-sum triple of distinct labels is a line of Φ_ind | `Hardness.closure` | Realize |
| HARD-9 (Pauli) ⚙ | **the induced Pauli configuration on the labels has deg = OPT + \|b\|**; its Φ_sub sub-configuration has deg = OPT; end-to-end for every XOR system | `lines_DR`, `realized_degree`, `realized_sub_degree`, `induced_reduction` | RealizeDeg |
| ASY-5 | phase-state averaging Σ_ε \|⟨ψ_ε\|P_a\|ψ_ε⟩\| = 4^m·2m·C(2m,m); Rademacher identity; Hermitian bound tr M³ ≥ λ³ − (tr M² − λ²)^{3/2}; Wallis | `sum_abs_ev`, `rademacher_abs`, `cube_trace_lower`, `wallis_w` | PhaseStates |
| ASY-5 | **(1/2 − ρ_N)·2^{N/2} ≥ φ(ℓ_N)** for N ≥ 2; **0.255·2^{−N/2} ≤ 1/2 − ρ_N ≤ 2^{−N/2}** for N ≥ 7; lim inf ≥ (2/π)^{3/2} − (1−2/π)^{3/2} | `delta_lower`, `rate_explicit`, `liminf_delta` | PhaseStates |
| ASY-7 (iii) | **ρ_{N+4} > ρ_N for every N ≥ 7** | `rho_window` | PhaseStates |
| DEN-1 | deg X ≥ \|L\|/2 − n^{3/2}(2^N−2)/(12√(2^N−1)) ≥ \|L\|/2 − n^{3/2}2^{N/2}/12; density form | `den1`, `den1_weak`, `den1_gap` | Density |
| DEN-1′ | ω-preserving (on X), span-injective maps preserve lines and degree; DEN-1 with any such N′ | `deg_configX_map`, `card_lines_configX_map`, `den1_embed` | Density |
| DEN-1′ | **intrinsic qubit number** N_X = (dim U + dim rad U)/2: DEN-1 holds with N_X, and no smaller N′ embeds X | `den1_intrinsic`, `intrinsic_min` | Intrinsic |
| DEN-2 | conditional expectations: one-coordinate averaging step; computable greedy assignment with 2\|V\| ≤ \|L\|; dense regime 1/(1−2ε)-approximation | `condExp_avg`, `greedy`, `greedy_half`, `den2` | Density |
| DEN-3 | the Pauli gadget Φ_ind needs N′ ≥ 3k qubits in every embedding (isotropic copies); D(Φ_ind) ≤ √n/(6·2^{3k/2}) | `isotropic_finrank_le`, `den3_qubits`, `den3_density` ⚙ (via the gadget certificates `reg_path`, `supp_aux`) | Den3 |
| GAME-1 | line/point LCS game: classical value (max over deterministic strategies; mixtures do not help) = 1 − deg/(3\|L\|) | `bestWins_eq`, `classicalValue_eq`, `mixture_le`, `agree_le_of_violated` | Game |
| GAME-2 | ω_c ≥ 5/6 always; W family: ω_c(G_N) ≤ 5/6 + 2^{−N/2}/3 and ω_c(G_N) → 5/6 | `classicalValue_ge`, `W_value_le`, `W_value_tendsto` | Game |
| GAME-1 (quantum) | Pauli operator solution; EPR identity ⟨Φ\|A⊗Bᵀ\|Φ⟩ = tr(AB)/d; Alice always valid; perfect quantum strategy | `operator_solution`, `epr_expect`, `alice_valid`, `quantum_win`, `quantum_perfect` | Game, QuantumGame |
| TIGHT-1 | Pauli expansion Σ⟨v\|P_a\|v⟩P_a = 2^N\|v⟩⟨v\|; (ii)⇒(i): a Pauli-flat state makes ASY-2 exact and its sign pattern optimal | `pauli_expand`, `flat_Mg`, `tight_of_flat` | Tight |
| TIGHT-1 | (i)⇒(ii): equality case of the cubic trace bound, rank-one idempotents; **deg = spectral bound ⇔ ∃ Pauli-flat state** | `cubic_eq_case`, `rank_one_of_idem`, `tight_converse`, `tight_iff` | TightConverse |
| TIGHT-1 examples ⚙ | ψ = (−3,1,…,1)/√24 is flat on Q⁺(7,2) ⇒ deg Q⁺(7,2) = 315 (second proof); X₄₉₆: \|L\| = 10880, **deg = 480** | `Qplus7_flat`, `Qplus7_eq_315_flat`, `X496_lines`, `X496_eq_480` | TightExamples |
| TIGHT-2 ⚙ | W(5,2) gauge kernel dim 7, incidence rank 56; y(a) mod 2 is a non-linear gauge; each violated set has 128 assignments | `finrank_kerW3`, `rank_incW3`, `qplus_mem_kerW`, `qplus_not_linear`, `card_fiber_violated` | GaugeKernel |
| NEG-1 | B(Λ) increasing; ASY-2 with any valid Λ; valid Λ ≥ every Rayleigh quotient; explicit ceilings (numbers 297/1488 stay in Python, X17) | `B_mono`, `spectral_lower_of_valid`, `valid_ge_rayleigh`, `ceiling` | Tight |
| ASY-7 (iv) ⚙ | **ρ₃ < ρ₄ < … < ρ₁₁** (new: deg W(19,2) ≤ 43768473840; ASY-2 lower bounds for N = 6..11) | `rho_strict_chain`, `rho_chain_ext`, `W19_le`, `W11_ge` … `W21_ge` | Chain |
| CONE-2 | **every subspace section of W: deg W(U) = 4^t deg W(2k−1,2)** (symplectic normal form by induction, no Witt) | `exists_sympData`, `std_section_degree`, `W_section_degree`, `W_section_degree'` | Section |
| CONE-2 (cor.) | tangent hyperplanes: deg W(a^⊥) = 4·deg W(2N−3,2); = 12 for W(5,2), = 252 for W(7,2) | `tangent_degree`, `W5_tangent` ⚙, `W7_tangent` ⚙ | SectionCor |
| CONE-3 (b) | **q ≠ 0 on rad U: deg(U ∩ Q) = 4^{t−1} deg W(2k−1,2)** (twist x ↦ x + q(x)r₀ onto a CONE-2 section; DEN-1′ for non-linear maps) | `deg_configX_fun`, `IsQuad`, `secQ`, `Q_section_degree_b` | ConeQuad |
| CONE-3 (cor.) | non-tangent hyperplanes: deg(a^⊥ ∩ Q) = deg W(2N−3,2); = 63 for Q^±(7,2) | `nontangent_degree`, `Qplus7_nontangent` ⚙, `Qminus7_nontangent` ⚙ | ConeQuad |
| CONE-3 (type) | **the degree of a non-degenerate quadric depends only on its type**: q = qplus + ω(c,·), and one transvection maps it to Q⁺ (qplus c = 0) or Q⁻ (qplus c = 1); on V 3 the degree is 21 or 9, on V 4 type 0 gives 315 | `quad_eq_qplus_add`, `tvL`, `deg_secQ_shift`, `deg_secQ_type`, `deg_secQ_qminus`, `deg_quad5` ⚙, `deg_quad5'` ⚙, `deg_quad7_plus` ⚙ | QuadType |
| CONE-1 (induced base) | the cone Y ⊗ ⟨Z⟩^t over any induced configuration Y: deg = 4^t deg Y | `XY`, `lines_XY`, `std_sub_degree` | ConeSub |
| CONE-3 (a) | **q = 0 on rad U: deg(U ∩ Q) = 4^t deg Q^δ(2k−1,2)**, δ the type of the induced form q₀ | `qInd`, `secQ_eq_image_XY`, `Q_section_degree_a`, `Q_section_degree_a'` | ConeSub |
| CONE-3 (tangent) | tangent hyperplanes: deg(a^⊥ ∩ Q) = 4 deg Q₀ (general), and exactly 84 for Q⁺(7,2), 36 for Q⁻(7,2), 1260 for Q⁺(9,2) | `tangent_quad_degree`, `tangent_quad_card`, `card_XY`, `tangent_Qplus7` ⚙, `tangent_Qminus7` ⚙, `tangent_Qplus9` ⚙ | ConeSub, TangentQuad |
| (audit) | axiom audit of all headline theorems (pure vs native_decide), run by check_all.sh | `#audit_pure`, `#audit_comp` | Audit |

### How the Q⁻(7,2) ≥ 216 certificate works
`Qm7Data` generates the 119 points, the 1071 lines and their signs, the 45696 doilies (one per 3-space
⟨c,u,v⟩, generated without duplicates) and, for every doily, the 60 grids spanned by ordered pairs of
disjoint lines. The single Boolean `certificate216` checks four things:
- every grid is an odd cycle inside its doily;
- every line of a doily lies in ≤ 24 of its 60 grids;
- for each of the 136 non-singular a, exactly 4032 doilies lie in O_a, and they cover each line of O_a ≤ 80 times;
- the 136 sets O_a cover each line ≤ 96 times.

The soundness chain is proved by hand:
grid ≥ 1 → doily ≥ 3 (60 > 24·2) → O_a ≥ 152 (4032·3 > 80·151) → Q⁻ ≥ 216 (136·152 > 96·215).
This uses 60 grids with coverage 24 in place of the blueprint's 10 grids with coverage 4; each grid simply
occurs 6 times. The counts match `code/cert216_full.py`.

## Changes to the skeleton (all deliberate)
- `Spectral.lean`: labels are `V N` and matrices are indexed by `Fin N → F` (P_a(r,c) = i^{y(a)+2z·c}[r = c+x]),
  in place of the bit-packed `Fin (4^N)`. The Pauli algebra becomes Finset algebra, with no popcount
  arithmetic. The ASY statements are restated in this encoding with the same content.
- `Qminus.lean`: the point type of `config` is `Fin 119`. Lines are generated with point indices, and the
  computational part lives in `PauliData/Qm7Data.lean`.
- The placeholder `True` theorems (`deg_invariant`, `cone_degree`, `chain_lemma`, `triangle_split`) were
  replaced by real statements.

## Notes on the new parts
- ASY-5 is proved with a **finite ensemble** (phase states ψ_ε = (i^{ε_c}), ε ∈ (ZMod 4)^d) in place of Haar
  measure. For Paulis with x ≠ 0 the mean of |⟨P⟩| is exactly the Haar value C(d,d/2)/2^d; the 2^N − 1 Pauli Z's
  are lost, which changes nothing asymptotically. Consequently the window statement ASY-7 (iii) holds from
  N = 7 (the blueprint's Haar constant 0.2679 gives N ≥ 6). No measure theory is used.
- The degree identity of Φ is proved for the Pauli signs of the construction (chain lines even; column 3 of each
  odd path odd), and HARD-6 is proved for every E3 system with the shape produced by the triangle split.

## Not formalised (remaining blueprint items)
- ASY-5′ (exact line correlation via Kendall's τ of Gamma variables), hence GAME-2's lower side and GAME-3:
  genuinely continuous probability — **paper only**.
- TIGHT-2: the count 120 of optimal W(5,2) violated sets (hence 15360 = 120·128) and the SIC correspondence.
- NEG-1 numerical ceilings 297 (Q⁻(7,2)) and 1488 (W(7,2)): λ_max of explicit matrices, checked in
  `certificates/certify_asym.py` (X17).
- GAME-4, OP-1 (noise model, Azuma–Hoeffding).
- HARD-10 (complexity theory) stays on paper by design.

See `blueprint/13_lean_findings.md` for what changed relative to the blueprint statements.
