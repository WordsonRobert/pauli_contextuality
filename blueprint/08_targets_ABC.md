# 08. Targets A, B, C (round 1): the attack on deg Q⁻(7,2) = 315

> **Round 2 (Nov 2026)** redefined A/B/C as asymptotic targets (strict jumps; lim inf/lim sup; lim = 1/2).
> They are resolved in `10_asymptotics.md`. Byproducts relevant here: deg W(7,2) ≥ 1451 and Q⁺(9,2) ≥ 6426 now come
> from the spectral bound (better than the 216-transfer values). For Q⁻(7,2) itself the spectral bound gives only
> 145 < 216, so the round-1 attack below is still the state of the art for that instance.

Interpretation used: **A** = structural lower bound, **B** = classification of optimal assignments, **C** = stronger
witnesses. These are the three directions proposed for the single unresolved instance Q⁻(7,2), whose value controls
W(7,2) and Q⁺(9,2).

## C. Stronger witnesses — state of the art: 216 (GEO-2)
What was done:
- Integrality cascade over line-orbits of reflection subgroups: stabilisers of random subspaces of dimension 1–4,
  with and without inner reflections; about 1000 orbits; iterated to a fixed point. Best: O_a, 756 lines → 216.
- Orbits of random small subgroups (1–3 generators, random elements of prime order): about 600 groups. Recorded
  orbit sizes that contain a whole doily: 15, 30, 40, 45, 60, 80, 90, 105, 135, 160, 180, 210, 240, 270, 315, 320,
  480, 630, 756, 864, 896, 1071. All are ≡ 0 mod 5 except 756, 864, 896 and 1071. Rounding gains: 756 → 216,
  896 → 216, 864 → 215. So no doily-containing orbit beats 216.
- Second-level cascade: orbits of size strictly between 756 and 1071 that contain some O_{a'}. None were found in 250
  random groups.
- Profile integer programs (stabilisers of a non-singular point, a singular point and an anisotropic plane, with
  about 9700 witnesses) all give 215. Integrality per orbit is weaker than the cascade.
- SAT certification of larger witnesses (a 340-line symmetric union of norm classes, needing ≥ 69): timeout at 50 min.

**Observation (worth proving).** Every line-orbit of a subgroup that contains a doily and has fewer than 756 lines has
size divisible by 5. If this holds for all subgroups, single-step cascades from doilies cannot beat 216.

**Next ideas for C.**
- Witnesses that are not doily-based: genuinely 4-qubit configurations with ratio > 216/1071, certified by odd-cycle
  covers. An odd-cycle cover of S where each line is covered c times by k odd cycles gives deg S ≥ ⌈k/c⌉. Search for
  sub-configurations S whose odd-cycle covers have k/c/|L(S)| > 0.2017. That is an LP over cycles: a column-generation
  search.
- Semidefinite (Lasserre level 2) relaxation in the association scheme of Q⁻(7,2) lines. This is not a packing bound,
  so the barrier does not apply.

## B. Classification of optimal assignments — strong evidence for a single orbit
- 16 independent optimal assignments (tabu, distinct seeds) give 16 distinct violated sets. Their coloured point–line
  incidence graphs are all isomorphic (nauty certificates). For Q⁻(7,2) every incidence automorphism comes from O⁻(8,2)
  (fundamental theorem of polar spaces), so they lie in one O⁻(8,2)-orbit.
- |Aut(Q⁻(7,2))| = 394813440. Stabiliser of an optimal violated set: 1008. Orbit size: 391680 = 1632 · 240, where 1632
  is the number of anisotropic planes. That is 240 optimal sets per anisotropic plane, the same number Li–Gupta–Ganesh
  found for Q⁺(7,2).
- Structure (certificate R3, all 16 runs): 3 tight parabolic sections a^⊥ with a ∈ E, E an anisotropic plane; E^⊥ ∩ Q⁻ is
  a Q⁺(5,2) carrying exactly 21 violated lines; points have violation degree 3/7/9 (14/21/84 points); parabolic
  sections meet V in 63/87/95/99 lines (3/42/63/28); tangent sections in 51/59/63 lines (14/21/84).
**CONJ-2.** The optimal violated sets of Q⁻(7,2) are exactly one O⁻(8,2)-orbit of size 391680. Equivalently there are
391680 optimal assignments modulo the 8-dimensional gauge (linear functionals).

## A. Structural lower bound — open
What would close it:
1. Show that every assignment with < 315 violations has a local defect that can be repaired, or
2. Use CONJ-2's structure: show that any optimal V must be tight on some Q⁺(5,2) = E^⊥ and then bound the rest. This is a
   classification-driven proof in the style of Li–Gupta–Ganesh (local constraints + exhaustive enumeration).
3. Formal route via SAT with symmetry breaking (O⁻(8,2) has order 3.9·10⁸; a lex-leader on 119 points plus gauge
   fixing) and DRAT proof. Not feasible on 2 cores; possibly feasible with a cluster.

Data and scripts: code/cascade*.py, code/smallorbit.py, code/classify_qm7.py, code/profile_qm7.py, code/structure_qm7.py.
