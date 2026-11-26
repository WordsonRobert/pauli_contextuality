# pauli_contextuality

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24567331.svg)](https://doi.org/10.5281/zenodo.24567331)

**How many contexts must a noncontextual model get wrong?**
Code, certificates and Lean 4 proofs for the paper

> *Almost half wrong: the contextuality degree of multi-qubit Pauli configurations*
> Wordson, Savith A, C. Jerin Mahibha — [`paper/pauli_contextuality.pdf`](paper/pauli_contextuality.pdf)

---

## The question in 30 seconds

Take some multi-qubit Pauli observables (like `XZ`, `YY`, `ZI`). Call three of them a **context** if they commute
and multiply to `+I` or `−I`. A classical hidden-variable model has to give every observable a fixed value `±1`.
On a context, the product of the three values should equal the sign (`+1` or `−1`). Quantum mechanics always gets
this right. A classical model cannot: some contexts come out wrong.

The **contextuality degree** is the smallest number of wrong contexts that any classical assignment can achieve.

The smallest example is the Peres–Mermin square (9 two-qubit observables, 6 contexts): every classical model gets
at least 1 context wrong.

## What we found

| | |
|---|---|
| **The key identity** | number of wrong contexts = `|contexts|/2 − tr(M³) / (12·2^N)`, where `M = Σ g(a)·P_a` is the signed sum of the observables. |
| **The limit** | For all N-qubit Paulis, the fraction of contexts any classical model must get wrong tends to **½**, at rate **2^(−N/2)**. So: *almost half wrong*. |
| **When the bound is exact** | Exactly when a quantum state has Pauli expectations of equal size on the observables and zero elsewhere ("Pauli-flat"). On 3 qubits these are the Hoggar SIC states, so the best classical assignments are sign patterns of maximally magic states. |
| **Games** | Each configuration is a two-player game. Quantum players win always (with N EPR pairs); classical players win with probability `1 − deg/(3·|contexts|)`, which tends to **5/6**, the lowest possible for this kind of game. |
| **Complexity** | Computing the degree is NP-hard, even when every possible context is included. Hard instances are exponentially sparse; dense ones are easy. |
| **New numbers** | `deg W(7,2) ≥ 1451`, `deg W(9,2) ≥ 28786`, `deg Q⁻(7,2) ≥ 216`, `deg Q⁺(9,2) ≥ 6426`, `deg Q⁻(9,2) ≥ 4873`, a short proof of `deg Q⁺(7,2) = 315`, and a new 5-qubit configuration with degree exactly 480. |

Main geometries (best known values):

| geometry | qubits | contexts | degree |
|---|---|---|---|
| W(3,2) (doily) | 2 | 15 | 3 |
| W(5,2) | 3 | 315 | 63 |
| Q⁺(7,2) | 4 | 1575 | 315 |
| Q⁻(7,2) | 4 | 1071 | between 216 and 315 |
| W(7,2) | 4 | 5355 | between 1451 and 1575 |
| W(9,2) | 5 | 86955 | between 28786 and 31479 |

## What is in this repository

```
paper/          the paper: pauli_contextuality.tex, the compiled PDF, and the class file
lean/           Lean 4 + Mathlib formalisation (about 1,100 theorems, no sorry)
certificates/   independent Python checker: re-verifies every finite fact in about a minute
code/           the scripts that found the constructions, witnesses and bounds
data/           machine-readable certificate data (JSON)
blueprint/      working notes: every result with numbered proof steps (one file per topic)
```

## Check the results yourself

```bash
git clone https://github.com/WordsonRobert/pauli_contextuality.git
cd pauli_contextuality
```

### 1. The quick check (about a minute, Python only)

```bash
pip install -r requirements.txt
cd certificates
python3 certify.py
```

This recomputes everything from scratch (Pauli products, all lines, all signs, every witness) and prints one
`[PASS]` line per check: 37 core checks (hardness gadget, small geometries, witnesses) followed by 18 checks for
the spectral results (labelled X1–X17). It exits with an error if anything fails. To run only the spectral
checks: `python3 certify_asym.py`.

### 2. The formal proofs (Lean 4)

You need [elan](https://github.com/leanprover/elan) (the Lean version manager).

```bash
cd lean
lake exe cache get     # download a prebuilt Mathlib (saves hours)
lake build             # builds everything and prints the axiom audit
```

The toolchain is pinned to Lean `v4.31.0` and Mathlib `v4.31.0`. The build ends with an **axiom audit**: for each
headline theorem it prints whether it uses only Lean's three standard axioms, or also trusts a finite computation
done with `native_decide`. A saved copy of that output is in
[`lean/build_evidence/audit_summary.txt`](lean/build_evidence/audit_summary.txt).

Every theorem statement is listed verbatim in [`lean/THEOREMS.md`](lean/THEOREMS.md). The paper's Appendix C maps
each numbered result to its Lean name.

## Where to find each result

| result (paper) | Lean file(s) in `lean/PauliContextuality/` | Python check |
|---|---|---|
| Pauli matrices, group law, cycle-sign lemma | `PauliMatrix`, `Basic`, `CycleSign`, `Invariance` | X2 |
| Transfer, rigidity, packing barrier | `Cover`, `Transfer`, `Profile`, `Packing` | — |
| Trace identity, spectral bound | `Spectral`, `SpectralConfig` | X1, X3 |
| ρ_N → ½ and the rate 2^(−N/2) | `SpectralW`, `NegLines`, `Tensor`, `PhaseStates`, `Chain` | X3, X7–X10 |
| Tight ⇔ Pauli-flat state | `Tight`, `TightConverse` | — |
| W(5,2) = 63, Q⁺(7,2) = 315, X₄₉₆ = 480, gauge space | `SpectralExact`, `TightExamples`, `GaugeKernel` | X4–X6, X12–X14 |
| Nonlocal games | `Game`, `QuantumGame` | X15 |
| Small geometries, cones, sections | `GeoBounds`, `Quadrics5`, `ThreeQubit`, `Cone`, `Section`, `ConeQuad`, `QuadType`, `ConeSub`, `TangentQuad` | D1–D3, R1–R2, K1–K2 |
| deg Q⁻(7,2) ≥ 216 | `Qminus`, `QminusBridge`, data in `lean/PauliData/Qm7Data.lean` | A1–A4, S1–S2 |
| Hardness, density | `Hardness`, `Gadget`, `GadgetModel`, `ToE3`, `HardMain`, `Realize`, `RealizeDeg`, `NoDeletion`, `Tractable`, `Density`, `Intrinsic`, `Den3` | T1–T6, C1–C5 |

**Not formalised** (proved in the paper only): the sharp constant (2/π)^(3/2) for the rate (needs continuous
probability), the noise and sampling statements for games, the count 120 of optimal W(5,2) violated sets, and the
complexity-class statements (the reductions themselves *are* formalised).

## What exactly is trusted

- **Lean.** No `sorry`, no user axioms. 195 of the 270 audited headline theorems use only `propext`,
  `Classical.choice` and `Quot.sound`. The other 75 also trust finite computations evaluated by `native_decide`
  (line counts, witness counts, the Q⁻(7,2) certificate). The Q⁻(7,2) data module is compiled to native code, so
  that one certificate also trusts the C compiler.
- **Python.** `certificates/certify.py` shares no code with the search scripts or the Lean data. It is a second,
  unrelated computation of every finite fact.

## Vocabulary (for readers new to the area)

- **Pauli label**: an N-qubit Pauli operator written as a bit vector `(x|z)` of length 2N; e.g. `Y = (1|1)`.
- **Line / context**: three distinct non-identity labels `a, b, a+b` that commute.
- **Sign** of a line: `+1` or `−1`, the scalar in `P_a · P_b · P_c = ±I`.
- **Assignment**: a choice of `±1` for every observable. A line is **violated** if the product of its three
  values differs from its sign.
- **Degree**: the minimum number of violated lines over all assignments. **Ratio**: degree / number of lines.
- **W(2N−1,2)**: all N-qubit Paulis with all their lines. **Q⁺, Q⁻**: the two kinds of quadrics inside it
  (Q⁺ = the real, symmetric Paulis).
- **Induced configuration**: a set of Paulis together with *every* line it contains.

## Citing

Please cite the paper (see [`CITATION.cff`](CITATION.cff)). The code and proofs are archived on Zenodo:
[doi:10.5281/zenodo.24567331](https://doi.org/10.5281/zenodo.24567331).

```bibtex
@article{pauli_contextuality_2026,
  title   = {Almost half wrong: the contextuality degree of multi-qubit {Pauli} configurations},
  author  = {Wordson and A, Savith and Mahibha, C. Jerin},
  year    = {2026},
  note    = {arXiv:XXXX.XXXXX},
  url     = {https://github.com/WordsonRobert/pauli_contextuality},
  doi     = {10.5281/zenodo.24567331}
}
```

## License

MIT, see [`LICENSE`](LICENSE).
