# Certificate checker

    python3 certify.py        # numpy only; ~10 s; exits non-zero if any check fails

Each printed label (T1-T6, C1-C5, D1-D3, S1-S7, U1-U5, R1-R2) matches Appendix A of the paper.
Witness files: one 0/1 value per line, in the point order produced by `geometry()` in certify.py
(all non-zero vectors of F_2^{2n} in lexicographic order, filtered to the quadric).

## Round 2: asymptotic checks (blueprint/10)
`certify_asym.py` (also run automatically at the end of `certify.py`) performs X1–X11 (X11: measure-and-assign correlation κ):
trace formula; integer-phase vs matrix signs; ASY-3 bound values; Hoggar equality for W(5,2); the 120-orbit;
deg Q+(7,2) = 315 (uses `witness_Qp7_2.txt`, 135 entries in `geometry("Q+", 4)` point order); Haar/Wallis constants;
negative-line closed form; tensor-product witnesses; strict chain ρ₃ < … < ρ₁₁; the 2^{−N/2} polynomial inequality.

## Round 3 (blueprint/11)
X12–X17: Q⁺(7,2) closed-form flat state; the 5-qubit X₄₉₆ exact degree 480 (`flat5_496.json`); W(5,2) gauge kernel dim 7 (15360); brute-force LCS game values (doily 14/15, Peres–Mermin 17/18); negative-line counts vs published tables; NEG-1 ceilings (`qm7_L1_witness.json`).
