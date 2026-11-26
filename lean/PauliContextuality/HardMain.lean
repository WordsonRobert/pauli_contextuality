/-
HardMain.lean — the composite value identity of the hardness reduction
(HARD-3 → HARD-2 → HARD-9).

For every XOR system S with non-empty rows, let S' = split(toE3 S) (an E3 system in which two
equations share at most one variable and every middle variable is original). Then

    deg Φ_sub(S') = OPT(S),     deg Φ_ind(S') = OPT(S) + |b'|.

The complexity-theoretic consequences (HARD-10) stay on paper.
-/
import PauliContextuality.Gadget
import PauliContextuality.ToE3

set_option synthInstance.maxSize 2048

namespace PauliCtx.Hardness



variable {ν ε : Type} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε]

/-- **Value identity of the reduction (sub-configurations).** -/
theorem reduction_sub (S : GSys ν ε) (hne : ∀ e, (S.eqs e).Nonempty) :
    (Phi (toE3 S).split false).deg = S.opt := by
  rw [sub_degree, split_opt, toE3_opt S hne]

/-- **Value identity of the reduction (induced configurations).** -/
theorem reduction_ind (S : GSys ν ε) (hne : ∀ e, (S.eqs e).Nonempty) :
    (Phi (toE3 S).split true).deg = S.opt + nNeg (toE3 S).split := by
  rw [induced_degree, split_opt, toE3_opt S hne]

end PauliCtx.Hardness
