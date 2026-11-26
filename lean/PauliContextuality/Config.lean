/-
Config.lean — abstract configurations, violated sets, degree. Blueprint: 00, 01 (ALG-1).
-/
import PauliContextuality.Basic

namespace PauliCtx

/-- An abstract configuration on a finite point type `α`: a finset of 3-element lines with signs. -/
structure Config (α : Type) [Fintype α] [DecidableEq α] where
  lines : Finset (Finset α)
  sign  : Finset α → F
  three : ∀ l ∈ lines, l.card = 3

variable {α : Type} [Fintype α] [DecidableEq α]

namespace Config

/-- `l` is violated by `s` iff `Σ_{p∈l} s p ≠ sign l`. -/
def Violated (C : Config α) (s : α → F) (l : Finset α) : Prop := (∑ p ∈ l, s p) + C.sign l ≠ 0

instance (C : Config α) (s : α → F) (l : Finset α) : Decidable (C.Violated s l) := by
  unfold Violated; infer_instance

def violated (C : Config α) (s : α → F) : Finset (Finset α) := C.lines.filter (C.Violated s)

/-- Degree: minimum number of violated lines (the assignment space is finite and non-empty). -/
noncomputable def deg (C : Config α) : ℕ :=
  (Finset.univ : Finset (α → F)).inf' Finset.univ_nonempty (fun s => (C.violated s).card)

theorem deg_le (C : Config α) (s : α → F) : C.deg ≤ (C.violated s).card :=
  Finset.inf'_le _ (Finset.mem_univ s)

theorem exists_opt (C : Config α) : ∃ s, (C.violated s).card = C.deg := by
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (α → F)))
    Finset.univ_nonempty (fun s => (C.violated s).card)
  exact ⟨s, hs.symm⟩

/-- Restriction to a sub-family of lines (same signs). -/
def sub (C : Config α) (L : Finset (Finset α)) (h : L ⊆ C.lines) : Config α :=
  { lines := L, sign := C.sign, three := fun l hl => C.three l (h hl) }

theorem violated_sub (C : Config α) (L) (h : L ⊆ C.lines) (s : α → F) :
    (C.sub L h).violated s = C.violated s ∩ L := by
  ext l; simp [violated, sub, Finset.mem_filter, Finset.mem_inter]; tauto

end Config
end PauliCtx
