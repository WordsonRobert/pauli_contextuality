/-
GadgetModel.lean — the finite model of one equation of the construction Φ (blueprint HARD-5/6,
facts T1–T6 and C1–C5 of certify.py).

The model has 13 qubits: three blocks of 3 qubits (one per position i = 0,1,2 of the equation) and
two registers of 2 qubits (one per odd path t = 0,1). Its 33 local points are
  * copies `c_{i,r} = Z^{λ_r}` on block i (λ = 100, 010, 001, 111);
  * aux points `u_{k+1} = s₁ + … + s_{k+2}` (k = 0..8), s_{3r+i+1} = c_{i,r};
  * path points `φ_t(T_q)` (q = 0..5 = p₂₁, p₂₂, p₂₃, p₃₁, p₃₂, p₃₃) of the template
      rows (ZI,IZ,ZZ)⊗II / (IX⊗IZ, XI⊗ZI, XX⊗ZZ) / (ZX⊗IZ, XZ⊗ZI, YY⊗ZZ),
    with φ_t : X₁ ↦ X on qubit 0 of block 1, X₂ ↦ X on qubit 0 of block 2, Z₁ ↦ Z^{111} on block 1,
    Z₂ ↦ Z^{111} on block 2, private qubits ↦ register t.
All facts below are statements about this fixed finite table and are checked by computation.
-/
import PauliContextuality.Gadget

namespace PauliCtx.Hardness.Model

/-- model qubits: (block i, qubit j) and (register t, qubit j) -/
abbrev Qm := (Fin 3 × Fin 3) ⊕ (Fin 2 × Fin 2)
/-- model Pauli labels (x | z) -/
abbrev LM := (Qm → F) × (Qm → F)
/-- local points: copies (i, r) and private points k (0..8 aux, 9.. path) -/
abbrev Lx := (Fin 3 × Fin 4) ⊕ Fin 21

def lam : Fin 4 → Fin 3 → F := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1]]

def mcopy (i : Fin 3) (r : Fin 4) : LM :=
  (0, fun q => match q with
    | .inl (i', j) => if i' = i then lam r j else 0
    | .inr _ => 0)

def maux (k : ℕ) : LM := ∑ x : Fin 3 × Fin 4, if rk x < k + 2 then mcopy x.1 x.2 else 0

/-- template points p₂₁, p₂₂, p₂₃, p₃₁, p₃₂, p₃₃ on 4 virtual qubits (x₁..x₄ | z₁..z₄) -/
def tmpl : Fin 6 → (Fin 4 → F) × (Fin 4 → F) :=
  ![(![0, 1, 0, 0], ![0, 0, 0, 1]),   -- IX ⊗ IZ
    (![1, 0, 0, 0], ![0, 0, 1, 0]),   -- XI ⊗ ZI
    (![1, 1, 0, 0], ![0, 0, 1, 1]),   -- XX ⊗ ZZ
    (![0, 1, 0, 0], ![1, 0, 0, 1]),   -- ZX ⊗ IZ
    (![1, 0, 0, 0], ![0, 1, 1, 0]),   -- XZ ⊗ ZI
    (![1, 1, 0, 0], ![1, 1, 1, 1])]   -- YY ⊗ ZZ

/-- the embedding φ_t of the template -/
def mphi (t : Fin 2) (T : (Fin 4 → F) × (Fin 4 → F)) : LM :=
  (fun q => match q with
    | .inl (i, j) => if j = 0 then (if i = 1 then T.1 0 else if i = 2 then T.1 1 else 0) else 0
    | .inr (t', j) => if t' = t then T.1 ⟨2 + j.val, by omega⟩ else 0,
   fun q => match q with
    | .inl (i, _) => if i = 1 then T.2 0 else if i = 2 then T.2 1 else 0
    | .inr (t', j) => if t' = t then T.2 ⟨2 + j.val, by omega⟩ else 0)

/-- the model label of a local point, as defined (copies, prefix sums, template under φ_t) -/
def mlabSpec : Lx → LM
  | .inl (i, r) => mcopy i r
  | .inr k => if h : k.val < 9 then maux k.val
      else mphi ⟨(k.val - 9) / 6, by omega⟩ (tmpl ⟨(k.val - 9) % 6, by omega⟩)

/-- index of a local point (copies 3r+i, private points 12+k) and of a model qubit -/
def lidx : Lx → ℕ
  | .inl (i, r) => 3 * r.val + i.val
  | .inr k => 12 + k.val

def qidx : Qm → ℕ
  | .inl (i, j) => 3 * i.val + j.val
  | .inr (t, j) => 9 + 2 * t.val + j.val

/-- the 33 model labels as bitmasks over the 13 model qubits (x-parts and z-parts) -/
def xsTab : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  64, 8, 72, 64, 8, 72, 64, 8, 72, 64, 8, 72]
def zsTab : Array ℕ := #[1, 8, 64, 2, 16, 128, 4, 32, 256, 7, 56, 448, 9, 73, 75, 91, 219, 223, 255,
  511, 504, 1024, 512, 1536, 1080, 960, 2040, 4096, 2048, 6144, 4152, 2496, 6648]

/-- the model label of a local point (table form; `mlab_spec` shows it equals `mlabSpec`) -/
def mlab (x : Lx) : LM :=
  (fun q => if (xsTab[lidx x]!).testBit (qidx q) then 1 else 0,
   fun q => if (zsTab[lidx x]!).testBit (qidx q) then 1 else 0)

/-- the table is the construction -/
theorem mlab_spec : ∀ x : Lx, mlab x = mlabSpec x := by native_decide

/-- the local line K -/
def lline (K : Fin 20) : Finset Lx := (cpTab K).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
  (privPart K).map ⟨Sum.inr, Sum.inr_injective⟩

/-- symplectic form, Y-count and the z·x pairing on model labels -/
def omegaM (a b : LM) : F := ∑ q, (a.1 q * b.2 q + a.2 q * b.1 q)
def ycountM (a : LM) : ℕ := (Finset.univ.filter (fun q => a.1 q = 1 ∧ a.2 q = 1)).card
def zxM (a b : LM) : F := ∑ q, a.2 q * b.1 q
/-- the phase of `P_a P_b` (cf. `ph` in PauliMatrix.lean) -/
def phM (a b : LM) : ZMod 4 := (ycountM a : ZMod 4) + ycountM b + dbl (zxM a b) - ycountM (a + b)
def sgnM (a b : LM) : F := if phM a b = 0 then 0 else 1

/-- type-A local points: copies and aux points -/
def isA : Lx → Prop
  | .inl _ => True
  | .inr k => k.val < 9

instance : DecidablePred isA := fun x => by cases x <;> unfold isA <;> infer_instance

/-- the register of a path point -/
def regOf : Lx → Option (Fin 2)
  | .inl _ => none
  | .inr k => if h : k.val < 9 then none else some ⟨(k.val - 9) / 6, by omega⟩

/-- vanishing on register t -/
def regZero (t : Fin 2) (m : LM) : Prop := ∀ j, m.1 (.inr (t, j)) = 0 ∧ m.2 (.inr (t, j)) = 0

instance (t : Fin 2) (m : LM) : Decidable (regZero t m) := by unfold regZero; infer_instance

/-- the block content of block i (z-part) -/
def bcM (m : LM) (i : Fin 3) : Fin 3 → F := fun j => m.2 (.inl (i, j))

/-- the block support of a model label -/
def suppM (m : LM) : Finset (Fin 3) := Finset.univ.filter (fun i => bcM m i ≠ 0)

/-! ### the finite facts -/

/-- (T2, C2) local labels are pairwise distinct -/
theorem mlab_inj : ∀ x y : Lx, mlab x = mlab y → x = y := by native_decide

/-- (T1, C3) every local line sums to zero and its points pairwise commute -/
theorem lline_sum : ∀ K : Fin 20, ∑ x ∈ lline K, mlab x = 0 := by native_decide

theorem lline_comm : ∀ K : Fin 20, ∀ x ∈ lline K, ∀ y ∈ lline K, omegaM (mlab x) (mlab y) = 0 := by
  native_decide

/-- (T3, T6) the Pauli signs of the local lines: chain lines even, column 3 of each path odd -/
theorem lline_sign : ∀ K : Fin 20, ∀ x ∈ lline K, ∀ y ∈ lline K, x ≠ y → sgnM (mlab x) (mlab y) = sgnT K := by
  native_decide

theorem lline_card : ∀ K : Fin 20, (lline K).card = 3 := by decide

set_option synthInstance.maxSize 1024 in
/-- (C4, T5) **local closure**: every zero-sum triple of distinct local labels is a local line -/
theorem local_closure : ∀ x y z : Lx, x ≠ y → x ≠ z → y ≠ z → mlab x + mlab y + mlab z = 0 →
    ∃ K, lline K = {x, y, z} := by native_decide

/-- (T4) type-A points vanish on both registers; path points are non-zero exactly on their own -/
theorem reg_A : ∀ x : Lx, isA x → ∀ t, regZero t (mlab x) := by native_decide
theorem reg_path : ∀ x : Lx, ∀ t, regOf x = some t → ¬ regZero t (mlab x) := by native_decide
theorem reg_other : ∀ x : Lx, ∀ t t', regOf x = some t → t' ≠ t → regZero t' (mlab x) := by native_decide
theorem regOf_none : ∀ x : Lx, regOf x = none ↔ isA x := by decide

/-- (T4) two path points of one register whose register parts cancel sum to a type-A label -/
theorem path_pair : ∀ x y : Lx, ∀ t, regOf x = some t → regOf y = some t → x ≠ y →
    regZero t (mlab x + mlab y) → ∃ z, isA z ∧ mlab z = mlab x + mlab y := by native_decide

/-- type-A labels have no x-part and live on the blocks -/
theorem A_x : ∀ x : Lx, isA x → (mlab x).1 = 0 := by native_decide

/-- (C5) block supports: copies {i}; u₁ on {0,1}; u₉ on {1,2}; the other aux points on all blocks -/
theorem supp_copy : ∀ i r, suppM (mlab (.inl (i, r))) = {i} := by native_decide
theorem supp_aux : ∀ k : Fin 21, k.val < 9 →
    suppM (mlab (.inr k)) = if k.val = 0 then {0, 1} else if k.val = 8 then {1, 2} else Finset.univ := by
  native_decide

/-- (C1) three distinct λ's never sum to zero -/
theorem lam_three : ∀ r r' r'' : Fin 4, r ≠ r' → r ≠ r'' → r' ≠ r'' → lam r + lam r' + lam r'' ≠ 0 := by
  decide

/-- copies are `λ_r` on their block -/
theorem bc_copy : ∀ i r i', bcM (mlab (.inl (i, r))) i' = if i' = i then lam r else 0 := by native_decide

theorem lam_ne : ∀ r, lam r ≠ 0 := by decide
theorem lam_inj : ∀ r r', lam r = lam r' → r = r' := by decide

end PauliCtx.Hardness.Model
