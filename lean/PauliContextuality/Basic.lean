/-
Basic.lean — Pauli labels, symplectic form, Pauli group law, lines and signs.
Blueprint: 00_conventions.md, 01_algebra.md (ALG-0).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PauliCtx

/-- `F = ZMod 2`. -/
abbrev F := ZMod 2

/-- An `n`-qubit Pauli label `(x | z)`. -/
abbrev V (n : ℕ) := (Fin n → F) × (Fin n → F)

variable {n : ℕ}

/-- Symplectic form ω(p,q) = Σ x_i z'_i + z_i x'_i. -/
def omega (p q : V n) : F := ∑ i, (p.1 i * q.2 i + p.2 i * q.1 i)

/-- Number of `Y` factors. -/
def ycount (p : V n) : ℕ := (Finset.univ.filter (fun i => p.1 i = 1 ∧ p.2 i = 1)).card

/-- Integer dot product of `z_p` with `x_q`, as a natural number. -/
def zx (p q : V n) : ℕ := (Finset.univ.filter (fun i => p.2 i = 1 ∧ q.1 i = 1)).card

/-- Pauli group element `(k, p)` meaning `i^k X^x Z^z`. -/
abbrev PG (n : ℕ) := ZMod 4 × V n

/-- Group law (ALG-0): `(k₁,p)(k₂,q) = (k₁+k₂+2⟦z_p·x_q⟧, p+q)`. -/
def mulPG (a b : PG n) : PG n := (a.1 + b.1 + 2 * (zx a.2 b.2 : ZMod 4), a.2 + b.2)

/-- Canonical Hermitian representative `P(p) = (⟦y(p)⟧, p)`. -/
def canon (p : V n) : PG n := ((ycount p : ZMod 4), p)

/-! ### The doubling map `ZMod 2 → ZMod 4`, `a ↦ 2·a` -/

/-- `dbl a = 2 · a.val ∈ ZMod 4`. It is additive (ALG-0 step 1: `2·(u mod 2) = 2u` in `ZMod 4`). -/
def dbl (a : F) : ZMod 4 := 2 * (a.val : ZMod 4)

theorem dbl_add (a b : F) : dbl (a + b) = dbl a + dbl b := by
  revert a b; decide

@[simp] theorem dbl_zero : dbl 0 = 0 := by decide

@[simp] theorem dbl_one : dbl 1 = 2 := by decide

theorem dbl_sum {ι : Type*} (s : Finset ι) (f : ι → F) : dbl (∑ i ∈ s, f i) = ∑ i ∈ s, dbl (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dbl_add, ih]

theorem two_mul_natCast (k : ℕ) : (2 : ZMod 4) * (k : ZMod 4) = dbl (k : F) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, Nat.cast_succ, mul_add, ih, dbl_add, dbl_one, mul_one]

theorem dbl_eq_two_mul_val (a : F) : dbl a = 2 * (a.val : ZMod 4) := rfl

/-! ### Counting lemmas: cardinalities mod 2 are dot products -/

theorem card_filter_cast (P Q : Fin n → F) :
    (((Finset.univ.filter (fun i => P i = 1 ∧ Q i = 1)).card : ℕ) : F) = ∑ i, P i * Q i := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize P i = x
  generalize Q i = y
  revert x y; decide

theorem zx_cast (p q : V n) : (zx p q : F) = ∑ i, p.2 i * q.1 i := card_filter_cast _ _

/-- Hyperbolic and elliptic quadratic forms (00_conventions). -/
def qplus (p : V n) : F := ∑ i, p.1 i * p.2 i
def qminus (p : V (n+1)) : F := qplus p + p.1 0 + p.2 0

theorem ycount_cast (p : V n) : (ycount p : F) = qplus p := card_filter_cast _ _

theorem zx_self (p : V n) : zx p p = ycount p := by
  unfold zx ycount
  congr 1
  ext i
  simp [and_comm]

@[simp] theorem zx_zero_left (q : V n) : zx 0 q = 0 := by
  simp [zx]

@[simp] theorem zx_zero_right (p : V n) : zx p 0 = 0 := by
  simp [zx]

theorem two_mul_zx (p q : V n) : (2 : ZMod 4) * (zx p q : ZMod 4) = dbl (∑ i, p.2 i * q.1 i) := by
  rw [two_mul_natCast, zx_cast]

theorem add_self_F (x : F) : x + x = 0 := by
  revert x; decide

theorem add_self_V (p : V n) : p + p = 0 := by
  ext i <;> simp [add_self_F]

/-! ### ALG-0 -/

theorem mulPG_assoc (a b c : PG n) : mulPG (mulPG a b) c = mulPG a (mulPG b c) := by
  simp only [mulPG, Prod.mk.injEq]
  refine ⟨?_, add_assoc _ _ _⟩
  rw [two_mul_zx, two_mul_zx, two_mul_zx, two_mul_zx]
  have key : (∑ i, a.2.2 i * b.2.1 i) + (∑ i, (a.2 + b.2).2 i * c.2.1 i)
      = (∑ i, b.2.2 i * c.2.1 i) + (∑ i, a.2.2 i * (b.2 + c.2).1 i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  have h2 := congrArg dbl key
  rw [dbl_add, dbl_add] at h2
  linear_combination h2

theorem mulPG_one_left (a : PG n) : mulPG (0, 0) a = a := by
  simp [mulPG]

theorem mulPG_one_right (a : PG n) : mulPG a (0, 0) = a := by
  simp [mulPG]

/-- Inverse (ALG-0 item 1). -/
theorem mulPG_inv (a : PG n) : mulPG a (-a.1 - 2 * (zx a.2 a.2 : ZMod 4), a.2) = (0, 0) := by
  simp only [mulPG, Prod.mk.injEq]
  exact ⟨by ring, add_self_V _⟩

/-- Centrality of phases (ALG-0 item 2). -/
theorem mulPG_central (k : ZMod 4) (a : PG n) : mulPG (k, 0) a = mulPG a (k, 0) := by
  simp only [mulPG, zx_zero_left, zx_zero_right, Nat.cast_zero, mul_zero, add_zero, zero_add,
    Prod.mk.injEq, and_true]
  ring

theorem comm_rule (p q : V n) :
    mulPG (0, p) (0, q) = mulPG ((2 : ZMod 4) * ((omega p q).val : ZMod 4), 0) (mulPG (0, q) (0, p)) := by
  simp only [mulPG, zx_zero_left, Nat.cast_zero, mul_zero, add_zero, zero_add, Prod.mk.injEq]
  refine ⟨?_, add_comm _ _⟩
  rw [two_mul_zx, two_mul_zx, ← dbl_eq_two_mul_val, ← dbl_add]
  congr 1
  unfold omega
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize p.1 i = a; generalize p.2 i = b; generalize q.1 i = c; generalize q.2 i = d
  revert a b c d; decide

theorem canon_sq (p : V n) : mulPG (canon p) (canon p) = (0, 0) := by
  simp only [mulPG, canon, zx_self, Prod.mk.injEq]
  refine ⟨?_, add_self_V p⟩
  have : (4 : ZMod 4) = 0 := rfl
  linear_combination (ycount p : ZMod 4) * this

/-- A line: three distinct non-zero labels with zero sum that commute. -/
structure IsLine (a b c : V n) : Prop where
  ne_ab : a ≠ b
  ne_ac : a ≠ c
  ne_bc : b ≠ c
  nz_a : a ≠ 0
  nz_b : b ≠ 0
  nz_c : c ≠ 0
  sum_zero : a + b + c = 0
  comm : omega a b = 0

/-- Sign of the ordered triple: `P(a)P(b)P(c) = (2e, 0)`.
Explicit: `k = y(a)+y(b)+y(c) + 2(z_a·x_b + (z_a+z_b)·x_c)`, `e = k/2`. -/
def signK (a b c : V n) : ZMod 4 :=
  (mulPG (mulPG (canon a) (canon b)) (canon c)).1

def sign (a b c : V n) : F := if signK a b c = 2 then 1 else 0

/-- The explicit formula for `signK` (00_conventions). -/
theorem signK_eq (a b c : V n) :
    signK a b c = ((ycount a + ycount b + ycount c : ℕ) : ZMod 4)
      + dbl (∑ i, (a.2 i * b.1 i + (a.2 i + b.2 i) * c.1 i)) := by
  simp only [signK, mulPG, canon, two_mul_zx, Nat.cast_add, Finset.sum_add_distrib, dbl_add,
    Prod.snd_add, Pi.add_apply]
  ring

theorem third_eq {a b c : V n} (h : a + b + c = 0) : c = a + b := by
  have : c = -(a + b) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  rw [this, neg_eq_iff_add_eq_zero, add_self_V]

theorem omega_comm (p q : V n) : omega p q = omega q p := by
  unfold omega
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem qplus_add (p q : V n) : qplus (p + q) = qplus p + qplus q + omega p q := by
  unfold qplus omega
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

/-- reduction `ZMod 4 → ZMod 2` -/
def red : ZMod 4 →+* F := ZMod.castHom (by norm_num : 2 ∣ 4) F

theorem red_dbl (a : F) : red (dbl a) = 0 := by
  revert a; decide

theorem eq_zero_or_two_of_red {k : ZMod 4} (h : red k = 0) : k = 0 ∨ k = 2 := by
  revert k h; decide

theorem signK_even {a b c : V n} (h : IsLine a b c) : signK a b c = 0 ∨ signK a b c = 2 := by
  apply eq_zero_or_two_of_red
  rw [signK_eq, map_add, red_dbl, add_zero, map_natCast, Nat.cast_add, Nat.cast_add,
    ycount_cast, ycount_cast, ycount_cast, third_eq h.sum_zero, qplus_add, h.comm]
  generalize qplus a = x; generalize qplus b = y
  revert x y; decide

/-- the sign is the halved phase: `signK = 2·sign` on lines -/
theorem signK_eq_dbl_sign {a b c : V n} (h : IsLine a b c) : signK a b c = dbl (sign a b c) := by
  unfold sign
  rcases signK_even h with h0 | h2
  · simp only [h0]; decide
  · simp only [h2]; decide

theorem IsLine.swap12 {a b c : V n} (h : IsLine a b c) : IsLine b a c :=
  { ne_ab := h.ne_ab.symm, ne_ac := h.ne_bc, ne_bc := h.ne_ac, nz_a := h.nz_b, nz_b := h.nz_a,
    nz_c := h.nz_c, sum_zero := by rw [add_comm b a]; exact h.sum_zero,
    comm := by rw [omega_comm]; exact h.comm }

theorem omega_add_right (p q r : V n) : omega p (q + r) = omega p q + omega p r := by
  unfold omega
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

theorem omega_self (p : V n) : omega p p = 0 := by
  unfold omega
  refine Finset.sum_eq_zero fun i _ => ?_
  generalize p.1 i = a; generalize p.2 i = b
  revert a b; decide

theorem IsLine.swap23 {a b c : V n} (h : IsLine a b c) : IsLine a c b :=
  { ne_ab := h.ne_ac, ne_ac := h.ne_ab, ne_bc := h.ne_bc.symm, nz_a := h.nz_a, nz_b := h.nz_c,
    nz_c := h.nz_b, sum_zero := by rw [add_assoc, add_comm c b, ← add_assoc]; exact h.sum_zero,
    comm := by rw [third_eq h.sum_zero, omega_add_right, omega_self, h.comm, add_zero] }

theorem signK_swap12 {a b c : V n} (h : IsLine a b c) : signK a b c = signK b a c := by
  rw [signK_eq, signK_eq]
  have hc := h.comm
  have e : (ycount a + ycount b + ycount c : ℕ) = ycount b + ycount a + ycount c := by ring
  rw [e]
  congr 1
  have key : ∑ i, (a.2 i * b.1 i + (a.2 i + b.2 i) * c.1 i)
      = (∑ i, (b.2 i * a.1 i + (b.2 i + a.2 i) * c.1 i)) + omega a b := by
    unfold omega
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    generalize a.1 i = x1; generalize a.2 i = x2; generalize b.1 i = y1; generalize b.2 i = y2
    generalize c.1 i = z1
    revert x1 x2 y1 y2 z1; decide
  rw [key, hc, add_zero]

theorem signK_swap23 {a b c : V n} (h : IsLine a b c) : signK a b c = signK a c b := by
  rw [signK_eq, signK_eq]
  have hbc : omega b c = 0 := by
    rw [third_eq h.sum_zero, omega_add_right, omega_self, omega_comm, h.comm, add_zero]
  have e : (ycount a + ycount b + ycount c : ℕ) = ycount a + ycount c + ycount b := by ring
  rw [e]
  congr 1
  have key : ∑ i, (a.2 i * b.1 i + (a.2 i + b.2 i) * c.1 i)
      = (∑ i, (a.2 i * c.1 i + (a.2 i + c.2 i) * b.1 i)) + omega b c := by
    unfold omega
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    generalize a.2 i = x2; generalize b.1 i = y1; generalize b.2 i = y2
    generalize c.1 i = z1; generalize c.2 i = z2
    revert x2 y1 y2 z1 z2; decide
  rw [key, hbc, add_zero]

theorem sign_symm {a b c : V n} (h : IsLine a b c) : sign a b c = sign b a c ∧ sign a b c = sign a c b := by
  -- order independence (the operators commute)
  unfold sign
  exact ⟨by rw [signK_swap12 h], by rw [signK_swap23 h]⟩

end PauliCtx
