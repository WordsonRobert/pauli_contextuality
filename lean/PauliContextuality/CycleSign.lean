/-
CycleSign.lean — ALG-2 (cycle-sign lemma) of 01_algebra.md.

  * `prodPG_canon`        : the product of canonical elements of a word, in closed form.
  * `prod_canon_even`     : if every label occurs an even number of times, the canonical product is
                            `(2·inv(w), 0)`, `inv(w) = Σ_{r<t, w_t ≺ w_r} ω(w_r, w_t)`.
  * `prod_line`           : `P(a)P(b)P(c) = (2·e, 0)` for a line.
  * `cycle_parity_eq_inversions` (ALG-2): for lines ℓ_1..ℓ_k whose word has even multiplicities,
                            `Σ_j e(ℓ_j) = inv(w)`.
Proof idea (no bubble sort): `Φ(w) = Σ y(w_i) + 2(Σ_{i<j} z_{w_i}·x_{w_j} + inv w)` is invariant under
permutations of `w`, and `Φ(p p r) = Φ(r)`.
-/
import PauliContextuality.Cover

namespace PauliCtx

variable {n : ℕ}

/-- Product of a list of Pauli group elements. -/
def prodPG : List (PG n) → PG n
  | [] => (0, 0)
  | a :: as => mulPG a (prodPG as)

/-- `β(p,q) = z_p · x_q ∈ F` -/
def beta (p q : V n) : F := ∑ i, p.2 i * q.1 i

theorem beta_add_right (p q r : V n) : beta p (q + r) = beta p q + beta p r := by
  unfold beta; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Prod.fst_add, Pi.add_apply]; ring

@[simp] theorem beta_zero_right (p : V n) : beta p 0 = 0 := by simp [beta]

theorem beta_sum (p : V n) (l : List (V n)) : beta p l.sum = (l.map (beta p)).sum := by
  induction l with
  | nil => simp
  | cons q l ih => rw [List.sum_cons, beta_add_right, ih, List.map_cons, List.sum_cons]

theorem beta_swap (p q : V n) : beta p q = beta q p + omega p q := by
  unfold beta omega; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
  generalize p.1 i = a; generalize p.2 i = b; generalize q.1 i = c; generalize q.2 i = d
  revert a b c d; decide

theorem beta_self (p : V n) : beta p p = (ycount p : F) := by
  rw [ycount_cast]; unfold beta qplus; refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- `Σ_{i<j} β(w_i, w_j)` -/
def pairSum : List (V n) → F
  | [] => 0
  | p :: ps => (ps.map (beta p)).sum + pairSum ps

def ysum (w : List (V n)) : ZMod 4 := (w.map (fun p => (ycount p : ZMod 4))).sum

/-- The product of the canonical elements of a word. -/
theorem prodPG_canon (w : List (V n)) :
    prodPG (w.map canon) = (ysum w + dbl (pairSum w), w.sum) := by
  induction w with
  | nil => simp [prodPG, ysum, pairSum]
  | cons p w ih =>
    simp only [List.map_cons, prodPG, ih, mulPG, canon, ysum, pairSum, List.sum_cons, Prod.mk.injEq,
      and_true]
    rw [two_mul_natCast, zx_cast, ← beta, beta_sum, dbl_add]
    ring

/-- Inversion count of a word w.r.t. a total order, weighted by ω. -/
def invSign [LinearOrder (V n)] : List (V n) → F
  | [] => 0
  | p :: ps => ((ps.filter (fun q => q < p)).map (omega p)).sum + invSign ps

section Phi

variable [LinearOrder (V n)]

def Psi (w : List (V n)) : F := pairSum w + invSign w

def Phi (w : List (V n)) : ZMod 4 := ysum w + dbl (Psi w)

theorem Psi_cons (p : V n) (w : List (V n)) :
    Psi (p :: w) = (w.map (beta p)).sum + ((w.filter (fun q => q < p)).map (omega p)).sum + Psi w := by
  simp only [Psi, pairSum, invSign]; ring

theorem Psi_perm {w w' : List (V n)} (h : w.Perm w') : Psi w = Psi w' := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    rw [Psi_cons, Psi_cons, ih]
    congr 2
    · exact (List.Perm.map _ ‹_›).sum_eq
    · exact ((List.Perm.filter _ ‹_›).map _).sum_eq
  | swap x y l =>
    rw [Psi_cons, Psi_cons, Psi_cons, Psi_cons]
    have hb := beta_swap x y
    have h2 : ∀ t : F, t + t = 0 := add_self_F
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have hn : ¬ y < x := not_lt.2 hxy.le
      rw [List.filter_cons_of_pos (p := fun q => decide (q < y)) (by simpa using hxy),
        List.filter_cons_of_neg (p := fun q => decide (q < x)) (by simpa using hn)]
      simp only [List.map_cons, List.sum_cons]
      rw [hb, omega_comm y x]
      ring
    · subst hxy; rfl
    · have hn : ¬ x < y := not_lt.2 hxy.le
      rw [List.filter_cons_of_neg (p := fun q => decide (q < y)) (by simpa using hn),
        List.filter_cons_of_pos (p := fun q => decide (q < x)) (by simpa using hxy)]
      simp only [List.map_cons, List.sum_cons]
      rw [hb]
      linear_combination (-1 : F) * h2 (omega x y)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ysum_perm {w w' : List (V n)} (h : w.Perm w') : ysum w = ysum w' := (h.map _).sum_eq

theorem Phi_perm {w w' : List (V n)} (h : w.Perm w') : Phi w = Phi w' := by
  unfold Phi; rw [ysum_perm h, Psi_perm h]

theorem Phi_pp (p : V n) (r : List (V n)) : Phi (p :: p :: r) = Phi r := by
  unfold Phi
  have hP : Psi (p :: p :: r) = beta p p + Psi r := by
    rw [Psi_cons, Psi_cons, List.filter_cons_of_neg (by simp)]
    simp only [List.map_cons, List.sum_cons]
    generalize (r.map (beta p)).sum = A
    generalize ((r.filter (fun q => q < p)).map (omega p)).sum = B
    have h2 : ∀ t : F, t + t = 0 := add_self_F
    linear_combination h2 A + h2 B
  rw [hP, dbl_add, beta_self, ← two_mul_natCast]
  simp only [ysum, List.map_cons, List.sum_cons]
  have : (4 : ZMod 4) = 0 := rfl
  linear_combination (ycount p : ZMod 4) * this

theorem even_count_erase {w : List (V n)} {p : V n} (heven : ∀ q, Even (w.count q)) (hp : p ∈ w) :
    ∃ r : List (V n), w.Perm (p :: p :: r) ∧ r.length + 2 = w.length ∧ ∀ q, Even (r.count q) := by
  have h1 := List.perm_cons_erase hp
  have hp2 : p ∈ w.erase p := by
    have hc := heven p
    have hpos : 0 < w.count p := List.count_pos_iff.2 hp
    have : 0 < (w.erase p).count p := by
      rw [List.count_erase_self]
      obtain ⟨k, hk⟩ := hc
      omega
    exact List.count_pos_iff.1 this
  have h2 := List.perm_cons_erase hp2
  refine ⟨(w.erase p).erase p, h1.trans (h2.cons p), ?_, ?_⟩
  · have := h1.trans (h2.cons p)
    have hl := this.length_eq
    simp only [List.length_cons] at hl
    omega
  · intro q
    by_cases hq : q = p
    · subst hq
      rw [List.count_erase_self, List.count_erase_self]
      have hpos : 0 < w.count q := List.count_pos_iff.2 hp
      obtain ⟨k, hk⟩ := heven q
      exact ⟨k - 1, by omega⟩
    · rw [List.count_erase_of_ne hq, List.count_erase_of_ne hq]; exact heven q

theorem Phi_even : ∀ (m : ℕ) (w : List (V n)), w.length = m → (∀ q, Even (w.count q)) → Phi w = 0
  | m, [], _, _ => by simp [Phi, ysum, Psi, pairSum, invSign]
  | m, p :: w', hm, heven => by
    obtain ⟨r, hperm, hlen, hr⟩ := even_count_erase heven List.mem_cons_self
    rw [Phi_perm hperm, Phi_pp]
    exact Phi_even r.length r rfl hr
  termination_by m => m
  decreasing_by simp_all; omega

theorem sum_even : ∀ (m : ℕ) (w : List (V n)), w.length = m → (∀ q, Even (w.count q)) → w.sum = 0
  | m, [], _, _ => rfl
  | m, p :: w', hm, heven => by
    obtain ⟨r, hperm, hlen, hr⟩ := even_count_erase heven List.mem_cons_self
    rw [hperm.sum_eq, List.sum_cons, List.sum_cons, ← add_assoc, add_self_V, zero_add]
    exact sum_even r.length r rfl hr
  termination_by m => m
  decreasing_by simp_all; omega

theorem dbl_inj {a b : F} (h : dbl a = dbl b) : a = b := by
  revert a b; decide

/-- ALG-2 (word form). If the word contains every label an even number of times,
its canonical product is `(2·inv, 0)`. -/
theorem prod_canon_even (w : List (V n)) (heven : ∀ p, Even (w.count p)) :
    prodPG (w.map canon) = ((2 : ZMod 4) * ((invSign w).val : ZMod 4), 0) := by
  rw [prodPG_canon, sum_even w.length w rfl heven, ← dbl_eq_two_mul_val]
  congr 1
  have h := Phi_even w.length w rfl heven
  unfold Phi Psi at h
  rw [dbl_add] at h
  have hn : ∀ t : F, dbl t + dbl t = 0 := fun t => by rw [← dbl_add, add_self_F, dbl_zero]
  linear_combination h - hn (invSign w)

end Phi

/-! ### products over lines -/

theorem prodPG_append (l₁ l₂ : List (PG n)) : prodPG (l₁ ++ l₂) = mulPG (prodPG l₁) (prodPG l₂) := by
  induction l₁ with
  | nil => simp [prodPG, mulPG_one_left]
  | cons a l ih => simp only [List.cons_append, prodPG, ih, mulPG_assoc]

theorem prod_line {a b c : V n} (h : IsLine a b c) :
    prodPG ([a, b, c].map canon) = (dbl (sign a b c), 0) := by
  simp only [List.map_cons, List.map_nil, prodPG, mulPG_one_right]
  rw [← mulPG_assoc]
  show ((mulPG (mulPG (canon a) (canon b)) (canon c)).1, (mulPG (mulPG (canon a) (canon b)) (canon c)).2) = _
  rw [show (mulPG (mulPG (canon a) (canon b)) (canon c)).1 = signK a b c from rfl, signK_eq_dbl_sign h]
  congr 1
  simp only [mulPG, canon]
  exact h.sum_zero

/-- the word of a list of ordered triples -/
def tripleWord (L : List (V n × V n × V n)) : List (V n) := L.flatMap (fun t => [t.1, t.2.1, t.2.2])

theorem prod_lines (L : List (V n × V n × V n)) (hL : ∀ t ∈ L, IsLine t.1 t.2.1 t.2.2) :
    prodPG ((tripleWord L).map canon) = (dbl ((L.map (fun t => sign t.1 t.2.1 t.2.2)).sum), 0) := by
  induction L with
  | nil => simp [tripleWord, prodPG]
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih (fun s hs => hL s (List.mem_cons_of_mem _ hs))
    simp only [tripleWord, List.flatMap_cons, List.map_append] at ih' ⊢
    rw [prodPG_append, prod_line ht, ih']
    simp [mulPG, dbl_add]

/-- ALG-2 (cycle-sign lemma). Let ℓ_1, …, ℓ_k be lines (as ordered triples) whose word
`w = a₁b₁c₁ a₂b₂c₂ …` contains every label an even number of times (i.e. they form a cycle).
Then `Σ_j e(ℓ_j) = Σ_{r<t, w_t ≺ w_r} ω(w_r, w_t)`. -/
theorem cycle_parity_eq_inversions [LinearOrder (V n)] (L : List (V n × V n × V n))
    (hL : ∀ t ∈ L, IsLine t.1 t.2.1 t.2.2) (heven : ∀ p, Even ((tripleWord L).count p)) :
    (L.map (fun t => sign t.1 t.2.1 t.2.2)).sum = invSign (tripleWord L) := by
  have h1 := prod_lines L hL
  have h2 := prod_canon_even (tripleWord L) heven
  rw [h1, ← dbl_eq_two_mul_val] at h2
  exact dbl_inj (Prod.mk.inj h2).1

end PauliCtx
