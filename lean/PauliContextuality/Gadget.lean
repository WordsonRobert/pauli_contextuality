/-
Gadget.lean — blueprint HARD-7, HARD-8, HARD-9: the value identities of the construction Φ.

For an E3 system S (equations E = (v₀, v₁, v₂), right-hand sides b_E) the configuration Φ has
  * copies c_{v,r} (v a variable, r = 1..4), shared between equations;
  * for each equation 21 private points: the aux points u₁..u₉ and the 12 points of two odd paths.
The local lines of E (indices K : Fin 20) are
  * K = 0..9 : the chain ℓ₁..ℓ₁₀  (ℓ₁ = {s₁,s₂,u₁}, ℓ_k = {u_{k−1}, s_{k+1}, u_k}, ℓ₁₀ = {u₉, s₁₁, s₁₂});
  * K = 10..14, 15..19 : rows 2, 3 and the three columns of path 1 and path 2 (column 3 has sign 1),
with s_{3(r−1)+i+1} = c_{v_i, r}. `Φ_ind` uses the chain and, for b_E = 1, both paths; `Φ_sub` drops
ℓ₁₀ of the negative equations and uses path 1 only.

  * `local_lower`, `local_upper` (HARD-7 + HARD-8): the minimum over the private points of E of its
      violated lines is [Y_E ≠ b_E] + b_E (ind) resp. [Y_E ≠ b_E] (sub), Y_E = sum of E's 12 copies.
  * `deg_phi` (HARD-9): **deg Φ_ind = OPT(S) + |b|** and **deg Φ_sub = OPT(S)**.

The signs are those of the Pauli realisation (Realize.lean): chain lines 0, and in each path only
column 3 is odd. HARD-7 needs only that each path closes an odd cycle with ℓ₁₀.
-/
import PauliContextuality.Hardness

namespace PauliCtx.Hardness

open Config

/-! ### the local tables -/

/-- private points of local line `K` (0..8 = u₁..u₉, 9+6t.. = path t) -/
def privPart : Fin 20 → Finset (Fin 21) :=
  ![{0}, {0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 7}, {7, 8}, {8}, {9, 10, 11},
    {12, 13, 14}, {9, 12}, {10, 13}, {8, 11, 14}, {15, 16, 17}, {18, 19, 20}, {15, 18}, {16, 19},
    {8, 17, 20}]

/-- copy points of local line `K`, as (position i in E, copy index r) -/
def cpTab : Fin 20 → Finset (Fin 3 × Fin 4) :=
  ![{(0, 0), (1, 0)}, {(2, 0)}, {(0, 1)}, {(1, 1)}, {(2, 1)}, {(0, 2)}, {(1, 2)}, {(2, 2)}, {(0, 3)},
    {(1, 3), (2, 3)}, ∅, ∅, {(1, 3)}, {(2, 3)}, ∅, ∅, ∅, {(1, 3)}, {(2, 3)}, ∅]

/-- signs: column 3 of each path is odd (these are the Pauli signs of the template, see Realize.lean) -/
def sgnT (K : Fin 20) : F := if K = 14 ∨ K = 19 then 1 else 0

/-- which local lines are present (`ind` = Φ_ind, otherwise Φ_sub) -/
def present (ind : Bool) (b : F) (K : Fin 20) : Bool :=
  if K.val < 9 then true
  else if K.val = 9 then (ind || decide (b = 0))
  else if K.val < 15 then decide (b = 1)
  else (ind && decide (b = 1))

def presentSet (ind : Bool) (b : F) : Finset (Fin 20) := Finset.univ.filter (fun K => present ind b K = true)

/-- the parity of local line `K` under copy values `c` and private values `y` -/
def linesum (K : Fin 20) (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) : F :=
  (∑ x ∈ cpTab K, c x) + (∑ i ∈ privPart K, y i) + sgnT K

/-- number of violated lines of `T` -/
def countV (T : Finset (Fin 20)) (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) : ℕ :=
  (T.filter (fun K => linesum K c y ≠ 0)).card

/-- the local cost of one equation -/
def cost (ind : Bool) (b : F) (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) : ℕ :=
  countV (presentSet ind b) c y

/-- the local minimum -/
def LB (ind : Bool) (b Y : F) : ℕ := (if Y ≠ b then 1 else 0) + (if ind = true ∧ b = 1 then 1 else 0)

theorem Fc (x : F) : x = 0 ∨ x = 1 := by revert x; decide

/-! ### parity of groups of local lines -/

theorem F_sum_ite_mem {ι κ : Type} [Fintype κ] [DecidableEq κ] (T : Finset ι) (A : ι → Finset κ)
    (f : κ → F) :
    ∑ K ∈ T, ∑ x ∈ A K, f x =
      ∑ x ∈ Finset.univ.filter (fun x => (T.filter (fun K => x ∈ A K)).card % 2 = 1), f x := by
  have h1 : ∀ K ∈ T, ∑ x ∈ A K, f x = ∑ x, if x ∈ A K then f x else 0 := by
    intro K _; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : ((T.filter (fun K => x ∈ A K)).card : F) =
      (((T.filter (fun K => x ∈ A K)).card % 2 : ℕ) : F) := by
    rw [ZMod.natCast_mod]
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one (T.filter (fun K => x ∈ A K)).card with h | h <;> simp [h]

theorem countV_parity (T : Finset (Fin 20)) (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    (countV T c y : F) = ∑ K ∈ T, linesum K c y := by
  unfold countV
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  generalize linesum K c y = x; revert x; decide

theorem countV_ge (T : Finset (Fin 20)) (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    (if ∑ K ∈ T, linesum K c y ≠ 0 then 1 else 0) ≤ countV T c y := by
  split_ifs with h
  · rw [← countV_parity] at h
    rcases Nat.eq_zero_or_pos (countV T c y) with h0 | h0
    · rw [h0, Nat.cast_zero] at h; exact absurd rfl h
    · exact h0
  · exact Nat.zero_le _

/-- the groups: chain ℓ₁..ℓ₉, ℓ₁₀, path 1, path 2 -/
def G9 : Finset (Fin 20) := Finset.univ.filter (fun K => K.val < 9)
def G10 : Finset (Fin 20) := {9}
def Gp1 : Finset (Fin 20) := Finset.univ.filter (fun K => 10 ≤ K.val ∧ K.val < 15)
def Gp2 : Finset (Fin 20) := Finset.univ.filter (fun K => 15 ≤ K.val)

theorem sum_linesum (T : Finset (Fin 20)) (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    ∑ K ∈ T, linesum K c y =
      (∑ x ∈ Finset.univ.filter (fun x => (T.filter (fun K => x ∈ cpTab K)).card % 2 = 1), c x) +
      (∑ i ∈ Finset.univ.filter (fun i => (T.filter (fun K => i ∈ privPart K)).card % 2 = 1), y i) +
      ∑ K ∈ T, sgnT K := by
  unfold linesum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, F_sum_ite_mem, F_sum_ite_mem]

theorem odd_cp_G9 : Finset.univ.filter (fun x => (G9.filter (fun K => x ∈ cpTab K)).card % 2 = 1) =
    Finset.univ.filter (fun x : Fin 3 × Fin 4 => x ≠ (1, 3) ∧ x ≠ (2, 3)) := by decide
theorem odd_pv_G9 : Finset.univ.filter (fun i => (G9.filter (fun K => i ∈ privPart K)).card % 2 = 1) =
    {8} := by decide
theorem sgn_G9 : ∑ K ∈ G9, sgnT K = 0 := by decide

theorem odd_cp_G10 : Finset.univ.filter (fun x => (G10.filter (fun K => x ∈ cpTab K)).card % 2 = 1) =
    {(1, 3), (2, 3)} := by decide
theorem odd_pv_G10 : Finset.univ.filter (fun i => (G10.filter (fun K => i ∈ privPart K)).card % 2 = 1) =
    {8} := by decide
theorem sgn_G10 : ∑ K ∈ G10, sgnT K = 0 := by decide

theorem odd_cp_Gp1 : Finset.univ.filter (fun x => (Gp1.filter (fun K => x ∈ cpTab K)).card % 2 = 1) =
    {(1, 3), (2, 3)} := by decide
theorem odd_pv_Gp1 : Finset.univ.filter (fun i => (Gp1.filter (fun K => i ∈ privPart K)).card % 2 = 1) =
    {8} := by decide
theorem sgn_Gp1 : ∑ K ∈ Gp1, sgnT K = 1 := by decide

theorem odd_cp_Gp2 : Finset.univ.filter (fun x => (Gp2.filter (fun K => x ∈ cpTab K)).card % 2 = 1) =
    {(1, 3), (2, 3)} := by decide
theorem odd_pv_Gp2 : Finset.univ.filter (fun i => (Gp2.filter (fun K => i ∈ privPart K)).card % 2 = 1) =
    {8} := by decide
theorem sgn_Gp2 : ∑ K ∈ Gp2, sgnT K = 1 := by decide

/-- the total of all copies -/
def Ysum (c : Fin 3 × Fin 4 → F) : F := ∑ x, c x

theorem sum_off (c : Fin 3 × Fin 4 → F) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin 3 × Fin 4 => x ≠ (1, 3) ∧ x ≠ (2, 3)), c x =
      Ysum c + c (1, 3) + c (2, 3) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : Fin 3 × Fin 4 => x ≠ (1, 3) ∧ x ≠ (2, 3)) c
  have hnot : Finset.univ.filter (fun x : Fin 3 × Fin 4 => ¬ (x ≠ (1, 3) ∧ x ≠ (2, 3))) = {(1, 3), (2, 3)} := by
    decide
  rw [hnot, Finset.sum_pair (by decide)] at hsplit
  unfold Ysum; rw [← hsplit]
  have h1 := add_self_F (c (1, 3)); have h2 := add_self_F (c (2, 3))
  linear_combination -h1 - h2

/-- HARD-1 for the chain ℓ₁..ℓ₉ (lower bound): at least [Y + τ ≠ 0] violated, τ = s₁₁ + s₁₂ + u₉ -/
theorem chain_lb (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    (if Ysum c + (c (1, 3) + c (2, 3) + y 8) ≠ 0 then 1 else 0) ≤ countV G9 c y := by
  have h := countV_ge G9 c y
  rw [sum_linesum, odd_cp_G9, odd_pv_G9, sgn_G9, sum_off, Finset.sum_singleton] at h
  convert h using 2; ring

/-- ℓ₁₀ is violated iff τ ≠ 0 -/
theorem l10_lb (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    (if c (1, 3) + c (2, 3) + y 8 ≠ 0 then 1 else 0) ≤ countV G10 c y := by
  have h := countV_ge G10 c y
  rw [sum_linesum, odd_cp_G10, odd_pv_G10, sgn_G10, Finset.sum_pair (by decide),
    Finset.sum_singleton, add_zero] at h
  exact h

/-- **HARD-7 (odd path).** Each path has at least [τ ≠ 1] violated lines. -/
theorem path1_lb (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    (if c (1, 3) + c (2, 3) + y 8 + 1 ≠ 0 then 1 else 0) ≤ countV Gp1 c y := by
  have h := countV_ge Gp1 c y
  rw [sum_linesum, odd_cp_Gp1, odd_pv_Gp1, sgn_Gp1, Finset.sum_pair (by decide),
    Finset.sum_singleton] at h
  exact h

theorem path2_lb (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    (if c (1, 3) + c (2, 3) + y 8 + 1 ≠ 0 then 1 else 0) ≤ countV Gp2 c y := by
  have h := countV_ge Gp2 c y
  rw [sum_linesum, odd_cp_Gp2, odd_pv_Gp2, sgn_Gp2, Finset.sum_pair (by decide),
    Finset.sum_singleton] at h
  exact h

theorem countV_union {T₁ T₂ : Finset (Fin 20)} (h : Disjoint T₁ T₂) (c : Fin 3 × Fin 4 → F)
    (y : Fin 21 → F) : countV (T₁ ∪ T₂) c y = countV T₁ c y + countV T₂ c y := by
  unfold countV
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem pres_ind1 : presentSet true 1 = ((G9 ∪ G10) ∪ Gp1) ∪ Gp2 := by decide
theorem pres_ind0 : presentSet true 0 = G9 ∪ G10 := by decide
theorem pres_sub0 : presentSet false 0 = G9 ∪ G10 := by decide
theorem pres_sub1 : presentSet false 1 = G9 ∪ Gp1 := by decide

theorem F_ne_iff (x y : F) : (if x + y ≠ 0 then 1 else 0 : ℕ) = if y ≠ x then 1 else 0 := by
  revert x y; decide

/-- **HARD-8 (lower bound).** -/
theorem local_lower (ind : Bool) (b : F) (c : Fin 3 × Fin 4 → F) (y : Fin 21 → F) :
    LB ind b (Ysum c) ≤ cost ind b c y := by
  have hch := chain_lb c y
  have h10 := l10_lb c y
  have hp1 := path1_lb c y
  have hp2 := path2_lb c y
  set τ := c (1, 3) + c (2, 3) + y 8
  rw [F_ne_iff] at hch
  unfold cost LB
  rcases Fc b with rfl | rfl
  · -- b = 0
    have hpres : presentSet ind 0 = G9 ∪ G10 := by cases ind <;> decide
    rw [hpres, countV_union (by decide)]
    have := (one_equation_b0 (Ysum c)).1 τ
    simp only [show ¬ (ind = true ∧ (0 : F) = 1) from fun h => absurd h.2 (by decide), if_false, add_zero]
    have e : (if Ysum c ≠ 0 then 1 else 0) = (if Ysum c ≠ 0 then 1 else 0 : ℕ) := rfl
    omega
  · cases ind
    · rw [pres_sub1, countV_union (by decide)]
      have := (one_equation_sub (Ysum c)).1 τ
      have e : (if τ + 1 ≠ 0 then 1 else 0 : ℕ) = if τ ≠ 1 then 1 else 0 := by
        generalize τ = t; revert t; decide
      rw [e] at hp1
      simp only [Bool.false_eq_true, false_and, if_false, add_zero]
      omega
    · rw [pres_ind1, countV_union (by decide), countV_union (by decide), countV_union (by decide)]
      have := (one_equation_ind (Ysum c)).1 τ
      have e : (if τ + 1 ≠ 0 then 1 else 0 : ℕ) = if τ ≠ 1 then 1 else 0 := by
        generalize τ = t; revert t; decide
      rw [e] at hp1 hp2
      simp only [and_self, if_true]
      omega

/-! ### the explicit optimal private assignment -/

/-- the position of a copy in the chain: `s_{j+1} = (j mod 3, j div 3)` -/
def rk (x : Fin 3 × Fin 4) : ℕ := x.2.val * 3 + x.1.val

/-- coefficients of the optimal private values: greedy prefix sums for u₁..u₈,
u₉ = b + s₁₁ + s₁₂, and the paths filled in to satisfy all their lines -/
def ycoef (i : Fin 21) (x : Fin 3 × Fin 4) : F :=
  (if i.val < 8 ∧ rk x < i.val + 2 then 1 else 0) +
  (if (i.val = 8 ∨ i.val = 14 ∨ i.val = 20) ∧ (x = (1, 3) ∨ x = (2, 3)) then 1 else 0) +
  (if (i.val = 12 ∨ i.val = 18) ∧ x = (1, 3) then 1 else 0) +
  (if (i.val = 13 ∨ i.val = 19) ∧ x = (2, 3) then 1 else 0)

def ycst (i : Fin 21) : F := if i.val = 8 ∨ i.val = 14 ∨ i.val = 20 then 1 else 0

/-- the constant shift of p₃₃ (column 3 is odd) -/
def yone (i : Fin 21) : F := if i.val = 14 ∨ i.val = 20 then 1 else 0

/-- the optimal private assignment of one equation -/
def yopt (b : F) (c : Fin 3 × Fin 4 → F) (i : Fin 21) : F := (∑ x, ycoef i x * c x) + ycst i * b + yone i

/-- the coefficient of `c x` in the parity of line `K` under `yopt` -/
def Acoef (K : Fin 20) (x : Fin 3 × Fin 4) : F :=
  (if x ∈ cpTab K then 1 else 0) + ∑ i ∈ privPart K, ycoef i x

/-- the constant part of the parity of line `K` under `yopt` -/
def tvc (K : Fin 20) (b : F) : F := if K = 8 ∨ K = 9 then b else if K = 11 ∨ K = 16 then b + 1 else 0

theorem linesum_yopt (K : Fin 20) (b : F) (c : Fin 3 × Fin 4 → F) :
    linesum K c (yopt b c) =
      (∑ x, Acoef K x * c x) + ((∑ i ∈ privPart K, ycst i) * b + ∑ i ∈ privPart K, yone i + sgnT K) := by
  unfold linesum yopt Acoef
  have h1 : ∑ x ∈ cpTab K, c x = ∑ x, (if x ∈ cpTab K then 1 else 0) * c x := by
    symm
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1]
  simp only [Finset.sum_add_distrib, add_mul]
  rw [Finset.sum_comm (s := privPart K) (t := Finset.univ)]
  simp only [Finset.sum_mul]
  ring

theorem Acoef_val : ∀ K x, Acoef K x = if K = 8 then 1 else 0 := by decide

theorem const_val : ∀ (K : Fin 20) (b : F),
    (∑ i ∈ privPart K, ycst i) * b + ∑ i ∈ privPart K, yone i + sgnT K = tvc K b := by decide

theorem linesum_yopt' (K : Fin 20) (b : F) (c : Fin 3 × Fin 4 → F) :
    linesum K c (yopt b c) = (if K = 8 then Ysum c else 0) + tvc K b := by
  rw [linesum_yopt, const_val]
  congr 1
  simp only [Acoef_val]
  split_ifs <;> simp [Ysum]

theorem final_tab : ∀ (ind : Bool) (b Y : F),
    ((presentSet ind b).filter (fun K => (if K = 8 then Y else 0) + tvc K b ≠ 0)).card = LB ind b Y := by
  decide

/-- **HARD-8 (upper bound).** -/
theorem local_upper (ind : Bool) (b : F) (c : Fin 3 × Fin 4 → F) :
    cost ind b c (yopt b c) = LB ind b (Ysum c) := by
  unfold cost countV
  simp only [linesum_yopt']
  exact final_tab ind b (Ysum c)

/-! ### the configuration Φ -/

variable {ν ε : Type} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε]

/-- points: copies `(v, r)` and private points `(E, i)` -/
abbrev Pt (ν ε : Type) := (ν × Fin 4) ⊕ (ε × Fin 21)

/-- the local line `K` of equation `E` -/
def lineOf (S : E3 ν ε) (E : ε) (K : Fin 20) : Finset (Pt ν ε) :=
  (cpTab K).image (fun x => Sum.inl (S.var E x.1, x.2)) ∪ (privPart K).image (fun i => Sum.inr (E, i))

theorem cp_inj (S : E3 ν ε) (E : ε) :
    Function.Injective (fun x : Fin 3 × Fin 4 => (Sum.inl (S.var E x.1, x.2) : Pt ν ε)) := by
  intro x x' h
  simp only [Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (S.inj E h.1) h.2

theorem pv_inj (E : ε) : Function.Injective (fun i : Fin 21 => (Sum.inr (E, i) : Pt ν ε)) := by
  intro i i' h; simpa using h

theorem disj_line (S : E3 ν ε) (E : ε) (K : Fin 20) :
    Disjoint ((cpTab K).image (fun x => (Sum.inl (S.var E x.1, x.2) : Pt ν ε)))
      ((privPart K).image (fun i => (Sum.inr (E, i) : Pt ν ε))) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hq
  exact Sum.inr_ne_inl hi

theorem card_tab : ∀ K : Fin 20, (cpTab K).card + (privPart K).card = 3 := by decide

theorem card_lineOf (S : E3 ν ε) (E : ε) (K : Fin 20) : (lineOf S E K).card = 3 := by
  unfold lineOf
  rw [Finset.card_union_of_disjoint (disj_line S E K), Finset.card_image_of_injective _ (cp_inj S E),
    Finset.card_image_of_injective _ (pv_inj E), card_tab]

theorem privPart_nonempty : ∀ K : Fin 20, (privPart K).Nonempty := by decide

theorem privPart_inj : ∀ K K' : Fin 20, privPart K = privPart K' → K = K' := by decide

theorem mem_lineOf_inr (S : E3 ν ε) {E E' : ε} {K : Fin 20} {i : Fin 21} :
    (Sum.inr (E', i) : Pt ν ε) ∈ lineOf S E K ↔ E' = E ∧ i ∈ privPart K := by
  unfold lineOf
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨x, -, hx⟩ | ⟨j, hj, hji⟩)
    · exact absurd hx Sum.inl_ne_inr
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at hji
      exact ⟨hji.1.symm, hji.2 ▸ hj⟩
  · rintro ⟨rfl, hi⟩; exact Or.inr ⟨i, hi, rfl⟩

theorem lineOf_inj (S : E3 ν ε) {E E' : ε} {K K' : Fin 20} (h : lineOf S E K = lineOf S E' K') :
    E = E' ∧ K = K' := by
  obtain ⟨i, hi⟩ := privPart_nonempty K
  have h1 : (Sum.inr (E, i) : Pt ν ε) ∈ lineOf S E' K' := h ▸ (mem_lineOf_inr S).2 ⟨rfl, hi⟩
  have hE : E = E' := ((mem_lineOf_inr S).1 h1).1
  subst hE
  refine ⟨rfl, privPart_inj K K' ?_⟩
  ext j
  constructor
  · intro hj; exact ((mem_lineOf_inr S).1 (h ▸ (mem_lineOf_inr S).2 ⟨rfl, hj⟩)).2
  · intro hj; exact ((mem_lineOf_inr S).1 (h.symm ▸ (mem_lineOf_inr S).2 ⟨rfl, hj⟩)).2

open Classical in
/-- the configuration Φ_ind (`ind = true`) or Φ_sub (`ind = false`) -/
noncomputable def Phi (S : E3 ν ε) (ind : Bool) : Config (Pt ν ε) where
  lines := Finset.univ.biUnion (fun E => (presentSet ind (S.rhs E)).image (lineOf S E))
  sign := fun l => if ∃ E K, lineOf S E K = l ∧ sgnT K = 1 then 1 else 0
  three := by
    intro l hl
    obtain ⟨E, -, hE⟩ := Finset.mem_biUnion.1 hl
    obtain ⟨K, -, rfl⟩ := Finset.mem_image.1 hE
    exact card_lineOf S E K

theorem Phi_sign (S : E3 ν ε) (ind : Bool) (E : ε) (K : Fin 20) :
    (Phi S ind).sign (lineOf S E K) = sgnT K := by
  classical
  show (if ∃ E' K', lineOf S E' K' = lineOf S E K ∧ sgnT K' = 1 then 1 else 0) = sgnT K
  by_cases hK : sgnT K = 1
  · rw [if_pos ⟨E, K, rfl, hK⟩, hK]
  · rw [if_neg]
    · rcases Fc (sgnT K) with h | h
      · exact h.symm
      · exact absurd h hK
    · rintro ⟨E', K', h, h1⟩
      obtain ⟨-, rfl⟩ := lineOf_inj S h
      exact hK h1

/-- local copy values and private values of an assignment -/
def cE (S : E3 ν ε) (s : Pt ν ε → F) (E : ε) : Fin 3 × Fin 4 → F := fun x => s (Sum.inl (S.var E x.1, x.2))
def yE (s : Pt ν ε → F) (E : ε) : Fin 21 → F := fun i => s (Sum.inr (E, i))

theorem sum_lineOf (S : E3 ν ε) (s : Pt ν ε → F) (E : ε) (K : Fin 20) :
    ∑ p ∈ lineOf S E K, s p = (∑ x ∈ cpTab K, cE S s E x) + ∑ i ∈ privPart K, yE s E i := by
  unfold lineOf
  rw [Finset.sum_union (disj_line S E K), Finset.sum_image (fun x _ y _ h => cp_inj S E h),
    Finset.sum_image (fun x _ y _ h => pv_inj E h)]
  rfl

theorem violated_lineOf (S : E3 ν ε) (ind : Bool) (s : Pt ν ε → F) (E : ε) (K : Fin 20) :
    (Phi S ind).Violated s (lineOf S E K) ↔ linesum K (cE S s E) (yE s E) ≠ 0 := by
  unfold Violated linesum
  rw [sum_lineOf, Phi_sign]

/-- the number of violated lines is the sum of the local costs -/
theorem card_violated_Phi (S : E3 ν ε) (ind : Bool) (s : Pt ν ε → F) :
    ((Phi S ind).violated s).card = ∑ E, cost ind (S.rhs E) (cE S s E) (yE s E) := by
  classical
  have hv : (Phi S ind).violated s = Finset.univ.biUnion (fun E =>
      ((presentSet ind (S.rhs E)).filter (fun K => linesum K (cE S s E) (yE s E) ≠ 0)).image
        (lineOf S E)) := by
    ext l
    simp only [violated, Phi, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨E, K, hK, rfl⟩, hv⟩
      exact ⟨E, K, ⟨hK, (violated_lineOf S ind s E K).1 hv⟩, rfl⟩
    · rintro ⟨E, K, ⟨hK, hv⟩, rfl⟩
      exact ⟨⟨E, K, hK, rfl⟩, (violated_lineOf S ind s E K).2 hv⟩
  rw [hv, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun E _ => ?_
    rw [Finset.card_image_of_injective _ (fun K K' h => (lineOf_inj S h).2)]
    rfl
  · intro E _ E' _ hEE'
    rw [Function.onFun, Finset.disjoint_left]
    intro l h1 h2
    obtain ⟨K, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨K', -, hK'⟩ := Finset.mem_image.1 h2
    exact hEE' (lineOf_inj S hK').1.symm

/-! ### HARD-9 -/

/-- `|b|`: the number of negative equations -/
def nNeg (S : E3 ν ε) : ℕ := (Finset.univ.filter (fun E => S.rhs E = 1)).card

/-- the variable values carried by the copies: z_v = Σ_r s(c_{v,r}) -/
def zOf (s : Pt ν ε → F) (v : ν) : F := ∑ r : Fin 4, s (Sum.inl (v, r))

theorem Ysum_cE (S : E3 ν ε) (s : Pt ν ε → F) (E : ε) :
    Ysum (cE S s E) = ∑ v ∈ S.toSys.eqs E, zOf s v := by
  rw [sum_three]
  unfold Ysum cE zOf
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]

theorem viol_eq_sum (S : E3 ν ε) (x : ν → F) :
    S.toSys.viol x = ∑ E, (if (∑ v ∈ S.toSys.eqs E, x v) ≠ S.rhs E then 1 else 0) := by
  unfold GSys.viol
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun E _ => ?_
  have : S.toSys.rhs E = S.rhs E := rfl
  rw [this]
  generalize (∑ v ∈ S.toSys.eqs E, x v) = a; generalize S.rhs E = b
  revert a b; decide

theorem sum_LB (S : E3 ν ε) (ind : Bool) (x : ν → F) :
    ∑ E, LB ind (S.rhs E) (∑ v ∈ S.toSys.eqs E, x v) =
      S.toSys.viol x + (if ind then nNeg S else 0) := by
  unfold LB
  rw [Finset.sum_add_distrib, ← viol_eq_sum]
  congr 1
  cases ind
  · simp
  · simp only [true_and, if_true]
    rw [nNeg, Finset.card_filter]

/-- **HARD-9.** deg Φ_ind = OPT + |b| and deg Φ_sub = OPT. -/
theorem deg_phi (S : E3 ν ε) (ind : Bool) :
    (Phi S ind).deg = S.toSys.opt + (if ind then nNeg S else 0) := by
  classical
  apply le_antisymm
  · -- upper bound: an optimal x on the first copies, optimal private points
    obtain ⟨x, hx⟩ := S.toSys.exists_opt
    let sc : ν × Fin 4 → F := fun p => if p.2 = 0 then x p.1 else 0
    let s : Pt ν ε → F := Sum.elim sc
      (fun p => yopt (S.rhs p.1) (fun y => sc (S.var p.1 y.1, y.2)) p.2)
    have hz : zOf s = x := by
      funext v; simp [zOf, s, sc, Fin.sum_univ_four]
    have hcost : ∀ E, cost ind (S.rhs E) (cE S s E) (yE s E) =
        LB ind (S.rhs E) (∑ v ∈ S.toSys.eqs E, x v) := by
      intro E
      have : yE s E = yopt (S.rhs E) (cE S s E) := rfl
      rw [this, local_upper, Ysum_cE, hz]
    have := (Phi S ind).deg_le s
    rw [card_violated_Phi, Finset.sum_congr rfl (fun E _ => hcost E), sum_LB, hx] at this
    exact this
  · -- lower bound
    obtain ⟨s, hs⟩ := (Phi S ind).exists_opt
    rw [← hs, card_violated_Phi]
    calc S.toSys.opt + (if ind then nNeg S else 0)
        ≤ S.toSys.viol (zOf s) + (if ind then nNeg S else 0) := by
          have := S.toSys.opt_le (zOf s); omega
      _ = ∑ E, LB ind (S.rhs E) (Ysum (cE S s E)) := by
          rw [← sum_LB]; refine Finset.sum_congr rfl fun E _ => ?_; rw [Ysum_cE]
      _ ≤ ∑ E, cost ind (S.rhs E) (cE S s E) (yE s E) :=
          Finset.sum_le_sum fun E _ => local_lower ind (S.rhs E) (cE S s E) (yE s E)

/-- **HARD-9 (induced variant).** deg Φ_ind = OPT + |b|. -/
theorem induced_degree (S : E3 ν ε) : (Phi S true).deg = S.toSys.opt + nNeg S := by
  simpa using deg_phi S true

/-- **HARD-9 (sub-configuration variant).** deg Φ_sub = OPT. -/
theorem sub_degree (S : E3 ν ε) : (Phi S false).deg = S.toSys.opt := by
  simpa using deg_phi S false

end PauliCtx.Hardness
