/-
Game.lean — blueprint 11, GAME-1/2/3: the line/point linear-system game of a configuration.

The game G_C of a configuration C (Cleve–Mittal, line/point form):
  * the referee draws a uniformly random line ℓ for Alice and a uniformly random point p ∈ ℓ for Bob;
  * Alice answers an assignment of the points of ℓ satisfying the line equation Σ_{q∈ℓ} x_q = e(ℓ);
  * Bob answers one bit; they win iff Bob's bit equals Alice's bit for p.

A deterministic strategy is a pair (A, B): `A ℓ : α → F` (only its values on ℓ matter, and it must
satisfy ℓ) and `B : α → F`.  Its winning probability is
      winProb = (1/|L|) Σ_ℓ (1/3) #{p ∈ ℓ : A ℓ p = B p} = wins/(3|L|).
**Definition.** `classicalValue C` is the maximum of `winProb` over deterministic strategies.
Shared randomness (any finite mixture of deterministic strategies) does not help: `mixture_le`.

  * `bestWins_eq`     : max wins = 3|L| − deg C.
  * `classicalValue_eq` (GAME-1): ω_c(G_C) = 1 − deg C/(3|L|).
  * `classicalValue_ge` (GAME-2, universal): ω_c ≥ 5/6.
  * `W_value_le`, `W_value_tendsto` (GAME-2, W family): ω_c(G_N) ≤ 5/6 + 2^{−N/2}/3 and ω_c(G_N) → 5/6.
  * `operator_solution` (quantum side): on every line {a, b, a+b} of an induced configuration the
      Pauli matrices commute pairwise and P_a P_b P_{a+b} = (−1)^{e(ℓ)} I.
-/
import PauliContextuality.SpectralW

open Matrix Filter Topology

namespace PauliCtx.Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-- number of points of `l` on which `u` and `v` agree -/
def agree (l : Finset α) (u v : α → F) : ℕ := (l.filter (fun p => u p = v p)).card

/-- Alice's strategy is admissible: her answer on every line satisfies that line -/
def Admissible (C : Config α) (A : Finset α → α → F) : Prop := ∀ l ∈ C.lines, ¬ C.Violated (A l) l

instance (C : Config α) (A : Finset α → α → F) : Decidable (C.Admissible A) := by
  unfold Admissible; infer_instance

/-- the number of winning (line, point) question pairs -/
def wins (C : Config α) (A : Finset α → α → F) (B : α → F) : ℕ := ∑ l ∈ C.lines, agree l (A l) B

/-- winning probability of a deterministic strategy (uniform line, uniform point of the line) -/
def winProb (C : Config α) (A : Finset α → α → F) (B : α → F) : ℚ :=
  (wins C A B : ℚ) / (3 * C.lines.card)

/-- the best number of winning question pairs over deterministic admissible strategies -/
noncomputable def bestWins (C : Config α) : ℕ :=
  (Finset.univ : Finset ((Finset α → α → F) × (α → F))).sup
    (fun AB => if C.Admissible AB.1 then wins C AB.1 AB.2 else 0)

/-- **the classical value** (max over deterministic strategies) -/
noncomputable def classicalValue (C : Config α) : ℚ := (bestWins C : ℚ) / (3 * C.lines.card)

omit [Fintype α] [DecidableEq α] in
theorem agree_le_card (l : Finset α) (u v : α → F) : agree l u v ≤ l.card := Finset.card_filter_le _ _

/-- key lemma: an answer satisfying a line differs from an assignment violating it in ≥ 1 position -/
theorem agree_le_of_violated (C : Config α) {l : Finset α} {u v : α → F}
    (hu : ¬ C.Violated u l) (hv : C.Violated v l) : agree l u v + 1 ≤ l.card := by
  have hlt : agree l u v < l.card := by
    refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => hv ?_⟩
    have heq : ∀ p ∈ l, u p = v p := fun p hp => (Finset.mem_filter.1 (hsub hp)).2
    have hu' : ∑ p ∈ l, u p + C.sign l = 0 := by unfold Violated at hu; exact not_not.1 hu
    rw [Finset.sum_congr rfl fun p hp => (heq p hp).symm]
    exact hu'
  omega

theorem wins_le (C : Config α) (A : Finset α → α → F) (hA : C.Admissible A) (B : α → F) :
    wins C A B + (C.violated B).card ≤ 3 * C.lines.card := by
  unfold wins violated
  rw [Finset.card_filter, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun l hl => ?_
  have h3 := C.three l hl
  split_ifs with hv
  · have := agree_le_of_violated C (hA l hl) hv; omega
  · have := agree_le_card l (A l) B; omega

/-- the best response of Alice to `B`: copy `B`, flipping one point on violated lines -/
noncomputable def bestA (C : Config α) (B : α → F) (l : Finset α) : α → F :=
  if h : C.Violated B l ∧ l.Nonempty then flip h.2.choose B else B

theorem bestA_adm (C : Config α) (B : α → F) : C.Admissible (bestA C B) := by
  intro l hl
  unfold bestA
  split_ifs with h
  · rw [violated_flip C l _ h.2.choose_spec, not_not]; exact h.1
  · have hne : l.Nonempty := Finset.card_pos.1 (by rw [C.three l hl]; norm_num)
    exact fun hv => h ⟨hv, hne⟩

omit [Fintype α] in
theorem agree_flip (l : Finset α) (B : α → F) {p : α} (hp : p ∈ l) :
    agree l (flip p B) B + 1 = l.card := by
  unfold agree
  have : l.filter (fun q => flip p B q = B q) = l.erase p := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_erase, flip]
    by_cases h : q = p
    · subst h; simp
    · simp [h]
  rw [this, Finset.card_erase_of_mem hp]
  have : 0 < l.card := Finset.card_pos.2 ⟨p, hp⟩
  omega

theorem wins_bestA (C : Config α) (B : α → F) :
    wins C (bestA C B) B + (C.violated B).card = 3 * C.lines.card := by
  unfold wins violated
  rw [Finset.card_filter, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun l hl => ?_
  have h3 := C.three l hl
  have hne : l.Nonempty := Finset.card_pos.1 (by rw [h3]; norm_num)
  unfold bestA
  by_cases hv : C.Violated B l
  · have h : C.Violated B l ∧ l.Nonempty := ⟨hv, hne⟩
    rw [dif_pos h, if_pos hv]
    have := agree_flip l B h.2.choose_spec
    omega
  · rw [dif_neg (fun h => hv h.1), if_neg hv]
    unfold agree
    rw [Finset.filter_true_of_mem (fun _ _ => rfl), h3]

/-- **max wins = 3|L| − deg** -/
theorem bestWins_eq (C : Config α) : bestWins C = 3 * C.lines.card - C.deg := by
  apply le_antisymm
  · refine Finset.sup_le fun AB _ => ?_
    split_ifs with hA
    · have h1 := wins_le C AB.1 hA AB.2
      have h2 := C.deg_le AB.2
      omega
    · exact Nat.zero_le _
  · obtain ⟨B, hB⟩ := C.exists_opt
    have h := wins_bestA C B
    have hle : wins C (bestA C B) B ≤ bestWins C := by
      have := Finset.le_sup (f := fun AB : (Finset α → α → F) × (α → F) =>
        if C.Admissible AB.1 then wins C AB.1 AB.2 else 0) (Finset.mem_univ (bestA C B, B))
      simp only [if_pos (bestA_adm C B)] at this
      exact this
    omega

theorem winProb_le (C : Config α) (A : Finset α → α → F) (hA : C.Admissible A) (B : α → F) :
    winProb C A B ≤ classicalValue C := by
  unfold winProb classicalValue
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := Finset.le_sup (f := fun AB : (Finset α → α → F) × (α → F) =>
    if C.Admissible AB.1 then wins C AB.1 AB.2 else 0) (Finset.mem_univ (A, B))
  simp only [if_pos hA] at this
  exact_mod_cast this

/-- shared randomness does not help: a finite mixture of deterministic admissible strategies wins
with probability ≤ classicalValue -/
theorem mixture_le {ι : Type} (C : Config α) (I : Finset ι) (w : ι → ℚ) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hw1 : ∑ i ∈ I, w i = 1) (A : ι → Finset α → α → F) (hA : ∀ i ∈ I, C.Admissible (A i))
    (B : ι → α → F) :
    ∑ i ∈ I, w i * winProb C (A i) (B i) ≤ classicalValue C := by
  calc ∑ i ∈ I, w i * winProb C (A i) (B i) ≤ ∑ i ∈ I, w i * classicalValue C :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (winProb_le C _ (hA i hi) _) (hw i hi)
    _ = classicalValue C := by rw [← Finset.sum_mul, hw1, one_mul]

/-- the value is attained by a deterministic strategy -/
theorem value_attained (C : Config α) :
    ∃ A B, C.Admissible A ∧ winProb C A B = classicalValue C := by
  obtain ⟨B, hB⟩ := C.exists_opt
  refine ⟨bestA C B, B, bestA_adm C B, ?_⟩
  unfold winProb classicalValue
  have h := wins_bestA C B
  rw [bestWins_eq]
  congr 2
  have := C.deg_le_half
  omega

/-- **GAME-1.** ω_c(G_C) = 1 − deg C/(3|L|). -/
theorem classicalValue_eq (C : Config α) (hL : 0 < C.lines.card) :
    classicalValue C = 1 - (C.deg : ℚ) / (3 * C.lines.card) := by
  unfold classicalValue
  rw [bestWins_eq]
  have hle : C.deg ≤ 3 * C.lines.card := by have := C.deg_le_half; omega
  have hL' : (0 : ℚ) < C.lines.card := by exact_mod_cast hL
  rw [Nat.cast_sub hle]
  push_cast
  field_simp

/-- **GAME-2 (universal bound).** ω_c(G_C) ≥ 5/6 for every configuration. -/
theorem classicalValue_ge (C : Config α) (hL : 0 < C.lines.card) : (5 : ℚ) / 6 ≤ classicalValue C := by
  rw [classicalValue_eq C hL]
  have h := C.deg_le_half
  have hL' : (0 : ℚ) < C.lines.card := by exact_mod_cast hL
  have h' : (2 * C.deg : ℚ) ≤ C.lines.card := by exact_mod_cast h
  rw [show (1 : ℚ) - C.deg / (3 * C.lines.card) = (3 * C.lines.card - C.deg) / (3 * C.lines.card) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  linarith

end PauliCtx.Config

namespace PauliCtx.Spectral

open Config

variable {N : ℕ}

theorem W_lines_pos (N : ℕ) (hN : 2 ≤ N) : 0 < (W N).lines.card := by
  have h := lines_W N (by omega)
  have h16 : 16 ≤ 4 ^ N := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have : 0 < (4 ^ N - 1) * (4 ^ N - 4) := Nat.mul_pos (by omega) (by omega)
  omega

/-- ω_c(G_N) = 1 − ρ_N/3 -/
theorem W_value_eq (N : ℕ) (hN : 2 ≤ N) : (classicalValue (W N) : ℝ) = 1 - rho N / 3 := by
  rw [classicalValue_eq _ (W_lines_pos N hN)]
  unfold rho
  push_cast
  ring

/-- **GAME-2 (the W family).** ω_c(G_N) ≤ 5/6 + 2^{−N/2}/3. -/
theorem W_value_le (N : ℕ) (hN : 2 ≤ N) :
    (classicalValue (W N) : ℝ) ≤ 5 / 6 + 1 / (3 * Real.sqrt (2 ^ N)) := by
  rw [W_value_eq N hN]
  have h := W_lower N hN
  change (1 : ℝ) / 2 - 1 / Real.sqrt (2 ^ N) ≤ rho N at h
  have hs : 0 < Real.sqrt (2 ^ N) := Real.sqrt_pos.2 (by positivity)
  have : 1 / (3 * Real.sqrt (2 ^ N)) = (1 / Real.sqrt (2 ^ N)) / 3 := by field_simp
  rw [this]
  linarith

theorem W_value_ge (N : ℕ) (hN : 2 ≤ N) : (5 : ℝ) / 6 ≤ classicalValue (W N) := by
  have h := (Rat.cast_le (K := ℝ)).2 (classicalValue_ge (W N) (W_lines_pos N hN))
  push_cast at h
  exact h

/-- **GAME-2.** ω_c(G_N) → 5/6. -/
theorem W_value_tendsto : Tendsto (fun N => (classicalValue (W N) : ℝ)) atTop (𝓝 (5 / 6)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (rho_tendsto_half.div_const 3)
  have e : (1 : ℝ) - 1 / 2 / 3 = 5 / 6 := by norm_num
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (W_value_eq N hN).symm

/-! ### the quantum side: Pauli operator solution -/

/-- **operator solution.** On every line of an induced configuration the three Pauli matrices
commute pairwise and their product is `(−1)^{e(ℓ)} I`, with `e(ℓ)` the sign of the line. -/
theorem operator_solution (X : Finset (V N)) (h0 : (0 : V N) ∉ X) :
    ∀ l ∈ (configX X h0).lines, ∃ a b c : V N, l = {a, b, c} ∧ a + b = c ∧
      P a * P b = P b * P a ∧ P a * P c = P c * P a ∧ P b * P c = P c * P b ∧
      P a * P b * P c = ((pm ((configX X h0).sign l) : ℤ) : ℂ) • (1 : Matrix (Bas N) (Bas N) ℂ) := by
  intro l hl
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
  have hL := isLine_of_OP h0 hp
  have hab := hL.comm
  have hac : omega p.1 (p.1 + p.2) = 0 := hL.swap23.comm
  have hbc : omega p.2 (p.1 + p.2) = 0 := hL.swap12.swap23.comm
  have comm : ∀ x y : V N, omega x y = 0 → P x * P y = P y * P x := fun x y h => by
    rw [pauli_comm x y, h, dbl_zero, iPow_zero, one_smul]
  refine ⟨p.1, p.2, p.1 + p.2, rfl, rfl, comm _ _ hab, comm _ _ hac, comm _ _ hbc, ?_⟩
  rw [pauli_mul, smul_mul_assoc, pauli_sq, iPow_ph_comm hab, configX_sign h0 hp, chi_eq_pm]

end PauliCtx.Spectral
