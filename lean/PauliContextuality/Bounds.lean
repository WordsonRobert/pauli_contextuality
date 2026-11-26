/-
Bounds.lean — elementary degree facts that need no geometry:
  * ASY-0  `deg_le_half`      : 2·deg C ≤ |L(C)| (averaging over assignments).
  * ALG-1  `deg_gauge`        : the degree only depends on the sign coset e + Im H.
  * ALG-4  `nc_bound`, `attenuation_iff` : the operational (noncontextual) inequality.
  * CERT-2 `packing_le_deg`, `packing_le_ratio` : fractional packings.
  * TR-3   `card_nontight_le` : stability, the number of non-tight members.
-/
import PauliContextuality.Cover
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace PauliCtx
namespace Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-! ### ASY-0 -/

/-- flip the value at `p` -/
def flip (p : α) (s : α → F) : α → F := Function.update s p (s p + 1)

theorem flip_flip (p : α) (s : α → F) : flip p (flip p s) = s := by
  ext q
  by_cases h : q = p
  · subst h; simp [flip, add_assoc, add_self_F]
  · simp [flip, h]

theorem sum_flip (p : α) (s : α → F) (l : Finset α) (hp : p ∈ l) :
    ∑ q ∈ l, flip p s q = (∑ q ∈ l, s q) + 1 := by
  unfold flip
  rw [Finset.sum_update_of_mem hp, Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase l s hp]
  ring

theorem violated_flip (C : Config α) (l : Finset α) (p : α) (hp : p ∈ l) (s : α → F) :
    C.Violated (flip p s) l ↔ ¬ C.Violated s l := by
  unfold Violated
  rw [sum_flip p s l hp, not_not]
  generalize ∑ q ∈ l, s q = x
  generalize C.sign l = e
  revert x e; decide

/-- For a non-empty line exactly half of all assignments violate it. -/
theorem two_mul_card_viol (C : Config α) (l : Finset α) (hl : l.Nonempty) :
    2 * (Finset.univ.filter (fun s : α → F => C.Violated s l)).card = Fintype.card (α → F) := by
  obtain ⟨p, hp⟩ := hl
  have hbij : (Finset.univ.filter (fun s : α → F => C.Violated s l)).card =
      (Finset.univ.filter (fun s : α → F => ¬ C.Violated s l)).card := by
    refine Finset.card_bij' (fun s _ => flip p s) (fun s _ => flip p s) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [violated_flip C l p hp, not_not]; exact hs
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [violated_flip C l p hp]; exact hs
    · intro s _; exact flip_flip p s
    · intro s _; exact flip_flip p s
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (α → F))) (fun s => C.Violated s l)
  rw [Finset.card_univ] at htot
  omega

/-- ASY-0: `deg C ≤ |L|/2`. -/
theorem deg_le_half (C : Config α) : 2 * C.deg ≤ C.lines.card := by
  have hN : 0 < Fintype.card (α → F) := Fintype.card_pos
  -- Σ_s |V(s)| = Σ_l #{s : l violated} = |L| N / 2
  have hsum : ∑ s : α → F, (C.violated s).card =
      ∑ l ∈ C.lines, (Finset.univ.filter (fun s : α → F => C.Violated s l)).card := by
    simp only [violated, Finset.card_filter]
    rw [Finset.sum_comm]
  have hle : Fintype.card (α → F) * C.deg ≤ ∑ s : α → F, (C.violated s).card := by
    rw [← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun s _ => C.deg_le s
  have h2 : 2 * ∑ s : α → F, (C.violated s).card = Fintype.card (α → F) * C.lines.card := by
    rw [hsum, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun l hl => two_mul_card_viol C l
      (Finset.card_pos.1 (by rw [C.three l hl]; norm_num))]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have : Fintype.card (α → F) * (2 * C.deg) ≤ Fintype.card (α → F) * C.lines.card := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left this hN

/-! ### ALG-1: gauge invariance -/

theorem violated_gauge (C C' : Config α) (hl : C.lines = C'.lines) (t : α → F)
    (hs : ∀ l ∈ C.lines, C'.sign l = C.sign l + ∑ p ∈ l, t p) (s : α → F) :
    C'.violated s = C.violated (s + t) := by
  ext l
  simp only [violated, Violated, Finset.mem_filter, ← hl, Pi.add_apply, Finset.sum_add_distrib]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> rw [hs l h1] at * <;>
    · intro h; apply h2; rw [← h]; ring

/-- ALG-1: changing the signs by an element of `Im H` (a gauge) does not change the degree. -/
theorem deg_gauge (C C' : Config α) (hl : C.lines = C'.lines) (t : α → F)
    (hs : ∀ l ∈ C.lines, C'.sign l = C.sign l + ∑ p ∈ l, t p) : C.deg = C'.deg := by
  apply le_antisymm
  · obtain ⟨s, hs'⟩ := C'.exists_opt
    rw [← hs', violated_gauge C C' hl t hs s]
    exact C.deg_le _
  · obtain ⟨s, hs'⟩ := C.exists_opt
    have : C'.violated (s + t) = C.violated s := by
      rw [violated_gauge C C' hl t hs]
      congr 1
      ext p
      simp [add_assoc, add_self_F]
    rw [← hs', ← this]
    exact C'.deg_le _

/-! ### ALG-4: operational inequality -/

/-- A deterministic noncontextual model `s` gives β = m − 2|V(s)| ≤ m − 2 deg. -/
theorem nc_bound (C : Config α) (s : α → F) :
    (C.lines.card : ℤ) - 2 * (C.violated s).card ≤ C.lines.card - 2 * C.deg := by
  have := C.deg_le s
  omega

/-- The bound is attained. -/
theorem nc_bound_attained (C : Config α) :
    ∃ s : α → F, (C.lines.card : ℤ) - 2 * (C.violated s).card = C.lines.card - 2 * C.deg := by
  obtain ⟨s, hs⟩ := C.exists_opt
  exact ⟨s, by rw [hs]⟩

/-- Mixtures: any convex combination of deterministic values is ≤ m − 2 deg. -/
theorem nc_bound_mixture {ι : Type} (I : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hw1 : ∑ i ∈ I, w i = 1) (C : Config α) (s : ι → α → F) :
    ∑ i ∈ I, w i * ((C.lines.card : ℝ) - 2 * (C.violated (s i)).card) ≤
      (C.lines.card : ℝ) - 2 * C.deg := by
  calc ∑ i ∈ I, w i * ((C.lines.card : ℝ) - 2 * (C.violated (s i)).card)
      ≤ ∑ i ∈ I, w i * ((C.lines.card : ℝ) - 2 * C.deg) := by
        refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hw i hi)
        have := C.deg_le (s i)
        have : (C.deg : ℝ) ≤ (C.violated (s i)).card := by exact_mod_cast this
        linarith
    _ = (C.lines.card : ℝ) - 2 * C.deg := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Uniform attenuation `v` violates the bound iff `v > 1 − 2 deg/m`. -/
theorem attenuation_iff (m D v : ℝ) (hm : 0 < m) : m - 2 * D < v * m ↔ 1 - 2 * D / m < v := by
  have e : 1 - 2 * D / m = (m - 2 * D) / m := by rw [sub_div, div_self hm.ne']
  rw [e, div_lt_iff₀ hm]

/-! ### CERT-2: fractional packings -/

/-- CERT-2 (a): the value of a fractional packing is a lower bound for the degree. -/
theorem packing_le_deg {ι : Type} [Fintype ι] (C : Config α) (fam : ι → Finset (Finset α))
    (hsub : ∀ i, fam i ⊆ C.lines) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpack : ∀ l ∈ C.lines, ∑ i ∈ Finset.univ.filter (fun i => l ∈ fam i), w i ≤ 1)
    (d : ι → ℕ) (hdeg : ∀ i (s : α → F), d i ≤ (C.violated s ∩ fam i).card) :
    ∑ i, w i * d i ≤ C.deg := by
  obtain ⟨s, hs⟩ := C.exists_opt
  set V := C.violated s
  calc ∑ i, w i * d i ≤ ∑ i, w i * (V ∩ fam i).card := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i)
        exact_mod_cast hdeg i s
    _ = ∑ l ∈ V, ∑ i ∈ Finset.univ.filter (fun i => l ∈ fam i), w i := by
        have : ∀ i, ((V ∩ fam i).card : ℝ) = ∑ l ∈ V, if l ∈ fam i then 1 else 0 := by
          intro i
          rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
          push_cast; rfl
        simp_rw [this, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ _l ∈ V, (1 : ℝ) := by
        refine Finset.sum_le_sum fun l hl => hpack l (Finset.mem_filter.1 hl).1
    _ = C.deg := by rw [Finset.sum_const, nsmul_one, hs]

/-- CERT-2 (b): if every member has ratio ≤ r then the packing value is ≤ r |L|. -/
theorem packing_le_ratio {ι : Type} [Fintype ι] (C : Config α) (fam : ι → Finset (Finset α))
    (hsub : ∀ i, fam i ⊆ C.lines) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpack : ∀ l ∈ C.lines, ∑ i ∈ Finset.univ.filter (fun i => l ∈ fam i), w i ≤ 1)
    (d : ι → ℕ) (r : ℝ) (hr : 0 ≤ r) (hd : ∀ i, (d i : ℝ) ≤ r * (fam i).card) :
    ∑ i, w i * d i ≤ r * C.lines.card := by
  calc ∑ i, w i * d i ≤ ∑ i, w i * (r * (fam i).card) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hd i) (hw i)
    _ = r * ∑ l ∈ C.lines, ∑ i ∈ Finset.univ.filter (fun i => l ∈ fam i), w i := by
        have : ∀ i, ((fam i).card : ℝ) = ∑ l ∈ C.lines, if l ∈ fam i then 1 else 0 := by
          intro i
          have h1 : (fam i).card = (C.lines.filter (· ∈ fam i)).card := by
            rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsub i)]
          rw [h1, Finset.card_filter]
          push_cast; rfl
        simp_rw [this, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
    _ ≤ r * ∑ _l ∈ C.lines, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpack) hr
    _ = r * C.lines.card := by rw [Finset.sum_const, nsmul_one]

/-! ### TR-3: stability -/

/-- TR-3: in the uniform-cover setting the number of non-tight members is at most the excess
`c|V| − |ι| d` (each non-tight member contributes ≥ 1 to the excess). -/
theorem card_nontight_le {ι : Type} [Fintype ι] (C : Config α) (fam : ι → Finset (Finset α))
    (hsub : ∀ i, fam i ⊆ C.lines) (c d : ℕ)
    (hcov : ∀ l ∈ C.lines, (Finset.univ.filter (fun i => l ∈ fam i)).card = c)
    (hdeg : ∀ i (s : α → F), d ≤ (C.violated s ∩ fam i).card) (s : α → F) :
    (Finset.univ.filter (fun i => (C.violated s ∩ fam i).card ≠ d)).card + Fintype.card ι * d ≤
      c * (C.violated s).card := by
  rw [← uniform_cover_excess C fam hsub c hcov s, Fintype.card, ← smul_eq_mul, ← Finset.sum_const,
    Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := hdeg i s
  split_ifs with h
  · omega
  · omega

end Config
end PauliCtx
