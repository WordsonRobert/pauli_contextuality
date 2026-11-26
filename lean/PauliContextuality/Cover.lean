/-
Cover.lean — odd-cycle lemma (CERT-1) and uniform-cover lemma (TR-1'), plus statements of
transfer / rigidity / stability / profile bound (03_transfer.md, 04_certificates.md).
-/
import PauliContextuality.Config

namespace PauliCtx
namespace Config

variable {α : Type} [Fintype α] [DecidableEq α]

/-- A set of lines `y` is a cycle if every point lies on an even number of its lines. -/
def IsCycle (y : Finset (Finset α)) : Prop := ∀ p : α, Even ((y.filter (fun l => p ∈ l)).card)

/-- In a cycle, `Σ_{l∈y} Σ_{p∈l} s p = 0` (each point is counted an even number of times). -/
theorem sum_sum_cycle (y : Finset (Finset α)) (hc : IsCycle y) (s : α → F) :
    ∑ l ∈ y, ∑ p ∈ l, s p = 0 := by
  have h1 : ∀ l ∈ y, ∑ p ∈ l, s p = ∑ p, if p ∈ l then s p else 0 := fun l _ => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  obtain ⟨k, hk⟩ := hc p
  rw [hk, Nat.cast_add, add_self_F, zero_mul]

/-- Double counting (TR-1' step 2) for an arbitrary set `V` of lines inside a set `D` and a family
covering each line of `D` at most `c` times: `Σ_i |V ∩ fam i| ≤ c |V|`. -/
theorem sum_inter_le {β ι : Type} [DecidableEq β] (I : Finset ι) (fam : ι → Finset β) (V : Finset β)
    (c : ℕ) (hcov : ∀ l ∈ V, (I.filter (fun i => l ∈ fam i)).card ≤ c) :
    ∑ i ∈ I, (V ∩ fam i).card ≤ c * V.card := by
  have h1 : ∀ i ∈ I, (V ∩ fam i).card = ∑ l ∈ V, if l ∈ fam i then 1 else 0 := by
    intro i _
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  calc ∑ l ∈ V, ∑ i ∈ I, (if l ∈ fam i then 1 else 0)
      = ∑ l ∈ V, (I.filter (fun i => l ∈ fam i)).card := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.card_filter]
    _ ≤ ∑ _l ∈ V, c := Finset.sum_le_sum hcov
    _ = c * V.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Exact double counting. -/
theorem sum_inter_eq {β ι : Type} [DecidableEq β] (I : Finset ι) (fam : ι → Finset β) (V : Finset β)
    (c : ℕ) (hcov : ∀ l ∈ V, (I.filter (fun i => l ∈ fam i)).card = c) :
    ∑ i ∈ I, (V ∩ fam i).card = c * V.card := by
  have h1 : ∀ i ∈ I, (V ∩ fam i).card = ∑ l ∈ V, if l ∈ fam i then 1 else 0 := by
    intro i _
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  calc ∑ l ∈ V, ∑ i ∈ I, (if l ∈ fam i then 1 else 0)
      = ∑ l ∈ V, (I.filter (fun i => l ∈ fam i)).card := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.card_filter]
    _ = ∑ _l ∈ V, c := Finset.sum_congr rfl hcov
    _ = c * V.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- CERT-1. An odd cycle forces at least one violated line.
Proof sketch: Σ_{l∈y} (Σ_{p∈l} s p + sign l) = Σ_p (#{l∈y : p∈l}) • s p + Σ_l sign l = 0 + 1 in ZMod 2
(`Finset.sum_comm`, evenness kills the first sum). If no line of y were violated every summand
would be 0, contradiction. -/
theorem odd_cycle_forces_violation (C : Config α) (y : Finset (Finset α)) (hy : y ⊆ C.lines)
    (hc : IsCycle y) (hodd : (∑ l ∈ y, C.sign l) = 1) (s : α → F) :
    1 ≤ (C.violated s ∩ y).card := by
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
  intro hempty
  have hsat : ∀ l ∈ y, (∑ p ∈ l, s p) + C.sign l = 0 := by
    intro l hl
    by_contra hv
    have hmem : l ∈ C.violated s ∩ y := Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨hy hl, hv⟩, hl⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have hsum := Finset.sum_congr rfl hsat
  rw [Finset.sum_add_distrib, sum_sum_cycle y hc s, zero_add, hodd, Finset.sum_const_zero] at hsum
  exact one_ne_zero hsum

/-- Stability (TR-3), uniform-cover form: Σ_i (|V ∩ fam i| - d) = c |V| - |ι| d. -/
theorem uniform_cover_excess {ι : Type} [Fintype ι] (C : Config α) (fam : ι → Finset (Finset α))
    (hsub : ∀ i, fam i ⊆ C.lines) (c : ℕ)
    (hcov : ∀ l ∈ C.lines, (Finset.univ.filter (fun i => l ∈ fam i)).card = c) (s : α → F) :
    ∑ i, (C.violated s ∩ fam i).card = c * (C.violated s).card :=
  sum_inter_eq _ fam _ c fun l hl => hcov l (Finset.mem_filter.1 hl).1

/-- TR-1' (uniform cover). `fam : ι → Finset (Finset α)` is a family of sub-line-sets, each line of `C`
lies in exactly `c` members, and each member forces at least `d` violations for every assignment.
Then every assignment violates at least `⌈|ι| d / c⌉` lines.
Proof sketch: Σ_i |V ∩ fam i| = Σ_{l∈V} #{i : l ∈ fam i} = c |V| (`Finset.sum_comm`), and the
left side is ≥ |ι| d. -/
theorem uniform_cover {ι : Type} [Fintype ι] (C : Config α) (fam : ι → Finset (Finset α))
    (hsub : ∀ i, fam i ⊆ C.lines) (c d : ℕ) (hc : 0 < c)
    (hcov : ∀ l ∈ C.lines, (Finset.univ.filter (fun i => l ∈ fam i)).card = c)
    (hdeg : ∀ i (s : α → F), d ≤ (C.violated s ∩ fam i).card)
    (s : α → F) : Fintype.card ι * d ≤ c * (C.violated s).card := by
  rw [← uniform_cover_excess C fam hsub c hcov s, Fintype.card, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun i _ => hdeg i s

/-- Corollary in the form used for bounds: `deg ≥ k` whenever `|ι| d > c (k-1)`. -/
theorem uniform_cover_deg {ι : Type} [Fintype ι] (C : Config α) (fam : ι → Finset (Finset α))
    (hsub : ∀ i, fam i ⊆ C.lines) (c d k : ℕ) (hc : 0 < c)
    (hcov : ∀ l ∈ C.lines, (Finset.univ.filter (fun i => l ∈ fam i)).card = c)
    (hdeg : ∀ i (s : α → F), d ≤ (C.violated s ∩ fam i).card)
    (hk : c * (k - 1) < Fintype.card ι * d) : k ≤ C.deg := by
  obtain ⟨s, hs⟩ := C.exists_opt
  have h := uniform_cover C fam hsub c d hc hcov hdeg s
  rw [hs] at h
  have : k - 1 < C.deg := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hk h)
  omega

/-- Rigidity (TR-2), stated for the uniform-cover setting: if `|ι| d = c · deg C` then every optimal
assignment meets every member in exactly `d` lines. -/
theorem uniform_cover_rigid {ι : Type} [Fintype ι] (C : Config α) (fam : ι → Finset (Finset α))
    (hsub : ∀ i, fam i ⊆ C.lines) (c d : ℕ) (hc : 0 < c)
    (hcov : ∀ l ∈ C.lines, (Finset.univ.filter (fun i => l ∈ fam i)).card = c)
    (hdeg : ∀ i (s : α → F), d ≤ (C.violated s ∩ fam i).card)
    (heq : Fintype.card ι * d = c * C.deg) (s : α → F) (hs : (C.violated s).card = C.deg) :
    ∀ i, (C.violated s ∩ fam i).card = d := by
  have hsum := uniform_cover_excess C fam hsub c hcov s
  rw [hs, ← heq, Fintype.card, ← smul_eq_mul, ← Finset.sum_const] at hsum
  have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hdeg i s)).1 hsum.symm
  exact fun i => (this i (Finset.mem_univ i)).symm

end Config
end PauliCtx
