/-
ThreeQubit.lean — blueprint TQ-3 (rigidity of W(5,2)), doily part.

  * `doily3` : the doily W(3,2) ⊗ I inside W(5,2) (15 lines, degree 3).
  * `doily_rigid` (TQ-3) : every optimal assignment of W(5,2) violates exactly 3 lines of every
      Sp(6,2)-translate of the doily. This is TR-2 with ρ(doily) = 3/15 = 63/315 = ρ(W(5,2)).
-/
import PauliContextuality.GeoBounds

namespace PauliCtx.Spectral

open Config

/-- the doily `W(3,2) ⊗ I` as a family of lines of `W(5,2)` -/
noncomputable def doily3 : Finset (Finset (V (2 + 1))) := (W 2).lines.image (fun l => l.map padE)

theorem doily3_sub : doily3 ⊆ (W (2 + 1)).lines := padL_sub (subset_refl _)

theorem doily3_card : doily3.card = 15 := by
  rw [doily3, (deg_pad (W 2).lines (subset_refl _)).2, card_lines_W2]

/-- **TQ-3 (doily rigidity).** Every optimal assignment of W(5,2) violates exactly 3 lines of every
Sp(6,2)-translate of the doily. -/
theorem doily_rigid (s : V (2 + 1) → F) (hs : ((W (2 + 1)).violated s).card = (W (2 + 1)).deg) :
    ∀ g ∈ Sp (2 + 1), ((W (2 + 1)).violated s ∩ imgL g doily3).card = 3 := by
  have hne : doily3.Nonempty := Finset.card_pos.1 (by rw [doily3_card]; norm_num)
  have doily3_deg : ((W (2 + 1)).sub doily3 doily3_sub).deg = 3 := by
    rw [show ((W (2 + 1)).sub doily3 doily3_sub).deg = ((W 2).sub (W 2).lines (subset_refl _)).deg from
      (deg_pad (W 2).lines (subset_refl _)).1, Config.sub_self, W3_eq_3]
  have heq : (W (2 + 1)).lines.card * ((W (2 + 1)).sub doily3 doily3_sub).deg =
      doily3.card * (W (2 + 1)).deg := by
    have hL : ∀ M, M = 3 → (W M).lines.card = 315 := by rintro M rfl; exact card_lines_W3
    have hD : ∀ M, M = 3 → (W M).deg = 63 := by rintro M rfl; exact W5_eq_63
    rw [doily3_deg, doily3_card, hL (2 + 1) (by norm_num), hD (2 + 1) (by norm_num)]
  intro g hg
  rw [← doily3_deg]
  exact rho_rigid doily3 doily3_sub hne heq s hs g hg

end PauliCtx.Spectral
