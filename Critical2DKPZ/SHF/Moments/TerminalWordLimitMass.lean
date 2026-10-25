/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSeparatedScale
import Mathlib.Tactic

/-! # Uniform terminal masses along separated moving starts -/

@[expose] public noncomputable section

open Filter
open scoped Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- Potential domination controls the row mass along every moving start
whose first pair has distinct limiting coordinates. No phase premise is needed
for this upper bound. -/
theorem eventually_wordTerminalTest_mass_le_of_potentialDomination
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·))
    {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → Fin h → Site) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hsep : x α.1.1 ≠ x α.1.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) (nN N) (xN N)
        (fun _ => 1) ≤ C := by
  let T := τ + 1
  let δ := ‖x α.1.2 - x α.1.1‖ / 2
  have hT : 0 < T := by dsimp [T]; linarith only [hτ]
  have hgap : 0 < ‖x α.1.2 - x α.1.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsep.symm)
  have hδ : 0 < δ := half_pos hgap
  obtain ⟨C, hC, hbound⟩ := eventually_wordTerminalTest_mass_le_uniform_of_potentialDomination
    ϑ hD T δ hT hδ α w hw
  have hgaplim : Tendsto
      (fun N => latticeRepresentative N (xN N α.1.2 - xN N α.1.1)) atTop
      (𝓝 (x α.1.2 - x α.1.1)) := by
    simpa only [latticeRepresentative_sub] using (hx α.1.2).sub (hx α.1.1)
  have hseplim := hgaplim.norm.eventually
    (Ioi_mem_nhds (show δ < ‖x α.1.2 - x α.1.1‖ by dsimp [δ]; linarith only [hgap]))
  have htimelim := hn.eventually (Iio_mem_nhds (show τ < T by dsimp [T]; linarith))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hseplim, htimelim, eventually_gt_atTop 0] with N hboundN hsepN htimeN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact hboundN (nN N) ((div_le_iff₀ hNr).mp htimeN.le) (xN N) hsepN.le

end Critical2DKPZ.SHF.Moments
