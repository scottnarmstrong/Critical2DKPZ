/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.Collision.ConditionalFlat
import Mathlib.Tactic

/-! # Conditional moments of past-measurable profiles -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Collision

/-- The conditional first moment of a past-measurable profile is its total mass. -/
theorem setIntegral_profileP2Fun_eq_sum (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site) (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ M : ℝ, ∀ ω w, |η ω w| ≤ M)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w)) (G : Set Disorder)
    (hG : MeasurableSet[disorderPast a] G) :
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ∂disorderLaw =
      ∫ ω in G, ∑ w ∈ A, η ω w ∂disorderLaw := by
  let X : Disorder → ℝ := randomFlatProfilePolymer β a b η
  have hXmeas : Measurable X := by
    dsimp [X, randomFlatProfilePolymer]
    exact measurable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hmeas
  have hXint : Integrable X disorderLaw := by
    dsimp [X, randomFlatProfilePolymer]
    exact integrable_randomTerminalProfilePolymer β a b A η (fun _ => 1)
      hsupp hbdd hmeas 1 (by intro z; simp)
  have hpast : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero a]
    exact Gaussian.disorderBlock_le 0 a
  have hce := condExp_randomFlatProfilePolymer β a b hab A η hsupp hmeas hXmeas hXint
  have hceG : ∀ᵐ ω ∂disorderLaw, ω ∈ G →
      disorderLaw[X | disorderPast a] ω = ∑ w ∈ A, η ω w := by
    filter_upwards [hce] with ω hω
    intro _
    exact hω
  calc
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ∂disorderLaw =
        ∫ ω in G, disorderLaw[X | disorderPast a] ω ∂disorderLaw := by
          simpa only [X, randomFlatProfilePolymer] using
            (setIntegral_condExp hpast hXint hG).symm
    _ = ∫ ω in G, ∑ w ∈ A, η ω w ∂disorderLaw :=
      setIntegral_congr_ae (hpast G hG) hceG

end Critical2DKPZ.FutureProfiles

end
