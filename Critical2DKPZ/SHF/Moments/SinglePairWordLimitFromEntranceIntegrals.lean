/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairEntranceLimitFromCutoffs
public import Critical2DKPZ.SHF.Moments.SinglePairWordMovingRepresentation
public import Critical2DKPZ.SHF.Moments.WordLimitSpectators
public import Critical2DKPZ.SHF.Moments.TimeRounding
import Mathlib.Tactic

/-! Convergence and cutoff control of entrance integrals imply the moving two-particle word limit. -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter DeltaBose
open scoped CompactlySupported Topology

/-- The exact tested diagram identity, discrete exhaustion error, and
full-clock cutoff limits imply the moving two-replica word limit. -/
theorem pairTwoWordLimit_of_entrance_identification_and_cutoff_limits
    (ϑ : ℝ)
    (hA : ∀ (θ T : ℝ), 0 < T → ∀ φ : Fin 2 → C_c(Plane × Plane, ℝ),
      (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i, φ i (x i, y i)) * (diagramKernel θ [pairTwo] T x y).toReal) =
      (1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
        (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
          pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1
        ∂(volume.restrict (Set.Ioo 0 T)).prod
          ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))))
    (hB : ∀ (ϑ T : ℝ), 0 < T → ∀ L : ℕ → ℕ,
      Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T) →
      ∀ φ : Fin 2 → C_c(Plane × Plane, ℝ), ∀ η : ℕ → C_c(ℝ × Plane, ℝ),
      (∀ k p, η k p ∈ Set.Icc (0 : ℝ) 1) →
      (∀ (k : ℕ) (p : ℝ × Plane), T / ((k : ℝ) + 3) ≤ p.1 →
        p.1 ≤ T - T / ((k : ℝ) + 3) → ‖p.2‖ ≤ k → η k p = 1) →
      ∀ ε > 0, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        |pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (fun _ => 1) -
          pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ (η k)| ≤ ε)
    (hC : ∀ (ϑ T : ℝ), 0 < T → ∀ L : ℕ → ℕ,
      Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T) →
      ∀ φ : Fin 2 → C_c(Plane × Plane, ℝ), ∀ η : C_c(ℝ × Plane, ℝ),
      (∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) →
      Tendsto (fun N => pairTwoTestedEntranceWindow ϑ N (L N) 1 (L N) φ η) atTop
        (𝓝 ((1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
          η (p.1, p.2.2.1) *
            ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
              pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1)
                φ ![p.2.1, p.2.2.2] p.2.2.1)
          ∂(volume.restrict (Set.Ioo 0 T)).prod
            ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)))))) :
    PairTwoWordLimit ϑ := by
  intro s t hs hst sN tN hsN htN hsN0 φ
  let L : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * tN N) - evenCeil ((N : ℝ) * sN N)
  have hT : 0 < t - s := sub_pos.mpr hst
  have hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 (t - s)) :=
    tendsto_evenCeil_moving_gap_div sN tN hsN htN hs hsN0 hst
  have hfull := tendsto_pairTwoTestedEntranceWindow_full_of_cutoff_limits
    ϑ (t - s) hT L φ
    (fun η hrange hplateau => hB ϑ (t - s) hT L hL φ η hrange hplateau)
    (fun η hη => hC ϑ (t - s) hT L hL φ η hη)
  rw [← hA (ϑ - Real.eulerMascheroniConstant) (t - s) hT φ] at hfull
  apply hfull.congr'
  filter_upwards [eventually_testedBlockWord_pairTwo_eq_entranceWindow_all_times ϑ φ] with N hN
  exact (hN (sN N) (tN N)).symm

end Critical2DKPZ.SHF.Moments
