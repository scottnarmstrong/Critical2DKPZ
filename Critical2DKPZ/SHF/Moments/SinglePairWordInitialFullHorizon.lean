/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialFull
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialCutoffHorizon
import Mathlib.Tactic

/-! # Full incoming cutoff entrance integrals on arbitrary horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- The cutoff entrance limit holds over all incoming locations. Compact test
support supplies the common finite-measure majorant; the continuum integral
is integrable, including the coincident-start set. -/
theorem integrable_and_tendsto_integral_pairTwoCutoffInitialStep_horizon
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) :
    Integrable (pairTwoContinuumCutoffEntrance (ϑ - Real.eulerMascheroniConstant) T s t φ η) ∧
    Tendsto (fun N => ∫ p : Plane × Plane, pairTwoCutoffInitialStep ϑ N (L N)
      (evenCeil (N * s) + 1) (evenCeil (N * t)) φ η p) atTop
      (𝓝 (∫ p : Plane × Plane, pairTwoContinuumCutoffEntrance
        (ϑ - Real.eulerMascheroniConstant) T s t φ η p)) := by
  obtain ⟨_M, R, _hM, _hR, _hφ, hφR⟩ := exists_collisionWord_compactTest_bounds φ
  let K : Set (Plane × Plane) := Metric.closedBall (0 : Plane) (R + 4) ×ˢ
    Metric.closedBall (0 : Plane) (R + 4)
  have hK : IsCompact K := (isCompact_closedBall (0 : Plane) (R + 4)).prod
    (isCompact_closedBall (0 : Plane) (R + 4))
  have hnot (p : Plane × Plane) (hp : p ∉ K) : R + 4 < ‖p.1‖ ∨ R + 4 < ‖p.2‖ := by
    simpa only [K, Set.mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le] using hp
  let F := pairTwoContinuumCutoffEntrance (ϑ - Real.eulerMascheroniConstant) T s t φ η
  have hz (p : Plane × Plane) (hp : p ∉ K) : F p = 0 :=
    continuumCutoffEntrance_zero_outside_ball _ T s t φ η hφR p (hnot p hp)
  have hi : Integrable F := (integrableOn_iff_integrable_of_support_subset
    (show Function.support F ⊆ K from fun p hp => by
      by_contra hn; exact hp (hz p hn))).mp
    (integrableOn_pairTwoContinuumCutoffEntrance_horizon ϑ T hT L hL hs hst φ η hη K hK.measure_ne_top)
  refine ⟨hi, ?_⟩
  have hlim := tendsto_integral_pairTwoCutoffInitialStep_horizon ϑ T hT L hL hs hst φ η hη K hK.measure_ne_top
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  exact cutoffInitialStep_zero_outside_ball ϑ hN _ _ _ φ η hφR p (hnot p hp)

end Critical2DKPZ.SHF.Moments
