/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceL1
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSupport
public import Critical2DKPZ.SHF.Moments.WordDominationCellSupport
import Mathlib.Tactic

/-! # The uncut continuum two-particle entrance is absolutely integrable -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

/-- Absolute integrability of the complete continuum entrance, over both
incoming locations, the collision center, and the full entrance-time slab.
Compact endpoint tests supply the incoming support automatically. -/
theorem integrable_pairTwo_continuum_entrance
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    Integrable (fun p : ℝ × (Plane × (Plane × Plane)) =>
      (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
        pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1)
      ((volume.restrict (Set.Ioo 0 T)).prod
        ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))) := by
  obtain ⟨_M, R, _hM, _hR, _hφ, hφR⟩ := exists_collisionWord_compactTest_bounds φ
  let K : Set Plane := Metric.closedBall 0 R
  let ν : Measure (Plane × Plane) := (volume : Measure Plane).prod volume
  let μ := (volume.restrict (Set.Ioo 0 T)).prod ((volume : Measure Plane).prod ν)
  let S : Set (ℝ × (Plane × (Plane × Plane))) := Set.univ ×ˢ (K ×ˢ Set.univ)
  let F := fun p : ℝ × (Plane × (Plane × Plane)) =>
    (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
      pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1
  have hmeasure : μ.restrict S = (volume.restrict (Set.Ioo 0 T)).prod
      ((volume.restrict K).prod ν) := by
    dsimp only [μ, S]
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      ← Measure.prod_restrict, Measure.restrict_univ]
  have hi : IntegrableOn F S μ := by
    rw [IntegrableOn, hmeasure]
    exact integrable_pairTwo_continuum_entrance_on_initial_window θ T hT φ K
      (isCompact_closedBall (0 : Plane) R).measure_ne_top
  apply (integrableOn_iff_integrable_of_support_subset (s := S) ?_).mp hi
  intro p hp
  by_contra hn
  have hnorm : R < ‖p.2.1‖ := by
    simpa only [S, K, Set.mem_prod, Set.mem_univ, true_and, and_true,
      Metric.mem_closedBall, dist_zero_right, not_le] using hn
  have hz := pairTwoContinuumFuture_zero_of_incoming_norm θ (T - p.1) φ
    ![p.2.1, p.2.2.2] hφR 0 hnorm p.2.2.1
  exact hp (by dsimp only [F]; rw [hz, mul_zero])

end Critical2DKPZ.SHF.Moments
