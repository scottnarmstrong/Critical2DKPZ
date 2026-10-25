/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.CriticalGap
public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonRenewal
public import Critical2DKPZ.OnePoint.SecondMoment

/-!
# Moving quasi-critical parameters

Elementary parameter identities used in the fixed-horizon Edwards--Wilkinson
argument.  Unlike the critical-window renewal limits, these statements allow
the parameter `-l N` to move with the lattice scale.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The distance of the variance at parameter `-l` from the critical replica
threshold.  The guards exclude the junk values of the critical parameter at
the finitely many small lattice scales. -/
theorem criticalSigmaSq_neg_mul_replicaOverlap (l : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hlog : Real.log (N : ℝ) ≠ 0) :
    Critical2DKPZ.criticalSigmaSq (-l) N * Critical2DKPZ.replicaOverlap N =
      1 - l / Real.log (N : ℝ) := by
  have hR : Critical2DKPZ.replicaOverlap N ≠ 0 :=
    (Critical2DKPZ.replicaOverlap_pos hN).ne'
  unfold Critical2DKPZ.criticalSigmaSq
  field_simp
  ring

/-- A moving quasi-critical parameter remains in the source-valid domain of
`criticalBeta` once `l / log N → 0` and `l → ∞`. -/
theorem eventually_criticalBeta_spec_neg_moving (l : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (Critical2DKPZ.criticalBeta (-l N) N ^ 2) - 1 =
        Critical2DKPZ.criticalSigmaSq (-l N) N := by
  have hlpos : ∀ᶠ N : ℕ in atTop, 0 < l N := hl.eventually_gt_atTop 0
  have hratioOne : ∀ᶠ N : ℕ in atTop, l N / Real.log (N : ℝ) < 1 :=
    hratio.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 2, hlpos, hratioOne] with N hN hlN hratioN
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlLog : l N < Real.log (N : ℝ) := (div_lt_one hlogpos).mp hratioN
  apply Critical2DKPZ.OnePoint.criticalBeta_spec_of_abs_lt_log (by omega)
  simpa only [abs_neg, abs_of_pos hlN] using hlLog

/-- In a moving quasi-critical window, the disorder variance has the same
leading normalization as throughout the fixed critical window. -/
theorem tendsto_criticalSigmaSq_neg_mul_log (l : ℕ → ℝ)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => Critical2DKPZ.criticalSigmaSq (-l N) N * Real.log (N : ℝ))
      atTop (𝓝 Real.pi) := by
  have hquot := ((tendsto_const_nhds (x := (1 : ℝ))).sub hratio).div
    Critical2DKPZ.Renewal.tendsto_overlap_div_log
    (one_div_pos.mpr Real.pi_pos).ne'
  have hquot' : Tendsto (fun N : ℕ =>
      (1 - l N / Real.log (N : ℝ)) /
        (Critical2DKPZ.replicaOverlap N / Real.log (N : ℝ)))
      atTop (𝓝 Real.pi) := by
    simpa only [sub_zero, one_div_one_div, Pi.div_def] using hquot
  apply hquot'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hR : Critical2DKPZ.replicaOverlap N ≠ 0 :=
    (Critical2DKPZ.replicaOverlap_pos (by omega)).ne'
  unfold Critical2DKPZ.criticalSigmaSq
  field_simp
  ring




end Critical2DKPZ.Extensions.GffTangent

end
