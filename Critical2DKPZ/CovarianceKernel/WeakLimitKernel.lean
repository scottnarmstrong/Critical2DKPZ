/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakCovarianceLimit

/-! # Local `L²` representatives of weighted weak limits -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.CovarianceKernel

/-- Recover an unweighted covariance representative from a weak limit of weighted kernels. -/
def weakLimitCovarianceKernel (v : Lp ℝ 2 (volume : Measure Plane)) (z : Plane) : ℝ :=
  v z / covarianceDecayWeight z

/-- The reciprocal of the decay weight is `(1 + ‖z‖) ^ 2`. -/
theorem covarianceDecayWeight_inv (z : Plane) :
    (covarianceDecayWeight z)⁻¹ = (1 + ‖z‖) ^ 2 := by
  have hb : 0 < 1 + ‖z‖ := by positivity
  simp [covarianceDecayWeight, Real.rpow_neg hb.le]

/-- Dividing a global `L²` function by the polynomial weight preserves local `L²`. -/
theorem weakLimitCovarianceKernel_memLp_two_on_compact
    (v : Lp ℝ 2 (volume : Measure Plane)) (K : Set Plane) (hK : IsCompact K) :
    MemLp (weakLimitCovarianceKernel v) 2 (volume.restrict K) := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  let B : ℝ := (1 + R) ^ 2
  have hB : 0 ≤ B := by positivity
  have hv : MemLp (fun z : Plane => v z) 2 (volume : Measure Plane) := Lp.memLp v
  have hinvCont : Continuous (fun z : Plane => (covarianceDecayWeight z)⁻¹) := by
    have hw : Continuous covarianceDecayWeight := by
      unfold covarianceDecayWeight
      refine Continuous.rpow_const (by fun_prop) fun z => Or.inl ?_
      positivity
    exact hw.inv₀ (fun z => (covarianceDecayWeight_pos z).ne')
  have hCstrong : AEStronglyMeasurable (weakLimitCovarianceKernel v)
      (volume.restrict K) := by
    change AEStronglyMeasurable
      (fun z : Plane => v z * (covarianceDecayWeight z)⁻¹) (volume.restrict K)
    exact (hv.restrict K).aestronglyMeasurable.mul hinvCont.aestronglyMeasurable
  apply MemLp.of_le_mul (hv.restrict K) hCstrong
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have hzR : ‖z‖ < R := hR z hz
  have hinvpos : 0 < (covarianceDecayWeight z)⁻¹ := inv_pos.mpr (covarianceDecayWeight_pos z)
  have hinvBound : (covarianceDecayWeight z)⁻¹ ≤ B := by
    rw [covarianceDecayWeight_inv]
    dsimp [B]
    have hbase : 0 ≤ 1 + ‖z‖ := by positivity
    have hbaseR : 0 ≤ 1 + R := by linarith
    exact (sq_le_sq₀ hbase hbaseR).2 (by linarith)
  change ‖v z * (covarianceDecayWeight z)⁻¹‖ ≤ B * ‖v z‖
  rw [norm_mul, Real.norm_of_nonneg hinvpos.le]
  calc
    ‖v z‖ * (covarianceDecayWeight z)⁻¹ ≤ ‖v z‖ * B :=
      mul_le_mul_of_nonneg_left hinvBound (norm_nonneg _)
    _ = B * ‖v z‖ := by ring

end Critical2DKPZ.CovarianceKernel

end
