/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralData
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-! # Zero extension from a compact frequency ball into spectral `L²` -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

open Classical in
/-- Extension by zero outside the closed frequency ball. -/
def compactSpectralFun (R : ℝ) (f : C(Metric.closedBall (0 : Plane) R, ℂ)) (ξ : Plane) : ℂ :=
  if hξ : ξ ∈ Metric.closedBall (0 : Plane) R then f ⟨ξ, hξ⟩ else 0

/-- Zero extension is measurable. -/
theorem measurable_compactSpectralFun (R : ℝ) (f : C(Metric.closedBall (0 : Plane) R, ℂ)) :
    Measurable (compactSpectralFun R f) :=
by
  classical
  exact f.continuous.measurable.dite measurable_const Metric.isClosed_closedBall.measurableSet

/-- The pointwise norm is bounded by the corresponding constant on the frequency ball. -/
theorem norm_compactSpectralFun_le (R : ℝ) (f : C(Metric.closedBall (0 : Plane) R, ℂ)) (ξ : Plane) :
    ‖compactSpectralFun R f ξ‖ ≤
      ‖(Metric.closedBall (0 : Plane) R).indicator (fun _ => (‖f‖ : ℂ)) ξ‖ := by
  classical
  by_cases hξ : ξ ∈ Metric.closedBall (0 : Plane) R
  · simp only [compactSpectralFun, hξ, dite_true, Set.indicator_of_mem hξ, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg f)]
    exact f.norm_coe_le_norm ⟨ξ, hξ⟩
  · simp only [compactSpectralFun, hξ, dite_false, Set.indicator_of_notMem hξ, norm_zero, le_refl]

/-- Finite mass of the frequency ball makes zero extension square integrable. -/
theorem memLp_compactSpectralFun (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (R : ℝ) (f : C(Metric.closedBall (0 : Plane) R, ℂ)) : MemLp (compactSpectralFun R f) 2 ν := by
  apply (memLp_indicator_const 2 Metric.isClosed_closedBall.measurableSet (‖f‖ : ℂ)
    (Or.inr (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne)).of_le
    (measurable_compactSpectralFun R f).aestronglyMeasurable
  exact Eventually.of_forall (norm_compactSpectralFun_le R f)

/-- The zero-extension linear map before supplying its operator norm bound. -/
def compactSpectralLinear (ν : Measure Plane) [IsLocallyFiniteMeasure ν] (R : ℝ) :
    C(Metric.closedBall (0 : Plane) R, ℂ) →ₗ[ℝ] Lp ℂ 2 ν where
  toFun := fun f => (memLp_compactSpectralFun ν R f).toLp (compactSpectralFun R f)
  map_add' := by
    classical
    intro f g
    apply Lp.ext
    filter_upwards [(memLp_compactSpectralFun ν R (f + g)).coeFn_toLp,
      (memLp_compactSpectralFun ν R f).coeFn_toLp,
      (memLp_compactSpectralFun ν R g).coeFn_toLp,
      Lp.coeFn_add ((memLp_compactSpectralFun ν R f).toLp _)
        ((memLp_compactSpectralFun ν R g).toLp _)] with ξ hfg hf hg hadd
    rw [hfg, hadd, Pi.add_apply, hf, hg]
    simp only [compactSpectralFun]
    split <;> simp
  map_smul' := by
    classical
    intro c f
    apply Lp.ext
    filter_upwards [(memLp_compactSpectralFun ν R (c • f)).coeFn_toLp,
      (memLp_compactSpectralFun ν R f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_compactSpectralFun ν R f).toLp _)] with ξ hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul, Pi.smul_apply, hf]
    simp only [compactSpectralFun]
    split <;> simp

/-- The operator norm is at most the square root of the spectral mass of the ball. -/
theorem norm_compactSpectralLinear_apply (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (R : ℝ) (f : C(Metric.closedBall (0 : Plane) R, ℂ)) :
    ‖compactSpectralLinear ν R f‖ ≤ Real.sqrt (specMass ν R) * ‖f‖ := by
  let G : Lp ℂ 2 ν := indicatorConstLp 2 Metric.isClosed_closedBall.measurableSet
    ((isCompact_closedBall (0 : Plane) R).measure_lt_top.ne) (‖f‖ : ℂ)
  have hnorm : ‖compactSpectralLinear ν R f‖ ≤ ‖G‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_compactSpectralFun ν R f).coeFn_toLp,
      (indicatorConstLp_coeFn (p := 2) (μ := ν) (s := Metric.closedBall (0 : Plane) R)
        (hs := Metric.isClosed_closedBall.measurableSet)
        (hμs := (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne) (c := (‖f‖ : ℂ)))] with ξ hf hG
    change ‖(memLp_compactSpectralFun ν R f).toLp _ ξ‖ ≤ ‖G ξ‖
    rw [hf, hG]
    exact norm_compactSpectralFun_le R f ξ
  calc
    ‖compactSpectralLinear ν R f‖ ≤ ‖G‖ := hnorm
    _ = ‖f‖ * Real.sqrt (specMass ν R) := by
      rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm, ENNReal.toReal_ofNat]
      rw [Real.sqrt_eq_rpow]
      rfl
    _ = Real.sqrt (specMass ν R) * ‖f‖ := mul_comm _ _

/-- Continuous zero extension to spectral `L²`. -/
def compactSpectralEmbedding (ν : Measure Plane) [IsLocallyFiniteMeasure ν] (R : ℝ) :
    C(Metric.closedBall (0 : Plane) R, ℂ) →L[ℝ] Lp ℂ 2 ν :=
  (compactSpectralLinear ν R).mkContinuous (Real.sqrt (specMass ν R))
    (norm_compactSpectralLinear_apply ν R)

/-- The continuous embedding has the same pointwise version. -/
theorem compactSpectralEmbedding_ae_eq (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (R : ℝ) (f : C(Metric.closedBall (0 : Plane) R, ℂ)) :
    (compactSpectralEmbedding ν R f : Plane → ℂ) =ᵐ[ν] compactSpectralFun R f :=
  (memLp_compactSpectralFun ν R f).coeFn_toLp

/-- Sharp operator norm estimate for the compact spectral embedding. -/
theorem norm_compactSpectralEmbedding_le (ν : Measure Plane) [IsLocallyFiniteMeasure ν] (R : ℝ) :
    ‖compactSpectralEmbedding ν R‖ ≤ Real.sqrt (specMass ν R) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

end Critical2DKPZ.Extensions.ScaleLimit
