/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeFubini
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureHorizon
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Uniform bounds for complete continuum two-particle futures -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported

/-- The continuum tested future is uniformly bounded up to the zero horizon
on every bounded interval of remaining times. Its time-integrability companion
is `integrableOn_pairTwoTestedSpatialProfile_time`. -/
theorem exists_pairTwoContinuumFuture_bound
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 0 ≤ q → q ≤ T → ∀ a : Fin 2 → Plane, ∀ z : Plane,
      |pairTwoContinuumFuture θ q φ a z| ≤ C := by
  let K : ℝ := 16 * Real.pi * ‖(φ 0).toBoundedContinuousFunction‖ *
    ‖(φ 1).toBoundedContinuousFunction‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : IntegrableOn (DeltaBose.scalarDensity θ) (Set.Ioc 0 T) :=
    Renewal.integrableOn_scalarDensity_Ioc θ T
  have hρnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 T)] DeltaBose.scalarDensity θ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (DeltaBose.scalarDensity_pos θ hu.1).le
  have hiρ : IntervalIntegrable (DeltaBose.scalarDensity θ) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hρ
  have hI : 0 ≤ ∫ u in (0 : ℝ)..T, DeltaBose.scalarDensity θ u := by
    rw [intervalIntegral.integral_of_le hT.le]
    exact setIntegral_nonneg_of_ae_restrict hρnonneg
  refine ⟨K * (∫ u in (0 : ℝ)..T, DeltaBose.scalarDensity θ u), mul_nonneg hK hI, ?_⟩
  intro q hq hqT a z
  have hb := (abs_integral_pairTwoTestedSpatialProfile_le_scalar θ q φ a z
    (s := 0) (t := q) le_rfl hq le_rfl).2
  have hmono := intervalIntegral.integral_mono_interval (a := 0) (b := q)
    (c := 0) (d := T) le_rfl hq hqT hρnonneg hiρ
  exact hb.trans (mul_le_mul_of_nonneg_left hmono hK)

end Critical2DKPZ.SHF.Moments
