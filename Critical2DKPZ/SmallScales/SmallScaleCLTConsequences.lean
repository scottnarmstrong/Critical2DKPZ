/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.Definitions.TestFnCompAffine
public import Critical2DKPZ.SmallScales.Inputs
public import Critical2DKPZ.SmallScales.SmallBallFromCLT

/-! # Probability consequences of the small-scale KPZ central limit theorem -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction Distributions Topology

universe u

namespace Critical2DKPZ.SmallScales


/-- Translation invariance makes the law of a dilated test pairing independent of its center. -/
theorem measure_abs_dilate_eq_of_KpzTransportAt
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hR7 : KpzTransportAt P H)
    (t ε k : ℝ) (ht : 0 < t) (φ : TestFn) (x : Plane) :
    P {ω | |H t 0 ω (φ.dilate ε x)| ≤ k} =
      P {ω | |H t 0 ω (φ.dilate ε 0)| ≤ k} := by
  let R : Plane ≃ₗᵢ[ℝ] Plane := LinearIsometryEquiv.refl ℝ Plane
  have hdet : LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 := by
    simp [R]
  have htest : (φ.dilate ε x).compAffine x R = φ.dilate ε 0 := by
    ext y
    simp [TestFn.compAffine, TestFn.dilate, R, sub_eq_add_neg]
  let htrans := hR7 1 (fun _ : Fin 1 => t) (fun _ => ht) (fun _ => φ.dilate ε x)
  have hlaw := htrans.2 x R hdet
  have hbase : AEMeasurable
      (fun ω (i : Fin 1) => H t 0 ω (φ.dilate ε 0)) P := by
    apply AEMeasurable.of_eval
    intro i
    exact (hR7 1 (fun _ : Fin 1 => t) (fun _ => ht) (fun _ => φ.dilate ε 0)).1 i
  have hshift : AEMeasurable
      (fun ω (i : Fin 1) => H t 0 ω (φ.dilate ε x)) P := by
    apply AEMeasurable.of_eval
    intro i
    exact htrans.1 i
  let fbase : Ω → Fin 1 → ℝ := fun ω _ => H t 0 ω (φ.dilate ε 0)
  let fshift : Ω → Fin 1 → ℝ := fun ω _ => H t 0 ω (φ.dilate ε x)
  have hmap : P.map fbase = P.map fshift := by
    simpa only [fbase, fshift, htest] using hlaw
  let S : Set (Fin 1 → ℝ) := {v | |v 0| ≤ k}
  have hS : MeasurableSet S := by
    exact measurableSet_le (measurable_abs.comp (measurable_pi_apply 0)) measurable_const
  calc
    P {ω | |H t 0 ω (φ.dilate ε x)| ≤ k} =
        P.map fshift S := by
      rw [Measure.map_apply_of_aemeasurable hshift hS]
      congr 1
    _ = P.map fbase S := by rw [hmap]
    _ = P {ω | |H t 0 ω (φ.dilate ε 0)| ≤ k} := by
      rw [Measure.map_apply_of_aemeasurable hbase hS]
      congr 1


end Critical2DKPZ.SmallScales

end
