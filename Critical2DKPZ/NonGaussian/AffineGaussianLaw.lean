/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.GaussianOrder
public import Critical2DKPZ.EhrhardType.Characterization
import Mathlib.Probability.HasLaw

/-! # Ehrhard laws dominated by an affine Gaussian law -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open Critical2DKPZ.EhrhardType

namespace Critical2DKPZ.NonGaussian

/-- An Ehrhard law bounded above by a Gaussian plus a constant is an affine Gaussian law
with the same slope. -/
theorem exists_affine_law_of_isEhrhardType_of_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (s : ℝ) (hs : 0 ≤ s)
    (hXlaw : P.map X = (gaussianReal 0 1).map (fun z => s * z)) (K : ℝ)
    (hbound : ∀ᵐ ω ∂P, Y ω ≤ X ω + K) (hYE : IsEhrhardType (P.map Y)) :
    ∃ b : ℝ, P.map Y = (gaussianReal 0 1).map (fun z => s * z + b) := by
  obtain ⟨h, hh, hc, hrep⟩ := exists_monotone_convex_representative hYE
  have hshift : P.map (fun ω => X ω + K) =
      (gaussianReal 0 1).map (fun z => s * z + K) := by
    calc
      _ = (P.map X).map (fun x : ℝ => x + K) :=
        (AEMeasurable.map_map_of_aemeasurable (g := fun x : ℝ => x + K) (f := X) (by fun_prop) hX).symm
      _ = _ := by
        rw [hXlaw, Measure.map_map (g := fun x : ℝ => x + K) (f := fun z : ℝ => s * z) (by fun_prop) (by fun_prop)]
        rfl
  have horder (a : ℝ) : ((gaussianReal 0 1).map (fun z => s * z + K)) (Iio a) ≤
      ((gaussianReal 0 1).map h) (Iio a) := by
    rw [← hshift, ← hrep, Measure.map_apply_of_aemeasurable (f := fun ω => X ω + K) (hX.add aemeasurable_const) measurableSet_Iio,
      Measure.map_apply_of_aemeasurable hY measurableSet_Iio]
    apply measure_mono_ae
    filter_upwards [hbound] with ω hω
    exact fun hx => hω.trans_lt hx
  have hm : Monotone (fun z : ℝ => s * z + K) :=
    fun x y hxy => add_le_add (mul_le_mul_of_nonneg_left hxy hs) le_rfl
  have hupper := monotone_le_of_standardGaussian_sublevel_le hh hm (by fun_prop) horder
  have haff := eq_affine_of_convex_bounded_above_sub hc s K hupper
  refine ⟨h 0, ?_⟩
  rw [hrep]
  congr 1
  exact funext haff

/-- The law of `sG + b`, for standard Gaussian `G`, is Gaussian with mean `b` and variance `s²`. -/
theorem standardGaussian_map_affine (s b : ℝ) :
    (gaussianReal 0 1).map (fun z => s * z + b) = gaussianReal b (NNReal.mk (s ^ 2) (sq_nonneg s)) := by
  have he : (fun z : ℝ => s * z + b) = (fun z => z + b) ∘ (fun z => s * z) := rfl
  rw [he, ← Measure.map_map (g := fun z : ℝ => z + b) (f := fun z : ℝ => s * z) (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  simp only [mul_zero, zero_add, mul_one]

/-- A centered Ehrhard law bounded above by a Gaussian plus a constant has the same Gaussian law,
including when the variance is zero. -/
theorem map_eq_of_isEhrhardType_of_le_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (s : ℝ) (hs : 0 ≤ s)
    (hXlaw : P.map X = (gaussianReal 0 1).map (fun z => s * z))
    (hY0 : ∫ ω, Y ω ∂P = 0) (K : ℝ)
    (hbound : ∀ᵐ ω ∂P, Y ω ≤ X ω + K) (hYE : IsEhrhardType (P.map Y)) :
    P.map Y = P.map X := by
  obtain ⟨b, hb⟩ := exists_affine_law_of_isEhrhardType_of_le P X Y hX hY s hs hXlaw K hbound hYE
  have hYlaw : HasLaw Y (gaussianReal b (NNReal.mk (s ^ 2) (sq_nonneg s))) P :=
    ⟨hY, hb.trans (standardGaussian_map_affine s b)⟩
  have hb0 : b = 0 := by
    have hm := hYlaw.integral_eq
    rw [integral_id_gaussianReal, hY0] at hm
    exact hm.symm
  rw [hb0] at hb
  calc
    P.map Y = (gaussianReal 0 1).map (fun z => s * z) := by simpa only [add_zero] using hb
    _ = P.map X := hXlaw.symm

end Critical2DKPZ.NonGaussian

end
