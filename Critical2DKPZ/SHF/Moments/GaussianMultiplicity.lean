/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Gaussian
import Mathlib.Tactic

/-! # Gaussian exponential moments with repeated coordinates

Finite Gaussian exponential moments depend on the summed coefficients at each repeated space-time coordinate. The replica formula retains triple and quadruple collisions. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.SHF.Moments

/-- The total coefficient of one disorder coordinate, including all its occurrences. -/
def coordinateCoefficient {ι : Type*} [Fintype ι]
    (e : ι → ℕ × Site) (c : ι → ℝ) (z : ℕ × Site) : ℝ :=
  ∑ i, if e i = z then c i else 0

/-- Grouping coefficients at repeated disorder coordinates preserves their weighted sum. -/
theorem sum_coordinateCoefficient {ι : Type*} [Fintype ι]
    (e : ι → ℕ × Site) (c : ι → ℝ) (f : (ℕ × Site) → ℝ) :
    ∑ z : ↥(Finset.univ.image e), coordinateCoefficient e c z.val * f z.val =
      ∑ i, c i * f (e i) := by
  classical
  rw [Finset.sum_coe_sort (Finset.univ.image e)
    (fun z => coordinateCoefficient e c z * f z)]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image e)
    (fun i _ => Finset.mem_image_of_mem e (Finset.mem_univ i))
    (fun i => c i * f (e i))
  rw [← h]
  apply Finset.sum_congr rfl
  intro z _
  simp only [coordinateCoefficient, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rw [hi]
  · exact zero_mul _

/-- Grouping repeated disorder coordinates leaves the finite Gaussian exponential unchanged. -/
theorem finiteExp_group_coordinates {ι : Type*} [Fintype ι]
    (e : ι → ℕ × Site) (c : ι → ℝ) (d : ℝ) :
    Polymer.finiteExp e c d =
      Polymer.finiteExp (fun z : ↥(Finset.univ.image e) => z.val)
        (fun z => coordinateCoefficient e c z.val) d := by
  funext ω
  unfold Polymer.finiteExp
  rw [sum_coordinateCoefficient]

/-- Exact Gaussian integral, without an injectivity hypothesis on the coordinate map. -/
theorem integral_finiteExp_repeated {ι : Type*} [Fintype ι]
    (e : ι → ℕ × Site) (c : ι → ℝ) (d : ℝ) :
    ∫ ω, Polymer.finiteExp e c d ω ∂disorderLaw =
      Real.exp ((∑ z : ↥(Finset.univ.image e),
        (coordinateCoefficient e c z.val) ^ 2 / 2) + d) := by
  rw [finiteExp_group_coordinates]
  exact Polymer.integral_finiteExp _ Subtype.val_injective _ _


end Critical2DKPZ.SHF.Moments
