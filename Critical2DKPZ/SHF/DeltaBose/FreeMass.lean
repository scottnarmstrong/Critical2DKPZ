/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Mass and convolution of the free particle kernel

The scalar heat identities from heat-kernel and Sobolev analysis tensorize with the ordinary product
Lebesgue measure on particle configurations. These identities supply the free
strand contractions used in collision diagrams.
-/

public section

open MeasureTheory

namespace Critical2DKPZ.DeltaBose

/-- Absolute integrability of the free kernel in its terminal configuration. -/
theorem integrable_freeKernel_right (n : ℕ) {t : ℝ} (ht : 0 < t) (x : Configuration n) :
    Integrable (freeKernel n t x) :=
  Integrable.fintype_prod fun i => (integrable_heatKernel ht).comp_sub_right (x i)

/-- The free kernel has total mass one. -/
theorem integral_freeKernel_right (n : ℕ) {t : ℝ} (ht : 0 < t) (x : Configuration n) :
    ∫ y : Configuration n, freeKernel n t x y = 1 := by
  change (∫ y : Fin n → Plane, ∏ i, heatKernel t (y i - x i)) = 1
  rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin n) (z : Plane) => heatKernel t (z - x i))]
  simp only [integral_heatKernel_sub ht, Finset.prod_const_one]

/-- The same mass identity in the initial configuration. -/
theorem integral_freeKernel_left (n : ℕ) {t : ℝ} (ht : 0 < t) (y : Configuration n) :
    ∫ x : Configuration n, freeKernel n t x y = 1 := by
  simp_rw [freeKernel_symm n t]
  exact integral_freeKernel_right n ht y

/-- Integrability in the initial configuration follows from symmetry. -/
theorem integrable_freeKernel_left (n : ℕ) {t : ℝ} (ht : 0 < t) (y : Configuration n) :
    Integrable (fun x : Configuration n => freeKernel n t x y) := by
  simp_rw [freeKernel_symm n t]
  exact integrable_freeKernel_right n ht y


end Critical2DKPZ.DeltaBose
