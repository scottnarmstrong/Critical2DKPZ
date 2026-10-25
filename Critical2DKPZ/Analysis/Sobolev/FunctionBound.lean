/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.AngularFourier
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The local negative Sobolev bound for functions

Angular Plancherel and monotonicity bound each local negative Sobolev square by the localized
L² integral, including infinite energies, as used in the proof of Lemma 6.4 of
*The Critical 2D KPZ Process*.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ

open Analysis.Sobolev

/-- At order zero the local Sobolev square equals the localized L² energy. -/
theorem localNegSobolevSq_ofFun_zero {f : Plane → ℝ}
    (hf : LocallyIntegrable f volume) (χ : TestFn)
    (hf2 : MemLp (fun x => χ x * f x) 2 volume) :
    localNegSobolevSq 0 (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) f volume ⊤) χ =
      ∫⁻ x : Plane, ENNReal.ofReal ((χ x * f x) ^ 2) := by
  have hi : Integrable (fun x => χ x * f x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport
      χ.continuous χ.hasCompactSupport
  unfold localNegSobolevSq
  simp only [neg_zero, Real.rpow_zero, one_mul]
  simp_rw [← norm_localizedFourier_sq, localizedFourier_ofFun hf]
  exact lintegral_angularFourier_norm_sq hi hf2

/-- For a locally integrable function, the local negative Sobolev square is bounded by its localized L² integral. -/
theorem localNegSobolevSq_ofFun_le_lintegral {a : ℝ} (ha : 0 ≤ a) {f : Plane → ℝ}
    (hf : LocallyIntegrable f volume) (χ : TestFn) :
    localNegSobolevSq a (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) f volume ⊤) χ ≤
      ∫⁻ x : Plane, ENNReal.ofReal ((χ x * f x) ^ 2) := by
  by_cases h2 : MemLp (fun x => χ x * f x) 2 volume
  · exact (localNegSobolevSq_antitone _ χ ha).trans_eq
      (localNegSobolevSq_ofFun_zero hf χ h2)
  · have hi : Integrable (fun x => χ x * f x) := by
      simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport
        χ.continuous χ.hasCompactSupport
    have htop : ∫⁻ x : Plane, ENNReal.ofReal ((χ x * f x) ^ 2) = ⊤ := by
      by_contra hfin
      have hsq := (lintegral_ofReal_ne_top_iff_integrable
        (hi.aestronglyMeasurable.pow 2)
        (Filter.Eventually.of_forall fun x => sq_nonneg (χ x * f x))).mp hfin
      exact h2 ((memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr hsq)
    rw [htop]
    exact le_top

/-- Locally square-integrable functions belong to every local negative Sobolev space of nonnegative order. -/
theorem memLocalNegSobolev_ofFun {a : ℝ} (ha : 0 ≤ a) {f : Plane → ℝ}
    (hf : LocallyIntegrable f volume)
    (hf2 : ∀ χ : TestFn, MemLp (fun x => χ x * f x) 2 volume) :
    MemLocalNegSobolev a (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) f volume ⊤) := by
  intro χ
  apply (localNegSobolevSq_ofFun_le_lintegral ha hf χ).trans_lt
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
    ((hf2 χ).aestronglyMeasurable.pow 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg (χ x * f x))).mpr (hf2 χ).integrable_sq)

end Critical2DKPZ

end
