/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CheckFieldTransfer
public import Critical2DKPZ.Extensions.Definitions.ScaledPairing
import Critical2DKPZ.Extensions.ScaleLimit.ReplacementReduction
import Critical2DKPZ.Extensions.ScaleLimit.MollifierReductions
import Critical2DKPZ.Extensions.ScaleLimit.ZeroReduction
import Critical2DKPZ.Extensions.ScaleLimit.FiniteProbability
import Mathlib.Tactic

/-! # Canonical-width finite-dimensional laws at unit time and the spatial origin -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- At unit time, any nonnegative unit-mass mollifier and canonical widths have
the Brownian finite-dimensional limit at every positive finite collection. -/
theorem canonical_unit_kpz_joint_limit (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1)
    (I : Finset ℝ≥0) (hI : ∀ i ∈ I, 0 < i) :
    TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
      scaledPairing (H 1 0 ω) φ 0 L (i.val : ℝ)) atTop id
      (fun _ => P) (BrownianReal.projectiveFamily I) := by
  obtain ⟨ψ, hψ, hψ1, hψb⟩ := exists_centered_mollifier φ hφ hφ1
  obtain ⟨ρ, hρ, hG⟩ := geometric_kpz_joint_limit ϑ P Z hZ H hH ψ hψ hψ1 hψb
  have hgeom := hG ρ le_rfl I hI
  have hm (L : Set.Ioi (0 : ℝ)) : AEMeasurable
      (fun ω (i : I) => scaledPairing (H 1 0 ω) φ 0 L (i.val : ℝ)) P :=
    aemeasurable_pi_iff.mpr fun i =>
      (memLp_scaledPairing_two ϑ P Z hZ H hH zero_lt_one φ 0 L i.val).aemeasurable
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hgeom _ hm
  have heq : ((fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (H 1 0 ω) φ 0 L (i.val : ℝ)) -
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
        H 1 0 ω (ψ.dilate (Real.sqrt (tau ρ (nL ρ L (i.val : ℝ)))) 0) / Real.sqrt L)) =
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
        (H 1 0 ω (φ.dilate (scaleRadius L (i.val : ℝ)) 0) -
          H 1 0 ω (ψ.dilate (Real.sqrt (tau ρ (nL ρ L (i.val : ℝ)))) 0)) / Real.sqrt L) := by
    funext L ω i
    simp only [Pi.sub_apply, scaledPairing]
    ring
  rw [heq]
  apply tendstoInMeasure_finite_pi P atTop _ 0
  intro i
  simpa only [Pi.zero_apply] using replacement_reduction ϑ P Z hZ H hH φ ψ hφ hψ hφ1 hψ1 hρ
    (by exact_mod_cast hI i.val i.property : 0 < (i.val : ℝ))

end Critical2DKPZ.Extensions.ScaleLimit
