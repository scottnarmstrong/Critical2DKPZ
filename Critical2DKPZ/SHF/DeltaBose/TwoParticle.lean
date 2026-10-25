/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.Tactic

/-! The two-particle kernel has a two-center integral representation with coefficient `4π` and center variance `(u-r)/2`. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

instance spectator_pairTwo_isEmpty : IsEmpty (Spectator pairTwo) := by
  refine ⟨fun i => ?_⟩
  have hi := i.1.isLt
  have h0 := i.2.1
  have h1 := i.2.2
  simp only [pairTwo] at h0 h1
  have h0' : i.1.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : i.1.val ≠ 1 := fun h => h1 (Fin.ext h)
  omega

/-- At two particles the collision embedding duplicates the sole center. -/
theorem collisionEmbedding_pairTwo (y : FusedConfiguration pairTwo) :
    collisionEmbedding pairTwo y = fun _ => y.1 := by
  funext i
  fin_cases i <;> simp [collisionEmbedding, pairTwo]

/-- The incoming block is the product of the two heat strands. -/
theorem incomingKernel_pairTwo (r : ℝ) (z : FusedConfiguration pairTwo)
    (x : Configuration 2) :
    incomingKernel pairTwo r z x = heatKernel r (z.1 - x 0) * heatKernel r (z.1 - x 1) := by
  simp only [incomingKernel, freeKernel, collisionEmbedding_pairTwo, Fin.prod_univ_two]

/-- The resummed two-particle block has no spectator factors. -/
theorem collisionKernel_pairTwo (θ t : ℝ) (z w : FusedConfiguration pairTwo) :
    collisionKernel pairTwo θ t z w =
      4 * Real.pi * scalarDensity θ t * heatKernel (t / 2) (w.1 - z.1) := by
  simp only [collisionKernel, Finset.univ_eq_empty, Finset.prod_empty, mul_one]

/-- Integrating an empty spectator configuration adds no volume factor. -/
theorem lintegral_fused_pairTwo {f : Plane → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration pairTwo, f z.1) = ∫⁻ z : Plane, f z := by
  have : IsProbabilityMeasure (volume : Measure (Spectator pairTwo → Plane)) := by
    refine ⟨?_⟩
    change (Measure.pi (fun _ : Spectator pairTwo => (volume : Measure Plane))) univ = 1
    rw [Measure.pi_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
  exact (measurePreserving_fst (μ := (volume : Measure Plane))
    (ν := (volume : Measure (Spectator pairTwo → Plane)))).lintegral_comp hf

/-- Removing both empty spectator configurations preserves the two-center integral. -/
theorem lintegral_fused_pairTwo_pair {F : Plane → Plane → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ z : FusedConfiguration pairTwo, ∫⁻ w : FusedConfiguration pairTwo, F z.1 w.1) =
      ∫⁻ z : Plane, ∫⁻ w : Plane, F z w := by
  calc (∫⁻ z : FusedConfiguration pairTwo, ∫⁻ w : FusedConfiguration pairTwo, F z.1 w.1)
      = ∫⁻ z : FusedConfiguration pairTwo, ∫⁻ w : Plane, F z.1 w := by
        apply lintegral_congr
        intro z
        exact lintegral_fused_pairTwo (f := F z.1)
          (hF.comp (show Measurable (fun w : Plane => (z.1, w)) from
            measurable_const.prodMk measurable_id))
    _ = ∫⁻ z : Plane, ∫⁻ w : Plane, F z w :=
      lintegral_fused_pairTwo (f := fun z => ∫⁻ w : Plane, F z w)
        (hF.lintegral_prod_right (ν := volume))

/-- The exact two-planar-center expression for the resummed collision contribution. -/
theorem twoParticleCorrection_eq_planar_integral (θ h : ℝ) (x y : Configuration 2) :
    twoParticleCorrection θ h x y =
      ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, ∫⁻ z : Plane, ∫⁻ w : Plane,
        ENNReal.ofReal (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r) *
          heatKernel ((u - r) / 2) (w - z)) *
        ENNReal.ofReal (heatKernel (h - u) (y 0 - w) * heatKernel (h - u) (y 1 - w)) := by
  rw [twoParticleCorrection_eq_integral]
  apply lintegral_congr
  intro r
  apply lintegral_congr
  intro u
  simp only [incomingKernel_pairTwo, collisionKernel_pairTwo, freeKernel,
    collisionEmbedding_pairTwo, Fin.prod_univ_two]
  let F : Plane → Plane → ℝ≥0∞ := fun z w =>
    ENNReal.ofReal (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r) * heatKernel ((u - r) / 2) (w - z)) *
    ENNReal.ofReal (heatKernel (h - u) (y 0 - w) * heatKernel (h - u) (y 1 - w))
  have hF : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    unfold heatKernel
    fun_prop
  change (∫⁻ z : FusedConfiguration pairTwo, ∫⁻ w : FusedConfiguration pairTwo, F z.1 w.1) =
    ∫⁻ z : Plane, ∫⁻ w : Plane, F z w
  exact lintegral_fused_pairTwo_pair hF

end Critical2DKPZ.DeltaBose
