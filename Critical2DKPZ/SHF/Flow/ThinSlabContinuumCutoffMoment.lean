/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabFreeEndpointMeasure
public import Critical2DKPZ.SHF.Flow.ThinSlabReplicaCutoff
public import Critical2DKPZ.SHF.Flow.PairingSlabComparisonHeatTest
import all Critical2DKPZ.SHF.Flow.ThinSlabSeparatedKernelMeasure

/-! # Identifying the uncut continuum second moment of an annealed slab -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Removing the continuum middle-coordinate cutoffs gives integration of the replica endpoint
test against the free-middle composition measure. This includes arbitrary signed compact tests. -/
theorem tendsto_slabContinuumHeatCutoffMoment (θ : ℝ) {a v b : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) (Φ : C_c(Plane × Plane, ℝ)) :
    Tendsto (fun R : ℝ => slabSeparatedMomentIntegral θ a b
      (slabHeatCutoffReplicaTest v R Φ)) atTop
      (𝓝 (∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i))
        ∂slabSeparatedFreeEndpointMeasure θ a v b)) := by
  let Ψ : C_c(Configuration 2 × Configuration 2, ℝ) :=
    slabMomentBlockTensorTest (fun _ => Φ)
  have hΨ (x y : Configuration 2) : Ψ (x, y) = ∏ i : Fin 2, Φ (x i, y i) := rfl
  let π := slabSeparatedMomentPiMeasure θ a b
  let W (p : Fin 2 → Configuration 2 × Configuration 2) : ℝ≥0∞ :=
    ENNReal.ofReal (freeKernel 2 v (p 0).2 (p 1).1)
  let endpoint (p : Fin 2 → Configuration 2 × Configuration 2) := ((p 0).1, (p 1).2)
  have hEnd : Measurable endpoint := by fun_prop
  have hW : Measurable W := by
    have hp : Measurable (fun p : Fin 2 → Configuration 2 × Configuration 2 =>
        (v, ((p 0).2, (p 1).1))) := by fun_prop
    exact ((measurable_freeKernel 2).comp hp).ennreal_ofReal
  have hΨfull : Integrable (Ψ : Configuration 2 × Configuration 2 → ℝ)
      (slabMomentKernelEndpointMeasure θ (a + v + b)) :=
    integrable_compactTest_of_locallyFinite _
      (locallyFinite_momentKernelMeasure 2 θ (add_pos (add_pos ha hv) hb)) Ψ
  have hΨfree := hΨfull.mono_measure (slabSeparatedFreeEndpointMeasure_le_full θ ha hv hb)
  have hPath : Integrable (fun p => Ψ (endpoint p)) (π.withDensity W) := by
    exact (integrable_map_measure Ψ.continuous.aestronglyMeasurable hEnd.aemeasurable).mp hΨfree
  have hlimit := integral_slabReplicaCutoff_tendsto (π.withDensity W) hPath
  have hsource (R : ℝ) : slabSeparatedMomentIntegral θ a b
      (slabHeatCutoffReplicaTest v R Φ) =
      ∫ p, Ψ (endpoint p) * slabReplicaCutoff R p ∂π.withDensity W := by
    have hfinite : ∀ᵐ p ∂π, W p < ⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [integral_withDensity_eq_integral_toReal_smul hW hfinite]
    unfold slabSeparatedMomentIntegral
    apply integral_congr_ae
    filter_upwards [] with p
    have hnonneg : 0 ≤ freeKernel 2 v (p 0).2 (p 1).1 := (freeKernel_pos 2 hv _ _).le
    simp only [W, ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
    simp [slabSeparatedGroupedTest_apply, slabHeatCutoffReplicaTest_apply,
      slabHeatCutoffConnectorValue, slabSeparatedArrayHomeomorph, slabSeparatedArrayEquiv,
      freeKernel, slabReplicaCutoff, endpoint, hΨ, Fin.prod_univ_two]
    ring
  have htarget : (∫ p, Ψ (endpoint p) ∂π.withDensity W) =
      ∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i))
        ∂slabSeparatedFreeEndpointMeasure θ a v b := by
    have hmap := integral_map (μ := π.withDensity W) hEnd.aemeasurable
      Ψ.continuous.aestronglyMeasurable
    change (∫ p, Ψ (endpoint p) ∂π.withDensity W) =
      ∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i)) ∂(π.withDensity W).map endpoint
    calc
      _ = ∫ q, Ψ q ∂(π.withDensity W).map endpoint := hmap.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun q => hΨ q.1 q.2)
  simpa only [← hsource, htarget] using hlimit

end Critical2DKPZ.SHF.Flow

end
