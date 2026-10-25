/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabContinuumCutoffMoment
public import Critical2DKPZ.SHF.Flow.ThinSlabCorrectionEndpointMeasure
public import Critical2DKPZ.SHF.Flow.PairingSlabComparisonTail
public import Critical2DKPZ.SHF.Flow.ThinSlabConnectorMomentLimit
import all Critical2DKPZ.SHF.Flow.ThinSlabSeparatedKernelMeasure

/-! # Identifying the first thin-slab error limit with the collision correction -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.DeltaBose
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- The uncut annealed slab product converges in second moment to the free-middle kernel pairing. Square integrability is supplied by `memLp_slabProduct_two`, `integral_sq_sub_slabProduct`, and `memLp_kernelProductCutoffPairing_two`. -/
theorem tendsto_slab_secondMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u v : ℝ} (hs : 0 ≤ s) (hst : s < t) (hv : 0 < v) (hvu : t + v < u)
    (Φ : C_c(Plane × Plane, ℝ)) :
    Tendsto (fun N => ∫ ω,
      kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t (t + v))
        (polymerMeasure ϑ N (t + v) u ω) Φ ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i))
        ∂slabSeparatedFreeEndpointMeasure (ϑ - Real.eulerMascheroniConstant)
          (t - s) v (u - (t + v)))) := by
  let S (N : ℕ) (ω : Disorder) := kernelProductPairing (polymerMeasure ϑ N s t ω)
    (slabMeanKernel ϑ N t (t + v)) (polymerMeasure ϑ N (t + v) u ω) Φ
  let SR (R : ℝ) (N : ℕ) (ω : Disorder) :=
    ∫ q, Φ (q.1.1, q.2.2) * slabMeanKernel ϑ N t (t + v) q.1.2 q.2.1 *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
        ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N (t + v) u ω))
  let A (R : ℝ) := slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
    (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ)
  have htu : t < u := (lt_add_of_pos_right t hv).trans hvu
  apply tendsto_secondMoment_of_cutoffs disorderLaw S SR A
  · obtain ⟨C, hC, hbound⟩ :=
      eventually_slabPairing_sq_bound ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu hv hvu Φ
    exact ⟨C, hC.le, hbound⟩
  · obtain ⟨C, _hC, hBound⟩ := exists_slabMeanKernel_bound ϑ (hs.trans hst.le) hv
    intro R
    exact Eventually.of_forall fun N => by
      let κ : Plane × Plane → ℝ := fun p => slabMeanKernel ϑ N t (t + v) p.1 p.2
      have hκ : Measurable κ := measurable_slabMeanKernel ϑ N t (t + v)
      have hnorm (p : Plane × Plane) : ‖κ p‖ ≤ C := by
        rw [Real.norm_eq_abs]
        exact hBound N p.1 p.2
      have hfull := memLp_kernelProductPairing_two ϑ N s t (t + v) u Φ κ hκ C hnorm
      have hcut := memLp_kernelProductCutoffPairing_two ϑ N s t (t + v) u Φ κ hκ C R hnorm
      exact ⟨hcut.integrable_sq, (hfull.sub hcut).integrable_sq⟩
  · exact slabPairing_cutoff_tail ϑ hs hst htu Φ hv hvu
  · exact fun R => tendsto_slabCutoffPairing_sq ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu hv hvu Φ R
  · exact tendsto_slabContinuumHeatCutoffMoment (ϑ - Real.eulerMascheroniConstant)
      (sub_pos.mpr hst) hv (sub_pos.mpr hvu) Φ

/-- The mean-square difference between the full pairing and the annealed slab product converges to the replica-test pairing with the nonnegative collision-correction measure. Integrability is supplied by `memLp_slabProduct_two`, `integral_sq_sub_slabProduct`, and `memLp_kernelProductCutoffPairing_two`. -/
theorem tendsto_slabError_secondMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u v : ℝ} (hs : 0 ≤ s) (hst : s < t) (hv : 0 < v) (hvu : t + v < u)
    (Φ : C_c(Plane × Plane, ℝ)) :
    Tendsto (fun N => ∫ ω,
      ((∫ p, Φ p ∂polymerMeasure ϑ N s u ω) -
        kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t (t + v))
          (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i))
        ∂slabCorrectionEndpointMeasure (ϑ - Real.eulerMascheroniConstant)
          (t - s) v (u - (t + v)))) := by
  let θ := ϑ - Real.eulerMascheroniConstant
  let Ψ : C_c(Configuration 2 × Configuration 2, ℝ) := slabMomentBlockTensorTest (fun _ => Φ)
  have htime : (t - s) + v + (u - (t + v)) = u - s := by ring
  have hsu : s < u := hst.trans ((lt_add_of_pos_right t hv).trans hvu)
  have hFull : Tendsto (fun N => ∫ ω,
      (∫ p, Φ p ∂polymerMeasure ϑ N s u ω) ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ q, Ψ q ∂slabMomentKernelEndpointMeasure θ
        ((t - s) + v + (u - (t + v))))) := by
    rw [htime, slabMomentKernelEndpointMeasure_integral θ (sub_pos.mpr hsu) Ψ]
    exact polymerPairing_secondMoment_tendsto_of_piMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hsu Φ
  have hSlab := tendsto_slab_secondMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hv hvu Φ
  have hdiff := hFull.sub hSlab
  have hcorrection := integral_slabEndpointCorrection_eq_sub θ
    (sub_pos.mpr hst) hv (sub_pos.mpr hvu) Ψ
  change (∫ q, Ψ q ∂slabMomentKernelEndpointMeasure θ ((t - s) + v + (u - (t + v)))) -
    (∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i)) ∂slabSeparatedFreeEndpointMeasure θ
      (t - s) v (u - (t + v))) =
    (∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i)) ∂slabCorrectionEndpointMeasure θ
      (t - s) v (u - (t + v))) at hcorrection
  rw [hcorrection] at hdiff
  convert hdiff using 1
  funext N
  exact (integral_sq_sub_slabProduct ϑ N hs hst (lt_add_of_pos_right t hv) hvu Φ).2.2

end Critical2DKPZ.SHF.Flow

end
