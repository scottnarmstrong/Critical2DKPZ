/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabMomentCollisionCorrection
public import Critical2DKPZ.SHF.Flow.ThinSlabCompactCorrectionSmall
import all Critical2DKPZ.SHF.Flow.ThinSlabSeparatedKernelMeasure

/-! # Annealing a thin polymer slab -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open Critical2DKPZ.DeltaBose
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow


/-- Replacing a thin polymer slab by its annealed kernel makes the pairing error small in mean square; integrability is supplied by `integral_sq_sub_slabProduct`. -/
theorem polymerMeasure_sub_slabProduct_sq_small_of (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant)) {s t u : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (htu : t < u) (Φ : C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∃ v₀ > 0, ∀ v : ℝ, 0 < v → v < v₀ → ∀ᶠ N : ℕ in atTop,
      ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω) - kernelProductPairing (polymerMeasure ϑ N s t ω)
        (slabMeanKernel ϑ N t (t + v)) (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw ≤ ε := by
  let θ := ϑ - Real.eulerMascheroniConstant
  have _hSemigroup : MomentKernelTwoSemigroup θ := hSG
  let Ψ : C_c(Configuration 2 × Configuration 2, ℝ) := slabMomentBlockTensorTest (fun _ => Φ)
  intro ε hε
  obtain ⟨v₁, hv₁, hsmall⟩ :=
    integral_slabCorrectionEndpointMeasure_uniformly_small θ (u - s) Ψ (ε / 2) (half_pos hε)
  refine ⟨min v₁ (u - t), lt_min hv₁ (sub_pos.mpr htu), ?_⟩
  intro v hv hv₀
  have hv₁' : v < v₁ := hv₀.trans_le (min_le_left _ _)
  have hvu : t + v < u := by
    have h := hv₀.trans_le (min_le_right v₁ (u - t))
    linarith only [h]
  have haT : t - s ≤ u - s := sub_le_sub_right htu.le s
  have hbT : u - (t + v) ≤ u - s :=
    sub_le_sub_left (hst.le.trans (le_add_of_nonneg_right hv.le)) u
  have hbound := hsmall θ (t - s) (u - (t + v)) v le_rfl
    (sub_pos.mpr hst) haT (sub_pos.mpr hvu) hbT hv hv₁'
  have hL : (∫ q, (∏ i : Fin 2, Φ (q.1 i, q.2 i))
      ∂slabCorrectionEndpointMeasure θ (t - s) v (u - (t + v))) < ε := by
    exact ((le_abs_self _).trans hbound).trans_lt (half_lt_self hε)
  have hlimit := tendsto_slabError_secondMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hv hvu Φ
  filter_upwards [hlimit.eventually (Iio_mem_nhds hL)] with N hN
  exact hN.le

end Critical2DKPZ.SHF.Flow

end
