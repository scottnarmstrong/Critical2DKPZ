/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabContinuumConnectorMoment
public import Critical2DKPZ.SHF.Flow.ThinSlabSmoothedSlabConnector
public import Critical2DKPZ.SHF.Flow.MollifiedHeatConnectorConvergence
public import Critical2DKPZ.SHF.Flow.SlabSmoothedBridgeIdentity
import all Critical2DKPZ.SHF.Flow.SmoothedProductCutoffTail
import Mathlib.Tactic

/-! # Continuum second-moment formulas for smoothed slab products -/

@[expose] public noncomputable section
open MeasureTheory Filter Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology
namespace Critical2DKPZ.SHF.Flow

/-- At each fixed compact continuous smoothing profile, the uncut pairing across two touching polymer intervals has a finite second-moment limit. Square integrability is supplied by `memLp_smoothedProductPairing_two`, `memLp_slabSmoothedProduct_two`, and `integral_sq_sub_slabSmoothedProduct`. -/
theorem tendsto_mollified_block_second_moment_with_integrability (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (Φ : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    Integrable (slabConnectorReplicaValue Φ (fun p => k (p.1 - p.2)))
      (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)) ∧
    Tendsto (fun N => ∫ ω,
      smoothedProductPairing (polymerMeasure ϑ N s t ω) k
        (polymerMeasure ϑ N t u ω) Φ ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ z, slabConnectorReplicaValue Φ (fun p => k (p.1 - p.2)) z ∂
        slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t))) := by
  let κ : C(Plane × Plane, ℝ) := ⟨fun p => k (p.1 - p.2), hk.comp (continuous_fst.sub continuous_snd)⟩
  obtain ⟨C, c, hc, hBound⟩ := compactKernel_gaussian_bound k hk hkc
  have h := tendsto_slabConnector_secondMoment_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst le_rfl htu Φ
    (fun _ => κ) (fun _ => κ.continuous.measurable) κ
    (fun _ _ δ hδ => Eventually.of_forall fun _ _ _ => by
      simpa only [sub_self, abs_zero] using hδ.le)
    ⟨C, c, hc, fun _ a b => hBound (a - b)⟩
  simpa only [kernelProductPairing, smoothedProductPairing, κ, ContinuousMap.coe_mk] using h

/-- The second moment of the smoothed pairing converges to the continuum two-block replica integral. Square integrability is supplied by `memLp_smoothedProductPairing_two`, `memLp_slabSmoothedProduct_two`, and `integral_sq_sub_slabSmoothedProduct`. -/
theorem tendsto_mollified_block_second_moment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (Φ : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    Tendsto (fun N => ∫ ω,
      smoothedProductPairing (polymerMeasure ϑ N s t ω) k
        (polymerMeasure ϑ N t u ω) Φ ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ z, slabConnectorReplicaValue Φ (fun p => k (p.1 - p.2)) z ∂
        slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t))) :=
  (tendsto_mollified_block_second_moment_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu Φ k hk hkc).2

/-- At fixed positive slab width and mollifier scale, the annealed smoothed product has a finite second-moment limit. Square integrability is supplied by `memLp_smoothedProductPairing_two`, `memLp_slabSmoothedProduct_two`, and `integral_sq_sub_slabSmoothedProduct`. -/
theorem tendsto_slabSmoothed_secondMoment_with_integrability (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u v e : ℝ} (hs : 0 ≤ s) (hst : s < t) (hv : 0 < v)
    (hvu : t + v < u) (he : 0 < e) (he1 : e ≤ 1)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    Integrable (slabConnectorReplicaValue Φ (slabSmoothedHeatConnector v e w))
      (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - (t + v))) ∧
    Tendsto (fun N => ∫ ω,
      kernelProductPairing (polymerMeasure ϑ N s t ω)
        (slabSmoothedConnector ϑ N t (t + v) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)))
        (polymerMeasure ϑ N (t + v) u ω) Φ ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ z, slabConnectorReplicaValue Φ (slabSmoothedHeatConnector v e w) z ∂
        slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - (t + v)))) := by
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwe : Continuous we := continuous_const.mul
    (hw.comp ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    exact HasCompactSupport.smul_left (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have ht : 0 ≤ t := hs.trans hst.le
  obtain ⟨C, c, hc, hEnvelope⟩ := exists_slabSmoothedConnector_gaussianBound ϑ ht hv w hw hwc hw0 hw1
  apply tendsto_slabConnector_secondMoment_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst (by linarith only [hv]) hvu Φ
    (fun N p => slabSmoothedConnector ϑ N t (t + v) we p.1 p.2)
    (fun N => measurable_slabSmoothedConnector ϑ N t (t + v) we hwe hwec)
    ⟨slabSmoothedHeatConnector v e w, continuous_slabSmoothedHeatConnector he w hw hwc⟩
  · intro K hK δ hδ
    filter_upwards [tendsto_slabSmoothedConnector_uniformOn_compact ϑ ht hv we hwe hwec K hK δ hδ]
      with N hN p hp
    rcases p with ⟨a, b⟩
    simpa only [ContinuousMap.coe_mk, slabSmoothedHeatConnector_eq_integral] using (hN a b hp).le
  · refine ⟨C, c, hc, fun N a b => ?_⟩
    simpa only [norm_sub_rev] using hEnvelope e he he1 N a b


/-- The second moment of the annealed smoothed slab product converges to its continuum two-block replica integral. Square integrability is supplied by `memLp_smoothedProductPairing_two`, `memLp_slabSmoothedProduct_two`, and `integral_sq_sub_slabSmoothedProduct`. -/
theorem tendsto_slabSmoothed_secondMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u v e : ℝ} (hs : 0 ≤ s) (hst : s < t) (hv : 0 < v)
    (hvu : t + v < u) (he : 0 < e) (he1 : e ≤ 1)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    Tendsto (fun N => ∫ ω,
      kernelProductPairing (polymerMeasure ϑ N s t ω)
        (slabSmoothedConnector ϑ N t (t + v) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)))
        (polymerMeasure ϑ N (t + v) u ω) Φ ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ z, slabConnectorReplicaValue Φ (slabSmoothedHeatConnector v e w) z ∂
        slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - (t + v)))) :=
  (tendsto_slabSmoothed_secondMoment_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hv hvu he he1 Φ w hw hwc hw0 hw1).2

/-- The mean-square slab error converges to the difference of the full and annealed continuum second-moment integrals. Square integrability is supplied by `memLp_smoothedProductPairing_two`, `memLp_slabSmoothedProduct_two`, and `integral_sq_sub_slabSmoothedProduct`. -/
theorem tendsto_slabSmoothedSlabError_secondMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u v e : ℝ} (hs : 0 ≤ s) (hst : s < t) (hv : 0 < v)
    (hvu : t + v < u) (he : 0 < e) (he1 : e ≤ 1)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    Tendsto (fun N => ∫ ω,
      (smoothedProductPairing (polymerMeasure ϑ N s t ω)
        (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) (polymerMeasure ϑ N t u ω) Φ -
        kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabSmoothedConnector ϑ N t (t + v) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)))
          (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw) atTop (𝓝 (
        (∫ z, slabConnectorReplicaValue Φ
          (fun p => e⁻¹ ^ 2 * w (e⁻¹ • (p.1 - p.2))) z ∂
          slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)) -
        ∫ z, slabConnectorReplicaValue Φ (slabSmoothedHeatConnector v e w) z ∂
          slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - (t + v)))) := by
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwe : Continuous we := continuous_const.mul
    (hw.comp ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    exact HasCompactSupport.smul_left (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have htu : t < u := lt_trans (lt_add_of_pos_right t hv) hvu
  have hA := tendsto_mollified_block_second_moment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu Φ we hwe hwec
  have hB := tendsto_slabSmoothed_secondMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hv hvu he he1
    Φ w hw hwc hw0 hw1
  have hlimit := hA.sub hB
  convert hlimit using 1
  funext N
  exact (integral_sq_sub_slabSmoothedProduct ϑ N hs hst (lt_add_of_pos_right t hv)
    hvu Φ we hwe hwec).2.2

end Critical2DKPZ.SHF.Flow
end
