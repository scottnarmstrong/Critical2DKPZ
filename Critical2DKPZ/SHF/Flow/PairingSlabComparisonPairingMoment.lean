/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.PairingSlabComparisonCutoffMoment
public import Critical2DKPZ.SHF.Flow.ThinSlabFullPairingMoment
public import Critical2DKPZ.SHF.Flow.SlabProductsIdentities
public import Critical2DKPZ.SHF.Flow.TwoParticleCancellation

/-! Compactly cut off slab pairings admit continuum moment limits. -/

@[expose] public section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open Critical2DKPZ.DeltaBose
open scoped ENNReal
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- The four-replica compact-test limit is the second-moment limit of the slab connector
pairing with compact middle-coordinate cutoffs. -/
theorem tendsto_slabCutoffPairing_sq (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    {v : ℝ} (hv : 0 < v) (hvu : t + v < u)
    (Φ : C_c(Plane × Plane, ℝ)) (R : ℝ) :
    Tendsto
      (fun N => ∫ ω,
        (∫ q, Φ (q.1.1, q.2.2) * slabMeanKernel ϑ N t (t + v) q.1.2 q.2.1 *
          ballCutoff R q.1.2 * ballCutoff R q.2.1
          ∂((polymerMeasure ϑ N s t ω).prod
            (polymerMeasure ϑ N (t + v) u ω))) ^ 2 ∂disorderLaw)
      atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
        (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ))) := by
  have hsource :
      (fun N => ∫ ω,
        (∫ q, Φ (q.1.1, q.2.2) * slabMeanKernel ϑ N t (t + v) q.1.2 q.2.1 *
          ballCutoff R q.1.2 * ballCutoff R q.2.1
          ∂((polymerMeasure ϑ N s t ω).prod
            (polymerMeasure ϑ N (t + v) u ω))) ^ 2 ∂disorderLaw) =
      (fun N => ∫ ω, ∫ q,
        slabCutoffReplicaValue ϑ N t v R Φ q ∂
          slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
            (polymerMeasure ϑ N (t + v) u ω) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    filter_upwards [] with ω
    let μ := polymerMeasure ϑ N s t ω
    let ν := polymerMeasure ϑ N (t + v) u ω
    have hμ : SigmaFinite μ :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _ μ inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
    have hν : SigmaFinite ν :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _ ν inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N (t + v) u ω)
    have hcut := integral_slabCutoffConnectorValue_eq_cutoffPairing
      μ ν ϑ N t v R Φ
    have hrep := @integral_slabCutoffReplicaValue_eq_sq μ ν hμ hν ϑ N t v R Φ
    calc
      _ = (∫ p, slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2 ∂(μ.prod ν)) ^ 2 := by
        exact congrArg (fun z : ℝ => z ^ 2) hcut.symm
      _ = ∫ q, slabCutoffReplicaValue ϑ N t v R Φ q ∂
          slabTwoBlockPiMeasure μ ν := by
        exact hrep.symm
      _ = _ := by rfl
  rw [hsource]
  exact tendsto_slabCutoffReplicaMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu hv hvu Φ R

/-- Orthogonality bounds the uncut slab second moment by the convergent full-pairing second moment. -/
theorem eventually_slabPairing_sq_bound (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    {v : ℝ} (hv : 0 < v) (hvu : t + v < u)
    (Φ : C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω =>
        kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabMeanKernel ϑ N t (t + v))
          (polymerMeasure ϑ N (t + v) u ω) Φ ^ 2) disorderLaw ∧
      ∫ ω, kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabMeanKernel ϑ N t (t + v))
          (polymerMeasure ϑ N (t + v) u ω) Φ ^ 2 ∂disorderLaw ≤ C := by
  let M : ℝ := ∫ x : Configuration 2, ∫ y : Configuration 2,
    (∏ i : Fin 2, Φ (x i, y i)) *
      (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (u - s) x y).toReal
  let C : ℝ := |M| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hfull : Tendsto
      (fun N => ∫ ω,
        (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw)
      atTop (𝓝 M) := by
    simpa only [M] using polymerPairing_secondMoment_tendsto_of_piMoment
      ϑ hPolymerMomentInput hFlatSixthMomentInput hs (hst.trans htu) Φ
  have hfullBound : ∀ᶠ N : ℕ in atTop,
      ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw ≤ C := by
    filter_upwards [hfull.eventually (Metric.ball_mem_nhds M one_pos)] with N hN
    have hdist : |(∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2
        ∂disorderLaw) - M| < 1 := by
      simpa only [Real.dist_eq] using hN
    dsimp [C]
    have hupper := (abs_lt.mp hdist).2
    have hM : M ≤ |M| := le_abs_self M
    linarith
  let S (N : ℕ) (ω : Disorder) : ℝ :=
    kernelProductPairing (polymerMeasure ϑ N s t ω)
      (slabMeanKernel ϑ N t (t + v))
      (polymerMeasure ϑ N (t + v) u ω) Φ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfullBound] with N hN
  have horth := integral_sq_sub_slabProduct ϑ N hs hst
    (lt_add_of_pos_right t hv) hvu Φ
  have hIntS : Integrable (fun ω => S N ω ^ 2) disorderLaw := by
    simpa [S] using horth.2.1
  have hEq := horth.2.2
  have hEqS :
      (∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω) - S N ω) ^ 2 ∂disorderLaw) =
        (∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw) -
          ∫ ω, S N ω ^ 2 ∂disorderLaw := by
    simpa only [S] using hEq
  have hnonneg : 0 ≤ ∫ ω,
      (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω) - S N ω) ^ 2 ∂disorderLaw :=
    integral_nonneg fun ω => sq_nonneg _
  have hvariance :
      ∫ ω, S N ω ^ 2 ∂disorderLaw ≤
        ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw := by
    rw [hEqS] at hnonneg
    linarith
  exact ⟨hIntS, hvariance.trans hN⟩

/-- The inverse logarithmic factor in the two-particle cancellation estimate vanishes as the
positive slab width tends to zero. -/
theorem tendsto_slab_inverseLog_nhdsGT_zero :
    Tendsto (fun v : ℝ => 1 / (1 + Real.log v⁻¹)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hinv : Tendsto (fun v : ℝ => v⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hlog : Tendsto (fun v : ℝ => Real.log v⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp hinv
  have hden : Tendsto (fun v : ℝ => 1 + Real.log v⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [add_comm] using tendsto_atTop_add_const_right (𝓝[>] (0 : ℝ)) 1 hlog
  have hfun : (fun v : ℝ => 1 / (1 + Real.log v⁻¹)) =
      (fun v => (1 + Real.log v⁻¹)⁻¹) := by
    funext v
    simp only [one_div]
  rw [hfun]
  exact tendsto_inv_atTop_zero.comp hden

end Critical2DKPZ.SHF.Flow

end
