/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseInputs
import Critical2DKPZ.SHF.Flow.PiMomentConvergence

/-! Compact polymer pairings admit second-moment limits. -/

@[expose] public section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.DeltaBose
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow


/-- The compact full-pairing second moment converges to its kernel integral, with finite-scale integrability supplied by `memLp_polymerPairing_two`. -/
theorem polymerPairing_secondMoment_tendsto_of_piMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (Φ : C_c(Plane × Plane, ℝ)) :
    Tendsto
      (fun N => ∫ ω,
        (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw)
      atTop
      (nhds (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i : Fin 2, Φ (x i, y i)) *
          (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (u - s) x y).toReal)) := by
  let F : (Fin 2 → Plane × Plane) → ℝ := fun q => ∏ i, Φ (q i)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  let K : Set (Fin 2 → Plane × Plane) := Set.univ.pi fun _ => tsupport Φ
  have hK : IsCompact K := isCompact_univ_pi fun _ => Φ.hasCompactSupport
  have hFsupport : Function.support F ⊆ K := by
    intro q hq
    apply Set.mem_univ_pi.mpr
    intro i
    by_contra hi
    have hzero : Φ (q i) = 0 := image_eq_zero_of_notMem_tsupport hi
    change F q ≠ 0 at hq
    exact hq (by simp only [F, Finset.prod_eq_zero (Finset.mem_univ i), hzero])
  have hFc : HasCompactSupport F := HasCompactSupport.of_support_subset_isCompact hK hFsupport
  have hPi := polymerMeasure_pi_moment_tendsto_of ϑ hPolymerMomentInput hFlatSixthMomentInput 2
    (by norm_num) (by norm_num) hs hsu F hF hFc
  have hsource :
      (fun N => ∫ ω,
        (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw) =
      (fun N => ∫ ω, ∫ q, F q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N s u ω) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    filter_upwards [] with ω
    have hSigma : SigmaFinite (polymerMeasure ϑ N s u ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N s u ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N s u ω)
    have hprod := @MeasureTheory.integral_fintype_prod_eq_prod ℝ (Fin 2)
      inferInstance inferInstance (fun _ => Plane × Plane) (fun _ p => Φ p)
      (mE := fun _ => inferInstance)
      (μ := fun _ => polymerMeasure ϑ N s u ω)
      (fun _ => hSigma)
    simpa [F, pow_two] using hprod.symm
  rw [hsource]
  simpa only [F] using hPi

end Critical2DKPZ.SHF.Flow

end
