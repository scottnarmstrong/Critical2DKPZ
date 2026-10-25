/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.SHF.Positivity.CompactConvergence
public import Critical2DKPZ.SHF.Moments.WordDominationFlatPairMoment
public import Critical2DKPZ.SHF.Limit.FirstMoment
public import Critical2DKPZ.JointConvergence.MomentConvergence
import Mathlib.Tactic

/-! # Exact first moments of nonnegative compact SHF tests -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Moments Critical2DKPZ.SHF.Positivity
open scoped CompactlySupported Topology

namespace Critical2DKPZ.NonGaussian

/-- A nonnegative compact SHF pairing is integrable and its expectation is the corresponding
heat-kernel pairing. -/
theorem integrable_and_integral_compactPairing_eq (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (φ : C_c(Plane × Plane, ℝ)) (hφ : ∀ p, 0 ≤ φ p) :
    Integrable (fun ω => ∫ p, φ p ∂Z s t ω) P ∧
      (∫ ω, ∫ p, φ p ∂Z s t ω ∂P) =
        ∫ p : Plane × Plane, φ p * heatKernel (t - s) (p.2 - p.1) := by
  let X : ℕ → Disorder → ℝ := fun N ω => ∫ p, φ p ∂polymerMeasure ϑ N s t ω
  let Y : Ω → ℝ := fun ω => ∫ p, φ p ∂Z s t ω
  have hD : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P := by
    have h := (isCriticalSHF_compact_pairings_tendsto P Z hZ (fun _ : Fin 1 => s)
      (fun _ => t) (fun _ => ⟨hs, hst⟩) (fun _ => φ)).continuous_comp (continuous_apply (0 : Fin 1))
    simpa only [Function.comp_def, X, Y] using h
  obtain ⟨B, _hB, hBounds⟩ := eventually_integral_compactAbs_pairing_product_le ϑ φ φ
    (τ := (t - s) / 2) (T := t) (by linarith only [hst])
  have hAbsEq (N : ℕ) (ω : Disorder) :
      (∫ p : Plane × Plane, compactAbs φ p * rescaledP2P ϑ N s t p ω) = X N ω := by
    dsimp [X]
    rw [integral_polymerMeasure]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      change |φ p| * _ = φ p * _
      rw [abs_of_nonneg (hφ p)]
  have hInt : ∀ᶠ N : ℕ in atTop, Integrable (fun ω => |X N ω| ^ (2 : ℝ)) disorderLaw := by
    filter_upwards [hBounds] with N hN
    have h := (hN s t hs (by linarith only [hst]) le_rfl).1
    simpa only [hAbsEq, ← pow_two, Real.rpow_two, sq_abs] using h
  have hBound : ∀ᶠ N : ℕ in atTop, (∫ ω, |X N ω| ^ (2 : ℝ) ∂disorderLaw) ≤ B := by
    filter_upwards [hBounds] with N hN
    have h := (hN s t hs (by linarith only [hst]) le_rfl).2
    simpa only [hAbsEq, ← pow_two, Real.rpow_two, sq_abs] using h
  have hLimit := JointConvergence.integrable_rpow_limit_of_tendstoInDistribution hD
    (by norm_num : (0 : ℝ) < 2) hInt hBound
  have hMem : MemLp Y 2 P := by
    apply (memLp_two_iff_integrable_sq hD.aemeasurable_limit.aestronglyMeasurable).mpr
    simpa only [Real.rpow_two, sq_abs] using hLimit.1
  have hConv := JointConvergence.tendsto_integral_of_tendstoInDistribution hD
    (by norm_num : (1 : ℝ) < 2) hBound hInt
  have hAnnealed := integral_polymerMeasure_mean ϑ hs hst φ
  exact ⟨hMem.integrable (by norm_num), tendsto_nhds_unique hConv hAnnealed⟩

end Critical2DKPZ.NonGaussian

end
