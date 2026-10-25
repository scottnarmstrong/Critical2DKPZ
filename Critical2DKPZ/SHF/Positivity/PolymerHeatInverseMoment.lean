/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.PolymerHeatSecondMoment
public import Critical2DKPZ.SHF.Positivity.SummableInverseMoments
import Mathlib.Tactic

/-! # Inverse moments of the polymer heat-start pairing -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology
open Critical2DKPZ.SHF.Limit

namespace Critical2DKPZ.SHF.Positivity

/-- For all sufficiently large lattice scales, the reciprocal heat-start pairing is integrable with uniformly bounded expectation. -/
theorem polymer_heat_pairing_inv_moment_le (ϑ : ℝ) {s t δ : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (∫ p, heatKernel δ (p.1 - x)
        ∂(polymerMeasure ϑ N s t ω))⁻¹) disorderLaw ∧
      ∫ ω, (∫ p, heatKernel δ (p.1 - x)
        ∂(polymerMeasure ϑ N s t ω))⁻¹ ∂disorderLaw ≤ C := by
  obtain ⟨C, hC⟩ := polymer_heat_pairing_sq_integral_bounded ϑ hs hst hδ x
  refine ⟨C, ?_⟩
  filter_upwards [hC, Filter.eventually_ge_atTop 1] with N hsecond hN
  let a := evenCeil (N * s)
  let b := evenCeil (N * t)
  let ν : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x)
  let H : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω)
  let F : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω
  have hN1 : 1 ≤ N := hN
  have hprofile := heatCellProfile_bounds hN1 hδ x
  have hβ : 0 ≤ criticalBeta ϑ N := Real.sqrt_nonneg _
  have hProfileInverseMomentInput := integral_rpow_neg_profileP2Fun_le_of_summable hβ a b ν
    hprofile.1 hprofile.2.1 hprofile.2.2.1 (p := 1) (by norm_num)
  have hexp : (1 : ℝ) * (1 + 1) / 2 = 1 := by norm_num
  have hProfileInverseMomentInputBound := hProfileInverseMomentInput.2
  rw [hexp, Real.rpow_one] at hProfileInverseMomentInputBound
  have hProfileInverseMomentInput' : Integrable (fun ω => F ω ^ (-1 : ℝ)) disorderLaw ∧
      ∫ ω, F ω ^ (-1 : ℝ) ∂disorderLaw ≤ ∫ ω, F ω ^ 2 ∂disorderLaw := by
    constructor
    · simpa only [F] using hProfileInverseMomentInput.1
    · simpa only [F, Real.rpow_neg_one] using hProfileInverseMomentInputBound
  have hEq : H =ᵐ[disorderLaw] F := by
    filter_upwards [ae_integral_heatKernel_polymerMeasure_eq ϑ hN1 hs hst hδ x] with ω hω
    simpa only [H, F, a, b, ν] using hω
  have hInvEq : (fun ω => H ω ^ (-1 : ℝ)) =ᵐ[disorderLaw]
      fun ω => F ω ^ (-1 : ℝ) := hEq.mono fun ω hω => congrArg (fun z : ℝ => z ^ (-1 : ℝ)) hω
  have hInvInt : Integrable (fun ω => H ω ^ (-1 : ℝ)) disorderLaw :=
    hProfileInverseMomentInput'.1.congr hInvEq.symm
  have hInvEq' : (fun ω => H ω ^ (-1 : ℝ)) =ᵐ[disorderLaw]
      fun ω => (H ω)⁻¹ := by
    filter_upwards [] with ω
    exact Real.rpow_neg_one (H ω)
  have hHeatInvInt : Integrable (fun ω => (H ω)⁻¹) disorderLaw :=
    hInvInt.congr hInvEq'
  have hSqEq : (fun ω => F ω ^ 2) =ᵐ[disorderLaw] fun ω => H ω ^ 2 :=
    hEq.mono fun ω hω => congrArg (fun z : ℝ => z ^ 2) hω.symm
  have hF2Int : Integrable (fun ω => F ω ^ 2) disorderLaw := hsecond.1.congr hSqEq.symm
  have hSqIntegral : (∫ ω, F ω ^ 2 ∂disorderLaw) =
      ∫ ω, H ω ^ 2 ∂disorderLaw := integral_congr_ae hSqEq
  have hInvBound : ∫ ω, (H ω)⁻¹ ∂disorderLaw ≤ C := by
    calc
      _ = ∫ ω, H ω ^ (-1 : ℝ) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact (Real.rpow_neg_one (H ω)).symm
      _ = ∫ ω, F ω ^ (-1 : ℝ) ∂disorderLaw := integral_congr_ae hInvEq
      _ ≤ ∫ ω, F ω ^ 2 ∂disorderLaw := hProfileInverseMomentInput'.2
      _ = ∫ ω, H ω ^ 2 ∂disorderLaw := hSqIntegral
      _ ≤ C := hsecond.2
  exact ⟨by simpa only [H] using hHeatInvInt, by simpa only [H] using hInvBound⟩

end Critical2DKPZ.SHF.Positivity

end
