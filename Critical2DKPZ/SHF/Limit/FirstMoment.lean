/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Basic

/-! # First moments of the polymer random measures -/

@[expose] public section

open MeasureTheory Filter
open scoped CompactlySupported Topology

noncomputable section

namespace Critical2DKPZ.SHF.Limit

/-- Pairing a polymer measure against a real-valued function is integration against its density. -/
theorem integral_polymerMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (f : Plane × Plane → ℝ) :
    ∫ p, f p ∂(polymerMeasure ϑ N s t ω) =
      ∫ p, f p * rescaledP2P ϑ N s t p ω := by
  have hpair : Measurable (fun q : (Plane × Plane) × Disorder =>
      rescaledP2P ϑ N s t q.1 q.2) :=
    SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s t
  have hsection : Measurable (fun p : Plane × Plane => rescaledP2P ϑ N s t p ω) := by
    exact hpair.of_uncurry_right
  have hmeas : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (rescaledP2P ϑ N s t p ω)) :=
    ENNReal.measurable_ofReal.comp hsection
  rw [polymerMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_ofReal (SHF.Moments.rescaledP2P_nonneg ϑ N s t p ω)]
  simp only [smul_eq_mul]
  rw [mul_comm]

/-- The annealed compact pairing converges to the heat-kernel pairing. -/
theorem integral_polymerMeasure_mean (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (f : C_c(Plane × Plane, ℝ)) :
    Tendsto (fun N => ∫ ω, ∫ p, f p ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw)
      atTop (𝓝 (∫ p : Plane × Plane, f p * heatKernel (t - s) (p.2 - p.1))) := by
  simp_rw [integral_polymerMeasure]
  exact SHF.Moments.firstMoment_pairing_limit ϑ hs hst f.continuous f.hasCompactSupport

end Critical2DKPZ.SHF.Limit

end
