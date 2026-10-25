/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.ScalarCLT
import Critical2DKPZ.Extensions.ScaleLimit.EventualLawTransfer
import Mathlib.Tactic

/-! # Regular initial values for the geometric heat-start field

The equal-endpoint pairing at index zero is unconstrained by the flow axioms.
Assigning zero there gives an integrable sequence at every index. The clock
`sqrt (1 + log n)` is positive even at the initial indices and has the same
asymptotic normalization as `sqrt (log n)`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The geometric heat-start logarithm with a regular value at index zero. -/
def geometricField {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n : ℕ) (ω : Ω) : ℝ := if n = 0 then 0 else Fheat Z (tau ρ n) 0 ω

/-- A strictly positive version of the square-root logarithmic clock. -/
def geometricNormalizer (n : ℕ) : ℝ := Real.sqrt (1 + Real.log n)

/-- Positive indices retain the original field. -/
theorem geometricField_of_pos {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) : geometricField Z ρ n ω = Fheat Z (tau ρ n) 0 ω := by
  simp only [geometricField, ite_eq_right hn.ne']

/-- The regularized geometric field is integrable at every index. -/
theorem integrable_geometricField (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) : Integrable (geometricField Z ρ n) P := by
  by_cases hn : n = 0
  · subst n
    change Integrable (fun _ : Ω => (0 : ℝ)) P
    exact integrable_const _
  · have heq : geometricField Z ρ n = Fheat Z (tau ρ n) 0 := by
      funext ω
      exact geometricField_of_pos Z ρ (Nat.pos_of_ne_zero hn) ω
    rw [heq]
    exact integrable_Fheat ϑ P Z hZ (tau ρ n) (tau_pos hρ n) (tau_lt_one hρ (Nat.pos_of_ne_zero hn)) 0

/-- The corrected clock is positive at all indices. -/
theorem geometricNormalizer_pos (n : ℕ) : 0 < geometricNormalizer n :=
  Real.sqrt_pos.mpr (by linarith [Real.log_natCast_nonneg n])

/-- Its square is the corrected logarithmic clock. -/
theorem geometricNormalizer_sq (n : ℕ) : geometricNormalizer n ^ 2 = 1 + Real.log n :=
  Real.sq_sqrt (by linarith [Real.log_natCast_nonneg n])

/-- The corrected normalizer diverges. -/
theorem geometricNormalizer_tendsto_atTop : Tendsto geometricNormalizer atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Real.tendsto_sqrt_atTop.comp (tendsto_atTop_mono (fun n => by linarith) hlog)

/-- The scalar Gaussian limit is unchanged by both harmless initial-value repairs. -/
theorem scalar_clt_geometric_regular (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) :
    TendstoInDistribution (fun n ω =>
      (geometricField Z ρ n ω - ∫ ω', geometricField Z ρ n ω' ∂P) / geometricNormalizer n)
      atTop id (fun _ => P) (gaussianReal 0 1) := by
  let c : ℕ → ℝ := fun n => Real.sqrt (Real.log n) / geometricNormalizer n
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto c atTop (𝓝 1) := by
    have h := (tendsto_sqrt_add_div_sqrt (fun n : ℕ => Real.log n) hlog 1).inv₀ (by norm_num)
    simpa only [c, geometricNormalizer, inv_div, inv_one, add_comm] using h
  have hprod := tendstoInDistribution_smul_of_tendsto P (gaussianReal 0 1)
    (scalar_clt_geometric ϑ P Z hZ ρ hρ) hc
  have hm (n : ℕ) : AEMeasurable (fun ω =>
      (geometricField Z ρ n ω - ∫ ω', geometricField Z ρ n ω' ∂P) / geometricNormalizer n) P :=
    ((integrable_geometricField ϑ P Z hZ hρ n).aemeasurable.sub_const _).div_const _
  have hmap : ∀ᶠ n : ℕ in atTop,
      P.map (fun ω => c n * ((Fheat Z (tau ρ n) 0 ω - ∫ ω', Fheat Z (tau ρ n) 0 ω' ∂P) /
        Real.sqrt (Real.log n))) = P.map (fun ω =>
          (geometricField Z ρ n ω - ∫ ω', geometricField Z ρ n ω' ∂P) / geometricNormalizer n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply Measure.map_congr
    filter_upwards [] with ω
    have hn0 : 0 < n := by omega
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hsne : Real.sqrt (Real.log n) ≠ 0 := (Real.sqrt_pos.mpr hlogpos).ne'
    simp only [geometricField_of_pos Z ρ hn0, c]
    field_simp [hsne]
  exact (tendstoInDistribution_congr_of_eventually_map_eq hprod.forall_aemeasurable hm
    hprod.aemeasurable_limit hmap).mp hprod

end Critical2DKPZ.Extensions.ScaleLimit
