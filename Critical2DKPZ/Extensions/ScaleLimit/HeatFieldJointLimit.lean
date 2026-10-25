/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.JointLimit
import Critical2DKPZ.Extensions.ScaleLimit.ProbabilityZeroTools
import Critical2DKPZ.Extensions.ScaleLimit.FiniteProbability
import Mathlib.Tactic

/-! # Joint transfer from independent blocks to the centered heat-start field -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The centered heat-start process with a regular initial value. -/
def normalizedHeatField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ρ L s : ℝ) (ω : Ω) : ℝ :=
  (geometricField Z ρ (nL ρ L s) ω - ∫ ω', geometricField Z ρ (nL ρ L s) ω' ∂P) / Real.sqrt L

/-- The regular initial-value heat-start field is square integrable at every index. -/
theorem memLp_geometricField_two (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) : MemLp (geometricField Z ρ n) 2 P := by
  by_cases hn : n = 0
  · subst n
    change MemLp (fun _ : Ω => (0 : ℝ)) 2 P
    exact memLp_const _
  · have heq : geometricField Z ρ n = Fheat Z (tau ρ n) 0 := by
      funext ω
      exact geometricField_of_pos Z ρ (Nat.pos_of_ne_zero hn) ω
    rw [heq]
    exact memLp_Fheat_two ϑ P Z hZ (tau ρ n) (tau_pos hρ n) (tau_lt_one hρ (Nat.pos_of_ne_zero hn)) 0

/-- Every normalized heat-start field is square integrable, including the initial scales. -/
theorem memLp_normalizedHeatField (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (L s : ℝ) : MemLp (normalizedHeatField P Z ρ L s) 2 P := by
  have h : MemLp (fun ω => (Real.sqrt L)⁻¹ *
      (geometricField Z ρ (nL ρ L s) ω - ∫ ω', geometricField Z ρ (nL ρ L s) ω' ∂P)) 2 P :=
    ((memLp_geometricField_two ϑ P Z hZ hρ (nL ρ L s)).sub (memLp_const _)).const_mul _
  change MemLp (fun ω => (_ - _) / Real.sqrt L) 2 P
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The centered block approximation remains negligible at each geometric scale time. -/
theorem normalizedHeatField_sub_partialSum (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ s : ℝ, 0 < s →
      TendstoInMeasure P (fun L : Set.Ioi (0 : ℝ) => fun ω =>
        normalizedHeatField P Z ρ L s ω - normalizedPartialSum P Z ρ L s ω) atTop (fun _ => 0) := by
  obtain ⟨ρ₀, hρ₀, hC⟩ := centring_application ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ s hs
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  have hn := nL_tendsto_atTop ρ s hρ1 hs
  have hraw := (hC ρ hρ).2.comp hn
  have hr : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      Real.sqrt (Real.log (nL ρ L s : ℝ)) / Real.sqrt L) atTop (𝓝 (Real.sqrt s)) := by
    have hh : Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.sqrt (Real.log (nL ρ L s : ℝ) / L))
        atTop (𝓝 (Real.sqrt s)) := by
      convert! Real.continuous_sqrt.continuousAt.tendsto.comp (log_nL_div_L_tendsto ρ s hρ1 hs) using 1
    exact hh.congr (fun L => Real.sqrt_div (Real.log_natCast_nonneg _) (L : ℝ))
  have hscaled := tendstoInMeasure_mul_constSeq_zero P hraw hr
  apply hscaled.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hn.eventually_ge_atTop 2] with L hN
  filter_upwards [] with ω
  have hF : geometricField Z ρ (nL ρ L s) = Fheat Z (tau ρ (nL ρ L s)) 0 := by
    funext ω
    exact geometricField_of_pos Z ρ (by omega : 0 < nL ρ L s) ω
  have hlogpos : 0 < Real.log (nL ρ L s : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < nL ρ L s))
  have hns := (Real.sqrt_pos.mpr hlogpos).ne'
  have hLs := (Real.sqrt_pos.mpr L.property).ne'
  simp only [Function.comp_def, normalizedHeatField, normalizedPartialSum, hF]
  field_simp [hns, hLs]

/-- The centered heat-start field has the Brownian finite-dimensional limit
on every positive finite collection of scale times. -/
theorem heatField_joint_limit (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ I : Finset ℝ≥0,
      (∀ i ∈ I, 0 < i) →
      TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
        normalizedHeatField P Z ρ L (i.val : ℝ) ω) atTop id
        (fun _ => P) (BrownianReal.projectiveFamily I) := by
  obtain ⟨ρS, hρS, hS⟩ := cramerWold_lindeberg ϑ P Z hZ
  obtain ⟨ρE, _hρE, hE⟩ := normalizedHeatField_sub_partialSum ϑ P Z hZ
  refine ⟨max ρS ρE, hρS.trans_le (le_max_left _ _), ?_⟩
  intro ρ hρ I hI
  have hρS' : ρS ≤ ρ := (le_max_left _ _).trans hρ
  have hρE' : ρE ≤ ρ := (le_max_right _ _).trans hρ
  have hρ1 : 1 < ρ := hρS.trans_le hρS'
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id (hS ρ hρS' I hI) _
    (fun L => aemeasurable_pi_iff.mpr (fun i => (memLp_normalizedHeatField ϑ P Z hZ hρ1 L i.val).aemeasurable))
  have heq : ((fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => normalizedHeatField P Z ρ L (i.val : ℝ) ω) -
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => normalizedPartialSum P Z ρ L (i.val : ℝ) ω)) =
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => normalizedHeatField P Z ρ L (i.val : ℝ) ω -
        normalizedPartialSum P Z ρ L (i.val : ℝ) ω) := by
    funext L ω i
    simp only [Pi.sub_apply]
  rw [heq]
  apply tendstoInMeasure_finite_pi P atTop _ 0
  intro i
  simpa only [Pi.zero_apply] using hE ρ hρE' i.val (by exact_mod_cast hI i.val i.property)

end Critical2DKPZ.Extensions.ScaleLimit
