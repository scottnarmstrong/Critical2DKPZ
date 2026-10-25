/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CentringApplication
public import Critical2DKPZ.Extensions.ScaleLimit.CenteredArrayCLT
import Critical2DKPZ.Extensions.ScaleLimit.CentringLemma
import Mathlib.Tactic

/-! # Covariance of the nested independent block sums -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The covariance of two nested sums of independent square-integrable variables
is the variance of the shorter sum. -/
theorem covariance_partialSumRange {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y P)
    (hmem : ∀ j, MemLp (Y j) 2 P) {m n : ℕ} (hmn : m ≤ n) :
    covariance (partialSumRange Y m) (partialSumRange Y n) P = variance (partialSumRange Y m) P := by
  change covariance (fun ω => ∑ i ∈ Finset.range m, Y i ω)
    (fun ω => ∑ j ∈ Finset.range n, Y j ω) P = _
  rw [covariance_fun_sum_fun_sum' (fun i _ => hmem i) (fun j _ => hmem j)]
  have hdiag (i : ℕ) (hi : i ∈ Finset.range m) :
      (∑ j ∈ Finset.range n, covariance (Y i) (Y j) P) = variance (Y i) P := by
    rw [Finset.sum_eq_single i]
    · exact covariance_self (hmem i).aemeasurable
    · intro j hj hij
      exact (hind.indepFun hij.symm).covariance_eq_zero (hmem i) (hmem j)
    · intro hin
      exact False.elim (hin (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hmn)))
  simp_rw [Finset.sum_congr rfl hdiag]
  have hv := IndepFun.variance_sum (s := Finset.range m) (X := Y)
    (fun i _ => hmem i) (fun i hi j hj hij => hind.indepFun hij)
  have heq : (∑ j ∈ Finset.range m, Y j) = partialSumRange Y m := by
    funext ω
    exact Finset.sum_apply ω _ _
  rw [heq] at hv
  exact hv.symm

/-- Exact covariance identity for the flow's nested logarithmic block sums. -/
theorem partialSum_covariance_eq (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) {m n : ℕ} (hmn : m ≤ n) :
    covariance (partialSum Z ρ m) (partialSum Z ρ n) P = variance (partialSum Z ρ m) P := by
  let Y : ℕ → Ω → ℝ := fun j => logTrunc Z ρ (j + 1)
  have hsum (k : ℕ) : partialSumRange Y k = partialSum Z ρ k := by
    funext ω
    exact sum_range_add_one_eq_sum_Icc (fun j => logTrunc Z ρ j ω) k
  have h := covariance_partialSumRange P Y (iIndepFun_logTrunc ϑ P Z hZ hρ)
    (fun j => memLp_logTrunc ϑ P Z hZ hρ j 2) hmn
  simpa only [hsum] using h

/-- The normalized covariance follows the Brownian minimum clock. -/
theorem partialSum_covariance (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ s s' : ℝ, 0 < s → s ≤ s' →
      Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ * covariance
        (partialSum Z ρ (nL ρ L s)) (partialSum Z ρ (nL ρ L s')) P) atTop (𝓝 s) := by
  obtain ⟨ρ₀, hρ₀, hC⟩ := centring_application ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ s s' hs hss'
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  have hV := (hC ρ hρ).1.comp (nL_tendsto_atTop ρ s hρ1 hs)
  have hclock := log_nL_div_L_tendsto ρ s hρ1 hs
  have hprod : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (variance (partialSum Z ρ (nL ρ L s)) P / Real.log (nL ρ L s)) *
        (Real.log (nL ρ L s) / (L : ℝ))) atTop (𝓝 s) := by
    simpa only [Function.comp_def, one_mul] using hV.mul hclock
  apply hprod.congr'
  filter_upwards [(nL_tendsto_atTop ρ s hρ1 hs).eventually_ge_atTop 2] with L hN
  rw [partialSum_covariance_eq ϑ P Z hZ hρ1 (monotone_nL_time ρ L hρ1 L.property hss')]
  have hlogpos : 0 < Real.log (nL ρ L s : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < nL ρ L s))
  field_simp [hlogpos.ne']

end Critical2DKPZ.Extensions.ScaleLimit
