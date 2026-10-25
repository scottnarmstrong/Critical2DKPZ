/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SmoothCompactApproximation
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite-dimensional laws determined by smooth tests

Uniform compact smooth approximation transfers equality of smooth compact
test integrals to all compact continuous tests. The Riesz uniqueness theorem
then identifies the finite measures. The bounded-jet formulation is the
finite-dimensional test class used in dense-time uniqueness.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Smooth compact tests determine finite measures on a finite-dimensional real space. -/
theorem measure_eq_of_integral_smoothCompact_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : C_c(E, ℝ), ContDiff ℝ ∞ f → (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  obtain ⟨K, _hK, happrox⟩ := exists_smoothCompactTest_uniform_approx f
  have hbound (ε : ℝ) (hε : 0 < ε) :
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ ε * (μ.real univ + ν.real univ) := by
    obtain ⟨g, hgc, _hgK, hgf⟩ := happrox ε hε
    have hfμ : Integrable f μ := f.integrable
    have hfν : Integrable f ν := f.integrable
    have hgμ : Integrable g μ := g.integrable
    have hgν : Integrable g ν := g.integrable
    have hbμ := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => f x - g x) (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs, abs_sub_comm] using (hgf x).le))
    have hbν := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun x => g x - f x) (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using (hgf x).le))
    rw [integral_sub hfμ hgμ, Real.norm_eq_abs] at hbμ
    rw [integral_sub hgν hfν, Real.norm_eq_abs] at hbν
    calc
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| =
          |((∫ x, f x ∂μ) - ∫ x, g x ∂μ) + ((∫ x, g x ∂ν) - ∫ x, f x ∂ν)| := by
        rw [← h g hgc]
        congr 1
        ring
      _ ≤ |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| + |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| := abs_add_le _ _
      _ ≤ ε * μ.real univ + ε * ν.real univ := add_le_add hbμ hbν
      _ = _ := (mul_add _ _ _).symm
  have hlim : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * (μ.real univ + ν.real univ))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (μ.real univ + ν.real univ)
  have hle : |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall (fun (n : ℕ) => hbound (1 / ((n : ℝ) + 1)) (by positivity)))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

/-- Uniformly bounded derivatives through order four suffice to determine a finite-dimensional law. -/
theorem measure_eq_of_integral_contDiff_bounded_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ H : E → ℝ, ContDiff ℝ 4 H →
      (∃ C : ℝ, ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ C) →
      (∫ x, H x ∂μ) = ∫ x, H x ∂ν) : μ = ν := by
  apply measure_eq_of_integral_smoothCompact_eq μ ν
  intro f hf
  obtain ⟨C, _hC, hC⟩ := f.hasCompactSupport.exists_bound_iteratedFDeriv hf 4
  exact h f (hf.of_le (by simp)) ⟨C, hC⟩

end Critical2DKPZ.SHF.Tsai

end
