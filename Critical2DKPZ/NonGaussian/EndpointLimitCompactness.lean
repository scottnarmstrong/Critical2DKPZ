/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointCompactness
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Concentrated pairings and compactness of their deterministic means -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported Topology

namespace Critical2DKPZ.NonGaussian

/-- An integrable random variable is close to a deterministic number when it
is close to its mean and its mean is close to that number. -/
theorem integral_abs_sub_le_centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) (c : ℝ) :
    (∫ ω, |X ω - c| ∂P) ≤
      (∫ ω, |X ω - ∫ ω', X ω' ∂P| ∂P) + |(∫ ω, X ω ∂P) - c| := by
  have hi : Integrable (fun ω => |X ω - ∫ ω', X ω' ∂P|) P :=
    (hX.sub (integrable_const _)).abs
  calc
    _ ≤ ∫ ω, |X ω - ∫ ω', X ω' ∂P| + |(∫ ω', X ω' ∂P) - c| ∂P := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ω => abs_nonneg _)
        (hi.add (integrable_const _))
      exact Filter.Eventually.of_forall fun ω => abs_sub_le _ _ _
    _ = _ := by rw [integral_add hi (integrable_const _)]; simp

/-- Vague compactness of the deterministic mean measures and concentration
of all compact pairings give a deterministic subsequential pairing limit. -/
theorem exists_subseq_endpoint_pairing_limit_of_mean_measures
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → C_c(Plane, ℝ) → Ω → ℝ) (m : ℕ → Measure Plane)
    (hm : ∀ n, m n Set.univ ≤ 1)
    (hA : ∀ n φ, Integrable (A n φ) P)
    (hmean : ∀ n φ, (∫ ω, A n φ ω ∂P) = ∫ y, φ y ∂m n)
    (hconc : ∀ φ : C_c(Plane, ℝ),
      Tendsto (fun n => ∫ ω, |A n φ ω - ∫ ω', A n φ ω' ∂P| ∂P)
        atTop (𝓝 0)) :
    ∃ (μ : Measure Plane) (σ : ℕ → ℕ), StrictMono σ ∧ IsFiniteMeasure μ ∧
      μ Set.univ ≤ 1 ∧ ∀ φ : C_c(Plane, ℝ),
        Tendsto (fun n => ∫ ω, |A (σ n) φ ω - ∫ y, φ y ∂μ| ∂P)
          atTop (𝓝 0) := by
  obtain ⟨μ, σ, hσ, hfinite, hmass, hpair⟩ := exists_subseq_vague_tendsto m hm
  refine ⟨μ, σ, hσ, hfinite, hmass, ?_⟩
  intro φ
  have hcenter := (hconc φ).comp hσ.tendsto_atTop
  have hmeanLimit : Tendsto (fun n => ∫ ω, A (σ n) φ ω ∂P)
      atTop (𝓝 (∫ y, φ y ∂μ)) := by
    simpa only [hmean] using hpair φ
  have habs : Tendsto (fun n => |(∫ ω, A (σ n) φ ω ∂P) - ∫ y, φ y ∂μ|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hmeanLimit.sub (tendsto_const_nhds (x := ∫ y, φ y ∂μ))).abs
  apply squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _)
    (fun n => integral_abs_sub_le_centered P (hA (σ n) φ) _)
  simpa only [zero_add, Function.comp_apply] using hcenter.add habs

end Critical2DKPZ.NonGaussian
