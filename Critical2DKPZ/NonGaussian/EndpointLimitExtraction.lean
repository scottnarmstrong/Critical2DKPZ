/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitMean
public import Critical2DKPZ.NonGaussian.EndpointLimitCompactness
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.TestFn
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Extraction of a deterministic endpoint limit from pairing concentration -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported Topology

namespace Critical2DKPZ.NonGaussian

/-- Concentration of averaged endpoint pairings and vague compactness of their mean measures
give a deterministic subprobability limit along a subsequence. -/
theorem exists_endpoint_limit_of_pairing_concentration
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t : ℝ} (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ1 : ∫ x, ψ x = 1)
    (hconc : ∀ φ : C_c(Plane, ℝ),
      Tendsto (fun r => ∫ ω, |(∫ x, ψ x * endpointPairing Z r t x φ ω) -
        ∫ ω', (∫ x, ψ x * endpointPairing Z r t x φ ω') ∂P| ∂P)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    ∃ (μ : Measure Plane) (r : ℕ → ℝ), IsFiniteMeasure μ ∧ μ Set.univ ≤ 1 ∧
      Tendsto r atTop (nhdsWithin 0 (Set.Ioi 0)) ∧ ∀ φ : C_c(Plane, ℝ),
        Tendsto (fun n => ∫ ω, |(∫ x, ψ x * endpointPairing Z (r n) t x φ ω) -
          ∫ y, φ y ∂μ| ∂P) atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun n => t / ((n : ℝ) + 2)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrt (n : ℕ) : r n < t := by
    dsimp [r]
    rw [div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)]
    nlinarith only [ht, mul_nonneg ht.le (Nat.cast_nonneg n)]
  have hrlim : Tendsto r atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, r] using
        (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 2)
    · exact Filter.Eventually.of_forall hr
  let m : ℕ → Measure Plane := fun n => endpointMeanMeasure P (Z (r n) t)
    (hZ.1 (r n) t (hr n).le (hrt n)) (r n) (hr n) ψ
  let A : ℕ → C_c(Plane, ℝ) → Ω → ℝ :=
    fun n φ ω => ∫ x, ψ x * endpointPairing Z (r n) t x φ ω
  have hspec (n : ℕ) := endpointMeanMeasure_spec P (Z (r n) t)
    (hZ.1 (r n) t (hr n).le (hrt n))
    ((hZ.2.1 (r n) t (hr n).le (hrt n)).mono fun ω hω => hω.1)
    (r n) (hr n) ψ ψ.continuous ψ.hasCompactSupport hψ hψ1
  have hEq (n : ℕ) (φ : C_c(Plane, ℝ)) (ω : Ω) :
      (∫ x, ψ x * (∫ y, φ y ∂endpointTerminalMeasure (Z (r n) t ω) (r n) x)) = A n φ ω := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      congrArg (fun a : ℝ => ψ x * a)
        (endpointPairing_eq_integral_endpointTerminalMeasure Z (hr n) t x φ
          φ.continuous.stronglyMeasurable ω).symm
  have hA (n : ℕ) (φ : C_c(Plane, ℝ)) : Integrable (A n φ) P :=
    ((hspec n).2.2 φ).1.congr (Filter.Eventually.of_forall (hEq n φ))
  have hmean (n : ℕ) (φ : C_c(Plane, ℝ)) : (∫ ω, A n φ ω ∂P) = ∫ y, φ y ∂m n :=
    (integral_congr_ae (Filter.Eventually.of_forall fun ω => (hEq n φ ω).symm)).trans
      ((hspec n).2.2 φ).2
  have hconcSeq (φ : C_c(Plane, ℝ)) :
      Tendsto (fun n => ∫ ω, |A n φ ω - ∫ ω', A n φ ω' ∂P| ∂P) atTop (𝓝 0) :=
    (hconc φ).comp hrlim
  obtain ⟨μ, σ, hσ, hfinite, hmass, hlimit⟩ :=
    exists_subseq_endpoint_pairing_limit_of_mean_measures P A m
      (fun n => (hspec n).2.1) hA hmean hconcSeq
  exact ⟨μ, fun n => r (σ n), hfinite, hmass, hrlim.comp hσ.tendsto_atTop, hlimit⟩

end Critical2DKPZ.NonGaussian
