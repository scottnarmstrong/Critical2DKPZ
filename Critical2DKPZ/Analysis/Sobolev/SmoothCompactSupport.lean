/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.SmoothTestIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.Compact

/-!
# Integration of compactly parameterized smooth test families

Joint smoothness and compact support in the parameter imply integrable bounds for every spatial
jet. This turns the finite-jet criterion into a direct distributional integral identity.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace Critical2DKPZ.Analysis.Sobolev

/-- Every spatial derivative of a jointly smooth family with compact parameter support has an
integrable parameter bound, for a measure finite on compact sets. -/
theorem exists_integrable_spatial_jet_bound (μ : Measure Plane) [IsFiniteMeasureOnCompacts μ]
    (S K : Compacts Plane) (F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2))
    (hS : ∀ p, p ∉ S → F p = 0) (n : ℕ) :
    ∃ g : Plane → ℝ, Integrable g μ ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (F p) x‖ ≤ g p := by
  have hcont : Continuous (fun z : Plane × Plane =>
      ‖iteratedFDeriv ℝ n (F z.1) z.2‖) :=
    (contDiff_param_iteratedFDeriv (f := fun p x => F p x) hF n).continuous.norm
  have hSK : IsCompact (S ×ˢ (K : Set Plane)) := S.2.prod K.2
  obtain ⟨c, hc⟩ := hSK.bddAbove_image hcont.continuousOn
  change ∀ y ∈ (fun z : Plane × Plane =>
    ‖iteratedFDeriv ℝ n (F z.1) z.2‖) '' (S ×ˢ (K : Set Plane)), y ≤ c at hc
  let C : ℝ := max c 0
  have hC : 0 ≤ C := le_max_right c 0
  let g : Plane → ℝ := Set.indicator S (fun _ => C)
  have hg : Integrable g μ := by
    unfold g
    exact (integrableOn_const (S.2.measure_ne_top)).integrable_indicator S.2.measurableSet
  refine ⟨g, hg, ?_⟩
  intro p x
  by_cases hp : p ∈ S
  · by_cases hx : x ∈ (K : Set Plane)
    · have hpoint : (p, x) ∈ S ×ˢ (K : Set Plane) := ⟨hp, hx⟩
      have hle : ‖iteratedFDeriv ℝ n (F p) x‖ ≤ c :=
        hc _ ⟨(p, x), hpoint, rfl⟩
      change ‖iteratedFDeriv ℝ n (F p) x‖ ≤ g p
      rw [show g p = C by simp [g, hp]]
      change ‖iteratedFDeriv ℝ n (F p) x‖ ≤ max c 0
      exact hle.trans (le_max_left c 0)
    · have hz : iteratedFDeriv ℝ n (F p) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx
          ((F p).tsupport_subset (tsupport_iteratedFDeriv_subset n h)))
      simpa [g, hp, hz] using hC
  · have hzero : (F p : Plane → ℝ) = 0 :=
      congrArg (fun f : ContDiffMapSupportedIn Plane ℝ ⊤ K => (f : Plane → ℝ)) (hS p hp)
    have hz : iteratedFDeriv ℝ n (F p) x = 0 := by rw [hzero]; simp
    simp [g, hp, hz]

/-- A smooth test family with compact parameter support can be integrated through every real
distribution. -/
theorem distribution_integral_compact_smooth_test_family (μ : Measure Plane)
    [IsFiniteMeasureOnCompacts μ] (T : Distr) (S K : Compacts Plane)
    (F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2))
    (hS : ∀ p, p ∉ S → F p = 0)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K) (hφ : ∀ x, φ x = ∫ p, F p x ∂μ) :
    T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) =
      ∫ p, T (TestFunction.ofSupportedIn (Set.subset_univ _) (F p)) ∂μ := by
  exact Analysis.Sobolev.distribution_integral_smooth_test_family μ T K F hF
    (fun n => exists_integrable_spatial_jet_bound μ S K F hF hS n) φ hφ

end Critical2DKPZ.Analysis.Sobolev

end
