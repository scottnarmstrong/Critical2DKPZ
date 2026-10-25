/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.CompactJets
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A distribution commutes with integration of test functions with common compact support when their finite derivative jets are integrable and commute with that integral. -/

public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace Critical2DKPZ

/-- Integrability in every finite jet norm implies integrability after evaluation by a distribution. -/
theorem integrable_distribution_compact_family {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Distr) (K : Compacts Plane) (F : Ω → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ∀ m : ℕ, Integrable (fun ω => compactTestJet K m (F ω)) μ) :
    Integrable (fun ω => T (TestFunction.ofSupportedIn (Set.subset_univ _) (F ω))) μ := by
  obtain ⟨m, L, hL⟩ := exists_distribution_compact_jet_extension T K
  exact (L.integrable_comp (hF m)).congr (Filter.Eventually.of_forall fun ω => hL (F ω))

/-- A real distribution commutes with a common-compact-support integral specified by its jets. -/
theorem distribution_compact_integral_comm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Distr) (K : Compacts Plane) (F : Ω → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ∀ m : ℕ, Integrable (fun ω => compactTestJet K m (F ω)) μ)
    (hφ : ∀ m : ℕ, compactTestJet K m φ = ∫ ω, compactTestJet K m (F ω) ∂μ) :
    T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) =
      ∫ ω, T (TestFunction.ofSupportedIn (Set.subset_univ _) (F ω)) ∂μ := by
  obtain ⟨m, L, hL⟩ := exists_distribution_compact_jet_extension T K
  rw [← hL φ, hφ m, ← L.integral_comp_comm (hF m)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => hL (F ω)

end Critical2DKPZ

end
