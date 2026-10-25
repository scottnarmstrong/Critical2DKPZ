/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.CompactTestIntegral
public import Critical2DKPZ.Analysis.Sobolev.SmoothIntegral

/-!
# Smooth compact-support test families and distributional integration

The finite jet integrals are proved from joint smoothness, ordinary integrable derivative bounds,
and the pointwise integral formula. The conclusion applies to every real distribution.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace Critical2DKPZ.Analysis.Sobolev

/-- A smooth test family with dominated spatial derivatives is integrable in every finite jet norm. -/
theorem integrable_compactTestJet_of_dominated (μ : Measure Plane) (K : Compacts Plane)
    (F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2))
    (hbound : ∀ n : ℕ, ∃ g : Plane → ℝ, Integrable g μ ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (F p) x‖ ≤ g p) (m : ℕ) :
    Integrable (fun p => compactTestJet K m (F p)) μ := by
  classical
  choose g hg hbg using hbound
  have hg0 (j : ℕ) (p : Plane) : 0 ≤ g j p :=
    (norm_nonneg (iteratedFDeriv ℝ j (F p) 0)).trans (hbg j p 0)
  let b (p : Plane) := ∑ j ∈ Finset.range (m + 1), g j p
  have hb : Integrable b μ := integrable_finsetSum _ (fun j _ => hg j)
  have hc := continuous_supported_test_family K F hF
  have hsc : SecondCountableTopologyEither Plane (CompactJetSpace m) :=
    ⟨Or.inl (inferInstance : SecondCountableTopology Plane)⟩
  apply hb.mono'
    (Continuous.stronglyMeasurable (h := hsc)
      ((compactTestJet K m).continuous.comp hc)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  change ‖compactTestJet K m (F p)‖ ≤ b p
  apply norm_compactTestJet_le K m (F p) (Finset.sum_nonneg fun j _ => hg0 j p)
  intro j hj x
  exact (hbg j p x).trans (Finset.single_le_sum (fun k _ => hg0 k p)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

/-- The pointwise integral of a smooth dominated test family has exactly the integrated finite jets. -/
theorem compactTestJet_integral_of_dominated (μ : Measure Plane) (K : Compacts Plane)
    (F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2))
    (hbound : ∀ n : ℕ, ∃ g : Plane → ℝ, Integrable g μ ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (F p) x‖ ≤ g p)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K) (hφ : ∀ x, φ x = ∫ p, F p x ∂μ) (m : ℕ) :
    compactTestJet K m φ = ∫ p, compactTestJet K m (F p) ∂μ := by
  have hi := integrable_compactTestJet_of_dominated μ K F hF hbound m
  funext i
  apply BoundedContinuousFunction.ext
  intro x
  have hd : iteratedFDeriv ℝ i.val φ x = ∫ p, iteratedFDeriv ℝ i.val (F p) x ∂μ := by
    have he : (φ : Plane → ℝ) = fun x => ∫ p, F p x ∂μ := funext hφ
    rw [he, iteratedFDeriv_integral_of_dominated μ (F := fun p x => F p x) hF hbound i.val]
  calc
    (compactTestJet K m φ) i x = iteratedFDeriv ℝ i.val φ x := by
      simp only [compactTestJet, ContinuousLinearMap.pi_apply,
        ContDiffMapSupportedIn.structureMapCLM_top_apply]
    _ = ∫ p, iteratedFDeriv ℝ i.val (F p) x ∂μ := hd
    _ = (∫ p, compactTestJet K m (F p) ∂μ) i x := by
      simpa only [compactJetEvalCLM_apply, compactTestJet, ContinuousLinearMap.pi_apply,
        ContDiffMapSupportedIn.structureMapCLM_top_apply] using!
        (compactJetEvalCLM m i x).integral_comp_comm hi

/-- Every real distribution commutes with the pointwise integral of a smooth dominated test family. -/
theorem distribution_integral_smooth_test_family (μ : Measure Plane) (T : Distr) (K : Compacts Plane)
    (F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2))
    (hbound : ∀ n : ℕ, ∃ g : Plane → ℝ, Integrable g μ ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (F p) x‖ ≤ g p)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K) (hφ : ∀ x, φ x = ∫ p, F p x ∂μ) :
    T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) =
      ∫ p, T (TestFunction.ofSupportedIn (Set.subset_univ _) (F p)) ∂μ :=
  distribution_compact_integral_comm μ T K F φ
    (integrable_compactTestJet_of_dominated μ K F hF hbound)
    (compactTestJet_integral_of_dominated μ K F hF hbound φ hφ)

/-- Every real distribution commutes with the pointwise integral of a smooth dominated test family
whose parameter lies in an arbitrary second-countable real normed space. This extends
`distribution_integral_smooth_test_family`, whose parameter is the plane. -/
theorem distribution_integral_smooth_test_family_of_parameter
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [SecondCountableTopology P]
    [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) (T : Distr) (K : Compacts Plane)
    (F : P → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : P × Plane => F p.1 p.2))
    (hbound : ∀ n : ℕ, ∃ g : P → ℝ, Integrable g μ ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (F p) x‖ ≤ g p)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K) (hφ : ∀ x, φ x = ∫ p, F p x ∂μ) :
    T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) =
      ∫ p, T (TestFunction.ofSupportedIn (Set.subset_univ _) (F p)) ∂μ := by
  classical
  have hjetInt (m : ℕ) : Integrable (fun p => compactTestJet K m (F p)) μ := by
    choose g hg hbg using hbound
    have hg0 (j : ℕ) (p : P) : 0 ≤ g j p :=
      (norm_nonneg (iteratedFDeriv ℝ j (F p) 0)).trans (hbg j p 0)
    let b (p : P) := ∑ j ∈ Finset.range (m + 1), g j p
    have hb : Integrable b μ := integrable_finsetSum _ (fun j _ => hg j)
    have hc := continuous_supported_test_family K F hF
    have hsc : SecondCountableTopologyEither P (CompactJetSpace m) :=
      ⟨Or.inl (inferInstance : SecondCountableTopology P)⟩
    apply hb.mono'
      (Continuous.stronglyMeasurable (h := hsc)
        ((compactTestJet K m).continuous.comp hc)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    change ‖compactTestJet K m (F p)‖ ≤ b p
    apply norm_compactTestJet_le K m (F p) (Finset.sum_nonneg fun j _ => hg0 j p)
    intro j hj x
    exact (hbg j p x).trans (Finset.single_le_sum (fun k _ => hg0 k p)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  have hjetEq (m : ℕ) :
      compactTestJet K m φ = ∫ p, compactTestJet K m (F p) ∂μ := by
    funext i
    apply BoundedContinuousFunction.ext
    intro x
    have hd : iteratedFDeriv ℝ i.val φ x =
        ∫ p, iteratedFDeriv ℝ i.val (F p) x ∂μ := by
      have he : (φ : Plane → ℝ) = fun x => ∫ p, F p x ∂μ := funext hφ
      rw [he, iteratedFDeriv_integral_of_dominated μ (F := fun p x => F p x)
        hF hbound i.val]
    calc
      (compactTestJet K m φ) i x = iteratedFDeriv ℝ i.val φ x := by
        simp only [compactTestJet, ContinuousLinearMap.pi_apply,
          ContDiffMapSupportedIn.structureMapCLM_top_apply]
      _ = ∫ p, iteratedFDeriv ℝ i.val (F p) x ∂μ := hd
      _ = (∫ p, compactTestJet K m (F p) ∂μ) i x := by
        simpa only [compactJetEvalCLM_apply, compactTestJet, ContinuousLinearMap.pi_apply,
          ContDiffMapSupportedIn.structureMapCLM_top_apply] using!
          (compactJetEvalCLM m i x).integral_comp_comm (hjetInt m)
  exact distribution_compact_integral_comm μ T K F φ hjetInt hjetEq

end Critical2DKPZ.Analysis.Sobolev

end
