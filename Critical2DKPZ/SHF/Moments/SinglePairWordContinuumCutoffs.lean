/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceFullL1
import Mathlib.Tactic

/-! # Removing space-time cutoffs from the continuum two-particle entrance -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Every uniformly bounded compact cutoff exhaustion converges in the full
continuum entrance integral. The majorant includes both time endpoints and
all spatial variables. -/
theorem tendsto_integral_pairTwo_continuum_entrance_cutoffs
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (η : ℕ → C_c(ℝ × Plane, ℝ)) (hη : ∀ k p, |η k p| ≤ 1)
    (hηlim : ∀ p : ℝ × Plane, 0 < p.1 → p.1 < T →
      Tendsto (fun k => η k p) atTop (𝓝 1)) :
    let μ := ((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
      ((volume : Measure Plane).prod ((volume : Measure Plane).prod (volume : Measure Plane)))
    let F := fun p : ℝ × (Plane × (Plane × Plane)) =>
      (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
        pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1
    (∀ k, Integrable (fun p => η k (p.1, p.2.2.1) * F p) μ) ∧
      Tendsto (fun k => ∫ p, η k (p.1, p.2.2.1) * F p ∂μ) atTop
        (𝓝 (∫ p, F p ∂μ)) := by
  dsimp only
  let μ := ((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
    ((volume : Measure Plane).prod ((volume : Measure Plane).prod (volume : Measure Plane)))
  let F := fun p : ℝ × (Plane × (Plane × Plane)) =>
    (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
      pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1
  have hi : Integrable F μ := integrable_pairTwo_continuum_entrance θ T hT φ
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun p => η k (p.1, p.2.2.1) * F p) μ :=
    (((η k).measurable.comp (measurable_fst.prodMk measurable_snd.snd.fst)).aestronglyMeasurable).mul
      hi.aestronglyMeasurable
  have hb (k : ℕ) (p : ℝ × (Plane × (Plane × Plane))) :
      ‖η k (p.1, p.2.2.1) * F p‖ ≤ ‖F p‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hη k (p.1, p.2.2.1)) (norm_nonneg _)).trans_eq
      (one_mul _)
  refine ⟨fun k => hi.norm.mono' (hm k) (Eventually.of_forall (hb k)), ?_⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun p => ‖F p‖)
  · exact Eventually.of_forall hm
  · exact Eventually.of_forall fun k => Eventually.of_forall (hb k)
  · exact hi.norm
  · have ht : ∀ᵐ p : ℝ × (Plane × (Plane × Plane)) ∂μ,
        p.1 ∈ Set.Ioo 0 T := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact Eventually.of_forall fun _ => hu
    filter_upwards [ht] with p hp
    simpa only [one_mul] using (hηlim (p.1, p.2.2.1) hp.1 hp.2).mul_const (F p)

end Critical2DKPZ.SHF.Moments
