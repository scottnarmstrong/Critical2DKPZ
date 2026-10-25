/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.AlmostEverywhereFieldGrowth
public import Critical2DKPZ.SmallScales.SmallBallKernel
public import Critical2DKPZ.SmallScales.DilatedFieldContinuity

/-! # Almost-everywhere spatial growth of shrinking test pairings -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

/-- A standard Gaussian small-scale limit and spatial translation invariance imply eventual growth of unit-mass test pairings along a vanishing sequence of scales at almost every spatial point, almost surely. -/
theorem ae_eventually_large_unitMass_dilate_of_CLT_and_invariance
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hR7 : KpzTransportAt P H)
    {t : ℝ} (ht : 0 < t)
    (hCLT : TendstoInDistribution
      (fun ε ω => H t 0 ω
        (Analysis.Sobolev.unitMassTestFn.dilate ε 0) /
          Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (gaussianReal 0 1)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhdsWithin 0 (Set.Ioi 0)) ∧
      (∀ k, 0 < ε k ∧ ε k < 1 / ((k : ℝ) + 1) ∧ ∀ x : Plane,
        (P {ω | |H t 0 ω (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)| ≤ (k : ℝ)}).toNNReal <
          (1 / 2 : NNReal) ^ k) ∧
      ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure Plane),
        ∀ᶠ k : ℕ in atTop, (k : ℝ) <
          |H t 0 ω (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)| := by
  obtain ⟨ε, hεlim, hε⟩ := exists_uniform_small_ball_scales_of_CLT_and_invariance
    P H hR7 ht Analysis.Sobolev.unitMassTestFn hCLT
  let X : ℕ → Plane → Ω → ℝ := fun k x ω =>
    H t 0 ω (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)
  have hmeasMod (k : ℕ) : ∃ G : Plane × Ω → ℝ, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ x : Plane, G (x, ω) = X k x ω := by
    apply exists_measurable_modification_joint_dilated_test_pairing_of_aemeasurable_sections
    intro x
    exact (hR7 1 (fun _ : Fin 1 => t) (fun _ => ht)
      (fun _ => Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)).1 0
  let G : ℕ → Plane × Ω → ℝ := fun k => (hmeasMod k).choose
  have hGmeas (k : ℕ) : Measurable (G k) := (hmeasMod k).choose_spec.1
  have hGae (k : ℕ) : ∀ᵐ ω ∂P, ∀ x : Plane, G k (x, ω) = X k x ω :=
    (hmeasMod k).choose_spec.2
  let Y : ℕ → Plane → Ω → ℝ := fun k x ω => G k (x, ω)
  have hXm (k : ℕ) : Measurable (fun z : Plane × Ω => Y k z.1 z.2) := by
    simpa only [Y] using hGmeas k
  have hsmall (k : ℕ) (x : Plane) :
      (P {ω | |X k x ω| ≤ (k : ℝ)}).toNNReal ≤ (1 / 2 : NNReal) ^ k := by
    exact (hε k).2.2 x |>.le
  have hsmallMod (k : ℕ) (x : Plane) :
      (P {ω | |Y k x ω| ≤ (k : ℝ)}).toNNReal ≤ (1 / 2 : NNReal) ^ k := by
    have hsets : {ω | |Y k x ω| ≤ (k : ℝ)} =ᵐ[P]
        {ω | |X k x ω| ≤ (k : ℝ)} := by
      filter_upwards [hGae k] with ω hω
      simp only [Y, X]
      rw [hω x]
    rw [measure_congr hsets]
    exact hsmall k x
  have hlocal (n : ℕ) :
      ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : Plane) (n : ℝ))),
        ∀ᶠ k : ℕ in atTop, (k : ℝ) < |Y k x ω| :=
    ae_eventually_index_lt_abs_of_uniform_smallBall P Y hXm hsmallMod _ measure_closedBall_lt_top
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : Plane) (n : ℝ))),
        ∀ᶠ k : ℕ in atTop, (k : ℝ) < |Y k x ω| :=
    ae_all_iff.mpr hlocal
  have hgrowth : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure Plane),
      ∀ᶠ k : ℕ in atTop, (k : ℝ) <
        |Y k x ω| := by
    filter_upwards [hall] with ω hω
    have hpm (k : ℕ) : Measurable (fun x : Plane => Y k x ω) := by
      have hpair : Measurable (fun x : Plane => (x, ω)) := by fun_prop
      have hsection := hXm k |>.comp hpair
      convert hsection using 1
      funext x
      rfl
    have hpmeas' : MeasurableSet
        {x : Plane | ∀ᶠ k : ℕ in atTop, (k : ℝ) < |Y k x ω|} := by
      have hset (k : ℕ) :
          MeasurableSet {x : Plane | (k : ℝ) < |Y k x ω|} :=
        measurableSet_lt measurable_const (measurable_abs.comp (hpm k))
      simp only [Filter.eventually_atTop]
      rw [Set.ofPred_exists]
      apply MeasurableSet.iUnion
      intro N
      rw [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro k
      by_cases hNk : N ≤ k
      · simpa [hNk] using hset k
      · simp [hNk]
    have hglobal' := ae_of_ae_restrict_closedBall_centered hpmeas' (fun n => hω n)
    filter_upwards [hglobal'] with x hx
    exact hx
  have hmods : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ x : Plane, G k (x, ω) = X k x ω := by
    rw [ae_all_iff]
    exact fun k => hGae k
  have hgrowthActual : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure Plane),
      ∀ᶠ k : ℕ in atTop, (k : ℝ) < |X k x ω| := by
    filter_upwards [hgrowth, hmods] with ω hω hωeq
    filter_upwards [hω] with x hx
    filter_upwards [hx] with k hk
    rw [← hωeq k x]
    exact hk
  exact ⟨ε, hεlim, hε, by simpa only [X] using hgrowthActual⟩

end Critical2DKPZ.SmallScales

end
