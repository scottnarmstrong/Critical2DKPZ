/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.UniformSmallBallScales
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Almost-everywhere spatial growth from uniform small-ball estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction Distributions ENNReal Topology

namespace Critical2DKPZ.SmallScales

/-- A property holding almost everywhere on every centered finite-radius ball holds almost
everywhere on the plane. -/
theorem ae_of_ae_restrict_closedBall_centered {p : Plane → Prop}
    (hp : MeasurableSet {x | p x})
    (h : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : Plane) (n : ℝ))), p x) :
    ∀ᵐ x ∂(volume : Measure Plane), p x := by
  have hnull (n : ℕ) :
      volume ({x | ¬ p x} ∩ Metric.closedBall (0 : Plane) (n : ℝ)) = 0 := by
    have hzero :
        (volume.restrict (Metric.closedBall (0 : Plane) (n : ℝ))) ({x | p x}ᶜ) = 0 :=
      ae_iff.mp (h n)
    rw [Measure.restrict_apply hp.compl] at hzero
    simpa only [Set.compl_ofPred, Set.inter_comm] using hzero
  have hcover : {x : Plane | ¬ p x} =
      ⋃ n : ℕ, {x : Plane | ¬ p x} ∩ Metric.closedBall (0 : Plane) (n : ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      refine ⟨n, hx, ?_⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using le_of_lt hn
    · rintro ⟨n, hx, _⟩
      exact hx
  apply ae_iff.mpr
  rw [hcover]
  exact measure_iUnion_null hnull

/-- Uniform summable small-ball probabilities force almost every sample to have eventually
large pairings at almost every spatial point in any finite-volume region. -/
theorem ae_eventually_index_lt_abs_of_uniform_smallBall
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Plane → Ω → ℝ)
    (hX : ∀ k, Measurable (fun z : Plane × Ω => X k z.1 z.2))
    (hsmall : ∀ k x,
      (P {ω | |X k x ω| ≤ (k : ℝ)}).toNNReal ≤ (1 / 2 : NNReal) ^ k)
    (S : Set Plane) (hSfinite : volume S < ∞) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume.restrict S),
      ∀ᶠ k : ℕ in atTop, (k : ℝ) < |X k x ω| := by
  let bad : ℕ → Set (Ω × Plane) := fun k =>
    {z | |X k z.2 z.1| ≤ (k : ℝ)}
  have hbad (k : ℕ) : MeasurableSet (bad k) := by
    have hm : Measurable (fun z : Ω × Plane => X k z.2 z.1) := by
      exact (hX k).comp measurable_swap
    exact measurableSet_le (measurable_abs.comp hm) measurable_const
  have hsection (k : ℕ) (x : Plane) :
      P {ω | |X k x ω| ≤ (k : ℝ)} ≤ (1 / 2 : ENNReal) ^ k := by
    rw [← ENNReal.coe_toNNReal (measure_ne_top P _)]
    have hcast : (↑((1 / 2 : NNReal) ^ k) : ENNReal) =
        (1 / 2 : ENNReal) ^ k := by norm_num [ENNReal.coe_pow]
    rw [← hcast]
    exact ENNReal.coe_le_coe.mpr (hsmall k x)
  have hbound (k : ℕ) :
      P.prod (volume.restrict S) (bad k) ≤
        (volume.restrict S Set.univ) * ((1 / 2 : ENNReal) ^ k) := by
    rw [Measure.prod_apply_symm (hbad k)]
    calc
      ∫⁻ x, P {ω | |X k x ω| ≤ (k : ℝ)} ∂(volume.restrict S) ≤
          ∫⁻ _x, (1 / 2 : ENNReal) ^ k ∂(volume.restrict S) :=
        lintegral_mono (fun x => hsection k x)
      _ = (volume.restrict S Set.univ) * ((1 / 2 : ENNReal) ^ k) := by
        rw [lintegral_const, mul_comm]
  have htsum : (∑' k, P.prod (volume.restrict S) (bad k)) ≠ ∞ := by
    have hle : (∑' k, P.prod (volume.restrict S) (bad k)) ≤
        (volume.restrict S Set.univ) * 2 := by
      calc
        (∑' k, P.prod (volume.restrict S) (bad k)) ≤
            ∑' k, (volume.restrict S Set.univ) * ((1 / 2 : ENNReal) ^ k) :=
          ENNReal.tsum_le_tsum hbound
        _ = (volume.restrict S Set.univ) *
            (∑' k : ℕ, (1 / 2 : ENNReal) ^ k) := ENNReal.tsum_mul_left
        _ = (volume.restrict S Set.univ) * 2 := by
          rw [ENNReal.tsum_geometric]
          norm_num
    exact ne_of_lt (lt_of_le_of_lt hle (ENNReal.mul_lt_top
      (by simpa using hSfinite) (by norm_num)))
  have hprod : ∀ᵐ z ∂P.prod (volume.restrict S), ∀ᶠ k in atTop, z ∉ bad k :=
    ae_eventually_notMem htsum
  have hmeas : MeasurableSet
      {z : Ω × Plane | ∀ᶠ k in atTop, z ∉ bad k} := by
    measurability
  have hsections := (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (μ := P) (ν := volume.restrict S) hmeas).mp hprod
  filter_upwards [hsections] with ω hω
  filter_upwards [hω] with x hx
  filter_upwards [hx] with k hk
  exact lt_of_not_ge (by simpa only [bad, Set.mem_ofPred_eq] using hk)

end Critical2DKPZ.SmallScales

end
