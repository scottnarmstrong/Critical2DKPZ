/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Fiberwise probability convergence on a product space

Fubini expresses each product-space error probability as the integral of
its conditional error probabilities. They converge almost everywhere and
are bounded by one, so dominated convergence gives the global result.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Measurable fiberwise probability convergence gives probability convergence on the product space. -/
theorem tendstoInMeasure_prod_of_fiberwise {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω' × Ω → E) (Y : Ω' × Ω → E)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hconv : ∀ᵐ a ∂P', TendstoInMeasure P (fun n ω => X n (a, ω)) atTop (fun ω => Y (a, ω))) :
    TendstoInMeasure (P'.prod P) X atTop Y := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let A (n : ℕ) : Set (Ω' × Ω) := {ω | ε ≤ dist (X n ω) (Y ω)}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le measurable_const ((hX n).dist hY)
  let q (n : ℕ) (a : Ω') := P (Prod.mk a ⁻¹' A n)
  have hqm (n : ℕ) : Measurable (q n) := measurable_measure_prodMk_left (hA n)
  have hqbound (n : ℕ) : q n ≤ᵐ[P'] fun _ => (1 : ℝ≥0∞) :=
    Filter.Eventually.of_forall (fun a => (measure_mono (Set.subset_univ _)).trans_eq (measure_univ : P Set.univ = 1))
  have hqlim : ∀ᵐ a ∂P', Tendsto (fun n => q n a) atTop (𝓝 0) := by
    filter_upwards [hconv] with a ha
    exact (tendstoInMeasure_iff_dist.1 ha) ε hε
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := P') (fun _ => (1 : ℝ≥0∞))
    hqm hqbound (by simp) hqlim
  simp only [lintegral_zero] at hlim
  have heq (n : ℕ) : (P'.prod P) (A n) = ∫⁻ a, q n a ∂P' := Measure.prod_apply (hA n)
  exact hlim.congr (fun n => (heq n).symm)

/-- Almost-everywhere measurable fiberwise limits give global product-space probability convergence. -/
theorem tendstoInMeasure_prod_of_fiberwise_ae {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω' × Ω → E) (Y : Ω' × Ω → E)
    (hX : ∀ n, AEStronglyMeasurable (X n) (P'.prod P)) (hY : AEStronglyMeasurable Y (P'.prod P))
    (hconv : ∀ᵐ a ∂P', TendstoInMeasure P (fun n ω => X n (a, ω)) atTop (fun ω => Y (a, ω))) :
    TendstoInMeasure (P'.prod P) X atTop Y := by
  let X' (n : ℕ) := (hX n).mk (X n)
  let Y' := hY.mk Y
  have hXrow : ∀ᵐ a ∂P', ∀ n, (fun ω => X n (a, ω)) =ᵐ[P] fun ω => X' n (a, ω) :=
    ae_all_iff.2 fun n => Measure.ae_ae_of_ae_prod (hX n).ae_eq_mk
  have hYrow : ∀ᵐ a ∂P', (fun ω => Y (a, ω)) =ᵐ[P] fun ω => Y' (a, ω) :=
    Measure.ae_ae_of_ae_prod hY.ae_eq_mk
  have hconv' : ∀ᵐ a ∂P', TendstoInMeasure P (fun n ω => X' n (a, ω)) atTop (fun ω => Y' (a, ω)) := by
    filter_upwards [hconv, hXrow, hYrow] with a ha hXa hYa
    exact ha.congr hXa hYa
  have h := tendstoInMeasure_prod_of_fiberwise P P' X' Y'
    (fun n => (hX n).stronglyMeasurable_mk.measurable) hY.stronglyMeasurable_mk.measurable hconv'
  exact h.congr (fun n => (hX n).ae_eq_mk.symm) hY.ae_eq_mk.symm

end Critical2DKPZ.SHF.Tsai

end
