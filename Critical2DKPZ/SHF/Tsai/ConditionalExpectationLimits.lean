/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounded continuous expectation limits after conditioning

Convergence in probability on almost every second-factor fiber gives the
bounded continuous expectation limit on that fiber. The bound on the test
then permits dominated convergence over the first factor. All product-space
expectations are integrable before Fubini is applied.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Tsai

/-- Fiberwise convergence in measure passes to product-space bounded continuous expectations,
with integrability of all tested random variables. -/
theorem tendsto_integral_prod_boundedContinuous_of_fiberwise_tendstoInMeasure
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω' × Ω → E) (Y : Ω' × Ω → E)
    (hX : ∀ n, AEStronglyMeasurable (X n) (P'.prod P))
    (hY : AEStronglyMeasurable Y (P'.prod P))
    (hconv : ∀ᵐ a ∂P', TendstoInMeasure P (fun n ω => X n (a, ω)) atTop (fun ω => Y (a, ω)))
    (H : E →ᵇ ℝ) :
    (∀ n, Integrable (fun ω => H (X n ω)) (P'.prod P)) ∧
    Integrable (fun ω => H (Y ω)) (P'.prod P) ∧
    Tendsto (fun n => ∫ ω, H (X n ω) ∂P'.prod P) atTop (𝓝 (∫ ω, H (Y ω) ∂P'.prod P)) := by
  have hHX (n) : AEStronglyMeasurable (fun ω => H (X n ω)) (P'.prod P) :=
    H.continuous.comp_aestronglyMeasurable (hX n)
  have hHY : AEStronglyMeasurable (fun ω => H (Y ω)) (P'.prod P) :=
    H.continuous.comp_aestronglyMeasurable hY
  have hIntX (n) : Integrable (fun ω => H (X n ω)) (P'.prod P) :=
    Integrable.of_bound (hHX n) ‖H‖ (Eventually.of_forall (fun ω => H.norm_coe_le_norm (X n ω)))
  have hIntY : Integrable (fun ω => H (Y ω)) (P'.prod P) :=
    Integrable.of_bound hHY ‖H‖ (Eventually.of_forall (fun ω => H.norm_coe_le_norm (Y ω)))
  refine ⟨hIntX, hIntY, ?_⟩
  have hlim : ∀ᵐ a ∂P', Tendsto (fun n => ∫ ω, H (X n (a, ω)) ∂P) atTop
      (𝓝 (∫ ω, H (Y (a, ω)) ∂P)) := by
    filter_upwards [hconv, ae_all_iff.2 (fun n => (hX n).prodMk_left), hY.prodMk_left]
      with a ha hXa hYa
    have hd := ha.tendstoInDistribution (fun n => (hXa n).aemeasurable)
    exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (fun n => (hXa n).aemeasurable) hYa.aemeasurable).1 hd H
  have hbound (n) (a : Ω') : ‖∫ ω, H (X n (a, ω)) ∂P‖ ≤ ‖H‖ := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := P) (Eventually.of_forall (fun ω => H.norm_coe_le_norm (X n (a, ω))))
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω' => ‖H‖)
    (Eventually.of_forall (fun n => (hHX n).integral_prod_right'))
    (Eventually.of_forall (fun n => Eventually.of_forall (hbound n))) (integrable_const _) hlim
  rw [← integral_prod _ hIntY] at hDCT
  apply hDCT.congr
  intro n
  exact (integral_prod _ (hIntX n)).symm

end Critical2DKPZ.SHF.Tsai

end
