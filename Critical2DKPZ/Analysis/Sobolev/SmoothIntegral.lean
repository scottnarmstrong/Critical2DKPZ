/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.TestFunctionFamily
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Joint smoothness and integrable derivative bounds permit differentiation of parameter integrals at every finite order. -/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Critical2DKPZ

/-- Joint smoothness of the derivative in the spatial variable. -/
theorem contDiff_param_fderiv {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P → E → G} (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P × E => fderiv ℝ (F p.1) p.2) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : (P × E) × E => F p.1.1 p.2) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hg.fderiv contDiff_snd (by simp)

/-- Dominated bounds on every spatial derivative justify every iterated derivative of the integral. -/
theorem iteratedFDeriv_integral_of_dominated {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [SecondCountableTopology P]
    [MeasurableSpace P] [BorelSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (μ : Measure P) {F : P → E → G}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F))
    (hbound : ∀ n : ℕ, ∃ g : P → ℝ, Integrable g μ ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (F p) x‖ ≤ g p) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => ∫ p, F p x ∂μ) =
      fun x => ∫ p, iteratedFDeriv ℝ n (F p) x ∂μ := by
  have hD (k : ℕ) := contDiff_param_iteratedFDeriv hF k
  have hI (k : ℕ) (x : E) : Integrable (fun p => iteratedFDeriv ℝ k (F p) x) μ := by
    obtain ⟨g, hg, hbg⟩ := hbound k
    exact hg.mono'
      (((hD k).continuous.comp (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => hbg p x)
  induction n with
  | zero =>
    have hi (x : E) : Integrable (fun p => F p x) μ := by
      obtain ⟨g, hg, hbg⟩ := hbound 0
      apply hg.mono'
        ((hF.continuous.comp (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun p => by
        simpa only [norm_iteratedFDeriv_zero, Function.uncurry_def, Function.comp_def, id_eq] using! hbg p x
    rw [iteratedFDeriv_zero_eq_comp]
    funext x
    change (continuousMultilinearCurryFin0 ℝ E G).symm (∫ p, F p x ∂μ) =
      ∫ p, (continuousMultilinearCurryFin0 ℝ E G).symm (F p x) ∂μ
    exact ((continuousMultilinearCurryFin0 ℝ E G).symm.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (hi x)).symm
  | succ n ih =>
    let : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] G) := inferInstance
    let : NormedSpace ℝ (E →L[ℝ] E [×n]→L[ℝ] G) := inferInstance
    obtain ⟨g, hg, hbg⟩ := hbound (n + 1)
    have hfd : Continuous (fun p : P × E => fderiv ℝ (iteratedFDeriv ℝ n (F p.1)) p.2) :=
      by
        simpa only [Function.uncurry_def] using!
          (contDiff_param_fderiv (F := fun p x => iteratedFDeriv ℝ n (F p) x) (hD n)).continuous
    have hfdI (x : E) : Integrable (fun p => fderiv ℝ (iteratedFDeriv ℝ n (F p)) x) μ := by
      apply hg.mono'
        ((hfd.comp (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun p => by
        change ‖fderiv ℝ (iteratedFDeriv ℝ n (F p)) x‖ ≤ g p
        rw [norm_fderiv_iteratedFDeriv]
        exact hbg p x
    have hderiv (x : E) : HasFDerivAt (fun y => ∫ p, iteratedFDeriv ℝ n (F p) y ∂μ)
        (∫ p, fderiv ℝ (iteratedFDeriv ℝ n (F p)) x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := g) Filter.univ_mem
        (Filter.Eventually.of_forall fun y => (hI n y).aestronglyMeasurable) (hI n x)
        (hfdI x).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun p y _ => by
          rw [norm_fderiv_iteratedFDeriv]
          exact hbg p y
      · exact hg
      · apply Filter.Eventually.of_forall
        intro p y _
        have hd : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ n (F p)) := by
          simpa only [Function.comp_def, Function.uncurry_def] using!
            (hD n).comp ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => p)).prodMk contDiff_id)
        exact (hd.differentiable (by simp) y).hasFDerivAt
    rw [iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) G).symm
      (fderiv ℝ (fun y => ∫ p, iteratedFDeriv ℝ n (F p) y ∂μ) x) = _
    rw [(hderiv x).fderiv]
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe] using!
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) G).symm.toLinearIsometry.integral_comp_comm
        (μ := μ) (fun p => fderiv ℝ (iteratedFDeriv ℝ n (F p)) x)).symm

end Critical2DKPZ

end
