/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Moment convergence on the compact unit interval

Polynomial approximation turns convergence of all moments into weak convergence.
This is used after the change of variables `x = exp(-t)` in renewal Laplace transforms.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- A continuous function on a compact space is integrable against a finite measure. -/
theorem integrable_continuousMap_compact {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℝ)) : Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact f).integrable μ

/-- A continuous-function integral against a probability measure is bounded in norm by the supremum norm. -/
theorem norm_integral_continuousMap_le {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X, ℝ)) : ‖∫ x, f x ∂μ‖ ≤ ‖f‖ := by
  simpa only [BoundedContinuousFunction.norm_mkOfCompact] using!
    (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm μ

/-- Monomial moment convergence implies convergence of polynomial integrals. -/
theorem tendsto_integral_polynomial_of_moments
    (μ : ℕ → ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (h : ∀ k : ℕ, Tendsto (fun N => ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(μ N : Measure _)) atTop
      (nhds (∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(ν : Measure _)))) (p : Polynomial ℝ) :
    Tendsto (fun N => ∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μ N : Measure _)) atTop
      (nhds (∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(ν : Measure _))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have heq (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
        (∫ x : Set.Icc (0 : ℝ) 1, (p + q).eval (x : ℝ) ∂(η : Measure _)) =
          (∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(η : Measure _)) +
          ∫ x : Set.Icc (0 : ℝ) 1, q.eval (x : ℝ) ∂(η : Measure _) := by
      simp only [Polynomial.eval_add]
      exact integral_add (integrable_continuousMap_compact _ (p.toContinuousMapOn _))
        (integrable_continuousMap_compact _ (q.toContinuousMapOn _))
    simpa only [heq] using hp.add hq
  | monomial k a =>
    simpa only [Polynomial.eval_monomial, integral_const_mul] using (h k).const_mul a

/-- Convergence of all monomial moments implies convergence of continuous-function integrals on the unit interval. -/
theorem tendsto_integral_continuous_of_moments
    (μ : ℕ → ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (h : ∀ k : ℕ, Tendsto (fun N => ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(μ N : Measure _)) atTop
      (nhds (∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(ν : Measure _))))
    (f : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    Tendsto (fun N => ∫ x : Set.Icc (0 : ℝ) 1, f x ∂(μ N : Measure _)) atTop
      (nhds (∫ x : Set.Icc (0 : ℝ) 1, f x ∂(ν : Measure _))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f (ε / 3) (by positivity)
  have herr (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
      ‖(∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(η : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, f x ∂(η : Measure _)‖ < ε / 3 := by
    have hpi : Integrable (fun x : Set.Icc (0 : ℝ) 1 => p.eval (x : ℝ)) (η : Measure _) := by
      simpa only [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] using!
        integrable_continuousMap_compact (η : Measure _) (p.toContinuousMapOn (Set.Icc (0 : ℝ) 1))
    have heq := integral_sub hpi (integrable_continuousMap_compact (η : Measure _) f)
    have hb := (norm_integral_continuousMap_le (η : Measure _) (p.toContinuousMapOn _ - f)).trans_lt hp
    simpa only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply, heq] using! hb
  have ht := Metric.tendsto_nhds.mp (tendsto_integral_polynomial_of_moments μ ν h p)
    (ε / 3) (by positivity)
  filter_upwards [ht] with N hN
  rw [Real.dist_eq] at hN ⊢
  have h1 := herr (μ N)
  have h2 := herr ν
  simp only [Real.norm_eq_abs] at h1 h2
  have htriangle := abs_add_three
    ((∫ x : Set.Icc (0 : ℝ) 1, f x ∂(μ N : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μ N : Measure _))
    ((∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μ N : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(ν : Measure _))
    ((∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(ν : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, f x ∂(ν : Measure _))
  rw [abs_sub_comm (∫ x : Set.Icc (0 : ℝ) 1, f x ∂(μ N : Measure _))] at htriangle
  have halg : (∫ x : Set.Icc (0 : ℝ) 1, f x ∂(μ N : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, f x ∂(ν : Measure _) =
    ((∫ x : Set.Icc (0 : ℝ) 1, f x ∂(μ N : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μ N : Measure _)) +
    ((∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(μ N : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(ν : Measure _)) +
    ((∫ x : Set.Icc (0 : ℝ) 1, p.eval (x : ℝ) ∂(ν : Measure _)) - ∫ x : Set.Icc (0 : ℝ) 1, f x ∂(ν : Measure _)) := by ring
  rw [← halg] at htriangle
  linarith only [htriangle, h1, h2, hN]

/-- Probability measures on `[0,1]` converge weakly whenever all their moments converge. -/
theorem tendsto_probabilityMeasure_of_moments
    (μ : ℕ → ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (h : ∀ k : ℕ, Tendsto (fun N => ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(μ N : Measure _)) atTop
      (nhds (∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(ν : Measure _)))) : Tendsto μ atTop (nhds ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact tendsto_integral_continuous_of_moments μ ν h f.toContinuousMap

end Critical2DKPZ.Renewal

end
