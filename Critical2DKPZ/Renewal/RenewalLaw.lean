/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CriticalLaplace
public import Critical2DKPZ.Renewal.TiltedDensity
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# The discrete tilted renewal probability law

The positive critical gap normalizes the exponentially damped renewal mass to a PMF.
Compactified moments are its discrete Laplace transforms.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Renewal

/-- The geometric normalization of the tilted critical renewal mass. -/
def criticalGap (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ) : ℝ :=
  1 - criticalSigmaSq ϑ N * dampedReturnSum a N

/-- The normalized tilted renewal weights sum to one. -/
theorem hasSum_tiltedRenewalWeights (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N) :
    HasSum (fun n => criticalGap ϑ a N *
      (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1)))) 1 := by
  have hs := hasSum_weightedStep_critical ϑ a N
  have hw : ∀ r, 0 ≤ criticalSigmaSq ϑ N * returnWeight r :=
    fun r => mul_nonneg hσ (srwKernel_nonneg _ _)
  have h := (hasSum_weighted_renewalMass (w := fun r => criticalSigmaSq ϑ N * returnWeight r)
    (ρ := dampingBase a N) hw (Real.exp_pos _).le hs.summable
      (by rw [hs.tsum_eq]; exact sub_pos.mp hgap)).mul_left (criticalGap ϑ a N)
  have hcancel : criticalGap ϑ a N *
      (1 / (1 - criticalSigmaSq ϑ N * dampedReturnSum a N)) = 1 :=
    mul_one_div_cancel hgap.ne'
  simpa only [criticalRenewalMass, dampingBase_pow, hs.tsum_eq, hcancel] using h

/-- The tilted renewal weight is nonnegative. -/
theorem tiltedRenewalWeight_nonneg (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N) (n : ℕ) :
    0 ≤ criticalGap ϑ a N * (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1))) :=
  mul_nonneg hgap.le (mul_nonneg
    (renewalMass_nonneg (fun _ => mul_nonneg hσ (srwKernel_nonneg _ _)) n) (Real.exp_pos _).le)

/-- The probability distribution of a renewal time under exponential damping. -/
def tiltedRenewalPMF (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (criticalGap ϑ a N *
      (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1)))), by
    have h := hasSum_tiltedRenewalWeights ϑ a N hσ hgap
    have heq : (∑' n, ENNReal.ofReal (criticalGap ϑ a N *
        (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1))))) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (tiltedRenewalWeight_nonneg ϑ a N hσ hgap)
        h.summable, h.tsum_eq, ENNReal.ofReal_one]
    rw [← heq]
    exact ENNReal.summable.hasSum⟩


/-- The tilted renewal probability mass function equals its normalized weight. -/
theorem tiltedRenewalPMF_apply (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N) (n : ℕ) :
    tiltedRenewalPMF ϑ a N hσ hgap n = ENNReal.ofReal (criticalGap ϑ a N *
      (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1)))) := rfl

/-- The tilted renewal law on the discrete time axis. -/
def tiltedRenewalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N) :
    ProbabilityMeasure ℕ :=
  ⟨(tiltedRenewalPMF ϑ a N hσ hgap).toMeasure, inferInstance⟩

/-- The compactified, rescaled tilted renewal law. -/
def compactRenewalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N) :
    ProbabilityMeasure (Set.Icc (0 : ℝ) 1) :=
  ProbabilityMeasure.map
    (tiltedRenewalLaw ϑ a N hσ hgap)
    (fun n : ℕ => compactifyTime ((n : ℝ) / (N + 1)))

/-- The time-compactification map for the discrete renewal law is measurable. -/
theorem measurable_compactRenewalLaw_map (N : ℕ) :
    Measurable (fun n : ℕ => compactifyTime ((n : ℝ) / (N + 1))) := measurable_of_countable _

/-- Integration against the rescaled law is the corresponding weighted renewal series. -/
theorem integral_compactRenewalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N)
    (g : Set.Icc (0 : ℝ) 1 → ℝ)
    (hg : Integrable g (compactRenewalLaw ϑ a N hσ hgap : Measure _)) :
    (∫ x, g x ∂(compactRenewalLaw ϑ a N hσ hgap : Measure _)) =
      ∑' n, (criticalGap ϑ a N * (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1)))) *
        g (compactifyTime ((n : ℝ) / (N + 1))) := by
  let p := tiltedRenewalPMF ϑ a N hσ hgap
  have hi : Integrable g (p.toMeasure.map (fun n : ℕ => compactifyTime ((n : ℝ) / (N + 1)))) := hg
  change (∫ x, g x ∂p.toMeasure.map (fun n : ℕ => compactifyTime ((n : ℝ) / (N + 1)))) = _
  rw [integral_map (measurable_compactRenewalLaw_map N).aemeasurable hi.aestronglyMeasurable]
  change (∫ n, g (compactifyTime ((n : ℝ) / (N + 1))) ∂p.toMeasure) = _
  have hi' : Integrable (fun n : ℕ => g (compactifyTime ((n : ℝ) / (N + 1)))) p.toMeasure := by
    simpa only [Function.comp_def] using! hi.comp_measurable (measurable_compactRenewalLaw_map N)
  rw [p.integral_eq_tsum _ hi']
  apply tsum_congr
  intro n
  simp only [p, tiltedRenewalPMF_apply, ENNReal.toReal_ofReal
    (tiltedRenewalWeight_nonneg ϑ a N hσ hgap n), smul_eq_mul]

/-- A moment of the compactified renewal law equals its normalized damped renewal series. -/
theorem integral_pow_compactRenewalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N) (k : ℕ) :
    (∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(compactRenewalLaw ϑ a N hσ hgap : Measure _)) =
      criticalGap ϑ a N * ∑' n, criticalRenewalMass ϑ N n *
        Real.exp (-((a : ℝ) + k) * n / (N + 1)) := by
  let p := tiltedRenewalPMF ϑ a N hσ hgap
  let f := fun n : ℕ => (compactifyTime ((n : ℝ) / (N + 1)) : ℝ) ^ k
  have hf : Integrable f p.toMeasure := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (measurable_of_countable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (compactifyTime _).2.1 _)]
      exact pow_le_one₀ (compactifyTime _).2.1 (compactifyTime _).2.2
  rw [compactRenewalLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_compactRenewalLaw_map N).aemeasurable (by fun_prop)]
  change (∫ n, f n ∂p.toMeasure) = _
  rw [p.integral_eq_tsum f hf, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have ht : 0 ≤ (n : ℝ) / (N + 1) := by positivity
  simp only [p, tiltedRenewalPMF_apply, ENNReal.toReal_ofReal
    (tiltedRenewalWeight_nonneg ϑ a N hσ hgap n), smul_eq_mul,
    f, compactifyTime_coe ht, ← Real.exp_nat_mul]
  have he : Real.exp (-a * n / (N + 1)) * Real.exp ((k : ℝ) * -((n : ℝ) / (N + 1))) =
      Real.exp (-((a : ℝ) + k) * n / (N + 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = criticalGap ϑ a N * criticalRenewalMass ϑ N n *
        (Real.exp (-a * n / (N + 1)) * Real.exp ((k : ℝ) * -((n : ℝ) / (N + 1)))) := by ring
    _ = _ := by rw [he]; ring

end Critical2DKPZ.Renewal

end
