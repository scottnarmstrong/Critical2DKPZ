/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-! Finite linear combinations of independent standard Gaussian disorder coordinates have explicitly computable exponential moments. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Polymer

/-- Each disorder coordinate has the standard Gaussian law. -/
theorem coordinate_hasLaw (i : ℕ × Site) :
    HasLaw (fun ω : Disorder => ω i) (gaussianReal 0 1) disorderLaw where
  aemeasurable := (measurable_pi_apply i).aemeasurable
  map_eq := Measure.infinitePi_map_eval _ i

/-- The disorder coordinates form an independent family. -/
theorem coordinates_independent :
    iIndepFun (fun i (ω : Disorder) => ω i) disorderLaw :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-- Exponential of a finite linear combination of distinct disorder coordinates. -/
def finiteExp {ι : Type*} [Fintype ι] (e : ι → ℕ × Site)
    (c : ι → ℝ) (d : ℝ) (ω : Disorder) : ℝ :=
  Real.exp ((∑ i, c i * ω (e i)) + d)

/-- The finite Gaussian exponential is measurable. -/
theorem measurable_finiteExp {ι : Type*} [Fintype ι] (e : ι → ℕ × Site)
    (c : ι → ℝ) (d : ℝ) : Measurable (finiteExp e c d) := by
  unfold finiteExp
  fun_prop

/-- The exponential moment of one Gaussian coordinate has its Gaussian value. -/
theorem integral_exp_coordinate (i : ℕ × Site) (c : ℝ) :
    ∫ ω, Real.exp (c * ω i) ∂disorderLaw = Real.exp (c ^ 2 / 2) := by
  change mgf (fun ω : Disorder => ω i) disorderLaw c = _
  rw [mgf_gaussianReal (coordinate_hasLaw i)]
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add]

/-- A finite Gaussian exponential has the stated explicit expectation. -/
theorem integral_finiteExp {ι : Type*} [Fintype ι] (e : ι → ℕ × Site)
    (he : Function.Injective e) (c : ι → ℝ) (d : ℝ) :
    ∫ ω, finiteExp e c d ω ∂disorderLaw =
      Real.exp ((∑ i, c i ^ 2 / 2) + d) := by
  have hind : iIndepFun (fun i (ω : Disorder) => ω (e i)) disorderLaw :=
    iIndepFun.precomp he coordinates_independent
  have hexp := hind.comp (fun i x => Real.exp (c i * x)) (fun _ => by fun_prop)
  have hprod := hexp.integral_fun_prod_eq_prod_integral (fun i =>
    (show Measurable ((fun x => Real.exp (c i * x)) ∘
      (fun ω : Disorder => ω (e i))) by fun_prop).aestronglyMeasurable)
  simp only [Function.comp_apply] at hprod
  simp_rw [integral_exp_coordinate] at hprod
  simp only [finiteExp, Real.exp_add, Real.exp_sum]
  rw [integral_mul_const, hprod]

/-- The finite Gaussian exponential is integrable. -/
theorem integrable_finiteExp {ι : Type*} [Fintype ι] (e : ι → ℕ × Site)
    (he : Function.Injective e) (c : ι → ℝ) (d : ℝ) :
    Integrable (finiteExp e c d) disorderLaw :=
  Integrable.of_integral_ne_zero (by
    rw [integral_finiteExp e he c d]
    exact Real.exp_ne_zero _)

/-- The exponential of a finite linear combination of disorder coordinates belongs to Lᵖ for every finite exponent. -/
theorem memLp_finiteExp {ι : Type*} [Fintype ι] (e : ι → ℕ × Site)
    (he : Function.Injective e) (c : ι → ℝ) (d : ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (finiteExp e c d) p disorderLaw := by
  have hm : AEStronglyMeasurable (finiteExp e c d) disorderLaw :=
    (measurable_finiteExp e c d).aestronglyMeasurable
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]
    exact hm
  apply (integrable_norm_rpow_iff hm hp0 hp).mp
  have heq : (fun ω => ‖finiteExp e c d ω‖ ^ p.toReal) =
      finiteExp e (fun i => p.toReal * c i) (p.toReal * d) := by
    funext ω
    simp only [finiteExp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 1
    rw [add_mul, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · ring
  rw [heq]
  exact integrable_finiteExp e he _ _

end Critical2DKPZ.Polymer
