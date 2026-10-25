/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.PathMoments
public import Critical2DKPZ.Gaussian.Harris
public import Critical2DKPZ.Gaussian.GaussianLaw
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Under Gaussian product disorder, integrable increasing finite-coordinate functions with integrable product satisfy `E[F] E[G] ≤ E[FG]`. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Function
open scoped BigOperators

namespace Critical2DKPZ.PolymerCalculus

private def clamp (k : ℕ) (x : ℝ) : ℝ := max (-(k : ℝ)) (min (k : ℝ) x)

private lemma monotone_clamp (k : ℕ) : Monotone (clamp k) :=
  monotone_const.max (monotone_const.min monotone_id)

private lemma measurable_clamp (k : ℕ) : Measurable (clamp k) :=
  measurable_const.max (measurable_const.min measurable_id)

private lemma norm_clamp_le (k : ℕ) (x : ℝ) : ‖clamp k x‖ ≤ (k : ℝ) := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) (min_le_left _ _)⟩

private lemma norm_clamp_le_norm (k : ℕ) (x : ℝ) : ‖clamp k x‖ ≤ ‖x‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
  constructor
  · exact (le_min (by linarith [abs_nonneg x, Nat.cast_nonneg (α := ℝ) k])
      (neg_abs_le x)).trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg x, Nat.cast_nonneg (α := ℝ) k])
      ((min_le_right _ _).trans (le_abs_self x))

private lemma tendsto_clamp (x : ℝ) : Tendsto (fun k : ℕ => clamp k x) atTop (nhds x) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with k hk
  have h : |x| ≤ (k : ℝ) := hN.trans (Nat.cast_le.mpr hk)
  dsimp only [clamp]
  rw [min_eq_right ((le_abs_self x).trans h), max_eq_right]
  linarith [neg_abs_le x]

/-- For increasing functions of finitely many disorder coordinates with `F`, `G` and `FG` integrable, `E[F] E[G] ≤ E[FG]`. -/
theorem disorder_harris_dependsOn (S : Finset (ℕ × Site)) {f g : Disorder → ℝ}
    (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f) (hgm : Measurable g)
    (hfs : DependsOn f (S : Set (ℕ × Site))) (hgs : DependsOn g (S : Set (ℕ × Site)))
    (hfi : Integrable f disorderLaw) (hgi : Integrable g disorderLaw)
    (hfgi : Integrable (fun x => f x * g x) disorderLaw) :
    (∫ x, f x ∂disorderLaw) * (∫ x, g x ∂disorderLaw) ≤
      ∫ x, f x * g x ∂disorderLaw := by
  have hc {u : Disorder → ℝ} (hm : Measurable u)
      (hi : Integrable u (disorderLaw)) :
      Tendsto (fun k => ∫ x, clamp k (u x) ∂disorderLaw) atTop
        (nhds (∫ x, u x ∂disorderLaw)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖u x‖)
      (fun k => ((measurable_clamp k).comp hm).aestronglyMeasurable) hi.norm
      (fun k => ae_of_all _ fun x => norm_clamp_le_norm k (u x))
      (ae_of_all _ fun x => tendsto_clamp (u x))
  have hprod : Tendsto (fun k => ∫ x, clamp k (f x) * clamp k (g x) ∂disorderLaw)
      atTop (nhds (∫ x, f x * g x ∂disorderLaw)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖f x * g x‖)
      (fun k => (((measurable_clamp k).comp hfm).mul
        ((measurable_clamp k).comp hgm)).aestronglyMeasurable) hfgi.norm
      (fun k => ae_of_all _ fun x => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (norm_clamp_le_norm k _) (norm_clamp_le_norm k _)
          (norm_nonneg _) (norm_nonneg _))
      (ae_of_all _ fun x => (tendsto_clamp (f x)).mul (tendsto_clamp (g x)))
  exact le_of_tendsto_of_tendsto ((hc hfm hfi).mul (hc hgm hgi)) hprod
    (Filter.Eventually.of_forall fun k => Gaussian.infinitePi_harris_dependsOn
      (fun _ : ℕ × Site => gaussianReal 0 1) S ((monotone_clamp k).comp hf)
      ((monotone_clamp k).comp hg) ((measurable_clamp k).comp hfm)
      ((measurable_clamp k).comp hgm)
      (fun _ _ h => congrArg (clamp k) (hfs h))
      (fun _ _ h => congrArg (clamp k) (hgs h))
      (fun x => norm_clamp_le k (f x)) (fun x => norm_clamp_le k (g x)))

/-- Square-integrable increasing observables of the same finite Gaussian coordinates associate. -/
theorem covariance_nonneg_disorder_dependsOn (S T : Finset (ℕ × Site))
    {f g : Disorder → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfs : DependsOn f (S : Set (ℕ × Site))) (hgs : DependsOn g (T : Set (ℕ × Site)))
    (hf2 : MemLp f 2 disorderLaw) (hg2 : MemLp g 2 disorderLaw) :
    0 ≤ cov[f, g; disorderLaw] := by
  rw [covariance_eq_sub hf2 hg2]
  apply sub_nonneg.mpr
  apply disorder_harris_dependsOn (S ∪ T) hf hg hfm hgm
  · intro x y h
    exact hfs (fun i hi => h i (Finset.mem_union_left T hi))
  · intro x y h
    exact hgs (fun i hi => h i (Finset.mem_union_right S hi))
  · exact hf2.integrable (by norm_num)
  · exact hg2.integrable (by norm_num)
  · exact hf2.integrable_mul hg2

end Critical2DKPZ.PolymerCalculus
