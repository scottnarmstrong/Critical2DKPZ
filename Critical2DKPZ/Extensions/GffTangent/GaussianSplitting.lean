/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Critical2DKPZ.Extensions.GffTangent.LogKernelIdentities
public import Critical2DKPZ.Extensions.GffTangent.ConvergenceTools
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic

/-!
# Gaussian splitting and covariance positivity

If two independent real random variables have the same law and their sum is Gaussian, then each
summand is Gaussian.  In the equal-law case, connectedness of the real line selects the unique
continuous square root of the characteristic function which equals one at zero.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ComplexConjugate Matrix Topology

namespace Critical2DKPZ.Extensions.GffTangent

open Spectral



/-- The finite-horizon heat covariance matrix is positive semidefinite. -/
theorem posSemidef_truncatedHeatCovariance {n : ℕ} (f : Fin n → TestFn)
    (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) {T : ℝ} (_hT : 0 < T) :
    (Matrix.of fun i j => 4 * Real.pi *
      ∫ s in Set.Ioc (0 : ℝ) T,
        ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hs0 : 0 < s := hs.1
    change (∫ x : Plane, f j x * heatSmooth (2 * s) (f i) x) =
      ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x
    rw [inner_heatSemigroup_eq_fourier
      ((f j).continuous.integrable_of_hasCompactSupport (f j).hasCompactSupport)
      ((f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport) hs0,
      inner_heatSemigroup_eq_fourier
      ((f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport)
      ((f j).continuous.integrable_of_hasCompactSupport (f j).hasCompactSupport) hs0]
    apply congrArg (fun q : ℝ => (2 * Real.pi)⁻¹ ^ 2 * q)
    apply integral_congr_ae
    filter_upwards [] with ξ
    change (fourierKPZ (f j) ξ * conj (fourierKPZ (f i) ξ)).re * _ =
      (fourierKPZ (f i) ξ * conj (fourierKPZ (f j) ξ)).re * _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  · intro z
    let h : TestFn := ∑ i, z i • f i
    have hfi (i : Fin n) : Integrable (f i : Plane → ℝ) :=
      (f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport
    have hfm (i : Fin n) : MemLp (f i : Plane → ℝ) 2 volume :=
      (f i).continuous.memLp_of_hasCompactSupport (f i).hasCompactSupport
    have h_apply : (h : Plane → ℝ) = fun x => ∑ i, z i * f i x := by
      funext x
      simp only [h, sum_apply, smul_apply, smul_eq_mul]
    have hhi : Integrable (h : Plane → ℝ) := by
      rw [h_apply]
      apply integrable_finsetSum
      intro i _
      exact (hfi i).const_mul (z i)
    have hhzero : (∫ x : Plane, h x) = 0 := by
      rw [h_apply, integral_finsetSum _ fun i _ => (hfi i).const_mul (z i)]
      simp only [MeasureTheory.integral_const_mul, hfzero, mul_zero, Finset.sum_const_zero]
    have hfirst (s : ℝ) (hs : 0 < s) (j : Fin n) :
        (∫ x : Plane, h x * heatSmooth (2 * s) (f j) x) =
          ∑ i, z i * ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x := by
      rw [h_apply]
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [← integral_const_mul]
      · intro i _
        exact (integrable_inner_heatSemigroup (hfi i) (hfi j) hs).const_mul (z i)
    have hsmooth (s : ℝ) (hs : 0 < s) (x : Plane) :
        heatSmooth (2 * s) h x = ∑ j, z j * heatSmooth (2 * s) (f j) x := by
      unfold heatSmooth
      rw [h_apply]
      have heq : (fun y : Plane => heatKernel (2 * s) (x - y) * ∑ j, z j * f j y) =
          (fun y => ∑ j, z j * (heatKernel (2 * s) (x - y) * f j y)) := by
        funext y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [heq, integral_finsetSum]
      · simp only [integral_const_mul]
      · intro j _
        exact (integrable_heatSmooth_integrand (hfi j) (mul_pos two_pos hs) x).const_mul (z j)
    have hquad (s : ℝ) (hs : 0 < s) :
        (∫ x : Plane, h x * heatSmooth (2 * s) h x) =
          ∑ i, ∑ j, z i * (∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x) * z j := by
      have heq : (fun x : Plane => h x * heatSmooth (2 * s) h x) =
          (fun x => ∑ j, z j * (h x * heatSmooth (2 * s) (f j) x)) := by
        funext x
        rw [hsmooth s hs x, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [heq, integral_finsetSum]
      · simp_rw [integral_const_mul, hfirst s hs, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      · intro j _
        exact (integrable_inner_heatSemigroup hhi (hfi j) hs).const_mul (z j)
    have htime (i j : Fin n) : IntegrableOn
        (fun s : ℝ => ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x)
        (Set.Ioc (0 : ℝ) T) := by
      have hglobal := (integral_inner_heatSemigroup_eq_fourier
        (hfi i) (hfi j)
        (hfm i) (hfm j)
        (hfzero i) (hfzero j)
        (integrable_firstMoment_testFn (f i)) (integrable_firstMoment_testFn (f j))).1
      exact hglobal.mono_set Set.Ioc_subset_Ioi_self
    have htermI (i j : Fin n) : IntegrableOn
        (fun s : ℝ => z i *
          (∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x) * z j)
        (Set.Ioc (0 : ℝ) T) := ((htime i j).const_mul (z i)).mul_const (z j)
    have heq :
        ∑ i, z i * (∑ j, (4 * Real.pi *
          ∫ s in Set.Ioc (0 : ℝ) T,
            ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x) * z j) =
        4 * Real.pi * ∫ s in Set.Ioc (0 : ℝ) T,
          ∫ x : Plane, h x * heatSmooth (2 * s) h x := by
      calc
        _ = 4 * Real.pi * ∑ i, ∑ j,
            ∫ s in Set.Ioc (0 : ℝ) T,
              z i * (∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x) * z j := by
          simp_rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 4 * Real.pi * ∫ s in Set.Ioc (0 : ℝ) T,
            ∑ i, ∑ j, z i *
              (∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x) * z j := by
          congr 1
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro i _
            rw [integral_finsetSum]
            intro j _
            exact htermI i j
          · intro i _
            exact integrable_finsetSum Finset.univ fun j _ => htermI i j
        _ = _ := by
          apply congrArg (fun q => 4 * Real.pi * q)
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          exact (hquad s hs.1).symm
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
    rw [heq]
    apply mul_nonneg (by positivity)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [inner_heatSemigroup_eq_fourier hhi hhi hs.1]
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro ξ
    change 0 ≤ (fourierKPZ h ξ * conj (fourierKPZ h ξ)).re * Real.exp (-s * ‖ξ‖ ^ 2)
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)

/-- Truncating the positive-time heat representation gives covariance matrices
converging entrywise to the logarithmic covariance matrix. -/
theorem tendsto_truncatedHeatCovariance_logCovariance {n : ℕ}
    (f : Fin n → TestFn) (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) :
    let g : Fin n → TestFn := fun i => (Real.sqrt 2)⁻¹ • f i
    let S : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k => Matrix.of fun i j =>
      4 * Real.pi * ∫ s in Set.Ioc (0 : ℝ) ((k : ℝ) + 1),
        ∫ x : Plane, g i x * heatSmooth (2 * s) (g j) x
    Tendsto S atTop (𝓝 (Matrix.of fun i j => logCovariance (f i) (f j))) := by
  dsimp only
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let H : ℝ → ℝ := fun s =>
    ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x
  have hHI : IntegrableOn H (Set.Ioi (0 : ℝ)) :=
    (integral_inner_heatSemigroup_testFn (f i) (f j) (hfzero i) (hfzero j)).1
  let A : ℕ → Set ℝ := fun k => Set.Ioc 0 ((k : ℝ) + 1)
  have hAm (k : ℕ) : MeasurableSet (A k) := measurableSet_Ioc
  have hAmono : Monotone A := by
    intro k l hkl
    exact Set.Ioc_subset_Ioc_right (by exact_mod_cast Nat.add_le_add_right hkl 1)
  have hAunion : (⋃ k, A k) = Set.Ioi (0 : ℝ) := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi, A]
    constructor
    · rintro ⟨k, hs0, _⟩
      exact hs0
    · intro hs
      obtain ⟨k : ℕ, hk⟩ := exists_nat_gt s
      exact ⟨k, hs, hk.le.trans (by norm_num)⟩
  have htrunc : Tendsto (fun k => ∫ s in A k, H s) atTop
      (𝓝 (∫ s in Set.Ioi (0 : ℝ), H s)) := by
    have h := tendsto_setIntegral_of_monotone hAm hAmono
      (show IntegrableOn H (⋃ k, A k) by rw [hAunion]; exact hHI)
    simpa only [hAunion] using h
  have hsqrt : (Real.sqrt 2)⁻¹ ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hscaled (s : ℝ) (_hs : 0 < s) :
      (∫ x : Plane,
        (((Real.sqrt 2)⁻¹ • f i : TestFn) x) *
          heatSmooth (2 * s) ((Real.sqrt 2)⁻¹ • f j : TestFn) x) =
        (2 : ℝ)⁻¹ * H s := by
    have hsmooth (x : Plane) :
        heatSmooth (2 * s) ((Real.sqrt 2)⁻¹ • f j : TestFn) x =
          (Real.sqrt 2)⁻¹ * heatSmooth (2 * s) (f j) x := by
      unfold heatSmooth
      simp only [smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    simp_rw [smul_apply, smul_eq_mul, hsmooth]
    rw [show (fun x : Plane => (Real.sqrt 2)⁻¹ * f i x *
        ((Real.sqrt 2)⁻¹ * heatSmooth (2 * s) (f j) x)) =
      fun x => ((Real.sqrt 2)⁻¹ ^ 2) *
        (f i x * heatSmooth (2 * s) (f j) x) by funext x; ring,
      integral_const_mul, hsqrt]
  have hevent : ∀ k : ℕ,
      (∫ s in Set.Ioc (0 : ℝ) ((k : ℝ) + 1),
        ∫ x : Plane, (((Real.sqrt 2)⁻¹ • f i : TestFn) x) *
          heatSmooth (2 * s) ((Real.sqrt 2)⁻¹ • f j : TestFn) x) =
      (2 : ℝ)⁻¹ * ∫ s in A k, H s := by
    intro k
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact hscaled s hs.1
  have hscaledT : Tendsto (fun k : ℕ => 4 * Real.pi *
      ∫ s in Set.Ioc (0 : ℝ) ((k : ℝ) + 1),
        ∫ x : Plane, (((Real.sqrt 2)⁻¹ • f i : TestFn) x) *
          heatSmooth (2 * s) ((Real.sqrt 2)⁻¹ • f j : TestFn) x) atTop
      (𝓝 (4 * Real.pi * (2 : ℝ)⁻¹ *
        ∫ s in Set.Ioi (0 : ℝ), H s)) := by
    apply Tendsto.congr' (Filter.Eventually.of_forall fun k => by rw [hevent k])
    simpa only [mul_assoc] using
      (htrunc.const_mul (2 : ℝ)⁻¹).const_mul (4 * Real.pi)
  have hlimit : 4 * Real.pi * (2 : ℝ)⁻¹ *
      (∫ s in Set.Ioi (0 : ℝ), H s) = logCovariance (f i) (f j) := by
    have h := four_pi_integral_eq_two_logCovariance (f i) (f j)
      (hfzero i) (hfzero j)
    dsimp only [H]
    linarith
  simpa only [Matrix.of_apply, hlimit] using hscaledT

/-- Centered Gaussian laws with truncated heat covariance converge to the finite GFF law. -/
theorem tendstoInDistribution_truncatedHeatGaussian {n : ℕ}
    (f : Fin n → TestFn) (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) :
    let g : Fin n → TestFn := fun i => (Real.sqrt 2)⁻¹ • f i
    let S : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k => Matrix.of fun i j =>
      4 * Real.pi * ∫ s in Set.Ioc (0 : ℝ) ((k : ℝ) + 1),
        ∫ x : Plane, g i x * heatSmooth (2 * s) (g j) x
    let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => logCovariance (f i) (f j)
    TendstoInDistribution (fun _ : ℕ => id) atTop id
      (fun k => ProbabilityTheory.multivariateGaussian 0 (S k))
      (ProbabilityTheory.multivariateGaussian 0 Q) := by
  dsimp only
  apply tendstoInDistribution_gaussian_of_cov_tendsto
  · exact tendsto_truncatedHeatCovariance_logCovariance f hfzero
  · intro k
    exact posSemidef_truncatedHeatCovariance
      (fun i => (Real.sqrt 2)⁻¹ • f i)
      (fun i => by simp only [smul_apply, smul_eq_mul,
        MeasureTheory.integral_const_mul, hfzero, mul_zero])
      (by positivity : 0 < (k : ℝ) + 1)
  · exact posSemidef_logCovariance f hfzero

end Critical2DKPZ.Extensions.GffTangent
