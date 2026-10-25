/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.GaussianSplitting
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonHeatPartition
import Mathlib.Tactic

/-! # Covariance identities for finite fixed-horizon projections -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Spatial product-kernel and heat-semigroup forms give the same finite
horizon covariance, including the endpoint convention for the finite horizon. -/
theorem integral_fixedHorizon_product_heat_eq (f g : TestFn) {T : ℝ} (hT : 0 < T) :
    (∫ s in Ioo (0 : ℝ) T, ∫ p : Plane × Plane,
      f p.1 * g p.2 * heatKernel (2 * s) (p.2 - p.1) ∂(volume.prod volume)) =
      ∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f x * heatSmooth (2 * s) g x := by
  rw [← integral_Ioc_eq_integral_Ioo]
  have hslices := (integrable_truncated_heat_pairing f g T hT).prod_left_ae
  apply integral_congr_ae
  filter_upwards [hslices] with s hs
  have he : (fun p : Plane × Plane => f p.1 * g p.2 * heatKernel (2 * s) (p.2 - p.1)) =
      (fun p : Plane × Plane => f p.1 * g p.2 * heatKernel (2 * s) (p.1 - p.2)) := by
    funext p
    rw [show p.2 - p.1 = -(p.1 - p.2) by abel, heatKernel_neg]
  rw [he, integral_prod _ hs]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [heatSmooth, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- The quadratic form of the requested matrix is the variance associated
with the same finite linear combination of tests. -/
theorem fixedHorizon_covariance_quadratic {n : ℕ} (f : Fin n → TestFn)
    (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) (T : ℝ) (z : Fin n → ℝ) :
    z ⬝ᵥ (Matrix.of fun i j => 4 * Real.pi *
      ∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x) *ᵥ z =
      4 * Real.pi * ∫ s in Ioc (0 : ℝ) T,
        ∫ x : Plane, (∑ i, z i • f i : TestFn) x *
          heatSmooth (2 * s) (∑ i, z i • f i : TestFn) x := by
  classical
  let h : TestFn := ∑ i, z i • f i
  have hfi (i : Fin n) : Integrable (f i : Plane → ℝ) :=
    (f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport
  have hfm (i : Fin n) : MemLp (f i : Plane → ℝ) 2 volume :=
    (f i).continuous.memLp_of_hasCompactSupport (f i).hasCompactSupport
  have h_apply : (h : Plane → ℝ) = fun x => ∑ i, z i * f i x := by
    funext x
    simp only [h, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  have hhi : Integrable (h : Plane → ℝ) := by
    rw [h_apply]
    apply integrable_finsetSum
    intro i _
    exact (hfi i).const_mul (z i)
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
  exact heq

end Critical2DKPZ.Extensions.GffTangent
