/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PotentialRows
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # Potential row bounds on finite products -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- A tensor product of planar heat kernels has unit mass on any finite product. -/
theorem lintegral_tensorHeatKernel_right {ι : Type*} [Fintype ι] {t : ℝ}
    (ht : 0 < t) (x : ι → Plane) :
    (∫⁻ y : ι → Plane, ∏ i, ENNReal.ofReal (heatKernel t (y i - x i))) = 1 := by
  classical
  let f : (ι → Plane) → ℝ := fun y => ∏ i, heatKernel t (y i - x i)
  have hi : Integrable f := by
    dsimp [f]
    exact Integrable.fintype_prod fun i =>
      (integrable_heatKernel ht).comp_sub_right (x i)
  have hn (y : ι → Plane) : 0 ≤ f y := by
    dsimp [f]
    exact Finset.prod_nonneg fun i _ => (Critical2DKPZ.heatKernel_pos ht _).le
  calc (∫⁻ y : ι → Plane, ∏ i, ENNReal.ofReal (heatKernel t (y i - x i)))
      = ∫⁻ y : ι → Plane, ENNReal.ofReal (f y) := by
          apply lintegral_congr
          intro y
          dsimp [f]
          rw [ENNReal.ofReal_prod_of_nonneg fun i _ => (Critical2DKPZ.heatKernel_pos ht _).le]
    _ = ENNReal.ofReal (∫ y : ι → Plane, f y) :=
          (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)).symm
    _ = 1 := by
          dsimp [f]
          rw [integral_fintype_prod_volume_eq_prod
            (fun (i : ι) (z : Plane) => heatKernel t (z - x i))]
          simp only [integral_heatKernel_sub ht, Finset.prod_const_one, ENNReal.ofReal_one]

/-- One fixed translate of the potential in a finite product costs one row bound. -/
theorem lintegral_tensorHeatKernel_mul_shiftedPotential_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {t : ℝ} (ht : 0 < t) (i : ι) (x : ι → Plane) (d : Plane) :
    (∫⁻ y : ι → Plane,
      (∏ k, ENNReal.ofReal (heatKernel t (y k - x k))) *
        heatPotential (y i - d)) ≤ heatPotentialRowBound t := by
  classical
  let F : (ι → Plane) → ℝ≥0∞ := fun y =>
    (∏ k, ENNReal.ofReal (heatKernel t (y k - x k))) * heatPotential (y i - d)
  have hF : Measurable F := by
    dsimp [F]
    have hprod : Measurable (fun y : ι → Plane =>
        ∏ k, ENNReal.ofReal (heatKernel t (y k - x k))) := by
      apply Finset.measurable_fun_prod
      intro k hk
      unfold heatKernel
      fun_prop
    have hdiff : Measurable (fun y : ι → Plane => y i - d) := by fun_prop
    exact hprod.mul (measurable_heatPotential.comp hdiff)
  have hsplit := lintegral_splitCoordinate i hF
  calc (∫⁻ y : ι → Plane, F y)
      = ∫⁻ v : {k : ι // k ≠ i} → Plane, ∫⁻ q : Plane,
          F (insertCoordinate i v q) := hsplit
    _ ≤ ∫⁻ v : {k : ι // k ≠ i} → Plane,
          heatPotentialRowBound t *
            (∏ k : {k : ι // k ≠ i},
              ENNReal.ofReal (heatKernel t (v k - x k.1))) := by
            apply lintegral_mono
            intro v
            let C : ℝ≥0∞ := ∏ k : {k : ι // k ≠ i},
              ENNReal.ofReal (heatKernel t (v k - x k.1))
            have hprod (q : Plane) :
                (∏ k : ι, ENNReal.ofReal
                  (heatKernel t (insertCoordinate i v q k - x k))) =
                  ENNReal.ofReal (heatKernel t (q - x i)) * C := by
              dsimp [C]
              rw [prod_splitCoordinate i
                (fun k : ι => ENNReal.ofReal (heatKernel t
                  (insertCoordinate i v q k - x k)))]
              simp only [insertCoordinate_same, insertCoordinate_other]
            have hq : Measurable (fun q : Plane =>
                ENNReal.ofReal (heatKernel t (x i - q)) *
                  heatPotential (q - d)) := by
              have hh : Measurable (fun q : Plane => heatKernel t (x i - q)) := by
                unfold heatKernel
                fun_prop
              exact hh.ennreal_ofReal.mul
                (measurable_heatPotential.comp (measurable_id.sub_const d))
            have hrow := lintegral_heatKernel_mul_heatPotential_shifted ht (x i) d
            calc (∫⁻ q : Plane, F (insertCoordinate i v q))
                = C * (∫⁻ q : Plane,
                    ENNReal.ofReal (heatKernel t (x i - q)) * heatPotential (q - d)) := by
                    calc (∫⁻ q : Plane, F (insertCoordinate i v q))
                        = ∫⁻ q : Plane, C *
                            (ENNReal.ofReal (heatKernel t (x i - q)) *
                              heatPotential (q - d)) := by
                              apply lintegral_congr
                              intro q
                              dsimp [F]
                              rw [hprod]
                              simp only [insertCoordinate_same]
                              have hs : heatKernel t (q - x i) = heatKernel t (x i - q) := by
                                rw [← neg_sub (x i) q, heatKernel_neg]
                              rw [hs]
                              ac_rfl
                      _ = C * (∫⁻ q : Plane,
                          ENNReal.ofReal (heatKernel t (x i - q)) *
                            heatPotential (q - d)) := lintegral_const_mul C hq
              _ ≤ C * heatPotentialRowBound t := mul_le_mul_right hrow C
              _ = heatPotentialRowBound t *
                    (∏ k : {k : ι // k ≠ i},
                      ENNReal.ofReal (heatKernel t (v k - x k.1))) := by
                    dsimp [C]
                    exact mul_comm _ _
    _ = heatPotentialRowBound t := by
          rw [lintegral_const_mul' _ _ (heatPotentialRowBound_ne_top t),
            lintegral_tensorHeatKernel_right ht (fun k : {k : ι // k ≠ i} => x k.1), mul_one]

/-- One potential weight on two distinct coordinates costs only a half-time row bound. -/
theorem lintegral_tensorHeatKernel_mul_pairPotential_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {t : ℝ} (ht : 0 < t) (i j : ι) (hij : i ≠ j)
    (x : ι → Plane) :
    (∫⁻ y : ι → Plane,
      (∏ k, ENNReal.ofReal (heatKernel t (y k - x k))) *
        heatPotential (y i - y j)) ≤ heatPotentialRowBound t := by
  classical
  let F : (ι → Plane) → ℝ≥0∞ := fun y =>
    (∏ k, ENNReal.ofReal (heatKernel t (y k - x k))) * heatPotential (y i - y j)
  have hF : Measurable F := by
    dsimp [F]
    have hprod : Measurable (fun y : ι → Plane =>
        ∏ k, ENNReal.ofReal (heatKernel t (y k - x k))) := by
      classical
      apply Finset.measurable_fun_prod
      intro k hk
      unfold heatKernel
      fun_prop
    exact hprod.mul (measurable_heatPotential.comp
      ((measurable_pi_apply i).sub (measurable_pi_apply j)))
  let R : {k : ι // k ≠ i} := ⟨j, hij.symm⟩
  have hsplit := lintegral_splitCoordinate i hF
  calc (∫⁻ y : ι → Plane, F y)
      = ∫⁻ v : {k : ι // k ≠ i} → Plane, ∫⁻ q : Plane,
          F (insertCoordinate i v q) := hsplit
    _ ≤ ∫⁻ v : {k : ι // k ≠ i} → Plane,
          heatPotentialRowBound t *
            (∏ k : {k : ι // k ≠ i},
              ENNReal.ofReal (heatKernel t (v k - x k.1))) := by
            apply lintegral_mono
            intro v
            let C : ℝ≥0∞ := ∏ k : {k : ι // k ≠ i},
              ENNReal.ofReal (heatKernel t (v k - x k.1))
            have hji : j ≠ i := hij.symm
            have hR : (R : {k : ι // k ≠ i}) = ⟨j, hji⟩ := rfl
            have hprod (q : Plane) :
                (∏ k : ι, ENNReal.ofReal
                  (heatKernel t (insertCoordinate i v q k - x k))) =
                  ENNReal.ofReal (heatKernel t (q - x i)) * C := by
              dsimp [C]
              rw [prod_splitCoordinate i
                (fun k : ι => ENNReal.ofReal (heatKernel t
                  (insertCoordinate i v q k - x k)))]
              simp only [insertCoordinate_same, insertCoordinate_other]
            have hweight (q : Plane) :
                heatPotential (insertCoordinate i v q i - insertCoordinate i v q j) =
                  heatPotential (q - v R) := by
              simp [insertCoordinate, R, hji]
            have hq : Measurable (fun q : Plane =>
                ENNReal.ofReal (heatKernel t (x i - q)) * heatPotential (q - v R)) := by
              have hh : Measurable (fun q : Plane => heatKernel t (x i - q)) := by
                unfold heatKernel
                fun_prop
              exact hh.ennreal_ofReal.mul
                (measurable_heatPotential.comp (measurable_id.sub_const (v R)))
            have hrow := lintegral_heatKernel_mul_heatPotential_shifted ht (x i) (v R)
            calc (∫⁻ q : Plane, F (insertCoordinate i v q))
                = C * (∫⁻ q : Plane,
                    ENNReal.ofReal (heatKernel t (x i - q)) *
                      heatPotential (q - v R)) := by
                    calc (∫⁻ q : Plane, F (insertCoordinate i v q))
                        = ∫⁻ q : Plane, C *
                            (ENNReal.ofReal (heatKernel t (x i - q)) *
                              heatPotential (q - v R)) := by
                              apply lintegral_congr
                              intro q
                              dsimp [F]
                              rw [hprod, hweight]
                              have hs : heatKernel t (q - x i) = heatKernel t (x i - q) := by
                                rw [← neg_sub (x i) q, heatKernel_neg]
                              rw [hs]
                              ac_rfl
                      _ = C * (∫⁻ q : Plane,
                          ENNReal.ofReal (heatKernel t (x i - q)) *
                            heatPotential (q - v R)) := lintegral_const_mul C hq
              _ ≤ C * heatPotentialRowBound t := mul_le_mul_right hrow C
              _ = heatPotentialRowBound t *
                    (∏ k : {k : ι // k ≠ i},
                      ENNReal.ofReal (heatKernel t (v k - x k.1))) := by
                    dsimp [C]
                    exact mul_comm _ _
    _ = heatPotentialRowBound t := by
          rw [lintegral_const_mul' _ _ (heatPotentialRowBound_ne_top t),
            lintegral_tensorHeatKernel_right ht (fun k : {k : ι // k ≠ i} => x k.1), mul_one]

end Critical2DKPZ.DeltaBose
