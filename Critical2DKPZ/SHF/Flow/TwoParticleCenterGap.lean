/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.TwoParticle
public import Critical2DKPZ.SHF.Flow.HeatPairFactor
public import Critical2DKPZ.SHF.Flow.HeatConvolutionENN
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Center and gap form of the two-particle collision correction -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- A finite scalar can be pulled through the two planar center integrals. -/
theorem lintegral_const_mul_double_plane {F : Plane → Plane → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (c : ℝ≥0∞) :
    (∫⁻ z : Plane, ∫⁻ w : Plane, c * F z w) =
      c * (∫⁻ z : Plane, ∫⁻ w : Plane, F z w) := by
  have hrow (z : Plane) : Measurable (fun w : Plane => F z w) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have houter : Measurable (fun z : Plane => ∫⁻ w : Plane, F z w) :=
    hF.lintegral_prod_right (ν := volume)
  calc
    (∫⁻ z : Plane, ∫⁻ w : Plane, c * F z w) =
        ∫⁻ z : Plane, c * ∫⁻ w : Plane, F z w := by
          apply lintegral_congr
          intro z
          exact lintegral_const_mul c (hrow z)
    _ = c * (∫⁻ z : Plane, ∫⁻ w : Plane, F z w) :=
          lintegral_const_mul c houter

/-- The two planar integrations can be written in center and gap coordinates.
The change of variables is the composition of two translations, so its
Jacobian is one. -/
theorem lintegral_pair_center_gap {F : Plane → Plane → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ x : Plane, ∫⁻ y : Plane, F x y) =
      ∫⁻ g : Plane, ∫⁻ c : Plane, F (c - (1 / 2 : ℝ) • g) (c + (1 / 2 : ℝ) • g) := by
  have hShift : Measurable (Function.uncurry (fun x g : Plane => F x (x + g))) := by
    exact hF.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  calc
    (∫⁻ x : Plane, ∫⁻ y : Plane, F x y) =
        ∫⁻ x : Plane, ∫⁻ g : Plane, F x (x + g) := by
          apply lintegral_congr
          intro x
          let hmp : MeasurePreserving (fun y : Plane => y - x) volume volume := by
            simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-x)
          let G : Plane → ℝ≥0∞ := fun g => F x (g + x)
          have hG : Measurable G := by
            exact hF.comp (measurable_const.prodMk
              (measurable_id.add_const x))
          calc
            (∫⁻ y : Plane, F x y) = ∫⁻ y : Plane, G (y - x) := by
              apply lintegral_congr
              intro y
              dsimp [G]
              congr 2
              abel
            _ = ∫⁻ g : Plane, G g := hmp.lintegral_comp hG
            _ = ∫⁻ g : Plane, F x (x + g) := by
              congr 1
              funext g
              dsimp [G]
              exact congrArg (F x) (add_comm g x)
    _ = ∫⁻ g : Plane, ∫⁻ x : Plane, F x (x + g) :=
      lintegral_lintegral_swap hShift.aemeasurable
    _ = ∫⁻ g : Plane, ∫⁻ c : Plane,
          F (c - (1 / 2 : ℝ) • g) (c + (1 / 2 : ℝ) • g) := by
          apply lintegral_congr
          intro g
          let hmp : MeasurePreserving
              (fun x : Plane => x + (1 / 2 : ℝ) • g) volume volume := by
            simpa only [sub_eq_add_neg] using
              measurePreserving_add_right volume ((1 / 2 : ℝ) • g)
          let G : Plane → ℝ≥0∞ := fun c =>
            F (c - (1 / 2 : ℝ) • g) (c + (1 / 2 : ℝ) • g)
          have hG : Measurable G := by
            exact hF.comp ((measurable_id.sub_const ((1 / 2 : ℝ) • g)).prodMk
              (measurable_id.add_const ((1 / 2 : ℝ) • g)))
          calc
            (∫⁻ x : Plane, F x (x + g)) = ∫⁻ x : Plane,
                G (x + (1 / 2 : ℝ) • g) := by
                  apply lintegral_congr
                  intro x
                  dsimp [G]
                  apply congrArg₂ F
                  · abel
                  · symm
                    calc
                      x + (1 / 2 : ℝ) • g + (1 / 2 : ℝ) • g =
                          x + ((1 / 2 : ℝ) • g + (1 / 2 : ℝ) • g) := by rw [add_assoc]
                      _ = x + (((1 / 2 : ℝ) + (1 / 2 : ℝ)) • g) := by rw [← add_smul]
                      _ = x + g := by rw [show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num,
                        one_smul]
            _ = ∫⁻ c : Plane, G c := hmp.lintegral_comp hG

/-- Two consecutive center heat steps collapse to one. -/
theorem lintegral_heatKernel_center_chainENN {r δ q : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hq : 0 < q) (X Y : Plane) :
    (∫⁻ z : Plane, ∫⁻ w : Plane,
      ENNReal.ofReal (heatKernel (r / 2) (z - X)) *
        (ENNReal.ofReal (heatKernel (δ / 2) (w - z)) *
          ENNReal.ofReal (heatKernel (q / 2) (Y - w)))) =
      ENNReal.ofReal (heatKernel ((r + δ + q) / 2) (Y - X)) := by
  have hrow (z : Plane) :
      (∫⁻ w : Plane,
        ENNReal.ofReal (heatKernel (δ / 2) (w - z)) *
          ENNReal.ofReal (heatKernel (q / 2) (Y - w))) =
        ENNReal.ofReal (heatKernel ((δ + q) / 2) (Y - z)) := by
    simpa only [show δ / 2 + q / 2 = (δ + q) / 2 by ring] using
      lintegral_heatKernel_initialProduct
        (div_pos hδ (show 0 < (2 : ℝ) by norm_num))
        (div_pos hq (show 0 < (2 : ℝ) by norm_num)) z Y
  calc
    _ = ∫⁻ z : Plane,
          ENNReal.ofReal (heatKernel (r / 2) (z - X)) *
            ENNReal.ofReal (heatKernel ((δ + q) / 2) (Y - z)) := by
          apply lintegral_congr
          intro z
          rw [lintegral_const_mul
            (ENNReal.ofReal (heatKernel (r / 2) (z - X)))
            (by
              exact (((measurable_heatKernel (δ / 2)).comp
                (measurable_id.sub_const z)).ennreal_ofReal).mul
                  (((measurable_heatKernel (q / 2)).comp
                    (measurable_const.sub measurable_id)).ennreal_ofReal))]
          rw [hrow z]
    _ = ENNReal.ofReal (heatKernel ((r + (δ + q)) / 2) (Y - X)) := by
          simpa only [add_assoc, show r / 2 + (δ + q) / 2 = (r + (δ + q)) / 2 by ring] using
            lintegral_heatKernel_initialProduct
              (div_pos hr (show 0 < (2 : ℝ) by norm_num))
              (div_pos (add_pos hδ hq) (show 0 < (2 : ℝ) by norm_num)) X Y
    _ = ENNReal.ofReal (heatKernel ((r + δ + q) / 2) (Y - X)) := by
          congr 2
          congr 1
          ring

/-- A free two-particle heat kernel separates into its center and gap heat
kernels. -/
theorem freeKernel_two_center_gap {t : ℝ} (ht : 0 < t)
    (x y : Configuration 2) :
    freeKernel 2 t x y =
      heatKernel (t / 2) ((1 / 2 : ℝ) • (y 0 + y 1) -
        (1 / 2 : ℝ) • (x 0 + x 1)) *
      heatKernel (2 * t) ((y 1 - y 0) - (x 1 - x 0)) := by
  let d₀ : Plane := y 0 - x 0
  let d₁ : Plane := y 1 - x 1
  have hp := heatKernel_pair_factor ht (-d₀) (-d₁) (0 : Plane)
  rw [show 0 - -d₀ = d₀ by abel, show 0 - -d₁ = d₁ by abel,
    show 0 - (1 / 2 : ℝ) • (-d₀ + -d₁) =
      (1 / 2 : ℝ) • (d₀ + d₁) by module,
    show (-d₁) - (-d₀) = - (d₁ - d₀) by abel, heatKernel_neg] at hp
  have hcenter : (1 / 2 : ℝ) • (d₀ + d₁) =
      (1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1) := by
    dsimp [d₀, d₁]
    module
  have hgap : d₁ - d₀ = (y 1 - y 0) - (x 1 - x 0) := by
    dsimp [d₀, d₁]
    abel
  rw [hcenter, hgap] at hp
  simpa only [freeKernel, Fin.prod_univ_two, d₀, d₁] using hp

/-- The two-particle collision correction separates into a center heat kernel
and the two endpoint gap heat kernels. -/
theorem twoParticleCorrection_eq_centerGap (θ h : ℝ) (x y : Configuration 2) :
    twoParticleCorrection θ h x y =
      ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h,
        (ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
          (ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
            ENNReal.ofReal (heatKernel (2 * (h - u)) (y 1 - y 0)))) *
          ENNReal.ofReal (heatKernel (h / 2)
            ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1))) := by
  rw [twoParticleCorrection_eq_planar_integral]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hrpos : 0 < r := hr.1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hδ : 0 < u - r := sub_pos.mpr hu.1
  have hq : 0 < h - u := sub_pos.mpr hu.2
  let c : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
    (ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
      ENNReal.ofReal (heatKernel (2 * (h - u)) (y 1 - y 0)))
  let A : Plane → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (heatKernel (r / 2)
      (z - (1 / 2 : ℝ) • (x 0 + x 1)))
  let B : Plane → Plane → ℝ≥0∞ := fun z w =>
    ENNReal.ofReal (heatKernel ((u - r) / 2) (w - z))
  let D : Plane → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (heatKernel ((h - u) / 2)
      ((1 / 2 : ℝ) • (y 0 + y 1) - w))
  have hBD : Measurable (Function.uncurry (fun z w => B z w * D w)) := by
    dsimp [B, D]
    exact (((measurable_heatKernel ((u - r) / 2)).comp
      (measurable_snd.sub measurable_fst)).ennreal_ofReal).mul
        (((measurable_heatKernel ((h - u) / 2)).comp
          (measurable_const.sub measurable_snd)).ennreal_ofReal)
  have hcenter := lintegral_heatKernel_center_chainENN hrpos hδ hq
    ((1 / 2 : ℝ) • (x 0 + x 1)) ((1 / 2 : ℝ) • (y 0 + y 1))
  have hspace :
      (∫⁻ z : Plane, ∫⁻ w : Plane, c * (A z * (B z w * D w))) =
        c * ENNReal.ofReal (heatKernel (h / 2)
          ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1))) := by
    rw [lintegral_const_mul_double_plane (by
      dsimp [A, B, D]
      exact (((measurable_heatKernel (r / 2)).comp
        (measurable_fst.sub_const ((1 / 2 : ℝ) • (x 0 + x 1)))).ennreal_ofReal).mul
          ((((measurable_heatKernel ((u - r) / 2)).comp
              (measurable_snd.sub measurable_fst)).ennreal_ofReal).mul
            (((measurable_heatKernel ((h - u) / 2)).comp
              (measurable_const.sub measurable_snd)).ennreal_ofReal))) c]
    have hsum : r + (u - r) + (h - u) = h := by ring
    have htime : (r + (u - r) + (h - u)) / 2 = h / 2 := by rw [hsum]
    congr 1
    dsimp [A, B, D]
    simpa only [htime] using hcenter
  calc
    (∫⁻ z : Plane, ∫⁻ w : Plane,
        ENNReal.ofReal (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r) *
            heatKernel ((u - r) / 2) (w - z)) *
          ENNReal.ofReal (heatKernel (h - u) (y 0 - w) *
            heatKernel (h - u) (y 1 - w))) =
        ∫⁻ z : Plane, ∫⁻ w : Plane, c * (A z * (B z w * D w)) := by
          apply lintegral_congr
          intro z
          apply lintegral_congr
          intro w
          have hIn := heatKernel_pair_factor hrpos (x 0) (x 1) z
          have hOut₀ : heatKernel (h - u) (y 0 - w) =
              heatKernel (h - u) (w - y 0) := by
            rw [show y 0 - w = -(w - y 0) by abel, heatKernel_neg]
          have hOut₁ : heatKernel (h - u) (y 1 - w) =
              heatKernel (h - u) (w - y 1) := by
            rw [show y 1 - w = -(w - y 1) by abel, heatKernel_neg]
          have hOut := heatKernel_pair_factor hq (y 0) (y 1) w
          rw [hIn, hOut₀, hOut₁, hOut,
            show heatKernel ((h - u) / 2)
                (w - (1 / 2 : ℝ) • (y 0 + y 1)) =
              heatKernel ((h - u) / 2)
                ((1 / 2 : ℝ) • (y 0 + y 1) - w) by
                  rw [show w - (1 / 2 : ℝ) • (y 0 + y 1) =
                    -((1 / 2 : ℝ) • (y 0 + y 1) - w) by abel, heatKernel_neg]]
          dsimp [c, A, B, D]
          have hcoef : 4 * Real.pi * scalarDensity θ (u - r) =
              Real.pi * (scalarDensity θ (u - r) * 4) := by ring
          rw [ENNReal.ofReal_mul (heatKernel_nonneg
              (div_nonneg hrpos.le (by norm_num : (0 : ℝ) ≤ 2)) _),
            ENNReal.ofReal_mul (mul_nonneg
              (mul_nonneg (by positivity : 0 ≤ (4 : ℝ)) (by positivity : 0 ≤ Real.pi))
              (scalarDensity_pos θ hδ).le),
            ENNReal.ofReal_mul (heatKernel_nonneg
              (div_nonneg hq.le (by norm_num : (0 : ℝ) ≤ 2)) _)]
          rw [hcoef]
          let a : ℝ≥0∞ := ENNReal.ofReal
            (heatKernel (r / 2) (z - (1 / 2 : ℝ) • (x 0 + x 1)))
          let b : ℝ≥0∞ := ENNReal.ofReal (heatKernel ((u - r) / 2) (w - z))
          let d : ℝ≥0∞ := ENNReal.ofReal
            (heatKernel ((h - u) / 2) ((1 / 2 : ℝ) • (y 0 + y 1) - w))
          let e : ℝ≥0∞ := ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0))
          let f : ℝ≥0∞ := ENNReal.ofReal (heatKernel (2 * (h - u)) (y 1 - y 0))
          let g : ℝ≥0∞ := ENNReal.ofReal (Real.pi * (scalarDensity θ (u - r) * 4))
          change ((a * e) * (g * b)) * (d * f) =
            (g * (e * f)) * (a * (b * d))
          ac_rfl
    _ = c * ENNReal.ofReal (heatKernel (h / 2)
          ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1))) := hspace

end Critical2DKPZ.SHF.Flow

end
