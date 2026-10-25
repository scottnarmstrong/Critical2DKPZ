/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleGapCut
public import Critical2DKPZ.SHF.DeltaBose.SingletonSymmetry
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The two-particle moment-kernel semigroup -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal RealInnerProductSpace

namespace Critical2DKPZ.SHF.Flow

/-- The semigroup law `Q_a Q_b = Q_{a+b}` of the two-particle delta-Bose kernel, as a proposition. -/
def MomentKernelTwoSemigroup (θ : ℝ) : Prop :=
  ∀ {a b : ℝ}, 0 < a → 0 < b →
    ∀ᵐ xy : Configuration 2 × Configuration 2,
      ∫⁻ w, momentKernel 2 θ a xy.1 w * momentKernel 2 θ b w xy.2 =
        momentKernel 2 θ (a + b) xy.1 xy.2

private theorem measurable_momentKernel_two_right {θ t : ℝ} (ht : 0 < t)
    (x : Configuration 2) :
    Measurable (fun y : Configuration 2 => momentKernel 2 θ t x y) := by
  have hcenter : Measurable (fun y : Configuration 2 =>
      (1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1)) := by
    fun_prop
  have hgap : Measurable (fun y : Configuration 2 => y 1 - y 0) := by
    fun_prop
  have heq : (fun y : Configuration 2 => momentKernel 2 θ t x y) =
      (fun y => ENNReal.ofReal (heatKernel (t / 2)
          ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1))) *
        twoParticleGapKernel θ t (x 1 - x 0) (y 1 - y 0)) := by
    funext y
    exact momentKernel_two_eq_centerGapProduct ht x y
  rw [heq]
  exact ((measurable_heatKernel (t / 2)).comp hcenter).ennreal_ofReal.mul
    ((measurable_twoParticleGapKernel θ t (x 1 - x 0)).comp hgap)

/-- The relative-coordinate kernel is symmetric in its endpoints. -/
theorem twoParticleGapKernel_symm {θ h : ℝ} (hh : 0 < h) (x y : Plane) :
    twoParticleGapKernel θ h x y = twoParticleGapKernel θ h y x := by
  let X : Configuration 2 :=
    ![(- (1 / 2 : ℝ) • x), (1 / 2 : ℝ) • x]
  let Y : Configuration 2 :=
    ![(- (1 / 2 : ℝ) • y), (1 / 2 : ℝ) • y]
  have hXcenter : (1 / 2 : ℝ) • (X 0 + X 1) = 0 := by
    dsimp [X]
    simp
  have hYcenter : (1 / 2 : ℝ) • (Y 0 + Y 1) = 0 := by
    dsimp [Y]
    simp
  have hXgap : X 1 - X 0 = x := by
    dsimp [X]
    simp
    module
  have hYgap : Y 1 - Y 0 = y := by
    dsimp [Y]
    simp
    module
  have hconst : ENNReal.ofReal (heatKernel (h / 2) (0 : Plane)) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (heatKernel_pos (div_pos hh (by norm_num)) 0)).ne'
  have hconstTop : ENNReal.ofReal (heatKernel (h / 2) (0 : Plane)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hsymm := momentKernel_two_symm θ h X Y
  rw [momentKernel_two_eq_centerGapProduct hh X Y,
    momentKernel_two_eq_centerGapProduct hh Y X] at hsymm
  have hsymm' : ENNReal.ofReal (heatKernel (h / 2) (0 : Plane)) *
      twoParticleGapKernel θ h x y =
        ENNReal.ofReal (heatKernel (h / 2) (0 : Plane)) *
          twoParticleGapKernel θ h y x := by
    simpa only [hXcenter, hYcenter, hXgap, hYgap, sub_self] using hsymm
  have hinv := ENNReal.inv_mul_cancel hconst hconstTop
  calc
    twoParticleGapKernel θ h x y =
        (ENNReal.ofReal (heatKernel (h / 2) (0 : Plane)))⁻¹ *
          (ENNReal.ofReal (heatKernel (h / 2) (0 : Plane)) *
            twoParticleGapKernel θ h x y) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := congrArg
      (fun z : ℝ≥0∞ => (ENNReal.ofReal (heatKernel (h / 2) (0 : Plane)))⁻¹ * z) hsymm'
    _ = twoParticleGapKernel θ h y x := by rw [← mul_assoc, hinv, one_mul]

/-- The two-particle delta-Bose kernel satisfies the semigroup law pointwise. -/
theorem momentKernel_two_semigroup_pointwise (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y : Configuration 2) :
    (∫⁻ w, momentKernel 2 θ a x w * momentKernel 2 θ b w y) =
      momentKernel 2 θ (a + b) x y := by
  let f : Configuration 2 → ℝ≥0∞ := fun w =>
    momentKernel 2 θ a x w * momentKernel 2 θ b w y
  have hA : Measurable (fun w : Configuration 2 => momentKernel 2 θ a x w) :=
    measurable_momentKernel_two_right ha x
  have hB : Measurable (fun w : Configuration 2 => momentKernel 2 θ b w y) := by
    have hswap : (fun w : Configuration 2 => momentKernel 2 θ b w y) =
        (fun w => momentKernel 2 θ b y w) := by
      funext w
      exact momentKernel_two_symm θ b w y
    rw [hswap]
    exact measurable_momentKernel_two_right hb y
  have hf : Measurable f := hA.mul hB
  let e : Configuration 2 ≃ᵐ Plane × Plane := MeasurableEquiv.finTwoArrow
  have hpair : Measurable (fun p : Plane × Plane => f (e.symm p)) :=
    hf.comp e.symm.measurable
  have hF : Measurable (Function.uncurry (fun x₀ x₁ : Plane =>
      f (e.symm (x₀, x₁)))) := by
    exact hpair.comp (measurable_fst.prodMk measurable_snd)
  have hconfigToPair :
      (∫⁻ w : Configuration 2, f w) =
        ∫⁻ x₀ : Plane, ∫⁻ x₁ : Plane, f (e.symm (x₀, x₁)) := by
    have hmp : MeasurePreserving e (volume : Measure (Configuration 2))
        (volume : Measure (Plane × Plane)) := volume_preserving_finTwoArrow Plane
    calc
      (∫⁻ w : Configuration 2, f w) =
          ∫⁻ w : Configuration 2, (fun p : Plane × Plane => f (e.symm p)) (e w) := by
            apply lintegral_congr_ae
            filter_upwards [] with w
            exact (congrArg f (e.symm_apply_apply w)).symm
      _ = ∫⁻ p : Plane × Plane, f (e.symm p) := hmp.lintegral_comp hpair
      _ = ∫⁻ x₀ : Plane, ∫⁻ x₁ : Plane, f (e.symm (x₀, x₁)) := by
            rw [Measure.volume_eq_prod,
              lintegral_prod (μ := volume) (ν := volume) _ hpair.aemeasurable]
  have hcenterGap := lintegral_pair_center_gap (F := fun x₀ x₁ =>
    f (e.symm (x₀, x₁))) hF
  let cx : Plane := (1 / 2 : ℝ) • (x 0 + x 1)
  let cy : Plane := (1 / 2 : ℝ) • (y 0 + y 1)
  let gx : Plane := x 1 - x 0
  let gy : Plane := y 1 - y 0
  let A : Plane → ℝ≥0∞ := fun c =>
    ENNReal.ofReal (heatKernel (a / 2) (c - cx)) *
      ENNReal.ofReal (heatKernel (b / 2) (cy - c))
  let B : Plane → ℝ≥0∞ := fun g =>
    twoParticleGapKernel θ a gx g * twoParticleGapKernel θ b g gy
  have hAmeas : Measurable A := by
    dsimp [A]
    exact (((measurable_heatKernel (a / 2)).comp (measurable_id.sub_const cx)).ennreal_ofReal).mul
      (((measurable_heatKernel (b / 2)).comp (measurable_const.sub measurable_id)).ennreal_ofReal)
  have hBmeas : Measurable B := by
    have hB' : Measurable (fun g : Plane =>
        twoParticleGapKernel θ a gx g * twoParticleGapKernel θ b gy g) :=
      (measurable_twoParticleGapKernel θ a gx).mul
        (measurable_twoParticleGapKernel θ b gy)
    have hB_eq : B = fun g : Plane =>
        twoParticleGapKernel θ a gx g * twoParticleGapKernel θ b gy g := by
      funext g
      dsimp [B]
      rw [twoParticleGapKernel_symm hb g gy]
    rw [hB_eq]
    exact hB'
  have hsplit (g : Plane) :
      (∫⁻ c : Plane, A c * B g) = B g * ∫⁻ c : Plane, A c := by
    calc
      (∫⁻ c : Plane, A c * B g) = ∫⁻ c : Plane, B g * A c := by
        apply lintegral_congr_ae
        filter_upwards [] with c
        exact mul_comm _ _
      _ = B g * ∫⁻ c : Plane, A c := lintegral_const_mul (B g) hAmeas
  have hcenterValue : (∫⁻ c : Plane, A c) =
      ENNReal.ofReal (heatKernel ((a + b) / 2) (cy - cx)) := by
    exact lintegral_twoParticle_center_heat_mul ha hb cx cy
  have hgapValue : (∫⁻ g : Plane, B g) =
      twoParticleGapKernel θ (a + b) gx gy := by
    exact twoParticleGapKernel_semigroup ha hb gx gy
  calc
    (∫⁻ w, f w) = ∫⁻ x₀ : Plane, ∫⁻ x₁ : Plane,
        f (e.symm (x₀, x₁)) := hconfigToPair
    _ = ∫⁻ g : Plane, ∫⁻ c : Plane,
        f (e.symm (c - (1 / 2 : ℝ) • g, c + (1 / 2 : ℝ) • g)) := hcenterGap
    _ = ∫⁻ g : Plane, ∫⁻ c : Plane, A c * B g := by
      apply lintegral_congr_ae
      filter_upwards [] with g
      apply lintegral_congr_ae
      filter_upwards [] with c
      let w : Configuration 2 := e.symm (c - (1 / 2 : ℝ) • g,
        c + (1 / 2 : ℝ) • g)
      have hw0 : w 0 = c - (1 / 2 : ℝ) • g := by
        simp [w, e]
      have hw1 : w 1 = c + (1 / 2 : ℝ) • g := by
        simp [w, e]
      have hwcenter : (1 / 2 : ℝ) • (w 0 + w 1) = c := by
        rw [hw0, hw1]
        module
      have hwgap : w 1 - w 0 = g := by
        rw [hw0, hw1]
        module
      change momentKernel 2 θ a x w * momentKernel 2 θ b w y = A c * B g
      rw [momentKernel_two_eq_centerGapProduct ha x w,
        momentKernel_two_eq_centerGapProduct hb w y]
      rw [hwcenter, hwgap]
      simp only [A, B, cx, cy, gx, gy]
      ac_rfl
    _ = (∫⁻ c : Plane, A c) * (∫⁻ g : Plane, B g) := by
      calc
        _ = ∫⁻ g : Plane, B g * ∫⁻ c : Plane, A c := by
          apply lintegral_congr_ae
          filter_upwards [] with g
          exact hsplit g
        _ = (∫⁻ c : Plane, A c) * (∫⁻ g : Plane, B g) := by
          calc
            (∫⁻ g : Plane, B g * ∫⁻ c : Plane, A c) =
                ∫⁻ g : Plane, (∫⁻ c : Plane, A c) * B g := by
                  apply lintegral_congr_ae
                  filter_upwards [] with g
                  exact mul_comm _ _
            _ = (∫⁻ c : Plane, A c) * (∫⁻ g : Plane, B g) :=
              lintegral_const_mul (∫⁻ c : Plane, A c) hBmeas
    _ = ENNReal.ofReal (heatKernel ((a + b) / 2) (cy - cx)) *
          twoParticleGapKernel θ (a + b) gx gy := by
      rw [hcenterValue, hgapValue]
    _ = momentKernel 2 θ (a + b) x y := by
      symm
      exact momentKernel_two_eq_centerGapProduct (add_pos ha hb) x y

/-- The two-particle delta-Bose kernel satisfies the semigroup law. -/
theorem momentKernel_two_semigroup (θ : ℝ) : MomentKernelTwoSemigroup θ := by
  intro a b ha hb
  filter_upwards [] with xy
  exact momentKernel_two_semigroup_pointwise θ ha hb xy.1 xy.2

end Critical2DKPZ.SHF.Flow

end
