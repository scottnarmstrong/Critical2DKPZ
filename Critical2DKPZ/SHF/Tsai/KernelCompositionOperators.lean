/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelOperator

/-! # Composition of the actual kernel operators

Positive data allow conversion to the extended positive action. Tonelli then
identifies composition without moving a signed nonintegrable expression
through a real integral. Positive and negative parts extend the identity to
all `L²` data.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Positive data have a positive real kernel action. -/
theorem configurationKernelAction_nonneg {n : ℕ}
    (K : Configuration n → Configuration n → ℝ≥0∞) {F : Configuration n → ℝ}
    (hF : ∀ y, 0 ≤ F y) (x : Configuration n) : 0 ≤ configurationKernelAction K F x :=
  integral_nonneg fun y => mul_nonneg ENNReal.toReal_nonneg (hF y)

/-- For positive `L²` data, the real action is the real version of the literal positive action. -/
theorem ofReal_configurationKernelAction {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    {F : Configuration n → ℝ} (hF : MemLp F 2) (hF0 : ∀ y, 0 ≤ F y) :
    ∀ᵐ x : Configuration n, ENNReal.ofReal (configurationKernelAction K F x) =
      ∫⁻ y, K x y * ENNReal.ofReal (F y) := by
  have hfinite := Measure.ae_ae_of_ae_prod (configurationKernel_ne_top_of_formBound hK hc hKF)
  filter_upwards [hfinite, ae_integrable_configurationKernelAction hK hc hKF hF] with x hx hI
  change ENNReal.ofReal (∫ y, (K x y).toReal * F y) = _
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun y => mul_nonneg ENNReal.toReal_nonneg (hF0 y))]
  apply lintegral_congr_ae
  filter_upwards [hx] with y hy
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy]

/-- The real action of a composed kernel agrees a.e. with iterated action on positive data. -/
theorem configurationKernelAction_comp_of_nonneg {n : ℕ}
    {K L : Configuration n → Configuration n → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (hKF : FormBound volume volume K c) (hLF : FormBound volume volume L d)
    {F : Configuration n → ℝ} (hFm : Measurable F) (hF : MemLp F 2) (hF0 : ∀ y, 0 ≤ F y) :
    configurationKernelAction (spatialKernelComp volume K L) F =ᵐ[volume]
      configurationKernelAction K (configurationKernelAction L F) := by
  have hcompm := measurable_spatialKernelComp volume hK hL
  have hcompF := hKF.comp volume volume volume hK hL hLF
  have hR := memLp_configurationKernelAction hL hd hLF hF
  have hR0 := configurationKernelAction_nonneg L hF0
  have hleft := ofReal_configurationKernelAction hcompm (ENNReal.mul_ne_top hc hd) hcompF hF hF0
  have hright := ofReal_configurationKernelAction hK hc hKF hR hR0
  have hmiddle := ofReal_configurationKernelAction hL hd hLF hF hF0
  filter_upwards [hleft, hright] with x hx hx'
  have heq : ENNReal.ofReal (configurationKernelAction (spatialKernelComp volume K L) F x) =
      ENNReal.ofReal (configurationKernelAction K (configurationKernelAction L F) x) := by
    rw [hx, hx', spatialKernelComp_action_eq volume volume hK hL hFm.ennreal_ofReal x]
    apply lintegral_congr_ae
    filter_upwards [hmiddle] with y hy
    rw [hy]
  have h := congrArg ENNReal.toReal heq
  simpa only [ENNReal.toReal_ofReal (configurationKernelAction_nonneg (spatialKernelComp volume K L) hF0 x),
    ENNReal.toReal_ofReal (configurationKernelAction_nonneg K hR0 x)] using h

/-- The bounded-operator composition identity on positive actual `L²` input. -/
theorem configurationKernelOperator_comp_toLp_of_nonneg {n : ℕ}
    {K L : Configuration n → Configuration n → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (hKF : FormBound volume volume K c) (hLF : FormBound volume volume L d)
    {F : Configuration n → ℝ} (hFm : Measurable F) (hF : MemLp F 2) (hF0 : ∀ y, 0 ≤ F y) :
    configurationKernelOperator (measurable_spatialKernelComp volume hK hL) (ENNReal.mul_ne_top hc hd)
      (hKF.comp volume volume volume hK hL hLF) (hF.toLp F) =
      configurationKernelOperator hK hc hKF (configurationKernelOperator hL hd hLF (hF.toLp F)) := by
  have hleft := coe_configurationKernelOperator_toLp
    (measurable_spatialKernelComp volume hK hL) (ENNReal.mul_ne_top hc hd)
    (hKF.comp volume volume volume hK hL hLF) hF
  have hmiddle := coe_configurationKernelOperator_toLp hL hd hLF hF
  have hright := coe_configurationKernelOperator hK hc hKF
    (configurationKernelOperator hL hd hLF (hF.toLp F))
  rw [configurationKernelAction_congr_ae K hmiddle] at hright
  apply Lp.ext
  exact hleft.trans ((configurationKernelAction_comp_of_nonneg hK hL hc hd hKF hLF hFm hF hF0).trans
    hright.symm)

/-- Spatial composition of positive kernels is composition of their actual bounded `L²` operators. -/
theorem configurationKernelOperator_comp {n : ℕ}
    {K L : Configuration n → Configuration n → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (hKF : FormBound volume volume K c) (hLF : FormBound volume volume L d) :
    configurationKernelOperator (measurable_spatialKernelComp volume hK hL) (ENNReal.mul_ne_top hc hd)
      (hKF.comp volume volume volume hK hL hLF) =
      (configurationKernelOperator hK hc hKF).comp (configurationKernelOperator hL hd hLF) := by
  let A := configurationKernelOperator (measurable_spatialKernelComp volume hK hL)
    (ENNReal.mul_ne_top hc hd) (hKF.comp volume volume volume hK hL hLF)
  let B := (configurationKernelOperator hK hc hKF).comp (configurationKernelOperator hL hd hLF)
  change A = B
  apply ContinuousLinearMap.ext
  intro G
  let Fp (x : Configuration n) := max (G x) 0
  let Fn (x : Configuration n) := max (-G x) 0
  have hp : MemLp Fp 2 := (Lp.memLp G).pos_part
  have hn : MemLp Fn 2 := (Lp.memLp G).neg_part
  have hpm : Measurable Fp := (Lp.stronglyMeasurable G).measurable.max measurable_const
  have hnm : Measurable Fn := (Lp.stronglyMeasurable G).measurable.neg.max measurable_const
  have hpos : A (hp.toLp Fp) = B (hp.toLp Fp) :=
    configurationKernelOperator_comp_toLp_of_nonneg hK hL hc hd hKF hLF hpm hp (fun x => le_max_right _ _)
  have hneg : A (hn.toLp Fn) = B (hn.toLp Fn) :=
    configurationKernelOperator_comp_toLp_of_nonneg hK hL hc hd hKF hLF hnm hn (fun x => le_max_right _ _)
  have hdecomp : G = hp.toLp Fp - hn.toLp Fn := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (hp.toLp Fp) (hn.toLp Fn), hp.coeFn_toLp, hn.coeFn_toLp]
      with x hsub hx hx'
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hx, hx']
    exact (posPart_sub_negPart (G x)).symm
  calc
    A G = A (hp.toLp Fp - hn.toLp Fn) := congrArg A hdecomp
    _ = A (hp.toLp Fp) - A (hn.toLp Fn) := map_sub A _ _
    _ = B (hp.toLp Fp) - B (hn.toLp Fn) := congrArg₂ (· - ·) hpos hneg
    _ = B (hp.toLp Fp - hn.toLp Fn) := (map_sub B _ _).symm
    _ = B G := congrArg B hdecomp.symm

end Critical2DKPZ.SHF.Tsai

end
