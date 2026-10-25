/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.Blocks
public import Mathlib.Probability.Independence.Basic
import Critical2DKPZ.Assembly.Final
import Critical2DKPZ.SmallScales.HeatStartMoments
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Mathlib.Tactic

/-! # Independence and first moments of positive geometric blocks

The reverse geometric grid is reordered on each finite prefix before applying
independence of consecutive flow increments. No equal-endpoint increment is used.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The heat mass is a measurable function of its underlying measure, even when
its integral is not finite. Both totalizations give zero at infinite mass. -/
theorem measurable_heatMass {δ : ℝ} (hδ : 0 < δ) :
    Measurable (fun μ : Measure (Plane × Plane) => ∫ p, heatKernel δ p.1 ∂μ) := by
  have hm : Measurable (fun p : Plane × Plane => heatKernel δ p.1) :=
    (measurable_heatKernel δ).comp measurable_fst
  have heq : (fun μ : Measure (Plane × Plane) => ∫ p, heatKernel δ p.1 ∂μ) =
      fun μ => (∫⁻ p, ENNReal.ofReal (heatKernel δ p.1) ∂μ).toReal := by
    funext μ
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => heatKernel_nonneg hδ.le p.1)
      hm.aestronglyMeasurable
  rw [heq]
  exact (Measure.measurable_lintegral hm.ennreal_ofReal).ennreal_toReal

/-- The strictly positive block indices form one independent family. -/
theorem iIndepFun_geometric_increments (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) :
    iIndepFun (fun j : ℕ => Z (tau ρ (j + 1)) (tau ρ j)) P := by
  classical
  have hD := Assembly.denseSHFAt ϑ P Z hZ (Set.range (tau ρ))
    (Set.countable_range _) (by rintro t ⟨j, rfl⟩; exact (tau_pos hρ j).le)
  apply iIndepFun_iff_finset.mpr
  intro S
  let K := S.sup id + 1
  have hj (j : S) : j.val < K := by
    have hb : j.val ≤ S.sup id := Finset.le_sup (f := id) j.property
    dsimp [K]
    omega
  have hind := hD.2.2.1 K (fun i : Fin (K + 1) => tau ρ (K - i.val))
    (by
      intro i j hij
      apply strictAnti_tau hρ
      have hi := i.isLt
      have hj := j.isLt
      change i.val < j.val at hij
      omega)
    (fun i => ⟨_, rfl⟩)
  let f : S → Fin K := fun j => ⟨K - (j.val + 1), by have := hj j; omega⟩
  have hf : Function.Injective f := by
    intro i j heq
    have heq' := congrArg Fin.val heq
    have hi := hj i
    have hj' := hj j
    apply Subtype.ext
    dsimp [f] at heq'
    omega
  have hpre := hind.precomp hf
  convert hpre using 1
  funext j
  have hbound := hj j
  have hleft : K - (f j).castSucc.val = j.val + 1 := by dsimp [f]; omega
  have hright : K - (f j).succ.val = j.val := by dsimp [f]; omega
  simp only [hleft, hright, Finset.restrict]

/-- Every positive-index block mass is measurable. -/
theorem measurable_blockMass (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) : Measurable (blockMass Z ρ (j + 1)) := by
  have h := (measurable_heatMass (tau_pos hρ (j + 1))).comp
    (hZ.1 _ _ (tau_pos hρ (j + 1)).le (tau_succ_lt hρ j))
  change Measurable (fun ω => ∫ p, heatKernel (tau ρ (j + 1)) p.1 * 1 ∂Z (tau ρ (j + 1)) (tau ρ j) ω)
  simpa only [Function.comp_def, mul_one] using h

/-- The positive-index block masses are mutually independent. -/
theorem iIndepFun_blockMass (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) : iIndepFun (fun j => blockMass Z ρ (j + 1)) P := by
  have h := (iIndepFun_geometric_increments ϑ P Z hZ hρ).comp
    (fun j μ => ∫ p, heatKernel (tau ρ (j + 1)) p.1 ∂μ)
    (fun j => measurable_heatMass (tau_pos hρ (j + 1)))
  change iIndepFun (fun j ω => ∫ p, heatKernel (tau ρ (j + 1)) p.1 * 1 ∂Z (tau ρ (j + 1)) (tau ρ j) ω) P
  simpa only [Function.comp_def, mul_one] using h


/-- Each positive-index block mass is almost surely strictly positive. -/
theorem blockMass_pos_ae (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) : ∀ᵐ ω ∂P, 0 < blockMass Z ρ (j + 1) ω := by
  have h := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
    (tau ρ (j + 1)) (tau ρ j) (tau ρ (j + 1)) 0 0
    (tau_pos hρ (j + 1)).le (tau_succ_lt hρ j) (tau_pos hρ (j + 1))).1
  simpa only [blockMass, Nat.add_sub_cancel, sub_zero, BoundedContinuousFunction.coe_zero,
    Pi.zero_apply, Real.exp_zero] using h

end Critical2DKPZ.Extensions.ScaleLimit
