/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HeatFieldJointLimit
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.TestFnDilate
import Critical2DKPZ.Extensions.ScaleLimit.TimeReversal
import Critical2DKPZ.Extensions.ScaleLimit.Centring
import Critical2DKPZ.Extensions.ScaleLimit.FiniteFamilyLaw
import Critical2DKPZ.Extensions.ScaleLimit.FiniteProbability
import Critical2DKPZ.Extensions.ScaleLimit.SeqReduction
import Critical2DKPZ.Extensions.Common.Canonical
import Mathlib.Tactic

/-! # Joint transfer from the heat-start field to the fixed reversed KPZ field

One check field is selected before all widths and finite collections. Its
uniform first-moment comparison transfers the heat-start Gaussian limit, and
its finite tested laws identify the resulting limit for the prescribed KPZ
version on the original probability space.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The geometric-width KPZ fields have Brownian finite-dimensional limits at
unit time for every centered nonnegative unit-mass mollifier. -/
theorem geometric_kpz_joint_limit (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (ψ : TestFn) (hψ : ∀ y, 0 ≤ ψ y) (hψ1 : (∫ y, ψ y) = 1)
    (hψb : SmallScales.barycentre ψ = 0) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ I : Finset ℝ≥0,
      (∀ i ∈ I, 0 < i) →
      TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
        H 1 0 ω (ψ.dilate (Real.sqrt (tau ρ (nL ρ L (i.val : ℝ)))) 0) / Real.sqrt L)
        atTop id (fun _ => P) (BrownianReal.projectiveFamily I) := by
  obtain ⟨Hc, hcm, hLaw, _hRate, hComp⟩ := exists_checkField ϑ P Z hZ
  obtain ⟨C, ε₀, hε₀, hCompare⟩ := hComp ψ hψ hψ1 hψb
  have hcm' (f : TestFn) : AEMeasurable (Hc f) P :=
    ((hcm f).mono (Common.shfSigma_le ϑ P Z hZ) le_rfl).aemeasurable
  have hHm (f : TestFn) : AEMeasurable (fun ω => H 1 0 ω f) P :=
    (memLp_kpz_two ϑ P Z hZ H hH 1 zero_lt_one f).aemeasurable
  obtain ⟨ρ₀, hρ₀, hHeat⟩ := heatField_joint_limit ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ I hI
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  let XC : Set.Ioi (0 : ℝ) → Ω → I → ℝ := fun L ω i =>
    Hc (ψ.dilate (Real.sqrt (tau ρ (nL ρ L (i.val : ℝ)))) 0) ω / Real.sqrt L
  have hXCm (L : Set.Ioi (0 : ℝ)) : AEMeasurable (XC L) P :=
    aemeasurable_pi_iff.mpr fun i => (hcm' _).div_const _
  have hXC : TendstoInDistribution XC atTop id (fun _ => P) (BrownianReal.projectiveFamily I) := by
    apply tendstoInDistribution_of_tendstoInMeasure_sub XC id (hHeat ρ hρ I hI) _ hXCm
    change TendstoInMeasure P (fun L ω (i : I) => XC L ω i -
      normalizedHeatField P Z ρ L (i.val : ℝ) ω) atTop (fun _ => 0)
    apply tendstoInMeasure_finite_pi P atTop _ (fun _ _ => 0)
    intro i
    let s : ℝ := i.val
    have hs : 0 < s := by exact_mod_cast hI i.val i.property
    let width : Set.Ioi (0 : ℝ) → ℝ := fun L => Real.sqrt (tau ρ (nL ρ L s))
    let D : Set.Ioi (0 : ℝ) → Ω → ℝ := fun L ω =>
      Hc (ψ.dilate (width L) 0) ω -
        (geometricField Z ρ (nL ρ L s) ω - ∫ ω', geometricField Z ρ (nL ρ L s) ω' ∂P)
    have hb : ∀ᶠ L in atTop, Integrable (D L) P ∧ (∫ ω, |D L ω| ∂P) ≤ C := by
      filter_upwards [(geometric_width_tendsto_zero ρ s hρ1 hs).eventually (gt_mem_nhds hε₀),
        eventually_one_le_nL ρ s hρ1 hs] with L hwidth hN
      have hwidthpos : 0 < width L := Real.sqrt_pos.mpr (tau_pos hρ1 _)
      have h := hCompare (width L) ⟨hwidthpos, hwidth⟩
      have hF : geometricField Z ρ (nL ρ L s) = Fheat Z (tau ρ (nL ρ L s)) 0 := by
        funext ω
        exact geometricField_of_pos Z ρ (by omega : 0 < nL ρ L s) ω
      simpa only [D, width, Real.sq_sqrt (tau_pos hρ1 _).le, hF] using h
    have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
      tendsto_Ioi_atTop.mp tendsto_id
    have hp := tendstoInMeasure_div_of_integral_abs_bound P atTop D
      (fun L => Real.sqrt L) (Real.tendsto_sqrt_atTop.comp hL) C hb
    apply hp.congr _ Filter.EventuallyEq.rfl
    intro L
    filter_upwards [] with ω
    dsimp only [D, width, s, XC, normalizedHeatField]
    ring
  have hXAm (L : Set.Ioi (0 : ℝ)) : AEMeasurable
      (fun ω (i : I) => H 1 0 ω (ψ.dilate (Real.sqrt (tau ρ (nL ρ L (i.val : ℝ)))) 0) / Real.sqrt L) P :=
    aemeasurable_pi_iff.mpr fun i => (hHm _).div_const _
  have hmaps (L : Set.Ioi (0 : ℝ)) : P.map (XC L) = P.map
      (fun ω (i : I) => H 1 0 ω (ψ.dilate (Real.sqrt (tau ρ (nL ρ L (i.val : ℝ)))) 0) / Real.sqrt L) := by
    let f : I → TestFn := fun i => ψ.dilate (Real.sqrt (tau ρ (nL ρ L (i.val : ℝ)))) 0
    have hmC : AEMeasurable (fun ω i => Hc (f i) ω) P :=
      aemeasurable_pi_iff.mpr fun i => hcm' _
    have hmA : AEMeasurable (fun ω i => H 1 0 ω (f i)) P :=
      aemeasurable_pi_iff.mpr fun i => hHm _
    have hraw : P.map (fun ω i => Hc (f i) ω) = P.map (fun ω i => H 1 0 ω (f i)) := by
      apply map_fintype_eq_of_fin_laws P P _ _ hmC hmA
      intro k g
      exact hLaw H hH k (fun j => f (g j))
    exact map_div_family_eq P P _ _ hmC hmA hraw (Real.sqrt L)
  exact (tendstoInDistribution_congr_of_map_eq hXCm hXAm aemeasurable_id hmaps).mp hXC

end Critical2DKPZ.Extensions.ScaleLimit
