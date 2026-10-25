/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.SHF.Positivity.PolymerHeatEhrhard
public import Critical2DKPZ.SHF.Positivity.PolymerHeatInverseMoment
public import Critical2DKPZ.SHF.Positivity.ProbabilityClosure
public import Critical2DKPZ.Provider.EhrhardTypeCharacterization
import Mathlib.Tactic

/-! # Positivity and Ehrhard type of critical-SHF heat pairings -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.SHF.Positivity

/-- At fixed parameters, a positive-time heat-start SHF pairing with bounded continuous log-terminal data is almost surely positive. Its logarithm is almost everywhere measurable and has an Ehrhard-type law. -/
theorem isCriticalSHF_heat_pairing_pos_isEhrhardType (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ) (hs : 0 ≤ s) (hst : s < t)
    (hδ : 0 < δ) :
    (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
      (fun y => Real.exp (h₀ y)) ω) ∧
    AEMeasurable (fun ω => Real.log (shfPairing Z s t
      (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P ∧
    IsEhrhardType (P.map fun ω => Real.log (shfPairing Z s t
      (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) := by
  let K : Plane → ℝ := fun y => heatKernel δ (y - x)
  let gOne : Plane →ᵇ ℝ := BoundedContinuousFunction.const Plane 1
  let gZero : Plane →ᵇ ℝ := BoundedContinuousFunction.const Plane 0
  let gExp : Plane →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun y : Plane => Real.exp (h₀ y), Real.continuous_exp.comp h₀.continuous⟩
      (2 * Real.exp ‖h₀‖) (by
        intro y z
        rw [Real.dist_eq]
        have hy : |h₀ y| ≤ ‖h₀‖ := by
          simpa only [Real.norm_eq_abs] using h₀.norm_coe_le_norm y
        have hz : |h₀ z| ≤ ‖h₀‖ := by
          simpa only [Real.norm_eq_abs] using h₀.norm_coe_le_norm z
        have hyexp : |Real.exp (h₀ y)| ≤ Real.exp ‖h₀‖ := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hy)
        have hzexp : |Real.exp (h₀ z)| ≤ Real.exp ‖h₀‖ := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hz)
        calc
          |Real.exp (h₀ y) - Real.exp (h₀ z)| ≤
              |Real.exp (h₀ y)| + |Real.exp (h₀ z)| := abs_sub _ _
          _ ≤ Real.exp ‖h₀‖ + Real.exp ‖h₀‖ := add_le_add hyexp hzexp
          _ = 2 * Real.exp ‖h₀‖ := by ring)
  let A : Ω → ℝ := fun ω => shfPairing Z s t K gOne ω
  let A_N : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, K p.1 ∂(polymerMeasure ϑ N s t ω)
  let Y : Ω → ℝ := fun ω => shfPairing Z s t K gExp ω
  let Y_N : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, K p.1 * Real.exp (h₀ p.2) ∂(polymerMeasure ϑ N s t ω)
  have hgExp (y : Plane) : gExp y = Real.exp (h₀ y) := by
    simp [gExp, BoundedContinuousFunction.mkOfBound_coe]
  have hOne := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ
    (s := s) (t := t) (δ := δ) hs hst hδ x gOne
  have hExp := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ
    (s := s) (t := t) (δ := δ) hs hst hδ x gExp
  have hAint : Integrable A P := by
    simpa only [A, K] using hOne.2.1
  have hYint : Integrable Y P := by
    simpa only [Y, K] using hExp.2.1
  have hDistA : TendstoInDistribution A_N atTop A (fun _ : ℕ => disorderLaw) P := by
    have hseq (N : ℕ) : (fun ω : Disorder =>
        ∫ p, heatKernel δ (p.1 - x) * gOne p.2
          ∂(polymerMeasure ϑ N s t ω)) =ᵐ[disorderLaw] A_N N := by
      filter_upwards [] with ω
      simp [A_N, K, gOne]
    exact hOne.2.2.2.congr hseq (Filter.Eventually.of_forall fun _ => rfl)
  have hDistY : TendstoInDistribution Y_N atTop Y (fun _ : ℕ => disorderLaw) P := by
    have hseq (N : ℕ) : (fun ω : Disorder =>
        ∫ p, heatKernel δ (p.1 - x) * gExp p.2
          ∂(polymerMeasure ϑ N s t ω)) =ᵐ[disorderLaw] Y_N N := by
      filter_upwards [] with ω
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by simp only [K, hgExp]
    exact hExp.2.2.2.congr hseq (Filter.Eventually.of_forall fun _ => rfl)
  have hPolymerZero := isEhrhardType_log_polymer_heat_pairing ϑ hs hst hδ x gZero
  have hANpos : ∀ᶠ N : ℕ in atTop, ∀ᵐ ω ∂disorderLaw, 0 < A_N N ω := by
    filter_upwards [hPolymerZero] with N hN
    filter_upwards [hN.1] with ω hω
    simpa [A_N, K, gZero] using hω.2
  obtain ⟨C, hInv⟩ := polymer_heat_pairing_inv_moment_le ϑ hs hst hδ x
  have hInvLIntegral : ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, (ENNReal.ofReal (A_N N ω))⁻¹ ∂disorderLaw ≤ ENNReal.ofReal C := by
    filter_upwards [hInv, hANpos] with N hmoment hpos
    have hInvNonneg : 0 ≤ᵐ[disorderLaw] fun ω => (A_N N ω)⁻¹ :=
      hpos.mono fun ω hω => inv_nonneg.mpr hω.le
    have hrecipEq : (fun ω => (ENNReal.ofReal (A_N N ω))⁻¹) =ᵐ[disorderLaw]
        fun ω => ENNReal.ofReal ((A_N N ω)⁻¹) := by
      filter_upwards [hpos] with ω hω
      exact (ENNReal.ofReal_inv_of_pos hω).symm
    calc
      _ = ∫⁻ ω, ENNReal.ofReal ((A_N N ω)⁻¹) ∂disorderLaw :=
        lintegral_congr_ae hrecipEq
      _ = ENNReal.ofReal (∫ ω, (A_N N ω)⁻¹ ∂disorderLaw) :=
        (ofReal_integral_eq_lintegral_ofReal hmoment.1 hInvNonneg).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hmoment.2
  have hsourceBound : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun N : ℕ => ∫⁻ ω, (ENNReal.ofReal (A_N N ω))⁻¹ ∂disorderLaw) :=
    Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩
  have htargetCobounded : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun _ : ℕ => ENNReal.ofReal C) := by
    refine ⟨⊤, ?_⟩
    intro a ha
    exact le_top
  have hliminfInv : atTop.liminf
      (fun N : ℕ => ∫⁻ ω, (ENNReal.ofReal (A_N N ω))⁻¹ ∂disorderLaw) ≤ ENNReal.ofReal C := by
    calc
      _ ≤ atTop.liminf (fun _ : ℕ => ENNReal.ofReal C) :=
        Filter.liminf_le_liminf hInvLIntegral hsourceBound htargetCobounded
      _ = ENNReal.ofReal C := by simp
  have hFatou := lintegral_inv_le_liminf_of_tendstoInDistribution hDistA
  have hAInvBound : ∫⁻ ω, (ENNReal.ofReal (A ω))⁻¹ ∂P ≤ ENNReal.ofReal C :=
    hFatou.trans hliminfInv
  have hApos : ∀ᵐ ω ∂P, 0 < A ω :=
    ae_pos_of_finite_lintegral_inverse hAint.aemeasurable
      (lt_of_le_of_lt hAInvBound (by simp))
  let c : ℝ := Real.exp (-‖h₀‖)
  have hlower : ∀ᵐ ω ∂P, c * A ω ≤ Y ω := by
    filter_upwards [hOne.1, hExp.1] with ω hOneInt hExpInt
    have hpoint : ∀ p : Plane × Plane,
        c * (K p.1 * gOne p.2) ≤ K p.1 * gExp p.2 := by
      intro p
      have hkernel : 0 ≤ K p.1 := Critical2DKPZ.heatKernel_nonneg hδ.le _
      have hterminal : c ≤ gExp p.2 := by
        rw [hgExp]
        exact Real.exp_le_exp.mpr (h₀.neg_norm_le_apply p.2)
      simpa [gOne, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hterminal hkernel)
    have hscaled : c * A ω =
        ∫ p, c * (K p.1 * gOne p.2) ∂(Z s t ω) := by
      simp only [A, shfPairing]
      rw [integral_const_mul]
    calc
      c * A ω = ∫ p, c * (K p.1 * gOne p.2) ∂(Z s t ω) := hscaled
      _ ≤ ∫ p, K p.1 * gExp p.2 ∂(Z s t ω) :=
        integral_mono_ae (hOneInt.const_mul c) hExpInt (Filter.Eventually.of_forall hpoint)
      _ = Y ω := by simp only [Y, K, shfPairing]
  have hYpos : ∀ᵐ ω ∂P, 0 < Y ω := by
    filter_upwards [hApos, hlower] with ω hAω hlow
    exact (mul_pos (Real.exp_pos _) hAω).trans_le hlow
  have hYlogMeas : AEMeasurable (fun ω => Real.log (Y ω)) P :=
    Real.measurable_log.comp_aemeasurable hYint.aemeasurable
  have hLogDist := tendstoInDistribution_log_of_ne_zero hDistY
    (hYpos.mono fun _ h => ne_of_gt h)
  have hPolymerEhrhard := isEhrhardType_log_polymer_heat_pairing ϑ hs hst hδ x h₀
  have hEhrhardEventually : ∀ᶠ N : ℕ in atTop,
      IsEhrhardType (disorderLaw.map fun ω => Real.log (Y_N N ω)) := by
    filter_upwards [hPolymerEhrhard] with N hN
    simpa only [Y_N, K] using hN.2
  let νN : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨disorderLaw.map (fun ω => Real.log (Y_N N ω)), inferInstance⟩
  let νLimit : ProbabilityMeasure ℝ := ⟨P.map (fun ω => Real.log (Y ω)), inferInstance⟩
  have hweak : Tendsto νN atTop (𝓝 νLimit) := by
    simpa only [νN, νLimit] using hLogDist.tendsto
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hEhrhardEventually
  let νShift : ℕ → ProbabilityMeasure ℝ := fun k => νN (k + N₀)
  have hweakShift : Tendsto νShift atTop (𝓝 νLimit) := by
    simpa only [νShift, Function.comp_def] using hweak.comp (tendsto_add_atTop_nat N₀)
  have hEhrhardShift (k : ℕ) : IsEhrhardType (νShift k : Measure ℝ) := by
    have h := hN₀ (k + N₀) (Nat.le_add_left N₀ k)
    simpa only [νShift, νN, ProbabilityMeasure.coe_mk] using h
  have hlimit := Provider.ehrhardType_weakClosure νShift νLimit hweakShift hEhrhardShift
  refine ⟨hYpos, hYlogMeas, ?_⟩
  have htargetEq (ω : Ω) : Y ω = shfPairing Z s t
      (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω := by
    simp only [Y, K, shfPairing]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by simp only [hgExp]
  have hmap : P.map (fun ω => Real.log (Y ω)) =
      P.map (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) := by
    apply Measure.map_congr
    filter_upwards [] with ω
    exact congrArg Real.log (htargetEq ω)
  rw [← hmap]
  simpa only [νLimit, ProbabilityMeasure.coe_mk] using hlimit

end Critical2DKPZ.SHF.Positivity

end
