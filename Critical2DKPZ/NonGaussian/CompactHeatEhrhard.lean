/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.CompactHeatMeanPositive
public import Critical2DKPZ.NonGaussian.HeatStartLp
public import Critical2DKPZ.NonGaussian.PositiveEhrhardLimit
public import Critical2DKPZ.NonGaussian.PositiveTerminalApproximation
public import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Mathlib.Tactic

/-! # Positivity and Ehrhard type for compact-terminal heat starts -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Positivity
open scoped CompactlySupported BoundedContinuousFunction Topology

namespace Critical2DKPZ.NonGaussian

/-- The heat-start pairing against a nonzero nonnegative compactly supported continuous terminal
is almost surely positive and its logarithm has an Ehrhard-type law. -/
theorem heatStart_cc_pairing_pos_isEhrhardType (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) (φ₀ : C_c(Plane, ℝ))
    (hφ₀ : ∀ y, 0 ≤ φ₀ y) (hφ₀' : φ₀ ≠ 0) :
    (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x)) φ₀ ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x)) φ₀ ω)) P ∧
      IsEhrhardType (P.map fun ω => Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x)) φ₀ ω))  := by
  let g : Plane →ᵇ ℝ := φ₀.toBoundedContinuousFunction
  have hg (y : Plane) : 0 ≤ g y := hφ₀ y
  let Y : Ω → ℝ := shfPairing Z s t (fun y => heatKernel δ (y - x)) φ₀
  let A : Ω → ℝ := shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let X : ℕ → Ω → ℝ := fun n ω => Y ω + ε n * A ω
  have hYmem : MemLp Y 2 P := memLp_heatStart_bounded ϑ P Z hZ hs hst hδ x g
  have hAmem : MemLp A 2 P := memLp_heatStart_flat ϑ P Z hZ hs hst hδ x
  have hXmem (n : ℕ) : MemLp (X n) 2 P := hYmem.add (hAmem.const_mul (ε n))
  have hPairY := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hPairA := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x (1 : Plane →ᵇ ℝ)
  have hAdd (n : ℕ) : (fun ω => shfPairing Z s t (fun y => heatKernel δ (y - x))
      (fun y => Real.exp (logPositiveTerminal g hg (ε n) (hε n) y)) ω) =ᵐ[P] X n := by
    filter_upwards [hPairY.1, hPairA.1] with ω hYω hAω
    have hAInt : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (Z s t ω) := by
      simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply, mul_one] using hAω
    change (∫ p, heatKernel δ (p.1 - x) *
      Real.exp (logPositiveTerminal g hg (ε n) (hε n) p.2) ∂Z s t ω) = X n ω
    simp_rw [exp_logPositiveTerminal]
    calc
      _ = ∫ p, (heatKernel δ (p.1 - x) * g p.2 + ε n * heatKernel δ (p.1 - x)) ∂Z s t ω := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => by ring
      _ = _ := by
        rw [integral_add hYω (hAInt.const_mul (ε n)), integral_const_mul]
        simp only [X, Y, A, shfPairing, g, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply, mul_one]
  have hPackage (n : ℕ) := isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x
    (logPositiveTerminal g hg (ε n) (hε n)) hs hst hδ
  have hXpos (n : ℕ) : ∀ᵐ ω ∂P, 0 < X n ω := by
    filter_upwards [(hPackage n).1, hAdd n] with ω hω heq
    exact heq ▸ hω
  have hXE (n : ℕ) : IsEhrhardType (P.map fun ω => Real.log (X n ω)) := by
    rw [← Measure.map_congr ((hAdd n).mono fun _ h => congrArg Real.log h)]
    exact (hPackage n).2.2
  have hY0 (ω : Ω) : 0 ≤ Y ω :=
    integral_nonneg fun p => mul_nonneg (heatKernel_nonneg hδ.le _) (hφ₀ _)
  have hA0 (ω : Ω) : 0 ≤ A ω :=
    integral_nonneg fun p => mul_nonneg (heatKernel_nonneg hδ.le _) zero_le_one
  have hMeanPos : 0 < ∫ ω, Y ω ∂P :=
    (integrable_and_integral_heatStart_cc_pos ϑ P Z hZ hs hst hδ x φ₀ hφ₀ hφ₀').2
  have hMean (n : ℕ) : (∫ ω, Y ω ∂P) ≤ ∫ ω, X n ω ∂P := by
    change (∫ ω, Y ω ∂P) ≤ ∫ ω, Y ω + ε n * A ω ∂P
    rw [integral_add (hYmem.integrable (by norm_num))
      ((hAmem.integrable (by norm_num)).const_mul (ε n)), integral_const_mul]
    exact le_add_of_nonneg_right (mul_nonneg (hε n).le (integral_nonneg hA0))
  have hSecond (n : ℕ) : (∫ ω, X n ω ^ 2 ∂P) ≤
      2 * ((∫ ω, Y ω ^ 2 ∂P) + ∫ ω, A ω ^ 2 ∂P) := by
    have hPoint (ω : Ω) : X n ω ^ 2 ≤ 2 * (Y ω ^ 2 + A ω ^ 2) := by
      have hX0 : 0 ≤ X n ω := add_nonneg (hY0 ω) (mul_nonneg (hε n).le (hA0 ω))
      have hXA : X n ω ≤ Y ω + A ω := by
        exact add_le_add le_rfl (mul_le_of_le_one_left (hA0 ω) (hεle n))
      exact ((sq_le_sq₀ hX0 (add_nonneg (hY0 ω) (hA0 ω))).mpr hXA).trans add_sq_le
    calc
      _ ≤ ∫ ω, 2 * (Y ω ^ 2 + A ω ^ 2) ∂P :=
        integral_mono (hXmem n).integrable_sq ((hYmem.integrable_sq.add hAmem.integrable_sq).const_mul 2) hPoint
      _ = _ := by rw [integral_const_mul, integral_add hYmem.integrable_sq hAmem.integrable_sq]
  have hConv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [X, zero_mul, add_zero] using tendsto_const_nhds.add (hεlim.mul_const (A ω))
  exact positive_isEhrhardType_of_ae_tendsto P hXmem hXpos hXE hYmem.aemeasurable hConv hMeanPos hMean hSecond

end Critical2DKPZ.NonGaussian

end
