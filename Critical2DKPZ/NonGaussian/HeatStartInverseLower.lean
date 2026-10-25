/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
public import Critical2DKPZ.NonGaussian.LatticeInverseLower
public import Critical2DKPZ.NonGaussian.HeatStartInverseConvergence
public import Critical2DKPZ.NonGaussian.LogInverseMean
import Critical2DKPZ.SmallScales.HeatStartMoments
import Mathlib.Tactic

/-! # The SHF inverse-moment logarithmic lower bound -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- The inverse flat-terminal heat-start mass is integrable and its expectation is at least
`c log (1/r)` for small `r`, uniformly over centers and durations in a fixed compact subset of `(0,∞)`. -/
theorem heatStart_inv_integral_ge_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) :
    ∃ c r₀ : ℝ, 0 < c ∧ 0 < r₀ ∧ ∀ s T r : ℝ, 0 ≤ s → τ₀ ≤ T - s → T - s ≤ τ₁ → 0 < r → r < r₀ →
      ∀ x : Plane,
        Integrable (fun ω => (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω)⁻¹) P ∧
        c * Real.log r⁻¹ ≤
          ∫ ω, (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω)⁻¹ ∂P  := by
  let Tlo : ℝ := τ₀ / 2
  let Thi : ℝ := max τ₁ τ₀ + 2
  have hTlo : 0 < Tlo := by dsimp [Tlo]; positivity
  have hThi : Tlo < Thi := by
    have h := le_max_right τ₁ τ₀
    dsimp [Tlo, Thi]
    linarith only [h, hτ₀]
  obtain ⟨q, c₀, hq, _hqT, hc₀, hLattice⟩ :=
    exists_lattice_inverse_log_lower_bound_of hVD |ϑ| Tlo Thi hTlo hThi
  let r₀ : ℝ := min q (min 1 (Real.exp (-2 * |Real.log τ₀|)))
  have hr₀ : 0 < r₀ := lt_min hq (lt_min zero_lt_one (Real.exp_pos _))
  refine ⟨c₀ / 2, r₀, by positivity, hr₀, ?_⟩
  intro s T r hs hτlo hτhi hr hrr₀ x
  have hrq : r < q := hrr₀.trans_le (min_le_left _ _)
  have hr1 : r < 1 := hrr₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrExp : r < Real.exp (-2 * |Real.log τ₀|) :=
    hrr₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsT : s < T := by linarith only [hτlo, hτ₀]
  let H : ℝ := r + (T - s)
  have hH : 0 < H := add_pos hr (sub_pos.mpr hsT)
  have hHlo : Tlo < H := by dsimp [Tlo, H]; linarith only [hτlo, hτ₀, hr]
  have hHhi : H < Thi := by
    have h := le_max_left τ₁ τ₀
    dsimp [H, Thi]
    linarith only [hτhi, hr1, h]
  let m : ℕ → ℕ := fun N => evenCeil (N * r)
  let n : ℕ → ℕ := fun N => m N + (evenCeil (N * T) - evenCeil (N * s))
  have hNum : Tendsto (fun N => (n N : ℝ) / N) atTop (𝓝 H) :=
    tendsto_heatStartWalkHorizon_div hs hsT.le hr.le
  have hRatio : Tendsto (fun N => (n N : ℝ) / (max (m N) 1 : ℕ)) atTop (𝓝 (H / r)) :=
    tendsto_heatStartWalkHorizon_ratio hs hsT.le hr
  have hLogRatio : Tendsto (fun N => c₀ * (1 + Real.log ((n N : ℝ) / (max (m N) 1 : ℕ))))
      atTop (𝓝 (c₀ * (1 + Real.log (H / r)))) :=
    (tendsto_const_nhds.add (hRatio.log (div_pos hH hr).ne')).const_mul c₀
  obtain ⟨_hInverseInt, hInverseConv⟩ := heatStart_inv_integral_tendsto_of ϑ P Z hHeatStartLogInput hs hsT hr x
  have hEventually : ∀ᶠ N : ℕ in atTop,
      c₀ * (1 + Real.log ((n N : ℝ) / (max (m N) 1 : ℕ))) ≤
        ∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * r)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)⁻¹ ∂disorderLaw := by
    filter_upwards [hLattice, hNum.eventually (Ioi_mem_nhds hHlo),
      hNum.eventually (Iio_mem_nhds hHhi), eventually_ge_atTop 1] with N hLN hLo hHi hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
    have hmCut : m N ≤ evenCeil (q * N) := by
      apply evenCeil_mono
      calc
        (N : ℝ) * r ≤ N * q := mul_le_mul_of_nonneg_left hrq.le hNpos.le
        _ = _ := mul_comm _ _
    have hLow := hLN ϑ ⟨neg_abs_le _, le_abs_self _⟩ (m N) (n N)
      (evenCeil_even _) hmCut ((le_div_iff₀ hNpos).mp hLo.le) ((div_le_iff₀ hNpos).mp hHi.le)
    have hab : evenCeil (N * s) ≤ evenCeil (N * T) :=
      evenCeil_mono (mul_le_mul_of_nonneg_left hsT.le hNpos.le)
    have hd : Even (evenCeil (N * T) - evenCeil (N * s)) := by
      exact_mod_cast ((show Even ((evenCeil (N * T) : ℤ)) from by exact_mod_cast evenCeil_even (N * T)).sub
        (show Even ((evenCeil (N * s) : ℤ)) from by exact_mod_cast evenCeil_even (N * s)))
    have hCell (ω : Disorder) :
        profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * r)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω =
        profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * r)) (w - latticePoint N x)) (fun _ => 1) ω := by
      simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero]
      exact heatStartWalkProfile_cellAverage_one_eq _ (by omega) hab (evenCeil_even _) hd x ω
    rw [show (∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * r)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)⁻¹ ∂disorderLaw) =
        ∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * r)) (w - latticePoint N x)) (fun _ => 1) ω)⁻¹ ∂disorderLaw from
      integral_congr_ae (Filter.Eventually.of_forall fun ω => congrArg Inv.inv (hCell ω))]
    have hLaw := identDistrib_heatStartWalkProfile_smoothed (criticalBeta ϑ N) hab (m N) (latticePoint N x)
    exact hLow.trans_eq hLaw.inv.integral_eq.symm
  have hLimitLower := le_of_tendsto_of_tendsto hLogRatio hInverseConv hEventually
  have hLogr : 2 * |Real.log τ₀| ≤ Real.log r⁻¹ := by
    have h := (Real.log_lt_iff_lt_exp hr).mpr hrExp
    rw [Real.log_inv]
    linarith only [h]
  have hHτ : τ₀ ≤ H := by dsimp [H]; linarith only [hτlo, hr]
  have hLogH : -|Real.log τ₀| ≤ Real.log H :=
    (neg_abs_le _).trans (Real.log_le_log hτ₀ hHτ)
  have hScalar : (1 / 2 : ℝ) * Real.log r⁻¹ ≤ 1 + Real.log (H / r) := by
    rw [Real.log_inv] at hLogr
    rw [Real.log_inv, Real.log_div hH.ne' hr.ne']
    linarith only [hLogr, hLogH]
  have hMean := heatStart_integral_eq_one ϑ P Z hZ hs hsT hr x
  have hPackage := hsym.2.2.2.2.2.2 s T r x (0 : Plane →ᵇ ℝ) hs hsT hr
  have hPos : ∀ᵐ ω ∂P, 0 < shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω := by
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hPackage.1
  have hE : IsEhrhardType (P.map fun ω => Real.log
      (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω)) := by
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hPackage.2.2
  have hInv := integrable_inv_and_log_integral_inv_le P hMean.1 hPos hMean.2 hE
  refine ⟨hInv.1, ?_⟩
  calc
    c₀ / 2 * Real.log r⁻¹ = c₀ * ((1 / 2 : ℝ) * Real.log r⁻¹) := by ring
    _ ≤ c₀ * (1 + Real.log (H / r)) := mul_le_mul_of_nonneg_left hScalar hc₀.le
    _ ≤ _ := hLimitLower

end Critical2DKPZ.NonGaussian

end
