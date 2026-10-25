/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.HeatStartWalkLaw
public import Critical2DKPZ.NonGaussian.HeatStartClocks
public import Critical2DKPZ.NonGaussian.InverseSquare
public import Critical2DKPZ.OnePoint.OnePointInverseMomentComparison
import Mathlib.Tactic

/-! # Uniform inverse-square moments at fixed heat-start width -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.NonGaussian

/-- At fixed positive heat width, the inverse squares of the flat polymer masses
are integrable and have uniformly bounded expectations over sufficiently large lattice scales
and all spatial starting points. -/
theorem exists_heatStartWalkProfile_inv_sq_bound (ϑ : ℝ) {s T δ : ℝ}
    (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
      Integrable (fun ω => (profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x)) (fun _ => 1) ω)⁻¹ ^ 2)
        disorderLaw ∧
      ∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x)) (fun _ => 1) ω)⁻¹ ^ 2
          ∂disorderLaw ≤ B := by
  let H : ℝ := δ + (T - s)
  have hH : 0 < H := add_pos hδ (sub_pos.mpr hsT)
  obtain ⟨C, hC⟩ := OnePoint.smoothedP2Plane_secondMoment_le_log |ϑ| (H / 2) (H + 1) (by positivity)
  let Q : ℝ := max C 0 * (1 + Real.log (H / δ + 1))
  have hR : 0 < H / δ := div_pos hH hδ
  have hLog : 0 ≤ Real.log (H / δ + 1) := Real.log_nonneg (by linarith only [hR])
  have hQ : 0 ≤ Q := mul_nonneg (le_max_right _ _) (by linarith only [hLog])
  let m : ℕ → ℕ := fun N => evenCeil (N * δ)
  let n : ℕ → ℕ := fun N => m N + (evenCeil (N * T) - evenCeil (N * s))
  have hNum : Tendsto (fun N => (n N : ℝ) / N) atTop (𝓝 H) :=
    tendsto_heatStartWalkHorizon_div hs hsT.le hδ.le
  have hRatio : Tendsto (fun N => (n N : ℝ) / (max (m N) 1 : ℕ)) atTop (𝓝 (H / δ)) :=
    tendsto_heatStartWalkHorizon_ratio hs hsT.le hδ
  refine ⟨Q ^ 3, pow_nonneg hQ _, ?_⟩
  filter_upwards [hC, hNum.eventually (Ioi_mem_nhds (by dsimp [H]; linarith only [hH] : H / 2 < H)),
    hNum.eventually (Iio_mem_nhds (by linarith : H < H + 1)),
    hRatio.eventually (Iio_mem_nhds (by linarith : H / δ < H / δ + 1)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1 / δ),
    eventually_ge_atTop 1] with N hCN hLo hHi hRN hNδ hN1
  intro x
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hm : 1 ≤ m N := by
    have hceil := le_evenCeil (N * δ)
    have hprod := (div_le_iff₀ hδ).mp hNδ
    have hr : (1 : ℝ) ≤ (m N : ℝ) := by dsimp [m]; linarith only [hceil, hprod]
    exact_mod_cast hr
  have hmn : m N ≤ n N := Nat.le_add_right _ _
  have hnLo : H / 2 * N ≤ (n N : ℝ) := ((le_div_iff₀ hNpos).mp hLo.le)
  have hnHi : (n N : ℝ) ≤ (H + 1) * N := ((div_le_iff₀ hNpos).mp hHi.le)
  have hRatioOne : (1 : ℝ) ≤ (n N : ℝ) / (max (m N) 1 : ℕ) := by
    rw [max_eq_left hm]
    apply (one_le_div (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm))).mpr
    exact_mod_cast hmn
  have hFactor : 0 ≤ 1 + Real.log ((n N : ℝ) / (max (m N) 1 : ℕ)) :=
    add_nonneg zero_le_one (Real.log_nonneg hRatioOne)
  have hLogR : Real.log ((n N : ℝ) / (max (m N) 1 : ℕ)) ≤ Real.log (H / δ + 1) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hRatioOne) hRN.le
  have hSecond := hCN ϑ ⟨neg_abs_le _, le_abs_self _⟩ (m N) (n N) hmn hnLo hnHi
  have hSecondBound : (∫ ω, smoothedP2Plane (criticalBeta ϑ N) (m N) (n N) 0 ω ^ 2 ∂disorderLaw) ≤ Q := by
    calc
      _ ≤ C * (1 + Real.log ((n N : ℝ) / (max (m N) 1 : ℕ))) := hSecond
      _ ≤ max C 0 * (1 + Real.log ((n N : ℝ) / (max (m N) 1 : ℕ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hFactor
      _ ≤ Q := mul_le_mul_of_nonneg_left (add_le_add le_rfl hLogR) (le_max_right _ _)
  have hInv := integral_inv_sq_smoothedP2Plane_le (β := criticalBeta ϑ N) (Real.sqrt_nonneg _) (m N) (n N) 0
  have hInvBound : (∫ ω, (smoothedP2Plane (criticalBeta ϑ N) (m N) (n N) 0 ω)⁻¹ ^ 2 ∂disorderLaw) ≤ Q ^ 3 :=
    hInv.2.trans (pow_le_pow_left₀ (integral_nonneg fun _ => sq_nonneg _) hSecondBound 3)
  have hab : evenCeil (N * s) ≤ evenCeil (N * T) :=
    evenCeil_mono (mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg _))
  have hLaw := identDistrib_heatStartWalkProfile_smoothed (criticalBeta ϑ N) hab (m N) (latticePoint N x)
  exact ⟨(hLaw.inv.pow.integrable_iff).mpr hInv.1,
    (hLaw.inv.pow.integral_eq).trans_le hInvBound⟩

end Critical2DKPZ.NonGaussian

end
