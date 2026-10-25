/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairingFubini
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
import Critical2DKPZ.SHF.Moments.WalkScaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The first pairing moment with moving time endpoints -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Moments

private theorem tendsto_evenCeil_div_moving {vN : ℕ → ℝ} {v : ℝ}
    (hv : Tendsto vN atTop (𝓝 v)) (hvN : ∀ᶠ N : ℕ in atTop, 0 ≤ vN N) :
    Tendsto (fun N : ℕ => (evenCeil ((N : ℝ) * vN N) : ℝ) / N) atTop (𝓝 v) := by
  have herr : Tendsto (fun N : ℕ =>
      (evenCeil ((N : ℝ) * vN N) : ℝ) / N - vN N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_nat 2)
    filter_upwards [eventually_gt_atTop 0, hvN] with N hN hvN'
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hx : 0 ≤ (N : ℝ) * vN N := mul_nonneg hNr.le hvN'
    have hlo := Critical2DKPZ.le_evenCeil ((N : ℝ) * vN N)
    have hhi := (Critical2DKPZ.evenCeil_lt_add_two hx).le
    have hlo' : 0 ≤
        (evenCeil ((N : ℝ) * vN N) : ℝ) / N - vN N := by
      rw [sub_nonneg, le_div_iff₀ hNr]
      simpa only [mul_comm] using hlo
    have hhi' :
        (evenCeil ((N : ℝ) * vN N) : ℝ) / N - vN N ≤ 2 / N := by
      rw [sub_le_iff_le_add, div_le_iff₀ hNr]
      have hmul : (2 / N + vN N) * N = 2 + vN N * N := by
        field_simp [hNr.ne']
      nlinarith [hhi, hmul]
    rw [Real.norm_eq_abs, abs_of_nonneg hlo']
    exact hhi'
  have h := herr.add hv
  simpa only [sub_add_cancel, zero_add] using h

private theorem tendsto_evenCeil_gap_div_moving
    {s t : ℝ} {sN tN : ℕ → ℝ}
    (hsN : Tendsto sN atTop (𝓝 s)) (htN : Tendsto tN atTop (𝓝 t))
    (hsN0 : ∀ N, 0 ≤ sN N) (hs : 0 ≤ s) (hst : s < t) :
    Tendsto (fun N : ℕ =>
      ((evenCeil ((N : ℝ) * tN N) - evenCeil ((N : ℝ) * sN N) : ℕ) : ℝ) / N)
      atTop (𝓝 (t - s)) := by
  have htpos : 0 < t := lt_of_le_of_lt hs hst
  have htNpos : ∀ᶠ N : ℕ in atTop, 0 < tN N :=
    htN.eventually (Ioi_mem_nhds htpos)
  have htN0 : ∀ᶠ N : ℕ in atTop, 0 ≤ tN N := htNpos.mono fun N hN => hN.le
  have hsRatio := tendsto_evenCeil_div_moving hsN (Filter.Eventually.of_forall hsN0)
  have htRatio := tendsto_evenCeil_div_moving htN htN0
  have htimeGap : Tendsto (fun N : ℕ => tN N - sN N) atTop (𝓝 (t - s)) := htN.sub hsN
  have htimeGapPos : ∀ᶠ N : ℕ in atTop, 0 < tN N - sN N :=
    htimeGap.eventually (Ioi_mem_nhds (sub_pos.mpr hst))
  have htimeOrder : ∀ᶠ N : ℕ in atTop, sN N < tN N :=
    htimeGapPos.mono fun N hN => by linarith
  have hclockOrder : ∀ᶠ N : ℕ in atTop,
      evenCeil ((N : ℝ) * sN N) ≤ evenCeil ((N : ℝ) * tN N) := by
    filter_upwards [htimeOrder] with N htime
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left htime.le (Nat.cast_nonneg N))
  have hsub : ∀ᶠ N : ℕ in atTop,
      ((evenCeil ((N : ℝ) * tN N) - evenCeil ((N : ℝ) * sN N) : ℕ) : ℝ) / N =
        (evenCeil ((N : ℝ) * tN N) : ℝ) / N -
          (evenCeil ((N : ℝ) * sN N) : ℝ) / N := by
    filter_upwards [hclockOrder] with N hN
    rw [Nat.cast_sub hN, sub_div]
  apply (htRatio.sub hsRatio).congr'
  exact hsub.mono fun N hN => hN.symm

/-- The annealed density converges pointwise with moving even-ceiling time endpoints. -/
theorem tendsto_integral_rescaledP2P_moving (ϑ : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (sN tN : ℕ → ℝ)
    (hsN : Tendsto sN atTop (𝓝 s)) (htN : Tendsto tN atTop (𝓝 t))
    (hsN0 : ∀ N, 0 ≤ sN N) (p : Plane × Plane) :
    Tendsto (fun N : ℕ =>
      ∫ ω, rescaledP2P ϑ N (sN N) (tN N) p ω ∂disorderLaw) atTop
      (𝓝 (heatKernel (t - s) (p.2 - p.1))) := by
  let m₀ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * sN N)
  let m₁ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * tN N)
  let n : ℕ → ℕ := fun N => m₁ N - m₀ N
  let z : ℕ → Site := fun N => latticePoint N p.2 - latticePoint N p.1
  have hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 (t - s)) := by
    simpa [n, m₀, m₁] using tendsto_evenCeil_gap_div_moving hsN htN hsN0 hs hst
  have hz : Tendsto (fun N : ℕ => latticeRepresentative N (z N)) atTop
      (𝓝 (p.2 - p.1)) := by
    simp only [z, latticeRepresentative_sub]
    exact (tendsto_cellSample p.2).sub (tendsto_cellSample p.1)
  have hphase : ∀ᶠ N : ℕ in atTop, Even (z N 0 + z N 1 + n N) := by
    filter_upwards with N
    have hnEven : Even (n N) := by
      dsimp [n, m₀, m₁]
      exact even_evenCeil_sub ((N : ℝ) * sN N) ((N : ℝ) * tN N)
    exact latticePoint_gap_phase N (n N) hnEven p.1 p.2
  have hkernel := tendsto_scaled_srwKernel (sub_pos.mpr hst) hn hz hphase
  simpa [integral_rescaledP2P, n, m₀, m₁, z] using hkernel

/-- A compact signed test paired against the annealed density converges when both
time endpoints move with `N` toward a strictly ordered limiting pair. -/
theorem tendsto_pairing_annealed_rescaledP2P_moving (ϑ : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (sN tN : ℕ → ℝ)
    (hsN : Tendsto sN atTop (𝓝 s)) (htN : Tendsto tN atTop (𝓝 t))
    (hsN0 : ∀ N, 0 ≤ sN N)
    {φ : Plane × Plane → ℝ} (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    Tendsto (fun N : ℕ => ∫ p : Plane × Plane,
      φ p * (∫ ω, rescaledP2P ϑ N (sN N) (tN N) p ω ∂disorderLaw)) atTop
      (𝓝 (∫ p : Plane × Plane, φ p * heatKernel (t - s) (p.2 - p.1))) := by
  obtain ⟨C, hC, hkernelBound⟩ := scaled_srwKernel_bound (half_pos (sub_pos.mpr hst))
  have hgap := tendsto_evenCeil_gap_div_moving hsN htN hsN0 hs hst
  have hgapEvent : ∀ᶠ N : ℕ in atTop,
      (t - s) / 2 <
        ((evenCeil ((N : ℝ) * tN N) - evenCeil ((N : ℝ) * sN N) : ℕ) : ℝ) / N :=
    hgap.eventually (Ioi_mem_nhds
      (half_lt_self (sub_pos.mpr hst)))
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ p : Plane × Plane,
      |∫ ω, rescaledP2P ϑ N (sN N) (tN N) p ω ∂disorderLaw| ≤ C := by
    filter_upwards [eventually_gt_atTop 0, hgapEvent] with N hN hgapN
    intro p
    rw [integral_rescaledP2P, abs_of_nonneg (mul_nonneg (by positivity)
      (Critical2DKPZ.srwKernel_nonneg _ _))]
    apply hkernelBound
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hscaled : ((t - s) / 2) * N <
        (evenCeil ((N : ℝ) * tN N) - evenCeil ((N : ℝ) * sN N) : ℕ) :=
      (lt_div_iff₀ hNr).mp hgapN
    exact hscaled.le
  apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |φ p|)
  · exact Filter.Eventually.of_forall fun N =>
      (hφ.measurable.mul (measurable_integral_rescaledP2P ϑ N (sN N) (tN N))).aestronglyMeasurable
  · filter_upwards [hbound] with N hN
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hN p) (abs_nonneg _)
  · exact ((hφ.integrable_of_hasCompactSupport hφs).norm.const_mul C)
  · exact Filter.Eventually.of_forall fun p =>
      (tendsto_const_nhds (x := φ p)).mul
        (tendsto_integral_rescaledP2P_moving ϑ hs hst sN tN hsN htN hsN0 p)




end Critical2DKPZ.SHF.Moments

end
