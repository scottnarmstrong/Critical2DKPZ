/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! Even-rounded moving times have the prescribed macroscopic limits. -/

public section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments


/-- The rounded-up clock is even. -/
theorem even_evenCeil (t : ℝ) : Even (evenCeil t) :=
  ⟨⌈t / 2⌉₊, by unfold evenCeil; omega⟩



/-- A fixed real constant divided by the natural-number scale tends to zero. -/
theorem tendsto_const_div_nat (C : ℝ) :
    Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    (tendsto_const_nhds (x := C)).mul
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

/-- The even ceiling has the same macroscopic time, including the initial time zero. -/
theorem tendsto_evenCeil_div (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ => (evenCeil ((N : ℝ) * t) : ℝ) / N) atTop (𝓝 t) := by
  have herr : Tendsto (fun N : ℕ =>
      (evenCeil ((N : ℝ) * t) : ℝ) / N - t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_nat 2)
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hl := Critical2DKPZ.le_evenCeil ((N : ℝ) * t)
    have hu := (Critical2DKPZ.evenCeil_lt_add_two (mul_nonneg hNr.le ht)).le
    have hl' : 0 ≤ (evenCeil ((N : ℝ) * t) : ℝ) / N - t := by
      rw [sub_nonneg, le_div_iff₀ hNr]
      simpa only [mul_comm t] using hl
    rw [Real.norm_eq_abs, abs_of_nonneg hl', sub_le_iff_le_add, div_le_iff₀ hNr]
    calc
      _ ≤ (N : ℝ) * t + 2 := hu
      _ = _ := by field_simp; ring
  have h := herr.add_const t
  simpa only [sub_add_cancel, zero_add] using h

/-- Even-ceiling rounding remains negligible when the target macroscopic time
also varies with the lattice scale. -/
theorem tendsto_evenCeil_moving_div {t : ℝ} (tN : ℕ → ℝ)
    (htN : Tendsto tN atTop (𝓝 t)) (htN0 : ∀ N, 0 ≤ tN N) :
    Tendsto (fun N : ℕ => (evenCeil ((N : ℝ) * tN N) : ℝ) / N)
      atTop (𝓝 t) := by
  have hround : Tendsto (fun N : ℕ =>
      (evenCeil ((N : ℝ) * tN N) : ℝ) / N - tN N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_nat 2)
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hlow := Critical2DKPZ.le_evenCeil ((N : ℝ) * tN N)
    have hupp := (Critical2DKPZ.evenCeil_lt_add_two
      (mul_nonneg (Nat.cast_nonneg N) (htN0 N))).le
    have hlow' : 0 ≤ (evenCeil ((N : ℝ) * tN N) : ℝ) / N - tN N := by
      rw [sub_nonneg, le_div_iff₀ hNr]
      simpa only [mul_comm] using hlow
    have hupp' : (evenCeil ((N : ℝ) * tN N) : ℝ) / N - tN N ≤ 2 / N := by
      rw [sub_le_iff_le_add, div_le_iff₀ hNr]
      have huppR : (evenCeil ((N : ℝ) * tN N) : ℝ) ≤ (N : ℝ) * tN N + 2 := by
        exact_mod_cast hupp
      have hfactor : (2 / (N : ℝ) + tN N) * N =
          2 + (N : ℝ) * tN N := by
        field_simp [hNr.ne']
      rw [hfactor]
      nlinarith [huppR]
    rw [Real.norm_eq_abs, abs_of_nonneg hlow']
    exact hupp'
  have h := hround.add htN
  simpa only [sub_add_cancel, zero_add] using h

/-- The duration between two moving even-ceiling checkpoints converges to the
limiting time gap. -/
theorem tendsto_evenCeil_moving_gap_div {s t : ℝ} (sN tN : ℕ → ℝ)
    (hs : Tendsto sN atTop (𝓝 s)) (ht : Tendsto tN atTop (𝓝 t))
    (hs0 : 0 ≤ s) (hsN0 : ∀ N, 0 ≤ sN N) (hst : s < t) :
    Tendsto (fun N : ℕ =>
      ((evenCeil ((N : ℝ) * tN N) - evenCeil ((N : ℝ) * sN N) : ℕ) : ℝ) / N)
      atTop (𝓝 (t - s)) := by
  have htpos : 0 < t := lt_of_le_of_lt hs0 hst
  have htNpos : ∀ᶠ N : ℕ in atTop, 0 < tN N :=
    ht.eventually (Ioi_mem_nhds htpos)
  let tN' : ℕ → ℝ := fun N => max (tN N) 0
  have ht' : Tendsto tN' atTop (𝓝 t) := by
    have hclipTime : tN' =ᶠ[atTop] tN := by
      filter_upwards [htNpos] with N hN
      simp [tN', max_eq_left hN.le]
    have hraw : tN =ᶠ[atTop] tN' := hclipTime.mono fun _ h => h.symm
    exact ht.congr' hraw
  have hceilT' := tendsto_evenCeil_moving_div tN' ht' (fun N => le_max_right _ _)
  have hclip : (fun N : ℕ =>
      (evenCeil ((N : ℝ) * tN' N) : ℝ) / N) =ᶠ[atTop]
      fun N => (evenCeil ((N : ℝ) * tN N) : ℝ) / N := by
    filter_upwards [htNpos] with N hN
    simp [tN', max_eq_left hN.le]
  have hceilT := hceilT'.congr' hclip
  have hceilS := tendsto_evenCeil_moving_div sN hs hsN0
  have hsNupper : ∀ᶠ N : ℕ in atTop, sN N < (s + t) / 2 :=
    hs.eventually (Iio_mem_nhds (by linarith : s < (s + t) / 2))
  have htNlower : ∀ᶠ N : ℕ in atTop, (s + t) / 2 < tN N :=
    ht.eventually (Ioi_mem_nhds (by linarith : (s + t) / 2 < t))
  have horder : ∀ᶠ N : ℕ in atTop,
      evenCeil ((N : ℝ) * sN N) ≤ evenCeil ((N : ℝ) * tN N) := by
    filter_upwards [hsNupper, htNlower] with N hS hT
    apply Critical2DKPZ.evenCeil_mono
    exact mul_le_mul_of_nonneg_left (lt_trans hS hT).le (Nat.cast_nonneg N)
  have hgapEq : (fun N : ℕ =>
      ((evenCeil ((N : ℝ) * tN N) - evenCeil ((N : ℝ) * sN N) : ℕ) : ℝ) / N) =ᶠ[atTop]
      fun N => (evenCeil ((N : ℝ) * tN N) : ℝ) / N -
        (evenCeil ((N : ℝ) * sN N) : ℝ) / N := by
    filter_upwards [horder] with N hN
    rw [Nat.cast_sub hN, sub_div]
  exact (hceilT.sub hceilS).congr' hgapEq.symm

/-- The even-rounded number of steps converges to the time gap for nonnegative ordered times. -/
theorem tendsto_evenCeil_gap_div {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun N : ℕ =>
      ((evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℕ) : ℝ) / N)
      atTop (𝓝 (t - s)) := by
  have he (N : ℕ) : evenCeil ((N : ℝ) * s) ≤ evenCeil ((N : ℝ) * t) :=
    Critical2DKPZ.evenCeil_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N))
  simp_rw [Nat.cast_sub (he _), sub_div]
  exact (tendsto_evenCeil_div t (hs.trans hst)).sub (tendsto_evenCeil_div s hs)


end Critical2DKPZ.SHF.Moments
