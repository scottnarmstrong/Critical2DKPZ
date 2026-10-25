/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceMoving
import Mathlib.Tactic

/-! # Collision entrances tested against uniformly convergent functions -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter
open scoped Topology

/-- On bounded positive-time clock windows the collision entrance is uniformly
continuous in its test in the supremum norm, including moving starting sites. -/
theorem tendsto_collisionEntrance_difference_of_uniform
    {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (lo hi : ℕ → ℕ) (a b : ℕ → Site)
    (htime : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Finset.Icc (lo N) (hi N), δ * (N : ℝ) ≤ r)
    (hcard : ∀ᶠ N : ℕ in atTop, ((Finset.Icc (lo N) (hi N)).card : ℝ) / N ≤ A)
    (FN : ℕ → ℝ × Plane → ℝ) (F : ℝ × Plane → ℝ)
    (hF : TendstoUniformly FN F atTop) :
    Tendsto (fun N => collisionEntrance N (lo N) (hi N) (a N) (b N) (FN N) -
      collisionEntrance N (lo N) (hi N) (a N) (b N) F) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := collisionEntrance_abs_le_positiveTime_card hδ
  let B : ℝ := C / δ * A
  have hB : 0 ≤ B := mul_nonneg (div_nonneg hC.le hδ.le) hA
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η : ℝ := ε / (B + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hu := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_univ.mpr hF) η hη
  filter_upwards [hu, htime, hcard, eventually_gt_atTop 0] with N huN htN hcN hN
  have hd (p : ℝ × Plane) : |FN N p - F p| ≤ η := by
    have h := huN p (Set.mem_univ p)
    simpa only [Real.dist_eq, abs_sub_comm] using h.le
  have hb := hbound N (lo N) (hi N) (a N) (b N)
    (fun p => FN N p - F p) η hN hη.le hd htN
  have hlinear := collisionEntrance_sub_test N (lo N) (hi N) (a N) (b N) (FN N) F
  rw [Real.dist_eq, sub_zero, ← hlinear]
  calc
    |collisionEntrance N (lo N) (hi N) (a N) (b N) (fun p => FN N p - F p)| ≤
        (η * C / δ) * ((Finset.Icc (lo N) (hi N)).card / (N : ℝ)) := hb
    _ ≤ (η * C / δ) * A :=
      mul_le_mul_of_nonneg_left hcN (div_nonneg (mul_nonneg hη.le hC.le) hδ.le)
    _ = η * B := by dsimp [B]; ring
    _ < ε := by
      dsimp [η]
      have hden : 0 < B + 1 := by positivity
      have he : ε / (B + 1) * B < ε / (B + 1) * (B + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one B) hη
      simpa only [div_mul_cancel₀ ε hden.ne'] using he

/-- Collision-entrance limits on positive-time windows are stable under uniformly converging tests. -/
theorem tendsto_collisionEntrance_spatial_test_away_zero_moving_window_of_uniform
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (M₀ M₁ : ℕ → ℕ)
    (hM₀ : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s))
    (hM₁ : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t))
    (aSite bSite : ℕ → Site)
    (haSite : ∀ N, aSite N ∈ evenLattice) (hbSite : ∀ N, bSite N ∈ evenLattice)
    (a b : Plane)
    (ha : Tendsto (fun N => latticeRepresentative N (aSite N)) atTop (𝓝 a))
    (hb : Tendsto (fun N => latticeRepresentative N (bSite N)) atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R B : ℝ) (hB : 0 ≤ B)
    (hFcont : Continuous F) (hFbound : ∀ u x, |F (u, x)| ≤ B)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (FN : ℕ → ℝ × Plane → ℝ) (hFN : TendstoUniformly FN F atTop) :
    Tendsto (fun N : ℕ => collisionEntrance N (M₀ N + 1) (M₁ N)
      (aSite N) (bSite N) (FN N)) atTop
      (𝓝 ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F))) := by
  have hfixed := tendsto_collisionEntrance_spatial_test_away_zero_moving_window
    hs hst M₀ M₁ hM₀ hM₁ aSite bSite haSite hbSite a b ha hb F R B hB
    hFcont hFbound hFsupport
  have hlo := hM₀.eventually (Ioi_mem_nhds (half_lt_self hs))
  have hhi := hM₁.eventually (Iio_mem_nhds (lt_add_one t))
  have htime : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
      (s / 2) * (N : ℝ) ≤ r := by
    filter_upwards [hlo, eventually_gt_atTop 0] with N hN hpos r hr
    have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
    have hstart := ((lt_div_iff₀ hNr).mp hN).le
    exact hstart.trans (by exact_mod_cast (show M₀ N ≤ r from
      (Nat.le_succ _).trans (Finset.mem_Icc.mp hr).1))
  have hcard : ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc (M₀ N + 1) (M₁ N)).card : ℝ) / N ≤ t + 2 := by
    filter_upwards [hhi, eventually_gt_atTop 0] with N hN hpos
    have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hpos
    have hc : ((Finset.Icc (M₀ N + 1) (M₁ N)).card : ℝ) ≤ (M₁ N : ℝ) + 1 := by
      exact_mod_cast (show (Finset.Icc (M₀ N + 1) (M₁ N)).card ≤ M₁ N + 1 from
        (Finset.card_le_card (Finset.Icc_subset_Icc_left (Nat.zero_le _))).trans_eq
          (by simp))
    apply (div_le_iff₀ hNr).mpr
    have hupper := (div_lt_iff₀ hNr).mp hN
    linarith only [hc, hupper, hNr1]
  have hd := tendsto_collisionEntrance_difference_of_uniform (half_pos hs)
    (show 0 ≤ t + 2 by linarith only [hs, hst])
    (fun N => M₀ N + 1) M₁ aSite bSite htime hcard FN F hFN
  apply hfixed.congr_dist
  simpa only [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm, norm_zero] using hd.norm

end Critical2DKPZ.SHF.Moments
