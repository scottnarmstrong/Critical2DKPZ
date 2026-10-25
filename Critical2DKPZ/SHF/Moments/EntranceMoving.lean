/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceGeneral
import Mathlib.Tactic

/-! # Moving-window bounds for collision entrance -/

@[expose] public section

noncomputable section

open scoped BigOperators
open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- On a positive-time window, a bounded test has entrance mass bounded by its
number of time slices divided by the diffusive scale. -/
theorem collisionEntrance_abs_le_positiveTime_card {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N lo hi : ℕ, ∀ a b : Site,
      ∀ F : ℝ × Plane → ℝ, ∀ M : ℝ,
      0 < N → 0 ≤ M → (∀ p, |F p| ≤ M) →
      (∀ r ∈ Finset.Icc lo hi, δ * (N : ℝ) ≤ r) →
      |collisionEntrance N lo hi a b F| ≤
        (M * C / δ) * ((Finset.Icc lo hi).card / (N : ℝ)) := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := srwKernel_gaussianBound_all_times
  refine ⟨C, hC, fun N lo hi a b F M hN hM hF htime => ?_⟩
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hkernel : ∀ r ∈ Finset.Icc lo hi,
      srwKernel (2 * r) (b - a) ≤ C / (δ * N) := by
    intro r hr
    have hrtime : δ * (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast htime r hr
    have hden : δ * (N : ℝ) ≤ (2 * (r : ℝ) + 1) := by nlinarith
    have hdenpos : 0 < δ * (N : ℝ) := mul_pos hδ hNreal
    have hexp : Real.exp
        (-c * ‖siteToPlane (b - a)‖ ^ 2 / (2 * (r : ℝ) + 1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith [sq_nonneg ‖siteToPlane (b - a)‖]
      · positivity
    have hbound := hgauss (2 * r) (b - a)
    have hdenCast : (((2 * r : ℕ) : ℝ) + 1) = 2 * (r : ℝ) + 1 := by norm_num
    rw [hdenCast] at hbound
    calc
      srwKernel (2 * r) (b - a) ≤
          C / (2 * (r : ℝ) + 1) *
            Real.exp (-c * ‖siteToPlane (b - a)‖ ^ 2 / (2 * (r : ℝ) + 1)) := hbound
      _ ≤ C / (2 * (r : ℝ) + 1) := by
        exact mul_le_of_le_one_right (by positivity) hexp
      _ ≤ C / (δ * (N : ℝ)) := by
        exact div_le_div_of_nonneg_left hC.le hdenpos hden
  have hsum : ∑ r ∈ Finset.Icc lo hi, srwKernel (2 * r) (b - a) ≤
      ((Finset.Icc lo hi).card : ℝ) * (C / (δ * (N : ℝ))) := by
    calc
      _ ≤ ∑ _r ∈ Finset.Icc lo hi, C / (δ * (N : ℝ)) :=
        Finset.sum_le_sum fun r hr => hkernel r hr
      _ = _ := by simp
  have hmass : M * ∑ r ∈ Finset.Icc lo hi, srwKernel (2 * r) (b - a) ≤
      M * (((Finset.Icc lo hi).card : ℝ) * (C / (δ * (N : ℝ)))) :=
    mul_le_mul_of_nonneg_left hsum hM
  calc
    |collisionEntrance N lo hi a b F| ≤
        M * ∑ r ∈ Finset.Icc lo hi, srwKernel (2 * r) (b - a) :=
      collisionEntrance_abs_le N lo hi a b hF
    _ ≤ M * (((Finset.Icc lo hi).card : ℝ) * (C / (δ * (N : ℝ)))) := hmass
    _ = (M * C / δ) * ((Finset.Icc lo hi).card / (N : ℝ)) := by
      field_simp [hδ.ne', hNreal.ne']

private theorem sum_Icc_zero_interval_sub (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ r ∈ Finset.Icc (m + 1) n, f r) =
      (∑ r ∈ Finset.Icc 0 n, f r) - ∑ r ∈ Finset.Icc 0 m, f r := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      simp
  | succ n ih =>
      by_cases heq : m = n + 1
      · subst m
        simp
      · have hm : m ≤ n := by omega
        rw [Finset.sum_Icc_succ_top (by omega : m + 1 ≤ n + 1),
          Finset.sum_Icc_succ_top (by omega : 0 ≤ n + 1), ih hm]
        ring

private theorem collisionEntrance_window_eq_prefix_sub (N m n : ℕ) (a b : Site)
    (F : ℝ × Plane → ℝ) (hmn : m ≤ n) :
    collisionEntrance N (m + 1) n a b F =
      collisionEntrance N 0 n a b F - collisionEntrance N 0 m a b F := by
  unfold collisionEntrance
  exact sum_Icc_zero_interval_sub
    (fun r => collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z))) hmn







/-- Changing one positive macroscopic endpoint by `o(N)` microscopic slices
changes a bounded spatially tested entrance by `o(1)`. -/
theorem tendsto_collisionEntrance_endpoint_perturbation
    {u : ℝ} (hu : 0 < u) (Mseq Kseq : ℕ → ℕ)
    (hM : Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 u))
    (hK : Tendsto (fun N : ℕ => (Kseq N : ℝ) / N) atTop (𝓝 u))
    (aSite bSite : ℕ → Site) (F : ℝ × Plane → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ p, |F p| ≤ B) :
    Tendsto (fun N : ℕ =>
      |collisionEntrance N 0 (Mseq N) (aSite N) (bSite N) F -
        collisionEntrance N 0 (Kseq N) (aSite N) (bSite N) F|)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hstrip⟩ := collisionEntrance_abs_le_positiveTime_card
    (δ := u / 2) (half_pos hu)
  have hMlower : ∀ᶠ N : ℕ in atTop, u / 2 ≤ (Mseq N : ℝ) / N :=
    hM.eventually (Ici_mem_nhds (by linarith : u / 2 < u))
  have hKlower : ∀ᶠ N : ℕ in atTop, u / 2 ≤ (Kseq N : ℝ) / N :=
    hK.eventually (Ici_mem_nhds (by linarith : u / 2 < u))
  have hgap : Tendsto (fun N : ℕ =>
      |(Mseq N : ℝ) / N - (Kseq N : ℝ) / N|) atTop (𝓝 0) := by
    have hdiff := hM.sub hK
    simpa [Function.comp_def, sub_self, abs_zero] using
      (continuous_abs.continuousAt.tendsto.comp hdiff)
  apply squeeze_zero'
    (f := fun N : ℕ =>
      |collisionEntrance N 0 (Mseq N) (aSite N) (bSite N) F -
        collisionEntrance N 0 (Kseq N) (aSite N) (bSite N) F|)
    (g := fun N : ℕ => (B * C / (u / 2)) *
      |(Mseq N : ℝ) / N - (Kseq N : ℝ) / N|)
  · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 0, hMlower, hKlower] with N hN hml hkL
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hmin : (u / 2) * (N : ℝ) ≤ (min (Mseq N) (Kseq N) : ℝ) := by
      have hm : (u / 2) * (N : ℝ) ≤ (Mseq N : ℝ) :=
        (le_div_iff₀ hNreal).mp hml
      have hk : (u / 2) * (N : ℝ) ≤ (Kseq N : ℝ) :=
        (le_div_iff₀ hNreal).mp hkL
      exact le_min hm hk
    have hwindow := hstrip N (min (Mseq N) (Kseq N) + 1)
      (max (Mseq N) (Kseq N)) (aSite N) (bSite N) F B hN hB hF
    have htime : ∀ r ∈ Finset.Icc (min (Mseq N) (Kseq N) + 1)
        (max (Mseq N) (Kseq N)), (u / 2) * (N : ℝ) ≤ r := by
      intro r hr
      have hle : min (Mseq N) (Kseq N) ≤ r :=
        Nat.le_trans (Nat.le_succ _) (Finset.mem_Icc.mp hr).1
      calc
        (u / 2) * (N : ℝ) ≤ (min (Mseq N) (Kseq N) : ℝ) := hmin
        _ ≤ (r : ℝ) := by exact_mod_cast hle
    have hbound := hwindow htime
    have hcard : ((Finset.Icc (min (Mseq N) (Kseq N) + 1)
        (max (Mseq N) (Kseq N))).card : ℝ) =
        |(Mseq N : ℝ) - (Kseq N : ℝ)| := by
      have hnat : max (Mseq N) (Kseq N) + 1 -
          (min (Mseq N) (Kseq N) + 1) =
            max (Mseq N) (Kseq N) - min (Mseq N) (Kseq N) := by omega
      rw [Nat.card_Icc, hnat]
      by_cases h : Mseq N ≤ Kseq N
      · simp only [min_eq_left h, max_eq_right h]
        rw [Nat.cast_sub h, abs_of_nonpos]
        · ring
        · exact sub_nonpos.mpr (by exact_mod_cast h)
      · have hk : Kseq N ≤ Mseq N := Nat.le_of_not_ge h
        simp only [min_eq_right hk, max_eq_left hk]
        rw [Nat.cast_sub hk, abs_of_nonneg]
        · exact sub_nonneg.mpr (by exact_mod_cast hk)
    have hratio : ((Finset.Icc (min (Mseq N) (Kseq N) + 1)
        (max (Mseq N) (Kseq N))).card : ℝ) / N =
        |(Mseq N : ℝ) / N - (Kseq N : ℝ) / N| := by
      rw [hcard]
      have hdiv : (Mseq N : ℝ) / N - (Kseq N : ℝ) / N =
          ((Mseq N : ℝ) - (Kseq N : ℝ)) / N := by ring
      rw [hdiv, abs_div, abs_of_pos hNreal]
    have hprefix : collisionEntrance N 0 (Mseq N) (aSite N) (bSite N) F -
        collisionEntrance N 0 (Kseq N) (aSite N) (bSite N) F =
        (if Kseq N ≤ Mseq N then
          collisionEntrance N (Kseq N + 1) (Mseq N) (aSite N) (bSite N) F
          else -collisionEntrance N (Mseq N + 1) (Kseq N) (aSite N) (bSite N) F) := by
      by_cases h : Kseq N ≤ Mseq N
      · have hw := collisionEntrance_window_eq_prefix_sub N (Kseq N) (Mseq N)
          (aSite N) (bSite N) F h
        calc
          _ = collisionEntrance N (Kseq N + 1) (Mseq N)
              (aSite N) (bSite N) F := by rw [← hw]
          _ = if Kseq N ≤ Mseq N then
                collisionEntrance N (Kseq N + 1) (Mseq N)
                  (aSite N) (bSite N) F
              else -collisionEntrance N (Mseq N + 1) (Kseq N)
                  (aSite N) (bSite N) F := by simp [h]
      · have hm : Mseq N ≤ Kseq N := Nat.le_of_not_ge h
        have hw := collisionEntrance_window_eq_prefix_sub N (Mseq N) (Kseq N)
          (aSite N) (bSite N) F hm
        calc
          _ = -(collisionEntrance N 0 (Kseq N) (aSite N) (bSite N) F -
              collisionEntrance N 0 (Mseq N) (aSite N) (bSite N) F) := by ring
          _ = -collisionEntrance N (Mseq N + 1) (Kseq N)
              (aSite N) (bSite N) F := by rw [← hw]
          _ = if Kseq N ≤ Mseq N then
                collisionEntrance N (Kseq N + 1) (Mseq N)
                  (aSite N) (bSite N) F
              else -collisionEntrance N (Mseq N + 1) (Kseq N)
                  (aSite N) (bSite N) F := by simp [h]
    have hAbs : |collisionEntrance N 0 (Mseq N) (aSite N) (bSite N) F -
        collisionEntrance N 0 (Kseq N) (aSite N) (bSite N) F| =
        |collisionEntrance N (min (Mseq N) (Kseq N) + 1)
            (max (Mseq N) (Kseq N)) (aSite N) (bSite N) F| := by
      rw [hprefix]
      by_cases h : Kseq N ≤ Mseq N
      · simp [h]
      · have hm : Mseq N ≤ Kseq N := Nat.le_of_not_ge h
        simp [h, hm]
    rw [hAbs]
    calc
      |collisionEntrance N (min (Mseq N) (Kseq N) + 1)
          (max (Mseq N) (Kseq N)) (aSite N) (bSite N) F| ≤
        (B * C / (u / 2)) *
          ((Finset.Icc (min (Mseq N) (Kseq N) + 1)
            (max (Mseq N) (Kseq N))).card / (N : ℝ)) := hbound
      _ = (B * C / (u / 2)) *
          |(Mseq N : ℝ) / N - (Kseq N : ℝ) / N| := by rw [hratio]
  · simpa using hgap.const_mul (B * C / (u / 2))

/-- Collision entrance integrals converge for moving positive-time windows and moving starting sites. -/
theorem tendsto_collisionEntrance_spatial_test_away_zero_moving_window
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (M₀ M₁ : ℕ → ℕ)
    (hM₀ : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s))
    (hM₁ : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t))
    (aSite bSite : ℕ → Site)
    (haSite : ∀ N, aSite N ∈ evenLattice)
    (hbSite : ∀ N, bSite N ∈ evenLattice)
    (a b : Plane)
    (ha : Tendsto (fun N => latticeRepresentative N (aSite N)) atTop (𝓝 a))
    (hb : Tendsto (fun N => latticeRepresentative N (bSite N)) atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R B : ℝ) (hB : 0 ≤ B)
    (hFcont : Continuous F)
    (hFbound : ∀ u x, |F (u, x)| ≤ B)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R) :
    Tendsto (fun N : ℕ => collisionEntrance N (M₀ N + 1) (M₁ N)
      (aSite N) (bSite N) F) atTop
      (𝓝 ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F))) := by
  let K₀ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * s)
  let K₁ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  let P₀ : ℕ → ℝ := fun N => collisionEntrance N 0 (M₀ N) (aSite N) (bSite N) F
  let P₁ : ℕ → ℝ := fun N => collisionEntrance N 0 (M₁ N) (aSite N) (bSite N) F
  let Q₀ : ℕ → ℝ := fun N => collisionEntrance N 0 (K₀ N) (aSite N) (bSite N) F
  let Q₁ : ℕ → ℝ := fun N => collisionEntrance N 0 (K₁ N) (aSite N) (bSite N) F
  have hK₀ : Tendsto (fun N : ℕ => (K₀ N : ℝ) / N) atTop (𝓝 s) := by
    simpa [K₀] using SHF.Moments.tendsto_evenCeil_div s hs.le
  have hK₁ : Tendsto (fun N : ℕ => (K₁ N : ℝ) / N) atTop (𝓝 t) := by
    simpa [K₁] using SHF.Moments.tendsto_evenCeil_div t (le_of_lt (lt_trans hs hst))
  have hM₀lt : ∀ᶠ N : ℕ in atTop,
      (M₀ N : ℝ) / N < (s + t) / 2 :=
    hM₀.eventually (Iio_mem_nhds (by linarith : s < (s + t) / 2))
  have hM₁gt : ∀ᶠ N : ℕ in atTop,
      (s + t) / 2 < (M₁ N : ℝ) / N :=
    hM₁.eventually (Ioi_mem_nhds (by linarith : (s + t) / 2 < t))
  have hMmono : ∀ᶠ N : ℕ in atTop, M₀ N ≤ M₁ N := by
    filter_upwards [hM₀lt, hM₁gt, eventually_gt_atTop 0] with N h₀ h₁ hN
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hratio : (M₀ N : ℝ) / N < (M₁ N : ℝ) / N := lt_trans h₀ h₁
    have hcast : (M₀ N : ℝ) < (M₁ N : ℝ) :=
      (div_lt_div_iff_of_pos_right hNreal).mp hratio
    exact_mod_cast hcast.le
  have hKmono : ∀ N, K₀ N ≤ K₁ N := by
    intro N
    dsimp [K₀, K₁]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  have hwindow : ∀ᶠ N : ℕ in atTop,
      collisionEntrance N (M₀ N + 1) (M₁ N) (aSite N) (bSite N) F =
        (P₁ N - P₀ N) := by
    filter_upwards [hMmono] with N hN
    exact (collisionEntrance_window_eq_prefix_sub N (M₀ N) (M₁ N)
      (aSite N) (bSite N) F hN)
  have hfixed : ∀ N : ℕ,
      collisionEntrance N (K₀ N + 1) (K₁ N) (aSite N) (bSite N) F =
        Q₁ N - Q₀ N := by
    intro N
    exact collisionEntrance_window_eq_prefix_sub N (K₀ N) (K₁ N)
      (aSite N) (bSite N) F (hKmono N)
  have hP₀ : Tendsto (fun N : ℕ => |P₀ N - Q₀ N|) atTop (𝓝 0) := by
    simpa [P₀, Q₀] using tendsto_collisionEntrance_endpoint_perturbation hs
      M₀ K₀ hM₀ hK₀ aSite bSite F B hB (fun p => hFbound p.1 p.2)
  have hP₁ : Tendsto (fun N : ℕ => |P₁ N - Q₁ N|) atTop (𝓝 0) := by
    simpa [P₁, Q₁] using tendsto_collisionEntrance_endpoint_perturbation
      (lt_trans hs hst) M₁ K₁ hM₁ hK₁ aSite bSite F B hB
      (fun p => hFbound p.1 p.2)
  have hdiff : Tendsto (fun N : ℕ =>
      |collisionEntrance N (M₀ N + 1) (M₁ N) (aSite N) (bSite N) F -
        collisionEntrance N (K₀ N + 1) (K₁ N) (aSite N) (bSite N) F|)
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (f := fun N : ℕ =>
        |collisionEntrance N (M₀ N + 1) (M₁ N) (aSite N) (bSite N) F -
          collisionEntrance N (K₀ N + 1) (K₁ N) (aSite N) (bSite N) F|)
      (g := fun N : ℕ => |P₁ N - Q₁ N| + |P₀ N - Q₀ N|)
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · filter_upwards [hwindow] with N hN
      rw [hN, hfixed N]
      have halgebra : (P₁ N - P₀ N) - (Q₁ N - Q₀ N) =
          (P₁ N - Q₁ N) - (P₀ N - Q₀ N) := by ring
      rw [halgebra]
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (P₁ N - Q₁ N) 0 (P₀ N - Q₀ N))
    · simpa using hP₁.add hP₀
  have hfixedLimit := tendsto_collisionEntrance_spatial_test_away_zero
    hs hst aSite bSite haSite hbSite a b ha hb F R B hB hFcont hFbound hFsupport
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  filter_upwards [
      hdiff.eventually (Metric.ball_mem_nhds (0 : ℝ) hhalf),
      hfixedLimit.eventually (Metric.ball_mem_nhds
        ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F)) hhalf)]
      with N hdiffN hfixedN
  have hdistDiff : dist
      (collisionEntrance N (M₀ N + 1) (M₁ N) (aSite N) (bSite N) F)
      (collisionEntrance N (K₀ N + 1) (K₁ N) (aSite N) (bSite N) F) < ε / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, dist_zero_right, Real.norm_eq_abs,
      abs_abs] using hdiffN
  have hdistFixed : dist
      (collisionEntrance N (K₀ N + 1) (K₁ N) (aSite N) (bSite N) F)
      ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F)) < ε / 2 := by
    simpa only [Metric.mem_ball] using hfixedN
  calc
    dist (collisionEntrance N (M₀ N + 1) (M₁ N) (aSite N) (bSite N) F)
        ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F)) ≤
      dist (collisionEntrance N (M₀ N + 1) (M₁ N) (aSite N) (bSite N) F)
        (collisionEntrance N (K₀ N + 1) (K₁ N) (aSite N) (bSite N) F) +
      dist (collisionEntrance N (K₀ N + 1) (K₁ N) (aSite N) (bSite N) F)
        ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F)) :=
      dist_triangle _ _ _
    _ < ε := by linarith

/-- Collision entrances are linear under subtraction of tests. -/
theorem collisionEntrance_sub_test (N lo hi : ℕ) (a b : Site)
    (F G : ℝ × Plane → ℝ) :
    collisionEntrance N lo hi a b (fun p => F p - G p) =
      collisionEntrance N lo hi a b F - collisionEntrance N lo hi a b G := by
  unfold collisionEntrance collisionSlice
  simp only [Finset.sum_sub_distrib, mul_sub]

/-- Split a collision entrance at an interior microscopic clock. -/
theorem collisionEntrance_window_split (N lo K hi : ℕ) (a b : Site)
    (F : ℝ × Plane → ℝ) (hlo : lo ≤ K) (hKhi : K < hi) :
    collisionEntrance N lo hi a b F =
      collisionEntrance N lo K a b F + collisionEntrance N (K + 1) hi a b F := by
  have hdisj : Disjoint (Finset.Icc lo K) (Finset.Icc (K + 1) hi) := by
    apply Finset.disjoint_left.mpr
    intro r hr₁ hr₂
    have hr₁' := (Finset.mem_Icc.mp hr₁).2
    have hr₂' := (Finset.mem_Icc.mp hr₂).1
    omega
  have hunion : Finset.Icc lo hi = Finset.Icc lo K ∪ Finset.Icc (K + 1) hi := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  unfold collisionEntrance
  rw [hunion, Finset.sum_union hdisj]






end Critical2DKPZ.SHF.Moments

end
