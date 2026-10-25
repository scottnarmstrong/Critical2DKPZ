/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeIntegral
public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeProfileHorizon
import Mathlib.Tactic

/-! # Interior tested renewal-time integrals on arbitrary finite horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- The full spatial profile, summed over an interior renewal-time slab,
converges to its continuum time integral along moving microscopic horizons
and incoming and collision locations. -/
theorem tendsto_pairTwoTestedSpatialSlice_timeIntegral_horizon
    (ϑ H : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 H))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (zN N 0 + zN N 1 + (L N : ℤ)))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < H) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t)),
        pairTwoTestedSpatialSlice ϑ N r (L N - r) φ (xN N) (zN N)) atTop
      (𝓝 (∫ u in s..t,
        pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z)) := by
  let lo : ℝ := s / 2
  let hi : ℝ := (t + H) / 2
  have hlo : 0 < lo := half_pos hs
  have hlos : lo < s := half_lt_self hs
  have hthi : t < hi := by dsimp [hi]; linarith only [ht]
  have hhi : hi < H := by dsimp [hi]; linarith only [ht]
  have hlohi : lo ≤ hi := (hlos.trans (hst.trans hthi)).le
  let c : ℝ → ℝ := fun u => max lo (min hi u)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcmem (u : ℝ) : c u ∈ Set.Icc lo hi := clamp_interval_mem hlohi u
  let F : ℝ → ℝ := fun u =>
    pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z
  let fN : ℕ → ℝ → ℝ := fun N u =>
    pairTwoTestedSpatialSliceProfile ϑ N (L N) φ (xN N) (zN N) u
  have hFcont := continuousOn_pairTwoTestedSpatialProfile_time
    (ϑ - Real.eulerMascheroniConstant) H φ a z
  have hFc : Continuous (fun u => F (c u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hu : c u ∈ Set.Ioo 0 (H) :=
      ⟨hlo.trans_le (hcmem u).1, (hcmem u).2.trans_lt hhi⟩
    have hf : ContinuousAt F (c u) := hFcont.continuousAt (isOpen_Ioo.mem_nhds hu)
    exact ContinuousAt.comp' (f := c) (g := F) hf hc.continuousAt
  have huniform := tendstoUniformlyOn_pairTwoTestedSpatialSliceProfile_Icc_horizon
    ϑ H L hL φ xN hx a ha zN z hz hphase hlo hhi
  have hclampUniform : TendstoUniformlyOn (fun N u => fN N (c u))
      (fun u => F (c u)) atTop (Set.Icc s (t + 1)) := by
    rw [Metric.tendstoUniformlyOn_iff] at huniform ⊢
    intro ε hε
    filter_upwards [huniform ε hε] with N hN
    intro u hu
    exact hN (c u) (hcmem u)
  let M₀ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * s)
  let M₁ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  have hmono (N : ℕ) : M₀ N ≤ M₁ N :=
    Critical2DKPZ.evenCeil_mono (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  have hr₀ : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s) :=
    tendsto_evenCeil_div s hs.le
  have hr₁ : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t) :=
    tendsto_evenCeil_div t (hs.trans hst).le
  have hlower : ∀ᶠ N : ℕ in atTop, s ≤ (M₀ N : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    exact (le_div_iff₀ hNr).2 (by simpa only [M₀, mul_comm] using Critical2DKPZ.le_evenCeil ((N : ℝ) * s))
  have hupper : ∀ᶠ N : ℕ in atTop, (M₁ N : ℝ) / N ≤ t + 1 :=
    (hr₁.eventually (Iio_mem_nhds (by linarith : t < t + 1))).mono fun N hN => hN.le
  have hbase := tendsto_scaledIntervalSum_uniformlyConverging hs hst hmono hr₀ hr₁
    (fun u => F (c u)) (fun N u => fN N (c u)) hFc hclampUniform hlower hupper
  have htarget : (∫ u in s..t, F (c u)) = ∫ u in s..t, F u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hst.le] at hu
    have hu' : u ∈ Set.Icc lo hi := ⟨hlos.le.trans hu.1, hu.2.trans hthi.le⟩
    change F (c u) = F u
    rw [show c u = u from clamp_interval_eq hu']
  rw [htarget] at hbase
  apply hbase.congr'
  filter_upwards [eventually_gt_atTop 0,
    hr₀.eventually (Ioi_mem_nhds hlos), hr₁.eventually (Iio_mem_nhds hthi)] with N hN hloN hhiN
  apply congrArg (fun r : ℝ => (N : ℝ)⁻¹ * r)
  apply Finset.sum_congr rfl
  intro r hr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr' := Finset.mem_Icc.mp hr
  have hlow : lo ≤ (r : ℝ) / N := by
    apply hloN.le.trans
    exact div_le_div_of_nonneg_right (by exact_mod_cast (show M₀ N ≤ r by omega)) hNr.le
  have hhigh : (r : ℝ) / N ≤ hi := by
    apply le_trans _ hhiN.le
    exact div_le_div_of_nonneg_right (by exact_mod_cast hr'.2) hNr.le
  have hcu : c ((r : ℝ) / N) = (r : ℝ) / N := clamp_interval_eq ⟨hlow, hhigh⟩
  have hfloor : Nat.floor ((N : ℝ) * ((r : ℝ) / N)) = r := by
    rw [show (N : ℝ) * ((r : ℝ) / N) = r by field_simp, Nat.floor_natCast]
  simp only [hcu, fN, pairTwoTestedSpatialSliceProfile, hfloor]

/-- The interior future renewal sum has the continuum time-integrated spatial
profile as its limit, in the original `N²` future-tail normalization. -/
theorem tendsto_pairTwo_testedFuture_interior_horizon
    (ϑ H : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 H))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (zN N 0 + zN N 1 + (L N : ℤ)))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < H) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * criticalSigmaSq ϑ N *
      ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t)),
        ∑ d ∈ endpoints 0 r, Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
          pairTwoFutureTerminalCellFactor N (L N - r) φ (xN N) (zN N + d) 0 *
          pairTwoFutureTerminalCellFactor N (L N - r) φ (xN N) (zN N + d) 1) atTop
      (𝓝 (∫ u in s..t,
        pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z)) := by
  have h := tendsto_pairTwoTestedSpatialSlice_timeIntegral_horizon
    ϑ H L hL φ xN hx a ha zN z hz hphase hs hst ht
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum : (∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t)),
      pairTwoTestedSpatialSlice ϑ N r (L N - r) φ (xN N) (zN N)) =
      (N : ℝ) ^ 3 * criticalSigmaSq ϑ N *
        ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t)),
          ∑ d ∈ endpoints 0 r, Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
            pairTwoFutureTerminalCellFactor N (L N - r) φ (xN N) (zN N + d) 0 *
            pairTwoFutureTerminalCellFactor N (L N - r) φ (xN N) (zN N + d) 1 := by
    simp only [pairTwoTestedSpatialSlice, Finset.mul_sum]
  rw [hsum]
  field_simp

end Critical2DKPZ.SHF.Moments
