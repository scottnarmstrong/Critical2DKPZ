/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceRiemann
public import Critical2DKPZ.SHF.Moments.CollisionProduct
public import Critical2DKPZ.SHF.Moments.EntranceReachability
public import Critical2DKPZ.Analysis.Lattice.Volume
import Critical2DKPZ.SHF.Moments.FirstMoment
import Critical2DKPZ.SHF.Moments.EntranceScaling
import Mathlib.Tactic

/-! # Collision entrances and shifted heat-cell sums

Reachable-site sums are reindexed by spatial parity, and compact support controls the absolute mass through the even-lattice cell partition. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped CompactlySupported Topology Uniformity

namespace Critical2DKPZ.SHF.Moments

/-- A unit spatial shift moves an endpoint reachable at time `r` from an even starting site to the even lattice. -/
def entranceParityShift (r : ℕ) : Site :=
  if r % 2 = 0 then 0 else ![1, 0]

/-- The entrance parity shift has the walk parity required from every even starting site. -/
theorem entranceParityShift_phase (r : ℕ) {a : Site} (ha : a ∈ evenLattice) :
    Even ((entranceParityShift r - a) 0 + (entranceParityShift r - a) 1 + r) := by
  change Even (a 0 + a 1) at ha
  rcases ha with ⟨k, hk⟩
  by_cases hr : r % 2 = 0
  · have hreq : (r : ℤ) = 2 * ((r / 2 : ℕ) : ℤ) := by omega
    simp [entranceParityShift, hr, Pi.sub_apply]
    refine ⟨((r / 2 : ℕ) : ℤ) - k, ?_⟩
    nlinarith only [hk, hreq]
  · have hreq : (r : ℤ) = 2 * ((r / 2 : ℕ) : ℤ) + 1 := by omega
    simp [entranceParityShift, hr, Pi.sub_apply]
    refine ⟨((r / 2 : ℕ) : ℤ) + 1 - k, ?_⟩
    nlinarith only [hk, hreq]

/-- Alternating between the two reachable spatial parity cosets does not change
the positive-time spacetime limit, provided both cell shifts vanish. -/
theorem tendsto_parityHeatKernelPairCellSum_timeSum_evenCeil {s t : ℝ}
    (hs : 0 < s) (hst : s < t)
    (aN bN : ℕ → Plane) (a b : Plane)
    (ha : Tendsto aN atTop (𝓝 a)) (hb : Tendsto bN atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ u x, |F (u, x)| ≤ C)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (hFcont : Continuous F) (δeven δodd : ℕ → Plane)
    (hδeven : Tendsto δeven atTop (𝓝 0)) (hδodd : Tendsto δodd atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (4 / (N : ℝ)) *
      ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t)),
        parityHeatKernelPairCellSum N ((r : ℝ) / N) aN bN δeven δodd F) atTop
      (𝓝 (4 * ∫ u in s..t, heatKernelPairProfileIntegral u a b F)) := by
  let M₀ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * s)
  let M₁ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  let profile : ℝ → ℝ := fun u => heatKernelPairProfileIntegral u a b F
  let profileExt : ℝ → ℝ := fun u => profile (max u s)
  have hprofileCont : ContinuousOn profile {u : ℝ | 0 < u} :=
    continuousOn_heatKernelPairProfileIntegral a b F R C hC hFbound hFsupport hFcont
  have hprofileExtCont : Continuous profileExt := by
    apply hprofileCont.comp_continuous
    · fun_prop
    · intro u
      exact lt_of_lt_of_le hs (le_max_right u s)
  have hMmono : ∀ N, M₀ N ≤ M₁ N := by
    intro N
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  have hM₀ratio : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s) := by
    simpa only [M₀] using tendsto_evenCeil_div s hs.le
  have hM₁ratio : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t) := by
    simpa only [M₁] using tendsto_evenCeil_div t (le_of_lt (lt_trans hs hst))
  have hM₀lower : ∀ᶠ N : ℕ in atTop, s ≤ (M₀ N : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hceil : (N : ℝ) * s ≤ (M₀ N : ℝ) := by
      simpa only [M₀] using Critical2DKPZ.le_evenCeil ((N : ℝ) * s)
    exact (le_div_iff₀ hNr).2 (by simpa only [mul_comm] using hceil)
  have hM₁upper : ∀ᶠ N : ℕ in atTop, (M₁ N : ℝ) / N ≤ t + 1 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNtwo : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    have hceil : (M₁ N : ℝ) ≤ (N : ℝ) * t + 2 := by
      have h := (Critical2DKPZ.evenCeil_lt_add_two
        (mul_nonneg (Nat.cast_nonneg N) (le_of_lt (lt_trans hs hst)))).le
      simpa only [M₁] using h
    apply (div_le_iff₀ hNr).2
    calc
      (M₁ N : ℝ) ≤ (N : ℝ) * t + 2 := hceil
      _ ≤ (N : ℝ) * t + (N : ℝ) := by nlinarith [hNtwo]
      _ = (t + 1) * (N : ℝ) := by ring
  have huniformEven := tendstoUniformlyOn_heatKernelPairCellSum_Icc
    (s := s) (t := t + 1) hs aN bN a b ha hb F R C hC hFbound hFsupport hFcont
    δeven hδeven
  have huniformOdd := tendstoUniformlyOn_heatKernelPairCellSum_Icc
    (s := s) (t := t + 1) hs aN bN a b ha hb F R C hC hFbound hFsupport hFcont
    δodd hδodd
  have huniformPhase : TendstoUniformlyOn
      (fun N u => parityHeatKernelPairCellSum N u aN bN δeven δodd F)
      profileExt atTop (Set.Icc s (t + 1)) := by
    intro U hU
    filter_upwards [huniformEven U hU, huniformOdd U hU] with N hEven hOdd
    intro u hu
    have huLower : s ≤ u := hu.1
    have hEq : profileExt u = profile u := by
      simp only [profileExt, profile, max_eq_left huLower]
    dsimp [parityHeatKernelPairCellSum]
    split_ifs with hparity
    · rw [hEq]
      exact hEven u hu
    · rw [hEq]
      exact hOdd u hu
  have htime := tendsto_scaledIntervalSum_uniformlyConverging
    hs hst hMmono hM₀ratio hM₁ratio profileExt
    (fun N u => parityHeatKernelPairCellSum N u aN bN δeven δodd F)
    hprofileExtCont huniformPhase hM₀lower hM₁upper
  have hprofileIntegral : ∫ u in s..t, profileExt u = ∫ u in s..t, profile u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc s t := by
      rw [uIcc_of_le hst.le] at hu
      exact hu
    simp only [profileExt, profile]
    rw [max_eq_left hu'.1]
  have htime4 : Tendsto
      (fun N : ℕ => (4 : ℝ) * ((N : ℝ)⁻¹ *
        ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
          parityHeatKernelPairCellSum N ((r : ℝ) / N) aN bN δeven δodd F)) atTop
      (𝓝 (4 * ∫ u in s..t, profile u)) := by
    have h := (tendsto_const_nhds (x := (4 : ℝ))).mul htime
    simpa only [hprofileIntegral] using h
  apply htime4.congr'
  filter_upwards with N
  simp only [M₀, M₁, parityHeatKernelPairCellSum]
  ring
/-- Translating the endpoint parity class identifies a reachable-site sum with the even-lattice heat-cell sum wherever the compact test is nonzero. -/
theorem heatKernelPairCellSum_eq_scaledEndpointHeatSum
    (N r : ℕ) (hN : 0 < N) (a b q : Site) (u : ℝ)
    (F : ℝ × Plane → ℝ)
    (hq : Even ((q - a) 0 + (q - a) 1 + r))
    (hcoverage : ∀ w : Site, w ∈ evenLattice →
      F (u, latticeRepresentative N (w + q)) ≠ 0 →
        w + q ∈ Polymer.endpoints a r) :
    heatKernelPairCellSum N u (fun _ => latticeRepresentative N a)
        (fun _ => latticeRepresentative N b) (fun _ => latticeRepresentative N q) F =
      (4 / (N : ℝ)) *
        ∑ z ∈ Polymer.endpoints a r,
          heatKernel u (latticeRepresentative N (z - a)) *
            heatKernel u (latticeRepresentative N (z - b)) *
              F (u, latticeRepresentative N z) := by
  classical
  let J : Finset Site := Polymer.endpoints a r
  let Jshift : Finset Site := J.image (fun z => z - q)
  let g : Site → ℝ := fun w =>
    F (u, latticeRepresentative N (w + q)) *
      (heatKernel u (latticeRepresentative N ((w + q) - a)) *
        heatKernel u (latticeRepresentative N ((w + q) - b)))
  have hrepAdd (w : Site) :
      latticeRepresentative N (w + q) =
        latticeRepresentative N w + latticeRepresentative N q := by
    have hsub := latticeRepresentative_sub N (w + q) q
    have hsite : (w + q) - q = w := by abel
    rw [hsite] at hsub
    calc
      latticeRepresentative N (w + q) =
          (latticeRepresentative N (w + q) - latticeRepresentative N q) +
            latticeRepresentative N q := by abel
      _ = latticeRepresentative N w + latticeRepresentative N q := by rw [← hsub]
  have hrepA (w : Site) :
      latticeRepresentative N ((w + q) - a) =
        latticeRepresentative N w + latticeRepresentative N q - latticeRepresentative N a := by
    rw [latticeRepresentative_sub N (w + q) a, hrepAdd]
  have hrepB (w : Site) :
      latticeRepresentative N ((w + q) - b) =
        latticeRepresentative N w + latticeRepresentative N q - latticeRepresentative N b := by
    rw [latticeRepresentative_sub N (w + q) b, hrepAdd]
  have hshiftEven : ∀ z ∈ J, z - q ∈ evenLattice := by
    intro z hz
    have hphase := endpoints_accessible_phase r a z hz
    have hEq : (z - q) 0 + (z - q) 1 =
        ((z - a) 0 + (z - a) 1 + r) -
          ((q - a) 0 + (q - a) 1 + r) := by
      simp only [Pi.sub_apply]
      ring
    change Even ((z - q) 0 + (z - q) 1)
    rw [hEq]
    exact Even.sub hphase hq
  have hJshiftEven : ∀ w ∈ Jshift, w ∈ evenLattice := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    exact hshiftEven z hz
  have htsum :
      heatKernelPairCellSum N u (fun _ => latticeRepresentative N a)
          (fun _ => latticeRepresentative N b) (fun _ => latticeRepresentative N q) F =
        ∑' w : Site, (volume (cell N w)).toReal * g w := by
    unfold heatKernelPairCellSum
    apply tsum_congr
    intro w
    simp only [g, hrepAdd, hrepA, hrepB]
  have hzero : ∀ w : Site, w ∉ Jshift →
      (volume (cell N w)).toReal * g w = 0 := by
    intro w hw
    by_cases heven : w ∈ evenLattice
    · by_cases hF : F (u, latticeRepresentative N (w + q)) = 0
      · simp [g, hF]
      · have hreach := hcoverage w heven hF
        have hmem : w ∈ Jshift := by
          apply Finset.mem_image.mpr
          refine ⟨w + q, hreach, ?_⟩
          abel
        exact (hw hmem).elim
    · have hempty : cell N w = ∅ := cell_eq_empty_of_not_even heven
      simp [hempty, g]
  have hfinite : (∑' w : Site, (volume (cell N w)).toReal * g w) =
      ∑ w ∈ Jshift, (volume (cell N w)).toReal * g w :=
    tsum_eq_sum (s := Jshift) hzero
  have hrepZ (z : Site) :
      latticeRepresentative N ((z - q) + q) = latticeRepresentative N z := by
    congr 1
    abel
  have hrepZA (z : Site) :
      latticeRepresentative N (((z - q) + q) - a) =
        latticeRepresentative N (z - a) := by
    congr 1
    abel
  have hrepZB (z : Site) :
      latticeRepresentative N (((z - q) + q) - b) =
        latticeRepresentative N (z - b) := by
    congr 1
    abel
  have hinj : Set.InjOn (fun z : Site => z - q) J := by
    intro z hz z' hz' h
    calc
      z = (z - q) + q := by abel
      _ = (z' - q) + q := congrArg (fun w : Site => w + q) h
      _ = z' := by abel
  calc
    _ = ∑ w ∈ Jshift, (volume (cell N w)).toReal * g w := by
      rw [htsum, hfinite]
    _ = ∑ w ∈ Jshift, (4 / (N : ℝ)) * g w := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [volume_cell_toReal hN (hJshiftEven w hw)]
    _ = ∑ z ∈ J, (4 / (N : ℝ)) * g (z - q) := by
      dsimp [Jshift]
      exact Finset.sum_image hinj
    _ = (4 / (N : ℝ)) *
        ∑ z ∈ J,
          heatKernel u (latticeRepresentative N (z - a)) *
            heatKernel u (latticeRepresentative N (z - b)) *
              F (u, latticeRepresentative N z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [g, hrepZ, hrepZA, hrepZB]
      ring

/-- At a microscopic grid time, the alternating cell shift agrees exactly with
the reachable endpoint sum whenever compact support is covered by endpoints. -/
theorem parityHeatKernelPairCellSum_eq_scaledEndpointHeatSum
    (N r : ℕ) (hN : 0 < N) (a b : Site)
    (ha : a ∈ evenLattice)
    (F : ℝ × Plane → ℝ)
    (hcoverage : ∀ w : Site, w ∈ evenLattice →
      F ((r : ℝ) / N, latticeRepresentative N (w + entranceParityShift r)) ≠ 0 →
        w + entranceParityShift r ∈ Polymer.endpoints a r) :
    parityHeatKernelPairCellSum N ((r : ℝ) / N)
      (fun _ => latticeRepresentative N a) (fun _ => latticeRepresentative N b)
      (fun M => latticeRepresentative M 0) (fun M => latticeRepresentative M ![1, 0]) F =
      (4 / (N : ℝ)) *
        ∑ z ∈ Polymer.endpoints a r,
          heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
            heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
              F ((r : ℝ) / N, latticeRepresentative N z) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hindex : ⌊(N : ℝ) * ((r : ℝ) / N)⌋₊ = r := by
    have hprod : (N : ℝ) * ((r : ℝ) / N) = (r : ℝ) := by
      field_simp [hNr.ne']
    rw [hprod, Nat.floor_natCast]
  have hphase := entranceParityShift_phase r ha
  have hrow := heatKernelPairCellSum_eq_scaledEndpointHeatSum N r hN a b
    (entranceParityShift r) ((r : ℝ) / N) F hphase hcoverage
  unfold parityHeatKernelPairCellSum
  rw [hindex]
  by_cases hr : r % 2 = 0
  · simp [hr]
    have hq : entranceParityShift r = 0 := by simp [entranceParityShift, hr]
    simpa only [heatKernelPairCellSum, hq] using hrow
  · simp [hr]
    have hq : entranceParityShift r = ![1, 0] := by simp [entranceParityShift, hr]
    simpa only [heatKernelPairCellSum, hq] using hrow

/-- On a time slab where the compact test is covered by reachable endpoints,
the heat-discrete entrance is exactly the alternating parity cell sum. -/
theorem collisionEntrance_heatDiscrete_eq_parityHeatKernelPairCellSum_of_cover
    (N lo hi : ℕ) (hN : 0 < N) (a b : Site) (ha : a ∈ evenLattice)
    (F : ℝ × Plane → ℝ)
    (hcoverage : ∀ r ∈ Finset.Icc lo hi, ∀ w : Site, w ∈ evenLattice →
      F ((r : ℝ) / N, latticeRepresentative N (w + entranceParityShift r)) ≠ 0 →
        w + entranceParityShift r ∈ Polymer.endpoints a r) :
    collisionEntrance_heatDiscrete N lo hi a b F =
      (4 / (N : ℝ)) *
        ∑ r ∈ Finset.Icc lo hi,
          parityHeatKernelPairCellSum N ((r : ℝ) / N)
            (fun _ => latticeRepresentative N a) (fun _ => latticeRepresentative N b)
            (fun M => latticeRepresentative M 0)
            (fun M => latticeRepresentative M ![1, 0]) F := by
  unfold collisionEntrance_heatDiscrete
  rw [← Finset.mul_sum]
  apply congrArg (fun x : ℝ => (4 / (N : ℝ)) * x)
  apply Finset.sum_congr rfl
  intro r hr
  rw [parityHeatKernelPairCellSum_eq_scaledEndpointHeatSum N r hN a b ha F
    (hcoverage r hr)]

/-- For compactly supported spatial tests, endpoint reachability supplies the
coverage hypothesis uniformly on a positive macroscopic time slab. -/
theorem eventually_collisionEntrance_heatDiscrete_eq_parityHeatKernelPairCellSum
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (aSite bSite : ℕ → Site) (a : Plane)
    (haSite : ∀ N, aSite N ∈ evenLattice)
    (ha : Tendsto (fun N => latticeRepresentative N (aSite N)) atTop (𝓝 a))
    (F : ℝ × Plane → ℝ) (R : ℝ)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R) :
    ∀ᶠ N : ℕ in atTop,
      collisionEntrance_heatDiscrete N (evenCeil ((N : ℝ) * s) + 1)
        (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F =
      (4 / (N : ℝ)) *
        ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1)
            (evenCeil ((N : ℝ) * t)),
          parityHeatKernelPairCellSum N ((r : ℝ) / N)
            (fun _ => latticeRepresentative N (aSite N))
            (fun _ => latticeRepresentative N (bSite N))
            (fun M => latticeRepresentative M 0)
            (fun M => latticeRepresentative M ![1, 0]) F := by
  let ε := s / 2
  let T := t + 1
  let lo : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * s) + 1
  let hi : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεT : ε ≤ T := by dsimp [ε, T]; linarith
  have hcoverEventual := eventually_endpoints_cover_scaled_compact
    (ε := ε) (T := T) (R := R + ‖a‖ + 1) hε hεT aSite
  have hcenterEventual : ∀ᶠ N : ℕ in atTop,
      ‖latticeRepresentative N (aSite N) - a‖ < 1 := by
    filter_upwards [ha.eventually (Metric.ball_mem_nhds a (by norm_num : (0:ℝ) < 1))]
      with N hN
    simpa only [Metric.mem_ball, dist_eq_norm] using hN
  filter_upwards [hcoverEventual, hcenterEventual, eventually_ge_atTop 2] with N hreach hcenter hNtwo
  have hN : 0 < N := by omega
  have hcenterBound : ‖latticeRepresentative N (aSite N)‖ ≤ ‖a‖ + 1 := by
    calc
      ‖latticeRepresentative N (aSite N)‖ ≤
          ‖latticeRepresentative N (aSite N) - a‖ + ‖a‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + ‖a‖ := add_le_add hcenter.le le_rfl
      _ = ‖a‖ + 1 := by ring
  have hcoverage : ∀ r ∈ Finset.Icc (lo N) (hi N), ∀ w : Site,
      w ∈ evenLattice →
      F ((r : ℝ) / N,
        latticeRepresentative N (w + entranceParityShift r)) ≠ 0 →
      w + entranceParityShift r ∈ Polymer.endpoints (aSite N) r := by
    intro r hr w hw hF
    have hrlo : lo N ≤ r := Finset.mem_Icc.mp hr |>.1
    have hrhi : r ≤ hi N := Finset.mem_Icc.mp hr |>.2
    have hlow : ε * (N : ℝ) ≤ r := by
      have hceil : (N : ℝ) * s ≤ (evenCeil ((N : ℝ) * s) : ℝ) := Critical2DKPZ.le_evenCeil _
      have hlo : ((evenCeil ((N : ℝ) * s) : ℕ) : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast (Nat.le_of_succ_le hrlo)
      dsimp [ε]
      nlinarith [hceil, hlo]
    have hhigh : (r : ℝ) ≤ T * N := by
      have hceil : (hi N : ℝ) ≤ (N : ℝ) * t + 2 := by
        dsimp [hi]
        exact (Critical2DKPZ.evenCeil_lt_add_two (mul_nonneg (Nat.cast_nonneg N)
          (le_of_lt (lt_trans hs hst)))).le
      have hhi : (r : ℝ) ≤ (hi N : ℝ) := by exact_mod_cast hrhi
      have hNtwoR : (2 : ℝ) ≤ N := by exact_mod_cast hNtwo
      dsimp [T]
      nlinarith [hhi, hceil, hNtwoR]
    have hphaseQ := entranceParityShift_phase r (haSite N)
    have hphaseW : Even (w 0 + w 1) := hw
    have hphase : Even
        (((w + entranceParityShift r) - aSite N) 0 +
          ((w + entranceParityShift r) - aSite N) 1 + r) := by
      have hsum :
          ((w + entranceParityShift r) - aSite N) 0 +
            ((w + entranceParityShift r) - aSite N) 1 + r =
          (w 0 + w 1) +
            ((entranceParityShift r - aSite N) 0 +
              (entranceParityShift r - aSite N) 1 + r) := by
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rw [hsum]
      exact Even.add hphaseW hphaseQ
    have hspace :
        ‖latticeRepresentative N ((w + entranceParityShift r) - aSite N)‖ ≤
          R + ‖a‖ + 1 := by
      have hrepSub := latticeRepresentative_sub N
        (w + entranceParityShift r) (aSite N)
      calc
        _ = ‖latticeRepresentative N (w + entranceParityShift r) -
              latticeRepresentative N (aSite N)‖ := by rw [hrepSub]
        _ ≤ ‖latticeRepresentative N (w + entranceParityShift r)‖ +
              ‖latticeRepresentative N (aSite N)‖ := norm_sub_le _ _
        _ ≤ R + (‖a‖ + 1) := add_le_add (hFsupport _ _ hF) hcenterBound
        _ = R + ‖a‖ + 1 := by ring
    exact hreach r hlow hhigh (w + entranceParityShift r) hphase hspace
  have hEq := collisionEntrance_heatDiscrete_eq_parityHeatKernelPairCellSum_of_cover
    N (lo N) (hi N) hN (aSite N) (bSite N) (haSite N) F hcoverage
  simpa only [lo, hi] using hEq

/-- Compact spatial support bounds the scaled absolute test mass over any
phase-correct endpoint set, uniformly in time and in the starting sites. -/
theorem scaledEndpoint_absSum_le_compactIntegralBound
    {R M : ℝ} (hM : 0 ≤ M)
    (F : ℝ × Plane → ℝ) (hFcont : Continuous F)
    (hFbound : ∀ u x, |F (u, x)| ≤ M)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N r : ℕ, 0 < N → ∀ a q : Site, ∀ u : ℝ,
      ‖latticeRepresentative N q‖ ≤ 2 →
      Even ((q - a) 0 + (q - a) 1 + r) →
      (4 / (N : ℝ)) *
        ∑ z ∈ Polymer.endpoints a r, |F (u, latticeRepresentative N z)| ≤ C := by
  let K : Set Plane := Metric.closedBall 0 (R + 4)
  let majorant : Plane → ℝ := K.indicator (fun _ => M)
  let C : ℝ := ∫ x : Plane, majorant x
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hMajorInt : Integrable majorant := by
    dsimp [majorant, K]
    exact (integrableOn_const hKcompact.measure_ne_top).integrable_indicator
      hKcompact.measurableSet
  have hC : 0 ≤ C := by
    dsimp [C]
    apply integral_nonneg
    intro x
    by_cases hx : x ∈ K
    · simp [majorant, hx, hM]
    · simp [majorant, hx]
  refine ⟨C, hC, ?_⟩
  intro N r hN a q u hqBound hphase
  let J : Finset Site := Polymer.endpoints a r
  let Jshift : Finset Site := J.image (fun z => z - q)
  let δ : Plane := latticeRepresentative N q
  let f : Plane → ℝ := fun x => |F (u, cellSample N x + δ)|
  have hslice : Continuous (fun x : Plane => F (u, x)) :=
    hFcont.comp (continuous_const.prodMk continuous_id)
  have hφsupport : HasCompactSupport (fun x : Plane => |F (u, x)|) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) R)
    apply Function.support_subset_iff'.mpr
    intro x hx
    by_contra hnot
    have hFx : F (u, x) ≠ 0 := by
      intro hz
      apply hnot
      simp [hz]
    have hxball : x ∈ Metric.closedBall (0 : Plane) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hFsupport u x hFx
    exact hx hxball
  let φ : C_c(Plane, ℝ) :=
    ⟨⟨fun x => |F (u, x)|, continuous_abs.comp hslice⟩, hφsupport⟩
  have hfInt : Integrable f := by
    have h := integrable_cellSample_shifted_compact_product N hN δ φ
      (fun _ : Plane => (1 : ℝ)) continuous_const
    simpa [f, φ] using h
  have hfMajor : ∀ x, f x ≤ majorant x := by
    intro x
    let y := cellSample N x + δ
    by_cases hFzero : F (u, y) = 0
    · have hzero : F (u, cellSample N x + δ) = 0 := by simpa [y] using hFzero
      change |F (u, cellSample N x + δ)| ≤ majorant x
      rw [hzero]
      by_cases hx : x ∈ K
      · simp [majorant, hx, hM]
      · simp [majorant, hx]
    · have hybound : ‖y‖ ≤ R := hFsupport u y hFzero
      have hdistSample : dist x (cellSample N x) ≤ 2 := by
        simpa only [dist_comm] using dist_cellSample_le_two hN x
      have hdistShift : dist (cellSample N x) y ≤ 2 := by
        dsimp [y]
        rw [dist_eq_norm]
        have hsub : cellSample N x - (cellSample N x + δ) = -δ := by abel
        rw [hsub, norm_neg]
        change ‖latticeRepresentative N q‖ ≤ 2
        exact hqBound
      have hdist : dist x y ≤ 4 := by
        calc
          dist x y ≤ dist x (cellSample N x) + dist (cellSample N x) y := dist_triangle _ _ _
          _ ≤ 2 + 2 := add_le_add hdistSample hdistShift
          _ = 4 := by norm_num
      have hxnorm : ‖x‖ ≤ dist x y + ‖y‖ := by
        rw [dist_eq_norm]
        exact norm_le_norm_sub_add x y
      have hxK : x ∈ K := by
        change x ∈ Metric.closedBall 0 (R + 4)
        rw [Metric.mem_closedBall, dist_zero_right]
        linarith
      simp [f, majorant, hxK]
      exact hFbound u y
  have hglobal : (∫ x : Plane, f x) ≤ C := by
    dsimp [C]
    exact integral_mono hfInt hMajorInt hfMajor
  have hshiftEven : ∀ z ∈ J, z - q ∈ evenLattice := by
    intro z hz
    have hphaseZ := endpoints_accessible_phase r a z hz
    have hsum : (z - q) 0 + (z - q) 1 =
        ((z - a) 0 + (z - a) 1 + r) - ((q - a) 0 + (q - a) 1 + r) := by
      simp only [Pi.sub_apply]
      ring
    change Even ((z - q) 0 + (z - q) 1)
    rw [hsum]
    exact Even.sub hphaseZ hphase
  have hJshiftEven : ∀ w ∈ Jshift, w ∈ evenLattice := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    exact hshiftEven z hz
  have hrepAdd (w : Site) :
      latticeRepresentative N (w + q) = latticeRepresentative N w + δ := by
    have hsub := latticeRepresentative_sub N (w + q) q
    have hsite : (w + q) - q = w := by abel
    rw [hsite] at hsub
    calc
      latticeRepresentative N (w + q) =
          (latticeRepresentative N (w + q) - latticeRepresentative N q) +
            latticeRepresentative N q := by abel
      _ = latticeRepresentative N w + δ := by
        dsimp [δ]
        rw [← hsub]
  have hconst (w : Site) (x : Plane) (hx : x ∈ cell N w) :
      f x = |F (u, latticeRepresentative N (w + q))| := by
    dsimp [f]
    rw [cellSample_eq_of_mem_cell hx, ← hrepAdd w]
  have hcell (w : Site) (hw : w ∈ Jshift) :
      (∫ x in cell N w, f x) =
        (volume (cell N w)).toReal * |F (u, latticeRepresentative N (w + q))| := by
    rw [setIntegral_congr_fun (measurableSet_cell N w) (fun x hx => hconst w x hx),
      setIntegral_const]
    simp only [measureReal_def, smul_eq_mul]
  have hdisj : Set.Pairwise (↑Jshift)
      (fun w w' : Site => Disjoint (cell N w) (cell N w')) := by
    intro w hw w' hw' hne
    exact pairwise_disjoint_cell N hne
  have hunion :
      (∫ x in ⋃ w ∈ Jshift, cell N w, f x) =
        ∑ w ∈ Jshift, ∫ x in cell N w, f x :=
    integral_biUnion_finset Jshift (fun w _ => measurableSet_cell N w) hdisj
      (fun w _ => hfInt.integrableOn)
  have hinj : Set.InjOn (fun z : Site => z - q) J := by
    intro z hz z' hz' h
    calc
      z = (z - q) + q := by abel
      _ = (z' - q) + q := congrArg (fun w : Site => w + q) h
      _ = z' := by abel
  have hsumImage :
      ∑ w ∈ Jshift, |F (u, latticeRepresentative N (w + q))| =
        ∑ z ∈ J, |F (u, latticeRepresentative N z)| := by
    calc
      _ = ∑ z ∈ J, |F (u, latticeRepresentative N ((z - q) + q))| := by
        dsimp [Jshift]
        exact Finset.sum_image hinj
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [show (z - q) + q = z by abel]
  have hsumCell :
      (4 / (N : ℝ)) * ∑ z ∈ J, |F (u, latticeRepresentative N z)| =
        ∫ x in ⋃ w ∈ Jshift, cell N w, f x := by
    calc
      _ = ∑ w ∈ Jshift, (4 / (N : ℝ)) *
          |F (u, latticeRepresentative N (w + q))| := by
        rw [← hsumImage, Finset.mul_sum]
      _ = ∑ w ∈ Jshift, (volume (cell N w)).toReal *
          |F (u, latticeRepresentative N (w + q))| := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [volume_cell_toReal hN (hJshiftEven w hw)]
      _ = ∑ w ∈ Jshift, ∫ x in cell N w, f x := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hcell w hw]
      _ = _ := hunion.symm
  have hset : (∫ x in ⋃ w ∈ Jshift, cell N w, f x) ≤ ∫ x : Plane, f x :=
    setIntegral_le_integral hfInt (Filter.Eventually.of_forall fun x => abs_nonneg _)
  rw [hsumCell]
  exact hset.trans hglobal

/-- The parity correction is at most two mesh units at every positive scale. -/
theorem norm_latticeRepresentative_entranceParityShift_le_two
    (N r : ℕ) (hN : 0 < N) :
    ‖latticeRepresentative N (entranceParityShift r)‖ ≤ 2 := by
  by_cases hr : r % 2 = 0
  · have hq : entranceParityShift r = 0 := by simp [entranceParityShift, hr]
    have hsite : siteToPlane (0 : Site) = 0 := by
      ext i
      simp [siteToPlane]
    rw [hq, latticeRepresentative, hsite]
    simp
  · have hq : entranceParityShift r = ![1, 0] := by
      simp [entranceParityShift, hr]
    rw [hq]
    have hsite : ‖siteToPlane ![1, 0]‖ ^ 2 = 1 := by
      rw [plane_norm_sq]
      simp [siteToPlane]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hNge : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hfrac : (2 : ℝ) / N ≤ 2 := by
      rw [div_le_iff₀ hNreal]
      nlinarith
    have hsq := norm_latticeRepresentative_sq N ![1, 0]
    rw [hsite] at hsq
    nlinarith [hsq, sq_nonneg (‖latticeRepresentative N ![1, 0]‖ - 2)]

/-- On a compactly supported test and a positive time slab, the summed local-CLT
error between the walk entrance and its heat-discrete version vanishes. -/
theorem tendsto_collisionEntrance_heatDiscrete_error_away_zero_compact
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (aSite bSite : ℕ → Site)
    (haSite : ∀ N, aSite N ∈ evenLattice)
    (hbSite : ∀ N, bSite N ∈ evenLattice)
    (F : ℝ × Plane → ℝ) (R M : ℝ) (hM : 0 ≤ M)
    (hFcont : Continuous F)
    (hFbound : ∀ u x, |F (u, x)| ≤ M)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R) :
    Tendsto (fun N : ℕ =>
      |collisionEntrance N (evenCeil ((N : ℝ) * s) + 1)
          (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F -
        collisionEntrance_heatDiscrete N (evenCeil ((N : ℝ) * s) + 1)
          (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F|) atTop (𝓝 0) := by
  let ε := s / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨Ctest, hCtest, htest⟩ :=
    scaledEndpoint_absSum_le_compactIntegralBound hM F hFcont hFbound hFsupport
  obtain ⟨Cclt, hCclt, hclt⟩ :=
    collisionEntrance_heatDiscrete_error_away_zero_evenStarts (ε := ε) hε
  let B : ℝ := 4 * Cclt * (t + 1) * Ctest
  have ht : 0 < t := lt_trans hs hst
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsmall := tendsto_const_div_nat B
  apply squeeze_zero_norm' _ hsmall
  filter_upwards [eventually_ge_atTop 3] with N hNthree
  have hN : 0 < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  let lo := evenCeil ((N : ℝ) * s) + 1
  let hi := evenCeil ((N : ℝ) * t)
  have hgap : ∀ r ∈ Finset.Icc lo hi, ε * (N : ℝ) ≤ r := by
    intro r hr
    have hlo : (evenCeil ((N : ℝ) * s) : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.le_of_succ_le (Finset.mem_Icc.mp hr).1)
    have hceil : (N : ℝ) * s ≤ (evenCeil ((N : ℝ) * s) : ℝ) := Critical2DKPZ.le_evenCeil _
    calc
      ε * (N : ℝ) ≤ (N : ℝ) * s := by
        dsimp [ε]
        nlinarith [mul_nonneg (Nat.cast_nonneg N) hs.le]
      _ ≤ (evenCeil ((N : ℝ) * s) : ℝ) := hceil
      _ ≤ (r : ℝ) := hlo
  have hcardNat : (Finset.Icc lo hi).card ≤ hi + 1 := by
    calc
      _ ≤ (Finset.range (hi + 1)).card := Finset.card_le_card (by
        intro r hr
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hr).2))
      _ = hi + 1 := by simp
  have hceilHi : (hi : ℝ) ≤ (N : ℝ) * t + 2 := by
    dsimp [hi]
    exact (Critical2DKPZ.evenCeil_lt_add_two
      (mul_nonneg (Nat.cast_nonneg N) (le_of_lt (lt_trans hs hst)))).le
  have hcard : ((Finset.Icc lo hi).card : ℝ) ≤ (t + 1) * (N : ℝ) := by
    have hcard' : ((Finset.Icc lo hi).card : ℝ) ≤ (hi : ℝ) + 1 := by
      exact_mod_cast hcardNat
    have hNthreeR : (3 : ℝ) ≤ N := by exact_mod_cast hNthree
    dsimp [hi]
    nlinarith [hcard', hceilHi, hNthreeR]
  have hrow : ∀ r ∈ Finset.Icc lo hi,
      ∑ z ∈ Polymer.endpoints (aSite N) r,
        |F ((r : ℝ) / N, latticeRepresentative N z)| ≤
          (N / 4) * Ctest := by
    intro r _hr
    have hscaled := htest N r hN (aSite N) (entranceParityShift r)
      ((r : ℝ) / N)
      (norm_latticeRepresentative_entranceParityShift_le_two N r hN)
      (entranceParityShift_phase r (haSite N))
    have hfactor :
        ∑ z ∈ Polymer.endpoints (aSite N) r,
          |F ((r : ℝ) / N, latticeRepresentative N z)| =
        (N / 4) * ((4 / N) *
          ∑ z ∈ Polymer.endpoints (aSite N) r,
            |F ((r : ℝ) / N, latticeRepresentative N z)|) := by
      field_simp [hNreal.ne']
    calc
      _ = (N / 4) * ((4 / N) *
          ∑ z ∈ Polymer.endpoints (aSite N) r,
            |F ((r : ℝ) / N, latticeRepresentative N z)|) := hfactor
      _ ≤ (N / 4) * Ctest :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
  have htotal :
      ∑ r ∈ Finset.Icc lo hi,
        ∑ z ∈ Polymer.endpoints (aSite N) r,
          |F ((r : ℝ) / N, latticeRepresentative N z)| ≤
        ((Finset.Icc lo hi).card : ℝ) * ((N / 4) * Ctest) := by
    calc
      _ ≤ ∑ _r ∈ Finset.Icc lo hi, (N / 4) * Ctest :=
        Finset.sum_le_sum fun r hr => hrow r hr
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have htotalBound :
      ∑ r ∈ Finset.Icc lo hi,
        ∑ z ∈ Polymer.endpoints (aSite N) r,
          |F ((r : ℝ) / N, latticeRepresentative N z)| ≤
        (t + 1) * (N : ℝ) * ((N / 4) * Ctest) :=
    htotal.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have herror := hclt N lo hi hN (aSite N) (bSite N)
    (haSite N) (hbSite N) F hgap
  have herrorBound :
      |collisionEntrance N lo hi (aSite N) (bSite N) F -
        collisionEntrance_heatDiscrete N lo hi (aSite N) (bSite N) F| ≤ B / N := by
    calc
      _ ≤ (16 * Cclt / N ^ 3) *
          ∑ r ∈ Finset.Icc lo hi,
            ∑ z ∈ Polymer.endpoints (aSite N) r,
              |F ((r : ℝ) / N, latticeRepresentative N z)| := herror
      _ ≤ (16 * Cclt / N ^ 3) *
          ((t + 1) * (N : ℝ) * ((N / 4) * Ctest)) :=
        mul_le_mul_of_nonneg_left htotalBound (by positivity)
      _ = B / N := by
        dsimp [B]
        field_simp [hNreal.ne']
        ring
  simpa only [lo, hi, Real.norm_eq_abs, abs_abs] using herrorBound

/-- Spatially tested collision entrances converge on a positive time slab for
moving even-lattice starts, with the planar heat-pair profile as limit. -/
theorem tendsto_collisionEntrance_spatial_test_away_zero
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (aSite bSite : ℕ → Site)
    (haSite : ∀ N, aSite N ∈ evenLattice)
    (hbSite : ∀ N, bSite N ∈ evenLattice)
    (a b : Plane)
    (ha : Tendsto (fun N => latticeRepresentative N (aSite N)) atTop (𝓝 a))
    (hb : Tendsto (fun N => latticeRepresentative N (bSite N)) atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R M : ℝ) (hM : 0 ≤ M)
    (hFcont : Continuous F)
    (hFbound : ∀ u x, |F (u, x)| ≤ M)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R) :
    Tendsto (fun N : ℕ => collisionEntrance N
      (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t))
      (aSite N) (bSite N) F) atTop
      (𝓝 ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F))) := by
  let aN : ℕ → Plane := fun N => latticeRepresentative N (aSite N)
  let bN : ℕ → Plane := fun N => latticeRepresentative N (bSite N)
  let δeven : ℕ → Plane := fun N => latticeRepresentative N 0
  let δodd : ℕ → Plane := fun N => latticeRepresentative N ![1, 0]
  have hδeven : Tendsto δeven atTop (𝓝 0) := by
    simpa [δeven] using tendsto_latticeRepresentative_fixed_site (0 : Site)
  have hδodd : Tendsto δodd atTop (𝓝 0) := by
    simpa [δodd] using tendsto_latticeRepresentative_fixed_site ![1, 0]
  have hheat := tendsto_parityHeatKernelPairCellSum_timeSum_evenCeil
    hs hst aN bN a b (by simpa [aN] using ha) (by simpa [bN] using hb)
    F R M hM hFbound hFsupport hFcont δeven δodd hδeven hδodd
  have hbridge := eventually_collisionEntrance_heatDiscrete_eq_parityHeatKernelPairCellSum
    hs hst aSite bSite a haSite ha F R hFsupport
  have hdiscrete : Tendsto (fun N : ℕ => collisionEntrance_heatDiscrete N
      (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t))
      (aSite N) (bSite N) F) atTop
      (𝓝 ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F))) := by
    apply hheat.congr'
    filter_upwards [hbridge] with N hN
    have hsum :
        ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1)
            (evenCeil ((N : ℝ) * t)),
          parityHeatKernelPairCellSum N ((r : ℝ) / N) aN bN δeven δodd F =
        ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1)
            (evenCeil ((N : ℝ) * t)),
          parityHeatKernelPairCellSum N ((r : ℝ) / N)
            (fun _ => latticeRepresentative N (aSite N))
            (fun _ => latticeRepresentative N (bSite N))
            (fun _ => latticeRepresentative N 0)
            (fun _ => latticeRepresentative N ![1, 0]) F := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [parityHeatKernelPairCellSum, heatKernelPairCellSum,
        aN, bN, δeven, δodd]
    calc
      _ = (4 / (N : ℝ)) *
          ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1)
              (evenCeil ((N : ℝ) * t)),
            parityHeatKernelPairCellSum N ((r : ℝ) / N)
              (fun _ => latticeRepresentative N (aSite N))
              (fun _ => latticeRepresentative N (bSite N))
              (fun _ => latticeRepresentative N 0)
              (fun _ => latticeRepresentative N ![1, 0]) F :=
        congrArg (fun x : ℝ => (4 / (N : ℝ)) * x) hsum
      _ = collisionEntrance_heatDiscrete N
          (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t))
          (aSite N) (bSite N) F := hN.symm
  have herr := tendsto_collisionEntrance_heatDiscrete_error_away_zero_compact
    hs hst aSite bSite haSite hbSite F R M hM hFcont hFbound hFsupport
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hηhalf : 0 < η / 2 := by linarith
  filter_upwards [
      hdiscrete.eventually (Metric.ball_mem_nhds _ hηhalf),
      herr.eventually (Metric.ball_mem_nhds (0 : ℝ) hηhalf)] with N hdiscreteN herrN
  have hdiscreteDist : dist (collisionEntrance_heatDiscrete N
      (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t))
      (aSite N) (bSite N) F)
      ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F)) < η / 2 :=
    Metric.mem_ball.mp hdiscreteN
  have herrAbs :
      |collisionEntrance N (evenCeil ((N : ℝ) * s) + 1)
          (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F -
        collisionEntrance_heatDiscrete N (evenCeil ((N : ℝ) * s) + 1)
          (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F| < η / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_abs] using herrN
  have herrDist : dist
      (collisionEntrance N (evenCeil ((N : ℝ) * s) + 1)
        (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F)
      (collisionEntrance_heatDiscrete N (evenCeil ((N : ℝ) * s) + 1)
        (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F) < η / 2 := by
    simpa only [Real.dist_eq] using herrAbs
  calc
    dist (collisionEntrance N (evenCeil ((N : ℝ) * s) + 1)
        (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F)
        ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F)) ≤
      dist (collisionEntrance N (evenCeil ((N : ℝ) * s) + 1)
          (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F)
        (collisionEntrance_heatDiscrete N (evenCeil ((N : ℝ) * s) + 1)
          (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F) +
      dist (collisionEntrance_heatDiscrete N (evenCeil ((N : ℝ) * s) + 1)
          (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F)
        ((4 : ℝ) * (∫ u in s..t, heatKernelPairProfileIntegral u a b F)) :=
      dist_triangle _ _ _
    _ < η := by linarith
end Critical2DKPZ.SHF.Moments

end
