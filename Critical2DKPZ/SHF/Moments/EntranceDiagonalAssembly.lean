/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceDiagonal
public import Critical2DKPZ.SHF.Moments.EntranceDiagonalLimit
public import Critical2DKPZ.SHF.Moments.EntranceMixedCenter
public import Critical2DKPZ.SHF.Moments.EntranceRiemann
public import Critical2DKPZ.SHF.Moments.EntranceBridge
public import Critical2DKPZ.SHF.Moments.EntranceOffDiagonal
import Mathlib.Tactic

/-! # Integrability of the diagonal heat profile at time zero -/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- A linearly vanishing test makes the diagonal heat profile integrable down to time zero, with absolute integral bounded by `5 * L * (δ + 2 * √δ)` on a short interval. -/
theorem exists_integrable_diagonal_heatProfile_shortInterval_bound
    (a : Plane) (F : ℝ × Plane → ℝ) (L R C : ℝ)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hFbound : ∀ u x, |F (u, x)| ≤ C)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (hFcont : Continuous F)
    (hFvanish : ∀ u x, 0 < u → |F (u, x)| ≤ L * (u + ‖x - a‖))
    {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun u => heatKernelPairProfileIntegral u a a F) volume 0 t ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ t →
        |∫ u in (0 : ℝ)..δ, heatKernelPairProfileIntegral u a a F| ≤
          5 * L * (δ + 2 * Real.sqrt δ) := by
  let profile : ℝ → ℝ := fun u => heatKernelPairProfileIntegral u a a F
  let majorant : ℝ → ℝ := fun u => 5 * L * (1 + u ^ (-(1 / 2 : ℝ)))
  have hprofileCont : ContinuousOn profile {u : ℝ | 0 < u} :=
    continuousOn_heatKernelPairProfileIntegral a a F R C hC hFbound hFsupport hFcont
  have hpowInt : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hbaseInt : IntervalIntegrable (fun u : ℝ => 1 + u ^ (-(1 / 2 : ℝ))) volume 0 t :=
    intervalIntegrable_const.add hpowInt
  have hmajorantInt : IntervalIntegrable majorant volume 0 t := by
    dsimp [majorant]
    exact hbaseInt.const_mul (5 * L)
  have hprofileAES (δ : ℝ) (hδ : 0 < δ) :
      AEStronglyMeasurable profile (volume.restrict (Set.uIoc 0 δ)) := by
    rw [Set.uIoc_of_le hδ.le]
    apply (hprofileCont.mono (Set.Ioc_subset_Ioi_self)).aestronglyMeasurable
    exact measurableSet_Ioc
  have hrootInv (u : ℝ) (hu : 0 < u) :
      u ^ (-(1 / 2 : ℝ)) = (Real.sqrt u)⁻¹ := by
    rw [show (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg hu.le, Real.sqrt_eq_rpow]
  have hprofileBound (u : ℝ) (hu : 0 < u) :
      |profile u| ≤ 5 * L * (1 + u ^ (-(1 / 2 : ℝ))) := by
    have hdiag := heatKernelPairProfileIntegral_diagonal_bound F L hL hFcont
      (fun v x hv => hFvanish v x hv) hu
    have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
    have hsqrtSq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
    have hkernel : heatKernel (2 * u) 0 = (4 * Real.pi * u)⁻¹ := by
      rw [heatKernel_at_zero]
      congr 1
      ring
    have hkernelLe : heatKernel (2 * u) 0 ≤ (4 * u)⁻¹ := by
      rw [hkernel]
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      nlinarith [Real.pi_gt_three, hu]
    have hsqrtHalf : Real.sqrt (u / 2) ≤ Real.sqrt u := by
      apply Real.sqrt_le_sqrt
      nlinarith [hu.le]
    have hbracket : u + (9 / 2) * Real.sqrt (u / 2) ≤
        u + (9 / 2) * Real.sqrt u := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsqrtHalf (by norm_num))
    have hsimple : heatKernel (2 * u) 0 *
        (u + (9 / 2) * Real.sqrt (u / 2)) ≤
        1 / 4 + (9 / 8) * (Real.sqrt u)⁻¹ := by
      calc
        _ ≤ heatKernel (2 * u) 0 * (u + (9 / 2) * Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hbracket (heatKernel_nonneg (by positivity) 0)
        _ ≤ (4 * u)⁻¹ * (u + (9 / 2) * Real.sqrt u) :=
          mul_le_mul_of_nonneg_right hkernelLe (by positivity)
        _ = 1 / 4 + (9 / 8) * (Real.sqrt u)⁻¹ := by
          field_simp [hu.ne', hsqrt.ne']
          nlinarith [hsqrtSq]
    have hinvNonneg : 0 ≤ (Real.sqrt u)⁻¹ := inv_nonneg.mpr hsqrt.le
    have hsimple' : heatKernel (2 * u) 0 *
        (u + (9 / 2) * Real.sqrt (u / 2)) ≤
        5 * (1 + (Real.sqrt u)⁻¹) := by
      nlinarith [hsimple, hinvNonneg]
    have hbound := mul_le_mul_of_nonneg_left hsimple' hL
    calc
      |profile u| ≤ L * heatKernel (2 * u) 0 *
          (u + (9 / 2) * Real.sqrt (u / 2)) := by simpa [profile] using hdiag
      _ ≤ 5 * L * (1 + (Real.sqrt u)⁻¹) := by nlinarith [hbound]
      _ = 5 * L * (1 + u ^ (-(1 / 2 : ℝ))) := by rw [hrootInv u hu]
  have hprofileInt : IntervalIntegrable profile volume 0 t := by
    apply hmajorantInt.mono_fun' (hprofileAES t ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rcases hu with ⟨hu, hut⟩
    have hu' : 0 < u := by simpa [min_eq_left (le_of_lt ht)] using hu
    change ‖profile u‖ ≤ majorant u
    rw [Real.norm_eq_abs]
    simpa [majorant] using hprofileBound u hu'
  refine ⟨by simpa [profile] using hprofileInt, ?_⟩
  intro δ hδ hδt
  have hIccsub : Set.uIcc (0 : ℝ) δ ⊆ Set.uIcc 0 t :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hδ, hδt⟩))
  have hpowIntδ := hpowInt.mono_set hIccsub
  have hbaseIntδ : IntervalIntegrable
      (fun u : ℝ => 1 + u ^ (-(1 / 2 : ℝ))) volume 0 δ :=
    intervalIntegrable_const.add hpowIntδ
  have hmajorantIntδ : IntervalIntegrable majorant volume 0 δ := by
    dsimp [majorant]
    exact hbaseIntδ.const_mul (5 * L)
  have hprofileIntδ : IntervalIntegrable profile volume 0 δ :=
    hprofileInt.mono_set hIccsub
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (f := profile) (le_of_lt hδ)
    (Filter.Eventually.of_forall fun u hu => by
      rcases hu with ⟨hu, hut⟩
      change ‖profile u‖ ≤ majorant u
      rw [Real.norm_eq_abs]
      simpa [majorant] using hprofileBound u hu)
    hmajorantIntδ
  have hpowIntegral :
      (∫ u in (0 : ℝ)..δ, u ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt δ := by
    rw [integral_rpow (a := 0) (b := δ) (r := -(1 / 2 : ℝ))
      (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
    simp
    ring
  have hmajorantIntegral :
      (∫ u in (0 : ℝ)..δ, majorant u) = 5 * L * (δ + 2 * Real.sqrt δ) := by
    dsimp [majorant]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const hpowIntδ,
      intervalIntegral.integral_const, hpowIntegral]
    simp
  rw [Real.norm_eq_abs] at hnorm
  rw [hmajorantIntegral] at hnorm
  simpa [profile] using hnorm

private theorem collisionEntrance_split_at (N lo mid hi : ℕ) (a b : Site)
    (F : ℝ × Plane → ℝ) (hlo : lo ≤ mid) (hmid : mid ≤ hi) :
    collisionEntrance N lo hi a b F =
      collisionEntrance N lo mid a b F + collisionEntrance N (mid + 1) hi a b F := by
  have hsplit : Finset.Icc lo hi =
      Finset.Icc lo mid ∪ Finset.Icc (mid + 1) hi := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint : Disjoint (Finset.Icc lo mid) (Finset.Icc (mid + 1) hi) := by
    apply Finset.disjoint_left.mpr
    intro r hr₁ hr₂
    simp only [Finset.mem_Icc] at hr₁ hr₂
    omega
  unfold collisionEntrance
  rw [hsplit, Finset.sum_union hdisjoint]

private theorem heatKernel_twoTime_le_inverse_gap_sq {z : Plane} (hz : z ≠ 0)
    {u : ℝ} (hu : 0 < u) :
    Critical2DKPZ.heatKernel (2 * u) z ≤ (Real.pi * ‖z‖ ^ 2)⁻¹ := by
  let v : ℝ := ‖z‖ ^ 2 / (4 * u)
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hv : 0 < v := by dsimp [v]; positivity
  have hvexp : v ≤ Real.exp v := by
    have h := Real.add_one_le_exp v
    linarith
  have hexp : Real.exp (-v) ≤ v⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos v) hv).2 hvexp
  have hformula : Critical2DKPZ.heatKernel (2 * u) z =
      (4 * Real.pi * u)⁻¹ * Real.exp (-v) := by
    rw [Critical2DKPZ.heatKernel_eq_exp]
    have hcoef : (2 * Real.pi * (2 * u))⁻¹ = (4 * Real.pi * u)⁻¹ := by
      field_simp
      norm_num
    have hexpArg : -((2 * (2 * u))⁻¹) * ‖z‖ ^ 2 = -v := by
      dsimp [v]
      field_simp [hu.ne']
      ring
    rw [hcoef, hexpArg]
  calc
    Critical2DKPZ.heatKernel (2 * u) z =
        (4 * Real.pi * u)⁻¹ * Real.exp (-v) := hformula
    _ ≤ (4 * Real.pi * u)⁻¹ * v⁻¹ :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (Real.pi * ‖z‖ ^ 2)⁻¹ := by
      dsimp [v]
      field_simp [hu.ne', hnorm.ne']

/-- The spatially tested collision entrance converges from time zero for a moving diagonal
start whose scaled center error is `o(1 / log N)`, when the test vanishes linearly at the
entrance center. The short-time continuum profile is integrable by the companion bound above. -/
theorem tendsto_collisionEntrance_spatial_test_coalescing_center_zero
    {t : ℝ} (ht : 0 < t) (aN bN : ℕ → Site) (c : Plane)
    (hEvenA : ∀ N, aN N ∈ evenLattice) (hEvenB : ∀ N, bN N ∈ evenLattice)
    (hcenterA : Tendsto
      (fun N : ℕ => ‖latticeRepresentative N (aN N) - c‖ *
        Real.log ((N : ℝ) + 2)) atTop (𝓝 0))
    (hcenterB : Tendsto
      (fun N : ℕ => ‖latticeRepresentative N (bN N) - c‖ *
        Real.log ((N : ℝ) + 2)) atTop (𝓝 0))
    (F : ℝ × Plane → ℝ) (R M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hFcont : Continuous F)
    (hFbound : ∀ u x, |F (u, x)| ≤ M)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (hFvanish : ∀ u x, 0 ≤ u → |F (u, x)| ≤ L * (u + ‖x - c‖)) :
    Tendsto (fun N : ℕ => collisionEntrance N 0
      (evenCeil ((N : ℝ) * t)) (aN N) (bN N) F) atTop
      (𝓝 (4 * (∫ u in (0 : ℝ)..t, heatKernelPairProfileIntegral u c c F))) := by
  let profile : ℝ → ℝ := fun u => heatKernelPairProfileIntegral u c c F
  let Lbar : ℝ := max L 1
  have hLbar : 0 < Lbar := by dsimp [Lbar]; positivity
  have hprofileBounds := exists_integrable_diagonal_heatProfile_shortInterval_bound
    c F L R M hL hM hFbound hFsupport hFcont
    (fun u x hu => hFvanish u x (le_of_lt hu)) ht
  obtain ⟨hprofileInt, hprofileShort⟩ := hprofileBounds
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLower : ∀ N : ℕ,
      Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
    intro N
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by linarith
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN2
  have ha : Tendsto (fun N : ℕ => latticeRepresentative N (aN N)) atTop
      (𝓝 c) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hsmall : ∀ᶠ N : ℕ in atTop,
        ‖latticeRepresentative N (aN N) - c‖ * Real.log ((N : ℝ) + 2) <
          Real.log 2 * ε := hcenterA.eventually_lt_const (mul_pos hlog2 hε)
    filter_upwards [hsmall] with N hsmall
    rw [dist_eq_norm]
    have hscaled := mul_le_mul_of_nonneg_left (hlogLower N)
      (norm_nonneg (latticeRepresentative N (aN N) - c))
    have hmul :
        Real.log 2 * ‖latticeRepresentative N (aN N) - c‖ < Real.log 2 * ε := by
      have := lt_of_le_of_lt hscaled hsmall
      simpa only [mul_comm] using this
    have hd := div_lt_div_of_pos_right hmul hlog2
    simpa [hlog2.ne'] using hd
  have hb : Tendsto (fun N : ℕ => latticeRepresentative N (bN N)) atTop
      (𝓝 c) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hsmall : ∀ᶠ N : ℕ in atTop,
        ‖latticeRepresentative N (bN N) - c‖ * Real.log ((N : ℝ) + 2) <
          Real.log 2 * ε := hcenterB.eventually_lt_const (mul_pos hlog2 hε)
    filter_upwards [hsmall] with N hsmall
    rw [dist_eq_norm]
    have hscaled := mul_le_mul_of_nonneg_left (hlogLower N)
      (norm_nonneg (latticeRepresentative N (bN N) - c))
    have hmul :
        Real.log 2 * ‖latticeRepresentative N (bN N) - c‖ < Real.log 2 * ε := by
      have := lt_of_le_of_lt hscaled hsmall
      simpa only [mul_comm] using this
    have hd := div_lt_div_of_pos_right hmul hlog2
    simpa [hlog2.ne'] using hd
  apply Metric.tendsto_atTop.mpr
  intro η hη
  let Q : ℝ := η / (180 * Lbar)
  let Mδ : ℝ := min 1 (Q ^ 2)
  let δcap : ℝ := min (t / 2) (min (1 / 2) Mδ)
  let δmax : ℝ := δcap
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hMδ : 0 < Mδ := by dsimp [Mδ]; positivity
  have hδcap : 0 < δcap := by dsimp [δcap]; positivity
  have hδmax : 0 < δmax := by simpa [δmax] using hδcap
  let εstrip : ℝ := η / 3
  have hεstrip : 0 < εstrip := by dsimp [εstrip]; positivity
  obtain ⟨δ, hδ, hδle, hstrip⟩ :=
    eventually_collisionEntrance_coalescing_short_strip_small
      aN bN c hcenterA hcenterB F L hL hFvanish δmax hδmax εstrip hεstrip
  let K : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * δ)
  let H : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  let low : ℕ → ℝ := fun N => collisionEntrance N 0 (K N) (aN N) (bN N) F
  let high : ℕ → ℝ := fun N => collisionEntrance N (K N + 1) (H N) (aN N) (bN N) F
  let tailTarget : ℝ := 4 * ∫ u in δ..t, profile u
  have hδlt : δ < t := by
    have hδcapT : δcap ≤ t / 2 := min_le_left _ _
    have hδT : δ ≤ t / 2 := hδle.trans hδcapT
    linarith
  have hδt : δ ≤ t := hδlt.le
  have hKleH : ∀ N, K N ≤ H N := by
    intro N
    dsimp [K, H]
    exact Critical2DKPZ.evenCeil_mono (mul_le_mul_of_nonneg_left hδt (Nat.cast_nonneg N))
  have hprofileIntShort : IntervalIntegrable profile volume 0 δ :=
    hprofileInt.mono_set (Set.uIcc_subset_uIcc
      Set.left_mem_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hδ.le, hδt⟩)))
  have hprofileIntTail : IntervalIntegrable profile volume δ t :=
    hprofileInt.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hδ.le, hδt⟩)) Set.right_mem_uIcc)
  have htarget :
      4 * (∫ u in (0 : ℝ)..t, profile u) =
        4 * (∫ u in (0 : ℝ)..δ, profile u) + tailTarget := by
    dsimp [tailTarget]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hprofileIntShort hprofileIntTail]
    ring
  have hhighLimit : Tendsto high atTop (𝓝 tailTarget) := by
    have h := tendsto_collisionEntrance_spatial_test_away_zero
      hδ hδlt aN bN hEvenA hEvenB c c ha hb F R M hM hFcont hFbound hFsupport
    simpa [high, K, H, tailTarget, profile] using h
  have hδleOne : δ ≤ 1 := by
    have hhalf : δ ≤ 1 / 2 :=
      (hδle.trans (min_le_right (t / 2) _)).trans (min_le_left _ _)
    linarith
  have hδsmall : δ ≤ Mδ := by
    exact (le_trans hδle (min_le_right (t / 2) _)).trans (min_le_right _ _)
  have hsqrtδ : Real.sqrt δ ≤ Q := by
    have hQnonneg : 0 ≤ Q := hQ.le
    calc
      Real.sqrt δ ≤ Real.sqrt Mδ := Real.sqrt_le_sqrt hδsmall
      _ ≤ Real.sqrt (Q ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = Q := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hQnonneg]
  have hδsqrt : δ ≤ Real.sqrt δ := by
    calc
      δ = Real.sqrt (δ ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδ.le]
      _ ≤ Real.sqrt δ := Real.sqrt_le_sqrt (by nlinarith [hδleOne])
  have hshortIntegral := hprofileShort δ hδ hδt
  have hshortTarget :
      |4 * (∫ u in (0 : ℝ)..δ, profile u)| ≤ η / 3 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      4 * |∫ u in (0 : ℝ)..δ, profile u| ≤
          4 * (5 * L * (δ + 2 * Real.sqrt δ)) :=
        mul_le_mul_of_nonneg_left hshortIntegral (by norm_num)
      _ = 20 * L * (δ + 2 * Real.sqrt δ) := by ring
      _ ≤ 60 * L * Real.sqrt δ := by nlinarith [hδsqrt, hL]
      _ ≤ 60 * Lbar * Real.sqrt δ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left L 1) (by norm_num))
          (Real.sqrt_nonneg δ)
      _ ≤ 60 * Lbar * Q := mul_le_mul_of_nonneg_left hsqrtδ (by positivity)
      _ = η / 3 := by
        dsimp [Q]
        field_simp [hLbar.ne']
        ring
  let midTarget : ℝ := 4 * (∫ u in (0 : ℝ)..δ, profile u)
  have hhighSmall : ∀ᶠ N : ℕ in atTop, dist (high N) tailTarget < η / 3 :=
    hhighLimit.eventually (Metric.ball_mem_nhds tailTarget (by positivity))
  have herrorEventually : ∀ᶠ N : ℕ in atTop,
      dist (collisionEntrance N 0 (H N) (aN N) (bN N) F)
        (4 * (∫ u in (0 : ℝ)..t, profile u)) < η := by
    filter_upwards [hstrip, hhighSmall] with N hlow hhigh
    have hsplitN : collisionEntrance N 0 (H N) (aN N) (bN N) F = low N + high N := by
      dsimp [low, high, H]
      apply collisionEntrance_split_at
      · exact Nat.zero_le _
      · exact hKleH N
    have hdecomp :
        collisionEntrance N 0 (H N) (aN N) (bN N) F -
            ((4 * (∫ u in (0 : ℝ)..δ, profile u)) + tailTarget) =
          low N + (high N - tailTarget) - midTarget := by
      rw [hsplitN]
      dsimp [midTarget]
      ring
    have hhighAbs : |high N - tailTarget| < η / 3 := by
      simpa only [Real.dist_eq] using hhigh
    have hlowAbs : |low N| < η / 3 := by
      simpa [low, K, εstrip] using hlow
    have hmidAbs : |midTarget| ≤ η / 3 := by
      simpa [midTarget] using hshortTarget
    have htriangle :
        |low N + (high N - tailTarget) - midTarget| ≤
          |low N| + |high N - tailTarget| + |midTarget| := by
      calc
        _ = |low N + ((high N - tailTarget) + (-midTarget))| := by congr 1; ring
        _ ≤ |low N| + |(high N - tailTarget) + (-midTarget)| := by
          have h := norm_add_le (low N) ((high N - tailTarget) + (-midTarget))
          simpa only [Real.norm_eq_abs] using h
        _ ≤ |low N| + (|high N - tailTarget| + |midTarget|) := by
          have h := norm_add_le (high N - tailTarget) (-midTarget)
          have h' : |(high N - tailTarget) + (-midTarget)| ≤
              |high N - tailTarget| + |midTarget| := by
            simpa only [Real.norm_eq_abs, abs_neg] using h
          exact add_le_add le_rfl h'
        _ = _ := by ac_rfl
    have herror :
        dist (collisionEntrance N 0 (H N) (aN N) (bN N) F)
            (4 * (∫ u in (0 : ℝ)..t, profile u)) < η := by
      rw [Real.dist_eq, htarget]
      rw [hdecomp]
      calc
        |low N + (high N - tailTarget) - midTarget| ≤
            |low N| + |high N - tailTarget| + |midTarget| := htriangle
        _ < η := by nlinarith [hlowAbs, hhighAbs, hmidAbs]
    simpa only [H] using herror
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp herrorEventually
  exact ⟨N₀, hN₀⟩



/-- For separated moving starting centers, the spatially tested collision entrance converges
from time zero for every bounded compactly supported continuous test. -/
theorem tendsto_collisionEntrance_spatial_test_offDiagonal_zero
    {a b : Plane} (hab : a ≠ b) {t : ℝ} (ht : 0 < t)
    (aSite bSite : ℕ → Site)
    (haSite : ∀ N, aSite N ∈ evenLattice)
    (hbSite : ∀ N, bSite N ∈ evenLattice)
    (ha : Tendsto (fun N => latticeRepresentative N (aSite N)) atTop (𝓝 a))
    (hb : Tendsto (fun N => latticeRepresentative N (bSite N)) atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R M : ℝ) (hM : 0 ≤ M)
    (hFcont : Continuous F) (hFbound : ∀ u x, |F (u, x)| ≤ M)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R) :
    Tendsto (fun N : ℕ => collisionEntrance N 0
      (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F) atTop
      (𝓝 (4 * (∫ u in (0 : ℝ)..t, heatKernelPairProfileIntegral u a b F))) := by
  let profile : ℝ → ℝ := fun u => heatKernelPairProfileIntegral u a b F
  let B : ℝ := M * (Real.pi * ‖b - a‖ ^ 2)⁻¹
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hgap : 0 < ‖b - a‖ := norm_pos_iff.mpr hab'
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprofileBound (u : ℝ) (hu : 0 < u) : ‖profile u‖ ≤ B := by
    rw [Real.norm_eq_abs]
    calc
      |profile u| ≤ M * Critical2DKPZ.heatKernel (2 * u) (b - a) := by
        simpa [profile] using
          abs_heatKernelPairProfileIntegral_le_heatKernel F M hFbound hFcont hu
      _ ≤ M * (Real.pi * ‖b - a‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (heatKernel_twoTime_le_inverse_gap_sq hab' hu) hM
  have hprofileCont : ContinuousOn profile {u : ℝ | 0 < u} := by
    exact continuousOn_heatKernelPairProfileIntegral a b F R M hM
      hFbound hFsupport hFcont
  have hprofileAES : AEStronglyMeasurable
      profile (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    rw [Set.uIoc_of_le ht.le]
    apply (hprofileCont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable
    exact measurableSet_Ioc
  have hconstInt : IntervalIntegrable (fun _ : ℝ => B) volume 0 t := by
    simp
  have hprofileInt : IntervalIntegrable profile volume 0 t := by
    apply hconstInt.mono_fun' hprofileAES
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hprofileBound u (by simpa [min_eq_left ht.le] using hu.1)
  obtain ⟨Cstrip, hCstrip, hstrip⟩ :=
    eventually_collisionEntrance_offDiagonal_short_strip_bound
      hab aSite bSite ha hb M hM
  let Astr : ℝ := (2 * M * Cstrip) / (‖b - a‖ / 2) ^ 2
  let AstrBar : ℝ := max Astr 1
  let Bbar : ℝ := max B 1
  have hAstr : 0 ≤ Astr := by dsimp [Astr]; positivity
  have hAstrBar : 0 < AstrBar := by dsimp [AstrBar]; positivity
  have hBbar : 0 < Bbar := by dsimp [Bbar]; positivity
  have hAstrLe : Astr ≤ AstrBar := le_max_left _ _
  have hBLe : B ≤ Bbar := le_max_left _ _
  apply Metric.tendsto_atTop.mpr
  intro η hη
  let δ : ℝ := min (t / 2)
    (min (η / (6 * AstrBar)) (η / (12 * Bbar)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδcapT : δ ≤ t / 2 := min_le_left _ _
  have hδlt : δ < t := by linarith
  have hδt : δ ≤ t := hδlt.le
  have hδAstr : δ ≤ η / (6 * AstrBar) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ η / (12 * Bbar) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hAstrδ : Astr * δ ≤ η / 6 := by
    calc
      Astr * δ ≤ AstrBar * δ := mul_le_mul_of_nonneg_right hAstrLe hδ.le
      _ ≤ AstrBar * (η / (6 * AstrBar)) :=
        mul_le_mul_of_nonneg_left hδAstr hAstrBar.le
      _ = η / 6 := by field_simp [hAstrBar.ne']
  have hBδ : B * δ ≤ η / 12 := by
    calc
      B * δ ≤ Bbar * δ := mul_le_mul_of_nonneg_right hBLe hδ.le
      _ ≤ Bbar * (η / (12 * Bbar)) :=
        mul_le_mul_of_nonneg_left hδB hBbar.le
      _ = η / 12 := by field_simp [hBbar.ne']
  let K : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * δ)
  let H : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  let low : ℕ → ℝ := fun N => collisionEntrance N 0 (K N) (aSite N) (bSite N) F
  let high : ℕ → ℝ := fun N => collisionEntrance N (K N + 1) (H N)
    (aSite N) (bSite N) F
  let tailTarget : ℝ := 4 * ∫ u in δ..t, profile u
  have hKleH : ∀ N, K N ≤ H N := by
    intro N
    dsimp [K, H]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hδt (Nat.cast_nonneg N))
  have hprofileIntShort : IntervalIntegrable profile volume 0 δ :=
    hprofileInt.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hδ.le, hδt⟩)))
  have hprofileIntTail : IntervalIntegrable profile volume δ t :=
    hprofileInt.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hδ.le, hδt⟩)) Set.right_mem_uIcc)
  have htarget :
      4 * (∫ u in (0 : ℝ)..t, profile u) =
        4 * (∫ u in (0 : ℝ)..δ, profile u) + tailTarget := by
    dsimp [tailTarget]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hprofileIntShort hprofileIntTail]
    ring
  have hhighLimit : Tendsto high atTop (𝓝 tailTarget) := by
    have h := tendsto_collisionEntrance_spatial_test_away_zero
      hδ hδlt aSite bSite haSite hbSite a b ha hb F R M hM
      hFcont hFbound hFsupport
    simpa [high, K, H, tailTarget, profile] using h
  have hshortIntegral :
      |∫ u in (0 : ℝ)..δ, profile u| ≤ B * δ := by
    have hconstIntShort : IntervalIntegrable (fun _ : ℝ => B) volume 0 δ :=
      hconstInt.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨hδ.le, hδt⟩)))
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le (f := profile) hδ.le
      (Filter.Eventually.of_forall fun u hu => hprofileBound u hu.1)
      hconstIntShort
    rw [Real.norm_eq_abs] at hnorm
    calc
      |∫ u in (0 : ℝ)..δ, profile u| ≤
          ∫ u in (0 : ℝ)..δ, (fun _ : ℝ => B) u := hnorm
      _ = B * δ := by simp; ring
  have hshortTarget :
      |4 * (∫ u in (0 : ℝ)..δ, profile u)| ≤ η / 3 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      4 * |∫ u in (0 : ℝ)..δ, profile u| ≤ 4 * (B * δ) :=
        mul_le_mul_of_nonneg_left hshortIntegral (by norm_num)
      _ ≤ 4 * (η / 12) := mul_le_mul_of_nonneg_left hBδ (by norm_num)
      _ = η / 3 := by ring
  have hround : ∀ᶠ N : ℕ in atTop, 3 * AstrBar / (N : ℝ) < η / 6 := by
    have hlim : Tendsto (fun N : ℕ => 3 * AstrBar / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_nat (3 * AstrBar)
    exact hlim.eventually_lt_const (by positivity)
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  have hlowSmall : ∀ᶠ N : ℕ in atTop, |low N| < η / 3 := by
    filter_upwards [hstrip F (fun p => hFbound p.1 p.2) δ hδ, hround, hNpos]
      with N hlow hroundN hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hroundLe : Astr * (3 / (N : ℝ)) ≤ 3 * AstrBar / (N : ℝ) := by
      calc
        Astr * (3 / (N : ℝ)) ≤ AstrBar * (3 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hAstrLe (by positivity)
        _ = 3 * AstrBar / (N : ℝ) := by ring
    have hlow' : |low N| ≤ Astr * (δ + 3 / (N : ℝ)) := by
      simpa [low, K, Astr] using hlow
    calc
      |low N| ≤ Astr * δ + Astr * (3 / (N : ℝ)) := by
        calc
          |low N| ≤ Astr * (δ + 3 / (N : ℝ)) := hlow'
          _ = Astr * δ + Astr * (3 / (N : ℝ)) := by ring
      _ ≤ η / 6 + 3 * AstrBar / (N : ℝ) := add_le_add hAstrδ hroundLe
      _ < η / 3 := by linarith
  let midTarget : ℝ := 4 * (∫ u in (0 : ℝ)..δ, profile u)
  have hhighSmall : ∀ᶠ N : ℕ in atTop, dist (high N) tailTarget < η / 3 :=
    hhighLimit.eventually (Metric.ball_mem_nhds tailTarget (by positivity))
  have herrorEventually : ∀ᶠ N : ℕ in atTop,
      dist (collisionEntrance N 0 (H N) (aSite N) (bSite N) F)
        (4 * (∫ u in (0 : ℝ)..t, profile u)) < η := by
    filter_upwards [hlowSmall, hhighSmall] with N hlow hhigh
    have hsplitN : collisionEntrance N 0 (H N) (aSite N) (bSite N) F =
        low N + high N := by
      dsimp [low, high, H]
      apply collisionEntrance_split_at
      · exact Nat.zero_le _
      · exact hKleH N
    have hdecomp :
        collisionEntrance N 0 (H N) (aSite N) (bSite N) F -
            ((4 * (∫ u in (0 : ℝ)..δ, profile u)) + tailTarget) =
          low N + (high N - tailTarget) - midTarget := by
      rw [hsplitN]
      dsimp [midTarget]
      ring
    have hhighAbs : |high N - tailTarget| < η / 3 := by
      simpa only [Real.dist_eq] using hhigh
    have hmidAbs : |midTarget| ≤ η / 3 := by
      simpa [midTarget] using hshortTarget
    have htriangle :
        |low N + (high N - tailTarget) - midTarget| ≤
          |low N| + |high N - tailTarget| + |midTarget| := by
      calc
        _ = |low N + ((high N - tailTarget) + (-midTarget))| := by congr 1; ring
        _ ≤ |low N| + |(high N - tailTarget) + (-midTarget)| := by
          have h := norm_add_le (low N) ((high N - tailTarget) + (-midTarget))
          simpa only [Real.norm_eq_abs] using h
        _ ≤ |low N| + (|high N - tailTarget| + |midTarget|) := by
          have h := norm_add_le (high N - tailTarget) (-midTarget)
          have h' : |(high N - tailTarget) + (-midTarget)| ≤
              |high N - tailTarget| + |midTarget| := by
            simpa only [Real.norm_eq_abs, abs_neg] using h
          exact add_le_add le_rfl h'
        _ = _ := by ac_rfl
    have herror :
        dist (collisionEntrance N 0 (H N) (aSite N) (bSite N) F)
            (4 * (∫ u in (0 : ℝ)..t, profile u)) < η := by
      rw [Real.dist_eq, htarget, hdecomp]
      calc
        |low N + (high N - tailTarget) - midTarget| ≤
            |low N| + |high N - tailTarget| + |midTarget| := htriangle
        _ < η := by nlinarith [hlow, hhighAbs, hmidAbs]
    simpa only [H] using herror
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp herrorEventually
  exact ⟨N₀, hN₀⟩

end Critical2DKPZ.SHF.Moments

end
