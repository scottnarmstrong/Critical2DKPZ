/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.LatticeReversalDiscrete
public import Critical2DKPZ.SHF.Symmetries.LatticeReversalEstimates
public import Critical2DKPZ.SHF.Symmetries.LatticeReversalRounding
public import Critical2DKPZ.SHF.Symmetries.LatticeReversalClockError
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Lattice reversal -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction CompactlySupported ENNReal Topology
open Critical2DKPZ.SHF.Moments

namespace Critical2DKPZ.SHF.Symmetries

private theorem pointToPoint_initialTwoStep_eq_sum (β : ℝ) (a n : ℕ)
    (x y : Site) (ω : Disorder) :
    pointToPoint β a (n + 2) x y ω =
      ∑ s : Fin 2 → Fin 4,
        (4 : ℝ)⁻¹ ^ 2 * Polymer.pathWeight β a x s ω *
          pointToPoint β (a + 2) n (x + walkPosition 0 s 2) y ω := by
  rw [show n + 2 = 2 + n by omega,
    Polymer.pointToPoint_chapmanKolmogorov β a 2 n x y ω]
  have htwo (z : Site) : pointToPoint β a 2 x z ω =
      ∑ s : Fin 2 → Fin 4, (4 : ℝ)⁻¹ ^ 2 * Polymer.pathWeight β a x s ω *
        if walkPosition x s 2 = z then 1 else 0 :=
    Polymer.pointToPoint_eq_sum β a 2 x z ω
  simp_rw [htwo]
  simp_rw [Finset.sum_mul]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro s hs
    let z := x + walkPosition 0 s 2
    have hendpoint (w : Site) : walkPosition x s 2 = w ↔ w = z := by
      rw [Polymer.walkPosition_eq_start_add]
      constructor
      · intro h
        dsimp [z] at h ⊢
        exact h.symm
      · rintro rfl
        simp [z]
    rw [tsum_eq_single z]
    · simp only [hendpoint, ite_true, mul_one]
      dsimp [z]
    · intro w hw
      have hne : walkPosition x s 2 ≠ w := by
        intro h
        apply hw
        dsimp [z]
        rw [Polymer.walkPosition_eq_start_add] at h
        exact h.symm
      simp [hne]
  · intro s hs
    apply summable_of_ne_finset_zero
      (s := {x + walkPosition 0 s 2})
    intro w hw
    have hne : walkPosition x s 2 ≠ w := by
      intro h
      apply hw
      rw [Polymer.walkPosition_eq_start_add] at h
      exact Finset.mem_singleton.mpr h.symm
    simp [hne]

private def pairFirstShiftTest (η : Plane) (φ : C_c(Plane × Plane, ℝ)) :
    C_c(Plane × Plane, ℝ) :=
  swapPairTest (pairSecondShiftTest η (swapPairTest φ))

private def pairFirstShift (η : Plane) : (Plane × Plane) ≃ₜ (Plane × Plane) where
  toFun p := (p.1 + η, p.2)
  invFun p := (p.1 - η, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := continuous_fst.add continuous_const |>.prodMk continuous_snd
  continuous_invFun := continuous_fst.sub continuous_const |>.prodMk continuous_snd

private theorem cellTestWeight_swapPairTest (N : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) (x y : Site) :
    cellTestWeight N (swapPairTest φ) x y = cellTestWeight N φ y x := by
  unfold cellTestWeight
  change (N / 4 : ℝ) *
      (∫ p in cell N x ×ˢ cell N y, φ p.swap) =
    (N / 4 : ℝ) * (∫ p in cell N y ×ˢ cell N x, φ p)
  rw [Measure.volume_eq_prod Plane Plane,
    MeasureTheory.setIntegral_prod_swap (μ := volume) (ν := volume)
    (s := cell N y) (t := cell N x)]

private theorem cellTestWeight_sub (N : ℕ)
    (φ ψ : C_c(Plane × Plane, ℝ)) (x y : Site) :
    cellTestWeight N (φ - ψ) x y =
      cellTestWeight N φ x y - cellTestWeight N ψ x y := by
  unfold cellTestWeight
  have hφ : IntegrableOn φ (cell N x ×ˢ cell N y) volume :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
  have hψ : IntegrableOn ψ (cell N x ×ˢ cell N y) volume :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).integrableOn
  change (N / 4 : ℝ) * (∫ p in cell N x ×ˢ cell N y, φ p - ψ p) = _
  rw [integral_sub hφ hψ]
  ring

private theorem cellTestWeight_translateFirst_even (N : ℕ) (hN : 0 < N)
    (x y d : Site) (hd : d ∈ Critical2DKPZ.evenLattice)
    (φ : C_c(Plane × Plane, ℝ)) :
    cellTestWeight N φ (x + d) y =
      cellTestWeight N (pairFirstShiftTest
        ((Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d) φ) x y := by
  let η : Plane :=
    (Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d
  rw [← cellTestWeight_swapPairTest N φ y (x + d),
    cellTestWeight_translateSecond_even N hN y x d hd (swapPairTest φ),
    ← cellTestWeight_swapPairTest N (pairSecondShiftTest η (swapPairTest φ)) x y]
  rfl

private theorem tsum_abs_cellTestWeight_le (N : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) :
    (∑' q : Site × Site, |cellTestWeight N φ q.1 q.2|) ≤
      (N / 4 : ℝ) * ∫ p, compactAbs φ p := by
  classical
  let ψ : C_c(Plane × Plane, ℝ) := compactAbs φ
  let S : Finset (Site × Site) :=
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  let Sψ : Finset (Site × Site) :=
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N ψ).toFinset
  have hsumψ : Summable (fun q : Site × Site => cellTestWeight N ψ q.1 q.2) := by
    apply summable_of_ne_finset_zero (s := Sψ)
    intro q hq
    exact cellTestWeight_eq_zero_of_not_mem N ψ q (by simpa [Sψ] using hq)
  have htotal : (∑' q : Site × Site, cellTestWeight N ψ q.1 q.2) =
      (N / 4 : ℝ) * ∫ p, ψ p := by
    calc
      _ = (N / 4 : ℝ) *
          ∑' q : Site × Site, ∫ p in cell N q.1 ×ˢ cell N q.2, ψ p := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro q
        simp [cellTestWeight]
      _ = (N / 4 : ℝ) * ∫ p, ψ p := by
        congr 1
        have h := Critical2DKPZ.SHF.Flow.integral_latticePairing_eq_cellTsum N ψ
          (fun _ _ : Site => (1 : ℝ))
        simpa using h.symm
  have hfinite : (∑ q ∈ S, |cellTestWeight N φ q.1 q.2|) ≤
      ∑ q ∈ S, cellTestWeight N ψ q.1 q.2 := by
    apply Finset.sum_le_sum
    intro q hq
    exact abs_cellTestWeight_le_abs_test N φ q.1 q.2
  have hsum_eq : (∑' q : Site × Site, |cellTestWeight N φ q.1 q.2|) =
      ∑ q ∈ S, |cellTestWeight N φ q.1 q.2| := by
    rw [tsum_eq_sum (s := S)]
    intro q hq
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  rw [hsum_eq]
  calc
    _ ≤ ∑ q ∈ S, cellTestWeight N ψ q.1 q.2 := hfinite
    _ ≤ ∑' q : Site × Site, cellTestWeight N ψ q.1 q.2 := by
      apply hsumψ.sum_le_tsum S
      intro q hq
      unfold cellTestWeight
      apply mul_nonneg (by positivity)
      apply integral_nonneg
      intro p
      dsimp [ψ, compactAbs]
      exact abs_nonneg _
    _ = (N / 4 : ℝ) * ∫ p, compactAbs φ p := by
      rw [htotal]

/-- The uniform scaled walk-kernel mass constant for a fixed macroscopic gap. -/
noncomputable def shiftedKernelMassConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  Classical.choose (Critical2DKPZ.SHF.Moments.scaled_srwKernel_bound hε)

/-- Positivity and the uniform pointwise bound for `shiftedKernelMassConstant`. -/
theorem shiftedKernelMassConstant_spec (ε : ℝ) (hε : 0 < ε) :
    0 < shiftedKernelMassConstant ε hε ∧
      ∀ N n : ℕ, ε * N ≤ n → ∀ z : Site,
        ((N : ℝ) / 4) * srwKernel n z ≤ shiftedKernelMassConstant ε hε :=
  Classical.choose_spec (Critical2DKPZ.SHF.Moments.scaled_srwKernel_bound hε)

private theorem tsum_shiftedCellKernel_le (ε : ℝ) (hε : 0 < ε)
    (N n : ℕ) (hN : 0 < N) (hgap : ε * N ≤ n) (d : Site)
    (φ : C_c(Plane × Plane, ℝ)) :
    (∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| *
      srwKernel n (q.2 - q.1 - d)) ≤ shiftedKernelMassConstant ε hε *
        ∫ p, compactAbs φ p := by
  let C := shiftedKernelMassConstant ε hε
  have hC : 0 < C := (shiftedKernelMassConstant_spec ε hε).1
  have hscaled := (shiftedKernelMassConstant_spec ε hε).2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkernel (z : Site) : srwKernel n z ≤ (4 * C) / N := by
    rw [le_div_iff₀ hNr]
    have h := hscaled N n hgap z
    nlinarith [h]
  have hsupport :
      (∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| *
        srwKernel n (q.2 - q.1 - d)) =
      ∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset,
        |cellTestWeight N φ q.1 q.2| * srwKernel n (q.2 - q.1 - d) := by
    rw [tsum_eq_sum (s :=
      (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset)]
    intro q hq
    rw [cellTestWeight_eq_zero_of_not_mem N φ q hq]
    simp
  rw [hsupport]
  calc
    _ ≤ (4 * C / N) *
        ∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset,
          |cellTestWeight N φ q.1 q.2| := by
      calc
        _ ≤ ∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset,
            |cellTestWeight N φ q.1 q.2| * (4 * C / N) := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_left (hkernel _) (abs_nonneg _)
        _ = ∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset,
            (4 * C / N) * |cellTestWeight N φ q.1 q.2| := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = (4 * C / N) *
            ∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset,
              |cellTestWeight N φ q.1 q.2| := by rw [Finset.mul_sum]
    _ ≤ (4 * C / N) * ((N / 4 : ℝ) * ∫ p, compactAbs φ p) := by
      have h := tsum_abs_cellTestWeight_le N φ
      have hsummable : Summable (fun q : Site × Site =>
          |cellTestWeight N φ q.1 q.2|) := by
        apply summable_of_ne_finset_zero (s :=
          (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset)
        intro q hq
        rw [cellTestWeight_eq_zero_of_not_mem N φ q hq]
        simp
      have hfinite :
          (∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset,
            |cellTestWeight N φ q.1 q.2|) ≤
            ∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| :=
        hsummable.sum_le_tsum _ (fun q hq => abs_nonneg _)
      calc
        _ ≤ (4 * C / N) * ∑' q : Site × Site,
            |cellTestWeight N φ q.1 q.2| :=
          mul_le_mul_of_nonneg_left hfinite (by positivity)
        _ ≤ (4 * C / N) * ((N / 4 : ℝ) * ∫ p, compactAbs φ p) :=
          mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * ∫ p, compactAbs φ p := by
      field_simp [ne_of_gt hNr]

/-- Translating the second coordinate of a compact test is continuous in spatial `L¹`. -/
theorem tendsto_pairSecondShiftTest_L1 (φ : C_c(Plane × Plane, ℝ))
    (d : Site) :
    Tendsto (fun N : ℕ => ∫ p,
      |pairSecondShiftTest
        ((Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d) φ p - φ p|)
      atTop (𝓝 0) := by
  let η : ℕ → Plane := fun N =>
    (Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d
  have hscale : Tendsto (fun N : ℕ => (Real.sqrt ((N : ℝ) / 2))⁻¹)
      atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num))
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa only [η, zero_smul] using hscale.smul_const (Critical2DKPZ.siteToPlane d)
  have hSupportBounded : Bornology.IsBounded (tsupport φ) :=
    φ.hasCompactSupport.isBounded
  obtain ⟨r, hr⟩ := hSupportBounded.subset_closedBall (0 : Plane × Plane)
  let R : ℝ := max r 0
  have hR : tsupport φ ⊆ Metric.closedBall (0 : Plane × Plane) R := by
    exact Set.Subset.trans hr (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let K : Set (Plane × Plane) := Metric.closedBall 0 (R + 1)
  have hKcompact : IsCompact K := by
    exact isCompact_closedBall _ _
  have hKfinite : volume K ≠ ∞ := by
    exact hKcompact.measure_ne_top
  let φb : Plane × Plane →ᵇ ℝ :=
    ofCompactSupport φ φ.continuous φ.hasCompactSupport
  let M : ℝ := ‖φb‖
  have hφbound (p : Plane × Plane) : |φ p| ≤ M := by
    change |φb p| ≤ M
    simpa [M, Real.norm_eq_abs] using
      BoundedContinuousFunction.norm_coe_le_norm φb p
  let B : Plane × Plane → ℝ := K.indicator (fun _ => 2 * M)
  have hBint : Integrable B volume := by
    exact IntegrableOn.integrable_indicator
      (integrableOn_const hKfinite) (Metric.isClosed_closedBall.measurableSet)
  let F : ℕ → Plane × Plane → ℝ := fun N p =>
    |pairSecondShiftTest (η N) φ p - φ p|
  have hFmeas (N : ℕ) : AEStronglyMeasurable (F N) volume := by
    have hcont : Continuous (F N) := by
      exact (pairSecondShiftTest (η N) φ).continuous.sub φ.continuous |>.abs
    exact hcont.aestronglyMeasurable
  have hsmall : ∀ᶠ N : ℕ in atTop, ‖η N‖ ≤ 1 := by
    filter_upwards [hη.norm.eventually
      (Iio_mem_nhds (by norm_num : ‖(0 : Plane)‖ < 1))]
      with N hN
    simpa using hN.le
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ᵐ p ∂volume, ‖F N p‖ ≤ B p := by
    filter_upwards [hsmall] with N hN
    refine Filter.Eventually.of_forall fun p => ?_
    by_cases hpK : p ∈ K
    · simp only [F, B, Set.indicator_of_mem hpK, Real.norm_eq_abs, abs_abs]
      have hφshiftBound : |pairSecondShiftTest (η N) φ p| ≤ M := by
        simpa [pairSecondShiftTest] using hφbound (pairSecondShift (η N) p)
      calc
        |pairSecondShiftTest (η N) φ p - φ p| ≤
            |pairSecondShiftTest (η N) φ p| + |φ p| := abs_sub _ _
        _ ≤ M + M := add_le_add
          hφshiftBound (hφbound p)
        _ = 2 * M := by ring
    · have hφzero (q : Plane × Plane) (hq : q ∉ tsupport φ) : φ q = 0 := by
        by_contra hne
        apply hq
        exact subset_tsupport φ (by simpa only [Function.mem_support] using hne)
      have hpzero : φ p = 0 := by
        apply hφzero p
        intro hp
        have hpR : dist p 0 ≤ R := (hR hp)
        have hpIn : p ∈ K := by
          change dist p 0 ≤ R + 1
          exact hpR.trans (by linarith)
        exact hpK hpIn
      have hshiftzero : φ (pairSecondShift (η N) p) = 0 := by
        apply hφzero (pairSecondShift (η N) p)
        intro hshift
        have hqR : dist (pairSecondShift (η N) p) 0 ≤ R := (hR hshift)
        have hdist : dist p (pairSecondShift (η N) p) = ‖η N‖ := by
          simp [pairSecondShift, dist_eq_norm, Prod.norm_def]
        have hpR : dist p 0 ≤ R + 1 := calc
          dist p 0 ≤ dist p (pairSecondShift (η N) p) +
              dist (pairSecondShift (η N) p) 0 := dist_triangle _ _ _
          _ ≤ 1 + R := add_le_add (hdist ▸ hN) hqR
          _ = R + 1 := by ring
        have hpIn : p ∈ K := by
          change dist p 0 ≤ R + 1
          exact hpR
        exact hpK hpIn
      simp [F, B, pairSecondShiftTest, hpK, hpzero, hshiftzero]
  have hpoint (p : Plane × Plane) : Tendsto (fun N => F N p) atTop (𝓝 0) := by
    have hshift : Tendsto (fun N : ℕ => pairSecondShift (η N) p) atTop (𝓝 p) := by
      change Tendsto (fun N : ℕ => (p.1, p.2 + η N)) atTop (𝓝 p)
      have hcont : Continuous (fun e : Plane => (p.1, p.2 + e)) := by fun_prop
      have hcont' := hcont.continuousAt.tendsto.comp hη
      simpa only [Function.comp_def, add_zero] using hcont'
    have hφshift : Tendsto (fun N : ℕ => φ (pairSecondShift (η N) p))
        atTop (𝓝 (φ p)) := φ.continuous.continuousAt.tendsto.comp hshift
    have hdiff : Tendsto (fun N : ℕ =>
        φ (pairSecondShift (η N) p) - φ p) atTop (𝓝 0) := by
      simpa using hφshift.sub_const (φ p)
    change Tendsto (fun N => |φ (pairSecondShift (η N) p) - φ p|) atTop (𝓝 0)
    simpa only [Function.comp_def, abs_zero] using
      (continuous_abs.continuousAt.tendsto.comp hdiff)
  have hlim : Tendsto (fun N : ℕ => ∫ p, F N p ∂volume) atTop (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence B
      (Filter.Eventually.of_forall hFmeas) hbound hBint
      (Filter.Eventually.of_forall hpoint)
  simpa only [F] using hlim

private theorem tendsto_pairFirstShiftTest_L1 (φ : C_c(Plane × Plane, ℝ))
    (d : Site) :
    Tendsto (fun N : ℕ => ∫ p,
      |pairFirstShiftTest
        ((Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d) φ p - φ p|)
      atTop (𝓝 0) := by
  let η : ℕ → Plane := fun N =>
    (Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d
  have hswap (N : ℕ) :
      (∫ p, |pairFirstShiftTest (η N) φ p - φ p|) =
        ∫ p, |pairSecondShiftTest (η N) (swapPairTest φ) p -
          swapPairTest φ p| := by
    let g : Plane × Plane → ℝ := fun p =>
      |pairSecondShiftTest (η N) (swapPairTest φ) p - swapPairTest φ p|
    have hpoint (p : Plane × Plane) :
        |pairFirstShiftTest (η N) φ p - φ p| = g p.swap := by
      change |φ (p.1 + η N, p.2) - φ p| =
        |φ (p.1 + η N, p.2) - φ p|
      rfl
    rw [Measure.volume_eq_prod Plane Plane]
    calc
      (∫ p, |pairFirstShiftTest (η N) φ p - φ p| ∂volume) =
          ∫ p, g p.swap ∂(volume.prod volume) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
      _ = ∫ p, g p ∂(volume.prod volume) :=
        integral_prod_swap g
      _ = ∫ p, |pairSecondShiftTest (η N) (swapPairTest φ) p -
            swapPairTest φ p| ∂volume := by rfl
  have hsecond := tendsto_pairSecondShiftTest_L1 (swapPairTest φ) d
  refine Tendsto.congr' ?_ hsecond
  filter_upwards [] with N
  simpa only [η] using (hswap N).symm

private theorem integral_compactAbs_pairFirstShiftTest_eq
    (η : Plane) (φ : C_c(Plane × Plane, ℝ)) :
    (∫ p, compactAbs (pairFirstShiftTest η φ) p) =
      ∫ p, compactAbs φ p := by
  have hmp : MeasurePreserving (pairFirstShift η)
      (volume : Measure (Plane × Plane)) volume := by
    rw [Measure.volume_eq_prod Plane Plane]
    exact (measurePreserving_add_right volume η).prod (MeasurePreserving.id volume)
  calc
    (∫ p, compactAbs (pairFirstShiftTest η φ) p) =
        ∫ p, compactAbs φ (pairFirstShift η p) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => by rfl
    _ = ∫ p, compactAbs φ p := by
      exact hmp.integral_comp' (f := (pairFirstShift η).toMeasurableEquiv)
        (fun p => compactAbs φ p)

/-- A compactly supported lattice point-to-point pairing is integrable in the disorder. -/
theorem integrable_pairing_latticeClock_of_test
    (ϑ : ℝ) {N a b : ℕ}
    (φ : C_c(Plane × Plane, ℝ)) :
    Integrable (fun ω => ∫ p, φ p *
      rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) disorderLaw := by
  have hprod : Integrable (fun q : (Plane × Plane) × Disorder =>
      φ q.1 * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) q.1 q.2)
      (volume.prod disorderLaw) :=
    Critical2DKPZ.SHF.Moments.integrable_pairing_rescaledP2P
      ϑ N ((a : ℝ) / N) ((b : ℝ) / N) φ.continuous φ.hasCompactSupport
  have hswap := hprod.swap
  have hI : Integrable (fun ω : Disorder => ∫ p : Plane × Plane,
      φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω ∂volume)
      disorderLaw := by
    simpa only [Function.comp_apply, Prod.swap_prod_mk, Prod.fst, Prod.snd] using
      hswap.integral_prod_left
  exact hI

private theorem integral_abs_pairing_latticeClock_le_of
    (ϑ : ℝ) {N a b : ℕ} (hN : 0 < N) (ha : Even a) (hb : Even b)
    (φ : C_c(Plane × Plane, ℝ)) (C : ℝ)
    (hkernel : (∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| *
        srwKernel (b - a) (q.2 - q.1)) ≤ C) :
    ∫ ω, |∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω| ∂disorderLaw ≤ C := by
  classical
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  let F : Site × Site → Disorder → ℝ := fun q ω =>
    cellTestWeight N φ q.1 q.2 * pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω
  have hpairSum (ω : Disorder) :
      (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) =
        ∑ q ∈ S, F q ω := by
    rw [pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hb φ ω]
    change (∑' q : Site × Site, F q ω) = ∑ q ∈ S, F q ω
    rw [tsum_eq_sum (s := S)]
    intro q hq
    change cellTestWeight N φ q.1 q.2 *
        pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω = 0
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  have hF (q : Site × Site) : Integrable (F q) disorderLaw := by
    exact (Polymer.integrable_pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2).const_mul _
  have hleft : Integrable (fun ω =>
      |∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω|) disorderLaw := by
    simpa only [Real.norm_eq_abs] using (integrable_pairing_latticeClock_of_test ϑ φ).norm
  have hright : Integrable (fun ω => ∑ q ∈ S, |F q ω|) disorderLaw := by
    exact integrable_finsetSum _ fun q hq => (hF q).norm
  have hpoint (ω : Disorder) :
      |∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω| ≤
        ∑ q ∈ S, |F q ω| := by
    rw [hpairSum ω]
    exact Finset.abs_sum_le_sum_abs _ _
  have hInt := integral_mono hleft hright hpoint
  have hsum : (∫ ω, ∑ q ∈ S, |F q ω| ∂disorderLaw) =
      ∑ q ∈ S, |cellTestWeight N φ q.1 q.2| * srwKernel (b - a) (q.2 - q.1) := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      calc
        (∫ ω, |F q ω| ∂disorderLaw) =
            |cellTestWeight N φ q.1 q.2| *
              ∫ ω, pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω ∂disorderLaw := by
          rw [show (fun ω => |F q ω|) = fun ω =>
              |cellTestWeight N φ q.1 q.2| *
                pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω by
                funext ω
                simp [F, abs_mul, abs_of_nonneg (Polymer.pointToPoint_nonneg _ _ _ _ _ _)] ,
            integral_const_mul]
        _ = _ := by rw [Polymer.integral_pointToPoint]
    · intro q hq
      exact (hF q).norm
  have hsumNonneg : Summable (fun q : Site × Site =>
      |cellTestWeight N φ q.1 q.2| * srwKernel (b - a) (q.2 - q.1)) := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  have hfinite_le :
      (∑ q ∈ S, |cellTestWeight N φ q.1 q.2| * srwKernel (b - a) (q.2 - q.1)) ≤
        ∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| * srwKernel (b - a) (q.2 - q.1) :=
    hsumNonneg.sum_le_tsum S (fun q hq => mul_nonneg (abs_nonneg _) (srwKernel_nonneg _ _))
  exact hInt.trans (hsum ▸ hfinite_le.trans hkernel)

private theorem walkPosition_two_mem_evenLattice (s : Fin 2 → Fin 4) :
    walkPosition 0 s 2 ∈ Critical2DKPZ.evenLattice := by
  change Even ((walkPosition 0 s 2) 0 + (walkPosition 0 s 2) 1)
  have hmod := Polymer.walkPosition_parity (0 : Site) s
  change ((walkPosition 0 s 2) 0 + (walkPosition 0 s 2) 1) % 2 =
    (0 + 0 + (2 : ℕ)) % 2 at hmod
  have heven : Even ((0 : ℤ) + 0 + 2) := by norm_num
  apply Int.even_iff.mpr
  rw [hmod]
  exact Int.even_iff.mp heven

private theorem neg_walkPosition_two_mem_evenLattice (s : Fin 2 → Fin 4) :
    -walkPosition 0 s 2 ∈ Critical2DKPZ.evenLattice := by
  change Even ((-walkPosition 0 s 2) 0 + (-walkPosition 0 s 2) 1)
  have h := walkPosition_two_mem_evenLattice s
  change Even ((walkPosition 0 s 2) 0 + (walkPosition 0 s 2) 1) at h
  simpa [add_comm] using h.neg

private theorem tsum_initialPath_reindex (ϑ : ℝ) (N a n : ℕ) (hN : 0 < N)
    (φ : C_c(Plane × Plane, ℝ)) (s : Fin 2 → Fin 4) (ω : Disorder) :
    (∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
      ((4 : ℝ)⁻¹ ^ 2 * Polymer.pathWeight (criticalBeta ϑ N) a q.1 s ω *
        pointToPoint (criticalBeta ϑ N) (a + 2) n
          (q.1 + walkPosition 0 s 2) q.2 ω)) =
      (4 : ℝ)⁻¹ ^ 2 * (∑' q : Site × Site,
        cellTestWeight N (pairFirstShiftTest
          ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
            Critical2DKPZ.siteToPlane (-walkPosition 0 s 2)) φ) q.1 q.2 *
          Polymer.pathWeight (criticalBeta ϑ N) a
            (q.1 - walkPosition 0 s 2) s ω *
          pointToPoint (criticalBeta ϑ N) (a + 2) n q.1 q.2 ω) := by
  let d := walkPosition 0 s 2
  let ψ := pairFirstShiftTest
    ((Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane (-d)) φ
  let E : (Site × Site) ≃ (Site × Site) :=
    Equiv.prodCongr (Equiv.addRight d) (Equiv.refl Site)
  let F : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2 *
    Polymer.pathWeight (criticalBeta ϑ N) a q.1 s ω *
      pointToPoint (criticalBeta ϑ N) (a + 2) n (q.1 + d) q.2 ω
  calc
    _ = ∑' q : Site × Site, (4 : ℝ)⁻¹ ^ 2 * F q := by
      apply tsum_congr
      intro q
      dsimp [F]
      ring
    _ = (4 : ℝ)⁻¹ ^ 2 * ∑' q : Site × Site, F q := by
      rw [tsum_mul_left]
    _ = (4 : ℝ)⁻¹ ^ 2 * ∑' q : Site × Site, F (E.symm q) := by
      congr 1
      exact (E.symm.tsum_eq F).symm
    _ = _ := by
      congr 1
      apply tsum_congr
      intro q
      have hE : E.symm q = (q.1 - d, q.2) := by
        ext <;> simp [E, sub_eq_add_neg]
      have htrans := cellTestWeight_translateFirst_even N hN
        (q.1) q.2 (-d) (neg_walkPosition_two_mem_evenLattice s) φ
      rw [hE]
      dsimp [F]
      have hcoord : q.1 - d = q.1 + -d := by abel
      rw [hcoord]
      rw [htrans]
      have hadd : q.1 + -d + d = q.1 := by abel
      rw [hadd]

private theorem pairing_latticeClock_startTwoStep_eq (ϑ : ℝ) {N a n : ℕ}
    (hN : 0 < N) (ha : Even a) (hab : Even (a + n + 2))
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
      (((a + n + 2 : ℕ) : ℝ) / N) p ω) =
      ∑ s : Fin 2 → Fin 4, (4 : ℝ)⁻¹ ^ 2 *
        (∑' q : Site × Site,
          cellTestWeight N (pairFirstShiftTest
            ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
              Critical2DKPZ.siteToPlane (-walkPosition 0 s 2)) φ) q.1 q.2 *
            Polymer.pathWeight (criticalBeta ϑ N) a
              (q.1 - walkPosition 0 s 2) s ω *
            pointToPoint (criticalBeta ϑ N) (a + 2) n q.1 q.2 ω) := by
  classical
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  have htermSummable (s : Fin 2 → Fin 4) : Summable (fun q : Site × Site =>
      cellTestWeight N φ q.1 q.2 * ((4 : ℝ)⁻¹ ^ 2 *
        Polymer.pathWeight (criticalBeta ϑ N) a q.1 s ω *
        pointToPoint (criticalBeta ϑ N) (a + 2) n
          (q.1 + walkPosition 0 s 2) q.2 ω)) := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  rw [pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hab φ ω]
  have hdur : (a + n + 2) - a = n + 2 := by omega
  calc
    _ = ∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        pointToPoint (criticalBeta ϑ N) a (n + 2) q.1 q.2 ω := by
      apply tsum_congr
      intro q
      simp only [hdur]
    _ = ∑' q : Site × Site, ∑ s : Fin 2 → Fin 4,
        cellTestWeight N φ q.1 q.2 * ((4 : ℝ)⁻¹ ^ 2 *
          Polymer.pathWeight (criticalBeta ϑ N) a q.1 s ω *
          pointToPoint (criticalBeta ϑ N) (a + 2) n
            (q.1 + walkPosition 0 s 2) q.2 ω) := by
      apply tsum_congr
      intro q
      rw [pointToPoint_initialTwoStep_eq_sum
        (criticalBeta ϑ N) a n q.1 q.2 ω]
      rw [Finset.mul_sum]
    _ = ∑ s : Fin 2 → Fin 4, ∑' q : Site × Site,
        cellTestWeight N φ q.1 q.2 * ((4 : ℝ)⁻¹ ^ 2 *
          Polymer.pathWeight (criticalBeta ϑ N) a q.1 s ω *
          pointToPoint (criticalBeta ϑ N) (a + 2) n
            (q.1 + walkPosition 0 s 2) q.2 ω) := by
      exact Summable.tsum_finsetSum (s := Finset.univ)
        (fun s hs => htermSummable s)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      exact tsum_initialPath_reindex ϑ N a n hN φ s ω

private theorem tsum_terminalPath_reindex (ϑ : ℝ) {N a n : ℕ}
    (hN : 0 < N) (φ : C_c(Plane × Plane, ℝ)) (s : Fin 2 → Fin 4)
    (ω : Disorder) :
    (∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
      (pointToPoint (criticalBeta ϑ N) a n q.1
        (q.2 - walkPosition 0 s 2) ω *
        Polymer.pathWeight (criticalBeta ϑ N) (a + n)
          (q.2 - walkPosition 0 s 2) s ω)) =
      (∑' q : Site × Site,
        cellTestWeight N (pairSecondShiftTest
          ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
            Critical2DKPZ.siteToPlane (walkPosition 0 s 2)) φ) q.1 q.2 *
          pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω *
          Polymer.pathWeight (criticalBeta ϑ N) (a + n) q.2 s ω) := by
  let d := walkPosition 0 s 2
  let ψ := pairSecondShiftTest
    ((Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d) φ
  let E : (Site × Site) ≃ (Site × Site) :=
    Equiv.prodCongr (Equiv.refl Site) (Equiv.addRight (-d))
  let F : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2 *
    (pointToPoint (criticalBeta ϑ N) a n q.1 (q.2 - d) ω *
      Polymer.pathWeight (criticalBeta ϑ N) (a + n) (q.2 - d) s ω)
  calc
    _ = ∑' q : Site × Site, F q := by
      apply tsum_congr
      intro q
      rfl
    _ = ∑' q : Site × Site, F (E.symm q) := by
      exact (E.symm.tsum_eq F).symm
    _ = _ := by
      apply tsum_congr
      intro q
      have hE : E.symm q = (q.1, q.2 + d) := by
        ext <;> simp [E]
      have htrans := cellTestWeight_translateSecond_even N hN q.1 q.2 d
        (walkPosition_two_mem_evenLattice s) φ
      rw [hE]
      dsimp [F, ψ, d]
      rw [htrans]
      simp only [add_sub_cancel_right]
      ring

/-- Expand a two-step extension at the terminal endpoint into its finitely many final paths. -/
theorem pairing_latticeClock_terminalTwoStep_eq (ϑ : ℝ) {N a n : ℕ}
    (hN : 0 < N) (ha : Even a) (hn : Even (a + n + 2))
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
      (((a + n + 2 : ℕ) : ℝ) / N) p ω) =
      ∑ s : Fin 2 → Fin 4, (4 : ℝ)⁻¹ ^ 2 *
        (∑' q : Site × Site,
          cellTestWeight N (pairSecondShiftTest
            ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
              Critical2DKPZ.siteToPlane (walkPosition 0 s 2)) φ) q.1 q.2 *
          pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω *
          Polymer.pathWeight (criticalBeta ϑ N) (a + n) q.2 s ω) := by
  classical
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  have htermSummable (s : Fin 2 → Fin 4) : Summable (fun q : Site × Site =>
      cellTestWeight N φ q.1 q.2 * ((4 : ℝ)⁻¹ ^ 2 *
        pointToPoint (criticalBeta ϑ N) a n q.1
          (q.2 - walkPosition 0 s 2) ω *
        Polymer.pathWeight (criticalBeta ϑ N) (a + n)
          (q.2 - walkPosition 0 s 2) s ω)) := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  rw [pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hn φ ω]
  have hduration : (a + n + 2) - a = n + 2 := by omega
  calc
    _ = ∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        pointToPoint (criticalBeta ϑ N) a (n + 2) q.1 q.2 ω := by
      apply tsum_congr
      intro q
      simp only [hduration]
    _ = ∑' q : Site × Site, ∑ s : Fin 2 → Fin 4,
        cellTestWeight N φ q.1 q.2 * ((4 : ℝ)⁻¹ ^ 2 *
          pointToPoint (criticalBeta ϑ N) a n q.1
            (q.2 - walkPosition 0 s 2) ω *
          Polymer.pathWeight (criticalBeta ϑ N) (a + n)
            (q.2 - walkPosition 0 s 2) s ω) := by
      apply tsum_congr
      intro q
      rw [pointToPoint_terminalTwoStep_eq_sum
        (criticalBeta ϑ N) a n q.1 q.2 ω]
      rw [Finset.mul_sum]
    _ = ∑ s : Fin 2 → Fin 4, ∑' q : Site × Site,
        cellTestWeight N φ q.1 q.2 * ((4 : ℝ)⁻¹ ^ 2 *
          pointToPoint (criticalBeta ϑ N) a n q.1
            (q.2 - walkPosition 0 s 2) ω *
          Polymer.pathWeight (criticalBeta ϑ N) (a + n)
            (q.2 - walkPosition 0 s 2) s ω) := by
      exact Summable.tsum_finsetSum (s := Finset.univ)
        (fun s hs => htermSummable s)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      calc
        _ = ∑' q : Site × Site, (4 : ℝ)⁻¹ ^ 2 *
            (cellTestWeight N φ q.1 q.2 *
              (pointToPoint (criticalBeta ϑ N) a n q.1
                (q.2 - walkPosition 0 s 2) ω *
              Polymer.pathWeight (criticalBeta ϑ N) (a + n)
                (q.2 - walkPosition 0 s 2) s ω)) := by
          apply tsum_congr
          intro q
          ring
        _ = (4 : ℝ)⁻¹ ^ 2 *
            (∑' q : Site × Site,
              cellTestWeight N φ q.1 q.2 *
                (pointToPoint (criticalBeta ϑ N) a n q.1
                  (q.2 - walkPosition 0 s 2) ω *
                Polymer.pathWeight (criticalBeta ϑ N) (a + n)
                  (q.2 - walkPosition 0 s 2) s ω)) := by
          rw [tsum_mul_left]
        _ = (4 : ℝ)⁻¹ ^ 2 *
            (∑' q : Site × Site,
              cellTestWeight N (pairSecondShiftTest
                ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
                  Critical2DKPZ.siteToPlane (walkPosition 0 s 2)) φ) q.1 q.2 *
                pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω *
                Polymer.pathWeight (criticalBeta ϑ N) (a + n) q.2 s ω) := by
          congr 1
          exact tsum_terminalPath_reindex ϑ hN φ s ω

/-- The integral bound for the short-path error; integrability is provided by `integrable_pathWeightError_tsum`. -/
theorem integral_abs_pathWeightError_tsum_le (ϑ ε : ℝ) (hε : 0 < ε)
    (N u a n : ℕ) (hN : 0 < N) (hgap : ε * N ≤ n)
    (s : Fin 2 → Fin 4) (pathStart : Site × Site → Site)
    (hdisj : u + 2 ≤ a ∨ a + n ≤ u) (φ : C_c(Plane × Plane, ℝ)) :
    ∫ ω, |∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
      ((Polymer.pathWeight (criticalBeta ϑ N) u (pathStart q) s ω - 1) *
        pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω)| ∂disorderLaw ≤
      Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1) *
        (shiftedKernelMassConstant ε hε * ∫ p, compactAbs φ p) := by
  classical
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  let β := criticalBeta ϑ N
  let F : Site × Site → Disorder → ℝ := fun q ω =>
    cellTestWeight N φ q.1 q.2 *
      ((Polymer.pathWeight β u (pathStart q) s ω - 1) *
        pointToPoint β a n q.1 q.2 ω)
  have hpairSum (ω : Disorder) :
      (∑' q : Site × Site, F q ω) = ∑ q ∈ S, F q ω := by
    rw [tsum_eq_sum (s := S)]
    intro q hq
    dsimp [F]
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  have hFabs (q : Site × Site) : Integrable (fun ω => |F q ω|) disorderLaw := by
    have hbase := integrable_abs_pathWeightError_mul_pointToPoint β u s
      a n (pathStart q) q.1 q.2 hdisj
    have hEq (ω : Disorder) : |F q ω| =
        |cellTestWeight N φ q.1 q.2| *
          (|Polymer.pathWeight β u (pathStart q) s ω - 1| *
            pointToPoint β a n q.1 q.2 ω) := by
      simp [F, abs_mul, abs_of_nonneg
        (Polymer.pointToPoint_nonneg β a n q.1 q.2 ω)]
    exact (hbase.const_mul _).congr
      (Filter.Eventually.of_forall fun ω => (hEq ω).symm)
  have hFintegrable (q : Site × Site) : Integrable (F q) disorderLaw := by
    have hnorm := (hFabs q)
    have hAEM : AEStronglyMeasurable (F q) disorderLaw := by
      have hmeas : Measurable (fun ω =>
          cellTestWeight N φ q.1 q.2 *
            (Polymer.pathWeight β u (pathStart q) s ω - 1) *
              pointToPoint β a n q.1 q.2 ω) :=
        (measurable_const.mul
          ((Polymer.measurable_pathWeight β u (pathStart q) s).sub measurable_const)).mul
            (Polymer.measurable_pointToPoint β a n q.1 q.2)
      simpa only [F, mul_assoc] using hmeas.aestronglyMeasurable
    have hnormEq : (fun ω => ‖F q ω‖) = fun ω => |F q ω| := by
      funext ω
      exact Real.norm_eq_abs _
    exact (integrable_norm_iff hAEM).mp (hnormEq ▸ hnorm)
  have hsumInt : Integrable (fun ω => ∑ q ∈ S, F q ω) disorderLaw :=
    integrable_finsetSum _ fun q hq => hFintegrable q
  have hleft : Integrable (fun ω => |∑' q : Site × Site, F q ω|) disorderLaw := by
    have h := hsumInt.norm
    have hEq (ω : Disorder) :
        ‖∑ q ∈ S, F q ω‖ = |∑' q : Site × Site, F q ω| := by
      rw [Real.norm_eq_abs, ← hpairSum ω]
    simpa only [Real.norm_eq_abs] using
      h.congr (Filter.Eventually.of_forall hEq)
  have hright : Integrable (fun ω => ∑ q ∈ S, |F q ω|) disorderLaw :=
    integrable_finsetSum _ fun q hq => hFabs q
  have hpoint (ω : Disorder) : |∑' q : Site × Site, F q ω| ≤
      ∑ q ∈ S, |F q ω| := by
    rw [hpairSum ω]
    exact Finset.abs_sum_le_sum_abs _ _
  have hInt := integral_mono hleft hright hpoint
  have hsum : (∫ ω, ∑ q ∈ S, |F q ω| ∂disorderLaw) =
      ∑ q ∈ S, |cellTestWeight N φ q.1 q.2| *
        ((∫ ω, |Polymer.pathWeight β u (pathStart q) s ω - 1| ∂disorderLaw) *
          srwKernel n (q.2 - q.1)) := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      have hEq (ω : Disorder) : |F q ω| =
          |cellTestWeight N φ q.1 q.2| *
            (|Polymer.pathWeight β u (pathStart q) s ω - 1| *
              pointToPoint β a n q.1 q.2 ω) := by
        simp [F, abs_mul, abs_of_nonneg
          (Polymer.pointToPoint_nonneg β a n q.1 q.2 ω)]
      rw [show (fun ω => |F q ω|) = fun ω =>
          |cellTestWeight N φ q.1 q.2| *
            (|Polymer.pathWeight β u (pathStart q) s ω - 1| *
              pointToPoint β a n q.1 q.2 ω) by funext ω; exact hEq ω,
        integral_const_mul,
        integral_abs_pathWeightError_mul_pointToPoint_eq β u s a n
          (pathStart q) q.1 q.2 hdisj]
    · intro q hq
      exact hFabs q
  have hmass := tsum_shiftedCellKernel_le ε hε N n hN hgap 0 φ
  have hmass' : (∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| *
      srwKernel n (q.2 - q.1)) ≤
        shiftedKernelMassConstant ε hε * ∫ p, compactAbs φ p := by
    simpa only [sub_zero] using hmass
  have hsumKernel : Summable (fun q : Site × Site =>
      |cellTestWeight N φ q.1 q.2| * srwKernel n (q.2 - q.1)) := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  have hfinite : (∑ q ∈ S, |cellTestWeight N φ q.1 q.2| *
      srwKernel n (q.2 - q.1)) ≤
        ∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| *
          srwKernel n (q.2 - q.1) :=
    hsumKernel.sum_le_tsum S (fun q hq =>
      mul_nonneg (abs_nonneg _) (srwKernel_nonneg _ _))
  have herror (q : Site × Site) :
      ∫ ω, |Polymer.pathWeight β u (pathStart q) s ω - 1| ∂disorderLaw ≤
        Real.sqrt (Real.exp (2 * β ^ 2) - 1) := by
    simpa only [Nat.cast_ofNat, mul_comm] using
      integral_abs_pathWeight_sub_one_le β u (pathStart q) s
  have hroot : 0 ≤ Real.sqrt (Real.exp (2 * β ^ 2) - 1) := Real.sqrt_nonneg _
  calc
    _ ≤ ∑ q ∈ S, |cellTestWeight N φ q.1 q.2| *
        ((∫ ω, |Polymer.pathWeight β u (pathStart q) s ω - 1| ∂disorderLaw) *
          srwKernel n (q.2 - q.1)) := by simpa [hsum] using hInt
    _ ≤ Real.sqrt (Real.exp (2 * β ^ 2) - 1) *
        ∑ q ∈ S, |cellTestWeight N φ q.1 q.2| * srwKernel n (q.2 - q.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hk : 0 ≤ srwKernel n (q.2 - q.1) := srwKernel_nonneg _ _
      calc
        |cellTestWeight N φ q.1 q.2| *
            ((∫ ω, |Polymer.pathWeight β u (pathStart q) s ω - 1| ∂disorderLaw) *
              srwKernel n (q.2 - q.1)) ≤
          |cellTestWeight N φ q.1 q.2| *
            (Real.sqrt (Real.exp (2 * β ^ 2) - 1) * srwKernel n (q.2 - q.1)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (herror q) hk) (abs_nonneg _)
        _ = Real.sqrt (Real.exp (2 * β ^ 2) - 1) *
              (|cellTestWeight N φ q.1 q.2| * srwKernel n (q.2 - q.1)) := by ring
    _ ≤ Real.sqrt (Real.exp (2 * β ^ 2) - 1) *
        (shiftedKernelMassConstant ε hε * ∫ p, compactAbs φ p) := by
      calc
        _ ≤ Real.sqrt (Real.exp (2 * β ^ 2) - 1) *
            (∑' q : Site × Site, |cellTestWeight N φ q.1 q.2| *
              srwKernel n (q.2 - q.1)) :=
                mul_le_mul_of_nonneg_left hfinite hroot
        _ ≤ _ := mul_le_mul_of_nonneg_left hmass' hroot

/-- The finite-support sum of short-path errors against a disjoint kernel is integrable. -/
theorem integrable_pathWeightError_tsum (ϑ : ℝ) {N u a n : ℕ}
    (s : Fin 2 → Fin 4) (pathStart : Site × Site → Site)
    (hdisj : u + 2 ≤ a ∨ a + n ≤ u) (φ : C_c(Plane × Plane, ℝ)) :
    Integrable (fun ω => ∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
      ((Polymer.pathWeight (criticalBeta ϑ N) u (pathStart q) s ω - 1) *
        pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω)) disorderLaw := by
  classical
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  let β := criticalBeta ϑ N
  let F : Site × Site → Disorder → ℝ := fun q ω =>
    cellTestWeight N φ q.1 q.2 *
      ((Polymer.pathWeight β u (pathStart q) s ω - 1) *
        pointToPoint β a n q.1 q.2 ω)
  have hpairSum (ω : Disorder) : (∑' q : Site × Site, F q ω) = ∑ q ∈ S, F q ω := by
    rw [tsum_eq_sum (s := S)]
    intro q hq
    dsimp [F]
    rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
    simp
  have hF (q : Site × Site) : Integrable (F q) disorderLaw := by
    have hnorm : Integrable (fun ω => |F q ω|) disorderLaw := by
      have hbase := integrable_abs_pathWeightError_mul_pointToPoint β u s
        a n (pathStart q) q.1 q.2 hdisj
      have hEq (ω : Disorder) : |F q ω| =
          |cellTestWeight N φ q.1 q.2| *
            (|Polymer.pathWeight β u (pathStart q) s ω - 1| *
              pointToPoint β a n q.1 q.2 ω) := by
        simp [F, abs_mul, abs_of_nonneg
        (Polymer.pointToPoint_nonneg β a n q.1 q.2 ω)]
      exact (hbase.const_mul _).congr
        (Filter.Eventually.of_forall fun ω => (hEq ω).symm)
    have hweight : Measurable (fun ω : Disorder =>
        Polymer.pathWeight β u (pathStart q) s ω - 1) :=
      (Polymer.measurable_pathWeight β u (pathStart q) s).sub measurable_const
    have hkernel : Measurable (fun ω : Disorder =>
        pointToPoint β a n q.1 q.2 ω) :=
      Polymer.measurable_pointToPoint β a n q.1 q.2
    have hmeas : Measurable (F q) := by
      change Measurable (fun ω => cellTestWeight N φ q.1 q.2 *
        ((Polymer.pathWeight β u (pathStart q) s ω - 1) *
          pointToPoint β a n q.1 q.2 ω))
      exact measurable_const.mul (hweight.mul hkernel)
    have hAEM : AEStronglyMeasurable (F q) disorderLaw := hmeas.aestronglyMeasurable
    have hnormEq : (fun ω => ‖F q ω‖) = fun ω => |F q ω| := by
      funext ω
      exact Real.norm_eq_abs _
    exact (integrable_norm_iff hAEM).mp (hnormEq ▸ hnorm)
  have hsum : Integrable (fun ω => ∑ q ∈ S, F q ω) disorderLaw :=
    integrable_finsetSum _ fun q hq => hF q
  exact hsum.congr (Filter.Eventually.of_forall fun ω => (hpairSum ω).symm)

private theorem tsum_initialPath_split (ϑ : ℝ) {N a n : ℕ}
    (hN : 0 < N) (ha : Even a) (hn : Even (a + n + 2))
    (φ : C_c(Plane × Plane, ℝ)) (s : Fin 2 → Fin 4) (d : Site)
    (ω : Disorder) :
    (∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
      Polymer.pathWeight (criticalBeta ϑ N) a (q.1 - d) s ω *
        pointToPoint (criticalBeta ϑ N) (a + 2) n q.1 q.2 ω) =
      (∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        ((Polymer.pathWeight (criticalBeta ϑ N) a (q.1 - d) s ω - 1) *
          pointToPoint (criticalBeta ϑ N) (a + 2) n q.1 q.2 ω)) +
      (∫ p, φ p * rescaledP2P ϑ N (((a + 2 : ℕ) : ℝ) / N)
        (((a + n + 2 : ℕ) : ℝ) / N) p ω) := by
  let W : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2 *
    ((Polymer.pathWeight (criticalBeta ϑ N) a (q.1 - d) s ω - 1) *
      pointToPoint (criticalBeta ϑ N) (a + 2) n q.1 q.2 ω)
  let G : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2 *
    pointToPoint (criticalBeta ϑ N) (a + 2) n q.1 q.2 ω
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  have hW : Summable W := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    simp [W, cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
  have hG : Summable G := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    simp [G, cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
  have hbase : (∑' q : Site × Site, G q) =
      ∫ p, φ p * rescaledP2P ϑ N (((a + 2 : ℕ) : ℝ) / N)
        (((a + n + 2 : ℕ) : ℝ) / N) p ω := by
    rw [pairing_latticeClock_eq_tsum_pointToPoint ϑ hN
      (Even.add ha even_two) hn φ ω]
    have hduration : a + n + 2 - (a + 2) = n := by omega
    apply tsum_congr
    intro q
    simp only [G, hduration]
  calc
    _ = (∑' q : Site × Site, W q) + ∑' q : Site × Site, G q := by
      rw [← hW.tsum_add hG]
      apply tsum_congr
      intro q
      dsimp [W, G]
      ring
    _ = _ := by rw [hbase]

private theorem pairing_latticeClock_sub_test_eq (ϑ : ℝ) {N a b : ℕ}
    (hN : 0 < N) (ha : Even a) (hb : Even b)
    (φ ψ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, (φ p - ψ p) *
      rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) =
      (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) -
        ∫ p, ψ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω := by
  change (∫ p, (φ - ψ) p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) = _
  rw [pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hb (φ - ψ) ω,
    pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hb φ ω,
    pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hb ψ ω]
  let K : Site × Site → ℝ := fun q =>
    pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω
  have hφ : Summable (fun q : Site × Site => cellTestWeight N φ q.1 q.2 * K q) := by
    apply summable_of_ne_finset_zero
      (s := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset)
    intro q hq
    simp [K, cellTestWeight_eq_zero_of_not_mem N φ q hq]
  have hψ : Summable (fun q : Site × Site => cellTestWeight N ψ q.1 q.2 * K q) := by
    apply summable_of_ne_finset_zero
      (s := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N ψ).toFinset)
    intro q hq
    simp [K, cellTestWeight_eq_zero_of_not_mem N ψ q hq]
  rw [← hφ.tsum_sub hψ]
  apply tsum_congr
  intro q
  simp only [K, cellTestWeight_sub]
  ring

/-- The integral bound for changing a test on one lattice clock; both pairings are integrable by `integrable_pairing_latticeClock_of_test`. -/
theorem integral_abs_pairing_latticeClock_sub_test_le
    (ϑ ε : ℝ) (hε : 0 < ε) {N a b : ℕ} (hN : 0 < N)
    (ha : Even a) (hb : Even b) (hgap : ε * N ≤ b - a)
    (φ ψ : C_c(Plane × Plane, ℝ)) :
    (∫ ω, |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) -
      ∫ p, ψ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω| ∂disorderLaw) ≤
      shiftedKernelMassConstant ε hε * ∫ p, compactAbs (φ - ψ) p := by
  have habR : (a : ℝ) ≤ b := by
    have hpos : 0 < ε * (N : ℝ) := mul_pos hε (by exact_mod_cast hN)
    linarith
  have hab : a ≤ b := by exact_mod_cast habR
  have hgapNat : ε * (N : ℝ) ≤ ((b - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub hab]
    exact hgap
  have hkernel := tsum_shiftedCellKernel_le ε hε N (b - a) hN hgapNat 0 (φ - ψ)
  have hkernel' : (∑' q : Site × Site,
      |cellTestWeight N (φ - ψ) q.1 q.2| * srwKernel (b - a) (q.2 - q.1)) ≤
      shiftedKernelMassConstant ε hε * ∫ p, compactAbs (φ - ψ) p := by
    simpa only [sub_zero] using hkernel
  have hbound := integral_abs_pairing_latticeClock_le_of ϑ hN ha hb (φ - ψ)
    (shiftedKernelMassConstant ε hε * ∫ p, compactAbs (φ - ψ) p) hkernel'
  have hrewrite (ω : Disorder) := pairing_latticeClock_sub_test_eq ϑ hN ha hb φ ψ ω
  have hfun : (fun ω =>
      |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) -
        ∫ p, ψ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω|) =
      fun ω => |∫ p, (φ p - ψ p) *
        rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω| := by
    funext ω
    rw [hrewrite ω]
  rw [hfun]
  exact hbound

/-- The integral of the absolute value of a finite sum is bounded by the sum of absolute integrals. -/
theorem integral_abs_finset_sum_le {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (∫ ω, |∑ i ∈ s, f i ω| ∂μ) ≤
      ∑ i ∈ s, ∫ ω, |f i ω| ∂μ := by
  have hsum : Integrable (fun ω => ∑ i ∈ s, f i ω) μ :=
    integrable_finsetSum _ hf
  have habs : Integrable (fun ω => ∑ i ∈ s, |f i ω|) μ :=
    integrable_finsetSum _ fun i hi => (hf i hi).norm
  have hpoint (ω : Ω) : |∑ i ∈ s, f i ω| ≤ ∑ i ∈ s, |f i ω| :=
    Finset.abs_sum_le_sum_abs _ _
  calc
    _ = ∫ ω, ‖∑ i ∈ s, f i ω‖ ∂μ := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ ω, ∑ i ∈ s, |f i ω| ∂μ := integral_mono hsum.norm habs hpoint
    _ = ∑ i ∈ s, ∫ ω, |f i ω| ∂μ := by
      rw [integral_finsetSum]
      intro i hi
      exact (hf i hi).norm

/-- The integral of the absolute value of a sum is bounded by the two absolute integrals. -/
theorem integral_abs_add_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ ω, |f ω + g ω| ∂μ) ≤
      (∫ ω, |f ω| ∂μ) + ∫ ω, |g ω| ∂μ := by
  have hadd := hf.add hg
  have habs := hf.norm.add hg.norm
  have hpoint (ω : Ω) : |f ω + g ω| ≤ |f ω| + |g ω| := abs_add_le _ _
  calc
    _ = ∫ ω, ‖f ω + g ω‖ ∂μ := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ ω, (|f ω| + |g ω|) ∂μ := integral_mono hadd.norm habs hpoint
    _ = _ := integral_add hf.norm hg.norm

private theorem integral_abs_startTwoStepPairing_le
    (ϑ ε : ℝ) (hε : 0 < ε) {N a n : ℕ} (hN : 0 < N)
    (ha : Even a) (hn : Even (a + n + 2)) (hgap : ε * N ≤ n)
    (φ : C_c(Plane × Plane, ℝ)) :
    (∫ ω, |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((a + n + 2 : ℕ) : ℝ) / N) p ω) -
        ∫ p, φ p * rescaledP2P ϑ N (((a + 2 : ℕ) : ℝ) / N)
          (((a + n + 2 : ℕ) : ℝ) / N) p ω| ∂disorderLaw) ≤
      ∑ s : Fin 2 → Fin 4, (4 : ℝ)⁻¹ ^ 2 *
        (Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1) *
            (shiftedKernelMassConstant ε hε * ∫ p, compactAbs φ p) +
          shiftedKernelMassConstant ε hε *
            ∫ p, compactAbs
              (pairFirstShiftTest
                ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
                  Critical2DKPZ.siteToPlane (-walkPosition 0 s 2)) φ - φ) p) := by
  classical
  let c : ℝ := (4 : ℝ)⁻¹ ^ 2
  let b : ℕ := a + n + 2
  let ψ : (Fin 2 → Fin 4) → C_c(Plane × Plane, ℝ) := fun s =>
    pairFirstShiftTest
      ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
        Critical2DKPZ.siteToPlane (-walkPosition 0 s 2)) φ
  let d : (Fin 2 → Fin 4) → Site := fun s => walkPosition 0 s 2
  let E : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω =>
    ∑' q : Site × Site, cellTestWeight N (ψ s) q.1 q.2 *
      ((Polymer.pathWeight (criticalBeta ϑ N) a (q.1 - d s) s ω - 1) *
        pointToPoint (criticalBeta ϑ N) (a + 2) n q.1 q.2 ω)
  let Q : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω =>
    ∫ p, ψ s p * rescaledP2P ϑ N (((a + 2 : ℕ) : ℝ) / N)
      ((b : ℝ) / N) p ω
  let B : Disorder → ℝ := fun ω =>
    ∫ p, φ p * rescaledP2P ϑ N (((a + 2 : ℕ) : ℝ) / N)
      ((b : ℝ) / N) p ω
  let D : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω => Q s ω - B ω
  let f : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω => c * (E s ω + D s ω)
  have hc : 0 ≤ c := by positivity
  have hcoeff : (∑ _s : Fin 2 → Fin 4, c) = 1 := by
    simp [c, Finset.sum_const, Finset.card_univ]
    norm_num
  have hBsum (ω : Disorder) : (∑ s : Fin 2 → Fin 4, c * B ω) = B ω := by
    calc
      _ = (∑ _s : Fin 2 → Fin 4, c) * B ω := by
        rw [← Finset.sum_mul]
      _ = B ω := by rw [hcoeff]; ring
  have hpair (ω : Disorder) :
      (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) =
        ∑ s : Fin 2 → Fin 4, c * (E s ω + Q s ω) := by
    rw [show b = a + n + 2 by rfl,
      pairing_latticeClock_startTwoStep_eq ϑ hN ha hn φ ω]
    apply Finset.sum_congr rfl
    intro s hs
    have hsplit := tsum_initialPath_split ϑ hN ha hn (ψ s) s (d s) ω
    simpa only [E, Q, ψ, d, b] using congrArg (fun x => c * x) hsplit
  have hdecomp (ω : Disorder) :
      (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) - B ω =
        ∑ s : Fin 2 → Fin 4, f s ω := by
    rw [hpair ω, ← hBsum ω]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [f, D]
    ring
  have hEint (s : Fin 2 → Fin 4) : Integrable (E s) disorderLaw := by
    simpa only [E, ψ, d] using
      integrable_pathWeightError_tsum ϑ s (fun q => q.1 - d s)
        (Or.inl (by omega)) (ψ s)
  have hQint (s : Fin 2 → Fin 4) : Integrable (Q s) disorderLaw := by
    exact integrable_pairing_latticeClock_of_test ϑ (ψ s)
  have hBint : Integrable B disorderLaw := by
    exact integrable_pairing_latticeClock_of_test ϑ φ
  have hfint (s : Fin 2 → Fin 4) : Integrable (f s) disorderLaw := by
    have hD : Integrable (D s) disorderLaw := by
      exact (hQint s).sub hBint
    have hED : Integrable (fun ω => E s ω + D s ω) disorderLaw :=
      (hEint s).add hD
    exact hED.const_mul c
  have hsumAbs := integral_abs_finset_sum_le disorderLaw Finset.univ f
    (fun s hs => hfint s)
  have hpath (s : Fin 2 → Fin 4) :
      (∫ ω, |E s ω| ∂disorderLaw) ≤
        Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1) *
          (shiftedKernelMassConstant ε hε * ∫ p, compactAbs (ψ s) p) := by
    simpa only [E, ψ, d] using
      integral_abs_pathWeightError_tsum_le ϑ ε hε N a (a + 2) n hN hgap s
        (fun q => q.1 - d s) (Or.inl (by omega)) (ψ s)
  have hpathMass (s : Fin 2 → Fin 4) :
      ∫ p, compactAbs (ψ s) p = ∫ p, compactAbs φ p := by
    exact integral_compactAbs_pairFirstShiftTest_eq _ φ
  have htest (s : Fin 2 → Fin 4) :
      (∫ ω, |D s ω| ∂disorderLaw) ≤
        shiftedKernelMassConstant ε hε * ∫ p, compactAbs (ψ s - φ) p := by
    have hgapReal : ε * (N : ℝ) ≤ (b : ℝ) - (a + 2 : ℕ) := by
      have hnat : a + 2 ≤ b := by dsimp [b]; omega
      rw [← Nat.cast_sub hnat]
      have hsub : b - (a + 2) = n := by dsimp [b]; omega
      rw [hsub]
      exact hgap
    simpa only [D, Q, B, b] using
      integral_abs_pairing_latticeClock_sub_test_le ϑ ε hε hN
        (Even.add ha even_two) hn hgapReal (ψ s) φ
  have hfsumBound :
      (∫ ω, |∑ s : Fin 2 → Fin 4, f s ω| ∂disorderLaw) ≤
        ∑ s : Fin 2 → Fin 4, c *
          ((∫ ω, |E s ω| ∂disorderLaw) + ∫ ω, |D s ω| ∂disorderLaw) := by
    calc
      _ ≤ ∑ s : Fin 2 → Fin 4, ∫ ω, |f s ω| ∂disorderLaw := hsumAbs
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        have hadd := integral_abs_add_le disorderLaw (E s) (D s) (hEint s)
          ((hQint s).sub hBint)
        have hrewrite : (∫ ω, |f s ω| ∂disorderLaw) =
            c * ∫ ω, |E s ω + D s ω| ∂disorderLaw := by
          simp [f, abs_mul, abs_of_nonneg hc, integral_const_mul]
        rw [hrewrite]
        exact mul_le_mul_of_nonneg_left hadd hc
  have hfinalBound :
      (∫ ω, |∑ s : Fin 2 → Fin 4, f s ω| ∂disorderLaw) ≤
        ∑ s : Fin 2 → Fin 4, c *
          (Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1) *
              (shiftedKernelMassConstant ε hε * ∫ p, compactAbs φ p) +
            shiftedKernelMassConstant ε hε *
              ∫ p, compactAbs (ψ s - φ) p) := by
    calc
      _ ≤ ∑ s : Fin 2 → Fin 4, c *
            ((∫ ω, |E s ω| ∂disorderLaw) + ∫ ω, |D s ω| ∂disorderLaw) := hfsumBound
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        have hpath' := hpath s
        rw [hpathMass s] at hpath'
        exact mul_le_mul_of_nonneg_left
          (add_le_add hpath' (htest s)) hc
  have hleftInt : Integrable
      (fun ω => |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) - B ω|)
      disorderLaw := by
    exact ((integrable_pairing_latticeClock_of_test ϑ φ).sub hBint).norm
  have hrewrite (ω : Disorder) :
      |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) - B ω| =
        |∑ s : Fin 2 → Fin 4, f s ω| := by rw [hdecomp ω]
  have htranslate :
      (∫ ω, |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) - B ω| ∂disorderLaw) =
        ∫ ω, |∑ s : Fin 2 → Fin 4, f s ω| ∂disorderLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hrewrite
  rw [htranslate]
  exact hfinalBound

/-- For fixed even clock sequences with an eventual macroscopic gap, shifting the initial clock by two makes the pairing error tend to zero in measure. -/
theorem tendstoInMeasure_startTwoStepPairingError
    (ϑ ε : ℝ) (hε : 0 < ε) (a b : ℕ → ℕ)
    (ha : ∀ N, Even (a N)) (hb : ∀ N, Even (b N))
    (hgap : ∀ᶠ N : ℕ in atTop,
      (2 * ε) * (N : ℝ) + 2 ≤ ((b N - a N : ℕ) : ℝ))
    (φ : C_c(Plane × Plane, ℝ)) :
    TendstoInMeasure disorderLaw
      (fun N ω =>
        (∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N) ((b N : ℝ) / N) p ω) -
          ∫ p, φ p * rescaledP2P ϑ N (((a N + 2 : ℕ) : ℝ) / N)
            ((b N : ℝ) / N) p ω)
      atTop (fun _ => 0) := by
  classical
  let c : ℝ := (4 : ℝ)⁻¹ ^ 2
  let shift (N : ℕ) (s : Fin 2 → Fin 4) : ℝ :=
    ∫ p, compactAbs
      (pairFirstShiftTest
        ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
          Critical2DKPZ.siteToPlane (-walkPosition 0 s 2)) φ - φ) p
  let root (N : ℕ) : ℝ :=
    Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1)
  let C : ℝ := shiftedKernelMassConstant ε hε
  let mass : ℝ := ∫ p, compactAbs φ p
  let upper (N : ℕ) : ℝ :=
    ∑ s : Fin 2 → Fin 4, c * (root N * (C * mass) + C * shift N s)
  have hβ := Critical2DKPZ.SHF.Moments.tendsto_criticalBeta_zero ϑ
  have hβsq : Tendsto (fun N : ℕ => (criticalBeta ϑ N) ^ 2) atTop (𝓝 0) := by
    simpa using hβ.pow 2
  have hdouble : Tendsto (fun N : ℕ => 2 * (criticalBeta ϑ N) ^ 2)
      atTop (𝓝 0) := by simpa using hβsq.const_mul 2
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hdouble
  have harg : Tendsto (fun N : ℕ => Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1)
      atTop (𝓝 0) := by
    have h := hexp.sub_const 1
    convert h using 1 <;> norm_num [Real.exp_zero]
  have hroot : Tendsto root atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp harg
    have h' : Tendsto (fun N : ℕ =>
        Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using h
    simpa [root] using h'
  have hshift (s : Fin 2 → Fin 4) : Tendsto (fun N => shift N s) atTop (𝓝 0) := by
    have h := tendsto_pairFirstShiftTest_L1 φ (-walkPosition 0 s 2)
    simpa [shift, compactAbs] using h
  have hterm (s : Fin 2 → Fin 4) :
      Tendsto (fun N => c * (root N * (C * mass) + C * shift N s))
        atTop (𝓝 0) := by
    have hfirst : Tendsto (fun N => root N * (C * mass)) atTop (𝓝 0) :=
      by simpa using hroot.mul_const (C * mass)
    have hsecond : Tendsto (fun N => C * shift N s) atTop (𝓝 0) :=
      by simpa using (hshift s).const_mul C
    have hadd := hfirst.add hsecond
    simpa [upper, c] using hadd.const_mul c
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using tendsto_finsetSum Finset.univ (fun s hs => hterm s)
  let err (N : ℕ) (ω : Disorder) : ℝ :=
    (∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N) ((b N : ℝ) / N) p ω) -
      ∫ p, φ p * rescaledP2P ϑ N (((a N + 2 : ℕ) : ℝ) / N)
        ((b N : ℝ) / N) p ω
  have hbound : ∀ᶠ N : ℕ in atTop,
      (∫ ω, |err N ω| ∂disorderLaw) ≤ upper N := by
    filter_upwards [eventually_gt_atTop 0, hgap] with N hN hgapN
    have hba : a N ≤ b N := by
      by_contra h
      have hlt : b N < a N := Nat.lt_of_not_ge h
      have hzero : b N - a N = 0 := Nat.sub_eq_zero_of_le hlt.le
      rw [hzero] at hgapN
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      have hpos : 0 < (2 * ε) * (N : ℝ) :=
        mul_pos (mul_pos (by norm_num) hε) hNreal
      have hpos' : 0 < (2 * ε) * (N : ℝ) + 2 := by linarith
      exact (not_le_of_gt hpos') (by simpa using hgapN)
    have hNatCast : (2 : ℝ) ≤ ((b N - a N : ℕ) : ℝ) := by
      have hnonneg : 0 ≤ (2 * ε) * (N : ℝ) := by positivity
      linarith
    have hgapReal : 2 ≤ (b N : ℝ) - a N := by
      rw [← Nat.cast_sub hba]
      exact hNatCast
    have hnatDiff : 2 ≤ b N - a N := by exact_mod_cast hNatCast
    have hnat : a N + 2 ≤ b N := by omega
    let n : ℕ := b N - (a N + 2)
    have hclock : a N + n + 2 = b N := by dsimp [n]; omega
    have hnatSub : b N - a N = n + 2 := by dsimp [n]; omega
    have hcastSub : ((b N - a N : ℕ) : ℝ) = (n : ℝ) + 2 := by
      rw [hnatSub]
      norm_num
    have hnGap : ε * (N : ℝ) ≤ n := by
      have hgap' : 2 * ε * (N : ℝ) + 2 ≤ (n : ℝ) + 2 := by
        rw [← hcastSub]
        exact hgapN
      nlinarith [mul_nonneg hε.le (show 0 ≤ (N : ℝ) by positivity)]
    have hnEven : Even (a N + n + 2) := by rw [hclock]; exact hb N
    have hboundN := integral_abs_startTwoStepPairing_le ϑ ε hε hN (ha N)
      hnEven hnGap φ
    have hboundN' :
        (∫ ω, |err N ω| ∂disorderLaw) ≤ upper N := by
      simpa [err, upper, root, C, mass, shift, n, hclock, c] using hboundN
    exact hboundN'
  have habsNonneg (N : ℕ) : 0 ≤ ∫ ω, |err N ω| ∂disorderLaw :=
    integral_nonneg fun ω => abs_nonneg (err N ω)
  have hL1 : Tendsto (fun N => ∫ ω, |err N ω| ∂disorderLaw) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall habsNonneg) hbound hupper
  have hIntegrable (N : ℕ) : Integrable (fun ω => |err N ω|) disorderLaw := by
    have h1 : Integrable (fun ω =>
        ∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N) ((b N : ℝ) / N) p ω)
        disorderLaw := integrable_pairing_latticeClock_of_test ϑ φ
    have h2 : Integrable (fun ω =>
        ∫ p, φ p * rescaledP2P ϑ N (((a N + 2 : ℕ) : ℝ) / N)
          ((b N : ℝ) / N) p ω) disorderLaw :=
      integrable_pairing_latticeClock_of_test ϑ φ
    simpa [err] using (h1.sub h2).norm
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro δ hδ
  have hmarkov (N : ℕ) : disorderLaw.real {ω | δ ≤ dist (err N ω) 0} ≤
      (∫ ω, |err N ω| ∂disorderLaw) / δ :=
    measureReal_dist_le_integral_abs disorderLaw (err N) (hIntegrable N) hδ
  have hdiv : Tendsto (fun N => (∫ ω, |err N ω| ∂disorderLaw) / δ)
      atTop (𝓝 0) := by simpa using hL1.div_const δ
  have hresult : Tendsto (fun N : ℕ => disorderLaw.real
      {ω | δ ≤ dist (err N ω) (0 : ℝ)}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [zero_div] using hdiv)
      (Filter.Eventually.of_forall fun N => measureReal_nonneg)
      (Filter.Eventually.of_forall hmarkov)
  simpa only [err] using hresult

end Critical2DKPZ.SHF.Symmetries

end
