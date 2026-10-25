/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.CompactMollifier
public import Critical2DKPZ.Analysis.Sobolev.TranslatedPairingConvolution
public import Critical2DKPZ.CovarianceKernel.WeakCovarianceKernelExistence
public import Critical2DKPZ.CovarianceKernel.RadialPairingRepresentation
public import Critical2DKPZ.SmallScales.DeterministicComparison
import Mathlib.Topology.Algebra.Support

/-! # Nonnegativity transfer for the Bessel inversion -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace Critical2DKPZ.CovarianceKernel

/-- Compact support gives a finite radius containing the normalized mollifier's support. -/
theorem exists_unitMassTestFn_support_radius :
    ∃ R : ℝ, 0 ≤ R ∧
      tsupport Analysis.Sobolev.unitMassTestFn ⊆ Metric.closedBall (0 : Plane) R := by
  obtain ⟨R, hR⟩ := Analysis.Sobolev.unitMassTestFn.hasCompactSupport.isBounded
    |>.subset_closedBall (0 : Plane)
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  exact hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))

/-- Dilation sends a compact test support into the correspondingly scaled ball. -/
theorem tsupport_testFn_dilate_subset_closedBall (φ : TestFn) {ε : ℝ} (hε : 0 < ε)
    (x : Plane) {R : ℝ}
    (hφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) R) :
    tsupport (φ.dilate ε x) ⊆ Metric.closedBall x (ε * R) := by
  let T : Homeomorph Plane Plane :=
    (Homeomorph.addRight (-x)).trans
      (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε.ne'))
  have hT (y : Plane) : T y = ε⁻¹ • (y - x) := by
    simp [T, sub_eq_add_neg]
  have hsupp : tsupport (φ.dilate ε x) ⊆ tsupport (φ ∘ T) := by
    change tsupport (fun y : Plane => ε⁻¹ ^ 2 * φ (ε⁻¹ • (y - x))) ⊆ _
    rw [show (fun y : Plane => ε⁻¹ ^ 2 * φ (ε⁻¹ • (y - x))) =
        fun y => ε⁻¹ ^ 2 • (φ ∘ T) y by
      funext y
      simp [hT]]
    exact tsupport_smul_subset_right _ _
  intro y hy
  have hyT : T y ∈ tsupport φ := by
    have : y ∈ T ⁻¹' tsupport φ := by
      rw [← tsupport_comp_eq_preimage φ T]
      exact hsupp hy
    exact this
  have hnorm : ‖T y‖ ≤ R := by
    simpa [dist_zero_right] using (Metric.mem_closedBall.mp (hφ hyT))
  have hnormT : ‖T y‖ = ε⁻¹ * ‖y - x‖ := by
    rw [hT, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  have hdist : ‖y - x‖ ≤ ε * R := by
    calc
      ‖y - x‖ = ε * (ε⁻¹ * ‖y - x‖) := by field_simp
      _ = ε * ‖T y‖ := by rw [← hnormT]
      _ ≤ ε * R := mul_le_mul_of_nonneg_left hnorm hε.le
  exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hdist)

/-- The convolution of test functions localized near two points is localized near their
difference. -/
theorem tsupport_testFnConvolution_dilate_subset_closedBall (φ ψ : TestFn)
    {ε R : ℝ} (x : Plane)
    (hφ : tsupport (φ.dilate ε x) ⊆ Metric.closedBall x (ε * R))
    (hψ : tsupport (ψ.dilate ε 0) ⊆ Metric.closedBall (0 : Plane) (ε * R)) :
    tsupport (Analysis.Sobolev.testFnConvolution (φ.dilate ε x) (ψ.dilate ε 0)) ⊆
      Metric.closedBall x (ε * R + ε * R) := by
  let ρ := Analysis.Sobolev.reflectedTestFn (ψ.dilate ε 0)
  have hρ : tsupport ρ ⊆ Metric.closedBall (0 : Plane) (ε * R) := by
    intro y hy
    have hy' : -y ∈ tsupport (ψ.dilate ε 0) := by
      have hpre : y ∈ (Homeomorph.neg Plane) ⁻¹' tsupport (ψ.dilate ε 0) := by
        rw [← tsupport_comp_eq_preimage (ψ.dilate ε 0) (Homeomorph.neg Plane)]
        exact hy
      simpa using hpre
    have hdist := Metric.mem_closedBall.mp (hψ hy')
    simpa [dist_zero_right, norm_neg] using hdist
  intro z hz
  have hsum := Analysis.Sobolev.tsupport_testFnConvolution_subset_sum
    (φ.dilate ε x) (ψ.dilate ε 0) hz
  rcases Set.mem_add.mp hsum with ⟨y, hy, w, hw, rfl⟩
  have hy' : dist y x ≤ ε * R := Metric.mem_closedBall.mp (hφ hy)
  have hw' : ‖w‖ ≤ ε * R := by
    simpa [dist_zero_right] using (Metric.mem_closedBall.mp (hρ hw))
  apply Metric.mem_closedBall.mpr
  calc
    dist (y + w) x = ‖(y - x) + w‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ ‖y - x‖ + ‖w‖ := norm_add_le _ _
    _ ≤ ε * R + ε * R := add_le_add (by simpa [dist_eq_norm] using hy') hw'

/-- A continuous-off-zero kernel is nonnegative there if all its localized convolution
pairings agree with a nonnegative locally square-integrable kernel. -/
theorem continuousOn_nonneg_of_testFnConvolution_pairing
    (F C : Plane → ℝ)
    (hFcont : ContinuousOn F ({0}ᶜ : Set Plane))
    (hFmem : ∀ K : Set Plane, IsCompact K → MemLp F 2 (volume.restrict K))
    (hCmem : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hCnonneg : ∀ᵐ z : Plane ∂volume, 0 ≤ C z)
    (hpair : ∀ φ ψ : TestFn,
      (∫ z : Plane, Analysis.Sobolev.testFnConvolution φ ψ z * F z) =
        ∫ z : Plane, Analysis.Sobolev.testFnConvolution φ ψ z * C z) :
    ∀ z : Plane, z ≠ 0 → 0 ≤ F z := by
  intro z hz
  by_contra hFz
  have hFzneg : F z < 0 := lt_of_not_ge hFz
  have hFzhalf : F z / 2 < 0 := by linarith
  have hFzltHalf : F z < F z / 2 := by linarith
  have hzcomp : z ∈ ({0}ᶜ : Set Plane) := by simpa using hz
  have hcontAt : ContinuousAt F z :=
    hFcont.continuousAt (isOpen_compl_singleton.mem_nhds hzcomp)
  have hnear : ∀ᶠ w : Plane in 𝓝 z, F w < F z / 2 :=
    hcontAt.eventually (Iio_mem_nhds hFzltHalf)
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨R, hR, hSupport⟩ := exists_unitMassTestFn_support_radius
  let ε : ℝ := δ / (2 * (R + 1))
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hrad : ε * R + ε * R < δ := by
    have hden : 0 < R + 1 := by linarith
    have hfrac : R / (R + 1) < 1 := (div_lt_one hden).2 (by linarith)
    calc
      ε * R + ε * R = δ * (R / (R + 1)) := by
        dsimp [ε]
        field_simp
        ring
      _ < δ * 1 := mul_lt_mul_of_pos_left hfrac hδpos
      _ = δ := mul_one δ
  let φ : TestFn := Analysis.Sobolev.unitMassTestFn.dilate ε z
  let ψ : TestFn := Analysis.Sobolev.unitMassTestFn.dilate ε 0
  let q : TestFn := Analysis.Sobolev.testFnConvolution φ ψ
  have hφnonneg : ∀ y : Plane, 0 ≤ φ y := by
    intro y
    change 0 ≤ ε⁻¹ ^ 2 * Analysis.Sobolev.unitMassTestFn (ε⁻¹ • (y - z))
    exact mul_nonneg (sq_nonneg _) (Analysis.Sobolev.unitMassTestFn_nonneg _)
  have hψnonneg : ∀ y : Plane, 0 ≤ ψ y := by
    intro y
    change 0 ≤ ε⁻¹ ^ 2 *
      Analysis.Sobolev.unitMassTestFn (ε⁻¹ • (y - (0 : Plane)))
    simp only [sub_zero]
    exact mul_nonneg (sq_nonneg _) (Analysis.Sobolev.unitMassTestFn_nonneg _)
  have hqnonneg : ∀ y : Plane, 0 ≤ q y := by
    intro y
    rw [Analysis.Sobolev.testFnConvolution_apply]
    exact integral_nonneg (fun u => mul_nonneg (hφnonneg u) (hψnonneg (u - y)))
  have hmassφ : ∫ y : Plane, φ y = 1 := by
    dsimp [φ]
    simpa [Analysis.Sobolev.integral_unitMassTestFn] using
      SmallScales.integral_testFn_dilate_mul Analysis.Sobolev.unitMassTestFn hεpos z
        (fun _ : Plane => (1 : ℝ))
  have hmassψ : ∫ y : Plane, ψ y = 1 := by
    dsimp [ψ]
    simpa [Analysis.Sobolev.integral_unitMassTestFn] using
      SmallScales.integral_testFn_dilate_mul Analysis.Sobolev.unitMassTestFn hεpos 0
        (fun _ : Plane => (1 : ℝ))
  have hmassq : ∫ y : Plane, q y = 1 := by
    dsimp [q]
    rw [Analysis.Sobolev.integral_testFnConvolution, hmassφ, hmassψ, one_mul]
  have hφsupport : tsupport φ ⊆ Metric.closedBall z (ε * R) := by
    dsimp [φ]
    exact tsupport_testFn_dilate_subset_closedBall Analysis.Sobolev.unitMassTestFn hεpos z hSupport
  have hψsupport : tsupport ψ ⊆ Metric.closedBall (0 : Plane) (ε * R) := by
    dsimp [ψ]
    exact tsupport_testFn_dilate_subset_closedBall Analysis.Sobolev.unitMassTestFn hεpos 0 hSupport
  have hqsupport : tsupport q ⊆ Metric.closedBall z (ε * R + ε * R) := by
    dsimp [q, φ, ψ]
    exact tsupport_testFnConvolution_dilate_subset_closedBall
      Analysis.Sobolev.unitMassTestFn Analysis.Sobolev.unitMassTestFn z hφsupport hψsupport
  have hqF : Integrable (fun y : Plane => q y * F y) volume :=
    Spectral.integrable_testFn_kernel F hFmem q
  have hqC : Integrable (fun y : Plane => q y * C y) volume :=
    Spectral.integrable_testFn_kernel C hCmem q
  have hqconstant : Integrable (fun y : Plane => q y * (F z / 2)) volume := by
    exact (q.continuous.integrable_of_hasCompactSupport q.hasCompactSupport).mul_const _
  have hpoint : ∀ᵐ y : Plane ∂volume, q y * F y ≤ q y * (F z / 2) := by
    filter_upwards [] with y
    by_cases hy : q y = 0
    · simp [hy]
    · have hySupport : y ∈ tsupport q := subset_tsupport q hy
      have hyRadius : dist y z < δ := by
        have hyBall := Metric.mem_closedBall.mp (hqsupport hySupport)
        have hyNorm : dist y z ≤ ε * R + ε * R := by
          simpa using hyBall
        exact lt_of_le_of_lt hyNorm hrad
      have hyF : F y < F z / 2 := hδball (Metric.mem_ball.mpr hyRadius)
      exact mul_le_mul_of_nonneg_left hyF.le (hqnonneg y)
  have hFintneg : ∫ y : Plane, q y * F y < 0 := by
    have hbound := integral_mono_ae hqF hqconstant hpoint
    rw [integral_mul_const, hmassq] at hbound
    have hbound' : (∫ y : Plane, q y * F y) ≤ F z / 2 := by simpa using hbound
    exact lt_of_le_of_lt hbound' hFzhalf
  have hCintnonneg : 0 ≤ ∫ y : Plane, q y * C y :=
    integral_nonneg_of_ae (hCnonneg.mono fun y hy => mul_nonneg (hqnonneg y) hy)
  have hpair' := hpair φ ψ
  change (∫ y : Plane, q y * F y) = ∫ y : Plane, q y * C y at hpair'
  linarith

end Critical2DKPZ.CovarianceKernel

end
