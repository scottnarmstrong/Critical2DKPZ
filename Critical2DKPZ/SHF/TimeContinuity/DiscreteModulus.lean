/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.TimeContinuity.EnvelopeSecondMoment
public import Critical2DKPZ.SHF.TimeContinuity.LimitPassage
public import Critical2DKPZ.SHF.TimeContinuity.SlabIdentities
public import Critical2DKPZ.MomentBounds.AiiKNormMGF
public import Critical2DKPZ.SHF.Flow.SlabSmoothedConnector
import Critical2DKPZ.SHF.Limit.SubseqLimit
import Mathlib.Tactic

/-! # The discrete compact-pairing modulus -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Bornology
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.TimeContinuity

open Critical2DKPZ.SHF.Limit

private def slabSectionTest (Φ : C_c(Plane × Plane, ℝ)) (z : Plane) :
    C_c(Plane, ℝ) where
  toFun x := Φ (x, z)
  continuous_toFun := Φ.continuous.comp (continuous_id.prodMk continuous_const)
  hasCompactSupport' := by
    let Kx : Set Plane := Prod.fst '' tsupport Φ
    have hKx : IsCompact Kx := Φ.hasCompactSupport.image continuous_fst
    apply HasCompactSupport.of_support_subset_isCompact hKx
    intro x hx
    have hΦ : Φ (x, z) ≠ 0 := by
      simpa only [Function.mem_support] using hx
    exact ⟨(x, z), subset_closure (Function.mem_support.mpr hΦ), rfl⟩

private theorem slabMeanKernel_test_eq_cellTsum (ϑ : ℝ) (N : ℕ) (s s' : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (y z : Plane) :
    (∫ x, Φ (x, z) * slabMeanKernel ϑ N s s' x y) =
      (N : ℝ) / 4 * ∑' w : Site,
        (∫ x in cell N w, Φ (x, z)) *
          Critical2DKPZ.srwKernel
            (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
            (latticePoint N y - w) := by
  let ψ := slabSectionTest Φ z
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  let G : Site → ℝ := fun w => Critical2DKPZ.srwKernel m (latticePoint N y - w)
  have hG : ∀ w, ‖G w‖ ≤ 1 := by
    intro w
    dsimp [G]
    rw [abs_of_nonneg (Critical2DKPZ.Polymer.kernel_nonneg _ _)]
    exact Critical2DKPZ.Polymer.srwKernel_le_one _ _
  have hψ (x : Plane) : ψ x = Φ (x, z) := rfl
  have hpoint (x : Plane) :
      Φ (x, z) * slabMeanKernel ϑ N s s' x y =
        (N : ℝ) / 4 * (ψ x * G (latticePoint N x)) := by
    rw [slabMeanKernel_eq_srwKernel, hψ]
    dsimp [G, m]
    ring
  calc
    _ = ∫ x, (N : ℝ) / 4 * (ψ x * G (latticePoint N x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = (N : ℝ) / 4 * ∫ x, ψ x * G (latticePoint N x) := by
      rw [integral_const_mul]
    _ = (N : ℝ) / 4 * ∑' w : Site,
        (∫ x in cell N w, Φ (x, z)) *
          Critical2DKPZ.srwKernel m (latticePoint N y - w) := by
      rw [Critical2DKPZ.SHF.Flow.integral_latticeStep_eq_cellTsum N ψ G 1 hG]
      apply congrArg (fun q : ℝ => ((N : ℝ) / 4) * q)
      apply tsum_congr
      intro w
      dsimp [G, m]
      congr 1


private theorem slabStepCount_le {N : ℕ} (hN : 0 < N) {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s ≤ s') :
    ((evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s) : ℕ) : ℝ) / N ≤
      (s' - s) + 2 / N := by
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * s')
  have hs' : 0 ≤ s' := hs.trans hss'
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hss' (Nat.cast_nonneg N))
  have ha : (N : ℝ) * s ≤ a := Critical2DKPZ.le_evenCeil _
  have hb : (b : ℝ) < (N : ℝ) * s' + 2 :=
    Critical2DKPZ.evenCeil_lt_add_two (mul_nonneg (Nat.cast_nonneg N) hs')
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
    exact Nat.cast_sub hab
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [hcast]
  apply (div_le_iff₀ hNreal).2
  have hba : (b : ℝ) - a ≤ (N : ℝ) * (s' - s) + 2 := by nlinarith
  calc
    (b : ℝ) - a ≤ (N : ℝ) * (s' - s) + 2 := hba
    _ = (s' - s + 2 / (N : ℝ)) * (N : ℝ) := by field_simp

private theorem dist_le_cellEndpoint (N : ℕ) (hN : 0 < N) (x y : Plane)
    (w v : Site) (hx : x ∈ cell N w) (hy : y ∈ cell N v) :
    dist x y ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖ +
      2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
  let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  have hxw : latticePoint N x = w := (Critical2DKPZ.mem_cell_iff N w x).mp hx
  have hyv : latticePoint N y = v := (Critical2DKPZ.mem_cell_iff N v y).mp hy
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hmx := Critical2DKPZ.norm_sub_latticePoint_le hN x
  have hmy := Critical2DKPZ.norm_sub_latticePoint_le hN y
  have hmx' : ‖x - scale • siteToPlane w‖ ≤ scale := by simpa [scale, hxw] using hmx
  have hmy' : ‖y - scale • siteToPlane v‖ ≤ scale := by simpa [scale, hyv] using hmy
  have hsite : siteToPlane w - siteToPlane v = siteToPlane (w - v) := by
    ext i
    simp [siteToPlane]
  have hcenter : ‖scale • siteToPlane w - scale • siteToPlane v‖ =
      scale * ‖siteToPlane (w - v)‖ := by
    rw [← smul_sub, hsite, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  have hmy'' : ‖scale • siteToPlane v - y‖ ≤ scale := by
    rw [norm_sub_rev]
    exact hmy'
  have hdecomp : x - y = (x - scale • siteToPlane w) +
      (scale • siteToPlane w - scale • siteToPlane v) +
      (scale • siteToPlane v - y) := by abel
  calc
    dist x y = ‖x - y‖ := dist_eq_norm x y
    _ = ‖(x - scale • siteToPlane w) +
        (scale • siteToPlane w - scale • siteToPlane v) +
        (scale • siteToPlane v - y)‖ := by rw [← hdecomp]
    _ ≤ ‖x - scale • siteToPlane w‖ +
        ‖scale • siteToPlane w - scale • siteToPlane v‖ +
        ‖scale • siteToPlane v - y‖ := by
      calc
        _ ≤ ‖(x - scale • siteToPlane w) +
            (scale • siteToPlane w - scale • siteToPlane v)‖ +
            ‖scale • siteToPlane v - y‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ scale + scale * ‖siteToPlane (w - v)‖ + scale := by
      rw [hcenter]
      exact add_le_add (add_le_add hmx' le_rfl) hmy''
    _ = _ := by dsimp [scale]; ring

/-- A compactly supported test `Φ` on `Plane × Plane` has a radius `R ≥ 0` such that `Φ (x, z) ≠ 0`
forces both `‖x‖ ≤ R` and `‖z‖ ≤ R`. -/
theorem slabTest_support_radius (Φ : C_c(Plane × Plane, ℝ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x z, Φ (x, z) ≠ 0 → ‖x‖ ≤ R ∧ ‖z‖ ≤ R := by
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane × Plane)).mp Φ.hasCompactSupport.isBounded
  refine ⟨max 0 R₀, le_max_left _ _, ?_⟩
  intro x z hΦ
  have hp : (x, z) ∈ tsupport Φ :=
    subset_closure (Function.mem_support.mpr hΦ)
  have hpball := hR₀ hp
  have hpnorm : ‖(x, z)‖ ≤ R₀ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hpball
  exact ⟨(norm_fst_le (x, z)).trans (hpnorm.trans (le_max_right 0 R₀)),
    (norm_snd_le (x, z)).trans (hpnorm.trans (le_max_right 0 R₀))⟩

/-- For `0 < N` and an even-lattice site `w`, the cell average `(N / 4) ∫_{cell N w} Φ (x, z) dx`
of the test `Φ` in its first variable is at most the sup norm of `Φ` in absolute value. -/
theorem slabCellAverage_abs_le {N : ℕ} (hN : 0 < N)
    (Φ : C_c(Plane × Plane, ℝ)) (z : Plane) (w : Site) (hw : w ∈ evenLattice) :
    |(N : ℝ) / 4 * (∫ x in cell N w, Φ (x, z))| ≤
      ‖Φ.toBoundedContinuousFunction‖ := by
  let ψ := slabSectionTest Φ z
  have hvol : volume (cell N w) < ⊤ := Critical2DKPZ.volume_cell_lt_top hN hw
  have hψint : Integrable ψ volume :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hψbound (x : Plane) : ‖ψ x‖ ≤ ‖Φ.toBoundedContinuousFunction‖ := by
    exact Φ.toBoundedContinuousFunction.norm_coe_le_norm (x, z)
  have hconst : IntegrableOn (fun _ : Plane => ‖Φ.toBoundedContinuousFunction‖)
      (cell N w) volume := integrableOn_const hvol.ne
  have hmono : (∫ x in cell N w, ‖ψ x‖) ≤
      ∫ x in cell N w, ‖Φ.toBoundedContinuousFunction‖ :=
    setIntegral_mono_on hψint.norm.integrableOn hconst
      (Critical2DKPZ.measurableSet_cell N w) (fun x _ => hψbound x)
  have hconstIntegral : (∫ x in cell N w, ‖Φ.toBoundedContinuousFunction‖) =
      ‖Φ.toBoundedContinuousFunction‖ * (4 / (N : ℝ)) := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul,
      Critical2DKPZ.volume_cell_toReal hN hw]
    ring
  have hnormIntegral : |∫ x in cell N w, ψ x| ≤ ∫ x in cell N w, ‖ψ x‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := ψ) (μ := volume.restrict (cell N w)))
  have hNnonneg : 0 ≤ (N : ℝ) / 4 := by positivity
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    |(N : ℝ) / 4 * (∫ x in cell N w, Φ (x, z))| =
        (N : ℝ) / 4 * |∫ x in cell N w, ψ x| := by
          rw [show (∫ x in cell N w, Φ (x, z)) = ∫ x in cell N w, ψ x by rfl,
            abs_mul, abs_of_nonneg hNnonneg]
    _ ≤ (N : ℝ) / 4 * (∫ x in cell N w, ‖ψ x‖) :=
      mul_le_mul_of_nonneg_left hnormIntegral hNnonneg
    _ ≤ (N : ℝ) / 4 * (∫ x in cell N w, ‖Φ.toBoundedContinuousFunction‖) :=
      mul_le_mul_of_nonneg_left hmono hNnonneg
    _ = ‖Φ.toBoundedContinuousFunction‖ := by
      rw [hconstIntegral]
      field_simp

private theorem slabCellAverage_near {N : ℕ} (hN : 0 < N)
    {s s' : ℝ} (Φ : C_c(Plane × Plane, ℝ))
    (y z : Plane) (w : Site) (ε δ r : ℝ)
    (hmod : ∀ x, dist x y < δ → |Φ (x, z) - Φ (y, z)| ≤ ε)
    (hnear : r + 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ < δ)
    (hw : w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y)
      (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)))
    (hd : (Real.sqrt ((N : ℝ) / 2))⁻¹ *
      ‖siteToPlane (w - latticePoint N y)‖ ≤ r) :
    |(N : ℝ) / 4 * (∫ x in cell N w, Φ (x, z)) - Φ (y, z)| ≤ ε := by
  let ψ := slabSectionTest Φ z
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  have hmEven : Even m := by
    dsimp [m]
    exact Critical2DKPZ.SHF.Moments.even_evenCeil_sub ((N : ℝ) * s) ((N : ℝ) * s')
  have hwEven : w ∈ evenLattice := by
    change Even (w 0 + w 1)
    exact Critical2DKPZ.SHF.Flow.even_mem_endpoints_of_even
      (Critical2DKPZ.latticePoint_mem_evenLattice N y) hmEven hw
  have hvol : volume (cell N w) < ⊤ := Critical2DKPZ.volume_cell_lt_top hN hwEven
  have hψint : Integrable ψ volume :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hconstInt : IntegrableOn (fun _ : Plane => ψ y) (cell N w) volume :=
    integrableOn_const hvol.ne
  have hdiffInt : IntegrableOn (fun x : Plane => ψ x - ψ y) (cell N w) volume :=
    hψint.integrableOn.sub hconstInt
  have hdiffBound (x : Plane) (hx : x ∈ cell N w) :
      ‖ψ x - ψ y‖ ≤ ε := by
    have hxw : latticePoint N x = w := (Critical2DKPZ.mem_cell_iff N w x).mp hx
    have hdist := dist_le_cellEndpoint N hN x y w (latticePoint N y) hx
      (Critical2DKPZ.mem_cell_latticePoint N y)
    have hdist' : dist x y < δ := by
      apply lt_of_le_of_lt hdist
      dsimp [m] at hmEven
      exact lt_of_le_of_lt (add_le_add hd le_rfl) hnear
    simpa [ψ, slabSectionTest, Real.norm_eq_abs] using hmod x hdist'
  have hεint : IntegrableOn (fun _ : Plane => ε) (cell N w) volume :=
    integrableOn_const hvol.ne
  have hdiffIntBound :
      (∫ x in cell N w, ‖ψ x - ψ y‖) ≤ ∫ x in cell N w, ε :=
    setIntegral_mono_on hdiffInt.norm hεint (Critical2DKPZ.measurableSet_cell N w)
      hdiffBound
  have hconstIntegral : (∫ x in cell N w, ψ y) = ψ y * (4 / (N : ℝ)) := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul,
      Critical2DKPZ.volume_cell_toReal hN hwEven]
    ring
  have hεIntegral : (∫ x in cell N w, ε) = ε * (4 / (N : ℝ)) := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul,
      Critical2DKPZ.volume_cell_toReal hN hwEven]
    ring
  have hdiffIntegral :
      (∫ x in cell N w, (ψ x - ψ y)) =
        (∫ x in cell N w, ψ x) - ∫ x in cell N w, ψ y := by
    exact integral_sub hψint.integrableOn hconstInt
  have hform : (N : ℝ) / 4 * (∫ x in cell N w, (ψ x - ψ y)) =
      (N : ℝ) / 4 * (∫ x in cell N w, ψ x) - ψ y := by
    rw [hdiffIntegral, hconstIntegral]
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hnormIntegral :
      |∫ x in cell N w, (ψ x - ψ y)| ≤ ∫ x in cell N w, ‖ψ x - ψ y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := fun x : Plane => ψ x - ψ y)
        (μ := volume.restrict (cell N w)))
  have hNnonneg : 0 ≤ (N : ℝ) / 4 := by positivity
  rw [show Φ (y, z) = ψ y by rfl]
  calc
    |(N : ℝ) / 4 * (∫ x in cell N w, ψ x) - ψ y| =
        |(N : ℝ) / 4 * (∫ x in cell N w, (ψ x - ψ y))| := by rw [hform]
    _ = (N : ℝ) / 4 * |∫ x in cell N w, (ψ x - ψ y)| := by
      rw [abs_mul, abs_of_nonneg hNnonneg]
    _ ≤ (N : ℝ) / 4 * (∫ x in cell N w, ‖ψ x - ψ y‖) :=
      mul_le_mul_of_nonneg_left hnormIntegral hNnonneg
    _ ≤ (N : ℝ) / 4 * (∫ x in cell N w, ε) :=
      mul_le_mul_of_nonneg_left hdiffIntBound hNnonneg
    _ = ε := by rw [hεIntegral]; field_simp

/-- The test `Φ (·, z)` smoothed in its first variable by the slab mean kernel on `(s, s']`:
`∫ x, Φ (x, z) * slabMeanKernel ϑ N s s' x y`. -/
def slabSmoothedTest (ϑ : ℝ) (N : ℕ) (s s' : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (y z : Plane) : ℝ :=
  ∫ x, Φ (x, z) * slabMeanKernel ϑ N s s' x y

/-- Expand the slab-smoothed test as the finite endpoint walk sum. -/
theorem slabSmoothedTest_endpoint_sum (ϑ : ℝ) {N : ℕ}
    (s s' : ℝ) (Φ : C_c(Plane × Plane, ℝ)) (y z : Plane) :
    slabSmoothedTest ϑ N s s' Φ y z =
      ∑ w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y)
          (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)),
        ((N : ℝ) / 4 * (∫ x in cell N w, Φ (x, z))) *
          Critical2DKPZ.srwKernel
            (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
            (latticePoint N y - w) := by
  classical
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  let v := latticePoint N y
  let E := Critical2DKPZ.Polymer.endpoints v m
  let A : Site → ℝ := fun w => (N : ℝ) / 4 * (∫ x in cell N w, Φ (x, z))
  let G : Site → ℝ := fun w => Critical2DKPZ.srwKernel m (v - w)
  have hGzero (w : Site) (hw : w ∉ E) : G w = 0 := by
    dsimp [G, E, v, m]
    rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
    exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem _ _ _ hw
  have hconv : slabSmoothedTest ϑ N s s' Φ y z = ∑' w : Site, A w * G w := by
    change (∫ x, Φ (x, z) * slabMeanKernel ϑ N s s' x y) = _
    rw [slabMeanKernel_test_eq_cellTsum]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro w
    dsimp [A, G, v, m]
    ring
  calc
    slabSmoothedTest ϑ N s s' Φ y z = ∑' w : Site, A w * G w := hconv
    _ = ∑ w ∈ E, A w * G w := by
      apply tsum_eq_sum
      intro w hw
      simp [hGzero w hw]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      rfl

private theorem slabSmoothedTest_local_error (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {s s' : ℝ} (_hs : 0 ≤ s) (_hss' : s ≤ s') (Φ : C_c(Plane × Plane, ℝ))
    (y z : Plane) (q r δ lam c : ℝ) (hq : 0 ≤ q)
    (hmod : ∀ x, dist x y < δ → |Φ (x, z) - Φ (y, z)| ≤ q / 4)
    (hnear : r + 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ < δ)
    (hlocal : 2 * ‖Φ.toBoundedContinuousFunction‖ *
      (c * Real.exp (-lam * r / 2)) ≤ q / 4)
    (htail : ∑ w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y)
        (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)),
      (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
          ‖siteToPlane (w - latticePoint N y)‖ then 1 else 0) *
        Critical2DKPZ.srwKernel
          (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
          (latticePoint N y - w) ≤ c * Real.exp (-lam * r / 2)) :
    |slabSmoothedTest ϑ N s s' Φ y z - Φ (y, z)| ≤ q / 2 := by
  classical
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  let v := latticePoint N y
  let E := Critical2DKPZ.Polymer.endpoints v m
  let G : Site → ℝ := fun w => Critical2DKPZ.srwKernel m (v - w)
  let A : Site → ℝ := fun w => (N : ℝ) / 4 * (∫ x in cell N w, Φ (x, z))
  have hGnonneg (w : Site) : 0 ≤ G w := by
    dsimp [G]
    exact Critical2DKPZ.Polymer.kernel_nonneg m (v - w)
  have hGzero (w : Site) (hw : w ∉ E) : G w = 0 := by
    dsimp [G, E, v, m]
    rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
    exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem _ _ _ hw
  have hGsum : (∑ w ∈ E, G w) = 1 := by
    have htsum : (∑' w : Site, G w) = ∑ w ∈ E, G w := by
      apply tsum_eq_sum
      intro w hw
      exact hGzero w hw
    rw [← htsum]
    have hEq : (fun w : Site => G w) = fun w =>
        Critical2DKPZ.srwKernel m (w - v) := by
      funext w
      dsimp [G]
      exact Critical2DKPZ.Polymer.srwKernel_sub_swap m v w
    rw [hEq]
    exact Critical2DKPZ.Polymer.tsum_srwKernel m v
  have hconv : slabSmoothedTest ϑ N s s' Φ y z =
      ∑' w : Site, A w * G w := by
    change (∫ x, Φ (x, z) * slabMeanKernel ϑ N s s' x y) = _
    rw [slabMeanKernel_test_eq_cellTsum]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro w
    dsimp [A, G, v, m]
    ring
  have hconvFinite : slabSmoothedTest ϑ N s s' Φ y z = ∑ w ∈ E, A w * G w := by
    rw [hconv]
    have htsum : (∑' w : Site, A w * G w) = ∑ w ∈ E, A w * G w := by
      apply tsum_eq_sum
      intro w hw
      simp [hGzero w hw]
    exact htsum
  have hΦsum : Φ (y, z) = ∑ w ∈ E, Φ (y, z) * G w := by
    calc
      Φ (y, z) = Φ (y, z) * 1 := by ring
      _ = Φ (y, z) * ∑ w ∈ E, G w := by rw [hGsum]
      _ = _ := by rw [Finset.mul_sum]
  have hdiff : slabSmoothedTest ϑ N s s' Φ y z - Φ (y, z) =
      ∑ w ∈ E, (A w - Φ (y, z)) * G w := by
    calc
      slabSmoothedTest ϑ N s s' Φ y z - Φ (y, z) =
          (∑ w ∈ E, A w * G w) - Φ (y, z) := by rw [hconvFinite]
      _ = (∑ w ∈ E, A w * G w) -
          Φ (y, z) * (∑ w ∈ E, G w) := by
        rw [hGsum]
        ring
      _ = (∑ w ∈ E, A w * G w) - ∑ w ∈ E, Φ (y, z) * G w := by
        congr 1
        rw [Finset.mul_sum]
      _ = ∑ w ∈ E, (A w - Φ (y, z)) * G w := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        ring
  have hMnonneg : 0 ≤ ‖Φ.toBoundedContinuousFunction‖ := norm_nonneg _
  have hΦbound : |Φ (y, z)| ≤ ‖Φ.toBoundedContinuousFunction‖ := by
    change |Φ.toBoundedContinuousFunction (y, z)| ≤ _
    exact Φ.toBoundedContinuousFunction.norm_coe_le_norm (y, z)
  have hterm (w : Site) (hw : w ∈ E) :
      |(A w - Φ (y, z)) * G w| ≤
        q / 4 * G w + 2 * ‖Φ.toBoundedContinuousFunction‖ *
          (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖ then 1 else 0) * G w := by
    let d := (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖
    by_cases hd : d ≤ r
    · have hcell := slabCellAverage_near hN Φ y z w (q / 4) δ r
        hmod hnear (by simpa [v, m, E] using hw) (by simpa [d] using hd)
      rw [abs_mul, abs_of_nonneg (hGnonneg w)]
      calc
        |A w - Φ (y, z)| * G w ≤ q / 4 * G w :=
          mul_le_mul_of_nonneg_right hcell (hGnonneg w)
        _ = q / 4 * G w + 2 * ‖Φ.toBoundedContinuousFunction‖ *
            (if r < d then 1 else 0) * G w := by simp [not_lt_of_ge hd]
    · have hrd : r < d := lt_of_not_ge hd
      have hAabs : |A w| ≤ ‖Φ.toBoundedContinuousFunction‖ := by
        dsimp [A]
        exact slabCellAverage_abs_le hN Φ z w
          (by
            have hmEven : Even m :=
              Critical2DKPZ.SHF.Moments.even_evenCeil_sub ((N : ℝ) * s) ((N : ℝ) * s')
            exact Critical2DKPZ.SHF.Flow.even_mem_endpoints_of_even
              (Critical2DKPZ.latticePoint_mem_evenLattice N y) hmEven hw)
      have hdiffabs : |A w - Φ (y, z)| ≤ 2 * ‖Φ.toBoundedContinuousFunction‖ := by
        calc
          |A w - Φ (y, z)| ≤ |A w| + |Φ (y, z)| := abs_sub _ _
          _ ≤ _ := add_le_add hAabs hΦbound
          _ = _ := by ring
      rw [abs_mul, abs_of_nonneg (hGnonneg w)]
      have hqG : 0 ≤ q / 4 * G w := mul_nonneg (by positivity) (hGnonneg w)
      calc
        |A w - Φ (y, z)| * G w ≤ 2 * ‖Φ.toBoundedContinuousFunction‖ * G w :=
          mul_le_mul_of_nonneg_right hdiffabs (hGnonneg w)
        _ ≤ q / 4 * G w + 2 * ‖Φ.toBoundedContinuousFunction‖ *
            (if r < d then 1 else 0) * G w := by
          simp [hrd]
          nlinarith [mul_nonneg (by positivity : 0 ≤ q / 4) (hGnonneg w)]
  have hsumBound :
      |∑ w ∈ E, (A w - Φ (y, z)) * G w| ≤
        q / 4 + 2 * ‖Φ.toBoundedContinuousFunction‖ *
          ∑ w ∈ E,
            (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖ then 1 else 0) * G w := by
    calc
      _ ≤ ∑ w ∈ E, |(A w - Φ (y, z)) * G w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ E, (q / 4 * G w + 2 * ‖Φ.toBoundedContinuousFunction‖ *
          (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖ then 1 else 0) * G w) := by
        apply Finset.sum_le_sum
        intro w hw
        simpa [v] using hterm w hw
      _ = q / 4 + 2 * ‖Φ.toBoundedContinuousFunction‖ *
          ∑ w ∈ E,
            (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖ then 1 else 0) * G w := by
        have hnearFactor :
            ∑ w ∈ E, (q / 4) * G w = q / 4 := by
          rw [← Finset.mul_sum, hGsum]
          ring
        have htailFactor :
            ∑ w ∈ E,
              (2 * ‖Φ.toBoundedContinuousFunction‖ *
                (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
                  ‖siteToPlane (w - v)‖ then 1 else 0)) * G w =
              2 * ‖Φ.toBoundedContinuousFunction‖ *
                ∑ w ∈ E,
                  (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
                    ‖siteToPlane (w - v)‖ then 1 else 0) * G w := by
          calc
            _ = ∑ w ∈ E, 2 * ‖Φ.toBoundedContinuousFunction‖ *
                ((if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
                  ‖siteToPlane (w - v)‖ then 1 else 0) * G w) := by
              apply Finset.sum_congr rfl
              intro w hw
              ring
            _ = _ := by rw [Finset.mul_sum]
        rw [Finset.sum_add_distrib, hnearFactor, htailFactor]
  have htail' :
      ∑ w ∈ E,
        (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖ then 1 else 0) * G w ≤
        c * Real.exp (-lam * r / 2) := by
    simpa [E, G, v, m] using htail
  calc
    |slabSmoothedTest ϑ N s s' Φ y z - Φ (y, z)| =
        |∑ w ∈ E, (A w - Φ (y, z)) * G w| := by rw [hdiff]
    _ ≤ q / 4 + 2 * ‖Φ.toBoundedContinuousFunction‖ *
        ∑ w ∈ E,
          (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (w - v)‖ then 1 else 0) * G w := hsumBound
    _ ≤ q / 4 + 2 * ‖Φ.toBoundedContinuousFunction‖ * (c * Real.exp (-lam * r / 2)) := by
      gcongr
    _ ≤ q / 2 := by linarith

private theorem srwKernel_exp_moment_start_le :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (a : Site) (m : ℕ) (lam : ℝ), (hlam : 0 ≤ lam) →
      ∑ z ∈ Critical2DKPZ.Polymer.endpoints a m,
        Real.exp (lam * ‖siteToPlane (z - a)‖) *
        Critical2DKPZ.srwKernel m (z - a) ≤ c * Real.exp (2 * c * lam ^ 2 * m) := by
  obtain ⟨c, hc, hmgf⟩ := Critical2DKPZ.MomentBounds.tsum_exp_mul_norm_srwKernel_le
  refine ⟨c, hc, ?_⟩
  intro a m lam hlam
  let f : Site → ℝ := fun z => Real.exp (lam * ‖siteToPlane z‖) *
    Critical2DKPZ.srwKernel m z
  have htranslate :
      ∑ z ∈ Critical2DKPZ.Polymer.endpoints a m, f (z - a) =
        ∑ z ∈ Critical2DKPZ.Polymer.endpoints 0 m, f z := by
    refine Finset.sum_bij (fun z _ => z - a) ?_ ?_ ?_ ?_
    · intro z hz
      obtain ⟨p, hp⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff a z m).mp hz
      apply (Critical2DKPZ.Polymer.mem_endpoints_iff 0 (z - a) m).mpr
      refine ⟨p, ?_⟩
      rw [Critical2DKPZ.Polymer.walkPosition_eq_start_add] at hp ⊢
      have hp' := congrArg (fun x : Site => x - a) hp
      simpa only [add_sub_cancel_left, zero_add] using hp'
    · intro z₁ hz₁ z₂ hz₂ heq
      apply funext
      intro i
      have hi := congrArg (fun x : Site => x i) heq
      simp only [Pi.sub_apply] at hi
      omega
    · intro z hz
      obtain ⟨p, hp⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff 0 z m).mp hz
      refine ⟨a + z, (Critical2DKPZ.Polymer.mem_endpoints_iff a (a + z) m).mpr ?_, ?_⟩
      · refine ⟨p, ?_⟩
        rw [Critical2DKPZ.Polymer.walkPosition_eq_start_add] at ⊢
        have hp' := congrArg (fun x : Site => a + x) hp
        exact hp'
      · simp
    · intro z hz
      rfl
  have hfinite :
      (∑ z ∈ Critical2DKPZ.Polymer.endpoints 0 m, f z) = ∑' z : Site, f z := by
    symm
    apply tsum_eq_sum
    intro z hz
    have hzero := Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem m 0 z
      (by simpa only [Critical2DKPZ.Polymer.endpoints] using hz)
    have hzero' : Critical2DKPZ.srwKernel m z = 0 := by simpa using hzero
    simp [f, hzero']
  calc
    _ = ∑ z ∈ Critical2DKPZ.Polymer.endpoints 0 m, f z := htranslate
    _ = ∑' z : Site, f z := hfinite
    _ ≤ c * Real.exp (2 * c * lam ^ 2 * m) := by
      simpa only [f] using (hmgf lam hlam m).1

private theorem srwKernel_scaledTail_exp_le :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (v : Site) (N : ℕ)
      (m : ℕ) (lam r : ℝ), (hlam : 0 ≤ lam) →
      ∑ w ∈ Critical2DKPZ.Polymer.endpoints v m,
        (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
            ‖siteToPlane (w - v)‖ then 1 else 0) *
          Critical2DKPZ.srwKernel m (v - w) ≤
          c * Real.exp (2 * c * (lam * (Real.sqrt ((N : ℝ) / 2))⁻¹) ^ 2 * m - lam * r) := by
  obtain ⟨c, hc, hstart⟩ := srwKernel_exp_moment_start_le
  refine ⟨c, hc, ?_⟩
  intro v N m lam r hlam
  let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hmoment := hstart v m (lam * scale) (mul_nonneg hlam hscale)
  have hmoment' :
      ∑ w ∈ Critical2DKPZ.Polymer.endpoints v m,
        Real.exp ((lam * scale) * ‖siteToPlane (w - v)‖) *
          Critical2DKPZ.srwKernel m (v - w) ≤
        c * Real.exp (2 * c * (lam * scale) ^ 2 * m) := by
    calc
      _ = ∑ w ∈ Critical2DKPZ.Polymer.endpoints v m,
          Real.exp ((lam * scale) * ‖siteToPlane (w - v)‖) *
            Critical2DKPZ.srwKernel m (w - v) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
      _ ≤ c * Real.exp (2 * c * (lam * scale) ^ 2 * m) := hmoment
  calc
    _ ≤ Real.exp (-lam * r) *
        ∑ w ∈ Critical2DKPZ.Polymer.endpoints v m,
          Real.exp ((lam * scale) * ‖siteToPlane (w - v)‖) *
            Critical2DKPZ.srwKernel m (v - w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w hw
      by_cases htail : r < scale * ‖siteToPlane (w - v)‖
      · have hprob : 0 ≤ Critical2DKPZ.srwKernel m (v - w) :=
          Critical2DKPZ.Polymer.kernel_nonneg m (v - w)
        have hdiff : 0 ≤ scale * ‖siteToPlane (w - v)‖ - r :=
          le_of_lt (sub_pos.mpr htail)
        have hexp : 1 ≤ Real.exp (-lam * r) *
            Real.exp ((lam * scale) * ‖siteToPlane (w - v)‖) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have hmul := mul_nonneg hlam hdiff
          nlinarith [hmul]
        calc
          (if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) *
              Critical2DKPZ.srwKernel m (v - w) =
              1 * Critical2DKPZ.srwKernel m (v - w) := by simp [htail]
          _ ≤ (Real.exp (-lam * r) *
              Real.exp ((lam * scale) * ‖siteToPlane (w - v)‖)) *
              Critical2DKPZ.srwKernel m (v - w) :=
            mul_le_mul_of_nonneg_right hexp hprob
          _ = Real.exp (-lam * r) *
              (Real.exp ((lam * scale) * ‖siteToPlane (w - v)‖) *
                Critical2DKPZ.srwKernel m (v - w)) := by ring
      · have hprob : 0 ≤ Critical2DKPZ.srwKernel m (v - w) :=
          Critical2DKPZ.Polymer.kernel_nonneg m (v - w)
        have hleft : (if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) *
            Critical2DKPZ.srwKernel m (v - w) = 0 := by simp [htail]
        rw [hleft]
        exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _) hprob)
    _ ≤ Real.exp (-lam * r) *
        (c * Real.exp (2 * c * (lam * scale) ^ 2 * m)) :=
      mul_le_mul_of_nonneg_left hmoment' (Real.exp_nonneg _)
    _ = c * (Real.exp (-lam * r) *
        Real.exp (2 * c * (lam * scale) ^ 2 * m)) := by ring
    _ = c * Real.exp (2 * c * (lam * scale) ^ 2 * m - lam * r) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- There is a constant `c ≥ 1` such that, for every `N > 0`, `0 ≤ s ≤ s'`, `y`, `lam ≥ 0` and `r`,
the walk-kernel mass of the endpoints `w` with `r < ‖siteToPlane (w - latticePoint N y)‖` scaled
by `(√(N / 2))⁻¹` is at most `c * exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * r)`. -/
theorem slabEndpoint_tail_le :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ {N : ℕ} (_hN : 0 < N) {s s' : ℝ}
      (_hs : 0 ≤ s) (_hss' : s ≤ s') (y : Plane) (lam r : ℝ), (hlam : 0 ≤ lam) →
      ∑ w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y)
          (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)),
        (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
            ‖siteToPlane (w - latticePoint N y)‖ then 1 else 0) *
          Critical2DKPZ.srwKernel
            (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
            (latticePoint N y - w) ≤
        c * Real.exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * r) := by
  obtain ⟨c, hc, htail⟩ := srwKernel_scaledTail_exp_le
  refine ⟨c, hc, ?_⟩
  intro N hN s s' hs hss' y lam r hlam
  let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  have hscaleSq : scale ^ 2 = 2 / (N : ℝ) := by
    dsimp [scale]
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
    field_simp
  have hm := slabStepCount_le hN hs hss'
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hExp : 2 * c * (lam * scale) ^ 2 * m ≤
      4 * c * lam ^ 2 * (s' - s + 2 / (N : ℝ)) := by
    have hnonneg : 0 ≤ 4 * c * lam ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hm hnonneg
    calc
      2 * c * (lam * scale) ^ 2 * m =
          4 * c * lam ^ 2 * (m / (N : ℝ)) := by
        rw [mul_pow, hscaleSq]
        field_simp
        ring
      _ ≤ 4 * c * lam ^ 2 * (s' - s + 2 / (N : ℝ)) := hmul
  calc
    _ ≤ c * Real.exp (2 * c * (lam * scale) ^ 2 * m - lam * r) :=
      htail (latticePoint N y) N m lam r hlam
    _ ≤ c * Real.exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (by linarith)

private theorem slabSmoothedTest_far_bound (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (hscaleLt : (Real.sqrt ((N : ℝ) / 2))⁻¹ < 1 / 2)
    {s s' : ℝ} (Φ : C_c(Plane × Plane, ℝ))
    {R : ℝ} (hR : ∀ x z, Φ (x, z) ≠ 0 → ‖x‖ ≤ R ∧ ‖z‖ ≤ R)
    (y z : Plane) (hyfar : R + 2 < ‖y‖)
    (lam c : ℝ) (hlamge4 : 4 ≤ lam) (hc : 1 ≤ c)
    (hgap : 4 * c * lam ^ 2 * (s' - s + 2 / N) ≤ lam / 2)
    (htail : ∀ r, 0 ≤ r →
      ∑ w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y)
          (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)),
        (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
            ‖siteToPlane (w - latticePoint N y)‖ then 1 else 0) *
          Critical2DKPZ.srwKernel
            (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
            (latticePoint N y - w) ≤
        c * Real.exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * r)) :
    |slabSmoothedTest ϑ N s s' Φ y z| ≤
      ‖Φ.toBoundedContinuousFunction‖ *
        (c * Real.exp (-lam * (‖y‖ - R - 1) / 2)) := by
  classical
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  let v := latticePoint N y
  let E := Critical2DKPZ.Polymer.endpoints v m
  let scale := (Real.sqrt ((N : ℝ) / 2))⁻¹
  let r := ‖y‖ - R - 1
  let M := ‖Φ.toBoundedContinuousFunction‖
  let A : Site → ℝ := fun w => (N : ℝ) / 4 * (∫ x in cell N w, Φ (x, z))
  let G : Site → ℝ := fun w => Critical2DKPZ.srwKernel m (v - w)
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hscale_lt : scale < 1 / 2 := by simpa [scale] using hscaleLt
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hGnonneg (w : Site) : 0 ≤ G w := by
    dsimp [G]
    exact Critical2DKPZ.Polymer.kernel_nonneg m (v - w)
  have hGzero (w : Site) (hw : w ∉ E) : G w = 0 := by
    dsimp [G, E, v, m]
    rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
    exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem _ _ _ hw
  have hAabs (w : Site) (hw : w ∈ E) : |A w| ≤ M := by
    dsimp [A, M]
    exact slabCellAverage_abs_le hN Φ z w (by
      have hmEven : Even m :=
        Critical2DKPZ.SHF.Moments.even_evenCeil_sub ((N : ℝ) * s) ((N : ℝ) * s')
      exact Critical2DKPZ.SHF.Flow.even_mem_endpoints_of_even
        (Critical2DKPZ.latticePoint_mem_evenLattice N y) hmEven hw)
  have hApoint (w : Site) (hAw : A w ≠ 0) :
      ∃ x, x ∈ cell N w ∧ Φ (x, z) ≠ 0 := by
    by_contra h
    push Not at h
    have hae : (fun x : Plane => Φ (x, z)) =ᵐ[volume.restrict (cell N w)] 0 := by
      filter_upwards [ae_restrict_mem (Critical2DKPZ.measurableSet_cell N w)] with x hx
      exact h x hx
    have hzero : ∫ x in cell N w, Φ (x, z) = 0 := by
      calc
        _ = ∫ x in cell N w, (0 : ℝ) := integral_congr_ae hae
        _ = 0 := by simp
    apply hAw
    simp [A, hzero]
  have hterm (w : Site) (hw : w ∈ E) :
      |A w * G w| ≤ M *
        ((if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) * G w) := by
    rw [abs_mul, abs_of_nonneg (hGnonneg w)]
    by_cases hAw : A w = 0
    · rw [hAw]
      by_cases hevent : r < scale * ‖siteToPlane (w - v)‖
      · simp [hevent]
        exact mul_nonneg hM (hGnonneg w)
      · simp [hevent]
    · obtain ⟨x, hx, hΦx⟩ := hApoint w hAw
      have hxR := (hR x z hΦx).1
      have hdist := dist_le_cellEndpoint N hN x y w v hx
        (Critical2DKPZ.mem_cell_latticePoint N y)
      have hnormLower : ‖y‖ ≤ dist x y + ‖x‖ := by
        simpa only [dist_eq_norm, norm_sub_rev] using norm_le_norm_sub_add y x
      have hevent : r < scale * ‖siteToPlane (w - v)‖ := by
        dsimp [r, scale] at *
        linarith
      have hMbound := hAabs w hw
      have hindicator : (if r < scale * ‖siteToPlane (w - v)‖ then (1 : ℝ) else 0) = 1 := by
        simp [hevent]
      have hfactor :
          (if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) * G w = G w := by
        calc
          _ = 1 * G w := congrArg (fun a : ℝ => a * G w) hindicator
          _ = G w := one_mul _
      have hfactor' := congrArg (fun a : ℝ => M * a) hfactor
      exact (mul_le_mul_of_nonneg_right hMbound (hGnonneg w)).trans hfactor'.symm.le
  have htail' :
      ∑ w ∈ E,
        (if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) * G w ≤
        c * Real.exp (-lam * r / 2) := by
    have htail0 := htail r (by dsimp [r]; linarith)
    calc
      _ ≤ c * Real.exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * r) := by
        simpa [E, G, v, m, scale] using htail0
      _ ≤ c * Real.exp (-lam * r / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        have hrhalf : lam / 2 ≤ lam * r / 2 := by
          have := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ lam / 2)
          nlinarith
        linarith
  have hsum : |∑ w ∈ E, A w * G w| ≤ M *
      ∑ w ∈ E, (if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) * G w := by
    calc
      _ ≤ ∑ w ∈ E, |A w * G w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ E, M *
          ((if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) * G w) := by
        apply Finset.sum_le_sum
        intro w hw
        exact hterm w hw
      _ = M * ∑ w ∈ E,
          (if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) * G w := by
        rw [Finset.mul_sum]
  have hrep := slabSmoothedTest_endpoint_sum ϑ (N := N) s s' Φ y z
  calc
    |slabSmoothedTest ϑ N s s' Φ y z| = |∑ w ∈ E, A w * G w| := by
      rw [hrep]
    _ ≤ M * (c * Real.exp (-lam * r / 2)) := by
      calc
        _ ≤ M * ∑ w ∈ E,
            (if r < scale * ‖siteToPlane (w - v)‖ then 1 else 0) * G w := hsum
        _ ≤ M * (c * Real.exp (-lam * r / 2)) := by gcongr
    _ = ‖Φ.toBoundedContinuousFunction‖ *
        (c * Real.exp (-lam * (‖y‖ - R - 1) / 2)) := by rfl

/-- The slab average of a compact test approaches that test uniformly after weighting by the
exponential envelope, as the slab duration and lattice mesh go to zero. -/
theorem slabMeanKernel_test_weighted_error (ϑ : ℝ) (Φ : C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∃ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ s s' : ℝ, ∀ y z : Plane,
      0 ≤ s → s ≤ s' → s' - s ≤ η →
        |slabSmoothedTest ϑ N s s' Φ y z - Φ (y, z)| ≤
          ε * Real.exp (-(‖y‖ + ‖z‖)) := by
  intro ε hε
  obtain ⟨R, _hRnonneg, hR⟩ := slabTest_support_radius Φ
  obtain ⟨c, hc, hTail⟩ := slabEndpoint_tail_le
  let M := ‖Φ.toBoundedContinuousFunction‖
  let q := ε * Real.exp (-(2 * R + 2))
  obtain ⟨δ, hδ, hδmod⟩ :=
    (Metric.uniformContinuous_iff.mp
      (CompactlySupportedContinuousMapClass.uniformContinuous Φ)) (q / 4) (by positivity)
  let r := δ / 4
  let Hfar := max 1 (2 * M * c / ε)
  let Hloc := max 1 (8 * M * c / q)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hHfar : 0 < Hfar := by dsimp [Hfar]; positivity
  have hHloc : 0 < Hloc := by dsimp [Hloc]; positivity
  have hHfarMax : 2 * M * c / ε ≤ Hfar := by dsimp [Hfar]; exact le_max_right _ _
  have hHlocMax : 8 * M * c / q ≤ Hloc := by dsimp [Hloc]; exact le_max_right _ _
  let Lfar := 2 * (2 * R + 2 + Real.log Hfar)
  let Lloc := 2 * Real.log Hloc / r
  let lam := max 4 (max Lfar Lloc)
  have hLamFar : Lfar ≤ lam := by
    calc
      Lfar ≤ max Lfar Lloc := le_max_left _ _
      _ ≤ max 4 (max Lfar Lloc) := le_max_right _ _
  have hLamLoc : Lloc ≤ lam := by
    calc
      Lloc ≤ max Lfar Lloc := le_max_right _ _
      _ ≤ max 4 (max Lfar Lloc) := le_max_right _ _
  have hLamge4 : 4 ≤ lam := by dsimp [lam]; exact le_max_left _ _
  have hLampos : 0 < lam := by linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hlam : 0 ≤ lam := le_of_lt hLampos
  have hlogfar : 2 * R + 2 - lam / 2 ≤ -Real.log Hfar := by
    dsimp [Lfar] at hLamFar
    linarith
  have hlogloc : Real.log Hloc ≤ lam * r / 2 := by
    have hLamLoc' : 2 * Real.log Hloc / r ≤ lam := by simpa [Lloc] using hLamLoc
    have hdiv := (div_le_iff₀ hrpos).mp hLamLoc'
    nlinarith
  have hfarRatio : M * c / Hfar ≤ ε / 2 := by
    have hmul₀ : 2 * M * c ≤ Hfar * ε := (div_le_iff₀ hε).mp hHfarMax
    have hmul : 2 * M * c ≤ ε * Hfar := by nlinarith [hmul₀]
    apply (div_le_iff₀ hHfar).2
    nlinarith
  have hlocalRatio : M * c / Hloc ≤ q / 8 := by
    have hmul₀ : 8 * M * c ≤ Hloc * q := (div_le_iff₀ hq).mp hHlocMax
    have hmul : 8 * M * c ≤ q * Hloc := by nlinarith [hmul₀]
    apply (div_le_iff₀ hHloc).2
    nlinarith
  have hfarConstant : M * c * Real.exp (2 * R + 2 - lam / 2) ≤ ε / 2 := by
    calc
      _ ≤ M * c * Real.exp (-Real.log Hfar) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hlogfar) (mul_nonneg hM (by positivity))
      _ = M * c / Hfar := by
        rw [Real.exp_neg, Real.exp_log hHfar]
        ring
      _ ≤ ε / 2 := hfarRatio
  have hlocalConstant : 2 * M * (c * Real.exp (-lam * r / 2)) ≤ q / 4 := by
    have hexp : Real.exp (-lam * r / 2) ≤ Real.exp (-Real.log Hloc) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ = 2 * (M * c) * Real.exp (-lam * r / 2) := by ring
      _ ≤ 2 * (M * c) * Real.exp (-Real.log Hloc) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 2 * (M * c / Hloc) := by
        rw [Real.exp_neg, Real.exp_log hHloc]
        ring
      _ ≤ q / 4 := by linarith [hlocalRatio]
  let K := min (lam * r / 2) (lam / 2)
  have hKpos : 0 < K := by
    dsimp [K]
    exact lt_min (by positivity) (by positivity)
  have hKfar : K ≤ lam / 2 := min_le_right _ _
  have hKlocal : K ≤ lam * r / 2 := min_le_left _ _
  let η := K / (8 * c * lam ^ 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hInv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hroundTendsto : Tendsto (fun N : ℕ => 2 / (N : ℝ)) atTop (𝓝 0) := by
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    simpa [div_eq_mul_inv] using htwo.mul hInv
  have hmeshTarget : 0 < min (δ / 4) (1 / 2) :=
    lt_min (by positivity) (by norm_num)
  have hmeshEventually : ∀ᶠ N : ℕ in atTop,
      (Real.sqrt ((N : ℝ) / 2))⁻¹ < min (δ / 4) (1 / 2) :=
    Critical2DKPZ.tendsto_lattice_mesh.eventually (gt_mem_nhds hmeshTarget)
  have hroundEventually : ∀ᶠ N : ℕ in atTop,
      2 / (N : ℝ) < K / (8 * c * lam ^ 2) :=
    hroundTendsto.eventually (gt_mem_nhds (by positivity))
  have hpositiveEventually : ∀ᶠ N : ℕ in atTop, 1 ≤ N := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    exact hN
  have hgoodEventually : ∀ᶠ N : ℕ in atTop,
      (Real.sqrt ((N : ℝ) / 2))⁻¹ < min (δ / 4) (1 / 2) ∧
        2 / (N : ℝ) < K / (8 * c * lam ^ 2) ∧ 1 ≤ N := by
    filter_upwards [hmeshEventually, hroundEventually, hpositiveEventually] with N hmesh hround hN
    exact ⟨hmesh, hround, hN⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hgoodEventually
  refine ⟨η, hη, max N₁ 1, ?_⟩
  intro N hN s s' y z hs hss' hgap
  have hgood := hN₁ N (le_trans (le_max_left N₁ 1) hN)
  rcases hgood with ⟨hmesh, hround, hNpositive⟩
  have hN : 0 < N := by omega
  have hscaleδ : (Real.sqrt ((N : ℝ) / 2))⁻¹ < δ / 4 :=
    lt_of_lt_of_le hmesh (min_le_left _ _)
  have hscaleHalf : (Real.sqrt ((N : ℝ) / 2))⁻¹ < 1 / 2 :=
    lt_of_lt_of_le hmesh (min_le_right _ _)
  have hroundη : 2 / (N : ℝ) ≤ η := by
    dsimp [η]
    exact hround.le
  have hgapRound : s' - s + 2 / (N : ℝ) ≤ η + η := by
    exact add_le_add hgap hroundη
  have hgapExp : 4 * c * lam ^ 2 * (s' - s + 2 / (N : ℝ)) ≤ K := by
    calc
      _ ≤ 4 * c * lam ^ 2 * (η + η) :=
        mul_le_mul_of_nonneg_left hgapRound (by positivity)
      _ = K := by dsimp [η]; field_simp; ring
  have hmodulus : ∀ x y' z', dist x y' < δ →
      |Φ (x, z') - Φ (y', z')| ≤ q / 4 := by
    intro x y' z' hxy
    have hpair : dist (x, z') (y', z') < δ := by
      simpa only [dist_prod_same_right] using hxy
    have hmod := hδmod hpair
    have hmodle : dist (Φ (x, z')) (Φ (y', z')) ≤ q / 4 := hmod.le
    simpa only [Real.dist_eq] using hmodle
  have hzeroSection (z' : Plane) (hz' : R < ‖z'‖) (x : Plane) :
      Φ (x, z') = 0 := by
    by_contra hne
    exact (not_le_of_gt hz') (hR x z' hne).2
  have hweightLocal (y' z' : Plane) (hy' : ‖y'‖ ≤ R + 2) (hz' : ‖z'‖ ≤ R) :
      q / 2 ≤ ε * Real.exp (-(‖y'‖ + ‖z'‖)) := by
    have hsum : ‖y'‖ + ‖z'‖ ≤ 2 * R + 2 := by linarith
    have hexp : Real.exp (-(2 * R + 2)) ≤ Real.exp (-(‖y'‖ + ‖z'‖)) :=
      Real.exp_le_exp.mpr (by linarith)
    dsimp [q]
    calc
      ε * Real.exp (-(2 * R + 2)) / 2 =
          (ε / 2) * Real.exp (-(2 * R + 2)) := by ring
      _ ≤ ε * Real.exp (-(‖y'‖ + ‖z'‖)) :=
        mul_le_mul (by linarith) hexp (Real.exp_nonneg _) (by positivity)
  have htailAt (y' : Plane) (ρ : ℝ) (hρ : 0 ≤ ρ) :
      ∑ w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y')
          (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)),
        (if ρ < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
            ‖siteToPlane (w - latticePoint N y')‖ then 1 else 0) *
          Critical2DKPZ.srwKernel
            (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
            (latticePoint N y' - w) ≤
        c * Real.exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * ρ) := by
    exact hTail (N := N) hN (s := s) (s' := s') hs hss' y' lam ρ hlam
  by_cases hzR : ‖z‖ ≤ R
  · by_cases hyR : ‖y‖ ≤ R + 2
    · have hnear : r + 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ < δ := by
        dsimp [r]
        linarith [hδ]
      have htailLocal :
          ∑ w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y)
              (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)),
              (if r < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
                ‖siteToPlane (w - latticePoint N y)‖ then 1 else 0) *
              Critical2DKPZ.srwKernel
                (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
                (latticePoint N y - w) ≤ c * Real.exp (-lam * r / 2) := by
        calc
          _ ≤ c * Real.exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * r) :=
            htailAt y r (by positivity)
          _ ≤ c * Real.exp (-lam * r / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp.mpr
            have := hgapExp.trans hKlocal
            linarith
      have hlocalError := slabSmoothedTest_local_error ϑ hN hs hss' Φ y z q r
        δ lam c (by positivity) (hmodulus · y z) hnear hlocalConstant htailLocal
      calc
        |slabSmoothedTest ϑ N s s' Φ y z - Φ (y, z)| ≤ q / 2 := hlocalError
        _ ≤ ε * Real.exp (-(‖y‖ + ‖z‖)) := hweightLocal y z hyR hzR
    · have hyfar : R + 2 < ‖y‖ := lt_of_not_ge hyR
      have hgapFar := hgapExp.trans hKfar
      have htailFar : ∀ ρ, 0 ≤ ρ →
          ∑ w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint N y)
              (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)),
            (if ρ < (Real.sqrt ((N : ℝ) / 2))⁻¹ *
                ‖siteToPlane (w - latticePoint N y)‖ then 1 else 0) *
              Critical2DKPZ.srwKernel
                (evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s))
                (latticePoint N y - w) ≤
            c * Real.exp (4 * c * lam ^ 2 * (s' - s + 2 / N) - lam * ρ) := by
        intro ρ hρ
        exact htailAt y ρ hρ
      have hfarError := slabSmoothedTest_far_bound ϑ hN hscaleHalf
        (s := s) (s' := s') Φ hR y z hyfar lam c hLamge4 hc hgapFar htailFar
      have hExpArg : ‖y‖ + ‖z‖ - lam * (‖y‖ - R - 1) / 2 ≤
          2 * R + 2 - lam / 2 := by
        have hcoef : 1 - lam / 2 ≤ 0 := by linarith
        have hYmul := mul_le_mul_of_nonpos_left (le_of_lt hyfar) hcoef
        calc
          _ = (1 - lam / 2) * ‖y‖ + ‖z‖ + lam / 2 * (R + 1) := by ring
          _ ≤ (1 - lam / 2) * (R + 2) + R + lam / 2 * (R + 1) :=
            add_le_add (add_le_add hYmul hzR) le_rfl
          _ = 2 * R + 2 - lam / 2 := by ring
      have hweighted : |slabSmoothedTest ϑ N s s' Φ y z| *
          Real.exp (‖y‖ + ‖z‖) ≤ ε / 2 := by
        calc
          _ ≤ (M * (c * Real.exp (-lam * (‖y‖ - R - 1) / 2))) *
              Real.exp (‖y‖ + ‖z‖) :=
            mul_le_mul_of_nonneg_right hfarError (Real.exp_nonneg _)
          _ = M * c * Real.exp (‖y‖ + ‖z‖ -
              lam * (‖y‖ - R - 1) / 2) := by
            calc
              _ = M * c * (Real.exp (-lam * (‖y‖ - R - 1) / 2) *
                  Real.exp (‖y‖ + ‖z‖)) := by ring
              _ = _ := by rw [← Real.exp_add]; congr 1; ring
          _ ≤ M * c * Real.exp (2 * R + 2 - lam / 2) := by
            gcongr
          _ ≤ ε / 2 := hfarConstant
      have hdiv : |slabSmoothedTest ϑ N s s' Φ y z| ≤
          ε / Real.exp (‖y‖ + ‖z‖) :=
        (le_div_iff₀ (Real.exp_pos _)).2 (hweighted.trans (by linarith))
      have hΦzero : Φ (y, z) = 0 := by
        by_contra hne
        have hY := (hR y z hne).1
        exact (not_le_of_gt (by linarith : R < ‖y‖)) hY
      calc
        |slabSmoothedTest ϑ N s s' Φ y z - Φ (y, z)| =
            |slabSmoothedTest ϑ N s s' Φ y z| := by rw [hΦzero, sub_zero]
        _ ≤ ε / Real.exp (‖y‖ + ‖z‖) := hdiv
        _ = ε * Real.exp (-(‖y‖ + ‖z‖)) := by
          rw [Real.exp_neg]
          simp [div_eq_mul_inv]
  · have hzfar : R < ‖z‖ := lt_of_not_ge hzR
    have hzero : ∀ x, Φ (x, z) = 0 := hzeroSection z hzfar
    have hzeroY := hzero y
    have hzeroSmoothed : slabSmoothedTest ϑ N s s' Φ y z = 0 := by
      simp [slabSmoothedTest, hzero]
    simp [hzeroSmoothed, hzeroY]
    positivity

/-- A pointwise bound `‖F p - G p‖ ≤ δ * H p` bounds the mean squared difference of the corresponding random-measure pairings by `δ ^ 2` times the envelope second moment, assuming both squared pairings are integrable. -/
theorem integral_sq_sub_le_scaled_envelope
    (F G H : Plane × Plane → ℝ) (μ : Disorder → Measure (Plane × Plane))
    (δ : ℝ) (hδ : 0 ≤ δ) (hHnonneg : ∀ p, 0 ≤ H p)
    (hpoint : ∀ p, ‖F p - G p‖ ≤ δ * H p)
    (hFG : ∀ᵐ ω ∂disorderLaw, Integrable F (μ ω) ∧ Integrable G (μ ω))
    (hH : ∀ᵐ ω ∂disorderLaw, Integrable H (μ ω))
    (hD : Integrable (fun ω => ((∫ p, F p ∂μ ω) - ∫ p, G p ∂μ ω) ^ 2)
      disorderLaw)
    (hE : Integrable (fun ω => (∫ p, H p ∂μ ω) ^ 2) disorderLaw) :
    ∫ ω, ((∫ p, F p ∂μ ω) - ∫ p, G p ∂μ ω) ^ 2 ∂disorderLaw ≤
      δ ^ 2 * ∫ ω, (∫ p, H p ∂μ ω) ^ 2 ∂disorderLaw := by
  have hpointwise : ∀ᵐ ω ∂disorderLaw,
      ((∫ p, F p ∂μ ω) - ∫ p, G p ∂μ ω) ^ 2 ≤
        δ ^ 2 * (∫ p, H p ∂μ ω) ^ 2 := by
    filter_upwards [hFG, hH] with ω hFGω hHω
    have hdiffInt : Integrable (fun p => F p - G p) (μ ω) := hFGω.1.sub hFGω.2
    have hdiff : |(∫ p, F p ∂μ ω) - ∫ p, G p ∂μ ω| ≤
        δ * ∫ p, H p ∂μ ω := by
      rw [← integral_sub hFGω.1 hFGω.2]
      calc
        |∫ p, (F p - G p) ∂μ ω| ≤ ∫ p, ‖F p - G p‖ ∂μ ω := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (f := fun p => F p - G p) (μ := μ ω)
        _ ≤ ∫ p, δ * H p ∂μ ω := by
          apply integral_mono hdiffInt.norm (hHω.const_mul δ)
          intro p
          exact hpoint p
        _ = δ * ∫ p, H p ∂μ ω := integral_const_mul δ H
    have hEω : 0 ≤ ∫ p, H p ∂μ ω := integral_nonneg_of_ae (Filter.Eventually.of_forall hHnonneg)
    have hdiff' : 0 ≤ |(∫ p, F p ∂μ ω) - ∫ p, G p ∂μ ω| := abs_nonneg _
    have hupper : 0 ≤ δ * ∫ p, H p ∂μ ω := mul_nonneg hδ hEω
    calc
      _ = |(∫ p, F p ∂μ ω) - ∫ p, G p ∂μ ω| ^ 2 := by rw [sq_abs]
      _ ≤ (δ * ∫ p, H p ∂μ ω) ^ 2 := (sq_le_sq₀ hdiff' hupper).2 hdiff
      _ = δ ^ 2 * (∫ p, H p ∂μ ω) ^ 2 := by ring
  calc
    _ ≤ ∫ ω, δ ^ 2 * (∫ p, H p ∂μ ω) ^ 2 ∂disorderLaw :=
      integral_mono_ae hD (hE.const_mul (δ ^ 2)) hpointwise
    _ = δ ^ 2 * ∫ ω, (∫ p, H p ∂μ ω) ^ 2 ∂disorderLaw := integral_const_mul _ _

/-- For `1 ≤ N` and all `s t`, for disorder-almost every `ω` the function
`p ↦ exp (-(‖p.1‖ + ‖p.2‖))` is integrable for the polymer measure `polymerMeasure ϑ N s t ω`. -/
theorem expEnvelope_integrable_ae (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t : ℝ) : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => Real.exp (-(‖p.1‖ + ‖p.2‖)))
        (polymerMeasure ϑ N s t ω) := by
  let f : Plane → ℝ := fun x => Real.exp (-‖x‖)
  have hf : Integrable f volume := by
    have hmajor := Critical2DKPZ.DeltaBose.integrable_exp_neg_planeOneNorm
      (show 0 < (Real.sqrt 2)⁻¹ by positivity)
    apply hmajor.mono' (Real.measurable_exp.comp (measurable_norm.neg)).aestronglyMeasurable
    filter_upwards [] with x
    have hone : 0 ≤ Critical2DKPZ.DeltaBose.planeOneNorm x :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsq := Critical2DKPZ.DeltaBose.planeOneNorm_sq_le x
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have haSq : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
      rw [inv_pow, hsqrt]
      norm_num
    have hnorm : (Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x ≤ ‖x‖ := by
      have hsq' : ((Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x) ^ 2 ≤ ‖x‖ ^ 2 :=
        by nlinarith [hsq, haSq]
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq'
    change ‖f x‖ ≤ Real.exp (-(Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (by nlinarith [hnorm])
  let H : Plane × Disorder → ℝ := fun q => f q.1 * rescaledP2Plane ϑ N s t q.1 q.2
  have hH : Integrable H (volume.prod disorderLaw) :=
    Critical2DKPZ.SHF.Limit.integrable_flatPairingProduct ϑ N s t hf
  have hslice := hH.swap.prod_right_ae
  filter_upwards [hslice] with ω hω
  have hslice' : Integrable (fun x : Plane => f x * rescaledP2Plane ϑ N s t x ω) volume := by
    simpa only [H, Prod.fst, Prod.snd, Function.comp_apply, Prod.swap_prod_mk] using hω
  have hdensity : Measurable (fun x : Plane => ENNReal.ofReal
      (rescaledP2Plane ϑ N s t x ω)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_uncurry_rescaledP2Plane ϑ N s t).of_uncurry_right
  have hmap : Integrable f ((polymerMeasure ϑ N s t ω).map Prod.fst) := by
    rw [map_fst_polymerMeasure ϑ hN s t ω]
    apply (integrable_withDensity_iff hdensity
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).2
    simpa only [ENNReal.toReal_ofReal
      (rescaledP2Plane_nonneg ϑ N s t _ _)] using hslice'
  have hweight : Measurable (fun p : Plane × Plane =>
      Real.exp (-(‖p.1‖ + ‖p.2‖))) := by fun_prop
  have hfmeas : Measurable f := by dsimp [f]; fun_prop
  have hFstInt : Integrable (fun p : Plane × Plane => f p.1)
      (polymerMeasure ϑ N s t ω) :=
    (integrable_map_measure hfmeas.aestronglyMeasurable measurable_fst.aemeasurable).mp hmap
  apply hFstInt.mono' hweight.aestronglyMeasurable
  filter_upwards [] with p
  change ‖Real.exp (-(‖p.1‖ + ‖p.2‖))‖ ≤ Real.exp (-‖p.1‖)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr (by linarith [norm_nonneg p.2])

/-- Moving-time two-replica convergence gives convergence of the second moment of one compact
polymer pairing along any nonnegative time sequences. -/
theorem polymerPairing_sq_tendsto_moving (ϑ : ℝ) (hPolymerMovingMomentInput : PolymerMovingMomentLimit ϑ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (sN tN : ℕ → ℝ)
    (hsN : Tendsto sN atTop (𝓝 s)) (htN : Tendsto tN atTop (𝓝 t))
    (hsN0 : ∀ N, 0 ≤ sN N) (Φ : C_c(Plane × Plane, ℝ)) :
    Tendsto (fun N => ∫ ω,
      (∫ p, Φ p ∂(polymerMeasure ϑ N (sN N) (tN N) ω)) ^ 2 ∂disorderLaw)
      atTop
      (𝓝 (∫ x : DeltaBose.Configuration 2, ∫ y : DeltaBose.Configuration 2,
        (∏ i, Φ (x i, y i)) *
          (DeltaBose.momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
  let φ : Fin 2 → C_c(Plane × Plane, ℝ) := fun _ => Φ
  have hmoving := hPolymerMovingMomentInput 2 (by norm_num) (by norm_num) hs hst sN tN hsN htN hsN0 φ
  have hpoint (N : ℕ) (ω : Disorder) :
      (∫ p, Φ p ∂(polymerMeasure ϑ N (sN N) (tN N) ω)) ^ 2 =
        ∏ i : Fin 2, ∫ p, φ i p *
          rescaledP2P ϑ N (sN N) (tN N) p ω := by
    rw [integral_polymerMeasure]
    simp [φ]
  have hseq :
      (fun N => ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N (sN N) (tN N) ω)) ^ 2
        ∂disorderLaw) =
      (fun N => ∫ ω, (∏ i : Fin 2, ∫ p, φ i p *
        rescaledP2P ϑ N (sN N) (tN N) p ω) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => hpoint N ω
  rw [hseq]
  exact hmoving

end Critical2DKPZ.SHF.TimeContinuity

end
