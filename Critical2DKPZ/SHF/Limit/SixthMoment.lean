/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.FlatBound
public import Critical2DKPZ.MomentBounds.CSZ25BlockMomentAssembly
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Critical2DKPZ.OnePoint.CriticalGap
public import Critical2DKPZ.Renewal.PolymerBridge
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Uniform flat-pairing sixth moments from CSZ25 -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators CompactlySupported Topology

noncomputable section

namespace Critical2DKPZ.SHF.Limit

private theorem integral_latticeStep_mul_eq_tsum_cell
    (N : ℕ) (f : Plane → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (G : Site → ℝ) :
    (∫ x : Plane, f x * G (latticePoint N x)) =
      ∑' z : Site, (∫ x in cell N z, f x) * G z := by
  classical
  let K : Set Plane := tsupport f
  have hK : IsCompact K := hfs
  let S : Set Site := latticePoint N '' K
  have hS : S.Finite := finite_latticePoint_image_of_bounded hK.isBounded
  let V : Set ℝ := (fun z : Site => |G z|) '' S
  have hV : V.Finite := hS.image _
  obtain ⟨B, hB⟩ := hV.bddAbove
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hprodMeas : Measurable (fun x : Plane => f x * G (latticePoint N x)) :=
    hf.measurable.mul ((measurable_of_countable G).comp (measurable_latticePoint N))
  have hbound (x : Plane) :
      ‖f x * G (latticePoint N x)‖ ≤ C * ‖f x‖ := by
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hxK : x ∈ K := subset_closure (Function.mem_support.mpr hfx)
      have hzS : latticePoint N x ∈ S := ⟨x, hxK, rfl⟩
      have hvalue : |G (latticePoint N x)| ≤ B := hB ⟨latticePoint N x, hzS, rfl⟩
      calc
        ‖f x * G (latticePoint N x)‖ = ‖f x‖ * |G (latticePoint N x)| := by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        _ ≤ ‖f x‖ * C := mul_le_mul_of_nonneg_left (hvalue.trans (le_max_left _ _)) (norm_nonneg _)
        _ = C * ‖f x‖ := by ring
  have hprod : Integrable (fun x : Plane => f x * G (latticePoint N x)) := by
    apply ((hf.integrable_of_hasCompactSupport hfs).norm.const_mul C).mono'
      hprodMeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall hbound
  have hcover : (⋃ z : Site, cell N z) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint N x, mem_cell_latticePoint N x⟩
  have hi := integral_iUnion (measurableSet_cell N) (pairwise_disjoint_cell N)
    hprod.integrableOn
  rw [hcover, setIntegral_univ] at hi
  rw [hi]
  apply tsum_congr
  intro z
  rw [setIntegral_congr_fun (measurableSet_cell N z) (fun x hx => ?_), integral_mul_const]
  rw [mem_cell_iff] at hx
  rw [hx]

private theorem profileSpread_pos_of_two_positive_sites
    (φ : Site → ℝ) (A : Finset Site) (hφA : ∀ z ∉ A, φ z = 0)
    (hφ : ∀ z, 0 ≤ φ z)
    {a b : Site} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hφa : 0 < φ a) (hφb : 0 < φ b) : 0 < MomentBounds.profileSpread φ := by
  rw [MomentBounds.profileSpread_eq_sum_of_support φ A hφA]
  have hsumNonneg (z : Site) (hz : z ∈ A) :
      0 ≤ ‖siteToPlane z - MomentBounds.profileMean φ‖ ^ 2 * φ z :=
    mul_nonneg (sq_nonneg _) (hφ z)
  have hsumNonneg' : 0 ≤ ∑ z ∈ A,
      ‖siteToPlane z - MomentBounds.profileMean φ‖ ^ 2 * φ z :=
    Finset.sum_nonneg fun z hz => hsumNonneg z hz
  by_contra hnot
  have hzero : (∑ z ∈ A,
      ‖siteToPlane z - MomentBounds.profileMean φ‖ ^ 2 * φ z) = 0 := by linarith
  have hterm (z : Site) (hz : z ∈ A) :
      ‖siteToPlane z - MomentBounds.profileMean φ‖ ^ 2 * φ z = 0 := by
    have hle := Finset.single_le_sum (f := fun z =>
      ‖siteToPlane z - MomentBounds.profileMean φ‖ ^ 2 * φ z)
      (fun w hw => hsumNonneg w hw) hz
    have hle' : ‖siteToPlane z - MomentBounds.profileMean φ‖ ^ 2 * φ z ≤
        ∑ w ∈ A, ‖siteToPlane w - MomentBounds.profileMean φ‖ ^ 2 * φ w := by
      simpa only [Finset.sum_attach] using hle
    exact le_antisymm (by simpa [hzero] using hle') (hsumNonneg z hz)
  have hmeanA : siteToPlane a = MomentBounds.profileMean φ := by
    have h := hterm a ha
    have hnorm : ‖siteToPlane a - MomentBounds.profileMean φ‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_right (ne_of_gt hφa)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  have hmeanB : siteToPlane b = MomentBounds.profileMean φ := by
    have h := hterm b hb
    have hnorm : ‖siteToPlane b - MomentBounds.profileMean φ‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_right (ne_of_gt hφb)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  have : siteToPlane a = siteToPlane b := hmeanA.trans hmeanB.symm
  apply hab
  ext i
  have hcoord := congrArg (fun x : Plane => x i) this
  simpa [siteToPlane] using hcoord

private theorem summable_shifted_srwKernel (n : ℕ) (z : Site) :
    Summable (fun w : Site => srwKernel n (z - w)) := by
  apply summable_of_ne_finset_zero (s := Polymer.endpoints z n)
  intro w hw
  rw [Polymer.srwKernel_sub_swap]
  exact Polymer.srwKernel_eq_zero_of_not_mem n z w hw

private theorem greenEnergy_le_of_finite_profile_bound
    (L : ℕ) (φ : Site → ℝ) (A : Finset Site)
    (hφA : ∀ z ∉ A, φ z = 0) (hφ : ∀ z, 0 ≤ φ z)
    (hmass : ∑ z ∈ A, φ z = 1) (K : ℝ) (hK : 0 ≤ K)
    (hφBound : ∀ z ∈ A, φ z ≤ K) :
    MomentBounds.greenEnergy L φ ≤ (L : ℝ) * K := by
  have hmassHas : HasSum φ 1 := by
    have h : HasSum φ (∑ z ∈ A, φ z) := hasSum_sum_of_ne_finset_zero hφA
    simpa only [hmass] using h
  have hkernelSum (m : ℕ) (z : Site) :
      ∑' w : Site, srwKernel (2 * m) (z - w) = 1 := by
    simpa only [Polymer.srwKernel_sub_swap] using Polymer.tsum_srwKernel (2 * m) z
  have hkernelFin (m : ℕ) (z : Site) :
      (∑ w ∈ A, srwKernel (2 * m) (z - w)) ≤ 1 := by
    calc
      _ ≤ ∑' w, srwKernel (2 * m) (z - w) :=
        (summable_shifted_srwKernel (2 * m) z).sum_le_tsum A
          (fun w _ => srwKernel_nonneg _ _)
      _ = 1 := hkernelSum m z
  have hinner (m : ℕ) (z : Site) :
      (∑' w, srwKernel (2 * m) (z - w) * φ w) ≤ K := by
    have hinnerEq : (∑' w, srwKernel (2 * m) (z - w) * φ w) =
        ∑ w ∈ A, srwKernel (2 * m) (z - w) * φ w := by
      apply tsum_eq_sum
      intro w hw
      simp [hφA w hw]
    rw [hinnerEq]
    calc
      _ ≤ ∑ w ∈ A, srwKernel (2 * m) (z - w) * K := by
        apply Finset.sum_le_sum
        intro w hw
        exact mul_le_mul_of_nonneg_left (hφBound w hw) (srwKernel_nonneg _ _)
      _ = K * ∑ w ∈ A, srwKernel (2 * m) (z - w) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left (hkernelFin m z) hK
      _ = K := by ring
  have henergy (m : ℕ) :
      (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) ≤ K := by
    have houterEq : (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) =
        ∑ z ∈ A, φ z * (∑' w, srwKernel (2 * m) (z - w) * φ w) := by
      calc
        _ = ∑' z, φ z * (∑' w, srwKernel (2 * m) (z - w) * φ w) := by
          apply tsum_congr
          intro z
          calc
            _ = ∑' w, φ z * (srwKernel (2 * m) (z - w) * φ w) := by
              apply tsum_congr
              intro w
              ring
            _ = φ z * (∑' w, srwKernel (2 * m) (z - w) * φ w) := tsum_mul_left
        _ = _ := by
          apply tsum_eq_sum
          intro z hz
          simp [hφA z hz]
    rw [houterEq]
    calc
      _ ≤ ∑ z ∈ A, φ z * K := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hinner m z) (hφ z)
      _ = K := by rw [← Finset.sum_mul, hmass]; ring
  rw [MomentBounds.greenEnergy_eq_sum L φ hφ hmassHas.summable]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 L, K := Finset.sum_le_sum fun n _ => henergy n
    _ = (L : ℝ) * K := by simp [Finset.sum_const]

private theorem profileP2Fun_raw_sixth_moment_le
    (β : ℝ) (L : ℕ) (φ : Site → ℝ) (c₃ Cgen : ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1)
    (hvar : Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ≤ c₃)
    (hcenterBound : |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω - 1) ^ 6
        ∂disorderLaw| ≤ Cgen *
          Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ 3) :
    Integrable (fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω ^ 6) disorderLaw ∧
      ∫ ω, profileP2Fun β 0 L φ (fun _ => 1) ω ^ 6 ∂disorderLaw ≤
        32 * (max Cgen 0 * c₃ ^ 3 + 1) := by
  classical
  let X : Disorder → ℝ := fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω
  let Y : Disorder → ℝ := fun ω => (X ω - 1) ^ 6
  have hXnonneg (ω : Disorder) : 0 ≤ X ω := by
    dsimp [X, profileP2Fun]
    exact tsum_nonneg fun z => mul_nonneg (hφ z) <|
      tsum_nonneg fun w => mul_nonneg (Polymer.pointToPoint_nonneg ..) (by norm_num)
  have hXint : Integrable (fun ω => X ω ^ 6) disorderLaw := by
    have h := Polymer.integrable_abs_pow_profile_probability β 0 L φ (fun _ => 1)
      hφ hmass.tsum_eq 1 (by norm_num) (by intro z; norm_num) 6
    apply h.congr
    filter_upwards [] with ω
    rw [abs_of_nonneg (hXnonneg ω)]
  have hYint : Integrable Y disorderLaw := by
    simpa [Y, X] using
      MomentBounds.integrable_centeredMoment_profileP2Fun 6 β L φ 1 hφ hmass
  have hVnonneg : 0 ≤ Var[fun ω => X ω; disorderLaw] := variance_nonneg X disorderLaw
  have hcenterIntegral :
      ∫ ω, Y ω ∂disorderLaw ≤ max Cgen 0 * c₃ ^ 3 := by
    have hcenter := hcenterBound
    dsimp [X, Y] at hcenter ⊢
    calc
      ∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω - 1) ^ 6 ∂disorderLaw ≤
          |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω - 1) ^ 6 ∂disorderLaw| :=
        le_abs_self _
      _ ≤ Cgen * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ 3 :=
        hcenter
      _ ≤ max Cgen 0 * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ 3 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hVnonneg _)
      _ ≤ max Cgen 0 * c₃ ^ 3 :=
        mul_le_mul_of_nonneg_left (by
          exact pow_le_pow_left₀ hVnonneg hvar 3) (le_max_right _ _)
  have hpoint (ω : Disorder) : X ω ^ 6 ≤ 32 * (Y ω + 1) := by
    have hX : |X ω| ≤ |X ω - 1| + 1 := by
      calc
        |X ω| = |(X ω - 1) + 1| := by congr 1; ring
        _ ≤ |X ω - 1| + 1 := by simpa using abs_add_le (X ω - 1) 1
    let u := |X ω - 1|
    have hu : (u + 1) ^ 6 ≤ 32 * (u ^ 6 + 1) := by
      have hid : 32 * (u ^ 6 + 1) - (u + 1) ^ 6 =
          (u - 1) ^ 2 * (31 * u ^ 4 + 56 * u ^ 3 + 66 * u ^ 2 + 56 * u + 31) := by ring
      have hnonneg : 0 ≤ (u - 1) ^ 2 *
          (31 * u ^ 4 + 56 * u ^ 3 + 66 * u ^ 2 + 56 * u + 31) := by positivity
      linarith
    calc
      X ω ^ 6 = |X ω| ^ 6 := by rw [abs_of_nonneg (hXnonneg ω)]
      _ ≤ (u + 1) ^ 6 := pow_le_pow_left₀ (abs_nonneg _) (by simpa [u] using hX) 6
      _ ≤ 32 * (u ^ 6 + 1) := hu
      _ = 32 * (Y ω + 1) := by
        congr 2
        calc
          |X ω - 1| ^ 6 = |(X ω - 1) ^ 6| := by rw [abs_pow]
          _ = (X ω - 1) ^ 6 := abs_of_nonneg (by positivity)
  have hupperInt : Integrable (fun ω => 32 * (Y ω + 1)) disorderLaw := by
    simpa [mul_add] using (hYint.const_mul 32).add (integrable_const (μ := disorderLaw) (32 : ℝ))
  constructor
  · simpa [X] using hXint
  · calc
      ∫ ω, X ω ^ 6 ∂disorderLaw ≤ ∫ ω, 32 * (Y ω + 1) ∂disorderLaw :=
        integral_mono_ae hXint hupperInt (Filter.Eventually.of_forall hpoint)
      _ = 32 * (∫ ω, Y ω ∂disorderLaw + 1) := by
        rw [integral_const_mul, integral_add hYint (integrable_const 1)]
        simp
      _ ≤ 32 * (max Cgen 0 * c₃ ^ 3 + 1) := by nlinarith [hcenterIntegral]

private theorem green_variance_scale_bound (L N : ℕ) (D C ell Q : ℝ)
    (hN : 0 < (N : ℝ)) (hD : 0 ≤ D) (hC : 0 ≤ C) (hell : 0 < ell)
    (hL : (L : ℝ) ≤ Q * (N : ℝ)) :
    ((L : ℝ) * (D / (N : ℝ))) * (C / ell) ≤ Q * D * C / ell := by
  have hLN : (L : ℝ) / (N : ℝ) ≤ Q := (div_le_iff₀ hN).2 hL
  have hcoeff : 0 ≤ D * C / ell := by positivity
  calc
    _ = (D * C / ell) * ((L : ℝ) / (N : ℝ)) := by
      field_simp [hN.ne', hell.ne']
    _ ≤ (D * C / ell) * Q := mul_le_mul_of_nonneg_left hLN hcoeff
    _ = Q * D * C / ell := by ring

private theorem flat_pairing_sixth_bound_of_profile
    (ϑ : ℝ) (N : ℕ) (hN : 1 ≤ N) (s t : ℝ) (f : Plane → ℝ)
    (hfcont : Continuous f) (hfsupp : HasCompactSupport f)
    (β : ℝ) (a b : ℕ) (hab : a ≤ b) (A : Finset Site)
    (w φ : Site → ℝ) (m : ℝ) (hm : 0 < m)
    (hφA : ∀ z ∉ A, φ z = 0) (hwA : ∀ z ∉ A, w z = 0)
    (hw : ∀ z, w z = ∫ x in cell N z, f x)
    (hφ : ∀ z, φ z = w z / m)
    (hkernel : ∀ ω x, rescaledP2Plane ϑ N s t x ω =
      Critical2DKPZ.pointToPlane β a (b - a) (latticePoint N x) ω)
    (hpairingInt : Integrable (fun ω =>
      (∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) disorderLaw)
    {C : ℝ}
    (hraw : ∫ ω, profileP2Fun β 0 (b - a) φ (fun _ => 1) ω ^ 6
      ∂disorderLaw ≤ C) :
    Integrable (fun ω =>
      (∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) disorderLaw ∧
      ∫ ω, (∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6
        ∂disorderLaw ≤ m ^ 6 * C := by
  have hpairEq (ω : Disorder) :
      (∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) =
        m * profileP2Fun β a b φ (fun _ => 1) ω := by
    let hG : Site → ℝ := fun z => Critical2DKPZ.pointToPlane β a (b - a) z ω
    calc
      _ = ∫ x, f x * rescaledP2Plane ϑ N s t x ω :=
        integral_map_fst_polymerMeasure ϑ hN s t ω f
      _ = ∫ x, f x * hG (latticePoint N x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [hkernel]
        rfl
      _ = ∑' z, w z * hG z := by
        rw [integral_latticeStep_mul_eq_tsum_cell N f hfcont hfsupp hG]
        apply tsum_congr
        intro z
        rw [hw z]
      _ = ∑ z ∈ A, w z * hG z := by
        apply tsum_eq_sum
        intro z hz
        simp [hwA z hz]
      _ = m * profileP2Fun β a b φ (fun _ => 1) ω := by
        have hprofile : profileP2Fun β a b φ (fun _ => 1) ω =
            ∑ z ∈ A, φ z * hG z := by
          rw [Polymer.profileP2Fun_eq_sum β a b φ (fun _ => 1) A hφA]
          simp only [mul_one, Polymer.tsum_pointToPoint, hG]
        calc
          _ = ∑ z ∈ A, m * (φ z * hG z) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hφ z]
            field_simp [hm.ne']
          _ = m * ∑ z ∈ A, φ z * hG z := by rw [Finset.mul_sum]
          _ = _ := by rw [hprofile]
  have htimeShift (ω : Disorder) :
      profileP2Fun β a b φ (fun _ => 1) ω =
        profileP2Fun β 0 (b - a) φ (fun _ => 1) (Smoothing.shiftEnvironment a ω) := by
    rw [Smoothing.profileP2Fun_timeShift_sub β (Nat.le_refl a) hab]
    simp
  have hprofileMeas : Measurable (fun ω : Disorder =>
      profileP2Fun β 0 (b - a) φ (fun _ => 1) ω ^ 6) :=
    (Polymer.measurable_profileP2Fun β 0 (b - a) φ (fun _ => 1)).pow_const 6
  have hshiftIntegral :
      (∫ ω, profileP2Fun β a b φ (fun _ => 1) ω ^ 6 ∂disorderLaw) =
        ∫ ω, profileP2Fun β 0 (b - a) φ (fun _ => 1) ω ^ 6 ∂disorderLaw := by
    calc
      _ = ∫ ω, profileP2Fun β 0 (b - a) φ (fun _ => 1)
            (Smoothing.shiftEnvironment a ω) ^ 6 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [htimeShift ω]
      _ = _ := Smoothing.integral_shiftEnvironment a hprofileMeas
  constructor
  · exact hpairingInt
  · calc
      _ = m ^ 6 * ∫ ω, profileP2Fun β a b φ (fun _ => 1) ω ^ 6 ∂disorderLaw := by
        rw [show (fun ω =>
            (∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) =
            fun ω => m ^ 6 * profileP2Fun β a b φ (fun _ => 1) ω ^ 6 by
              funext ω
              rw [hpairEq ω, mul_pow]]
        rw [integral_const_mul]
      _ = m ^ 6 * ∫ ω, profileP2Fun β 0 (b - a) φ (fun _ => 1) ω ^ 6
          ∂disorderLaw := by rw [hshiftIntegral]
      _ ≤ m ^ 6 * C := mul_le_mul_of_nonneg_left hraw (pow_nonneg hm.le _)

private theorem profileP2Fun_centered_sixth_bound_of_gen
    (β : ℝ) (L : ℕ) (φ : Site → ℝ) (Cgen : ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1)
    (hGen : |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ 6
        ∂disorderLaw| ≤ Cgen *
          Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^
            ((6 : ℝ) / 2))
    (hmean : ∫ ω, profileP2Fun β 0 L φ (fun _ => 1) ω ∂disorderLaw = 1) :
    Integrable (fun ω => (profileP2Fun β 0 L φ (fun _ => 1) ω - 1) ^ 6) disorderLaw ∧
      |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω - 1) ^ 6 ∂disorderLaw| ≤
        Cgen * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ 3 := by
  constructor
  · exact MomentBounds.integrable_centeredMoment_profileP2Fun 6 β L φ 1 hφ hmass
  · rw [hmean] at hGen
    have hpow : ((6 : ℝ) / 2) = (3 : ℕ) := by norm_num
    rw [hpow, Real.rpow_natCast] at hGen
    exact hGen

/-- Under `CCRMomentBound 6`, compact flat pairings have an eventual uniform sixth-moment bound on bounded time windows with interval lengths bounded away from zero. Integrability is supplied by `integrable_flat_polymerMeasure_pow`. -/
theorem polymerMeasure_flat_sixth_moment_le_of_ccr
    (hccr : MomentBounds.CCRMomentBound 6) (ϑ : ℝ) (χ : C_c(Plane, ℝ))
    {τ T : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
      ∫ ω, (∫ x, |χ x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6
        ∂disorderLaw ≤ C := by
  classical
  by_cases hχzero : ∀ x, χ x = 0
  · refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro s t hs hst ht
    have hzero (ω : Disorder) :
        ∫ x, |χ x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst) = 0 := by
      rw [integral_map_fst_polymerMeasure ϑ hN s t ω]
      simp [hχzero]
    simp [hzero]
  · have hχne : ∃ x, χ x ≠ 0 := not_forall.mp hχzero
    let f : Plane → ℝ := fun x => |χ x|
    have hfcont : Continuous f := by exact χ.continuous.abs
    have hfsupp : HasCompactSupport f := by
      have h := χ.hasCompactSupport.abs
      convert h using 1
      funext x
      rfl
    have hfint : Integrable f volume := by
      exact hfcont.integrable_of_hasCompactSupport hfsupp
    have hfnn (x : Plane) : 0 ≤ f x := abs_nonneg _
    have hfx : ∃ x, f x ≠ 0 := by
      obtain ⟨x, hx⟩ := hχne
      refine ⟨x, ?_⟩
      simp [f, hx]
    have hmassPos : 0 < ∫ x, f x := by
      obtain ⟨x, hx⟩ := hfx
      exact hfcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hfsupp hfnn hx
    let m : ℝ := ∫ x, f x
    have hm : 0 < m := hmassPos
    let support : Set Plane := tsupport (χ : Plane → ℝ)
    have hsupport : IsCompact support := χ.hasCompactSupport
    obtain ⟨R₀, hR₀⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hsupport.isBounded
    let R : ℝ := max R₀ 0
    have hR : 0 ≤ R := le_max_right _ _
    have hsupportNorm (x : Plane) (hx : x ∈ support) : ‖x‖ ≤ R := by
      have h := hR₀ hx
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h.trans (le_max_left _ _)
    obtain ⟨B₀, hB₀⟩ := hsupport.exists_bound_of_continuousOn χ.continuous.continuousOn
    let B : ℝ := max B₀ 1
    have hBpos : 0 < B := by dsimp [B]; positivity
    have hBbound (x : Plane) : f x ≤ B := by
      by_cases hx : χ x = 0
      · simp [f, hx, B]
      · have hxSupport : x ∈ support :=
          subset_closure (Function.mem_support.mpr hx)
        have hbound := hB₀ x hxSupport
        change |χ.toContinuousMap x| ≤ B
        calc
          |χ.toContinuousMap x| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hbound
          _ ≤ B := le_max_left _ _
    let D : ℝ := 4 * B / m
    have hDpos : 0 < D := by dsimp [D]; positivity
    let Q : ℝ := max T 0 + 3
    have hQpos : 0 < Q := by dsimp [Q]; positivity
    let c₁ : ℝ := Real.exp (2 * (R + 2) / Real.sqrt τ)
    have hc₁ : 0 < c₁ := Real.exp_pos _
    let ell : ℝ := Real.log (1 + 1 / (Q + 1))
    have hell : 0 < ell := by
      dsimp [ell]
      apply Real.log_pos
      have : 0 < 1 / (Q + 1) := by positivity
      linarith
    let c₂ : ℝ := D * Q * c₁ + 1
    have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
    obtain ⟨Csec, hCsec, hSecond⟩ :=
      Renewal.secondMoment_log_bound_horizon ϑ Q
    let c₃ : ℝ := Q * D * Csec / ell + 1
    have hc₃ : 0 < c₃ := by dsimp [c₃]; positivity
    have hgen : MomentBounds.GenMomentBound 6 :=
      MomentBounds.genMomentBound_of_ccr 6 (by
        intro hh
        norm_num at hh
        exact hccr)
    obtain ⟨L₀, Cgen, hGen⟩ := hgen 1 c₁ c₂ c₃ (by norm_num) hc₁ hc₂ hc₃
    let timeScale : ℝ := max ((L₀ : ℝ) + 2) 4
    have htimeScale : 0 < timeScale := by dsimp [timeScale]; positivity
    have hNtime : ∀ᶠ N : ℕ in atTop,
        timeScale / τ ≤ (N : ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈timeScale / τ⌉₊] with N hN
      have hceil : timeScale / τ ≤ (⌈timeScale / τ⌉₊ : ℝ) := Nat.le_ceil _
      have hN' : (⌈timeScale / τ⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      exact hceil.trans hN'
    have hNcells : ∀ᶠ N : ℕ in atTop, 2 * D ≤ (N : ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈2 * D⌉₊] with N hN
      have hceil : 2 * D ≤ (⌈2 * D⌉₊ : ℝ) := Nat.le_ceil _
      have hN' : (⌈2 * D⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      exact hceil.trans hN'
    refine ⟨m ^ 6 * (32 * (max Cgen 0 * c₃ ^ 3 + 1)), ?_⟩
    filter_upwards [eventually_ge_atTop 1, hNtime, hNcells,
      hSecond, criticalBeta_spec ϑ] with N hN hNtimeN hNcellsN hSecondN hBeta
    intro s t hs hst ht
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have ht0 : 0 ≤ t := by linarith
    let a : ℕ := evenCeil ((N : ℝ) * s)
    let b : ℕ := evenCeil ((N : ℝ) * t)
    let L : ℕ := b - a
    have hab : a ≤ b := by
      dsimp [a, b]
      apply evenCeil_mono
      exact mul_le_mul_of_nonneg_left (by linarith [hst]) (Nat.cast_nonneg N)
    have hclock :
        |((b : ℝ) - (a : ℝ)) - ((N : ℝ) * t - (N : ℝ) * s)| < 2 := by
      have h := evenCeil_duration_error
        (mul_nonneg (Nat.cast_nonneg N) hs) (mul_nonneg (Nat.cast_nonneg N) ht0)
      simpa [a, b, mul_sub] using h
    have hLcast : (L : ℝ) = (b : ℝ) - (a : ℝ) := by
      simp [L, Nat.cast_sub hab]
    have hNt : (N : ℝ) * (t - s) ≤ (N : ℝ) * T :=
      mul_le_mul_of_nonneg_left (by linarith) hNreal.le
    have hTQ : T + 3 ≤ Q := by dsimp [Q]; linarith [le_max_left T 0]
    have hDurationUpper : (L : ℝ) ≤ (N : ℝ) * (t - s) + 2 := by
      have hclockHi := (abs_lt.mp hclock).2
      rw [hLcast]
      nlinarith [hNt, hNreal, hTQ]
    have hNreal1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hLhi : (L : ℝ) ≤ Q * N := by
      calc
        (L : ℝ) ≤ (N : ℝ) * (t - s) + 2 := hDurationUpper
        _ ≤ (N : ℝ) * T + 2 := by linarith [hNt]
        _ ≤ (N : ℝ) * T + 3 * (N : ℝ) := by nlinarith
        _ = (T + 3) * (N : ℝ) := by ring
        _ ≤ Q * N := mul_le_mul_of_nonneg_right hTQ hNreal.le
    have htimeScaled : timeScale ≤ τ * (N : ℝ) := by
      have h := (div_le_iff₀ hτ).mp hNtimeN
      nlinarith [h]
    have hLlo : τ * (N : ℝ) - 2 < (L : ℝ) := by
      rw [hLcast]
      have hclockLo := (abs_lt.mp hclock).1
      have htimeLo : τ * (N : ℝ) ≤ (N : ℝ) * (t - s) := by
        calc
          τ * (N : ℝ) = (N : ℝ) * τ := by ring
          _ ≤ (N : ℝ) * (t - s) := mul_le_mul_of_nonneg_left hst hNreal.le
      nlinarith [hclockLo, htimeLo]
    have hL0real : (L₀ : ℝ) ≤ (L : ℝ) := by
      have htimeLo : (L₀ : ℝ) + 2 ≤ τ * (N : ℝ) := by
        have h := htimeScaled
        dsimp [timeScale] at h
        exact (le_max_left _ _).trans h
      linarith [hLlo]
    have hL0 : L₀ ≤ L := by exact_mod_cast hL0real
    have hLposReal : 0 < (L : ℝ) := by
      have htimeLo : 4 ≤ τ * (N : ℝ) := by
        have h := htimeScaled
        dsimp [timeScale] at h
        exact (le_max_right _ _).trans h
      linarith [hLlo]
    have hLpos : 0 < L := by exact_mod_cast hLposReal
    have hLscale : τ * (N : ℝ) / 2 ≤ (L : ℝ) := by
      have htimeLo : 4 ≤ τ * (N : ℝ) := by
        have h := htimeScaled
        dsimp [timeScale] at h
        exact (le_max_right _ _).trans h
      linarith [hLlo]
    have hLplus : (L : ℝ) + 1 ≤ (Q + 1) * (N : ℝ) := by
      calc
        (L : ℝ) + 1 ≤ Q * (N : ℝ) + 1 := by linarith [hLhi]
        _ ≤ Q * (N : ℝ) + (N : ℝ) := by linarith
        _ = (Q + 1) * (N : ℝ) := by ring
    have hratio : 1 / (Q + 1) ≤ (N : ℝ) / ((L : ℝ) + 1) := by
      apply (div_le_div_iff₀ (by positivity : 0 < Q + 1)
        (by positivity : 0 < (L : ℝ) + 1)).2
      nlinarith [hLplus]
    have hlog : ell ≤ Real.log (1 + (N : ℝ) / ((L : ℝ) + 1)) := by
      dsimp [ell]
      apply Real.log_le_log (by positivity)
      linarith [hratio]
    let β : ℝ := criticalBeta ϑ N
    have hβnonneg : 0 ≤ β := by dsimp [β]; exact Real.sqrt_nonneg _
    have hsecN := hSecondN L hLhi
    have hsecProd : Polymer.sigmaSq β * Renewal.freeSecondMoment β L ≤ Csec / ell := by
      have hsec : Polymer.sigmaSq β * Renewal.freeSecondMoment β L ≤
          Csec / Real.log (1 + (N : ℝ) / ((L : ℝ) + 1)) := by
        simpa [Polymer.sigmaSq, Renewal.freeSecondMoment, β, hBeta] using hsecN
      exact hsec.trans (div_le_div_of_nonneg_left hCsec.le hell hlog)
    have hprofileConst (z : Site) (hz : z ∈ (finite_latticePoint_image_of_bounded
        (N := N) hsupport.isBounded).toFinset) :
        IntegrableOn f (cell N z) volume ∧
          ∫ x in cell N z, f x ≤ B * (4 / (N : ℝ)) := by
      constructor
      · exact hfint.integrableOn
      · by_cases hzEven : z ∈ evenLattice
        · have hvol := volume_cell_lt_top (Nat.pos_of_ne_zero (by omega : N ≠ 0)) hzEven
          have hIntConst : IntegrableOn (fun _ : Plane => B) (cell N z) volume :=
            integrableOn_const hvol.ne
          calc
            ∫ x in cell N z, f x ≤ ∫ x in cell N z, (fun _ : Plane => B) x :=
              setIntegral_mono_on hfint.integrableOn hIntConst (measurableSet_cell N z)
                (fun x _ => hBbound x)
            _ = B * (4 / (N : ℝ)) := by
              rw [setIntegral_const, measureReal_def, volume_cell_toReal
                (Nat.pos_of_ne_zero (by omega : N ≠ 0)) hzEven]
              ring
        · have hempty : cell N z = ∅ := cell_eq_empty_of_not_even hzEven
          simp [hempty]
          positivity
    let A : Finset Site :=
      (finite_latticePoint_image_of_bounded (N := N) hsupport.isBounded).toFinset
    let w : Site → ℝ := fun z => ∫ x in cell N z, f x
    let φ : Site → ℝ := fun z => w z / m
    have hcellw0 (z : Site) (hz : z ∉ A) : w z = 0 := by
      have hfin : (latticePoint N '' support).Finite :=
        finite_latticePoint_image_of_bounded (N := N) hsupport.isBounded
      have heq : (∫ x in cell N z, f x) = ∫ x in cell N z, (fun _ : Plane => 0) x := by
        apply setIntegral_congr_fun (measurableSet_cell N z)
        intro x hx
        by_contra hfx
        have hxχ : χ x ≠ 0 := by simpa [f] using hfx
        have hxSupport : x ∈ support := subset_closure (Function.mem_support.mpr hxχ)
        have hzlink : latticePoint N x = z := (mem_cell_iff N z x).mp hx
        have hsite : latticePoint N x ∈ A := by
          have hmem : latticePoint N x ∈ latticePoint N '' support := ⟨x, hxSupport, rfl⟩
          exact hfin.mem_toFinset.mpr hmem
        apply hz
        simpa [hzlink] using hsite
      dsimp [w]
      rw [heq]
      simp
    have hφA : ∀ z ∉ A, φ z = 0 := by
      intro z hz
      simp [φ, hcellw0 z hz]
    have hweightsum : (∫ x, f x) = ∑' z, w z := by
      simpa [w] using
        (integral_latticeStep_mul_eq_tsum_cell N f hfcont hfsupp (fun _ : Site => 1))
    have hwSum : (∑ z ∈ A, w z) = m := by
      calc
        _ = ∑' z, w z := by
          symm
          apply tsum_eq_sum
          intro z hz
          exact hcellw0 z hz
        _ = m := by dsimp [m]; exact hweightsum.symm
    have hφmassFin : (∑ z ∈ A, φ z) = 1 := by
      calc
        _ = (∑ z ∈ A, w z) / m := by simp [φ, Finset.sum_div]
        _ = 1 := by rw [hwSum]; exact div_self hm.ne'
    have hφhas : HasSum φ 1 := by
      have h : HasSum φ (∑ z ∈ A, φ z) :=
        hasSum_sum_of_ne_finset_zero (s := A) (f := φ) hφA
      simpa only [hφmassFin] using h
    have hφnonneg (z : Site) : 0 ≤ φ z := by
      dsimp [φ]
      exact div_nonneg (setIntegral_nonneg (measurableSet_cell N z) fun x _ => hfnn x) hm.le
    have hφcellBound (z : Site) (hz : z ∈ A) : φ z ≤ D / (N : ℝ) := by
      have hweight := (hprofileConst z hz).2
      dsimp [φ, D]
      calc
        _ ≤ (B * (4 / (N : ℝ))) / m := div_le_div_of_nonneg_right hweight hm.le
        _ = (4 * B / m) / (N : ℝ) := by field_simp [hm.ne', hNreal.ne']
    have hA_siteNorm (z : Site) (hz : z ∈ A) :
        ‖siteToPlane z‖ ≤ Real.sqrt ((N : ℝ) / 2) * (R + 2) := by
      have hfin : (latticePoint N '' support).Finite :=
        finite_latticePoint_image_of_bounded (N := N) hsupport.isBounded
      have hz' : z ∈ latticePoint N '' support := hfin.mem_toFinset.mp hz
      obtain ⟨x, hx, rfl⟩ := hz'
      have hxnorm := hsupportNorm x hx
      have hsample := Critical2DKPZ.norm_cellSample_le hR hxnorm N
      have hroot : 0 < Real.sqrt ((N : ℝ) / 2) := by positivity
      have hsample' :
          ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (latticePoint N x)‖ ≤ R + 2 := by
        simpa only [Critical2DKPZ.cellSample, Critical2DKPZ.latticeRepresentative] using hsample
      have hscaled :
          (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (latticePoint N x)‖ ≤ R + 2 := by
        simpa only [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hroot.le)] using hsample'
      calc
        ‖siteToPlane (latticePoint N x)‖ = Real.sqrt ((N : ℝ) / 2) *
            ((Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (latticePoint N x)‖) := by
          field_simp [hroot.ne']
        _ ≤ Real.sqrt ((N : ℝ) / 2) * (R + 2) :=
          mul_le_mul_of_nonneg_left hscaled hroot.le
    have hrootL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 hLposReal
    have hrootτ : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
    have hrootProduct : Real.sqrt ((N : ℝ) / 2) * Real.sqrt τ ≤ Real.sqrt (L : ℝ) := by
      calc
        Real.sqrt ((N : ℝ) / 2) * Real.sqrt τ =
            Real.sqrt (((N : ℝ) / 2) * τ) := by
              rw [Real.sqrt_mul (by positivity : 0 ≤ (N : ℝ) / 2)]
        _ ≤ Real.sqrt (L : ℝ) := Real.sqrt_le_sqrt (by
          calc
            ((N : ℝ) / 2) * τ = τ * (N : ℝ) / 2 := by ring
            _ ≤ L := hLscale)
    have hrootRatio :
        Real.sqrt ((N : ℝ) / 2) / Real.sqrt (L : ℝ) ≤ 1 / Real.sqrt τ := by
      apply (div_le_iff₀ hrootL).2
      calc
        Real.sqrt ((N : ℝ) / 2) ≤ Real.sqrt (L : ℝ) / Real.sqrt τ :=
          (le_div_iff₀ hrootτ).2 hrootProduct
        _ = (1 / Real.sqrt τ) * Real.sqrt (L : ℝ) := by ring
    let W : Site → ℝ := fun z => φ z * Real.exp
      (2 * 1 * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt (L : ℝ))
    have hWsupport : ∀ z ∉ A, W z = 0 := by
      intro z hz
      simp [W, hφA z hz]
    have hWsum : HasSum W (∑ z ∈ A, W z) :=
      hasSum_sum_of_ne_finset_zero (s := A) (f := W) hWsupport
    have hWbound : ∑ z ∈ A, W z ≤ c₁ := by
        calc
          _ ≤ ∑ z ∈ A, φ z * c₁ := by
            apply Finset.sum_le_sum
            intro z hz
            have hratioZ : ‖siteToPlane z‖ / Real.sqrt (L : ℝ) ≤
                (R + 2) / Real.sqrt τ := by
              calc
                _ ≤ (Real.sqrt ((N : ℝ) / 2) * (R + 2)) / Real.sqrt (L : ℝ) :=
                  div_le_div_of_nonneg_right (hA_siteNorm z hz) hrootL.le
                _ = (R + 2) *
                    (Real.sqrt ((N : ℝ) / 2) / Real.sqrt (L : ℝ)) := by ring
                _ ≤ (R + 2) / Real.sqrt τ := by
                  calc
                    _ ≤ (R + 2) * (1 / Real.sqrt τ) :=
                      mul_le_mul_of_nonneg_left hrootRatio (by linarith)
                    _ = _ := by ring
            have hexp : Real.exp
                (2 * 1 * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt (L : ℝ)) ≤ c₁ := by
              apply Real.exp_le_exp.mpr
              calc
                2 * 1 * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt (L : ℝ) =
                    2 * (‖siteToPlane z‖ / Real.sqrt (L : ℝ)) := by
                      simp only [sub_zero]
                      ring
                _ ≤ 2 * ((R + 2) / Real.sqrt τ) :=
                  mul_le_mul_of_nonneg_left hratioZ (by norm_num)
                _ = 2 * (R + 2) / Real.sqrt τ := by ring
            exact mul_le_mul_of_nonneg_left hexp (hφnonneg z)
          _ = c₁ := by rw [← Finset.sum_mul, hφmassFin]; ring
    have hlocal : MomentBounds.ExpLocalized 1 c₁ L φ := by
      refine ⟨0, hWsum.summable, ?_⟩
      change (∑' z, W z) ≤ c₁
      rw [hWsum.tsum_eq]
      exact hWbound
    have hspreadBound : MomentBounds.profileSpread φ ≤ (L : ℝ) * c₁ := by
      have hlocalFinite : ∑ z ∈ A, φ z * Real.exp
          (2 * 1 * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt (L : ℝ)) ≤ c₁ := by
        change (∑ z ∈ A, W z) ≤ c₁
        exact hWbound
      have hspread := MomentBounds.profileSpread_le_of_exponential_localization_finiteSupport
        1 (by norm_num) L hLpos φ A hφA hφnonneg hφmassFin 0 c₁ hlocalFinite
      simpa using hspread
    have hφSqBound : (∑' z, φ z ^ 2) ≤ D / (N : ℝ) := by
      rw [tsum_eq_sum (fun z hz => by simp [hφA z hz])]
      calc
        _ ≤ ∑ z ∈ A, (D / (N : ℝ)) * φ z := by
          apply Finset.sum_le_sum
          intro z hz
          simpa [pow_two, mul_comm] using
            mul_le_mul_of_nonneg_right (hφcellBound z hz) (hφnonneg z)
        _ = D / (N : ℝ) := by rw [← Finset.mul_sum, hφmassFin]; ring
    have hDhalf : D / (N : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hNreal]
      linarith [hNcellsN]
    have hposA : ∃ z ∈ A, 0 < φ z := by
      by_contra hn
      have hnonpos : ∀ z ∈ A, φ z ≤ 0 := by
        intro z hz
        by_contra hnot
        exact hn ⟨z, hz, lt_of_not_ge hnot⟩
      have hsumNonpos : (∑ z ∈ A, φ z) ≤ 0 := Finset.sum_nonpos fun z hz => hnonpos z hz
      linarith [hφmassFin]
    obtain ⟨z₁, hz₁, hφz₁⟩ := hposA
    have hposB : ∃ z ∈ A, z ≠ z₁ ∧ 0 < φ z := by
      by_contra hn
      have hzero : ∀ z ∈ A, z ≠ z₁ → φ z = 0 := by
        intro z hz hzz
        have hnpos : ¬ 0 < φ z := by
          intro hp
          exact hn ⟨z, hz, hzz, hp⟩
        exact le_antisymm (le_of_not_gt hnpos) (hφnonneg z)
      have hsumEq : (∑ z ∈ A, φ z) = φ z₁ := by
        calc
          _ = ∑ z ∈ A, if z = z₁ then φ z₁ else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hzz : z = z₁
            · simp [hzz]
            · simp [hzz, hzero z hz hzz]
          _ = φ z₁ := by simp [hz₁]
      have hbound := hφcellBound z₁ hz₁
      linarith [hφmassFin, hDhalf]
    obtain ⟨z₂, hz₂, hne, hφz₂⟩ := hposB
    have hspreadPos : 0 < MomentBounds.profileSpread φ :=
      profileSpread_pos_of_two_positive_sites φ A hφA hφnonneg hz₁ hz₂ hne.symm hφz₁ hφz₂
    have hsqSpread : (∑' z, φ z ^ 2) * MomentBounds.profileSpread φ ≤ D * Q * c₁ := by
      have hspreadNN := MomentBounds.profileSpread_nonneg φ hφnonneg
      calc
        _ ≤ (D / (N : ℝ)) * MomentBounds.profileSpread φ :=
          mul_le_mul_of_nonneg_right hφSqBound hspreadNN
        _ ≤ (D / (N : ℝ)) * ((L : ℝ) * c₁) :=
          mul_le_mul_of_nonneg_left hspreadBound (div_nonneg hDpos.le hNreal.le)
        _ = (D * c₁) * ((L : ℝ) / (N : ℝ)) := by ring
        _ ≤ (D * c₁) * Q :=
          mul_le_mul_of_nonneg_left ((div_le_iff₀ hNreal).2 hLhi)
            (mul_nonneg hDpos.le hc₁.le)
        _ = D * Q * c₁ := by ring
    have hsqHyp : (∑' z, φ z ^ 2) ≤ c₂ / MomentBounds.profileSpread φ := by
      apply (le_div_iff₀ hspreadPos).2
      dsimp [c₂]
      exact le_trans hsqSpread (le_add_of_nonneg_right (by norm_num))
    have hgreen : MomentBounds.greenEnergy L φ ≤ (L : ℝ) * (D / (N : ℝ)) :=
      greenEnergy_le_of_finite_profile_bound L φ A hφA hφnonneg hφmassFin
        (D / (N : ℝ)) (div_nonneg hDpos.le hNreal.le) hφcellBound
    have hvarFormula := MomentBounds.variance_profileP2Fun_bounds β L φ hφnonneg hφhas.summable
    have hvarProdNonneg : 0 ≤ Polymer.sigmaSq β * Renewal.freeSecondMoment β L := by
      apply mul_nonneg
      · dsimp [Polymer.sigmaSq]
        exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (sq_nonneg β))
      · exact integral_nonneg fun ω => sq_nonneg _
    have hgreenNonneg : 0 ≤ MomentBounds.greenEnergy L φ :=
      MomentBounds.greenEnergy_nonneg L φ hφnonneg
    have hgreenBoundNonneg : 0 ≤ (L : ℝ) * (D / (N : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg L) (div_nonneg hDpos.le hNreal.le)
    have hvar :
        Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ≤ c₃ := by
      calc
        _ ≤ MomentBounds.greenEnergy L φ * Polymer.sigmaSq β * Renewal.freeSecondMoment β L :=
          hvarFormula.2
        _ ≤ ((L : ℝ) * (D / (N : ℝ))) * (Csec / ell) := by
          have hprod := mul_le_mul hgreen hsecProd hvarProdNonneg hgreenBoundNonneg
          simpa only [mul_assoc] using hprod
        _ ≤ Q * D * Csec / ell :=
          green_variance_scale_bound L N D Csec ell Q hNreal hDpos.le hCsec.le hell hLhi
        _ ≤ c₃ := le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℝ))
    have hGenBound := hGen β hβnonneg L hL0 φ hφnonneg hφhas hlocal hsqHyp hvar
    have hmean := Polymer.integral_profile_flat_probability β 0 L φ hφnonneg hφhas.tsum_eq
    have hcenterBound := profileP2Fun_centered_sixth_bound_of_gen β L φ Cgen
      hφnonneg hφhas hGenBound hmean
    have hrawProfile := profileP2Fun_raw_sixth_moment_le β L φ c₃ Cgen
      hφnonneg hφhas hvar hcenterBound.2
    have hpairingInt : Integrable (fun ω =>
        (∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) disorderLaw :=
      integrable_flat_polymerMeasure_pow ϑ N s t χ 6
    have hpairingBound := flat_pairing_sixth_bound_of_profile
      ϑ N hN s t f hfcont hfsupp β a b hab A w φ m hm hφA hcellw0
      (fun z => rfl) (fun z => rfl) (fun ω x => rfl) hpairingInt hrawProfile.2
    exact hpairingBound.2

end Critical2DKPZ.SHF.Limit

end
