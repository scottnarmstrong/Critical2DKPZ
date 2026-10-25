/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.TimeBlocks
public import Critical2DKPZ.SHF.Flow.SlabProjection
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Polymer.ChapmanKolmogorov
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic

/-! # One-step annealing of a terminal profile -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.SHF.Flow

/-- Finite Jensen for nonnegative weights, in the sixth-moment form used when averaging a
Gaussian boundary layer. -/
theorem weighted_nonneg_sum_pow_six_le (S : Finset Site) (a x : Site → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hx : ∀ i ∈ S, 0 ≤ x i) :
    (∑ i ∈ S, a i * x i) ^ 6 ≤
      (∑ i ∈ S, a i) ^ 5 * ∑ i ∈ S, a i * x i ^ 6 := by
  classical
  let A : ℝ := ∑ i ∈ S, a i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi => ha i hi
  by_cases hA0 : A = 0
  · have hzero : ∀ i ∈ S, a i = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => ha i hi)).mp
      simpa [A] using hA0
    have hsum : (∑ i ∈ S, a i * x i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hzero i hi]
    have hsum6 : (∑ i ∈ S, a i * x i ^ 6) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hzero i hi]
    rw [hsum, hsum6]
    norm_num
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hweightsum : (∑ i ∈ S, a i / A) = 1 := by
      rw [← Finset.sum_div]
      simp [A, hApos.ne']
    have hmean : (∑ i ∈ S, (a i / A) * x i) =
        (∑ i ∈ S, a i * x i) / A := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hmom : (∑ i ∈ S, (a i / A) * x i ^ 6) =
        (∑ i ∈ S, a i * x i ^ 6) / A := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hJensen := (convexOn_pow (𝕜 := ℝ) 6).map_sum_le
      (fun i hi => div_nonneg (ha i hi) hA)
      hweightsum
      (fun i hi => Set.mem_Ici.mpr (hx i hi))
    have hJensen' : (∑ i ∈ S, (a i / A) * x i) ^ 6 ≤
        ∑ i ∈ S, (a i / A) * x i ^ 6 := by
      simpa only [smul_eq_mul] using hJensen
    have hJensen'' : ((∑ i ∈ S, a i * x i) / A) ^ 6 ≤
        (∑ i ∈ S, a i * x i ^ 6) / A := by
      simpa only [hmean, hmom] using hJensen'
    calc
      (∑ i ∈ S, a i * x i) ^ 6 =
          A ^ 6 * ((∑ i ∈ S, a i * x i) / A) ^ 6 := by
            field_simp [hApos.ne']
      _ ≤ A ^ 6 * ((∑ i ∈ S, a i * x i ^ 6) / A) :=
        mul_le_mul_of_nonneg_left hJensen'' (by positivity)
      _ = A ^ 5 * ∑ i ∈ S, a i * x i ^ 6 := by
        field_simp [hApos.ne']

private theorem pointToPoint_resample_complement_previous (β : ℝ) {n : ℕ}
    (x y : Site) (ω η : Disorder) :
    pointToPoint β 0 (n - 1) x y
      (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) =
      pointToPoint β 0 (n - 1) x y ω := by
  apply Blocks.blockMeasurable_resample_keep
  convert Polymer.measurable_pointToPoint_block β 0 (n - 1) x y using 1
  simp only [Nat.zero_add]

private theorem pointToPlane_resample_complement_final (β : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (x : Site) (ω η : Disorder) :
    pointToPlane β 0 n x (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) =
      ∑' y, pointToPoint β 0 (n - 1) x y ω * pointToPlane β (n - 1) 1 y η := by
  have hsplit : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hck := Polymer.pointToPlane_chapmanKolmogorov β 0 (n - 1) 1 x
    (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η)
  have hck' : pointToPlane β 0 n x
      (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) =
      ∑' y, pointToPoint β 0 (n - 1) x y
        (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) *
        pointToPlane β (n - 1) 1 y (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) := by
    calc
      _ = pointToPlane β 0 ((n - 1) + 1) x
          (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) := by rw [hsplit]
      _ = _ := by simpa only [Nat.zero_add] using hck
  calc
    pointToPlane β 0 n x (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) =
        ∑' y, pointToPoint β 0 (n - 1) x y
          (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) *
          pointToPlane β (n - 1) 1 y (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) := hck'
    _ = _ := by
      apply tsum_congr
      intro y
      rw [pointToPoint_resample_complement_previous β x y ω η]
      congr 1
      apply blockMeasurable_resample_outside
        (a := n - 1) (b := n) (c := 0) (d := n - 1)
        (Set.disjoint_left.mpr fun i hi hj => by
          simp only [Set.mem_Ioc] at hi hj
          omega)
      convert Polymer.measurable_pointToPlane_block β (n - 1) 1 y using 1
      rw [hsplit]

/-- Averaging the complement of the first `n - 1` disorder layers replaces the final
one-layer point-to-plane factor by its annealed value. -/
theorem integral_pointToPlane_resample_complement_final (β : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (x : Site) (ω : Disorder) :
    ∫ η, pointToPlane β 0 n x
      (Gaussian.resample (Gaussian.timeBlock 0 (n - 1)) ω η) ∂disorderLaw =
      pointToPlane β 0 (n - 1) x ω := by
  calc
    _ = ∫ η, ∑' y, pointToPoint β 0 (n - 1) x y ω *
        pointToPlane β (n - 1) 1 y η ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun η =>
        pointToPlane_resample_complement_final β hn x ω η
    _ = pointToPlane β 0 (n - 1) x ω := by
      let E : Finset Site := Polymer.endpoints x (n - 1)
      have hzero (y : Site) (hy : y ∉ E) : pointToPoint β 0 (n - 1) x y ω = 0 :=
        Polymer.pointToPoint_eq_zero_of_not_mem β 0 (n - 1) x y ω (by simpa [E] using hy)
      have hsum (η : Disorder) :
          (∑' y, pointToPoint β 0 (n - 1) x y ω * pointToPlane β (n - 1) 1 y η) =
            ∑ y ∈ E, pointToPoint β 0 (n - 1) x y ω * pointToPlane β (n - 1) 1 y η := by
        rw [tsum_eq_sum (s := E)]
        intro y hy
        rw [hzero y hy]
        simp only [zero_mul]
      have hint (y : Site) : Integrable
          (fun η => pointToPoint β 0 (n - 1) x y ω * pointToPlane β (n - 1) 1 y η)
          disorderLaw :=
        (Polymer.integrable_pointToPlane β (n - 1) 1 y).const_mul _
      calc
        _ = ∫ η, ∑ y ∈ E, pointToPoint β 0 (n - 1) x y ω *
            pointToPlane β (n - 1) 1 y η ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hsum
        _ = ∑ y ∈ E, pointToPoint β 0 (n - 1) x y ω := by
          rw [integral_finsetSum E (fun y _ => hint y)]
          apply Finset.sum_congr rfl
          intro y hy
          rw [integral_const_mul, Polymer.integral_pointToPlane, mul_one]
        _ = pointToPlane β 0 (n - 1) x ω := by
          rw [← Polymer.tsum_pointToPoint]
          symm
          exact tsum_eq_sum (s := E) (fun y hy => by
            rw [hzero y hy])



/-- Conditional Jensen also compares sixth moments of every finite nonnegative weighted
sum of point-to-plane profiles across one terminal disorder layer. -/
theorem integral_sixth_weightedPointToPlane_sub_horizon_le (β : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (S : Finset Site) (a : Site → ℝ) (ha : ∀ x ∈ S, 0 ≤ a x) :
    ∫ ω, (∑ x ∈ S, a x * pointToPlane β 0 (n - 1) x ω) ^ 6 ∂disorderLaw ≤
      ∫ ω, (∑ x ∈ S, a x * pointToPlane β 0 n x ω) ^ 6 ∂disorderLaw := by
  let F : Disorder → ℝ := ∑ x ∈ S, fun ω => a x * pointToPlane β 0 n x ω
  let G : Disorder → ℝ := ∑ x ∈ S, fun ω => a x * pointToPlane β 0 (n - 1) x ω
  have hFmem : MemLp F 6 disorderLaw := by
    have h : MemLp (fun ω => ∑ x ∈ S, a x * pointToPlane β 0 n x ω)
        6 disorderLaw := by
      apply memLp_finsetSum (s := S)
      intro x hx
      exact (Polymer.memLp_pointToPlane β 0 n x 6 (by norm_num)).const_mul (a x)
    change MemLp (∑ x ∈ S, fun ω => a x * pointToPlane β 0 n x ω) 6 disorderLaw
    convert h using 1
    funext ω
    simp only [Finset.sum_apply]
  have hFm : Measurable F := by
    have h : Measurable (fun ω => ∑ x ∈ S, a x * pointToPlane β 0 n x ω) := by
      apply Finset.measurable_sum (s := S)
      intro x hx
      exact measurable_const.mul (Polymer.measurable_pointToPlane β 0 n x)
    change Measurable (∑ x ∈ S, fun ω => a x * pointToPlane β 0 n x ω)
    convert h using 1
    funext ω
    simp only [Finset.sum_apply]
  have hFint : Integrable F disorderLaw := hFmem.integrable (by norm_num)
  have hFnonneg (ω : Disorder) : 0 ≤ F ω := by
    dsimp [F]
    simp only [Finset.sum_apply]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (ha x hx) (Polymer.pointToPlane_pos β 0 n x ω).le
  have hGnonneg (ω : Disorder) : 0 ≤ G ω := by
    dsimp [G]
    simp only [Finset.sum_apply]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (ha x hx) (Polymer.pointToPlane_pos β 0 (n - 1) x ω).le
  have hnormPow (z : ℝ) (hz : 0 ≤ z) : ‖z‖ ^ (6 : ℝ) = z ^ 6 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hz,
      show (6 : ℝ) = (6 : ℕ) by norm_num, Real.rpow_natCast]
  have hFnormNat : Integrable (fun ω => ‖F ω‖ ^ 6) disorderLaw :=
    hFmem.integrable_norm_pow'
  have hF6 : Integrable (fun ω => F ω ^ 6) disorderLaw := by
    apply hFnormNat.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg ω)]
  have hFpow : Integrable (fun ω => ‖F ω‖ ^ (6 : ℝ)) disorderLaw := by
    apply hF6.congr
    filter_upwards [] with ω
    exact (hnormPow _ (hFnonneg ω)).symm
  let m : MeasurableSpace Disorder := Gaussian.disorderBlock 0 (n - 1)
  have hCEsum := condExp_finsetSum (s := S)
    (fun x hx => (Polymer.integrable_pointToPlane β 0 n x).const_mul (a x)) m
  have hCEprofile (x : Site) : disorderLaw[pointToPlane β 0 n x | m] =ᵐ[disorderLaw]
      fun ω => pointToPlane β 0 (n - 1) x ω := by
    have hCE := Gaussian.condExp_disorderBlock_ae_eq 0 (n - 1)
      (Polymer.measurable_pointToPlane β 0 n x)
      (Polymer.integrable_pointToPlane β 0 n x)
    filter_upwards [hCE] with ω hω
    rw [hω]
    exact integral_pointToPlane_resample_complement_final β hn x ω
  have hCEweighted (x : Site) :
      disorderLaw[(fun ω => a x * pointToPlane β 0 n x ω) | m] =ᵐ[disorderLaw]
        fun ω => a x * pointToPlane β 0 (n - 1) x ω := by
    change disorderLaw[(a x) • (fun ω => pointToPlane β 0 n x ω) | m] =ᵐ[disorderLaw]
      fun ω => a x * pointToPlane β 0 (n - 1) x ω
    have hsmul := condExp_smul (μ := disorderLaw) (c := a x)
      (f := fun ω => pointToPlane β 0 n x ω) m
    filter_upwards [hsmul, hCEprofile x] with ω hω hprofile
    simpa only [smul_eq_mul] using hω.trans (congrArg (fun z => a x * z) hprofile)
  have hCEG : disorderLaw[F | m] =ᵐ[disorderLaw] G := by
    have hsum := eventuallyEq_sum (s := S) fun x hx => hCEweighted x
    dsimp [F, G]
    exact hCEsum.trans hsum
  have hJensen := integral_norm_condExp_rpow_le
    (μ := disorderLaw) (m := m) (f := F) (p := (6 : ℝ)) (by norm_num) hFpow
  calc
    ∫ ω, (∑ x ∈ S, a x * pointToPlane β 0 (n - 1) x ω) ^ 6 ∂disorderLaw =
        ∫ ω, ‖disorderLaw[F | m] ω‖ ^ (6 : ℝ) ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [hCEG] with ω hω
      have hsum : (∑ x ∈ S, a x * pointToPlane β 0 (n - 1) x ω) = G ω := by
        dsimp [G]
        simp only [Finset.sum_apply]
      rw [hsum, hω]
      exact (hnormPow _ (hGnonneg ω)).symm
    _ ≤ ∫ ω, ‖F ω‖ ^ (6 : ℝ) ∂disorderLaw := hJensen
    _ = ∫ ω, F ω ^ 6 ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => hnormPow _ (hFnonneg ω)
    _ = ∫ ω, (∑ x ∈ S, a x * pointToPlane β 0 n x ω) ^ 6 ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        dsimp [F]
        simp only [Finset.sum_apply]

end Critical2DKPZ.SHF.Flow

end
