/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockCompositionPairLocalError
public import Critical2DKPZ.SHF.Moments.PairBlockCompositionVariance
public import Critical2DKPZ.SHF.Moments.PairBlockCompositionTail
public import Critical2DKPZ.SHF.Moments.PairBlockGaussianList
public import Critical2DKPZ.SHF.Moments.PairBlockGaussianizedList
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Spatial local profiles of critical pair-block compositions -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- The explicit Gaussian support-tail estimate is bounded by a simple
exponential in the block duration. -/
private theorem eventually_gaussianizedBlockIntProbability_l1_le_exp_quarter :
    ∀ᶠ m : ℕ in atTop,
      (∑' j : ℤ,
        |gaussianizedBlockIntProbability m j - fullGaussianBlockProbability m j|) ≤
        224 * Real.exp (-((m : ℝ) / 4)) := by
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
    eventually_gaussianizedBlockIntProbability_l1_le
  filter_upwards [eventually_ge_atTop (max m₀ 1)] with m hm
  have hmBound := hm₀ m (le_trans (le_max_left m₀ 1) hm)
  have hmone : 1 ≤ m := le_trans (le_max_right m₀ 1) hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hroot : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
    calc
      Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast hmone])
      _ = (m : ℝ) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hlinear : (m : ℝ) ≤ 4 * Real.exp ((m : ℝ) / 4) := by
    nlinarith [Real.add_one_le_exp ((m : ℝ) / 4)]
  have hexp : Real.exp (-((m : ℝ) / 2)) * Real.exp ((m : ℝ) / 4) =
      Real.exp (-((m : ℝ) / 4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ 56 * Real.sqrt (m : ℝ) * Real.exp (-((m : ℝ) / 2)) := hmBound
    _ ≤ 56 * (m : ℝ) * Real.exp (-((m : ℝ) / 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot (by norm_num)) (Real.exp_nonneg _)
    _ = 56 * Real.exp (-((m : ℝ) / 2)) * (m : ℝ) := by ring
    _ ≤ 56 * Real.exp (-((m : ℝ) / 2)) *
        (4 * Real.exp ((m : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hlinear (by positivity)
    _ = 224 * (Real.exp (-((m : ℝ) / 2)) * Real.exp ((m : ℝ) / 4)) := by ring
    _ = 224 * Real.exp (-((m : ℝ) / 4)) := by rw [hexp]

/-- The natural-number ceiling of the logarithmic spatial cutoff. -/
def spatialLogCutoff (N : ℕ) : ℕ := ⌈Real.log (N : ℝ)⌉₊

/-- The twelfth logarithmic cutoff power is negligible on the diffusive scale. -/
theorem eventually_spatialLogCutoff_pow12_div_sqrt_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (spatialLogCutoff N : ℝ) ^ 12 / Real.sqrt (N : ℝ) < ε := by
  have h := tendsto_ceilLogPow_twelve_div_sqrt.eventually
    (Iio_mem_nhds hε)
  filter_upwards [h] with N hN
  simpa only [spatialLogCutoff] using hN

private theorem spatialLogCutoff_kernel_error_small
    (N K : ℕ) (ε : ℝ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hRatio : (K : ℝ) ^ 12 / Real.sqrt (N : ℝ) < ε / 64) :
    32 * (K : ℝ) ^ 2 / (N : ℝ) < ε / 2 := by
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hKpow : (K : ℝ) ^ 2 ≤ (K : ℝ) ^ 12 := by
    have hKten : (1 : ℝ) ≤ (K : ℝ) ^ 10 := by
      calc
        (1 : ℝ) = 1 ^ 10 := by norm_num
        _ ≤ (K : ℝ) ^ 10 :=
          pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hK) 10
    calc
      (K : ℝ) ^ 2 = (K : ℝ) ^ 2 * 1 := by ring
      _ ≤ (K : ℝ) ^ 2 * (K : ℝ) ^ 10 :=
        mul_le_mul_of_nonneg_left hKten (sq_nonneg (K : ℝ))
      _ = (K : ℝ) ^ 12 := by ring
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
  have hrootOne : 1 ≤ Real.sqrt (N : ℝ) := by
    have h := Real.sqrt_le_sqrt hNreal
    simpa using h
  have hrootSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ))
  have hrootle : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hrootOne (Real.sqrt_nonneg (N : ℝ))
    have hmul' : Real.sqrt (N : ℝ) ≤ Real.sqrt (N : ℝ) ^ 2 := by
      simpa [pow_two] using hmul
    simpa [hrootSq] using hmul'
  have hratio : (K : ℝ) ^ 2 / (N : ℝ) ≤
      (K : ℝ) ^ 12 / Real.sqrt (N : ℝ) := by
    calc
      _ ≤ (K : ℝ) ^ 12 / (N : ℝ) :=
        div_le_div_of_nonneg_right hKpow (Nat.cast_nonneg _)
      _ ≤ (K : ℝ) ^ 12 / Real.sqrt (N : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hroot hrootle
  calc
    32 * (K : ℝ) ^ 2 / (N : ℝ) =
        32 * ((K : ℝ) ^ 2 / (N : ℝ)) := by ring
    _ ≤ 32 * ((K : ℝ) ^ 12 / Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 32)
    _ < 32 * (ε / 64) := mul_lt_mul_of_pos_left hRatio (by norm_num)
    _ = ε / 2 := by ring

private theorem tendsto_spatialLogCutoff_expQuarter :
    Tendsto (fun N : ℕ => (N : ℝ) *
      (spatialLogCutoff N : ℝ) ^ 2 *
        Real.exp (-((spatialLogCutoff N : ℝ) ^ 10 / 4)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually_ge_atTop 2
  have hN := eventually_ge_atTop 1
  have hpowLim := tendsto_ceilLogPow_twelve_div_sqrt
  have hbound : ∀ᶠ N : ℕ in atTop,
      0 ≤ (N : ℝ) * (spatialLogCutoff N : ℝ) ^ 2 *
          Real.exp (-((spatialLogCutoff N : ℝ) ^ 10 / 4)) ∧
        (N : ℝ) * (spatialLogCutoff N : ℝ) ^ 2 *
          Real.exp (-((spatialLogCutoff N : ℝ) ^ 10 / 4)) ≤
          (spatialLogCutoff N : ℝ) ^ 12 / Real.sqrt (N : ℝ) := by
    filter_upwards [hlarge, hN] with N hlogN hNpos
    let x : ℝ := Real.log (N : ℝ)
    let K : ℝ := spatialLogCutoff N
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hNpos
    have hx : 2 ≤ x := by exact_mod_cast hlogN
    have hKlower : x ≤ K := by
      dsimp [x, K, spatialLogCutoff]
      exact Nat.le_ceil _
    have hpow9 : 8 ≤ x ^ 9 := by
      have hpow : (2 : ℝ) ^ 9 ≤ x ^ 9 :=
        pow_le_pow_left₀ (by norm_num) hx 9
      norm_num at hpow ⊢
      exact le_trans (by norm_num) hpow
    have hpow10 : 2 * x ≤ K ^ 10 / 4 := by
      have hbase : 2 * x ≤ x ^ 10 / 4 := by
        have hx10 : x ^ 10 = x ^ 9 * x := by ring
        rw [hx10]
        nlinarith [mul_le_mul_of_nonneg_right hpow9 (by linarith : 0 ≤ x)]
      have hKpow : x ^ 10 ≤ K ^ 10 := pow_le_pow_left₀ (by linarith) hKlower 10
      exact hbase.trans (div_le_div_of_nonneg_right hKpow (by norm_num))
    have hexpOrder :
        Real.exp (-((K ^ 10) / 4)) ≤ Real.exp (-2 * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hexpLog : Real.exp (-2 * x) = 1 / (N : ℝ) ^ 2 := by
      calc
        _ = (Real.exp (x + x))⁻¹ := by
          rw [show -2 * x = -(x + x) by ring, Real.exp_neg]
        _ = 1 / (N : ℝ) ^ 2 := by
          rw [Real.exp_add, Real.exp_log (by positivity : 0 < (N : ℝ))]
          ring
    have hKge1 : 1 ≤ K := by linarith
    have hKpow : K ^ 2 ≤ K ^ 12 := by
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hKge1 10
      nlinarith [show K ^ 12 = K ^ 2 * K ^ 10 by ring]
    have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hrootle : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
        Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ))
      nlinarith [Real.sqrt_nonneg (N : ℝ), hsq]
    have hratio : K ^ 2 / (N : ℝ) ≤ K ^ 12 / Real.sqrt (N : ℝ) := by
      calc
        _ ≤ K ^ 12 / (N : ℝ) :=
          div_le_div_of_nonneg_right hKpow (Nat.cast_nonneg _)
        _ ≤ K ^ 12 / Real.sqrt (N : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hsqrtN hrootle
    have hupper : (N : ℝ) * K ^ 2 * Real.exp (-(K ^ 10 / 4)) ≤
        K ^ 2 / (N : ℝ) := by
      calc
        _ ≤ (N : ℝ) * K ^ 2 * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hexpOrder.trans_eq hexpLog)
            (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg K))
      _ = K ^ 2 / (N : ℝ) := by
        field_simp [ne_of_gt (by positivity : (0 : ℝ) < (N : ℝ))]
    exact ⟨by positivity, by simpa [K] using hupper.trans hratio⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hpowLim
  · filter_upwards with N
    positivity
  · filter_upwards [hbound] with N hN
    exact hN.2

private theorem sampledGaussianBlock_den_pos (m : ℕ) (hm : 0 < m) :
    0 < ∑ k ∈ Finset.range (m + 1), sampledHypergeometricGaussianWeight m k := by
  apply Finset.sum_pos
  · intro k hk
    unfold sampledHypergeometricGaussianWeight
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    positivity
  · exact ⟨0, by simp⟩

private theorem normalizedSampledHypergeometricGaussianWeight_sum_one
    (m : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k = 1 := by
  unfold normalizedSampledHypergeometricGaussianWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (sampledGaussianBlock_den_pos m hm))

private theorem naturalBlockLawExtension_of_nat
    (n j : ℕ) (f : ℕ → ℝ) (hj : j ≤ n) :
    naturalBlockLawExtension n f (j : ℤ) = f j := by
  simp [naturalBlockLawExtension, hj]

/-- Expand a finite natural convolution by its left-hand index. -/
theorem finiteNaturalConvolution_eq_sum_left {m n : ℕ}
    (p q : ℕ → ℝ) (k : ℕ) :
    finiteNaturalConvolution m n p q k =
      ∑ i ∈ (Finset.range (m + 1)).filter (fun i => i ≤ k ∧ k - i ≤ n),
        p i * q (k - i) := by
  classical
  let A := Finset.range (m + 1)
  let B := Finset.range (n + 1)
  let F := (A.product B).filter (fun ij => ij.1 + ij.2 = k)
  let T := A.filter (fun i => i ≤ k ∧ k - i ≤ n)
  unfold finiteNaturalConvolution
  change (∑ ij ∈ F, p ij.1 * q ij.2) =
    ∑ i ∈ T, p i * q (k - i)
  refine Finset.sum_bij (s := F) (t := T) (fun ij _ => ij.1) ?_ ?_ ?_ ?_
  · intro ij hij
    have hmem := (Finset.mem_filter.mp hij).1
    have hsum := (Finset.mem_filter.mp hij).2
    have hpair := Finset.mem_product.mp hmem
    simp only [T, Finset.mem_filter]
    refine ⟨hpair.1, ?_⟩
    constructor
    · omega
    · have hj : ij.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hpair.2)
      have hsub : k - ij.1 = ij.2 := by omega
      simpa [hsub] using hj
  · intro ij hij ij' hij' hmap
    have hsum := (Finset.mem_filter.mp hij).2
    have hsum' := (Finset.mem_filter.mp hij').2
    have hsnd : ij.2 = ij'.2 := by omega
    exact Prod.ext hmap hsnd
  · intro i hi
    have hi' : i ≤ m := by
      have := (Finset.mem_filter.mp hi).1
      simp only [A, Finset.mem_range] at this
      omega
    have hprops := (Finset.mem_filter.mp hi).2
    refine ⟨(i, k - i), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi'),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hprops.2)⟩
      · omega
    · rfl
  · intro ij hij
    have hsum := (Finset.mem_filter.mp hij).2
    have hsnd : ij.2 = k - ij.1 := by omega
    rw [hsnd]

/-- Spatial displacement of the long-block remainder after short marks `a,b`. -/
def shortShiftSite (z : Site) (S a b : ℕ) : Site :=
  ![z 0 + (S : ℤ) - (a : ℤ) - (b : ℤ),
    z 1 + (b : ℤ) - (a : ℤ)]

private theorem shortShiftSite_coordinate_bounds (S a b : ℕ)
    (ha : a ≤ S) (hb : b ≤ S) :
    |(S : ℝ) - a - b| ≤ S ∧ |(b : ℝ) - a| ≤ S := by
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have haS : (a : ℝ) ≤ S := by exact_mod_cast ha
  have hbS : (b : ℝ) ≤ S := by exact_mod_cast hb
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

private theorem heatKernel_compact_slab_modulus
    (δ R ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ p ∈ (Set.Icc (δ / 8) (1 / 2) ×ˢ
        Metric.closedBall (0 : Plane) (2 * |R| + 2)),
      ∀ q ∈ (Set.Icc (δ / 8) (1 / 2) ×ˢ
        Metric.closedBall (0 : Plane) (2 * |R| + 2)),
        dist p q < ρ →
          |heatKernel p.1 p.2 - heatKernel q.1 q.2| < ε := by
  let K : Set (ℝ × Plane) := Set.Icc (δ / 8) (1 / 2) ×ˢ
    Metric.closedBall 0 (2 * |R| + 2)
  have hcompact : IsCompact K :=
    isCompact_Icc.prod (isCompact_closedBall 0 (2 * |R| + 2))
  have hcontinuous : ContinuousOn
      (fun p : ℝ × Plane => heatKernel p.1 p.2) K := by
    apply (Critical2DKPZ.DeltaBose.continuousOn_heatKernel).mono
    intro p hp
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < δ / 8)
      (Set.mem_Icc.mp hp.1).1
  have huniform : UniformContinuousOn
      (fun p : ℝ × Plane => heatKernel p.1 p.2) K :=
    hcompact.uniformContinuousOn_of_continuous hcontinuous
  obtain ⟨ρ, hρ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huniform ε hε
  refine ⟨ρ, hρ, ?_⟩
  intro p hp q hq hdist
  have h := hmod p hp q hq hdist
  simpa only [Real.dist_eq] using h

private theorem spatialScale_le_two_div_sqrt (N : ℕ) (hN : 1 ≤ N) :
    (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 2 / Real.sqrt (N : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hrootHalf : Real.sqrt (N : ℝ) / 2 ≤ Real.sqrt ((N : ℝ) / 2) := by
    have hsqrtn : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNreal.le
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
    nlinarith
  have hbound : 1 / Real.sqrt ((N : ℝ) / 2) ≤ 2 / Real.sqrt (N : ℝ) :=
    (div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hroot).2
      (by nlinarith [hrootHalf])
  simpa [one_div] using hbound

private theorem shortShift_scaled_space_bounds
    (N S : ℕ) (R : ℝ) (hN : 1 ≤ N)
    (z : Site) (hz : ‖siteToPlane z‖ ≤ R * Real.sqrt N)
    (a b : ℕ) (ha : a ≤ S) (hb : b ≤ S) :
    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ 2 * |R| ∧
    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ •
        siteToPlane (shortShiftSite z S a b)‖ ≤
      2 * |R| + 4 * (S : ℝ) / Real.sqrt (N : ℝ) ∧
    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ •
        siteToPlane (shortShiftSite z S a b) -
        (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤
      4 * (S : ℝ) / Real.sqrt (N : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hαbound := spatialScale_le_two_div_sqrt N hN
  have hαpos : 0 < (Real.sqrt ((N : ℝ) / 2))⁻¹ := by positivity
  have hzplane : ‖siteToPlane z‖ ≤ |R| * Real.sqrt (N : ℝ) := by
    exact le_trans hz (mul_le_mul_of_nonneg_right (le_abs_self R) (Real.sqrt_nonneg _))
  have hxnorm : ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ 2 * |R| := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαpos]
    calc
      _ ≤ (2 / Real.sqrt (N : ℝ)) * (|R| * Real.sqrt (N : ℝ)) :=
        mul_le_mul hαbound hzplane (norm_nonneg _) (by positivity)
      _ = 2 * |R| := by field_simp [hroot.ne']
  let z' := shortShiftSite z S a b
  let d : Site := z' - z
  have hcoords := shortShiftSite_coordinate_bounds S a b ha hb
  have hshift0 : shortShiftSite z S a b 0 =
      z 0 + (S : ℤ) - (a : ℤ) - (b : ℤ) := by simp [shortShiftSite]
  have hshift1 : shortShiftSite z S a b 1 =
      z 1 + (b : ℤ) - (a : ℤ) := by simp [shortShiftSite]
  have hdcoord0 : ((d 0 : ℤ) : ℝ) = (S : ℝ) - a - b := by
    change ((shortShiftSite z S a b 0 - z 0 : ℤ) : ℝ) = _
    rw [hshift0]
    push_cast
    ring
  have hdcoord1 : ((d 1 : ℤ) : ℝ) = (b : ℝ) - a := by
    change ((shortShiftSite z S a b 1 - z 1 : ℤ) : ℝ) = _
    rw [hshift1]
    push_cast
    ring
  have hd0sq : ((d 0 : ℤ) : ℝ) ^ 2 ≤ (S : ℝ) ^ 2 := by
    rw [hdcoord0]
    have h := (sq_le_sq₀ (abs_nonneg ((S : ℝ) - a - b)) (Nat.cast_nonneg S)).2 hcoords.1
    simpa [sq_abs] using h
  have hd1sq : ((d 1 : ℤ) : ℝ) ^ 2 ≤ (S : ℝ) ^ 2 := by
    rw [hdcoord1]
    have h := (sq_le_sq₀ (abs_nonneg ((b : ℝ) - a)) (Nat.cast_nonneg S)).2 hcoords.2
    simpa [sq_abs] using h
  have hnormSq : ‖siteToPlane d‖ ^ 2 ≤ (2 * (S : ℝ)) ^ 2 := by
    rw [Critical2DKPZ.norm_siteToPlane_sq]
    nlinarith [hd0sq, hd1sq]
  have hsiteShift : ‖siteToPlane z' - siteToPlane z‖ ≤ 2 * (S : ℝ) := by
    have hsite : siteToPlane d = siteToPlane z' - siteToPlane z := by
      ext i
      simp [d, z', siteToPlane]
    rw [← hsite]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hnormSq
  have hspacele :
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z' -
        (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤
        4 * (S : ℝ) / Real.sqrt (N : ℝ) := by
    calc
      _ = ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ •
            (siteToPlane z' - siteToPlane z)‖ := by rw [← smul_sub]
      _ = |(Real.sqrt ((N : ℝ) / 2))⁻¹| *
            ‖siteToPlane z' - siteToPlane z‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ * (2 * (S : ℝ)) := by
        rw [abs_of_pos hαpos]
        exact mul_le_mul_of_nonneg_left hsiteShift hαpos.le
      _ ≤ (2 / Real.sqrt (N : ℝ)) * (2 * (S : ℝ)) :=
        mul_le_mul_of_nonneg_right hαbound (by positivity)
      _ = 4 * (S : ℝ) / Real.sqrt (N : ℝ) := by ring
  have hshifted :
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z'‖ ≤
        2 * |R| + 4 * (S : ℝ) / Real.sqrt (N : ℝ) := by
    calc
      _ ≤ ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ +
          ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z' -
            (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ := by
        have h := norm_le_norm_add_norm_sub
          ((Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z)
          ((Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z')
        simpa only [norm_sub_rev] using h
      _ ≤ 2 * |R| + 4 * (S : ℝ) / Real.sqrt (N : ℝ) := add_le_add hxnorm hspacele
  exact ⟨hxnorm, hshifted, hspacele⟩

private theorem shortShift_time_bounds
    (δ ρ η : ℝ) (hNδ : 0 < δ) (hρ : 0 < ρ)
    (hηδ : η ≤ δ / 4) (hηρ : η ≤ ρ / 8)
    (N n L S : ℕ) (hN : 1 ≤ N)
    (hnLower : δ * (N : ℝ) ≤ n) (hnUpper : n ≤ N)
    (hsum : L + S = n) (hSN : (S : ℝ) / (N : ℝ) < η) :
    δ / 8 < (L : ℝ) / (2 * N) ∧
    δ / 8 ≤ (n : ℝ) / (2 * N) ∧
    (L : ℝ) / (2 * N) ≤ 1 / 2 ∧
    (n : ℝ) / (2 * N) ≤ 1 / 2 ∧
    |(L : ℝ) / (2 * N) - (n : ℝ) / (2 * N)| < ρ := by
  have hNpos : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hSsmall : (S : ℝ) / (N : ℝ) < δ / 4 := lt_of_lt_of_le hSN hηδ
  have hsumR : (L : ℝ) + (S : ℝ) = (n : ℝ) := by exact_mod_cast hsum
  have htimeEq :
      |(L : ℝ) / (2 * N) - (n : ℝ) / (2 * N)| = (S : ℝ) / (2 * N) := by
    rw [← hsumR]
    have hSnonneg : 0 ≤ (S : ℝ) := Nat.cast_nonneg _
    rw [show (L : ℝ) / (2 * N) - ((L : ℝ) + (S : ℝ)) / (2 * N) =
      -((S : ℝ) / (2 * N)) by ring, abs_neg,
      abs_of_nonneg (div_nonneg hSnonneg (by positivity))]
  have htime : |(L : ℝ) / (2 * N) - (n : ℝ) / (2 * N)| < ρ := by
    rw [htimeEq]
    have htimeLe : (S : ℝ) / (2 * N) ≤ (S : ℝ) / (N : ℝ) := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg S) hNreal
      nlinarith
    have htimeSmall : (S : ℝ) / (2 * N) < η := htimeLe.trans_lt hSN
    calc
      _ < η := htimeSmall
      _ ≤ ρ / 8 := hηρ
      _ < ρ := by nlinarith [hρ]
  have hLcast : (L : ℝ) + (S : ℝ) = (n : ℝ) := hsumR
  have hLtimeLower : δ / 8 < (L : ℝ) / (2 * N) := by
    have hnDiv : δ ≤ (n : ℝ) / (N : ℝ) :=
      (le_div_iff₀ hNreal).2 (by nlinarith [hnLower])
    have hLdivEq : (L : ℝ) / (N : ℝ) =
        (n : ℝ) / (N : ℝ) - (S : ℝ) / (N : ℝ) := by
      rw [← hLcast]
      field_simp [hNreal.ne']
      ring
    have hLdiv : δ - (S : ℝ) / (N : ℝ) ≤ (L : ℝ) / (N : ℝ) := by
      calc
        _ ≤ (n : ℝ) / (N : ℝ) - (S : ℝ) / (N : ℝ) := sub_le_sub_right hnDiv _
        _ = _ := hLdivEq.symm
    have hLdiv' : δ / 2 < (L : ℝ) / (N : ℝ) := by linarith [hSsmall]
    have hLtime : δ / 4 < (L : ℝ) / (2 * N) := by
      calc
        _ = (δ / 2) / 2 := by ring
        _ < ((L : ℝ) / (N : ℝ)) / 2 :=
          div_lt_div_of_pos_right hLdiv' (by norm_num)
        _ = (L : ℝ) / (2 * N) := by field_simp [hNreal.ne']
    linarith
  have hnTime : δ / 8 ≤ (n : ℝ) / (2 * N) := by
    have hnDiv : δ ≤ (n : ℝ) / (N : ℝ) :=
      (le_div_iff₀ hNreal).2 (by nlinarith [hnLower])
    have hnTime' : δ / 2 ≤ ((n : ℝ) / (N : ℝ)) / 2 :=
      div_le_div_of_nonneg_right hnDiv (by norm_num)
    have htimeEq' : ((n : ℝ) / (N : ℝ)) / 2 = (n : ℝ) / (2 * N) := by
      field_simp [hNreal.ne']
    calc
      _ ≤ δ / 2 := by linarith
      _ ≤ ((n : ℝ) / (N : ℝ)) / 2 := hnTime'
      _ = _ := htimeEq'
  have hLtimeUpper : (L : ℝ) / (2 * N) ≤ 1 / 2 := by
    have hLn : L ≤ n := by omega
    have hLnR : (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLn
    have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnUpper
    calc
      _ ≤ (n : ℝ) / (2 * N) := div_le_div_of_nonneg_right hLnR (by positivity)
      _ ≤ (N : ℝ) / (2 * N) := div_le_div_of_nonneg_right hnR (by positivity)
      _ = 1 / 2 := by field_simp [hNreal.ne']
  have hnTimeUpper : (n : ℝ) / (2 * N) ≤ 1 / 2 := by
    have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnUpper
    calc
      _ ≤ (N : ℝ) / (2 * N) := div_le_div_of_nonneg_right hnR (by positivity)
      _ = 1 / 2 := by field_simp [hNreal.ne']
  exact ⟨hLtimeLower, hnTime, hLtimeUpper, hnTimeUpper, htime⟩

/-- Uniform heat-kernel continuity under the deterministic short-block time and space shifts. -/
theorem eventually_heatKernel_short_shift_error
    (δ R ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ n L S : ℕ, δ * (N : ℝ) ≤ n → n ≤ N →
      L + S = n → (S : ℝ) ≤ (spatialLogCutoff N : ℝ) ^ 12 →
      ∀ z : Site, ‖siteToPlane z‖ ≤ R * Real.sqrt N →
      ∀ a b : ℕ, a ≤ S → b ≤ S →
        |heatKernel ((L : ℝ) / (2 * N))
            ((Real.sqrt (N / 2))⁻¹ • siteToPlane (shortShiftSite z S a b)) -
          heatKernel ((n : ℝ) / (2 * N))
            ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| < ε := by
  obtain ⟨ρ, hρ, hmod⟩ := heatKernel_compact_slab_modulus δ R ε hδ hε
  let η : ℝ := min (ρ / 8) (min (1 / 8) (δ / 4))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η ≤ δ / 4 := by
    dsimp [η]
    exact min_le_right _ _ |>.trans (min_le_right _ _)
  have hηρ : η ≤ ρ / 8 := by dsimp [η]; exact min_le_left _ _
  have hηsmall : η ≤ 1 / 8 := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hratio := eventually_spatialLogCutoff_pow12_div_sqrt_lt hη
  filter_upwards [hratio, eventually_ge_atTop 1] with N hratioN hN
  intro n L S hnLower hnUpper hsum hS z hz a b ha hb
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hrootOne : 1 ≤ Real.sqrt (N : ℝ) := by
    have hNle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h := Real.sqrt_le_sqrt hNle
    simpa using h
  have hrootLe : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNreal.le
    have hmul := mul_le_mul_of_nonneg_right hrootOne (Real.sqrt_nonneg (N : ℝ))
    have hmul' : Real.sqrt (N : ℝ) ≤ Real.sqrt (N : ℝ) ^ 2 := by
      simpa [pow_two] using hmul
    simpa [hsq] using hmul'
  have hratioN' : (spatialLogCutoff N : ℝ) ^ 12 /
      Real.sqrt (N : ℝ) < η := by
    simpa only [spatialLogCutoff] using hratioN
  have hSroot : (S : ℝ) / Real.sqrt (N : ℝ) < η := by
    calc
      _ ≤ (spatialLogCutoff N : ℝ) ^ 12 / Real.sqrt (N : ℝ) :=
        div_le_div_of_nonneg_right hS hroot.le
      _ < η := hratioN'
  have hSN : (S : ℝ) / (N : ℝ) < η := by
    calc
      _ ≤ (spatialLogCutoff N : ℝ) ^ 12 / (N : ℝ) :=
        div_le_div_of_nonneg_right hS hNreal.le
      _ ≤ (spatialLogCutoff N : ℝ) ^ 12 / Real.sqrt (N : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hroot
          hrootLe
      _ < η := hratioN'
  have htime := shortShift_time_bounds δ ρ η hδ hρ hηδ hηρ
    N n L S (by omega) hnLower hnUpper hsum hSN
  have hspace := shortShift_scaled_space_bounds N S R (by omega) z hz a b ha hb
  have hspaceSmall : 4 * (S : ℝ) / Real.sqrt (N : ℝ) < ρ := by
    calc
      _ = 4 * ((S : ℝ) / Real.sqrt (N : ℝ)) := by ring
      _ < 4 * η := mul_lt_mul_of_pos_left hSroot (by norm_num)
      _ ≤ 4 * (ρ / 8) := mul_le_mul_of_nonneg_left hηρ (by norm_num)
      _ = ρ / 2 := by ring
      _ < ρ := div_lt_self hρ (by norm_num : (1 : ℝ) < 2)
  have hshiftSmall : 4 * (S : ℝ) / Real.sqrt (N : ℝ) < 1 := by
    calc
      _ = 4 * ((S : ℝ) / Real.sqrt (N : ℝ)) := by ring
      _ < 4 * η := mul_lt_mul_of_pos_left hSroot (by norm_num)
      _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left hηsmall (by norm_num)
      _ < 1 := by norm_num
  let α : ℝ := (Real.sqrt (N / 2))⁻¹
  let z' := shortShiftSite z S a b
  have hp : ((L : ℝ) / (2 * N), α • siteToPlane z') ∈
      Set.Icc (δ / 8) (1 / 2) ×ˢ Metric.closedBall 0 (2 * |R| + 2) := by
    refine ⟨⟨htime.1.le, htime.2.2.1⟩, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ 2 * |R| + 4 * (S : ℝ) / Real.sqrt (N : ℝ) := hspace.2.1
      _ ≤ 2 * |R| + 1 := by linarith [hshiftSmall.le]
      _ ≤ 2 * |R| + 2 := by linarith
  have hq : ((n : ℝ) / (2 * N), α • siteToPlane z) ∈
      Set.Icc (δ / 8) (1 / 2) ×ˢ Metric.closedBall 0 (2 * |R| + 2) := by
    refine ⟨⟨htime.2.1, htime.2.2.2.1⟩, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_trans hspace.1 (by linarith)
  have hdist : dist ((L : ℝ) / (2 * N), α • siteToPlane z')
      ((n : ℝ) / (2 * N), α • siteToPlane z) < ρ := by
    rw [dist_eq_norm]
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    exact max_lt_iff.mpr ⟨htime.2.2.2.2,
      lt_of_le_of_lt hspace.2.2 hspaceSmall⟩
  have hkernel := hmod _ hp _ hq hdist
  simpa [α, Real.dist_eq] using hkernel

/-- If every block is below the cutoff, the hybrid law is exactly hypergeometric. -/
theorem largeBlockGaussianListLaw_eq_hypergeometric_of_all_lt
    (mCut : ℕ) (ms : List ℕ) (hshort : ∀ m ∈ ms, m < mCut) (j : ℕ) :
    largeBlockGaussianListLaw mCut ms j = hypergeometricBlockListLaw ms j := by
  induction ms generalizing j with
  | nil => simp [largeBlockGaussianListLaw, hypergeometricBlockListLaw]
  | cons m ms ih =>
      have hm : m < mCut := hshort m (by simp)
      have htail : ∀ a ∈ ms, a < mCut := by
        intro a ha
        exact hshort a (by simp [ha])
      have htailLaw : largeBlockGaussianListLaw mCut ms = hypergeometricBlockListLaw ms := by
        funext k
        exact ih htail k
      have hnot : ¬ mCut ≤ m := by omega
      have hweight : largeBlockGaussianWeight mCut m = WalkTails.hypergeometricWeight m := by
        funext k
        simp [largeBlockGaussianWeight, hnot]
      change finiteNaturalConvolution m ms.sum
        (largeBlockGaussianWeight mCut m) (largeBlockGaussianListLaw mCut ms) j =
        finiteNaturalConvolution m ms.sum
          (WalkTails.hypergeometricWeight m) (hypergeometricBlockListLaw ms) j
      rw [hweight, htailLaw]

private theorem largeBlockGaussianListLaw_eq_sampledGaussianBlockListProbability_of_all_ge
    (mCut : ℕ) (ms : List ℕ) (hall : ∀ m ∈ ms, mCut ≤ m)
    (j : ℕ) (hj : j ≤ ms.sum) :
    largeBlockGaussianListLaw mCut ms j =
      sampledGaussianBlockListProbability ms (j : ℤ) := by
  have hnormalized := largeBlockGaussianListLaw_eq_normalized_of_all_ge
    mCut ms hall j
  have hjext : naturalBlockLawExtension ms.sum
      (normalizedGaussianBlockListLaw ms) (j : ℤ) =
      normalizedGaussianBlockListLaw ms j :=
    naturalBlockLawExtension_of_nat ms.sum j
      (normalizedGaussianBlockListLaw ms) hj
  calc
    _ = normalizedGaussianBlockListLaw ms j := hnormalized
    _ = naturalBlockLawExtension ms.sum
        (normalizedGaussianBlockListLaw ms) (j : ℤ) := hjext.symm
    _ = sampledGaussianBlockListProbability ms (j : ℤ) :=
      (sampledGaussianBlockListProbability_eq_normalizedGaussianBlockListLaw_extension
        ms (j : ℤ)).symm

/-- A linear factor is dominated by exponential decay along the natural scale. -/
theorem tendsto_nat_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-a * (N : ℝ))) atTop (𝓝 0) := by
  have hscaled : Tendsto (fun N : ℕ => a * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hpow := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscaled
  convert hpow.const_mul a⁻¹ using 1
  · ext N
    simp only [Function.comp_apply, pow_one]
    rw [show -(a * (N : ℝ)) = -a * (N : ℝ) by ring]
    field_simp [ha.ne']
  · simp

/-- The full-lattice Gaussian composition profile converges uniformly on
positive time slabs after the diffusive scaling. -/
private theorem eventually_fullGaussianBlockListPair_heat_error
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ms : List ℕ, ms ≠ [] →
      ms.length ≤ spatialLogCutoff N ^ 2 →
      (∀ m ∈ ms, 0 < m) →
      (∀ m ∈ ms, spatialLogCutoff N ^ 10 ≤ m) →
      δ * (N : ℝ) ≤ (ms.sum : ℝ) → (ms.sum : ℝ) ≤ N →
      ∀ z : Site, ∀ j₁ j₂ : ℤ,
        2 * j₁ = (ms.sum : ℤ) + z 0 + z 1 →
        2 * j₂ = (ms.sum : ℤ) + z 0 - z 1 →
        |(N / 4 : ℝ) * fullGaussianBlockListProbability ms j₁ *
            fullGaussianBlockListProbability ms j₂ -
          heatKernel ((ms.sum : ℝ) / (2 * N))
            ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| < ε := by
  have hlogT := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := hlogT.eventually_ge_atTop 2
  have hN := eventually_ge_atTop 1
  have hratio := eventually_spatialLogCutoff_pow12_div_sqrt_lt
    (by positivity : (0 : ℝ) < ε / 64)
  have hdecaySmall := (tendsto_nat_mul_exp_neg δ hδ).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hNexp := tendsto_nat_mul_exp_neg δ hδ |>.eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
  filter_upwards [hlog, hN, hratio, hdecaySmall, hNexp]
    with N hlogN hNpos hratioN hdecayN hNexpN
  intro ms hne hlen hpositive hall hsumLower hsumUpper z j₁ j₂ h₁ h₂
  let K : ℕ := spatialLogCutoff N
  let M : ℕ := K ^ 10
  have hNpos' : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos'
  have hceil : Real.log (N : ℝ) ≤ (K : ℝ) := by
    dsimp [K, spatialLogCutoff]
    exact Nat.le_ceil _
  have hlog2 : 2 ≤ Real.log (N : ℝ) := hlogN
  have hKlower : 2 ≤ (K : ℝ) := le_trans hlog2 hceil
  have hKpow9 : 8 ≤ (K : ℝ) ^ 9 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hKlower 9
    norm_num at h ⊢
    exact le_trans (by norm_num) h
  have hMlog : 2 * Real.log (N : ℝ) ≤ (M : ℝ) := by
    have hK10 : 2 * (K : ℝ) ≤ (K : ℝ) ^ 10 := by
      have h := mul_le_mul_of_nonneg_right hKpow9 (by positivity : 0 ≤ (K : ℝ))
      have hpow : (K : ℝ) ^ 10 = (K : ℝ) ^ 9 * (K : ℝ) := by ring
      rw [hpow]
      nlinarith
    have hKlog : Real.log (N : ℝ) ≤ (K : ℝ) := hceil
    have hMcast : (M : ℝ) = (K : ℝ) ^ 10 := by
      dsimp [M]
      norm_cast
    rw [hMcast]
    nlinarith
  have hpi8 : (1 : ℝ) ≤ Real.pi ^ 2 / 8 := by
    nlinarith [Real.pi_gt_three]
  have hpi4 : (1 : ℝ) ≤ Real.pi ^ 2 / 4 := by
    nlinarith [Real.pi_gt_three]
  have hMq : (M : ℝ) ≤ (ms.sum : ℝ) := by
    have hsumNat : M ≤ ms.sum := by
      cases ms with
      | nil => exact (hne rfl).elim
      | cons m ms =>
          have hm := hall m (by simp)
          simpa [M, K] using Nat.le_trans hm (Nat.le_add_right m ms.sum)
    exact_mod_cast hsumNat
  have hMqNat : M ≤ ms.sum := by exact_mod_cast hMq
  have hMpos : 0 < M := by
    have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < (K : ℝ) by linarith)
    exact Nat.pow_pos hKpos
  have hargLower : 7 ≤ (Real.pi ^ 2 / 8) * (M : ℝ) := by
    have hMlarge : 7 ≤ (M : ℝ) := by
      have hKlarge : 2 ≤ K := by exact_mod_cast hKlower
      have hMp : (1024 : ℕ) ≤ M := by
        dsimp [M]
        exact (by norm_num : 1024 ≤ 2 ^ 10).trans
          (Nat.pow_le_pow_left hKlarge 10)
      exact_mod_cast (le_trans (by norm_num) hMp)
    nlinarith [mul_le_mul_of_nonneg_right hpi8 (Nat.cast_nonneg M)]
  have hExpEight : 8 ≤ Real.exp ((Real.pi ^ 2 / 8) * (M : ℝ)) := by
    have h := Real.add_one_le_exp ((Real.pi ^ 2 / 8) * (M : ℝ))
    linarith
  have hq : Real.exp (-((Real.pi ^ 2 / 8) * (M : ℝ))) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 8)).2 hExpEight
  have hq' : Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) ≤ 1 / 8 := by
    simpa only [neg_mul] using hq
  have hExpM : Real.exp (-(M : ℝ)) ≤ 1 / (N : ℝ) ^ 2 := by
    have horder : -(M : ℝ) ≤ -2 * Real.log (N : ℝ) := by nlinarith [hMlog]
    calc
      _ ≤ Real.exp (-2 * Real.log (N : ℝ)) := Real.exp_le_exp.mpr horder
      _ = 1 / (N : ℝ) ^ 2 := by
        rw [show -2 * Real.log (N : ℝ) =
          -(Real.log (N : ℝ) + Real.log (N : ℝ)) by ring,
          Real.exp_neg, Real.exp_add, Real.exp_log hNreal]
        ring
  have hprofileExp :
      Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) ≤ Real.exp (-(M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hpi8 (Nat.cast_nonneg M)]
  have htheta := fullGaussianBlockMassThetaError_le_exp_of_cutoff
    M ms.sum hMpos hMqNat hq'
  have hthetaPos : 0 ≤ fullGaussianBlockMassThetaError ms.sum :=
    fullGaussianBlockMassThetaError_nonneg ms.sum
      (by cases ms with | nil => exact (hne rfl).elim | cons m ms =>
        exact lt_of_lt_of_le (hpositive m (by simp)) (Nat.le_add_right _ _))
  have hthetaBound : fullGaussianBlockMassThetaError ms.sum ≤
      (16 / 7 : ℝ) * Real.exp (-δ * (N : ℝ)) := by
    apply le_trans htheta
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16 / 7)
    apply Real.exp_le_exp.mpr
    have hsumCast : δ * (N : ℝ) ≤ (ms.sum : ℝ) := hsumLower
    nlinarith [hpi4, hsumCast]
  have hthetaLeOne : fullGaussianBlockMassThetaError ms.sum ≤ 1 := by
    calc
      _ ≤ (16 / 7 : ℝ) * Real.exp (-δ * (N : ℝ)) := hthetaBound
      _ ≤ 1 := by
        have hExp : Real.exp (-δ * (N : ℝ)) < 1 / 16 := by
          have hNle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
          have hmul : Real.exp (-δ * (N : ℝ)) ≤
              (N : ℝ) * Real.exp (-δ * (N : ℝ)) := by
            have hexpNonneg := Real.exp_nonneg (-δ * (N : ℝ))
            nlinarith
          exact lt_of_le_of_lt hmul (by simpa [mul_comm] using hdecayN)
        nlinarith [Real.exp_pos (-δ * (N : ℝ))]
  have hsmallKernel := spatialLogCutoff_kernel_error_small N K ε hNpos
    (by
      have hKnat : 2 ≤ K := by exact_mod_cast hKlower
      omega) hratioN
  have hsmallTheta : (12 / 7 : ℝ) * (N : ℝ) *
      Real.exp (-δ * (N : ℝ)) < ε / 2 := by
    nlinarith only [hNexpN, hε]
  have hfull := fullGaussianBlockListPair_heatKernel_error_of_cutoff
    N M hNpos' hMpos hq' ms hne hpositive hall z j₁ j₂ h₁ h₂
  have hprofileScaled : (N / 2 : ℝ) * (ms.length : ℝ) *
      (64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))) ≤
      32 * (K : ℝ) ^ 2 / (N : ℝ) := by
    have hlenR : (ms.length : ℝ) ≤ (K : ℝ) ^ 2 := by
      exact_mod_cast hlen
    have hfirst :
        (N / 2 : ℝ) * (ms.length : ℝ) *
          (64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))) ≤
        32 * (N : ℝ) * (ms.length : ℝ) * Real.exp (-(M : ℝ)) := by
      have hcoef : 0 ≤ (N / 2 : ℝ) * (ms.length : ℝ) * 64 := by positivity
      calc
        _ = ((N / 2 : ℝ) * (ms.length : ℝ) * 64) *
            Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) := by ring
        _ ≤ ((N / 2 : ℝ) * (ms.length : ℝ) * 64) *
            Real.exp (-(M : ℝ)) := mul_le_mul_of_nonneg_left hprofileExp hcoef
        _ = _ := by ring
    calc
      _ ≤ 32 * (N : ℝ) * (ms.length : ℝ) * Real.exp (-(M : ℝ)) := hfirst
      _ ≤ 32 * (N : ℝ) * (K : ℝ) ^ 2 * Real.exp (-(M : ℝ)) := by
        gcongr
      _ ≤ 32 * (N : ℝ) * (K : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) := by
        gcongr
      _ = 32 * (K : ℝ) ^ 2 / (N : ℝ) := by
        field_simp [hNreal.ne']
  have hthetaScaled : (N / 4 : ℝ) *
      (2 * fullGaussianBlockMassThetaError ms.sum +
        fullGaussianBlockMassThetaError ms.sum ^ 2) < ε / 2 := by
    have hsq : fullGaussianBlockMassThetaError ms.sum ^ 2 ≤
        fullGaussianBlockMassThetaError ms.sum := by
      have h := mul_le_mul_of_nonneg_left hthetaLeOne hthetaPos
      simpa [pow_two] using h
    have hpoly : 2 * fullGaussianBlockMassThetaError ms.sum +
        fullGaussianBlockMassThetaError ms.sum ^ 2 ≤
        3 * fullGaussianBlockMassThetaError ms.sum := by
      nlinarith only [hsq]
    calc
      _ ≤ (N / 4 : ℝ) *
          (3 * fullGaussianBlockMassThetaError ms.sum) := by
        gcongr
      _ ≤ (12 / 7 : ℝ) * (N : ℝ) * Real.exp (-δ * (N : ℝ)) := by
        rw [show (N / 4 : ℝ) *
          (3 * fullGaussianBlockMassThetaError ms.sum) =
            (3 / 4 : ℝ) * (N : ℝ) * fullGaussianBlockMassThetaError ms.sum by ring]
        calc
          _ ≤ (3 / 4 : ℝ) * (N : ℝ) *
              ((16 / 7 : ℝ) * Real.exp (-δ * (N : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hthetaBound
              (by positivity : 0 ≤ (3 / 4 : ℝ) * (N : ℝ))
          _ = (12 / 7 : ℝ) * (N : ℝ) * Real.exp (-δ * (N : ℝ)) := by ring
      _ < ε / 2 := hsmallTheta
  have hfullBound :
      |(N / 4 : ℝ) * fullGaussianBlockListProbability ms j₁ *
          fullGaussianBlockListProbability ms j₂ -
        heatKernel ((ms.sum : ℝ) / (2 * (N : ℝ)))
          ((Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z)| < ε := by
    have htriangle := hfull
    have herror := htriangle.trans (add_le_add hprofileScaled hthetaScaled.le)
    linarith
  exact hfullBound

/-- On compositions whose blocks all exceed the logarithmic cutoff, replacing
their sampled Gaussian pair law by the full-lattice Gaussian pair law has
vanishing error after the diffusive `N` scaling. -/
theorem eventually_scaled_sampledGaussianBlockListPairProbability_error
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ms : List ℕ,
      ms.length ≤ spatialLogCutoff N ^ 2 →
      (∀ m ∈ ms, spatialLogCutoff N ^ 10 ≤ m) →
      (∀ m ∈ ms, 0 < m) → ∀ j₁ j₂ : ℤ,
        (N : ℝ) *
          |sampledGaussianBlockListProbability ms j₁ *
              sampledGaussianBlockListProbability ms j₂ -
            fullGaussianBlockListProbability ms j₁ *
              fullGaussianBlockListProbability ms j₂| < ε := by
  -- The cutoff threshold is uniform in the list and all its block durations.
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
    eventually_gaussianizedBlockIntProbability_l1_le_exp_quarter
  have hsmall := tendsto_spatialLogCutoff_expQuarter.eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 448))
  have hlogT := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := hlogT.eventually_gt_atTop (max (m₀ : ℝ) 2)
  filter_upwards [hsmall, hlog, eventually_ge_atTop 1] with N hsmallN hlogN hN
  let K := spatialLogCutoff N
  have hNpos : 0 < N := by omega
  have hKlarge : max m₀ 1 ≤ K := by
    have hceil : Real.log (N : ℝ) ≤ (K : ℝ) := by
      dsimp [K, spatialLogCutoff]
      exact Nat.le_ceil _
    have hm₀log : (m₀ : ℝ) < Real.log (N : ℝ) :=
      (le_max_left _ _).trans_lt hlogN
    have h2log : (2 : ℝ) < Real.log (N : ℝ) :=
      (le_max_right _ _).trans_lt hlogN
    have hm₀K : (m₀ : ℝ) ≤ (K : ℝ) := hm₀log.le.trans hceil
    have honeK : (1 : ℝ) ≤ (K : ℝ) :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (h2log.le.trans hceil)
    have hcast : max (m₀ : ℝ) 1 ≤ (K : ℝ) := max_le hm₀K honeK
    exact_mod_cast hcast
  have hKpow : K ≤ K ^ 10 := Nat.le_self_pow (by norm_num) K
  intro ms hlen hall hpositive j₁ j₂
  have hden : ∀ m ∈ ms, 0 < ∑ k ∈ Finset.range (m + 1),
      sampledHypergeometricGaussianWeight m k := by
    intro m hm
    exact sampledGaussianBlock_den_pos m (hpositive m hm)
  have hnorm : ∀ m ∈ ms, ∑ k ∈ Finset.range (m + 1),
      normalizedSampledHypergeometricGaussianWeight m k = 1 := by
    intro m hm
    exact normalizedSampledHypergeometricGaussianWeight_sum_one m (hpositive m hm)
  have hblock : ∀ m ∈ ms,
      (∑' j : ℤ,
        |gaussianizedBlockIntProbability m j - fullGaussianBlockProbability m j|) ≤
        224 * Real.exp (-((K : ℝ) ^ 10 / 4)) := by
    intro m hm
    have hmlarge : m₀ ≤ m := by
      exact le_trans (le_trans (le_max_left m₀ 1) hKlarge)
        (le_trans hKpow (hall m hm))
    have herror := hm₀ m hmlarge
    have hMle : (K : ℝ) ^ 10 ≤ (m : ℝ) := by exact_mod_cast hall m hm
    exact le_trans herror (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hMle] :
        -((m : ℝ) / 4) ≤ -((K : ℝ) ^ 10 / 4)))
      (by norm_num))
  have hsum : (ms.map fun m =>
      ∑' j : ℤ, |gaussianizedBlockIntProbability m j -
        fullGaussianBlockProbability m j|).sum ≤
      (ms.length : ℝ) * (224 * Real.exp (-((K : ℝ) ^ 10 / 4))) := by
    calc
      _ ≤ (ms.map fun _ : ℕ => 224 * Real.exp (-((K : ℝ) ^ 10 / 4))).sum :=
        List.sum_le_sum hblock
      _ = _ := by simp [nsmul_eq_mul]
  have hpair := sampledGaussianBlockListPairProbability_profileError_bound
    ms hpositive hden hnorm j₁ j₂
  have hpair' :
      |sampledGaussianBlockListProbability ms j₁ *
          sampledGaussianBlockListProbability ms j₂ -
        fullGaussianBlockListProbability ms j₁ *
          fullGaussianBlockListProbability ms j₂| ≤
      2 * ((ms.length : ℝ) * (224 * Real.exp (-((K : ℝ) ^ 10 / 4)))) :=
    hpair.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
  have hlenR : (ms.length : ℝ) ≤ (K : ℝ) ^ 2 := by
    exact_mod_cast hlen
  have hscale : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hfinal :
      (N : ℝ) *
        |sampledGaussianBlockListProbability ms j₁ *
            sampledGaussianBlockListProbability ms j₂ -
          fullGaussianBlockListProbability ms j₁ *
            fullGaussianBlockListProbability ms j₂| ≤
        448 * (N : ℝ) * (K : ℝ) ^ 2 *
          Real.exp (-((K : ℝ) ^ 10 / 4)) := by
    calc
      _ ≤ (N : ℝ) *
          (2 * ((ms.length : ℝ) *
            (224 * Real.exp (-((K : ℝ) ^ 10 / 4))))) :=
        mul_le_mul_of_nonneg_left hpair' hscale
      _ ≤ 448 * (N : ℝ) * (K : ℝ) ^ 2 *
          Real.exp (-((K : ℝ) ^ 10 / 4)) := by
        have hExpNonneg : 0 ≤ Real.exp (-((K : ℝ) ^ 10 / 4)) :=
          Real.exp_nonneg _
        have hlenE : (ms.length : ℝ) * Real.exp (-((K : ℝ) ^ 10 / 4)) ≤
            (K : ℝ) ^ 2 * Real.exp (-((K : ℝ) ^ 10 / 4)) :=
          mul_le_mul_of_nonneg_right hlenR hExpNonneg
        calc
          _ = 448 * (N : ℝ) * (ms.length : ℝ) *
              Real.exp (-((K : ℝ) ^ 10 / 4)) := by ring
          _ ≤ 448 * (N : ℝ) * ((K : ℝ) ^ 2 *
                Real.exp (-((K : ℝ) ^ 10 / 4))) := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlenE
              (by positivity : 0 ≤ 448 * (N : ℝ))
          _ = _ := by ring
  have hsmallN' :
      448 * (N : ℝ) * (K : ℝ) ^ 2 *
        Real.exp (-((K : ℝ) ^ 10 / 4)) < ε := by
    have h := hsmallN
    dsimp [K] at h ⊢
    nlinarith [h]
  exact lt_of_le_of_lt hfinal hsmallN'


/-- Long-block hybrid pair laws have the full Gaussian heat profile. -/
theorem eventually_largeBlockGaussianListPairLaw_heat_error_longBlocks
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ms : List ℕ, ms ≠ [] →
      ms.length ≤ spatialLogCutoff N ^ 2 →
      (∀ m ∈ ms, 0 < m) →
      (∀ m ∈ ms, spatialLogCutoff N ^ 10 ≤ m) →
      δ * (N : ℝ) ≤ (ms.sum : ℝ) → (ms.sum : ℝ) ≤ N →
      ∀ z : Site, ∀ j₁ j₂ : ℕ,
        j₁ ∈ Finset.range (ms.sum + 1) → j₂ ∈ Finset.range (ms.sum + 1) →
        2 * (j₁ : ℤ) = (ms.sum : ℤ) + z 0 + z 1 →
        2 * (j₂ : ℤ) = (ms.sum : ℤ) + z 0 - z 1 →
        |(N / 4 : ℝ) * largeBlockGaussianListPairLaw
            (spatialLogCutoff N ^ 10) ms j₁ j₂ -
          heatKernel ((ms.sum : ℝ) / (2 * N))
            ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| < ε := by
  have hsampled := eventually_scaled_sampledGaussianBlockListPairProbability_error
    (by positivity : 0 < ε / 2)
  have hgaussian := eventually_fullGaussianBlockListPair_heat_error
    δ (ε / 2) hδ (by positivity : 0 < ε / 2)
  filter_upwards [hsampled, hgaussian] with N hsampledN hgaussianN
  intro ms hne hlen hpositive hall hsumLower hsumUpper z j₁ j₂ hj₁ hj₂ h₁ h₂
  have hsampledBound := hsampledN ms hlen hall hpositive (j₁ : ℤ) (j₂ : ℤ)
  have hgaussianBound := hgaussianN ms hne hlen hpositive hall
    hsumLower hsumUpper z (j₁ : ℤ) (j₂ : ℤ) h₁ h₂
  have hcoordinate (j : ℕ) (hj : j ∈ Finset.range (ms.sum + 1)) :
      largeBlockGaussianListLaw (spatialLogCutoff N ^ 10) ms j =
        sampledGaussianBlockListProbability ms (j : ℤ) := by
    exact largeBlockGaussianListLaw_eq_sampledGaussianBlockListProbability_of_all_ge
      (spatialLogCutoff N ^ 10) ms hall j
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hpairLaw : largeBlockGaussianListPairLaw
      (spatialLogCutoff N ^ 10) ms j₁ j₂ =
        sampledGaussianBlockListProbability ms (j₁ : ℤ) *
          sampledGaussianBlockListProbability ms (j₂ : ℤ) := by
    simp only [largeBlockGaussianListPairLaw]
    rw [hcoordinate j₁ hj₁, hcoordinate j₂ hj₂]
  let Q : ℝ := largeBlockGaussianListPairLaw (spatialLogCutoff N ^ 10) ms j₁ j₂
  let G : ℝ := fullGaussianBlockListProbability ms (j₁ : ℤ) *
    fullGaussianBlockListProbability ms (j₂ : ℤ)
  let H : ℝ := heatKernel ((ms.sum : ℝ) / (2 * N))
    ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)
  have hpairLaw' : Q =
      sampledGaussianBlockListProbability ms (j₁ : ℤ) *
        sampledGaussianBlockListProbability ms (j₂ : ℤ) := by
    simpa [Q] using hpairLaw
  have hscale (x y : ℝ) (hxy : (N : ℝ) * |x - y| < ε / 2) :
      |((N : ℝ) / 4) * x - ((N : ℝ) / 4) * y| < ε / 8 := by
    rw [show ((N : ℝ) / 4) * x - ((N : ℝ) / 4) * y =
      ((N : ℝ) / 4) * (x - y) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 4)]
    calc
      _ = ((N : ℝ) * |x - y|) / 4 := by ring
      _ < (ε / 2) / 4 := div_lt_div_of_pos_right hxy (by norm_num)
      _ = ε / 8 := by ring
  have hsampledBase := hsampledBound
  rw [← hpairLaw'] at hsampledBase
  have hsampledScaled : |((N : ℝ) / 4) * Q - ((N : ℝ) / 4) * G| < ε / 8 := by
    simpa [Q, G] using hscale _ _ hsampledBase
  have hfullScaled : |((N : ℝ) / 4) * G - H| < ε / 2 := by
    simpa [G, H, mul_assoc] using hgaussianBound
  have htriangle : |((N : ℝ) / 4) * Q - H| ≤
      |((N : ℝ) / 4) * Q - ((N : ℝ) / 4) * G| +
        |((N : ℝ) / 4) * G - H| := abs_sub_le _ _ _
  have hbound : |((N : ℝ) / 4) * Q - H| < ε := by
    calc
      _ ≤ _ := htriangle
      _ < ε / 8 + ε / 2 := add_lt_add hsampledScaled hfullScaled
      _ < ε := by linarith
  simpa [Q, H] using hbound

end Critical2DKPZ.SHF.Moments

end
