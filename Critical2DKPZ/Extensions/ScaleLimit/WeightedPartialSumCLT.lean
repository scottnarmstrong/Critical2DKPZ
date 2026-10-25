/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CenteredArrayCLT
public import Critical2DKPZ.Extensions.ScaleLimit.WeightedCutoffs
import Mathlib.Tactic

/-! # Bounded-array CLT for finite projections of independent partial sums -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Finite projections of nested bounded independent partial sums satisfy the
scalar Gaussian CLT whenever their normalized variances converge. -/
theorem tendstoInDistribution_weighted_partialSums
    {κ Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter κ) [l.IsCountablyGenerated]
    (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y P) (hm : ∀ j, AEMeasurable (Y j) P)
    (hmean : ∀ j, (∫ ω, Y j ω ∂P) = 0) (K : ℝ)
    (hb : ∀ j, ∀ᵐ ω ∂P, |Y j ω| ≤ K)
    (n : κ → I → ℕ) (a : κ → ℝ) (ha : Tendsto a l atTop) (v : I → ℝ) (σ : ℝ≥0)
    (hv : Tendsto (fun i => variance
      (fun ω => (∑ s, partialSumRange Y (n i s) ω * v s) / a i) P) l (𝓝 (σ : ℝ))) :
    TendstoInDistribution (fun i ω => (∑ s, partialSumRange Y (n i s) ω * v s) / a i)
      l id (fun _ => P) (gaussianReal 0 σ) := by
  classical
  let W : κ → ℕ → ℝ := fun i j => cutoffWeight (n i) v j
  let N : κ → ℕ := fun i => Finset.univ.sup (n i)
  let R : κ → ℕ → Ω → ℝ := fun i j ω => W i j * Y j ω / a i
  let B : κ → ℝ := fun i => ((∑ s, |v s|) * K) * |(a i)⁻¹|
  have hRi (i : κ) : iIndepFun (R i) P :=
    (hind.comp (fun j z => W i j * z / a i) (fun _ => by fun_prop))
  have hRm (i : κ) (j : ℕ) : AEMeasurable (R i j) P :=
    ((hm j).const_mul _).div_const _
  have hRmean (i : κ) (j : ℕ) : (∫ ω, R i j ω ∂P) = 0 := by
    simp only [R, integral_div, integral_const_mul, hmean, mul_zero, zero_div]
  have hRb (i : κ) (j : ℕ) : ∀ᵐ ω ∂P, |R i j ω| ≤ B i := by
    filter_upwards [hb j] with ω hω
    have hW := abs_cutoffWeight_le (n i) v j
    calc
      |R i j ω| = |W i j| * |Y j ω| * |(a i)⁻¹| := by
        simp only [R, div_eq_mul_inv, abs_mul]
      _ ≤ ((∑ s, |v s|) * K) * |(a i)⁻¹| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul hW hω (abs_nonneg _) (Finset.sum_nonneg fun s _ => abs_nonneg _)
      _ = B i := rfl
  have hB : Tendsto B l (𝓝 0) := by
    have hinv : Tendsto (fun i => (a i)⁻¹) l (𝓝 0) := by
      convert! tendsto_inv_atTop_zero.comp ha using 1
    simpa only [B, abs_zero, mul_zero] using tendsto_const_nhds.mul hinv.abs
  have hsum (i : κ) : (fun ω => ∑ j ∈ Finset.range (N i), R i j ω) =
      fun ω => (∑ s, partialSumRange Y (n i s) ω * v s) / a i := by
    funext ω
    change (∑ j ∈ Finset.range (N i), W i j * Y j ω / a i) = _
    rw [← Finset.sum_div]
    congr 1
    exact sum_cutoffWeight_eq (n i) v (fun j => Y j ω)
  have hRmem (i : κ) (j : ℕ) : MemLp (R i j) 2 P :=
    memLp_of_ae_abs_le P (hRm i j) (B i) (hRb i j) 2
  have hvar (i : κ) : variance (fun ω => ∑ j ∈ Finset.range (N i), R i j ω) P =
      ∑ j ∈ Finset.range (N i), ∫ ω, R i j ω ^ 2 ∂P := by
    have hvsum := IndepFun.variance_sum (s := Finset.range (N i)) (X := R i)
      (fun j _ => hRmem i j) (fun j hj k hk hjk => (hRi i).indepFun hjk)
    have heq : (∑ j ∈ Finset.range (N i), R i j) =
        fun ω => ∑ j ∈ Finset.range (N i), R i j ω := by
      funext ω
      exact Finset.sum_apply ω _ _
    rw [heq] at hvsum
    rw [hvsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [variance_eq_integral (hRm i j), hRmean]
    simp only [sub_zero]
  have hmoment : Tendsto (fun i => ∑ j ∈ Finset.range (N i), ∫ ω, R i j ω ^ 2 ∂P)
      l (𝓝 (σ : ℝ)) := by
    simpa only [← hvar, hsum] using hv
  have hclt := tendstoInDistribution_sum_bounded_indep P l N R B hRi hRm hRmean hRb hB σ hmoment
  have hfamily : (fun i ω => ∑ j ∈ Finset.range (N i), R i j ω) =
      (fun i ω => (∑ s, partialSumRange Y (n i s) ω * v s) / a i) := by
    funext i
    exact hsum i
  rw [hfamily] at hclt
  exact hclt

end Critical2DKPZ.Extensions.ScaleLimit
