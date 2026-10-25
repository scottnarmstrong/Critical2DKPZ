/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BoundedArrayCLT
import Mathlib.Tactic

/-! # Gaussian limits of centered bounded partial sums

The limiting variance may be zero. This form permits a subsequence of partial
sum indices and a normalization tending to infinity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The sum of the first `n` variables of a real sequence, indexed from zero. -/
def partialSumRange {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, Y i ω

/-- A bounded independent sequence has a Gaussian subsequential partial-sum limit
whenever its normalized variances converge. -/
theorem tendstoInDistribution_centered_bounded_sums {κ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter κ) [l.IsCountablyGenerated]
    (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y P) (hm : ∀ i, AEMeasurable (Y i) P)
    (K : ℝ) (hK : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ K)
    (n : κ → ℕ) (a : κ → ℝ) (ha : Tendsto a l atTop) (v : ℝ≥0)
    (hv : Tendsto (fun L => variance (fun ω => ∑ i ∈ Finset.range (n L), Y i ω) P /
      a L ^ 2) l (𝓝 (v : ℝ))) :
    TendstoInDistribution (fun L ω => ((∑ i ∈ Finset.range (n L), Y i ω) -
      ∫ ω', (∑ i ∈ Finset.range (n L), Y i ω') ∂P) / a L)
      l id (fun _ => P) (gaussianReal 0 v) := by
  have hmem (i : ℕ) (p : ℝ≥0∞) : MemLp (Y i) p P := memLp_of_ae_abs_le P (hm i) K (hK i) p
  have hint (i : ℕ) : Integrable (Y i) P := (hmem i 1).integrable le_rfl
  have hmeanbound (i : ℕ) : |∫ ω, Y i ω ∂P| ≤ |K| := by
    have hh := norm_integral_le_of_norm_le_const (μ := P) (f := Y i) (C := K)
      (by simpa only [Real.norm_eq_abs] using hK i)
    have hh' : |∫ ω, Y i ω ∂P| ≤ K := by simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh
    exact hh'.trans (le_abs_self K)
  let X : κ → ℕ → Ω → ℝ := fun L i ω => (Y i ω - ∫ ω', Y i ω' ∂P) / a L
  have hXm (L : κ) (i : ℕ) : AEMeasurable (X L i) P := ((hm i).sub_const _).div_const _
  have hXind (L : κ) : iIndepFun (X L) P :=
    hind.comp (fun i (y : ℝ) => (y - ∫ ω, Y i ω ∂P) / a L) (fun _ => by fun_prop)
  have hXmean (L : κ) (i : ℕ) : (∫ ω, X L i ω ∂P) = 0 := by
    dsimp [X]
    rw [integral_div, integral_sub (hint i) (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul, sub_self, zero_div]
  let B : κ → ℝ := fun L => (2 * |K|) * |(a L)⁻¹|
  have hXbound (L : κ) (i : ℕ) : ∀ᵐ ω ∂P, |X L i ω| ≤ B L := by
    filter_upwards [hK i] with ω hω
    have hc : |Y i ω - ∫ ω', Y i ω' ∂P| ≤ 2 * |K| :=
      (abs_sub _ _).trans (by linarith [hmeanbound i, le_abs_self K])
    dsimp [X, B]
    rw [div_eq_mul_inv, abs_mul]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hB : Tendsto B l (𝓝 0) := by
    simpa only [B, Function.comp_def, abs_zero, mul_zero] using
      ((tendsto_inv_atTop_zero.comp ha).abs.const_mul (2 * |K|))
  have hXmem (L : κ) (i : ℕ) (p : ℝ≥0∞) : MemLp (X L i) p P :=
    memLp_of_ae_abs_le P (hXm L i) (B L) (hXbound L i) p
  have hSmean (L : κ) : (∫ ω, (∑ i ∈ Finset.range (n L), Y i ω) ∂P) =
      ∑ i ∈ Finset.range (n L), ∫ ω, Y i ω ∂P :=
    integral_finsetSum _ (fun i _ => hint i)
  have hsum (L : κ) (ω : Ω) : (∑ i ∈ Finset.range (n L), X L i ω) =
      ((∑ i ∈ Finset.range (n L), Y i ω) -
        ∫ ω', (∑ i ∈ Finset.range (n L), Y i ω') ∂P) / a L := by
    simp only [X, ← Finset.sum_div, Finset.sum_sub_distrib, hSmean]
  have hsummean (L : κ) : (∫ ω, (∑ i ∈ Finset.range (n L), X L i ω) ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hXmem L i 1).integrable le_rfl)]
    exact Finset.sum_eq_zero (fun i _ => hXmean L i)
  have hsecond (L : κ) : (∑ i ∈ Finset.range (n L), ∫ ω, X L i ω ^ 2 ∂P) =
      variance (fun ω => ∑ i ∈ Finset.range (n L), Y i ω) P / a L ^ 2 := by
    rw [← integral_sq_sum_indep_centered P _ _ (hXind L)
      (fun i _ => hXmem L i 2) (fun i _ => hXmean L i)]
    have hsumM : MemLp (fun ω => ∑ i ∈ Finset.range (n L), X L i ω) 2 P :=
      memLp_finsetSum _ (fun i _ => hXmem L i 2)
    have hvsum := variance_eq_integral hsumM.aemeasurable
    rw [hsummean] at hvsum
    simp only [sub_zero] at hvsum
    rw [← hvsum]
    simp_rw [hsum, div_eq_mul_inv]
    rw [variance_mul_const,
      variance_sub_const (memLp_finsetSum _ (fun i _ => hmem i 2)).aestronglyMeasurable]
    simp only [inv_pow]
  have hvX : Tendsto (fun L => ∑ i ∈ Finset.range (n L), ∫ ω, X L i ω ^ 2 ∂P)
      l (𝓝 (v : ℝ)) := by simpa only [hsecond] using hv
  have hclt := tendstoInDistribution_sum_bounded_indep P l n X B hXind hXm hXmean hXbound hB v hvX
  exact hclt.congr (fun L => Eventually.of_forall (hsum L)) EventuallyEq.rfl

end Critical2DKPZ.Extensions.ScaleLimit
