/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.NormalizedArrayCLT
public import Critical2DKPZ.Extensions.ScaleLimit.ArrayMoments
import Mathlib.Tactic

/-! # Central limit theorem for bounded independent triangular arrays

The row bounds tend to zero and the sums of the second moments converge. The
limit may have variance zero. The proof works along every countably generated
filter, including the positive real parameter tending to infinity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Bounded independent centred rows with vanishing row bounds satisfy the scalar
central limit theorem, including the degenerate Gaussian limit. -/
theorem tendstoInDistribution_sum_bounded_indep {κ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter κ) [l.IsCountablyGenerated]
    (n : κ → ℕ) (Y : κ → ℕ → Ω → ℝ) (B : κ → ℝ)
    (hind : ∀ L, iIndepFun (Y L) P) (hm : ∀ L i, AEMeasurable (Y L i) P)
    (hmean : ∀ L i, (∫ ω, Y L i ω ∂P) = 0)
    (hbound : ∀ L i, ∀ᵐ ω ∂P, |Y L i ω| ≤ B L)
    (hB : Tendsto B l (𝓝 0)) (v : ℝ≥0)
    (hvar : Tendsto (fun L => ∑ i ∈ Finset.range (n L), ∫ ω, Y L i ω ^ 2 ∂P)
      l (𝓝 (v : ℝ))) :
    TendstoInDistribution (fun L ω => ∑ i ∈ Finset.range (n L), Y L i ω)
      l id (fun _ => P) (gaussianReal 0 v) := by
  have hmem (L : κ) (i : ℕ) (p : ℝ≥0∞) : MemLp (Y L i) p P :=
    memLp_of_ae_abs_le P (hm L i) (B L) (hbound L i) p
  have hsum (L : κ) : MemLp (fun ω => ∑ i ∈ Finset.range (n L), Y L i ω) 2 P :=
    memLp_finsetSum _ (fun i _ => hmem L i 2)
  by_cases hv : v = 0
  · subst v
    have hzero := tendstoInMeasure_zero_of_integral_sq P l
      (fun L ω => ∑ i ∈ Finset.range (n L), Y L i ω) hsum
      (by
        simpa only [integral_sq_sum_indep_centered P _ _ (hind _) (fun i _ => hmem _ i 2)
          (fun i _ => hmean _ i), NNReal.coe_zero] using hvar)
    have hzlaw := hzero.tendstoInDistribution_of_aemeasurable
      (fun L => (hsum L).aemeasurable) measurable_const.aemeasurable
    have hmap : P.map (fun _ : Ω => (0 : ℝ)) = (gaussianReal 0 0).map id := by
      simp only [gaussianReal_zero_var, Measure.map_id, Measure.map_const, measure_univ, one_smul]
    refine ⟨fun L => (hsum L).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [hmap] using hzlaw.tendsto
  · let s : ℝ := Real.sqrt v
    have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
    have hs : 0 < s := Real.sqrt_pos.mpr hvpos
    have hs2 : s ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
    let X : κ → ℕ → Ω → ℝ := fun L i ω => Y L i ω / s
    have hXm (L : κ) (i : ℕ) : AEMeasurable (X L i) P := (hm L i).div_const s
    have hXind (L : κ) : iIndepFun (X L) P :=
      (hind L).comp (fun _ (y : ℝ) => y / s) (fun _ => by fun_prop)
    have hXmem (L : κ) (i : ℕ) : MemLp (X L i) 3 P := by
      simpa only [X, div_eq_mul_inv, mul_comm] using (hmem L i 3).const_mul s⁻¹
    have hXmean (L : κ) (i : ℕ) : (∫ ω, X L i ω ∂P) = 0 := by
      change (∫ ω, Y L i ω / s ∂P) = 0
      rw [integral_div, hmean, zero_div]
    have hXvar : Tendsto (fun L => ∑ i ∈ Finset.range (n L), ∫ ω, X L i ω ^ 2 ∂P)
        l (𝓝 1) := by
      have heq (L : κ) : (∑ i ∈ Finset.range (n L), ∫ ω, X L i ω ^ 2 ∂P) =
          (∑ i ∈ Finset.range (n L), ∫ ω, Y L i ω ^ 2 ∂P) / s ^ 2 := by
        simp only [X, div_pow, integral_div, Finset.sum_div]
      simp_rw [heq]
      rw [hs2]
      have hh := hvar.div_const (v : ℝ)
      rw [div_self hvpos.ne'] at hh
      exact hh
    have hXbound (L : κ) (i : ℕ) : ∀ᵐ ω ∂P, |X L i ω| ≤ B L / s := by
      filter_upwards [hbound L i] with ω hω
      dsimp [X]
      rw [abs_div, abs_of_pos hs]
      exact div_le_div_of_nonneg_right hω hs.le
    have hthirdbound (L : κ) :
        (∑ i ∈ Finset.range (n L), ∫ ω, |X L i ω| ^ 3 ∂P) ≤
          (B L / s) * (∑ i ∈ Finset.range (n L), ∫ ω, X L i ω ^ 2 ∂P) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact (integral_abs_cube_le_bound_mul_sq P (hXm L i) (B L / s) (hXbound L i)).2.2
    have hthird : Tendsto (fun L => ∑ i ∈ Finset.range (n L), ∫ ω, |X L i ω| ^ 3 ∂P)
        l (𝓝 0) := by
      apply squeeze_zero (fun L => Finset.sum_nonneg (fun i _ =>
        integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3))) hthirdbound
      simpa only [zero_div, zero_mul] using (hB.div_const s).mul hXvar
    have hclt := tendstoInDistribution_sum_of_lyapunov P l n X hXind hXm hXmem hXmean
      hXvar hthird
    have hscaled := hclt.continuous_comp (g := fun y : ℝ => s * y) (by fun_prop)
    have hsumcancel (L : κ) : (fun ω => s * (∑ i ∈ Finset.range (n L), X L i ω)) =
        (fun ω => ∑ i ∈ Finset.range (n L), Y L i ω) := by
      funext ω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [X]
      field_simp [hs.ne']
    have hmap : (gaussianReal 0 1).map (fun y : ℝ => s * y) = gaussianReal 0 v := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · ring
      · apply NNReal.coe_injective
        simpa only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one] using hs2
    refine ⟨fun L => (hsum L).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Function.comp_def, id_eq, hsumcancel, hmap, Measure.map_id] using hscaled.tendsto

end Critical2DKPZ.Extensions.ScaleLimit
