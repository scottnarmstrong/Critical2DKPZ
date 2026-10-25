/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-! # Moment estimates for bounded independent arrays

The third moment is bounded by the row bound times the second moment. Independent
centred sums have second moment equal to the sum of their second moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A real random variable bounded a.e. has every finite moment. -/
theorem memLp_of_ae_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hm : AEMeasurable X P)
    (B : ℝ) (hb : ∀ᵐ ω ∂P, |X ω| ≤ B) (p : ℝ≥0∞) : MemLp X p P := by
  exact MemLp.of_bound hm.aestronglyMeasurable B (by simpa only [Real.norm_eq_abs] using hb)

/-- The absolute third moment of a bounded variable is bounded by its second moment. -/
theorem integral_abs_cube_le_bound_mul_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hm : AEMeasurable X P) (B : ℝ) (hb : ∀ᵐ ω ∂P, |X ω| ≤ B) :
    Integrable (fun ω => |X ω| ^ 3) P ∧ Integrable (fun ω => X ω ^ 2) P ∧
      (∫ ω, |X ω| ^ 3 ∂P) ≤ B * ∫ ω, X ω ^ 2 ∂P := by
  have h3 := memLp_of_ae_abs_le P hm B hb 3
  have h2 := memLp_of_ae_abs_le P hm B hb 2
  have h3i : Integrable (fun ω => |X ω| ^ 3) P := by
    simpa only [Real.norm_eq_abs] using h3.integrable_norm_pow'
  have h2i : Integrable (fun ω => X ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp h2
  refine ⟨h3i, h2i, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae h3i (h2i.const_mul B)
  filter_upwards [hb] with ω hω
  calc
    |X ω| ^ 3 = |X ω| * (X ω) ^ 2 := by rw [← sq_abs]; ring
    _ ≤ B * (X ω) ^ 2 := mul_le_mul_of_nonneg_right hω (sq_nonneg _)

/-- The second moment of a finite independent centred sum is the sum of second moments. -/
theorem integral_sq_sum_indep_centered {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (I : Finset ι) (X : ι → Ω → ℝ)
    (hind : iIndepFun X P) (hmem : ∀ i ∈ I, MemLp (X i) 2 P)
    (hmean : ∀ i ∈ I, (∫ ω, X i ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ I, X i ω) ^ 2 ∂P) = ∑ i ∈ I, ∫ ω, X i ω ^ 2 ∂P := by
  classical
  have hsum : MemLp (fun ω => ∑ i ∈ I, X i ω) 2 P := memLp_finsetSum I hmem
  have hsummean : (∫ ω, (∑ i ∈ I, X i ω) ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i hi => (hmem i hi).integrable (by norm_num))]
    exact Finset.sum_eq_zero hmean
  have hvar := IndepFun.variance_sum hmem (fun i hi j hj hij => hind.indepFun hij)
  have hsumfun : (∑ i ∈ I, X i) = (fun ω => ∑ i ∈ I, X i ω) := by
    funext ω
    exact Finset.sum_apply ω I X
  have hvarsum : variance (fun ω => ∑ i ∈ I, X i ω) P =
      ∑ i ∈ I, variance (X i) P := by
    rw [hsumfun] at hvar
    exact hvar
  rw [variance_eq_integral hsum.aemeasurable] at hvarsum
  simp only [hsummean, sub_zero] at hvarsum
  rw [hvarsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [variance_eq_integral (hmem i hi).aemeasurable, hmean i hi]
  simp only [sub_zero]

/-- Vanishing integrable second moments imply convergence to zero in probability. -/
theorem tendstoInMeasure_zero_of_integral_sq {κ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter κ) (X : κ → Ω → ℝ)
    (hm : ∀ L, MemLp (X L) 2 P)
    (hlim : Tendsto (fun L => ∫ ω, X L ω ^ 2 ∂P) l (𝓝 0)) :
    TendstoInMeasure P X l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim' : Tendsto (fun L => (∫ ω, X L ω ^ 2 ∂P) / ε ^ 2) l (𝓝 0) := by
    simpa only [zero_div] using hlim.div_const (ε ^ 2)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim'
  intro L
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => sq_nonneg (X L ω)))
    ((memLp_two_iff_integrable_sq (hm L).aestronglyMeasurable).mp (hm L)) (ε ^ 2)
  have hsub : {ω | ε ≤ ‖X L ω - 0‖} ⊆ {ω | ε ^ 2 ≤ X L ω ^ 2} := by
    intro ω hω
    change ε ≤ ‖X L ω - 0‖ at hω
    change ε ^ 2 ≤ X L ω ^ 2
    have hh : ε ≤ |X L ω| := by simpa only [sub_zero, Real.norm_eq_abs] using hω
    have := pow_le_pow_left₀ hε.le hh 2
    simpa only [sq_abs] using this
  exact (measureReal_mono hsub).trans ((le_div_iff₀ (sq_pos_of_pos hε)).mpr
    (by simpa only [mul_comm] using hmarkov))

end Critical2DKPZ.Extensions.ScaleLimit
