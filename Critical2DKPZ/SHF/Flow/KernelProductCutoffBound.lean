/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsCore
public import Critical2DKPZ.SHF.Tsai.Cutoff
import Mathlib.MeasureTheory.Integral.Prod

/-! # Deterministic endpoint-tail reduction for kernel-product cutoffs -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

noncomputable section

namespace Critical2DKPZ.SHF.Flow

/-- The tail set for the second coordinate of one polymer pair. -/
def kernelProductSecondTail (R : ℝ) : Set (Plane × Plane) :=
  {p | R < ‖p.2‖}





/-- With a Gaussian connector, the cutoff error splits into a tail of the first intermediate
endpoint and a Gaussian-small remainder. On the remainder, the first endpoint is within half
the cutoff radius while the second endpoint is beyond the radius. -/
theorem abs_kernelProductPairing_cutoff_error_le_leftTail_add_gaussian
    (μ ν : Measure (Plane × Plane)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Plane → Plane → ℝ) (hκm : Measurable (fun p : Plane × Plane => κ p.1 p.2))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hκ : ∀ x y, |κ x y| ≤ C * Real.exp (-c * ‖x - y‖ ^ 2))
    (Φ : C_c(Plane × Plane, ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hΦ : ∀ p, |Φ p| ≤ M) (R : ℝ) (hR : 0 ≤ R) :
    |kernelProductPairing μ κ ν Φ -
      ∫ q, Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν)| ≤
      M * C * (μ.real (kernelProductSecondTail (R / 2)) * ν.real Set.univ +
        Real.exp (-c * (R / 2) ^ 2) * μ.real Set.univ * ν.real Set.univ) := by
  let μν : Measure ((Plane × Plane) × (Plane × Plane)) := μ.prod ν
  let Iset : Set ((Plane × Plane) × (Plane × Plane)) :=
    kernelProductSecondTail (R / 2) ×ˢ (Set.univ : Set (Plane × Plane))
  let I : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    Set.indicator Iset (fun _ => 1)
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1
  let E : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    F q * (1 - ballCutoff R q.1.2 * ballCutoff R q.2.1)
  let H : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    M * C * (I q + Real.exp (-c * (R / 2) ^ 2))
  have htail : MeasurableSet (kernelProductSecondTail (R / 2)) := by
    change MeasurableSet {p : Plane × Plane | R / 2 < ‖p.2‖}
    exact (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).measurableSet
  have hIset : MeasurableSet Iset :=
    htail.prod (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Plane × Plane)))
  have hIm : Measurable I := by
    dsimp [I]
    exact measurable_const.indicator hIset
  have houter : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      (q.1.1, q.2.2)) := by fun_prop
  have hmiddle : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      (q.1.2, q.2.1)) := by fun_prop
  have hcut₁ : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ballCutoff R q.1.2) := (continuous_ballCutoff R).measurable.comp (by fun_prop)
  have hcut₂ : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ballCutoff R q.2.1) := (continuous_ballCutoff R).measurable.comp (by fun_prop)
  have hFm : Measurable F := by
    dsimp [F]
    exact (Φ.measurable.comp houter).mul (hκm.comp hmiddle)
  have hEm : Measurable E := by
    dsimp [E]
    exact hFm.mul (measurable_const.sub (hcut₁.mul hcut₂))
  have hIbound (q : (Plane × Plane) × (Plane × Plane)) : ‖I q‖ ≤ 1 := by
    dsimp [I]
    by_cases hq : q ∈ Iset <;> simp [Set.indicator, hq]
  have hEbound (q : (Plane × Plane) × (Plane × Plane)) :
      |E q| ≤ H q := by
    let w := q.1.2
    let y := q.2.1
    let a := ballCutoff R w
    let b := ballCutoff R y
    have ha := ballCutoff_mem_Icc R w
    have hb := ballCutoff_mem_Icc R y
    have hD0 : 0 ≤ 1 - a * b := by nlinarith [ha.1, ha.2, hb.1, hb.2]
    have hD1 : 1 - a * b ≤ 1 := by nlinarith [ha.1, hb.1]
    have hκcap : |κ w y| ≤ C := by
      calc
        |κ w y| ≤ C * Real.exp (-c * ‖w - y‖ ^ 2) := hκ w y
        _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.exp_le_one_iff.mpr
          nlinarith [sq_nonneg ‖w - y‖]
        _ = C := by ring
    have hFcap : |F q| ≤ M * C := by
      dsimp [F, w, y]
      rw [abs_mul]
      exact mul_le_mul (hΦ _) hκcap (abs_nonneg _) hM
    have hfactor : 0 ≤ M * C := mul_nonneg hM hC
    have hδ : 0 ≤ Real.exp (-c * (R / 2) ^ 2) := Real.exp_nonneg _
    have htarget_nonneg : 0 ≤ I q + Real.exp (-c * (R / 2) ^ 2) := by
      have hInn : 0 ≤ I q := by
        by_cases hq : q ∈ Iset <;> simp [I, hq]
      exact add_nonneg hInn hδ
    have hEeq : |E q| = |F q| * (1 - a * b) := by
      dsimp [E, a, b]
      rw [abs_mul, abs_of_nonneg hD0]
    rw [hEeq]
    by_cases hw : R / 2 < ‖w‖
    · have hIq : I q = 1 := by
        simp [I, Iset, w, kernelProductSecondTail, hw]
      dsimp [H]
      rw [hIq]
      calc
        |F q| * (1 - a * b) ≤ M * C * 1 := by
          nlinarith [hFcap, hD1, hD0]
        _ ≤ M * C * (1 + Real.exp (-c * (R / 2) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ) hfactor
    · have hw' : ‖w‖ ≤ R / 2 := le_of_not_gt hw
      have hwR : ‖w‖ ≤ R := by linarith
      have haone : a = 1 := by dsimp [a]; exact ballCutoff_eq_one_of_norm_le hwR
      have hIzero : I q = 0 := by
        simp [I, Iset, w, kernelProductSecondTail, hw]
      have hzero_or_y : b = 1 ∨ R < ‖y‖ := by
        by_cases hbeq : b = 1
        · exact Or.inl hbeq
        · right
          by_contra hnot
          have hyR : ‖y‖ ≤ R := le_of_not_gt hnot
          have hbone : b = 1 := by dsimp [b]; exact ballCutoff_eq_one_of_norm_le hyR
          exact hbeq hbone
      dsimp [H]
      rw [hIzero, haone]
      rcases hzero_or_y with hbone | hyR
      · rw [hbone]
        simpa only [one_mul, sub_self, zero_add, mul_zero] using
          mul_nonneg (mul_nonneg hM hC) (Real.exp_nonneg (-c * (R / 2) ^ 2))
      · have htriangle : ‖y‖ ≤ ‖w - y‖ + ‖w‖ := by
          have := norm_le_norm_sub_add y w
          simpa only [norm_sub_rev] using this
        have hdist : R / 2 ≤ ‖w - y‖ := by linarith
        have hdistSq : (R / 2) ^ 2 ≤ ‖w - y‖ ^ 2 := by
          nlinarith [sq_nonneg (‖w - y‖ - R / 2), hR]
        have hexp : Real.exp (-c * ‖w - y‖ ^ 2) ≤
            Real.exp (-c * (R / 2) ^ 2) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hdistSq (by linarith : -c ≤ 0)
        have hκtail : |κ w y| ≤ C * Real.exp (-c * (R / 2) ^ 2) :=
          (hκ w y).trans (mul_le_mul_of_nonneg_left hexp hC)
        have hFtail : |F q| ≤ M * C * Real.exp (-c * (R / 2) ^ 2) := by
          dsimp [F, w, y]
          rw [abs_mul]
          calc
            |Φ (q.1.1, q.2.2)| * |κ w y| ≤ M * (C * Real.exp (-c * (R / 2) ^ 2)) :=
              mul_le_mul (hΦ _) hκtail (abs_nonneg _) hM
            _ = M * C * Real.exp (-c * (R / 2) ^ 2) := by ring
        have hDnonneg : 0 ≤ 1 - b := by nlinarith [hb.1, hb.2]
        have hDle : 1 - b ≤ 1 := by nlinarith [hb.1]
        have hEtail : |F q| * (1 - b) ≤ M * C * Real.exp (-c * (R / 2) ^ 2) := by
          calc
            |F q| * (1 - b) ≤ |F q| * 1 :=
              mul_le_mul_of_nonneg_left hDle (abs_nonneg _)
            _ = |F q| := by ring
            _ ≤ M * C * Real.exp (-c * (R / 2) ^ 2) := hFtail
        simpa only [one_mul, zero_add] using hEtail
  have hIint : Integrable I μν :=
    Integrable.of_bound hIm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hIbound)
  have hδint : Integrable (fun _ : (Plane × Plane) × (Plane × Plane) =>
      Real.exp (-c * (R / 2) ^ 2)) μν := integrable_const _
  have hHint : Integrable H μν := by
    dsimp [H]
    exact (hIint.add hδint).const_mul (M * C)
  have hEint : Integrable E μν := by
    apply hHint.mono' hEm.aestronglyMeasurable
    filter_upwards [] with q
    rw [Real.norm_eq_abs]
    exact hEbound q
  have hF : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1) := by
    simpa only [F] using hFm
  have hG : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 * ballCutoff R q.1.2 * ballCutoff R q.2.1) := by
    exact ((hF.mul hcut₁).mul hcut₂)
  have hFbound (q : (Plane × Plane) × (Plane × Plane)) :
      ‖Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1‖ ≤ M * C := by
    rw [Real.norm_eq_abs, abs_mul]
    have hκcap : |κ q.1.2 q.2.1| ≤ C := by
      calc
        |κ q.1.2 q.2.1| ≤ C * Real.exp (-c * ‖q.1.2 - q.2.1‖ ^ 2) := hκ _ _
        _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.exp_le_one_iff.mpr
          nlinarith [sq_nonneg ‖q.1.2 - q.2.1‖]
        _ = C := by ring
    exact mul_le_mul (hΦ _) hκcap (abs_nonneg _) hM
  have hGbound (q : (Plane × Plane) × (Plane × Plane)) :
      ‖Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 * ballCutoff R q.1.2 * ballCutoff R q.2.1‖ ≤ M * C := by
    have hc₁ := ballCutoff_mem_Icc R q.1.2
    have hc₂ := ballCutoff_mem_Icc R q.2.1
    have hcut₁abs : |ballCutoff R q.1.2| ≤ 1 := by
      rw [abs_of_nonneg hc₁.1]
      exact hc₁.2
    have hcut₂abs : |ballCutoff R q.2.1| ≤ 1 := by
      rw [abs_of_nonneg hc₂.1]
      exact hc₂.2
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      |Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1| *
          |ballCutoff R q.1.2| * |ballCutoff R q.2.1| ≤
        |Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1| * 1 *
          |ballCutoff R q.2.1| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcut₁abs (abs_nonneg _))
              (abs_nonneg _)
      _ ≤ |Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1| * 1 * 1 :=
        mul_le_mul_of_nonneg_left hcut₂abs
          (mul_nonneg (abs_nonneg _) (by norm_num))
      _ = |Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1| := by ring
      _ ≤ M * C := by
        simpa only [Real.norm_eq_abs] using hFbound q
  have hFint : Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1) μν :=
    Integrable.of_bound hF.aestronglyMeasurable (M * C) (Filter.Eventually.of_forall hFbound)
  have hGint : Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 * ballCutoff R q.1.2 * ballCutoff R q.2.1) μν :=
    Integrable.of_bound hG.aestronglyMeasurable (M * C) (Filter.Eventually.of_forall hGbound)
  have hEeq : (fun q => E q) = fun q =>
      Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 -
        (Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 *
          ballCutoff R q.1.2 * ballCutoff R q.2.1) := by
    funext q
    dsimp [E, F]
    ring
  have hdiff : kernelProductPairing μ κ ν Φ -
      ∫ q, Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 * ballCutoff R q.1.2 *
        ballCutoff R q.2.1 ∂μν = ∫ q, E q ∂μν := by
    rw [kernelProductPairing, ← integral_sub hFint hGint, hEeq]
  have hrealI : ∫ q, I q ∂μν =
      μ.real (kernelProductSecondTail (R / 2)) * ν.real Set.univ := by
    have hmeasure : μν.real Iset =
        μ.real (kernelProductSecondTail (R / 2)) * ν.real Set.univ := by
      simp [μν, Iset]
    calc
      _ = μν.real Iset := by
        dsimp [I]
        simpa [Measure.real] using (integral_indicator_const (1 : ℝ) hIset)
      _ = _ := hmeasure
  have huniv : μν.real Set.univ = μ.real Set.univ * ν.real Set.univ := by
    simpa only [μν, Set.univ_prod_univ] using
      (measureReal_prod_prod (μ := μ) (ν := ν) Set.univ Set.univ)
  have hHintegral : ∫ q, H q ∂μν =
      M * C * (μ.real (kernelProductSecondTail (R / 2)) * ν.real Set.univ +
        Real.exp (-c * (R / 2) ^ 2) * μ.real Set.univ * ν.real Set.univ) := by
    dsimp [H]
    rw [integral_const_mul, integral_add hIint hδint, hrealI, integral_const, huniv]
    ring
  have hboundIntegral : ∫ q, E q ∂μν ≤ ∫ q, H q ∂μν := by
    apply integral_mono hEint hHint
    intro q
    exact (le_abs_self (E q)).trans (hEbound q)
  have habs : |∫ q, E q ∂μν| ≤ ∫ q, H q ∂μν := by
    calc
      |∫ q, E q ∂μν| ≤ ∫ q, |E q| ∂μν := abs_integral_le_integral_abs
      _ ≤ ∫ q, H q ∂μν := by
        apply integral_mono
        · exact hEint.abs
        · exact hHint
        · intro q
          exact hEbound q
  calc
    |kernelProductPairing μ κ ν Φ -
        ∫ q, Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 * ballCutoff R q.1.2 *
          ballCutoff R q.2.1 ∂μν| = |∫ q, E q ∂μν| := by rw [hdiff]
    _ ≤ ∫ q, H q ∂μν := habs
    _ = _ := hHintegral

end Critical2DKPZ.SHF.Flow

end
