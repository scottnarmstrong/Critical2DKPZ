/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.L2ProductHelpers
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Lifting scalar `L²` approximation through product fibers

Uniformly bounded approximation on each fiber lifts to product-space
approximation by dominated convergence of the squared fiber errors. The
operators here act on actual scalar functions; the joint measurability
hypothesis records the property supplied by their integral kernels.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- A uniform fiber bound gives the same bound on the product. -/
theorem eLpNorm_fiberAction_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) [SigmaFinite ν] [SigmaFinite μ]
    (T : (X → ℝ) → X → ℝ) {M : ℝ≥0∞}
    (hT : ∀ φ, MemLp φ 2 ν → eLpNorm (T φ) 2 ν ≤ M * eLpNorm φ 2 ν)
    {F : X × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (ν.prod μ))
    (hTFm : Measurable (fun q : X × Y => T (fun x => F (x, q.2)) q.1)) :
    eLpNorm (fun q : X × Y => T (fun x => F (x, q.2)) q.1) 2 (ν.prod μ) ≤
      M * eLpNorm F 2 (ν.prod μ) := by
  have hm : Measurable (fun y => (eLpNorm (fun x => F (x, y)) 2 ν) ^ (2 : ℕ)) := by
    have heq : (fun y => (eLpNorm (fun x => F (x, y)) 2 ν) ^ (2 : ℕ)) =
        fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ (2 : ℕ) ∂ν := by
      funext y
      have hs : Measurable (fun x => F (x, y)) := hFm.comp (measurable_id.prodMk measurable_const)
      exact sq_eLpNorm_two_eq_lintegral_enorm hs.aestronglyMeasurable
    rw [heq]
    exact ((hFm.enorm.pow_const (2 : ℕ)).comp measurable_swap).lintegral_prod_right'
  have hsq : (eLpNorm (fun q : X × Y => T (fun x => F (x, q.2)) q.1) 2 (ν.prod μ)) ^ (2 : ℕ) ≤
      M ^ 2 * (eLpNorm F 2 (ν.prod μ)) ^ (2 : ℕ) := by
    rw [← lintegral_fiber_eLpNorm_sq_eq ν μ hTFm, ← lintegral_fiber_eLpNorm_sq_eq ν μ hFm,
      ← lintegral_const_mul _ hm]
    apply lintegral_mono_ae
    filter_upwards [ae_memLp_prod_left ν μ hFm hF] with y hy
    simpa only [mul_pow] using pow_le_pow_left₀
      (bot_le : (0 : ℝ≥0∞) ≤ eLpNorm (T (fun x => F (x, y))) 2 ν) (hT _ hy) 2
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).1
  simpa only [mul_pow] using hsq

/-- Strong approximation and a common finite bound lift through measurable product fibers. -/
theorem fiberAction_memLp_and_tendsto {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) [SigmaFinite ν] [SigmaFinite μ]
    (T : ℕ → (X → ℝ) → X → ℝ) {M : ℝ≥0∞} (hMfin : M ≠ ⊤)
    (hTbound : ∀ j φ, MemLp φ 2 ν → eLpNorm (T j φ) 2 ν ≤ M * eLpNorm φ 2 ν)
    (hTlim : ∀ φ, Measurable φ → MemLp φ 2 ν →
      Tendsto (fun j => eLpNorm (T j φ - φ) 2 ν) atTop (𝓝 0))
    {F : X × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (ν.prod μ))
    (hTFm : ∀ j, Measurable (fun q : X × Y => T j (fun x => F (x, q.2)) q.1)) :
    (∀ j, MemLp (fun q : X × Y => T j (fun x => F (x, q.2)) q.1) 2 (ν.prod μ)) ∧
    Tendsto (fun j => eLpNorm (fun q : X × Y => T j (fun x => F (x, q.2)) q.1 - F q)
      2 (ν.prod μ)) atTop (𝓝 0) := by
  let δ (j : ℕ) (q : X × Y) := T j (fun x => F (x, q.2)) q.1 - F q
  have hδ (j) : Measurable (δ j) := (hTFm j).sub hFm
  let R (j : ℕ) (y : Y) := ∫⁻ x, ‖δ j (x, y)‖ₑ ^ (2 : ℕ) ∂ν
  have hRm (j) : Measurable (R j) :=
    (((hδ j).enorm.pow_const (2 : ℕ)).comp measurable_swap).lintegral_prod_right'
  let B (y : Y) := (M + 1) ^ 2 * ∫⁻ x, ‖F (x, y)‖ₑ ^ (2 : ℕ) ∂ν
  have hFM : Measurable (fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ (2 : ℕ) ∂ν) :=
    ((hFm.enorm.pow_const (2 : ℕ)).comp measurable_swap).lintegral_prod_right'
  have hBfin : (∫⁻ y, B y ∂μ) ≠ ⊤ := by
    rw [show (∫⁻ y, B y ∂μ) = (M + 1) ^ 2 * ∫⁻ y,
      (∫⁻ x, ‖F (x, y)‖ₑ ^ (2 : ℕ) ∂ν) ∂μ from lintegral_const_mul _ hFM,
      ← lintegral_prod_symm _ (hFm.enorm.pow_const (2 : ℕ)).aemeasurable,
      ← sq_eLpNorm_two_eq_lintegral_enorm hFm.aestronglyMeasurable]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simpa using hMfin))
      (ENNReal.pow_ne_top hF.eLpNorm_ne_top)
  have hfiber := ae_memLp_prod_left ν μ hFm hF
  have hbound (j : ℕ) : R j ≤ᵐ[μ] B := by
    filter_upwards [hfiber] with y hy
    have hslice : Measurable (fun x => F (x, y)) := hFm.comp (measurable_id.prodMk measurable_const)
    have hTslice : Measurable (T j (fun x => F (x, y))) :=
      (hTFm j).comp (measurable_id.prodMk measurable_const)
    have hbase := eLpNorm_sub_le (f := T j (fun x => F (x, y))) (g := fun x => F (x, y))
      (μ := ν) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hmid := add_le_add (hTbound j _ hy) (le_refl (eLpNorm (fun x => F (x, y)) 2 ν))
    have hnorm : eLpNorm (T j (fun x => F (x, y)) - fun x => F (x, y)) 2 ν ≤
        (M + 1) * eLpNorm (fun x => F (x, y)) 2 ν := by
      rw [add_mul, one_mul]
      exact hbase.trans hmid
    have hsq := pow_le_pow_left₀ (bot_le : (0 : ℝ≥0∞) ≤ eLpNorm
      (T j (fun x => F (x, y)) - fun x => F (x, y)) 2 ν) hnorm 2
    rw [mul_pow, sq_eLpNorm_two_eq_lintegral_enorm
      (hTslice.aestronglyMeasurable.sub hslice.aestronglyMeasurable),
      sq_eLpNorm_two_eq_lintegral_enorm hslice.aestronglyMeasurable] at hsq
    exact hsq
  have hglobal (j : ℕ) : (eLpNorm (δ j) 2 (ν.prod μ)) ^ (2 : ℕ) = ∫⁻ y, R j y ∂μ := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm (hδ j).aestronglyMeasurable,
      lintegral_prod_symm _ ((hδ j).enorm.pow_const (2 : ℕ)).aemeasurable]
  refine ⟨?_, ?_⟩
  · intro j
    exact (eLpNorm_fiberAction_le ν μ (T j) (hTbound j) hFm hF (hTFm j)).trans_lt
      (ENNReal.mul_lt_top hMfin.lt_top hF.eLpNorm_lt_top)
  · have hlim : ∀ᵐ y ∂μ, Tendsto (fun j => R j y) atTop (𝓝 0) := by
      filter_upwards [hfiber] with y hy
      have hs : Measurable (fun x => F (x, y)) := hFm.comp (measurable_id.prodMk measurable_const)
      have hpow := ENNReal.Tendsto.pow (n := 2) (hTlim _ hs hy)
      have heq (j) : (eLpNorm (T j (fun x => F (x, y)) - fun x => F (x, y)) 2 ν) ^ (2 : ℕ) =
          R j y := by
        have hm : Measurable (fun x => δ j (x, y)) :=
          (hδ j).comp (measurable_id.prodMk measurable_const)
        exact sq_eLpNorm_two_eq_lintegral_enorm hm.aestronglyMeasurable
      simp_rw [heq] at hpow
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hpow
    have hDCT := tendsto_lintegral_of_dominated_convergence B hRm hbound hBfin hlim
    simp only [lintegral_zero] at hDCT
    have hsqrt := hDCT.ennrpow_const (1 / 2 : ℝ)
    simp_rw [← hglobal] at hsqrt
    have hpoweq (a : ℝ≥0∞) : (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a := by
      convert ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) a using 1; norm_num
    simpa only [hpoweq, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hsqrt

end Critical2DKPZ.SHF.Tsai

end
