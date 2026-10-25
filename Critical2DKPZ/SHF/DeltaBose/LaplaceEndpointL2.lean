/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
public import Critical2DKPZ.SHF.DeltaBose.TraceL2
public import Critical2DKPZ.SHF.Flow.KernelMixture
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! # Laplace integrated collision traces on squared L² -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The scalar time majorant for a Laplace integrated endpoint trace. -/
noncomputable def laplaceIncomingTimeMajorant (rate t : ℝ) : ℝ≥0∞ :=
  laplaceTimeWeight rate t * ENNReal.ofReal ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)))


/-- The Laplace-integrated incoming heat trace has a squared L² bound given by the time integral of the square-root trace bound. -/
theorem laplaceTimeKernel_incoming_l2_sq_le {n : ℕ} (α : CollisionPair n)
    (rate : ℝ) {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ x : Configuration n,
        laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id) z x * f x) ^ 2) ≤
      (∫⁻ t in Ioi (0 : ℝ), laplaceIncomingTimeMajorant rate t) ^ 2 *
        ∫⁻ x : Configuration n, f x ^ 2 := by
  let H : ℝ → FusedConfiguration α → ℝ≥0∞ := fun t z =>
    laplaceTimeWeight rate t *
      (∫⁻ x : Configuration n, ENNReal.ofReal (incomingKernel α t z x) * f x)
  let a : ℝ → ℝ≥0∞ := laplaceIncomingTimeMajorant rate
  have hweight : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
    unfold laplaceTimeWeight
    fun_prop
  have hin : Measurable (fun p : (ℝ × FusedConfiguration α) × Configuration n =>
      ENNReal.ofReal (incomingKernel α p.1.1 p.1.2 p.2)) := by
    have hp : Measurable (fun p : (ℝ × FusedConfiguration α) × Configuration n =>
        (p.1.1, (p.1.2, p.2))) := by fun_prop
    exact ((measurable_incomingKernel α).comp hp).ennreal_ofReal
  have hIntegrand : Measurable (fun p : (ℝ × FusedConfiguration α) × Configuration n =>
      laplaceTimeWeight rate p.1.1 *
        (ENNReal.ofReal (incomingKernel α p.1.1 p.1.2 p.2) * f p.2)) := by
    have hw : Measurable (fun p : (ℝ × FusedConfiguration α) × Configuration n =>
        laplaceTimeWeight rate p.1.1) :=
      hweight.comp (measurable_fst.comp measurable_fst)
    have hf' : Measurable (fun p : (ℝ × FusedConfiguration α) × Configuration n => f p.2) :=
      hf.comp measurable_snd
    exact hw.mul (hin.mul hf')
  have hH : Measurable (Function.uncurry H) := by
    change Measurable (fun p : ℝ × FusedConfiguration α =>
      laplaceTimeWeight rate p.1 *
        ∫⁻ x : Configuration n,
          ENNReal.ofReal (incomingKernel α p.1 p.2 x) * f x)
    have h' := hIntegrand.lintegral_prod_right' (ν := volume)
    convert h' using 1
    funext p
    rw [← lintegral_const_mul' _ _ (by
      unfold laplaceTimeWeight
      exact ENNReal.ofReal_ne_top)]
  have ha : Measurable a := by
    dsimp [a, laplaceIncomingTimeMajorant]
    exact hweight.mul ((measurable_const.mul measurable_id).pow_const _).ennreal_ofReal
  have ha0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), a t ≠ 0 ∧ a t ≠ ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hwpos : laplaceTimeWeight rate t ≠ 0 := by
      unfold laplaceTimeWeight
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hwtop : laplaceTimeWeight rate t ≠ ⊤ := by
      unfold laplaceTimeWeight
      exact ENNReal.ofReal_ne_top
    have ht' : 0 < t := ht
    have hrpos : 0 < (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact ⟨mul_ne_zero hwpos (ENNReal.ofReal_pos.mpr hrpos).ne',
      ENNReal.mul_ne_top hwtop ENNReal.ofReal_ne_top⟩
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (∫⁻ z : FusedConfiguration α, H t z ^ 2) ≤
        a t ^ 2 * ∫⁻ x : Configuration n, f x ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htrace := incomingKernel_l2_sq_le α ht hf
    have hbase : 0 < 4 * Real.pi * t := by
      have htpos : 0 < t := ht
      positivity
    have hroot : ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 2 = (4 * Real.pi * t)⁻¹ := by
      rw [← Real.rpow_mul_natCast hbase.le (-(1 / 2 : ℝ)) 2]
      rw [show (↑(2 : ℕ) : ℝ) = 2 by norm_num,
        show -(1 / 2 : ℝ) * (2 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    have hcoef : a t ^ 2 = laplaceTimeWeight rate t ^ 2 *
        ENNReal.ofReal (4 * Real.pi * t)⁻¹ := by
      dsimp [a, laplaceIncomingTimeMajorant]
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.rpow_pos_of_pos hbase _).le, hroot]
    have hweightTop : laplaceTimeWeight rate t ^ 2 ≠ ⊤ := by
      exact ENNReal.pow_ne_top (by unfold laplaceTimeWeight; exact ENNReal.ofReal_ne_top)
    have hscaled :
        (∫⁻ z : FusedConfiguration α, H t z ^ 2) =
          laplaceTimeWeight rate t ^ 2 *
            ∫⁻ z : FusedConfiguration α,
              (∫⁻ x : Configuration n,
                ENNReal.ofReal (incomingKernel α t z x) * f x) ^ 2 := by
      calc
        _ = ∫⁻ z : FusedConfiguration α,
            laplaceTimeWeight rate t ^ 2 *
              (∫⁻ x : Configuration n,
                ENNReal.ofReal (incomingKernel α t z x) * f x) ^ 2 := by
              apply lintegral_congr
              intro z
              simp only [H, mul_pow]
        _ = _ := lintegral_const_mul' _ _ hweightTop
    calc
      ∫⁻ z : FusedConfiguration α, H t z ^ 2 =
          laplaceTimeWeight rate t ^ 2 *
          ∫⁻ z : FusedConfiguration α,
            (∫⁻ x : Configuration n,
              ENNReal.ofReal (incomingKernel α t z x) * f x) ^ 2 := hscaled
      _ ≤ laplaceTimeWeight rate t ^ 2 *
            (ENNReal.ofReal (4 * Real.pi * t)⁻¹ *
              ∫⁻ x : Configuration n, f x ^ 2) :=
          mul_le_mul' le_rfl htrace
      _ = (laplaceTimeWeight rate t ^ 2 * ENNReal.ofReal (4 * Real.pi * t)⁻¹) *
            ∫⁻ x : Configuration n, f x ^ 2 := by ac_rfl
      _ = a t ^ 2 * ∫⁻ x : Configuration n, f x ^ 2 := by rw [hcoef]
  have hmix := Critical2DKPZ.SHF.Flow.lintegral_mixture_sq_le
    (volume.restrict (Ioi (0 : ℝ))) volume hH ha ha0 hbound
  have hAction (z : FusedConfiguration α) :
      (∫⁻ t in Ioi (0 : ℝ), H t z) =
        ∫⁻ x : Configuration n,
          laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id) z x * f x := by
    let F : ℝ → Configuration n → ℝ≥0∞ := fun t x =>
      laplaceTimeWeight rate t *
        (ENNReal.ofReal (incomingKernel α t z x) * f x)
    have hF : Measurable (Function.uncurry F) := by
      have hp : Measurable (fun p : ℝ × Configuration n => (p.1, (z, p.2))) := by
        fun_prop
      have hk := ((measurable_incomingKernel α).comp hp).ennreal_ofReal
      exact (hweight.comp measurable_fst).mul (hk.mul (hf.comp measurable_snd))
    have hswap := lintegral_lintegral_swap
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume) hF.aemeasurable
    calc
      (∫⁻ t in Ioi (0 : ℝ), H t z) =
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Configuration n,
            laplaceTimeWeight rate t *
              (ENNReal.ofReal (incomingKernel α t z x) * f x) := by
            apply lintegral_congr
            intro t
            simp only [H]
            rw [lintegral_const_mul' _ _ (by
              unfold laplaceTimeWeight
              exact ENNReal.ofReal_ne_top)]
      _ = ∫⁻ x : Configuration n, ∫⁻ t in Ioi (0 : ℝ), F t x := hswap
      _ = ∫⁻ x : Configuration n,
          laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id) z x * f x := by
            apply lintegral_congr
            intro x
            have hk : Measurable (fun t : ℝ =>
                laplaceTimeWeight rate t * ENNReal.ofReal (incomingKernel α t z x)) := by
              exact (hweight.mul
                (((measurable_incomingKernel α).comp
                  (measurable_id.prodMk
                    (measurable_const.prodMk measurable_const))).ennreal_ofReal))
            have hFmul : (fun t : ℝ => F t x) = fun t =>
                (laplaceTimeWeight rate t *
                  ENNReal.ofReal (incomingKernel α t z x)) * f x := by
              funext t
              dsimp [F]
              ac_rfl
            rw [hFmul, lintegral_mul_const _ hk, laplaceTimeKernel]
            congr 1
            apply lintegral_congr
            intro t
            simp only [freeTimeKernel, id_eq]
            congr 2
            exact freeKernel_symm n t x (collisionEmbedding α z)
  calc
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ x : Configuration n,
        laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id) z x * f x) ^ 2) =
      ∫⁻ z : FusedConfiguration α, (∫⁻ t in Ioi (0 : ℝ), H t z) ^ 2 := by
        apply lintegral_congr
        intro z
        rw [hAction z]
    _ ≤ (∫⁻ t in Ioi (0 : ℝ), a t) ^ 2 * ∫⁻ x : Configuration n, f x ^ 2 := hmix
    _ = _ := rfl

/-- The transposed Laplace integrated incoming trace has the same squared
`L²` bound, for data on the fused collision space. -/
theorem laplaceTimeKernel_incoming_adjoint_l2_sq_le {n : ℕ} (α : CollisionPair n)
    (rate : ℝ) {f : FusedConfiguration α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n,
      (∫⁻ z : FusedConfiguration α,
        laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)) x z * f z) ^ 2) ≤
      (∫⁻ t in Ioi (0 : ℝ), laplaceIncomingTimeMajorant rate t) ^ 2 *
        ∫⁻ z : FusedConfiguration α, f z ^ 2 := by
  let H : ℝ → Configuration n → ℝ≥0∞ := fun t x =>
    laplaceTimeWeight rate t *
      (∫⁻ z : FusedConfiguration α, ENNReal.ofReal (incomingKernel α t z x) * f z)
  let a : ℝ → ℝ≥0∞ := laplaceIncomingTimeMajorant rate
  have hweight : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
    unfold laplaceTimeWeight
    fun_prop
  have hin : Measurable (fun p : (ℝ × Configuration n) × FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α p.1.1 p.2 p.1.2)) := by
    have hp : Measurable (fun p : (ℝ × Configuration n) × FusedConfiguration α =>
        (p.1.1, (p.2, p.1.2))) := by fun_prop
    exact ((measurable_incomingKernel α).comp hp).ennreal_ofReal
  have hIntegrand : Measurable (fun p : (ℝ × Configuration n) × FusedConfiguration α =>
      laplaceTimeWeight rate p.1.1 *
        (ENNReal.ofReal (incomingKernel α p.1.1 p.2 p.1.2) * f p.2)) := by
    have hw : Measurable (fun p : (ℝ × Configuration n) × FusedConfiguration α =>
        laplaceTimeWeight rate p.1.1) :=
      hweight.comp (measurable_fst.comp measurable_fst)
    have hf' : Measurable
        (fun p : (ℝ × Configuration n) × FusedConfiguration α => f p.2) :=
      hf.comp measurable_snd
    exact hw.mul (hin.mul hf')
  have hH : Measurable (Function.uncurry H) := by
    change Measurable (fun p : ℝ × Configuration n =>
      laplaceTimeWeight rate p.1 *
        ∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α p.1 z p.2) * f z)
    have h' := hIntegrand.lintegral_prod_right' (ν := volume)
    convert h' using 1
    funext p
    rw [← lintegral_const_mul' _ _ (by
      unfold laplaceTimeWeight
      exact ENNReal.ofReal_ne_top)]
  have ha : Measurable a := by
    dsimp [a, laplaceIncomingTimeMajorant]
    exact hweight.mul ((measurable_const.mul measurable_id).pow_const _).ennreal_ofReal
  have ha0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), a t ≠ 0 ∧ a t ≠ ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hwpos : laplaceTimeWeight rate t ≠ 0 := by
      unfold laplaceTimeWeight
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hwtop : laplaceTimeWeight rate t ≠ ⊤ := by
      unfold laplaceTimeWeight
      exact ENNReal.ofReal_ne_top
    have ht' : 0 < t := ht
    have hrpos : 0 < (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact ⟨mul_ne_zero hwpos (ENNReal.ofReal_pos.mpr hrpos).ne',
      ENNReal.mul_ne_top hwtop ENNReal.ofReal_ne_top⟩
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (∫⁻ x : Configuration n, H t x ^ 2) ≤
        a t ^ 2 * ∫⁻ z : FusedConfiguration α, f z ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htrace := incomingKernel_adjoint_l2_sq_le α ht hf
    have htpos : 0 < t := ht
    have hbase : 0 < 4 * Real.pi * t := by positivity
    have hroot : ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 2 = (4 * Real.pi * t)⁻¹ := by
      rw [← Real.rpow_mul_natCast hbase.le (-(1 / 2 : ℝ)) 2,
        show (↑(2 : ℕ) : ℝ) = 2 by norm_num,
        show -(1 / 2 : ℝ) * (2 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    have hcoef : a t ^ 2 = laplaceTimeWeight rate t ^ 2 *
        ENNReal.ofReal (4 * Real.pi * t)⁻¹ := by
      dsimp [a, laplaceIncomingTimeMajorant]
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.rpow_pos_of_pos hbase _).le, hroot]
    have hweightTop : laplaceTimeWeight rate t ^ 2 ≠ ⊤ := by
      exact ENNReal.pow_ne_top (by unfold laplaceTimeWeight; exact ENNReal.ofReal_ne_top)
    have hscaled :
        (∫⁻ x : Configuration n, H t x ^ 2) =
          laplaceTimeWeight rate t ^ 2 *
            ∫⁻ x : Configuration n,
              (∫⁻ z : FusedConfiguration α,
                ENNReal.ofReal (incomingKernel α t z x) * f z) ^ 2 := by
      calc
        _ = ∫⁻ x : Configuration n,
            laplaceTimeWeight rate t ^ 2 *
              (∫⁻ z : FusedConfiguration α,
                ENNReal.ofReal (incomingKernel α t z x) * f z) ^ 2 := by
              apply lintegral_congr
              intro x
              simp only [H, mul_pow]
        _ = _ := lintegral_const_mul' _ _ hweightTop
    calc
      ∫⁻ x : Configuration n, H t x ^ 2 =
          laplaceTimeWeight rate t ^ 2 *
            ∫⁻ x : Configuration n,
              (∫⁻ z : FusedConfiguration α,
                ENNReal.ofReal (incomingKernel α t z x) * f z) ^ 2 := hscaled
      _ ≤ laplaceTimeWeight rate t ^ 2 *
            (ENNReal.ofReal (4 * Real.pi * t)⁻¹ *
              ∫⁻ z : FusedConfiguration α, f z ^ 2) := mul_le_mul' le_rfl htrace
      _ = (laplaceTimeWeight rate t ^ 2 * ENNReal.ofReal (4 * Real.pi * t)⁻¹) *
            ∫⁻ z : FusedConfiguration α, f z ^ 2 := by ac_rfl
      _ = a t ^ 2 * ∫⁻ z : FusedConfiguration α, f z ^ 2 := by rw [hcoef]
  have hmix := Critical2DKPZ.SHF.Flow.lintegral_mixture_sq_le
    (volume.restrict (Ioi (0 : ℝ))) volume hH ha ha0 hbound
  have hAction (x : Configuration n) :
      (∫⁻ t in Ioi (0 : ℝ), H t x) =
        ∫⁻ z : FusedConfiguration α,
          laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)) x z * f z := by
    let F : ℝ → FusedConfiguration α → ℝ≥0∞ := fun t z =>
      laplaceTimeWeight rate t *
        (ENNReal.ofReal (incomingKernel α t z x) * f z)
    have hF : Measurable (Function.uncurry F) := by
      have hp : Measurable (fun p : ℝ × FusedConfiguration α =>
          (p.1, (p.2, x))) := by fun_prop
      have hk := ((measurable_incomingKernel α).comp hp).ennreal_ofReal
      exact (hweight.comp measurable_fst).mul (hk.mul (hf.comp measurable_snd))
    have hswap := lintegral_lintegral_swap
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume) hF.aemeasurable
    calc
      (∫⁻ t in Ioi (0 : ℝ), H t x) =
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ z : FusedConfiguration α,
            laplaceTimeWeight rate t *
              (ENNReal.ofReal (incomingKernel α t z x) * f z) := by
            apply lintegral_congr
            intro t
            simp only [H]
            rw [lintegral_const_mul' _ _ (by
              unfold laplaceTimeWeight
              exact ENNReal.ofReal_ne_top)]
      _ = ∫⁻ z : FusedConfiguration α, ∫⁻ t in Ioi (0 : ℝ), F t z := hswap
      _ = ∫⁻ z : FusedConfiguration α,
          laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)) x z * f z := by
            apply lintegral_congr
            intro z
            have hk : Measurable (fun t : ℝ =>
                laplaceTimeWeight rate t * ENNReal.ofReal (incomingKernel α t z x)) := by
              exact (hweight.mul
                (((measurable_incomingKernel α).comp
                  (measurable_id.prodMk
                    (measurable_const.prodMk measurable_const))).ennreal_ofReal))
            have hFmul : (fun t : ℝ => F t z) = fun t =>
                (laplaceTimeWeight rate t *
                  ENNReal.ofReal (incomingKernel α t z x)) * f z := by
              funext t
              dsimp [F]
              ac_rfl
            rw [hFmul, lintegral_mul_const _ hk, laplaceTimeKernel]
            congr 1
  calc
    (∫⁻ x : Configuration n,
      (∫⁻ z : FusedConfiguration α,
        laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)) x z * f z) ^ 2) =
      ∫⁻ x : Configuration n, (∫⁻ t in Ioi (0 : ℝ), H t x) ^ 2 := by
        apply lintegral_congr
        intro x
        rw [hAction x]
    _ ≤ (∫⁻ t in Ioi (0 : ℝ), a t) ^ 2 * ∫⁻ z : FusedConfiguration α, f z ^ 2 := hmix
    _ = _ := rfl


end Critical2DKPZ.DeltaBose
