/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadTail
public import Critical2DKPZ.SHF.Tsai.HeadBlockBounds
public import Critical2DKPZ.SHF.Tsai.WeightedFormBoundIntegral
public import Critical2DKPZ.SHF.Tsai.HeadGaussian
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Tsai.HeadPowerConvolution
public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! # Laplace-integrated weighted incoming endpoint -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

private theorem weightedFormBound_const_mul_left {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SigmaFinite ν]
    {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ} {K : X → Y → ℝ≥0∞}
    {c r : ℝ≥0∞} (hKm : Measurable (Function.uncurry K))
    (h : WeightedFormBound μ ν wX wY p p' K c) :
    WeightedFormBound μ ν wX wY p p' (fun x y => r * K x y) (r * c) := by
  intro f g hf hg
  let NF : ℝ≥0∞ :=
    (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p : ℝ)
  let NG : ℝ≥0∞ :=
    (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p' : ℝ)
  have hInner (x : X) :
      (∫⁻ y, (r * K x y) * f y ∂ν) = r * (∫⁻ y, K x y * f y ∂ν) := by
    calc
      _ = ∫⁻ y, r * (K x y * f y) ∂ν := by
        apply lintegral_congr
        intro y
        ac_rfl
      _ = _ := lintegral_const_mul _ (hKm.comp (measurable_const.prodMk measurable_id) |>.mul hf)
  have hAct : Measurable (fun x : X => ∫⁻ y, K x y * f y ∂ν) :=
    measurable_kernelAction ν hKm hf
  have hOuter :
      (∫⁻ x, g x * (∫⁻ y, (r * K x y) * f y ∂ν) ∂μ) =
        r * (∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ) := by
    rw [show (fun x => g x * (∫⁻ y, (r * K x y) * f y ∂ν)) =
      fun x => r * (g x * (∫⁻ y, K x y * f y ∂ν)) by
        funext x
        rw [hInner x]
        ac_rfl]
    exact lintegral_const_mul r (hg.mul hAct)
  calc
    _ = r * (∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ) := hOuter
    _ ≤ r * (c * NF * NG) := mul_le_mul' le_rfl (h f g hf hg)
    _ = (r * c) * NF * NG := by simp only [mul_assoc]

private theorem measurable_laplaceTimeWeight (rate : ℝ) :
    Measurable (laplaceTimeWeight rate) := by
  unfold laplaceTimeWeight
  fun_prop

/-- The Laplace transform of the free incoming strand has a weighted
`Lᵖ → L²` form bound, uniformly for damping rates at least one. -/
theorem exists_weightedFormBound_laplace_incoming_to_L2 {n : ℕ}
    (α : CollisionPair n) {p a : ℝ} (hp : 2 < p) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ rate : ℝ, 1 ≤ rate →
      WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
        (fun x : Configuration n => a * configurationOneNorm x) p 2
        (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id))
        (ENNReal.ofReal C) := by
  obtain ⟨cIn, hcIn, hIn⟩ := weightedFormBound_incoming_to_L2 α hp ha
  let b : ℝ := 1 - 1 / p
  have hb : 0 < b := by
    dsimp [b]
    have hp0 : 0 < p := by linarith
    have hp2 : 1 < p := by linarith
    have hrecip' : 1 / p < 1 / (1 : ℝ) := one_div_lt_one_div_of_lt zero_lt_one hp2
    have hrecip : 1 / p < 1 := by simpa using hrecip'
    linarith
  have hpow : -1 / p = b - 1 := by
    dsimp [b]
    ring
  let C : ℝ := cIn * Real.Gamma b
  have hC : 0 < C := mul_pos hcIn (Real.Gamma_pos_of_pos hb)
  refine ⟨C, hC, ?_⟩
  intro rate hrate
  let K : ℝ → FusedConfiguration α → Configuration n → ℝ≥0∞ := fun t z x =>
    laplaceTimeWeight rate t *
      causalKernel (freeTimeKernel (collisionEmbedding α) id) (t, z, x)
  let c : ℝ → ℝ≥0∞ := fun t =>
    if 0 < t then laplaceTimeWeight rate t * ENNReal.ofReal (cIn * t ^ (-1 / p)) else 0
  have hKmeas : Measurable (fun q : ℝ × FusedConfiguration α × Configuration n =>
      K q.1 q.2.1 q.2.2) := by
    dsimp [K]
    exact (measurable_laplaceTimeWeight rate).comp measurable_fst |>.mul
      ((measurable_causalKernel
        (measurable_freeTimeKernel (measurable_collisionEmbedding α) measurable_id)).comp
          (by fun_prop))
  have hcm : Measurable c := by
    dsimp [c]
    have hpowm : Measurable (fun t : ℝ => t ^ (-1 / p : ℝ)) := by
      have hargs : Measurable (fun t : ℝ => (t, (-1 / p : ℝ))) := by fun_prop
      exact measurable_real_rpow.comp hargs
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      ((measurable_laplaceTimeWeight rate).mul
        ((measurable_const.mul hpowm).ennreal_ofReal)) measurable_const
  have hbound (t : ℝ) :
      WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
        (fun x : Configuration n => a * configurationOneNorm x) p 2 (K t) (c t) := by
    by_cases ht : 0 < t
    · have hbase := hIn t ht
      have hbaseMeas : Measurable (Function.uncurry (fun z : FusedConfiguration α =>
          fun x : Configuration n => ENNReal.ofReal (incomingKernel α t z x))) := by
        change Measurable (fun q : FusedConfiguration α × Configuration n =>
          ENNReal.ofReal (incomingKernel α t q.1 q.2))
        have hargs : Measurable (fun q : FusedConfiguration α × Configuration n =>
            (t, q.1, q.2)) := by fun_prop
        exact ((measurable_incomingKernel α).comp hargs).ennreal_ofReal
      have hfree :
          (fun z : FusedConfiguration α => fun x : Configuration n =>
            causalKernel (freeTimeKernel (collisionEmbedding α) id) (t, z, x)) =
          fun z x => ENNReal.ofReal (incomingKernel α t z x) := by
        funext z x
        rw [causalKernel_of_pos _ ht]
        change ENNReal.ofReal (freeKernel n t (collisionEmbedding α z) x) =
          ENNReal.ofReal (freeKernel n t x (collisionEmbedding α z))
        rw [freeKernel_symm]
      have hscaled := weightedFormBound_const_mul_left
        (r := laplaceTimeWeight rate t) hbaseMeas hbase
      have hEqK : K t = fun z x =>
          laplaceTimeWeight rate t * ENNReal.ofReal (incomingKernel α t z x) := by
        funext z x
        dsimp [K]
        rw [show causalKernel (freeTimeKernel (collisionEmbedding α) id) (t, z, x) =
          ENNReal.ofReal (incomingKernel α t z x) from congrFun (congrFun hfree z) x]
      have hEqC : c t = laplaceTimeWeight rate t *
          ENNReal.ofReal (cIn * t ^ (-1 / p)) := by simp [c, ht]
      rw [hEqK, hEqC]
      exact hscaled
    · have hKzero : K t = 0 := by
        funext z x
        dsimp [K]
        simp [causalKernel, ht]
      have hc0 : c t = 0 := by
        simp [c, ht]
      rw [hKzero, hc0]
      simp [WeightedFormBound]
  have hLap := WeightedFormBound.lintegral_param
    (κ := volume.restrict (Ioi (0 : ℝ))) (μ := volume) (ν := volume)
    (wX := fun _ : FusedConfiguration α => 0)
    (wY := fun x : Configuration n => a * configurationOneNorm x)
    (p := p) (p' := 2) (K := K) (c := c) hKmeas hcm hbound
  have hcoeff :
      (∫⁻ t in Ioi (0 : ℝ), c t) ≤ ENNReal.ofReal C := by
    have hrateExp (t : ℝ) (ht : 0 < t) :
        Real.exp (-(rate * t)) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hrate ht.le]
    have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
        c t ≤ ENNReal.ofReal (cIn * (Real.exp (-t) * t ^ (-1 / p))) := by
      have htpos : 0 < t := ht
      have hpowpos : 0 < t ^ (-1 / p : ℝ) := Real.rpow_pos_of_pos htpos _
      have hexp : laplaceTimeWeight rate t ≤ ENNReal.ofReal (Real.exp (-t)) := by
        unfold laplaceTimeWeight
        exact ENNReal.ofReal_le_ofReal (by simpa [mul_comm] using hrateExp t htpos)
      calc
        c t = laplaceTimeWeight rate t * ENNReal.ofReal (cIn * t ^ (-1 / p)) := by
          simp [c, htpos]
        _ ≤ ENNReal.ofReal (Real.exp (-t)) *
              ENNReal.ofReal (cIn * t ^ (-1 / p)) :=
                mul_le_mul' hexp le_rfl
        _ = ENNReal.ofReal (cIn * (Real.exp (-t) * t ^ (-1 / p))) := by
              rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
              congr 1
              ring
    have hGammaInt : IntegrableOn
        (fun t : ℝ => Real.exp (-t) * t ^ (-1 / p : ℝ)) (Ioi (0 : ℝ)) := by
      have hp0 : 0 < p := by linarith
      have hp1 : 1 < p := by linarith
      have hrecip' : 1 / p < 1 / (1 : ℝ) := one_div_lt_one_div_of_lt zero_lt_one hp1
      have hrecip : 1 / p < 1 := by simpa using hrecip'
      have hs : -1 < -1 / p := by linarith
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := -1 / p) hs one_pos one_pos
      simpa [Real.rpow_one, one_mul, mul_neg_one, mul_comm] using h
    have hGammaAE :
        0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
          (fun t : ℝ => cIn * (Real.exp (-t) * t ^ (-1 / p : ℝ))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hcIn.le
        (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht.le _))
    have hGammaVal :
        (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (-1 / p : ℝ)) = Real.Gamma b := by
      calc
        _ = ∫ t in Ioi (0 : ℝ), t ^ (b - 1) * Real.exp (-t) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              rw [hpow]
              ring
        _ = (1 / (1 : ℝ)) ^ b * Real.Gamma b := by
              calc
                _ = ∫ t in Ioi (0 : ℝ), t ^ (b - 1) * Real.exp (-(1 * t)) := by
                      apply setIntegral_congr_fun measurableSet_Ioi
                      intro t ht
                      simp only [one_mul]
                _ = _ := Real.integral_rpow_mul_exp_neg_mul_Ioi hb one_pos
        _ = Real.Gamma b := by norm_num
    have hGammaLin :
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (cIn * (Real.exp (-t) * t ^ (-1 / p : ℝ)))) = ENNReal.ofReal C := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hGammaInt.const_mul cIn) hGammaAE]
      rw [integral_const_mul, hGammaVal]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (cIn * (Real.exp (-t) * t ^ (-1 / p : ℝ))) := by
            apply setLIntegral_mono (by fun_prop)
            intro t ht
            exact hpoint t ht
      _ = ENNReal.ofReal C := hGammaLin
  have hkernel (z : FusedConfiguration α) (x : Configuration n) :
      (∫⁻ t in Ioi (0 : ℝ), K t z x) =
        laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id) z x := by
    unfold laplaceTimeKernel
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    change laplaceTimeWeight rate t *
      causalKernel (freeTimeKernel (collisionEmbedding α) id) (t, z, x) = _
    rw [causalKernel_of_pos _ htpos]
  exact WeightedFormBound.mono hLap
    (by intro z x; exact (hkernel z x).symm.le) hcoeff

/-- The Laplace-damped incoming kernel has a weighted `Lᵖ → L²` form bound of order `rate^{-(1 - 1/p)}` for every positive damping rate. -/
theorem exists_weightedFormBound_laplace_incoming_to_L2_scaled {n : ℕ}
    (α : CollisionPair n) {p a : ℝ} (hp : 2 < p) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ rate : ℝ, 0 < rate →
      WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
        (fun x : Configuration n => a * configurationOneNorm x) p 2
        (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id))
        (ENNReal.ofReal (C * (1 / rate) ^ (1 - 1 / p))) := by
  obtain ⟨cIn, hcIn, hIn⟩ := weightedFormBound_incoming_to_L2 α hp ha
  let b : ℝ := 1 - 1 / p
  have hb : 0 < b := by
    dsimp [b]
    have hp0 : 0 < p := by linarith
    have hp1 : 1 < p := by linarith
    have hrecip : 1 / p < 1 := by
      simpa using (one_div_lt_one_div_of_lt zero_lt_one hp1)
    linarith
  have hpow : b - 1 = -1 / p := by dsimp [b]; ring
  let C : ℝ := cIn * Real.Gamma b
  have hC : 0 < C := mul_pos hcIn (Real.Gamma_pos_of_pos hb)
  refine ⟨C, hC, ?_⟩
  intro rate hrate
  let K : ℝ → FusedConfiguration α → Configuration n → ℝ≥0∞ := fun t z x =>
    laplaceTimeWeight rate t *
      causalKernel (freeTimeKernel (collisionEmbedding α) id) (t, z, x)
  let c : ℝ → ℝ≥0∞ := fun t =>
    if 0 < t then laplaceTimeWeight rate t *
      ENNReal.ofReal (cIn * t ^ (-1 / p)) else 0
  have hKmeas : Measurable (fun q : ℝ × FusedConfiguration α × Configuration n =>
      K q.1 q.2.1 q.2.2) := by
    dsimp [K]
    exact (measurable_laplaceTimeWeight rate).comp measurable_fst |>.mul
      ((measurable_causalKernel
        (measurable_freeTimeKernel (measurable_collisionEmbedding α) measurable_id)).comp
          (by fun_prop))
  have hcm : Measurable c := by
    dsimp [c]
    have hpowm : Measurable (fun t : ℝ => t ^ (-1 / p : ℝ)) := by
      have hargs : Measurable (fun t : ℝ => (t, (-1 / p : ℝ))) := by fun_prop
      exact measurable_real_rpow.comp hargs
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      ((measurable_laplaceTimeWeight rate).mul
        ((measurable_const.mul hpowm).ennreal_ofReal)) measurable_const
  have hbound (t : ℝ) :
      WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
        (fun x : Configuration n => a * configurationOneNorm x) p 2
        (K t) (c t) := by
    by_cases ht : 0 < t
    · have hbase := hIn t ht
      have hbaseMeas : Measurable (Function.uncurry (fun z : FusedConfiguration α =>
          fun x : Configuration n => ENNReal.ofReal (incomingKernel α t z x))) := by
        change Measurable (fun q : FusedConfiguration α × Configuration n =>
          ENNReal.ofReal (incomingKernel α t q.1 q.2))
        have hargs : Measurable (fun q : FusedConfiguration α × Configuration n =>
            (t, q.1, q.2)) := by fun_prop
        exact ((measurable_incomingKernel α).comp hargs).ennreal_ofReal
      have hfree :
          (fun z : FusedConfiguration α => fun x : Configuration n =>
            causalKernel (freeTimeKernel (collisionEmbedding α) id) (t, z, x)) =
          fun z x => ENNReal.ofReal (incomingKernel α t z x) := by
        funext z x
        rw [causalKernel_of_pos _ ht]
        change ENNReal.ofReal (freeKernel n t (collisionEmbedding α z) x) =
          ENNReal.ofReal (freeKernel n t x (collisionEmbedding α z))
        rw [freeKernel_symm]
      have hscaled := weightedFormBound_const_mul_left
        (r := laplaceTimeWeight rate t) hbaseMeas hbase
      have hEqK : K t = fun z x =>
          laplaceTimeWeight rate t * ENNReal.ofReal (incomingKernel α t z x) := by
        funext z x
        dsimp [K]
        rw [show causalKernel (freeTimeKernel (collisionEmbedding α) id) (t, z, x) =
          ENNReal.ofReal (incomingKernel α t z x) from congrFun (congrFun hfree z) x]
      have hEqC : c t = laplaceTimeWeight rate t *
          ENNReal.ofReal (cIn * t ^ (-1 / p)) := by simp [c, ht]
      rw [hEqK, hEqC]
      exact hscaled
    · have hKzero : K t = 0 := by
        funext z x
        dsimp [K]
        simp [causalKernel, ht]
      have hc0 : c t = 0 := by simp [c, ht]
      rw [hKzero, hc0]
      simp [WeightedFormBound]
  have hLap := WeightedFormBound.lintegral_param
    (κ := volume.restrict (Ioi (0 : ℝ))) (μ := volume) (ν := volume)
    (wX := fun _ : FusedConfiguration α => 0)
    (wY := fun x : Configuration n => a * configurationOneNorm x)
    (p := p) (p' := 2) (K := K) (c := c) hKmeas hcm hbound
  have hGammaInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(rate * t)) * t ^ (-1 / p : ℝ)) (Ioi (0 : ℝ)) := by
    have hp1 : 1 < p := by linarith
    have hrecip : 1 / p < 1 := by
      simpa using (one_div_lt_one_div_of_lt zero_lt_one hp1)
    have hs : -1 < -1 / p := by linarith
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := -1 / p) (b := rate) hs one_pos hrate
    simpa [Real.rpow_one, one_mul, mul_comm] using hi
  have hGammaNonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => cIn * (Real.exp (-(rate * t)) * t ^ (-1 / p : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hcIn.le
      (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht.le _))
  have hGammaVal :
      (∫ t in Ioi (0 : ℝ), Real.exp (-(rate * t)) * t ^ (-1 / p : ℝ)) =
        (1 / rate) ^ b * Real.Gamma b := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), t ^ (b - 1) * Real.exp (-(rate * t)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            rw [hpow]
            ring
      _ = _ := Real.integral_rpow_mul_exp_neg_mul_Ioi hb hrate
  have hGammaLin :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (cIn * (Real.exp (-(rate * t)) * t ^ (-1 / p : ℝ)))) =
        ENNReal.ofReal (C * (1 / rate) ^ b) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hGammaInt.const_mul cIn) hGammaNonneg]
    rw [integral_const_mul, hGammaVal]
    simp [C, mul_left_comm, mul_comm]
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      c t = ENNReal.ofReal
        (cIn * (Real.exp (-(rate * t)) * t ^ (-1 / p : ℝ))) := by
    have htpos : 0 < t := ht
    calc
      c t = laplaceTimeWeight rate t * ENNReal.ofReal (cIn * t ^ (-1 / p)) := by
        simp [c, htpos]
      _ = ENNReal.ofReal (Real.exp (-(rate * t))) *
            ENNReal.ofReal (cIn * t ^ (-1 / p)) := by rfl
      _ = ENNReal.ofReal
            (cIn * (Real.exp (-(rate * t)) * t ^ (-1 / p : ℝ))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          ring
  have hcoeff : (∫⁻ t in Ioi (0 : ℝ), c t) =
      ENNReal.ofReal (C * (1 / rate) ^ b) := by
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (cIn * (Real.exp (-(rate * t)) * t ^ (-1 / p : ℝ))) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact hpoint t ht
      _ = _ := hGammaLin
  have hkernel (z : FusedConfiguration α) (x : Configuration n) :
      (∫⁻ t in Ioi (0 : ℝ), K t z x) =
        laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id) z x := by
    change laplaceTimeKernel rate
      (causalKernel (freeTimeKernel (collisionEmbedding α) id)) z x = _
    exact laplaceTimeKernel_causalKernel rate _ z x
  have hFinal := hLap.mono (fun z x => (hkernel z x).symm.le) hcoeff.le
  simpa [b] using hFinal

end Critical2DKPZ.SHF.Tsai

end
