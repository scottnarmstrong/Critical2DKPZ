/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PiCoordinateSplit
public import Critical2DKPZ.SHF.Tsai.Tech
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Tsai.HeadCoordinateSplit
public import Critical2DKPZ.SHF.Tsai.HeadOneCollision
public import Critical2DKPZ.SHF.DeltaBose.SupBlockBounds
import Mathlib.Tactic

/-! # A heat strand attached to a weighted form bound -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Weighted positive form bounds are preserved by measure-preserving endpoint
coordinate changes. -/
theorem WeightedFormBound.pullback {X Y X' Y' : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
    {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
    (eX : X ≃ᵐ X') (eY : Y ≃ᵐ Y')
    (heX : MeasurePreserving eX μ μ') (heY : MeasurePreserving eY ν ν')
    {wX' : X' → ℝ} {wY' : Y' → ℝ} {p p' : ℝ}
    {K : X' → Y' → ℝ≥0∞} {c : ℝ≥0∞}
    (hK : WeightedFormBound μ' ν' wX' wY' p p' K c) :
    WeightedFormBound μ ν (fun x => wX' (eX x)) (fun y => wY' (eY y)) p p'
      (fun x y => K (eX x) (eY y)) c := by
  intro f g hf hg
  have h := hK (fun y' => f (eY.symm y')) (fun x' => g (eX.symm x'))
    (hf.comp eY.symm.measurable) (hg.comp eX.symm.measurable)
  have hinner (x' : X') :
      (∫⁻ y', K x' y' * f (eY.symm y') ∂ν') =
        ∫⁻ y, K x' (eY y) * f y ∂ν := by
    simpa only [eY.symm_apply_apply] using
      (heY.lintegral_comp_emb eY.measurableEmbedding
        (fun y' => K x' y' * f (eY.symm y'))).symm
  have hleft :
      (∫⁻ x, g x * (∫⁻ y, K (eX x) (eY y) * f y ∂ν) ∂μ) =
        ∫⁻ x', g (eX.symm x') *
          (∫⁻ y', K x' y' * f (eY.symm y') ∂ν') ∂μ' := by
    have ht := heX.lintegral_comp_emb eX.measurableEmbedding
      (fun x' => g (eX.symm x') *
        ∫⁻ y', K x' y' * f (eY.symm y') ∂ν')
    simpa only [eX.symm_apply_apply, hinner] using ht
  have hfnorm :
      (∫⁻ y', (f (eY.symm y') * ENNReal.ofReal (Real.exp (wY' y'))) ^ p ∂ν') =
        ∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY' (eY y)))) ^ p ∂ν := by
    simpa only [eY.symm_apply_apply] using
      (heY.lintegral_comp_emb eY.measurableEmbedding
        (fun y' => (f (eY.symm y') * ENNReal.ofReal (Real.exp (wY' y'))) ^ p)).symm
  have hgnorm :
      (∫⁻ x', (g (eX.symm x') * ENNReal.ofReal (Real.exp (wX' x'))) ^ p' ∂μ') =
        ∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX' (eX x)))) ^ p' ∂μ := by
    simpa only [eX.symm_apply_apply] using
      (heX.lintegral_comp_emb eX.measurableEmbedding
        (fun x' => (g (eX.symm x') * ENNReal.ofReal (Real.exp (wX' x'))) ^ p')).symm
  rw [← hleft, hfnorm, hgnorm] at h
  exact h

/-- An independent planar heat strand can be integrated against the weighted
test function before applying the remaining kernel form bound. -/
theorem WeightedFormBound.planarHeatFactor_of_eval {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {N : X → ℝ} {η : Y → Plane} {a p : ℝ}
    {R : X → Y → ℝ≥0∞} {d : ℝ≥0∞} {c : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a)
    (hN : Measurable N) (hη : Measurable η)
    (hR : Measurable (Function.uncurry R))
    (hEval : ∀ s : ℝ, 0 < s → ∀ y : Plane, ∀ ψ : Plane → ℝ≥0∞,
      Measurable ψ →
        (∫⁻ ξ : Plane,
          ENNReal.ofReal (heatKernel s (y - ξ)) * ψ ξ ∂volume) ≤
          ENNReal.ofReal (c * s ^ (-1 / p)) *
            (∫⁻ ξ : Plane, ψ ξ ^ p ∂volume) ^ (1 / p))
    (hbound : WeightedFormBound μ ν (fun x => a * N x) (fun _ : Y => 0)
      2 p R d) :
    ∀ s : ℝ, 0 < s →
      WeightedFormBound (μ.prod volume) ν
        (fun q : X × Plane => a * (N q.1 + planeOneNorm q.2))
        (fun _ : Y => 0) 2 p
        (fun q y => ENNReal.ofReal (heatKernel s (η y - q.2)) * R q.1 y)
        (d * ENNReal.ofReal (c * s ^ (-1 / p))) := by
  have hp0 : 0 < p := by linarith
  intro s hs f g hf hg
  let Eξ : Plane → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Real.exp (a * planeOneNorm ξ))
  let K : X × Plane → Y → ℝ≥0∞ := fun q y =>
    ENNReal.ofReal (heatKernel s (η y - q.2)) * R q.1 y
  let Gξ : X × Plane → ℝ≥0∞ := fun q => g q * Eξ q.2
  let S : X → ℝ≥0∞ := fun x => (∫⁻ ξ : Plane, Gξ (x, ξ) ^ p) ^ (1 / p : ℝ)
  have hEξ : Measurable Eξ := by
    dsimp [Eξ]
    exact (measurable_const.mul measurable_planeOneNorm).exp.ennreal_ofReal
  have hK : Measurable (Function.uncurry K) := by
    dsimp [K]
    have hArg : Measurable (fun q : (X × Plane) × Y => η q.2 - q.1.2) :=
      (hη.comp measurable_snd).sub (measurable_snd.comp measurable_fst)
    exact ((measurable_heatKernel s).comp hArg).ennreal_ofReal |>.mul
      (hR.comp (measurable_fst.fst.prodMk measurable_snd))
  have hGξ : Measurable Gξ := by
    dsimp [Gξ]
    exact hg.mul (hEξ.comp measurable_snd)
  have hGξp : Measurable (fun q : X × Plane => Gξ q ^ p) := by fun_prop
  have hSpow : Measurable (fun x : X => ∫⁻ ξ : Plane, Gξ (x, ξ) ^ p) :=
    hGξp.lintegral_prod_right'
  have hS : Measurable S := by
    dsimp [S]
    exact (ENNReal.continuous_rpow_const (y := (1 / p : ℝ))).measurable.comp hSpow
  have hE : Measurable (fun x : X => ENNReal.ofReal (Real.exp (a * N x))) :=
    (measurable_const.mul hN).exp.ennreal_ofReal
  have hWeight : Measurable (fun q : X × Plane =>
      ENNReal.ofReal (Real.exp (a * (N q.1 + planeOneNorm q.2)))) := by
    have hreal : Measurable (fun q : X × Plane =>
        Real.exp (a * (N q.1 + planeOneNorm q.2))) :=
      (measurable_const.mul
        ((hN.comp measurable_fst).add (measurable_planeOneNorm.comp measurable_snd))).exp
    exact hreal.ennreal_ofReal
  have hWeightMul (x : X) (ξ : Plane) :
      ENNReal.ofReal (Real.exp (a * (N x + planeOneNorm ξ))) =
        ENNReal.ofReal (Real.exp (a * N x)) * Eξ ξ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have hSweight (x : X) :
      (S x * ENNReal.ofReal (Real.exp (a * N x))) ^ p =
        ∫⁻ ξ : Plane,
          (g (x, ξ) * ENNReal.ofReal (Real.exp (a * (N x + planeOneNorm ξ)))) ^ p := by
    have hSpower : S x ^ p = ∫⁻ ξ : Plane, Gξ (x, ξ) ^ p := by
      dsimp [S]
      rw [← ENNReal.rpow_mul]
      have hpInv : (1 / p : ℝ) * p = 1 := by field_simp
      rw [hpInv, ENNReal.rpow_one]
    calc
      _ = S x ^ p * ENNReal.ofReal (Real.exp (a * N x)) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      _ = (∫⁻ ξ : Plane, Gξ (x, ξ) ^ p) *
            ENNReal.ofReal (Real.exp (a * N x)) ^ p := by rw [hSpower]
      _ = ENNReal.ofReal (Real.exp (a * N x)) ^ p *
            (∫⁻ ξ : Plane, Gξ (x, ξ) ^ p) := by rw [mul_comm]
      _ = ∫⁻ ξ : Plane,
            ENNReal.ofReal (Real.exp (a * N x)) ^ p * Gξ (x, ξ) ^ p := by
        rw [lintegral_const_mul _ (by fun_prop)]
      _ = ∫⁻ ξ : Plane,
            (g (x, ξ) * ENNReal.ofReal
              (Real.exp (a * (N x + planeOneNorm ξ)))) ^ p := by
        apply lintegral_congr
        intro ξ
        rw [show Gξ (x, ξ) = g (x, ξ) * Eξ ξ by rfl, hWeightMul]
        calc
          _ = (g (x, ξ) ^ p * Eξ ξ ^ p) *
                ENNReal.ofReal (Real.exp (a * N x)) ^ p := by
                  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
                  ac_rfl
          _ = (g (x, ξ) *
                (ENNReal.ofReal (Real.exp (a * N x)) * Eξ ξ)) ^ p := by
                  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
                    ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
                  ac_rfl
  have hNormEq :
      (∫⁻ x : X, (S x * ENNReal.ofReal (Real.exp (a * N x))) ^ p ∂μ) =
        ∫⁻ q : X × Plane,
          (g q * ENNReal.ofReal
            (Real.exp (a * (N q.1 + planeOneNorm q.2)))) ^ p ∂μ.prod volume := by
    calc
      _ = ∫⁻ x : X, ∫⁻ ξ : Plane,
            (g (x, ξ) * ENNReal.ofReal
              (Real.exp (a * (N x + planeOneNorm ξ)))) ^ p ∂volume ∂μ := by
        apply lintegral_congr
        exact hSweight
      _ = _ := by
        have hfull : Measurable (fun q : X × Plane =>
            (g q * ENNReal.ofReal
              (Real.exp (a * (N q.1 + planeOneNorm q.2)))) ^ p) := by fun_prop
        exact lintegral_lintegral hfull.aemeasurable
  have hpoint (x : X) (y : Y) :
      (∫⁻ ξ : Plane,
        ENNReal.ofReal (heatKernel s (η y - ξ)) * g (x, ξ) ∂volume) ≤
        ENNReal.ofReal (c * s ^ (-1 / p)) * S x := by
    have hexp (ξ : Plane) : 1 ≤ Eξ ξ := by
      dsimp [Eξ]
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (mul_nonneg ha (planeOneNorm_nonneg ξ)))
    have hmono :
        (∫⁻ ξ : Plane,
          ENNReal.ofReal (heatKernel s (η y - ξ)) * g (x, ξ) ∂volume) ≤
        ∫⁻ ξ : Plane,
          ENNReal.ofReal (heatKernel s (η y - ξ)) * Gξ (x, ξ) ∂volume := by
      apply lintegral_mono
      intro ξ
      exact mul_le_mul' le_rfl (by
        dsimp [Gξ]
        calc
          g (x, ξ) ≤ g (x, ξ) * Eξ ξ := by
            calc
              g (x, ξ) = g (x, ξ) * 1 := by simp
              _ ≤ g (x, ξ) * Eξ ξ := mul_le_mul' le_rfl (hexp ξ)
          _ = _ := rfl)
    have hEval' := hEval s hs (η y) (fun ξ => Gξ (x, ξ))
      (hGξ.comp (measurable_const.prodMk measurable_id))
    simpa only [S, Gξ] using hmono.trans hEval'
  have hAction : Measurable (fun q : X × Plane =>
      ∫⁻ y : Y, K q y * f y ∂ν) := measurable_kernelAction ν hK hf
  have hF : Measurable (fun q : (X × Plane) × Y =>
      g q.1 * ENNReal.ofReal (heatKernel s (η q.2 - q.1.2)) *
        R q.1.1 q.2 * f q.2) := by
    have hG : Measurable (fun q : (X × Plane) × Y => g q.1) := hg.comp measurable_fst
    have hH : Measurable (fun q : (X × Plane) × Y =>
        ENNReal.ofReal (heatKernel s (η q.2 - q.1.2))) := by
      exact ((measurable_heatKernel s).comp
        ((hη.comp measurable_snd).sub (measurable_snd.comp measurable_fst))).ennreal_ofReal
    have hR' : Measurable (fun q : (X × Plane) × Y => R q.1.1 q.2) :=
      hR.comp (measurable_fst.fst.prodMk measurable_snd)
    have hff : Measurable (fun q : (X × Plane) × Y => f q.2) := hf.comp measurable_snd
    exact (((hG.mul hH).mul hR').mul hff)
  have hL :
      (∫⁻ q : X × Plane, g q * (∫⁻ y : Y, K q y * f y ∂ν) ∂(μ.prod volume)) =
        ∫⁻ x : X, ∫⁻ ξ : Plane, ∫⁻ y : Y,
          g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ)) *
            R x y * f y ∂ν ∂volume ∂μ := by
    calc
      _ = ∫⁻ q : X × Plane, ∫⁻ y : Y,
            g q * (K q y * f y) ∂ν ∂(μ.prod volume) := by
              apply lintegral_congr
              intro q
              exact (lintegral_const_mul _
                ((hK.comp (measurable_const.prodMk measurable_id)).mul hf)).symm
      _ = ∫⁻ x : X, ∫⁻ ξ : Plane, ∫⁻ y : Y,
            g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ)) *
              R x y * f y ∂ν ∂volume ∂μ := by
              have hInner (q : X × Plane) : Measurable (fun y : Y =>
                  g q * (K q y * f y)) := by
                exact measurable_const.mul
                  ((hK.comp (measurable_const.prodMk measurable_id)).mul hf)
              let J : X × Plane → Y → ℝ≥0∞ := fun q y => g q * (K q y * f y)
              have hJ : Measurable (Function.uncurry J) := by
                exact (hg.comp measurable_fst).mul
                  ((hK.comp (measurable_fst.prodMk measurable_snd)).mul
                    (hf.comp measurable_snd))
              have hA : Measurable (fun q : X × Plane => ∫⁻ y : Y, J q y ∂ν) :=
                hJ.lintegral_prod_right'
              have hAcurried : Measurable (Function.uncurry
                  (fun x : X => fun ξ : Plane => ∫⁻ y : Y, J (x, ξ) y ∂ν)) := by
                change Measurable (fun q : X × Plane => ∫⁻ y : Y, J q y ∂ν)
                exact hA
              have hProd := (lintegral_lintegral (μ := μ)
                (ν := (volume : Measure Plane)) hAcurried.aemeasurable).symm
              simpa [J, K, mul_assoc] using hProd
  have hSwap (x : X) :
      (∫⁻ ξ : Plane, ∫⁻ y : Y,
        g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ)) * R x y * f y ∂ν ∂volume) =
      ∫⁻ y : Y, ∫⁻ ξ : Plane,
        g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ)) * R x y * f y ∂volume ∂ν := by
    apply lintegral_lintegral_swap
    have hSection : Measurable (fun z : Plane × Y =>
        g (x, z.1) * ENNReal.ofReal (heatKernel s (η z.2 - z.1)) *
          R x z.2 * f z.2) := by
      exact hF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    exact hSection.aemeasurable
  have hpointFactor (x : X) (y : Y) :
      (∫⁻ ξ : Plane,
        g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ)) * R x y * f y ∂volume) ≤
      ENNReal.ofReal (c * s ^ (-1 / p)) *
        (S x * (R x y * f y)) := by
    have hHeat : Measurable (fun ξ : Plane =>
        ENNReal.ofReal (heatKernel s (η y - ξ))) := by
      exact ((measurable_heatKernel s).comp
        (measurable_const.sub measurable_id)).ennreal_ofReal
    have hconst : Measurable (fun ξ : Plane =>
        g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ))) :=
      (hg.comp (measurable_const.prodMk measurable_id)).mul hHeat
    have hEq :
        (∫⁻ ξ : Plane,
          g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ)) * R x y * f y ∂volume) =
          (R x y * f y) * (∫⁻ ξ : Plane,
            ENNReal.ofReal (heatKernel s (η y - ξ)) * g (x, ξ) ∂volume) := by
      calc
        _ = ∫⁻ ξ : Plane,
              (R x y * f y) *
                (ENNReal.ofReal (heatKernel s (η y - ξ)) * g (x, ξ)) ∂volume := by
                  apply lintegral_congr
                  intro ξ
                  ac_rfl
        _ = _ := lintegral_const_mul _
          ((hHeat).mul (hg.comp (measurable_const.prodMk measurable_id)))
    rw [hEq]
    calc
      _ ≤ (R x y * f y) *
          (ENNReal.ofReal (c * s ^ (-1 / p)) * S x) := mul_le_mul' le_rfl (hpoint x y)
      _ = _ := by ac_rfl
  have hRpair (x : X) : Measurable (fun y : Y => R x y * f y) :=
    (hR.comp (measurable_const.prodMk measurable_id)).mul hf
  have hRinner : Measurable (fun x : X =>
      S x * ∫⁻ y : Y, R x y * f y ∂ν) := by
    have hRA : Measurable (fun x : X => ∫⁻ y : Y, R x y * f y ∂ν) :=
      (hR.mul (hf.comp measurable_snd)).lintegral_prod_right'
    exact hS.mul hRA
  have hLeftBound :
      (∫⁻ q : X × Plane, g q * (∫⁻ y : Y, K q y * f y ∂ν) ∂(μ.prod volume)) ≤
        ENNReal.ofReal (c * s ^ (-1 / p)) *
          (∫⁻ x : X, S x * (∫⁻ y : Y, R x y * f y ∂ν) ∂μ) := by
    rw [hL]
    calc
      _ = ∫⁻ x : X, ∫⁻ y : Y, ∫⁻ ξ : Plane,
            g (x, ξ) * ENNReal.ofReal (heatKernel s (η y - ξ)) * R x y * f y
              ∂volume ∂ν ∂μ := by
                apply lintegral_congr
                intro x
                exact hSwap x
      _ ≤ ∫⁻ x : X, ∫⁻ y : Y,
            ENNReal.ofReal (c * s ^ (-1 / p)) * (S x * (R x y * f y))
              ∂ν ∂μ := by
                apply lintegral_mono
                intro x
                apply lintegral_mono
                intro y
                exact hpointFactor x y
      _ = ENNReal.ofReal (c * s ^ (-1 / p)) *
            (∫⁻ x : X, S x * (∫⁻ y : Y, R x y * f y ∂ν) ∂μ) := by
                have hInnerEq (x : X) :
                    (∫⁻ y : Y, ENNReal.ofReal (c * s ^ (-1 / p)) *
                        (S x * (R x y * f y)) ∂ν) =
                      ENNReal.ofReal (c * s ^ (-1 / p)) *
                        (S x * ∫⁻ y : Y, R x y * f y ∂ν) := by
                  calc
                    _ = ENNReal.ofReal (c * s ^ (-1 / p)) *
                          (∫⁻ y : Y, S x * (R x y * f y) ∂ν) :=
                            lintegral_const_mul _ (measurable_const.mul (hRpair x))
                    _ = _ := by
                          rw [lintegral_const_mul _ (hRpair x)]
                calc
                  _ = ∫⁻ x : X, ENNReal.ofReal (c * s ^ (-1 / p)) *
                        (S x * ∫⁻ y : Y, R x y * f y ∂ν) ∂μ := by
                          apply lintegral_congr
                          exact hInnerEq
                  _ = _ := lintegral_const_mul _ hRinner
  have hbound' := hbound f S hf hS
  have hNormS :
      (∫⁻ x : X, (S x * ENNReal.ofReal (Real.exp (a * N x))) ^ p ∂μ) ^ (1 / p : ℝ) =
        (∫⁻ q : X × Plane,
          (g q * ENNReal.ofReal
            (Real.exp (a * (N q.1 + planeOneNorm q.2)))) ^ p ∂μ.prod volume) ^ (1 / p : ℝ) :=
    congrArg (fun z : ℝ≥0∞ => z ^ (1 / p : ℝ)) hNormEq
  calc
    _ ≤ ENNReal.ofReal (c * s ^ (-1 / p)) *
        (∫⁻ x : X, S x * (∫⁻ y : Y, R x y * f y ∂ν) ∂μ) := hLeftBound
    _ ≤ ENNReal.ofReal (c * s ^ (-1 / p)) *
        (d * (∫⁻ y : Y, (f y * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ (2 : ℝ) ∂ν) ^
              (1 / 2 : ℝ) *
          (∫⁻ x : X, (S x * ENNReal.ofReal (Real.exp (a * N x))) ^ p ∂μ) ^
              (1 / p : ℝ)) := by
          exact mul_le_mul' le_rfl (by
            simpa only [Real.exp_zero, ENNReal.ofReal_one, mul_one, WeightedFormBound] using hbound')
    _ = (d * ENNReal.ofReal (c * s ^ (-1 / p))) *
          (∫⁻ y : Y,
            (f y * ENNReal.ofReal (Real.exp ((fun _ : Y => 0) y))) ^ (2 : ℝ) ∂ν) ^
              (1 / 2 : ℝ) *
          (∫⁻ q : X × Plane,
            (g q * ENNReal.ofReal
              (Real.exp ((fun q : X × Plane => a * (N q.1 + planeOneNorm q.2)) q))) ^ p ∂μ.prod volume) ^
              (1 / p : ℝ) := by
          rw [hNormS]
          simp [Real.exp_zero, ENNReal.ofReal_one, mul_one,
            mul_assoc, mul_left_comm]


end Critical2DKPZ.SHF.Tsai

end
