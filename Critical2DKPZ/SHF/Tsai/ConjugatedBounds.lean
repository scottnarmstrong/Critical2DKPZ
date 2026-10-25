/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadTail
public import Critical2DKPZ.SHF.Flow.WeightMeasurability
public import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
import Mathlib.Tactic

/-! # Conjugated weighted bounds for the delta-Bose heat kernels -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Conjugate an unweighted bilinear kernel estimate by measurable endpoint weights. -/
theorem WeightedFormBound.conjugate {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ}
    {K Kbar : X → Y → ℝ≥0∞} {c : ℝ≥0∞}
    (hwX : Measurable wX) (hwY : Measurable wY)
    (hKbar : Measurable (Function.uncurry Kbar))
    (h : WeightedFormBound μ ν (fun _ => 0) (fun _ => 0) p p' Kbar c)
    (hrel : ∀ x y, K x y = Kbar x y * ENNReal.ofReal (Real.exp (wX x)) *
      ENNReal.ofReal (Real.exp (wY y))) :
    WeightedFormBound μ ν wX wY p p' K c := by
  intro f g hf hg
  let f' : Y → ℝ≥0∞ := fun y => f y * ENNReal.ofReal (Real.exp (wY y))
  let g' : X → ℝ≥0∞ := fun x => g x * ENNReal.ofReal (Real.exp (wX x))
  have hf' : Measurable f' := by
    dsimp [f']
    exact hf.mul (hwY.exp.ennreal_ofReal)
  have hg' : Measurable g' := by
    dsimp [g']
    exact hg.mul (hwX.exp.ennreal_ofReal)
  have hKsec (x : X) : Measurable (Kbar x) :=
    hKbar.comp (measurable_const.prodMk measurable_id)
  have hAction (x : X) :
      (∫⁻ y, K x y * f y ∂ν) =
        ENNReal.ofReal (Real.exp (wX x)) * (∫⁻ y, Kbar x y * f' y ∂ν) := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal (Real.exp (wX x)) * (Kbar x y * f' y) ∂ν := by
        apply lintegral_congr
        intro y
        rw [hrel x y]
        dsimp [f']
        ac_rfl
      _ = _ := lintegral_const_mul _ ((hKsec x).mul hf')
  calc
    (∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ) =
        ∫⁻ x, g' x * (∫⁻ y, Kbar x y * f' y ∂ν) ∂μ := by
          apply lintegral_congr
          intro x
          rw [hAction x]
          dsimp [g']
          ac_rfl
    _ ≤ c * (∫⁻ y, f' y ^ p ∂ν) ^ (1 / p) *
          (∫⁻ x, g' x ^ p' ∂μ) ^ (1 / p') := by
            simpa [WeightedFormBound, f', g', Real.exp_zero, ENNReal.ofReal_one,
              mul_assoc] using
              h f' g' hf' hg'

/-- The incoming kernel has a conjugated weighted `Lᵖ` form bound `c e^{ct} t^{-1/p}`, with opposite endpoint weight signs, as in Tsai (2024), equation (2.9a). -/
theorem weightedFormBound_incoming_conj {n : ℕ} (α : CollisionPair n) {p a : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
      WeightedFormBound volume volume (fun z => -(a * fusedOneNorm α z))
        (fun x => a * configurationOneNorm x) p (p / (p - 1))
        (fun z x => ENNReal.ofReal (incomingKernel α t z x))
        (ENNReal.ofReal (c * Real.exp (c * t) * t ^ (-1 / p))) := by
  obtain ⟨c₀, hc₀, hbase⟩ := weightedFormBound_incoming_unweighted α hp
  let c : ℝ := c₀ * 2 ^ n + 2 * n * a ^ 2 + 1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, fun t ht => ?_⟩
  let K : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α t z x)
  let K₂ : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α (2 * t) z x)
  let Kbar : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α t z x *
      Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)))
  have hwX : Measurable (fun z : FusedConfiguration α => -(a * fusedOneNorm α z)) := by
    exact (measurable_const.mul (measurable_fusedOneNorm α)).neg
  have hwY : Measurable (fun x : Configuration n => a * configurationOneNorm x) :=
    measurable_const.mul (measurable_configurationOneNorm n)
  have hK₂ : Measurable (Function.uncurry K₂) := by
    dsimp [K₂]
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hKbar : Measurable (Function.uncurry Kbar) := by
    dsimp [Kbar]
    have hIn : Measurable (fun z : FusedConfiguration α × Configuration n =>
        incomingKernel α t z.1 z.2) :=
      measurable_incomingKernel α |>.comp (measurable_const.prodMk measurable_id)
    have hweight : Measurable (fun z : FusedConfiguration α × Configuration n =>
        a * (fusedOneNorm α z.1 - configurationOneNorm z.2)) := by
      exact measurable_const.mul
        (((measurable_fusedOneNorm α).comp measurable_fst).sub
          ((measurable_configurationOneNorm n).comp measurable_snd))
    exact (hIn.mul hweight.exp).ennreal_ofReal
  have hrel (z : FusedConfiguration α) (x : Configuration n) :
      K z x = Kbar z x * ENNReal.ofReal
        (Real.exp (-(a * fusedOneNorm α z))) * ENNReal.ofReal
        (Real.exp (a * configurationOneNorm x)) := by
    dsimp [K, Kbar]
    have hexp : Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) *
        Real.exp (-(a * fusedOneNorm α z)) *
        Real.exp (a * configurationOneNorm x) = 1 := by
      calc
        _ = Real.exp (a * (fusedOneNorm α z - configurationOneNorm x) +
              -(a * fusedOneNorm α z)) * Real.exp (a * configurationOneNorm x) := by
                rw [← Real.exp_add]
        _ = Real.exp (a * (fusedOneNorm α z - configurationOneNorm x) +
              -(a * fusedOneNorm α z) + a * configurationOneNorm x) := by
                rw [← Real.exp_add]
        _ = 1 := by
              rw [show a * (fusedOneNorm α z - configurationOneNorm x) +
                -(a * fusedOneNorm α z) + a * configurationOneNorm x = 0 by ring,
                Real.exp_zero]
    have hI : 0 ≤ incomingKernel α t z x := (incomingKernel_pos α ht z x).le
    have hreal : incomingKernel α t z x =
        ((incomingKernel α t z x * Real.exp
          (a * (fusedOneNorm α z - configurationOneNorm x))) *
          Real.exp (-(a * fusedOneNorm α z))) * Real.exp (a * configurationOneNorm x) := by
      calc
        _ = incomingKernel α t z x *
              (Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) *
                Real.exp (-(a * fusedOneNorm α z)) *
                Real.exp (a * configurationOneNorm x)) := by rw [hexp]; ring
        _ = _ := by ring
    have hfactor : ENNReal.ofReal
        (((incomingKernel α t z x * Real.exp
          (a * (fusedOneNorm α z - configurationOneNorm x))) *
          Real.exp (-(a * fusedOneNorm α z))) * Real.exp (a * configurationOneNorm x)) =
          ENNReal.ofReal (incomingKernel α t z x *
            Real.exp (a * (fusedOneNorm α z - configurationOneNorm x))) *
            ENNReal.ofReal (Real.exp (-(a * fusedOneNorm α z))) *
            ENNReal.ofReal (Real.exp (a * configurationOneNorm x)) := by
      have hA : 0 ≤ incomingKernel α t z x *
          Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) :=
        mul_nonneg hI (Real.exp_pos _).le
      have hAB : 0 ≤ incomingKernel α t z x *
          Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) *
          Real.exp (-(a * fusedOneNorm α z)) :=
        mul_nonneg hA (Real.exp_pos _).le
      have hAB_mul :
          ENNReal.ofReal (incomingKernel α t z x *
            Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) *
            Real.exp (-(a * fusedOneNorm α z))) *
            ENNReal.ofReal (Real.exp (a * configurationOneNorm x)) =
          ENNReal.ofReal ((incomingKernel α t z x *
            Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) *
            Real.exp (-(a * fusedOneNorm α z))) *
            Real.exp (a * configurationOneNorm x)) := (ENNReal.ofReal_mul hAB).symm
      have hA_mul :
          ENNReal.ofReal (incomingKernel α t z x *
            Real.exp (a * (fusedOneNorm α z - configurationOneNorm x))) *
            ENNReal.ofReal (Real.exp (-(a * fusedOneNorm α z))) =
          ENNReal.ofReal (incomingKernel α t z x *
            Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) *
            Real.exp (-(a * fusedOneNorm α z))) := (ENNReal.ofReal_mul hA).symm
      calc
        _ = ENNReal.ofReal (incomingKernel α t z x *
              Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) *
              Real.exp (-(a * fusedOneNorm α z))) *
              ENNReal.ofReal (Real.exp (a * configurationOneNorm x)) := hAB_mul.symm
        _ = _ := by rw [hA_mul]
    calc
      _ = ENNReal.ofReal
          (((incomingKernel α t z x * Real.exp
            (a * (fusedOneNorm α z - configurationOneNorm x))) *
            Real.exp (-(a * fusedOneNorm α z))) * Real.exp (a * configurationOneNorm x)) :=
              congrArg ENNReal.ofReal hreal
      _ = _ := hfactor
  have hdom (z : FusedConfiguration α) (x : Configuration n) :
      Kbar z x ≤ ENNReal.ofReal (weightGrowth n a t) * K₂ z x := by
    dsimp [Kbar, K₂]
    rw [← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    exact ENNReal.ofReal_le_ofReal (incomingKernel_mul_exp_weight_le α ha ht z x)
  have hbar : WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
      (fun _ : Configuration n => 0) p (p / (p - 1)) Kbar
      (ENNReal.ofReal (weightGrowth n a t) * ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / p))) := by
    intro f g hf hg
    have hAction₂ : Measurable (fun z : FusedConfiguration α =>
        ∫⁻ x : Configuration n, K₂ z x * f x) := measurable_kernelAction volume hK₂ hf
    have hInner (z : FusedConfiguration α) :
        (∫⁻ x : Configuration n, Kbar z x * f x) ≤
          ENNReal.ofReal (weightGrowth n a t) *
            (∫⁻ x : Configuration n, K₂ z x * f x) := by
      calc
        _ ≤ ∫⁻ x : Configuration n,
            ENNReal.ofReal (weightGrowth n a t) * (K₂ z x * f x) := by
              apply lintegral_mono
              intro x
              calc
                Kbar z x * f x ≤
                    (ENNReal.ofReal (weightGrowth n a t) * K₂ z x) * f x :=
                      mul_le_mul' (hdom z x) le_rfl
                _ = ENNReal.ofReal (weightGrowth n a t) * (K₂ z x * f x) := by ac_rfl
        _ = _ := lintegral_const_mul _
          ((hK₂.comp (measurable_const.prodMk measurable_id)).mul hf)
    calc
      _ ≤ ∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (weightGrowth n a t) *
            (g z * (∫⁻ x : Configuration n, K₂ z x * f x)) := by
              apply lintegral_mono
              intro z
              calc
                g z * (∫⁻ x, Kbar z x * f x) ≤
                    g z * (ENNReal.ofReal (weightGrowth n a t) *
                      (∫⁻ x, K₂ z x * f x)) := mul_le_mul' le_rfl (hInner z)
                _ = _ := by ac_rfl
      _ = ENNReal.ofReal (weightGrowth n a t) *
            (∫⁻ z : FusedConfiguration α,
              g z * (∫⁻ x : Configuration n, K₂ z x * f x)) :=
              lintegral_const_mul _ (hg.mul hAction₂)
      _ ≤ ENNReal.ofReal (weightGrowth n a t) *
            ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / p)) *
              (∫⁻ x : Configuration n,
                (f x * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p ∂volume) ^ (1 / p) *
              (∫⁻ z : FusedConfiguration α,
                (g z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ (p / (p - 1)) ∂volume) ^
                (1 / (p / (p - 1))) := by
              have hscaled := hbase (2 * t) (by positivity) f g hf hg
              change (∫⁻ z : FusedConfiguration α,
                  g z * (∫⁻ x : Configuration n, K₂ z x * f x)) ≤
                ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / p)) *
                  (∫⁻ x : Configuration n,
                    (f x * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p ∂volume) ^ (1 / p) *
                  (∫⁻ z : FusedConfiguration α,
                    (g z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ (p / (p - 1)) ∂volume) ^
                    (1 / (p / (p - 1))) at hscaled
              calc
                _ ≤ ENNReal.ofReal (weightGrowth n a t) *
                    (ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / p)) *
                      (∫⁻ x : Configuration n,
                        (f x * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p ∂volume) ^ (1 / p) *
                      (∫⁻ z : FusedConfiguration α,
                        (g z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ (p / (p - 1)) ∂volume) ^
                        (1 / (p / (p - 1)))) := mul_le_mul' le_rfl hscaled
                _ = ENNReal.ofReal (weightGrowth n a t) *
                    ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / p)) *
                      (∫⁻ x : Configuration n,
                        (f x * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p ∂volume) ^ (1 / p) *
                      (∫⁻ z : FusedConfiguration α,
                        (g z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ (p / (p - 1)) ∂volume) ^
                        (1 / (p / (p - 1))) := by ac_rfl
  /- A larger constant controls both the prefactor and the exponential growth rate. -/
  have hbar' := WeightedFormBound.conjugate hwX hwY hKbar hbar hrel
  have hcoef : weightGrowth n a t * (c₀ * (2 * t) ^ (-1 / p)) ≤
      c * Real.exp (c * t) * t ^ (-1 / p) := by
    have hpneg : -1 / p ≤ 0 := by
      have hp0 : 0 < p := lt_trans zero_lt_one hp
      rw [neg_div]
      exact neg_nonpos.mpr (le_of_lt (one_div_pos.mpr hp0))
    have htime : (2 * t) ^ (-1 / p) ≤ t ^ (-1 / p) := by
      exact Real.rpow_le_rpow_of_nonpos ht (by nlinarith) hpneg
    have hgrowth : 2 * (n : ℝ) * a ^ 2 ≤ c := by
      dsimp [c]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hc₀.le (show 0 ≤ (2 : ℝ) ^ n by positivity)]
    have hexp : Real.exp (2 * (n : ℝ) * a ^ 2 * t) ≤ Real.exp (c * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hgrowth ht.le)
    have hcoef0 : c₀ * 2 ^ n ≤ c := by dsimp [c]; nlinarith
    have htp : 0 ≤ t ^ (-1 / p) := Real.rpow_nonneg ht.le _
    unfold weightGrowth
    calc
      2 ^ n * Real.exp (2 * n * a ^ 2 * t) * (c₀ * (2 * t) ^ (-1 / p)) =
          2 ^ n * Real.exp (2 * n * a ^ 2 * t) * c₀ * (2 * t) ^ (-1 / p) := by ring
      _ ≤ 2 ^ n * Real.exp (2 * n * a ^ 2 * t) * c₀ * t ^ (-1 / p) := by
            gcongr
      _ ≤ 2 ^ n * Real.exp (c * t) * c₀ * t ^ (-1 / p) := by
            gcongr
      _ = (c₀ * 2 ^ n) * Real.exp (c * t) * t ^ (-1 / p) := by ring
      _ ≤ c * Real.exp (c * t) * t ^ (-1 / p) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef0 (Real.exp_nonneg _)) htp
  have hcoefENN : ENNReal.ofReal (weightGrowth n a t) *
      ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / p)) ≤
        ENNReal.ofReal (c * Real.exp (c * t) * t ^ (-1 / p)) := by
    rw [← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    exact ENNReal.ofReal_le_ofReal hcoef
  refine hbar'.mono ?_ hcoefENN
  intro z x
  exact le_rfl

/-- The outgoing kernel has a conjugated weighted `Lᵖ` form bound `c e^{ct} t^{-(p-1)/p}`, as in Tsai (2024), equation (2.9a). -/
theorem weightedFormBound_outgoing_conj {n : ℕ} (α : CollisionPair n) {p a : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
      WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
        (fun z => a * fusedOneNorm α z) p (p / (p - 1))
        (fun x z => ENNReal.ofReal (incomingKernel α t z x))
        (ENNReal.ofReal (c * Real.exp (c * t) * t ^ (-(p - 1) / p))) := by
  let q : ℝ := p / (p - 1)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 1 < q := by
    dsimp [q]
    rw [lt_div_iff₀ (by linarith : 0 < p - 1)]
    nlinarith
  have hqdual : q / (q - 1) = p := by
    dsimp [q]
    field_simp [show p - 1 ≠ 0 by linarith]
    ring
  obtain ⟨c₀, hc₀, hbase⟩ := weightedFormBound_incoming_unweighted α hq
  let c : ℝ := c₀ * 2 ^ n + 2 * n * a ^ 2 + 1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, fun t ht => ?_⟩
  let K : Configuration n → FusedConfiguration α → ℝ≥0∞ := fun x z =>
    ENNReal.ofReal (incomingKernel α t z x)
  let K₂ : Configuration n → FusedConfiguration α → ℝ≥0∞ := fun x z =>
    ENNReal.ofReal (incomingKernel α (2 * t) z x)
  let Kbar : Configuration n → FusedConfiguration α → ℝ≥0∞ := fun x z =>
    ENNReal.ofReal (incomingKernel α t z x *
      Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)))
  have hwX : Measurable (fun x : Configuration n => -(a * configurationOneNorm x)) :=
    (measurable_const.mul (measurable_configurationOneNorm n)).neg
  have hwY : Measurable (fun z : FusedConfiguration α => a * fusedOneNorm α z) :=
    measurable_const.mul (measurable_fusedOneNorm α)
  have hK₂base : Measurable (Function.uncurry (fun z : FusedConfiguration α => fun x : Configuration n =>
      ENNReal.ofReal (incomingKernel α (2 * t) z x))) := by
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hK₂ : Measurable (Function.uncurry K₂) := by
    change Measurable (fun p : Configuration n × FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α (2 * t) p.2 p.1))
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))).ennreal_ofReal
  have hKbar : Measurable (Function.uncurry Kbar) := by
    dsimp [Kbar]
    have hIn : Measurable (fun p : Configuration n × FusedConfiguration α =>
        incomingKernel α t p.2 p.1) :=
      measurable_incomingKernel α |>.comp
        (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
    have hweight : Measurable (fun p : Configuration n × FusedConfiguration α =>
        a * (configurationOneNorm p.1 - fusedOneNorm α p.2)) := by
      exact measurable_const.mul
        ((measurable_configurationOneNorm n).comp measurable_fst |>.sub
          ((measurable_fusedOneNorm α).comp measurable_snd))
    exact (hIn.mul hweight.exp).ennreal_ofReal
  have hrel (x : Configuration n) (z : FusedConfiguration α) :
      K x z = Kbar x z * ENNReal.ofReal (Real.exp (-(a * configurationOneNorm x))) *
        ENNReal.ofReal (Real.exp (a * fusedOneNorm α z)) := by
    dsimp [K, Kbar]
    have hexp : Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
        Real.exp (-(a * configurationOneNorm x)) *
        Real.exp (a * fusedOneNorm α z) = 1 := by
      calc
        _ = Real.exp (a * (configurationOneNorm x - fusedOneNorm α z) +
              -(a * configurationOneNorm x)) * Real.exp (a * fusedOneNorm α z) := by
                rw [← Real.exp_add]
        _ = Real.exp (a * (configurationOneNorm x - fusedOneNorm α z) +
              -(a * configurationOneNorm x) + a * fusedOneNorm α z) := by
                rw [← Real.exp_add]
        _ = 1 := by
              rw [show a * (configurationOneNorm x - fusedOneNorm α z) +
                -(a * configurationOneNorm x) + a * fusedOneNorm α z = 0 by ring,
                Real.exp_zero]
    have hI : 0 ≤ incomingKernel α t z x := (incomingKernel_pos α ht z x).le
    have hreal : incomingKernel α t z x =
        incomingKernel α t z x * Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
          Real.exp (-(a * configurationOneNorm x)) * Real.exp (a * fusedOneNorm α z) := by
      calc
        _ = incomingKernel α t z x *
              (Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
                Real.exp (-(a * configurationOneNorm x)) * Real.exp (a * fusedOneNorm α z)) := by
                rw [hexp]
                ring
        _ = _ := by ring
    have hA : 0 ≤ incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) :=
      mul_nonneg hI (Real.exp_pos _).le
    have hAB : 0 ≤ incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
        Real.exp (-(a * configurationOneNorm x)) := mul_nonneg hA (Real.exp_pos _).le
    have hABmul : ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
        Real.exp (-(a * configurationOneNorm x))) *
        ENNReal.ofReal (Real.exp (a * fusedOneNorm α z)) =
      ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
        Real.exp (-(a * configurationOneNorm x)) * Real.exp (a * fusedOneNorm α z)) :=
          (ENNReal.ofReal_mul hAB).symm
    have hAmul : ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z))) *
        ENNReal.ofReal (Real.exp (-(a * configurationOneNorm x))) =
      ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
        Real.exp (-(a * configurationOneNorm x))) := (ENNReal.ofReal_mul hA).symm
    calc
      _ = ENNReal.ofReal (incomingKernel α t z x *
          Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) *
          Real.exp (-(a * configurationOneNorm x)) * Real.exp (a * fusedOneNorm α z)) :=
            congrArg ENNReal.ofReal hreal
      _ = _ := by rw [hABmul.symm, hAmul.symm]
  have hdom (x : Configuration n) (z : FusedConfiguration α) :
      Kbar x z ≤ ENNReal.ofReal (weightGrowth n a t) * K₂ x z := by
    dsimp [Kbar, K₂]
    have hfree := freeKernel_mul_exp_weight_le n ha ht x (collisionEmbedding α z)
    have hreal : incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) ≤
        weightGrowth n a t * incomingKernel α (2 * t) z x := by
      simpa only [incomingKernel, configurationOneNorm_collisionEmbedding, weightGrowth] using hfree
    rw [← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    exact ENNReal.ofReal_le_ofReal hreal
  have hgrowth : 1 ≤ weightGrowth n a t := by
    unfold weightGrowth
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hexpOne : (1 : ℝ) ≤ Real.exp (2 * n * a ^ 2 * t) :=
      Real.one_le_exp (by positivity)
    calc
      1 = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ n * Real.exp (2 * n * a ^ 2 * t) :=
        mul_le_mul htwo hexpOne (by norm_num) (by norm_num)
  have hbase₂ := hbase (2 * t) (by positivity)
  have hbaseT := WeightedFormBound.transpose hK₂base hbase₂
  rw [hqdual] at hbaseT
  have hbaseC : WeightedFormBound volume volume (fun _ : Configuration n => 0)
      (fun _ : FusedConfiguration α => 0) p q K₂
      (ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / q))) := by
    simpa only [K₂, Real.exp_zero, ENNReal.ofReal_one, mul_one] using hbaseT
  have hbar : WeightedFormBound volume volume (fun _ : Configuration n => 0)
      (fun _ : FusedConfiguration α => 0) p q Kbar
      (ENNReal.ofReal (weightGrowth n a t) *
        ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / q))) := by
    intro f g hf hg
    have hAction₂ : Measurable (fun x : Configuration n =>
        ∫⁻ z : FusedConfiguration α, K₂ x z * f z) :=
      measurable_kernelAction volume hK₂ hf
    have hInner (x : Configuration n) :
        (∫⁻ z : FusedConfiguration α, Kbar x z * f z) ≤
          ENNReal.ofReal (weightGrowth n a t) *
            (∫⁻ z : FusedConfiguration α, K₂ x z * f z) := by
      calc
        _ ≤ ∫⁻ z : FusedConfiguration α,
            ENNReal.ofReal (weightGrowth n a t) * (K₂ x z * f z) := by
              apply lintegral_mono
              intro z
              calc
                Kbar x z * f z ≤
                    (ENNReal.ofReal (weightGrowth n a t) * K₂ x z) * f z :=
                      mul_le_mul' (hdom x z) le_rfl
                _ = _ := by ac_rfl
        _ = _ := lintegral_const_mul _ (hK₂.comp (measurable_const.prodMk measurable_id) |>.mul hf)
    calc
      _ ≤ ∫⁻ x : Configuration n,
          ENNReal.ofReal (weightGrowth n a t) *
            (g x * (∫⁻ z : FusedConfiguration α, K₂ x z * f z)) := by
              apply lintegral_mono
              intro x
              calc
                g x * (∫⁻ z, Kbar x z * f z) ≤
                    g x * (ENNReal.ofReal (weightGrowth n a t) *
                      (∫⁻ z, K₂ x z * f z)) := mul_le_mul' le_rfl (hInner x)
                _ = _ := by ac_rfl
      _ = ENNReal.ofReal (weightGrowth n a t) *
            (∫⁻ x : Configuration n,
              g x * (∫⁻ z : FusedConfiguration α, K₂ x z * f z)) :=
              lintegral_const_mul _ (hg.mul hAction₂)
      _ ≤ ENNReal.ofReal (weightGrowth n a t) *
            (ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / q)) *
              (∫⁻ z : FusedConfiguration α,
                (f z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p ∂volume) ^ (1 / p) *
              (∫⁻ x : Configuration n,
                (g x * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ q ∂volume) ^ (1 / q)) := by
              have htest := hbaseC f g hf hg
              change (∫⁻ x : Configuration n,
                  g x * (∫⁻ z : FusedConfiguration α, K₂ x z * f z)) ≤
                ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / q)) *
                  (∫⁻ z : FusedConfiguration α,
                    (f z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p ∂volume) ^ (1 / p) *
                  (∫⁻ x : Configuration n,
                    (g x * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ q ∂volume) ^ (1 / q) at htest
              exact mul_le_mul' le_rfl htest
      _ = ENNReal.ofReal (weightGrowth n a t) *
            ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / q)) *
              (∫⁻ z : FusedConfiguration α,
                (f z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p ∂volume) ^ (1 / p) *
              (∫⁻ x : Configuration n,
                (g x * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ q ∂volume) ^ (1 / q) := by ac_rfl
  have hbar' := WeightedFormBound.conjugate hwX hwY hKbar hbar hrel
  let qexp : ℝ := -(p - 1) / p
  have hqexp : -1 / q = qexp := by
    dsimp [qexp, q]
    field_simp
  have hqneg : qexp ≤ 0 := by
    dsimp [qexp]
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg (sub_nonneg.mpr hp.le) hp0.le)
  have htime : (2 * t) ^ (-1 / q) ≤ t ^ qexp := by
    rw [hqexp]
    calc
      (2 * t) ^ qexp ≤ t ^ qexp :=
        Real.rpow_le_rpow_of_nonpos ht (by nlinarith) hqneg
      _ = t ^ qexp := rfl
  have hcoefGrowth : 2 * (n : ℝ) * a ^ 2 ≤ c := by
    dsimp [c]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hc₀.le (show 0 ≤ (2 : ℝ) ^ n by positivity)]
  have hexp : Real.exp (2 * (n : ℝ) * a ^ 2 * t) ≤ Real.exp (c * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcoefGrowth ht.le)
  have hcoef0 : c₀ * 2 ^ n ≤ c := by dsimp [c]; nlinarith
  have htp : 0 ≤ t ^ qexp := Real.rpow_nonneg ht.le _
  have hcoef : weightGrowth n a t * (c₀ * (2 * t) ^ (-1 / q)) ≤
      c * Real.exp (c * t) * t ^ qexp := by
    unfold weightGrowth
    calc
      2 ^ n * Real.exp (2 * n * a ^ 2 * t) * (c₀ * (2 * t) ^ (-1 / q)) =
          2 ^ n * Real.exp (2 * n * a ^ 2 * t) * c₀ * (2 * t) ^ (-1 / q) := by ring
      _ ≤ 2 ^ n * Real.exp (2 * n * a ^ 2 * t) * c₀ * t ^ qexp := by gcongr
      _ ≤ 2 ^ n * Real.exp (c * t) * c₀ * t ^ qexp := by gcongr
      _ = (c₀ * 2 ^ n) * Real.exp (c * t) * t ^ qexp := by ring
      _ ≤ c * Real.exp (c * t) * t ^ qexp := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef0 (Real.exp_nonneg _)) htp
  have hcoefENN : ENNReal.ofReal (weightGrowth n a t) *
      ENNReal.ofReal (c₀ * (2 * t) ^ (-1 / q)) ≤
      ENNReal.ofReal (c * Real.exp (c * t) * t ^ qexp) := by
    rw [← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    exact ENNReal.ofReal_le_ofReal hcoef
  exact hbar'.mono (fun _ _ => le_rfl) hcoefENN

end Critical2DKPZ.SHF.Tsai

end
