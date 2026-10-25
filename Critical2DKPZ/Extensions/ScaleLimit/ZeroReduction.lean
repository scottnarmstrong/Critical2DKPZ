/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BrownianZeroPadding
public import Critical2DKPZ.Extensions.Definitions.ScaledPairing
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
import Critical2DKPZ.Extensions.ScaleLimit.FiniteProbability
import Critical2DKPZ.Extensions.ScaleLimit.LimitLawTransfer
import Critical2DKPZ.Extensions.ScaleLimit.SlutskyTools
import Critical2DKPZ.Extensions.ScaleLimit.ArrayMoments
import Critical2DKPZ.Extensions.ScaleLimit.Centring
import Mathlib.Tactic

/-! # The zero scale-time coordinate and finite-dimensional zero padding -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A zero coordinate vanishing in probability can be added to the positive
finite-dimensional Brownian limit. -/
theorem tendstoInDistribution_of_drop_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Set.Ioi (0 : ℝ) → Ω → ℝ≥0 → ℝ)
    (hm : ∀ L s, AEMeasurable (fun ω => X L ω s) P)
    (hzero : TendstoInMeasure P (fun L ω => X L ω 0) atTop (fun _ => 0))
    (I : Finset ℝ≥0)
    (hpos : TendstoInDistribution (fun L ω (i : I.erase 0) => X L ω i.val)
      atTop id (fun _ => P) (BrownianReal.projectiveFamily (I.erase 0))) :
    TendstoInDistribution (fun L ω (i : I) => X L ω i.val) atTop id
      (fun _ => P) (BrownianReal.projectiveFamily I) := by
  classical
  let Y : Set.Ioi (0 : ℝ) → Ω → I → ℝ := fun L ω => padZero I (fun i => X L ω i.val)
  have hpad := hpos.continuous_comp (continuous_padZero I)
  have hmap : (BrownianReal.projectiveFamily (I.erase 0)).map ((padZero I) ∘ id) =
      (BrownianReal.projectiveFamily I).map id := by
    simpa only [Function.comp_id, Measure.map_id] using map_padZero_projectiveFamily I
  have hpad' : TendstoInDistribution Y atTop id (fun _ => P) (BrownianReal.projectiveFamily I) := by
    have h := tendstoInDistribution_of_limit_map_eq hpad aemeasurable_id hmap
    simpa only [Y, Function.comp_def] using h
  have hdif : TendstoInMeasure P (fun L ω (i : I) => X L ω i.val - Y L ω i) atTop (fun _ => 0) := by
    apply tendstoInMeasure_finite_pi P atTop _ (fun _ _ => 0)
    intro i
    by_cases hi : i.val = 0
    · simpa [Y, padZero, hi] using hzero
    · have hz := tendstoInMeasure_const_of_tendsto P
        (tendsto_const_nhds : Tendsto (fun _ : Set.Ioi (0 : ℝ) => (0 : ℝ)) atTop (𝓝 0))
      simpa [Y, padZero, hi] using hz
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hpad' _
    (fun L => aemeasurable_pi_iff.mpr (fun i => hm L i.val))
  change TendstoInMeasure P (fun L ω (i : I) => X L ω i.val - Y L ω i) atTop (fun _ => 0)
  exact hdif

/-- Every scaled KPZ pairing is square integrable at every scale. -/
theorem memLp_scaledPairing_two (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (φ : TestFn) (x : Plane) (L : Set.Ioi (0 : ℝ)) (s : ℝ) :
    MemLp (fun ω => scaledPairing (H t 0 ω) φ x L s) 2 P := by
  have h : MemLp (fun ω => (Real.sqrt L)⁻¹ * H t 0 ω (φ.dilate (scaleRadius L s) x)) 2 P :=
    (memLp_kpz_two ϑ P Z hZ H hH t ht _).const_mul _
  simpa only [scaledPairing, div_eq_mul_inv, mul_comm] using h

/-- The zero scale-time coordinate converges to zero in second moment. -/
theorem tendsto_second_moment_scaledPairing_zero (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (_hH : IsCriticalKPZ P Z H)
    {t : ℝ} (_ht : 0 < t) (φ : TestFn) (x : Plane) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω, (scaledPairing (H t 0 ω) φ x L 0) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ ω, (H t 0 ω (φ.dilate (Real.exp (-1)) x)) ^ 2 ∂P
  have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hh : Tendsto (fun L : Set.Ioi (0 : ℝ) => M / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  apply hh.congr
  intro L
  simp only [scaledPairing, scaleRadius, mul_zero, Real.exp_zero, div_pow, integral_div,
    Real.sq_sqrt L.property.le, M]

/-- In particular the zero scale-time coordinate vanishes in probability. -/
theorem tendstoInMeasure_scaledPairing_zero (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (φ : TestFn) (x : Plane) :
    TendstoInMeasure P (fun L : Set.Ioi (0 : ℝ) => fun ω => scaledPairing (H t 0 ω) φ x L 0)
      atTop (fun _ => 0) :=
  tendstoInMeasure_zero_of_integral_sq P atTop _
    (fun L => memLp_scaledPairing_two ϑ P Z hZ H hH ht φ x L 0)
    (tendsto_second_moment_scaledPairing_zero ϑ P Z hZ H hH ht φ x)

end Critical2DKPZ.Extensions.ScaleLimit
