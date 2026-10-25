/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Assembly.LatticeCentring
public import Critical2DKPZ.LocalSobolev.LatticeReversalPointwiseL1
public import Critical2DKPZ.LocalSobolev.DistributionValuedLimits
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Exact reversal errors along moving even clocks -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.LocalSobolev

private theorem tested_eLpNorm_one_le_clockError (E : Plane → Disorder → ℝ)
    (φ : TestFn) (B : ℝ) (hm : Measurable (Function.uncurry E))
    (hi : ∀ x, Integrable (E x) disorderLaw)
    (hb : ∀ x, (∫ ω, |E x ω| ∂disorderLaw) ≤ B) :
    eLpNorm (fun ω => ∫ x, φ x * E x ω) 1 disorderLaw ≤
      ENNReal.ofReal ((∫ x, |φ x|) * B) := by
  let F : Plane × Disorder → ℝ := fun p => φ p.1 * E p.1 p.2
  have hF : Measurable F := (φ.continuous.measurable.comp measurable_fst).mul hm
  have hφ : Integrable (fun x => |φ x|) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).abs
  have hs (x : Plane) : Integrable (fun ω => F (x, ω)) disorderLaw :=
    (hi x).const_mul (φ x)
  have hmean (x : Plane) : (∫ ω, ‖F (x, ω)‖ ∂disorderLaw) =
      |φ x| * ∫ ω, |E x ω| ∂disorderLaw := by
    simp only [F, Real.norm_eq_abs, abs_mul, integral_const_mul]
  have hmajor (x : Plane) : ‖∫ ω, ‖F (x, ω)‖ ∂disorderLaw‖ ≤ |φ x| * B := by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hmean]
    exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  have hmarg : Integrable (fun x => ∫ ω, ‖F (x, ω)‖ ∂disorderLaw) :=
    (hφ.mul_const B).mono'
      hF.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
      (Eventually.of_forall hmajor)
  have hprod : Integrable F (volume.prod disorderLaw) :=
    (integrable_prod_iff hF.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall hs, hmarg⟩
  have htested : Integrable (fun ω => ∫ x, φ x * E x ω) disorderLaw :=
    hprod.integral_prod_right
  have habsInt : Integrable (fun ω => ∫ x, ‖F (x, ω)‖) disorderLaw :=
    hprod.norm.integral_prod_right
  have hnorm : (∫ ω, ‖∫ x, φ x * E x ω‖ ∂disorderLaw) ≤
      (∫ x, |φ x|) * B := by
    calc
      _ ≤ ∫ ω, (∫ x, ‖F (x, ω)‖) ∂disorderLaw :=
        integral_mono_ae htested.norm habsInt
          (Eventually.of_forall fun _ => norm_integral_le_integral_norm _)
      _ = ∫ x, ∫ ω, ‖F (x, ω)‖ ∂disorderLaw :=
        (integral_integral_swap hprod.norm).symm
      _ ≤ ∫ x, |φ x| * B := integral_mono_ae hmarg (hφ.mul_const B)
        (Eventually.of_forall fun x => by
          change (∫ ω, ‖F (x, ω)‖ ∂disorderLaw) ≤ |φ x| * B
          rw [hmean]
          exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _))
      _ = _ := integral_mul_const _ _
  rw [eLpNorm_one_eq_lintegral_enorm htested.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm htested]
  exact ENNReal.ofReal_le_ofReal hnorm

private theorem measurable_kpzLattice_exactReverse_error (ϑ : ℝ) {N m L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmEven : Even m) (hLEven : Even L) (hmL : m ≤ L)
    (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun p : Plane × Disorder =>
      kpzLattice ϑ N ((m : ℝ) / N) h₀ p.1 p.2 -
        kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ p.1
          (PolymerCalculus.reversedDisorder L p.2)) := by
  let β := criticalBeta ϑ N
  let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  let ξ : Disorder → Disorder := fun ω =>
    Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)
  let A : Site → Disorder → ℝ := fun z ω =>
    β * ω (m, z) - β ^ 2 / 2 +
      (Real.log (profileP2Fun 0 (m - 1) m (endpointDist β (m - 1) z (ξ ω)) f (ξ ω)) -
        Real.log (profileP2Fun β (m - 1) m (endpointDist β (m - 1) z (ξ ω)) f (ξ ω))) +
      ((∫ ζ, Real.log (pointToPlane β 0 m 0 ζ) ∂disorderLaw) -
        kpzLatticeCentring ϑ N ((m : ℝ) / N))
  have hξ : Measurable ξ := (Smoothing.measurable_shiftEnvironment _).comp
    (PolymerCalculus.measurePreserving_reversedDisorder L).measurable
  have hA (z : Site) : Measurable (A z) := by
    have hη (w : Site) : Measurable (fun ω => endpointDist β (m - 1) z (ξ ω) w) :=
      (Polymer.measurable_endpointDist β (m - 1) z w).comp hξ
    have hprof (γ : ℝ) := Smoothing.measurable_profileP2Fun_param γ (m - 1) m f hη hξ
    exact (((measurable_pi_apply (m, z)).const_mul β).sub_const _).add
      ((hprof 0).log.sub (hprof β).log) |>.add_const _
  have hsite : Measurable (fun p : Site × Disorder => A p.1 p.2) :=
    measurable_from_prod_countable_right hA
  have hmap : Measurable (fun p : Plane × Disorder =>
      (latticePoint N p.1, p.2)) :=
    ((measurable_latticePoint N).comp measurable_fst).prodMk measurable_snd
  convert hsite.comp hmap using 1
  funext p
  exact kpzLattice_sub_exactReverseField_eq ϑ hN hm hmEven hLEven hmL h₀ p.1 p.2

/-- Testing the pointwise exact-clock reversal estimate preserves its uniform bound, including
integrability, at a single specified pair of even clocks. -/
theorem eLpNorm_tested_kpzLattice_exactReverseClock_le (ϑ : ℝ) {N m L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmEven : Even m) (hLEven : Even L) (hmL : m ≤ L)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (hcenter : |kpzLatticeCentring ϑ N ((m : ℝ) / N) -
      ∫ ζ, Real.log (pointToPlane (criticalBeta ϑ N) 0 m 0 ζ) ∂disorderLaw| ≤
        (criticalBeta ϑ N) ^ 2 / 2) :
    eLpNorm (fun ω => ∫ x, φ x * (kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ x
        (PolymerCalculus.reversedDisorder L ω))) 1 disorderLaw ≤
      ENNReal.ofReal ((∫ x, |φ x|) *
        (|criticalBeta ϑ N| + (criticalBeta ϑ N) ^ 2 +
          Real.sqrt ((criticalBeta ϑ N) ^ 2 + (criticalBeta ϑ N) ^ 4 / 4))) := by
  let E : Plane → Disorder → ℝ := fun x ω =>
    kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ x
        (PolymerCalculus.reversedDisorder L ω)
  let B : ℝ := |criticalBeta ϑ N| + (criticalBeta ϑ N) ^ 2 +
    Real.sqrt ((criticalBeta ϑ N) ^ 2 + (criticalBeta ϑ N) ^ 4 / 4)
  have hmE : Measurable (Function.uncurry E) := by
    dsimp [E]
    exact measurable_kpzLattice_exactReverse_error ϑ hN hm hmEven hLEven hmL h₀
  have hpoint (x : Plane) := integral_abs_kpzLattice_sub_exactReverseField_le
    ϑ hN hm hmEven hLEven hmL h₀ x hcenter
  have hi (x : Plane) : Integrable (E x) disorderLaw := by
    apply (integrable_norm_iff ((hmE.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mp
    simpa only [E, Function.comp_def, Function.uncurry, id_eq, Real.norm_eq_abs] using
      (hpoint x).1
  have hb (x : Plane) : (∫ ω, |E x ω| ∂disorderLaw) ≤ B := by
    simpa only [E, B] using (hpoint x).2
  simpa only [E, B] using tested_eLpNorm_one_le_clockError E φ B hmE hi hb

/-- The tested exact-clock reversal error tends to zero even when the even clocks vary with
`N`, provided the reflected forward clock is eventually positive and no later than the horizon. -/
theorem tendsto_eLpNorm_tested_exactReverseField_error_of_movingClock (ϑ : ℝ)
    (m L : ℕ → ℕ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (hmPos : ∀ᶠ N : ℕ in atTop, 1 ≤ m N)
    (hmEven : ∀ N, Even (m N)) (hLEven : ∀ N, Even (L N))
    (hmL : ∀ᶠ N : ℕ in atTop, m N ≤ L N) :
    Tendsto (fun N : ℕ => eLpNorm (fun ω => ∫ x, φ x *
      (kpzLattice ϑ N ((m N : ℝ) / N) h₀ x ω -
        kpzLatticeReversed ϑ N (((L N - m N : ℕ) : ℝ) / N) ((L N : ℝ) / N)
          h₀ x (PolymerCalculus.reversedDisorder (L N) ω))) 1 disorderLaw)
      atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun N => |criticalBeta ϑ N| + (criticalBeta ϑ N) ^ 2 +
    Real.sqrt ((criticalBeta ϑ N) ^ 2 + (criticalBeta ϑ N) ^ 4 / 4)
  have hR : Tendsto R atTop (𝓝 0) := by
    have hc : Continuous (fun b : ℝ => |b| + b ^ 2 + Real.sqrt (b ^ 2 + b ^ 4 / 4)) := by
      fun_prop
    have hh := hc.continuousAt.tendsto.comp
      (Critical2DKPZ.SHF.Moments.tendsto_criticalBeta_zero ϑ)
    simpa [R, Function.comp_def] using hh
  have hbound : ∀ᶠ N : ℕ in atTop,
      eLpNorm (fun ω => ∫ x, φ x *
        (kpzLattice ϑ N ((m N : ℝ) / N) h₀ x ω -
          kpzLatticeReversed ϑ N (((L N - m N : ℕ) : ℝ) / N)
            ((L N : ℝ) / N) h₀ x (PolymerCalculus.reversedDisorder (L N) ω)))
        1 disorderLaw ≤ ENNReal.ofReal ((∫ x, |φ x|) * R N) := by
    filter_upwards [eventually_gt_atTop 0, hmPos, hmL] with N hN hmPosN hmLN
    have hcenter := Critical2DKPZ.Assembly.kpzLatticeCentring_clock_sub_logPointToPlane_le
      ϑ hN (hmEven N) hmPosN
    exact eLpNorm_tested_kpzLattice_exactReverseClock_le ϑ hN hmPosN
      (hmEven N) (hLEven N) hmLN h₀ φ hcenter
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal ((∫ x, |φ x|) * R N))
      atTop (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hR.const_mul (∫ x, |φ x|))
    simpa [Function.comp_def, mul_comm] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [hbound] with N hN
  exact hN

end Critical2DKPZ.LocalSobolev

end
