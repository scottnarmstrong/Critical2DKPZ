/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.BallAsymptotic
public import Critical2DKPZ.CovarianceKernel.SlowVariationTail

/-! # Radial mass consequences of the KPZ spectral asymptotic -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ComplexConjugate Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The spectral mass of the closed ball of radius `R`. -/
def spectralBallMass (ν : Measure Plane) (R : ℝ) : ℝ :=
  (ν (Metric.closedBall (0 : Plane) R)).toReal

/-- Closed-ball mass is monotone in the radius, including negative radii. -/
theorem spectralBallMass_mono (ν : Measure Plane) [IsLocallyFiniteMeasure ν] :
    Monotone (spectralBallMass ν) := by
  intro r s hrs
  have hsub : Metric.closedBall (0 : Plane) r ⊆ Metric.closedBall (0 : Plane) s := by
    intro x hx
    exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hx).trans hrs)
  have hfinite : ν (Metric.closedBall (0 : Plane) s) ≠ ⊤ := by
    by_cases hs : s < 0
    · rw [Metric.closedBall_of_neg hs]
      simp
    · exact (isCompact_closedBall (0 : Plane) s).measure_ne_top
  exact ENNReal.toReal_mono hfinite (measure_mono hsub)

/-- For large radii, multiplying the radius by `u ≥ 1` increases its double logarithm by at
most `log u`. -/
theorem logLog_mul_le_logLog_add_log_of_large_radius {R u : ℝ}
    (hR : Real.exp (Real.exp 1) < R) (hu : 1 ≤ u) :
    Real.log (Real.log (R * u)) ≤ Real.log (Real.log R) + Real.log u := by
  have hRpos : 0 < R := by
    have h0 : 0 < Real.exp (Real.exp 1) := by positivity
    linarith
  have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hlogR : 1 < Real.log R := by
    have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hR
    have he : 1 < Real.exp 1 := by exact Real.one_lt_exp_iff.mpr (by norm_num)
    rw [Real.log_exp] at h
    exact he.trans h
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hsum : Real.log R + Real.log u ≤ Real.log R * (1 + Real.log u) := by
    calc
      Real.log R + Real.log u ≤ Real.log R + Real.log R * Real.log u := by
        simpa only [one_mul] using
          add_le_add_right (mul_le_mul_of_nonneg_right hlogR.le hlogu) (Real.log R)
      _ = Real.log R * (1 + Real.log u) := by ring
  have hsumpos : 0 < Real.log R + Real.log u := by positivity
  have houter := Real.log_le_log hsumpos hsum
  calc
    Real.log (Real.log (R * u)) = Real.log (Real.log R + Real.log u) := by
      rw [Real.log_mul hRpos.ne' hupos.ne']
    _ ≤ Real.log (Real.log R * (1 + Real.log u)) := houter
    _ = Real.log (Real.log R) + Real.log (1 + Real.log u) := by
      rw [Real.log_mul (ne_of_gt (by linarith : 0 < Real.log R))
        (ne_of_gt (by linarith : 0 < 1 + Real.log u))]
    _ ≤ Real.log (Real.log R) + Real.log u := by
      have h : Real.log (1 + Real.log u) ≤ Real.log u := by
        calc
          Real.log (1 + Real.log u) ≤ (1 + Real.log u) - 1 :=
            Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + Real.log u)
          _ = Real.log u := by ring
      exact add_le_add_right h _

/-- The spectral mass of a ball is asymptotic to the double logarithm of its radius. -/
theorem spectralBallMass_tendsto_div_logLog_of (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) {t : ℝ} (ht : 0 < t)
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) :
    Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1) := by
  simpa [spectralBallMass] using
    kpz_spectralMeasure_ball_asymp_of ϑ P Z hZ H hH hShrinkingVarianceInput ht ν hν

/-- Double-logarithmic ball growth makes the spectral mass eventually positive. -/
theorem spectralBallMass_pos_eventually_of_tendsto (ν : Measure Plane)
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    ∀ᶠ R : ℝ in atTop, 0 < spectralBallMass ν R := by
  filter_upwards
    [hM.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      eventually_gt_atTop (Real.exp (Real.exp 1))] with R hratio hR
  have hL : 0 < Real.log (Real.log R) := by
    have hlog : Real.exp 1 < Real.log R := by
      have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hR
      simpa using h
    exact Real.log_pos (lt_trans (by norm_num) hlog)
  have hquot : 0 < spectralBallMass ν R / Real.log (Real.log R) := by linarith
  have hmul := mul_pos hquot hL
  rwa [div_mul_cancel₀ _ hL.ne'] at hmul

/-- The double-log ball-mass asymptotic is slowly varying under every fixed positive rescaling. -/
theorem spectralBallMass_slowlyVarying_of_tendsto (ν : Measure Plane) (u : ℝ)
    (hu : 0 < u)
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    Tendsto (fun R => spectralBallMass ν (R * u) / spectralBallMass ν R)
      atTop (𝓝 1) := by
  let L : ℝ → ℝ := fun R => Real.log (Real.log R)
  have hscaled' : Tendsto (fun R => spectralBallMass ν (u * R) / L (u * R))
      atTop (𝓝 1) := by
    have hcomp := hM.comp (tendsto_id.const_mul_atTop hu)
    convert hcomp using 1
    ext R
    simp [L]
  have hscaled : Tendsto (fun R => spectralBallMass ν (R * u) / L (R * u))
      atTop (𝓝 1) := hscaled'.congr' (by filter_upwards [] with R; rw [mul_comm])
  have hscale' : Tendsto (fun R => L (u * R) / L R) atTop (𝓝 1) := by
    simpa only [L] using tendsto_logLog_mul_div_of_pos_const u hu
  have hscale : Tendsto (fun R => L (R * u) / L R) atTop (𝓝 1) :=
    hscale'.congr' (by filter_upwards [] with R; rw [mul_comm])
  have hquot : Tendsto
      (fun R => (spectralBallMass ν (R * u) / L (R * u)) /
        (spectralBallMass ν R / L R)) atTop (𝓝 1) := by
    have h := hscaled.div hM (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    norm_num [L]
  have hprod := hquot.mul hscale
  have hmasspos := spectralBallMass_pos_eventually_of_tendsto ν hM
  have hlargeR : ∀ᶠ R : ℝ in atTop, Real.exp (Real.exp 1) < R :=
    eventually_gt_atTop (Real.exp (Real.exp 1))
  have hlargeRu' : ∀ᶠ R : ℝ in atTop, Real.exp (Real.exp 1) < u * R :=
    (tendsto_id.const_mul_atTop hu).eventually
      (eventually_gt_atTop (Real.exp (Real.exp 1)))
  have hlargeRu : ∀ᶠ R : ℝ in atTop, Real.exp (Real.exp 1) < R * u := by
    filter_upwards [hlargeRu'] with R hR
    simpa only [mul_comm] using hR
  have hEq : (fun R : ℝ =>
      (spectralBallMass ν (R * u) / L (R * u) /
        (spectralBallMass ν R / L R)) * (L (R * u) / L R)) =ᶠ[atTop]
      fun R => spectralBallMass ν (R * u) / spectralBallMass ν R := by
    filter_upwards [hmasspos, hlargeR, hlargeRu] with R hMR hR hRu
    have hL : 0 < L R := by
      dsimp [L]
      have hlog : Real.exp 1 < Real.log R := by
        have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hR
        simpa using h
      exact Real.log_pos (lt_trans (by norm_num) hlog)
    have hLu : 0 < L (R * u) := by
      dsimp [L]
      have hlog : Real.exp 1 < Real.log (R * u) := by
        have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hRu
        simpa using h
      exact Real.log_pos (lt_trans (by norm_num) hlog)
    dsimp [L]
    rw [div_div_div_eq, div_mul_div_comm]
    field_simp [hL.ne', hLu.ne', hMR.ne']
    apply (div_eq_iff (mul_ne_zero hL.ne' hLu.ne')).2
    ring
  simpa using hprod.congr' hEq

/-- The double-logarithmic ball-mass asymptotic is stable under the growing rescaling `R ↦ R²`.
This lets the Bessel tail be split into one intermediate annulus and a far tail. -/
theorem spectralBallMass_squareScale_ratio_of_tendsto (ν : Measure Plane)
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    Tendsto (fun R => spectralBallMass ν (R ^ 2) / spectralBallMass ν R) atTop (𝓝 1) := by
  let L : ℝ → ℝ := fun R => Real.log (Real.log R)
  have hpow : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hMpow : Tendsto (fun R => spectralBallMass ν (R ^ 2) /
      Real.log (Real.log (R ^ 2))) atTop (𝓝 1) := by
    convert hM.comp hpow using 1
    rfl
  have hL : Tendsto L atTop atTop := by
    dsimp [L]
    exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hshift : Tendsto (fun R : ℝ => Real.log 2 / L R) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := Real.log 2)).div_atTop hL
  have hscaleBase : Tendsto (fun R : ℝ => 1 + Real.log 2 / L R) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hshift
  have hscaleEq : (fun R : ℝ => 1 + Real.log 2 / L R) =ᶠ[atTop]
      fun R => L (R ^ 2) / L R := by
    filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1))] with R hR
    have hlogR : 1 < Real.log R := by
      have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hR
      have h1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      rw [Real.log_exp] at h
      exact h1.trans h
    have hlogRpos : 0 < Real.log R := by linarith
    have hLpos : 0 < L R := by dsimp [L]; exact Real.log_pos hlogR
    have hpowLog : Real.log (R ^ 2) = 2 * Real.log R := by
      rw [Real.log_pow]
      norm_num
    have hnum : L (R ^ 2) = Real.log 2 + L R := by
      dsimp [L]
      rw [hpowLog, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogRpos.ne']
    rw [hnum]
    field_simp [hLpos.ne']
    ring
  have hscale : Tendsto (fun R : ℝ => L (R ^ 2) / L R) atTop (𝓝 1) :=
    hscaleBase.congr' hscaleEq
  have hmassPos := spectralBallMass_pos_eventually_of_tendsto ν hM
  have hquot : Tendsto
      ((fun R => spectralBallMass ν (R ^ 2) / L (R ^ 2)) /
        (fun R => spectralBallMass ν R / L R)) atTop (𝓝 1) := by
    change Tendsto
      ((fun R => spectralBallMass ν (R ^ 2) / Real.log (Real.log (R ^ 2))) /
        (fun R => spectralBallMass ν R / Real.log (Real.log R))) atTop (𝓝 1)
    simpa using hMpow.div hM (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := hquot.mul hscale
  have hEq : (fun R : ℝ =>
      (spectralBallMass ν (R ^ 2) / L (R ^ 2)) /
        (spectralBallMass ν R / L R) * (L (R ^ 2) / L R)) =ᶠ[atTop]
      fun R => spectralBallMass ν (R ^ 2) / spectralBallMass ν R := by
    filter_upwards [hmassPos, eventually_gt_atTop (Real.exp (Real.exp 1))] with R hmass hR
    have hlogR : 1 < Real.log R := by
      have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hR
      have h1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      rw [Real.log_exp] at h
      exact h1.trans h
    have hLden : 0 < L R := by dsimp [L]; exact Real.log_pos hlogR
    have hlogR2 : 1 < Real.log (R ^ 2) := by
      have hpowLog : Real.log (R ^ 2) = 2 * Real.log R := by
        rw [Real.log_pow]
        norm_num
      rw [hpowLog]
      nlinarith
    have hLnum : 0 < L (R ^ 2) := by dsimp [L]; exact Real.log_pos hlogR2
    field_simp [hLden.ne', hLnum.ne', hmass.ne']
  simpa only [mul_one] using hprod.congr' hEq

/-- Spectral ball mass satisfies a uniform logarithmic dilation bound at sufficiently large radii. -/
theorem spectralBallMass_logDilationBound_of_tendsto (ν : Measure Plane)
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    ∃ A : ℝ, ∀ᶠ R : ℝ in atTop, ∀ u : ℝ, 1 ≤ u →
      spectralBallMass ν (R * u) ≤ A * (1 + Real.log u) * spectralBallMass ν R := by
  have hnear : ∀ᶠ S : ℝ in atTop,
      (1 / 2 : ℝ) < spectralBallMass ν S / Real.log (Real.log S) ∧
        spectralBallMass ν S / Real.log (Real.log S) < 2 := by
    filter_upwards
      [hM.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
        hM.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with S hlow hup
    exact ⟨hlow, hup⟩
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.mp hnear
  let R₀ : ℝ := max S₀ (Real.exp (Real.exp 1))
  refine ⟨4, ?_⟩
  filter_upwards [eventually_gt_atTop R₀] with R hR₀
  intro u hu
  have hlargeR : Real.exp (Real.exp 1) < R := by
    exact lt_of_le_of_lt (le_max_right _ _) hR₀
  have hS₀R : S₀ < R := lt_of_le_of_lt (le_max_left _ _) hR₀
  have hRpos : 0 < R := by
    have h0 : 0 < Real.exp (Real.exp 1) := by positivity
    linarith
  have hS₀Ru : S₀ < R * u := by
    calc
      S₀ < R := hS₀R
      _ ≤ R * u := by
        calc
          R = R * 1 := by ring
          _ ≤ R * u := mul_le_mul_of_nonneg_left hu hRpos.le
  have hnearR := hS₀ R hS₀R.le
  have hnearRu := hS₀ (R * u) hS₀Ru.le
  have hLR : 1 < Real.log (Real.log R) := by
    have hlog : Real.exp 1 < Real.log R := by
      have h := Real.log_lt_log
        (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hlargeR
      simpa using h
    have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp 1) hlog
    simpa using h
  have hmassLower : (1 / 2 : ℝ) * Real.log (Real.log R) ≤ spectralBallMass ν R := by
    have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have hlogR : 1 < Real.log R := lt_trans hexp (by
      have h := Real.log_lt_log
        (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hlargeR
      simpa using h)
    have h := (lt_div_iff₀ (Real.log_pos hlogR)).mp hnearR.1
    nlinarith
  have hRuLarge : Real.exp (Real.exp 1) < R * u := by
    calc
      Real.exp (Real.exp 1) < R := hlargeR
      _ ≤ R * u := by
        calc
          R = R * 1 := by ring
          _ ≤ R * u := mul_le_mul_of_nonneg_left hu hRpos.le
  have hLRu : 0 < Real.log (Real.log (R * u)) := by
    have hlog : Real.exp 1 < Real.log (R * u) := by
      have h := Real.log_lt_log
        (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hRuLarge
      simpa using h
    exact Real.log_pos (lt_trans (by norm_num) hlog)
  have hmassUpper : spectralBallMass ν (R * u) ≤ 2 * Real.log (Real.log (R * u)) := by
    have h := (div_lt_iff₀ hLRu).mp hnearRu.2
    linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hLprofile : Real.log (Real.log R) + Real.log u ≤
      Real.log (Real.log R) * (1 + Real.log u) := by
    calc
      Real.log (Real.log R) + Real.log u ≤
          Real.log (Real.log R) + Real.log (Real.log R) * Real.log u := by
        simpa only [one_mul] using add_le_add_right
          (mul_le_mul_of_nonneg_right (le_of_lt hLR) hlogu) (Real.log (Real.log R))
      _ = Real.log (Real.log R) * (1 + Real.log u) := by ring
  have hlogBound := logLog_mul_le_logLog_add_log_of_large_radius hlargeR hu
  have hLM : Real.log (Real.log R) ≤ 2 * spectralBallMass ν R := by
    nlinarith [hmassLower]
  calc
    spectralBallMass ν (R * u) ≤ 2 * Real.log (Real.log (R * u)) := hmassUpper
    _ ≤ 2 * (Real.log (Real.log R) + Real.log u) :=
      mul_le_mul_of_nonneg_left hlogBound (by norm_num)
    _ ≤ 2 * (Real.log (Real.log R) * (1 + Real.log u)) :=
      mul_le_mul_of_nonneg_left hLprofile (by norm_num)
    _ ≤ 4 * (1 + Real.log u) * spectralBallMass ν R := by
      calc
        2 * (Real.log (Real.log R) * (1 + Real.log u)) ≤
            2 * (2 * spectralBallMass ν R * (1 + Real.log u)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hLM (by positivity)) (by norm_num)
        _ = 4 * (1 + Real.log u) * spectralBallMass ν R := by ring

/-- Double-logarithmic spectral ball growth gives normalized first-moment and tail integral limits equal to one. -/
theorem spectralBallMass_integralAsymptotics_of_tendsto (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν]
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    Tendsto (fun R => 2 / R ^ 2 *
      (∫ a in (0 : ℝ)..R, a * spectralBallMass ν a) / spectralBallMass ν R)
        atTop (𝓝 1) ∧
      Tendsto (fun R => Real.sqrt R / 2 *
        (∫ a in Set.Ioi R, a ^ (-(3 : ℝ) / 2) * spectralBallMass ν a) /
          spectralBallMass ν R) atTop (𝓝 1) := by
  have hmono : Monotone (spectralBallMass ν) := spectralBallMass_mono ν
  have hMzero : 0 ≤ spectralBallMass ν 0 := by
    exact ENNReal.toReal_nonneg
  have hpos : ∀ᶠ R : ℝ in atTop, 0 < spectralBallMass ν R :=
    spectralBallMass_pos_eventually_of_tendsto ν hM
  have hslow : ∀ u : ℝ, 0 < u →
      Tendsto (fun R => spectralBallMass ν (R * u) / spectralBallMass ν R)
        atTop (𝓝 1) := by
    intro u hu
    exact spectralBallMass_slowlyVarying_of_tendsto ν u hu hM
  have hdom : ∃ A : ℝ, ∀ᶠ R : ℝ in atTop, ∀ u : ℝ, 1 ≤ u →
      spectralBallMass ν (R * u) ≤ A * (1 + Real.log u) * spectralBallMass ν R :=
    spectralBallMass_logDilationBound_of_tendsto ν hM
  exact ⟨tendsto_integral_mul_div_of_slowlyVarying (spectralBallMass ν)
      hmono hMzero hpos hslow,
    tendsto_integral_rpow_div_of_slowlyVarying (spectralBallMass ν)
      hmono hpos hslow hdom⟩

end Critical2DKPZ.CovarianceKernel

end
