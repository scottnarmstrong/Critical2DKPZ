/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RadialInversion

/-! # Asymptotic estimates for radial Bessel inversion -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.CovarianceKernel


/-- The real mass of a finite radial annulus is the difference of the two ball masses. -/
theorem spectralBallMass_annulus_toReal_of_le (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {r s : ℝ} (hrs : r ≤ s) :
    (ν (Metric.closedBall (0 : Plane) s \ Metric.closedBall (0 : Plane) r)).toReal =
      spectralBallMass ν s - spectralBallMass ν r := by
  let B : Set Plane := Metric.closedBall (0 : Plane) r
  let D : Set Plane := Metric.closedBall (0 : Plane) s
  have hBsub : B ⊆ D := by
    intro ξ hξ
    exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hξ).trans hrs)
  have hBfinite : ν B ≠ ⊤ := (isCompact_closedBall (0 : Plane) r).measure_ne_top
  have hDfinite : ν D ≠ ⊤ := (isCompact_closedBall (0 : Plane) s).measure_ne_top
  have hAnfinite : ν (D \ B) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfinite (measure_mono (by intro ξ hξ; exact hξ.1))
  have hdisj : Disjoint B (D \ B) := Set.disjoint_left.mpr fun _ hξ hξ' => hξ'.2 hξ
  have hunion : D = B ∪ (D \ B) := by
    ext ξ
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hξ
      by_cases hB : ξ ∈ B
      · exact Or.inl hB
      · exact Or.inr ⟨hξ, hB⟩
    · rintro (hξ | ⟨hξ, _⟩)
      · exact hBsub hξ
      · exact hξ
  have hsum : ν D = ν B + ν (D \ B) := by
    calc
      ν D = ν (B ∪ (D \ B)) := congrArg ν hunion
      _ = ν B + ν (D \ B) := measure_union hdisj
        ((isCompact_closedBall (0 : Plane) s).measurableSet.diff
          (isCompact_closedBall (0 : Plane) r).measurableSet)
  have hsumReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hBfinite hAnfinite] at hsumReal
  dsimp [B, D, spectralBallMass] at hsumReal ⊢
  linarith

/-- Logarithmic growth makes the Bessel kernel at any fixed positive reciprocal scale integrable. -/
theorem integrable_besselJ0_scaled_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hGrowth : ∀ s : ℝ, 1 ≤ s →
      spectralBallMass ν s ≤ A * (1 + Real.log s)) :
    Integrable (fun ξ : Plane => Spectral.besselJ0Angular (‖ξ‖ / R)) ν := by
  let z : Plane := WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)
  have hnormz : ‖z‖ = R⁻¹ := by
    dsimp [z]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    positivity
  have hz : z ≠ 0 := by
    intro hz
    have hcoord := congrArg (fun x : Plane => x 0) hz
    have : (R⁻¹ : ℝ) = 0 := by simpa [z] using hcoord
    exact (inv_ne_zero hR.ne') this
  have hJ := integrable_besselJ0_of_logGrowth ν hA hGrowth z hz
  apply hJ.congr
  filter_upwards [] with ξ
  have harg : ‖ξ‖ * ‖z‖ = ‖ξ‖ / R := by
    rw [hnormz]
    field_simp [hR.ne']
  exact congrArg Spectral.besselJ0Angular harg


/-- The Bessel kernel differs from one by at most a quadratic error on a small fraction of the
spectral ball. The integrability conjunct makes the set integral nonvacuous. -/
theorem integrableOn_besselJ0_sub_one_ball_bound (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {R η : ℝ} (hR : 0 < R) (hη : 0 ≤ η) :
    IntegrableOn (fun ξ : Plane =>
      |Spectral.besselJ0Angular (‖ξ‖ / R) - 1|)
      (Metric.closedBall (0 : Plane) (η * R)) ν ∧
      (∫ ξ in Metric.closedBall (0 : Plane) (η * R),
        |Spectral.besselJ0Angular (‖ξ‖ / R) - 1| ∂ν) ≤
        (η ^ 2 / 2) * spectralBallMass ν (η * R) := by
  let B : Set Plane := Metric.closedBall (0 : Plane) (η * R)
  let f : Plane → ℝ := fun ξ =>
    |Spectral.besselJ0Angular (‖ξ‖ / R) - 1|
  have hBcompact : IsCompact B := by
    dsimp [B]
    exact isCompact_closedBall (0 : Plane) (η * R)
  have hBfinite : ν B ≠ ⊤ := hBcompact.measure_ne_top
  have hBmeas : MeasurableSet B := hBcompact.measurableSet
  have hfcont : Continuous f := by
    dsimp [f]
    exact continuous_abs.comp
      ((Spectral.continuous_besselJ0Angular.comp
        (continuous_norm.mul continuous_const)).sub continuous_const)
  have htwo : IntegrableOn (fun _ : Plane => (2 : ℝ)) B ν := integrableOn_const hBfinite
  have hfint : IntegrableOn f B ν := by
    apply htwo.mono' hfcont.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hBmeas] with ξ hξ
    have hnorm : ‖ξ‖ ≤ η * R := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hξ
    have harg : 0 ≤ ‖ξ‖ / R ∧ ‖ξ‖ / R ≤ η := by
      constructor
      · positivity
      · exact (div_le_iff₀ hR).2 (by nlinarith)
    have hbound : f ξ ≤ 2 := by
      dsimp [f]
      have hone := Spectral.abs_besselJ0Angular_le_one (‖ξ‖ / R)
      have htriangle := abs_sub_le (Spectral.besselJ0Angular (‖ξ‖ / R)) 0 (1 : ℝ)
      have htriangle' : |Spectral.besselJ0Angular (‖ξ‖ / R) - 1| ≤
          |Spectral.besselJ0Angular (‖ξ‖ / R)| + 1 := by simpa using htriangle
      nlinarith
    have hfnn : 0 ≤ f ξ := abs_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hfnn,
      abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using hbound
  have hsmall : IntegrableOn (fun _ : Plane => (η ^ 2 / 2 : ℝ)) B ν :=
    integrableOn_const hBfinite
  have hpoint : ∀ ξ ∈ B, f ξ ≤ η ^ 2 / 2 := by
    intro ξ hξ
    have hnorm : ‖ξ‖ ≤ η * R := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hξ
    have harg : 0 ≤ ‖ξ‖ / R ∧ ‖ξ‖ / R ≤ η := by
      constructor
      · positivity
      · exact (div_le_iff₀ hR).2 (by nlinarith)
    have hJ := Spectral.abs_besselJ0Angular_sub_one_le (‖ξ‖ / R)
    dsimp [f]
    nlinarith [sq_nonneg (‖ξ‖ / R), harg.2]
  have hmono := setIntegral_mono_on hfint hsmall hBmeas hpoint
  refine ⟨hfint, ?_⟩
  calc
    (∫ ξ in B, f ξ ∂ν) ≤ ∫ ξ in B, (η ^ 2 / 2 : ℝ) ∂ν := hmono
    _ = (η ^ 2 / 2) * spectralBallMass ν (η * R) := by
      rw [setIntegral_const]
      simp [Measure.real, spectralBallMass, B, smul_eq_mul]
      ring

/-- On the ball of radius `R²`, the scaled Bessel integral is squeezed between its small-ball
quadratic approximation and the total ball mass. Integrability is included for both bounds. -/
theorem besselJ0_integral_ball_squeeze (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A R η : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hGrowth : ∀ s : ℝ, 1 ≤ s →
      spectralBallMass ν s ≤ A * (1 + Real.log s)) :
    IntegrableOn (fun ξ : Plane => Spectral.besselJ0Angular (‖ξ‖ / R))
        (Metric.closedBall (0 : Plane) (R ^ 2)) ν ∧
      (1 - η ^ 2 / 2) * spectralBallMass ν (η * R) -
          (spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) ≤
        ∫ ξ in Metric.closedBall (0 : Plane) (R ^ 2),
          Spectral.besselJ0Angular (‖ξ‖ / R) ∂ν ∧
      (∫ ξ in Metric.closedBall (0 : Plane) (R ^ 2),
        Spectral.besselJ0Angular (‖ξ‖ / R) ∂ν) ≤ spectralBallMass ν (R ^ 2) := by
  let B : Set Plane := Metric.closedBall (0 : Plane) (η * R)
  let C : Set Plane := Metric.closedBall (0 : Plane) (R ^ 2)
  let J : Plane → ℝ := fun ξ => Spectral.besselJ0Angular (‖ξ‖ / R)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRadius : η * R ≤ R ^ 2 := by
    calc
      η * R ≤ 1 * R := mul_le_mul_of_nonneg_right hη1 hRpos.le
      _ ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hBsubC : B ⊆ C := by
    intro ξ hξ
    exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hξ).trans hRadius)
  have hBmeas : MeasurableSet B := (isCompact_closedBall (0 : Plane) (η * R)).measurableSet
  have hCcompact : IsCompact C := isCompact_closedBall (0 : Plane) (R ^ 2)
  have hCmeas : MeasurableSet C := hCcompact.measurableSet
  have hCfinite : ν C ≠ ⊤ := hCcompact.measure_ne_top
  have hBfinite : ν B ≠ ⊤ := (isCompact_closedBall (0 : Plane) (η * R)).measure_ne_top
  have hJ : Integrable J ν := by
    simpa only [J] using integrable_besselJ0_scaled_of_logGrowth ν hA hRpos hGrowth
  have hJonB : IntegrableOn J B ν := hJ.integrableOn.mono_set (Set.subset_univ _)
  have hJonC : IntegrableOn J C ν := hJ.integrableOn.mono_set (Set.subset_univ _)
  have hsmall := integrableOn_besselJ0_sub_one_ball_bound ν hRpos hη.le
  have hsmallInt : IntegrableOn (fun ξ : Plane => |J ξ - 1|) B ν := by
    simpa [B, J] using hsmall.1
  have hdiffInt : IntegrableOn (fun ξ : Plane => J ξ - 1) B ν :=
    hJonB.sub (integrableOn_const hBfinite)
  have hnegabsInt : IntegrableOn (fun ξ : Plane => -|J ξ - 1|) B ν :=
    hsmallInt.neg
  have hdiffLower :
      -(η ^ 2 / 2 * spectralBallMass ν (η * R)) ≤
        ∫ ξ in B, (J ξ - 1) ∂ν := by
    have hmono := setIntegral_mono_on hnegabsInt hdiffInt hBmeas
      (fun ξ _ => neg_abs_le (J ξ - 1))
    calc
      -(η ^ 2 / 2 * spectralBallMass ν (η * R)) ≤
          -(∫ ξ in B, |J ξ - 1| ∂ν) := neg_le_neg hsmall.2
      _ = ∫ ξ in B, -|J ξ - 1| ∂ν := by rw [integral_neg]
      _ ≤ ∫ ξ in B, (J ξ - 1) ∂ν := hmono
  have hOneB : IntegrableOn (fun _ : Plane => (1 : ℝ)) B ν := integrableOn_const hBfinite
  have hOneBIntegral : (∫ ξ in B, (1 : ℝ) ∂ν) = spectralBallMass ν (η * R) := by
    rw [setIntegral_const]
    simp [Measure.real, spectralBallMass, B, smul_eq_mul]
  have hlowIntegral :
      (1 - η ^ 2 / 2) * spectralBallMass ν (η * R) ≤ ∫ ξ in B, J ξ ∂ν := by
    have hsum :
        (∫ ξ in B, J ξ ∂ν) =
          (∫ ξ in B, (1 : ℝ) ∂ν) + ∫ ξ in B, (J ξ - 1) ∂ν := by
      calc
        (∫ ξ in B, J ξ ∂ν) =
            ∫ ξ in B, (fun ξ => (1 : ℝ) + (J ξ - 1)) ξ ∂ν := by
              apply setIntegral_congr_fun hBmeas
              intro ξ _
              ring
        _ = (∫ ξ in B, (1 : ℝ) ∂ν) + ∫ ξ in B, (J ξ - 1) ∂ν :=
          integral_add hOneB hdiffInt
    rw [hsum, hOneBIntegral]
    nlinarith [hdiffLower]
  have hShellMass : (ν (C \ B)).toReal =
      spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R) := by
    simpa [B, C] using spectralBallMass_annulus_toReal_of_le ν hRadius
  have hShellfinite : ν (C \ B) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfinite (measure_mono (by intro ξ hξ; exact hξ.1))
  have hShellmeas : MeasurableSet (C \ B) := hCmeas.diff hBmeas
  have hShellConst : IntegrableOn (fun _ : Plane => (-1 : ℝ)) (C \ B) ν :=
    integrableOn_const hShellfinite
  have hShellJ : IntegrableOn J (C \ B) ν := hJonC.mono_set Set.sdiff_subset
  have hShellPoint : ∀ ξ ∈ C \ B, -1 ≤ J ξ := by
    intro ξ _
    have habs := Spectral.abs_besselJ0Angular_le_one (‖ξ‖ / R)
    have hJabs : |J ξ| ≤ 1 := by simpa [J] using habs
    exact (abs_le.mp hJabs).1
  have hShellLower :
      -(spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) ≤
        ∫ ξ in C \ B, J ξ ∂ν := by
    have hmono := setIntegral_mono_on hShellConst hShellJ hShellmeas hShellPoint
    have hconst :
        (∫ ξ in C \ B, (-1 : ℝ) ∂ν) =
          -(spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) := by
      rw [setIntegral_const]
      change (ν (C \ B)).toReal • (-1 : ℝ) = _
      rw [hShellMass]
      simp
    rw [← hconst]
    exact hmono
  have hsplit :
      (∫ ξ in C, J ξ ∂ν) =
        (∫ ξ in B, J ξ ∂ν) + ∫ ξ in C \ B, J ξ ∂ν := by
    have hsdiff := setIntegral_sdiff hBmeas hJonC hBsubC
    linarith
  have hlow :
      (1 - η ^ 2 / 2) * spectralBallMass ν (η * R) -
          (spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) ≤
        ∫ ξ in C, J ξ ∂ν := by
    calc
      (1 - η ^ 2 / 2) * spectralBallMass ν (η * R) -
          (spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) ≤
          (∫ ξ in B, J ξ ∂ν) + ∫ ξ in C \ B, J ξ ∂ν := add_le_add hlowIntegral hShellLower
      _ = ∫ ξ in C, J ξ ∂ν := hsplit.symm
  have hOneC : IntegrableOn (fun _ : Plane => (1 : ℝ)) C ν := integrableOn_const hCfinite
  have hOneCIntegral : (∫ ξ in C, (1 : ℝ) ∂ν) = spectralBallMass ν (R ^ 2) := by
    rw [setIntegral_const]
    simp [Measure.real, spectralBallMass, C, smul_eq_mul]
  have hUpperPoint : ∀ ξ ∈ C, J ξ ≤ 1 := by
    intro ξ _
    have habs := Spectral.abs_besselJ0Angular_le_one (‖ξ‖ / R)
    exact le_trans (le_abs_self (J ξ)) (by simpa [J] using habs)
  have hupper : (∫ ξ in C, J ξ ∂ν) ≤ spectralBallMass ν (R ^ 2) := by
    calc
      (∫ ξ in C, J ξ ∂ν) ≤ (∫ ξ in C, (1 : ℝ) ∂ν) :=
        setIntegral_mono_on hJonC hOneC hCmeas hUpperPoint
      _ = spectralBallMass ν (R ^ 2) := hOneCIntegral
  exact ⟨hJonC, hlow, hupper⟩

/-- On the region beyond radius `R²`, the oscillatory Bessel kernel is bounded by the exterior
inverse-square-root weight. The resulting set integral has the explicit spectral-mass squeeze tail bound. -/
theorem integrableOn_besselJ0_squareExterior_bound (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hGrowth : ∀ s : ℝ, 1 ≤ s → spectralBallMass ν s ≤ A * (1 + Real.log s))
    (hDilation : ∀ u : ℝ, 1 ≤ u →
      spectralBallMass ν (R ^ 2 * u) ≤
        A * (1 + Real.log u) * spectralBallMass ν (R ^ 2)) :
    IntegrableOn (fun ξ : Plane => |Spectral.besselJ0Angular (‖ξ‖ / R)|)
        (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ ν ∧
      (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
        |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) ≤
        30 * A * spectralBallMass ν (R ^ 2) / Real.sqrt R := by
  let S : ℝ := R ^ 2
  let E : Set Plane := (Metric.closedBall (0 : Plane) S)ᶜ
  let z : Plane := WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hSone : 1 ≤ S := by dsimp [S]; nlinarith [sq_nonneg (R - 1)]
  have hsqrtRpos : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
  have hnormz : ‖z‖ = R⁻¹ := by
    dsimp [z]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    positivity
  have hz : z ≠ 0 := by
    intro hz
    have hcoord := congrArg (fun x : Plane => x 0) hz
    have : (R⁻¹ : ℝ) = 0 := by simpa [z] using hcoord
    exact (inv_ne_zero (ne_of_gt hRpos)) this
  have hJraw := integrable_besselJ0_of_logGrowth ν hA hGrowth z hz
  have hJ : Integrable (fun ξ : Plane =>
      Spectral.besselJ0Angular (‖ξ‖ / R)) ν := by
    apply hJraw.congr
    filter_upwards [] with ξ
    have harg : ‖ξ‖ * ‖z‖ = ‖ξ‖ / R := by
      rw [hnormz]
      field_simp
    exact congrArg Spectral.besselJ0Angular harg
  have hJabs : Integrable (fun ξ : Plane =>
      |Spectral.besselJ0Angular (‖ξ‖ / R)|) ν := hJ.abs
  have hTail := integrable_inverseSqrtTailAbove_integral_bound ν hA hSone hGrowth hDilation
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact (isCompact_closedBall (0 : Plane) S).measurableSet.compl
  have hTailScaled : IntegrableOn
      (fun ξ : Plane => 3 * Real.sqrt R * spectralInverseSqrtTailAbove S ξ) E ν :=
    (hTail.1.const_mul (3 * Real.sqrt R)).integrableOn
  have hpoint : ∀ ξ ∈ E,
      |Spectral.besselJ0Angular (‖ξ‖ / R)| ≤
        3 * Real.sqrt R * spectralInverseSqrtTailAbove S ξ := by
    intro ξ hξ
    have hrad : S < ‖ξ‖ := by
      have hnot : ¬ ‖ξ‖ ≤ S := by
        simpa [E, Metric.mem_closedBall, dist_zero_right] using hξ
      exact lt_of_not_ge hnot
    have hradOne : 1 ≤ ‖ξ‖ := by
      dsimp [S] at hrad
      nlinarith [sq_nonneg (R - 1)]
    have harg : 1 ≤ ‖ξ‖ / R := by
      apply (le_div_iff₀ hRpos).2
      dsimp [S] at hrad
      nlinarith [sq_nonneg (R - 1)]
    have hJbound := Spectral.abs_besselJ0Angular_le_three_div_sqrt harg
    have htail : spectralInverseSqrtTailAbove S ξ = (Real.sqrt ‖ξ‖)⁻¹ := by
      have hmem : ξ ∈ {ξ : Plane | S < ‖ξ‖} := hrad
      have hnorm : 1 ≤ ‖ξ‖ := hradOne
      simp [spectralInverseSqrtTailAbove, hmem, spectralInverseSqrtTail, hnorm]
    have hsqrtDiv : Real.sqrt (‖ξ‖ / R) = Real.sqrt ‖ξ‖ / Real.sqrt R :=
      Real.sqrt_div (norm_nonneg ξ) R
    calc
      |Spectral.besselJ0Angular (‖ξ‖ / R)| ≤
          3 / Real.sqrt (‖ξ‖ / R) := hJbound
      _ = 3 * Real.sqrt R * spectralInverseSqrtTailAbove S ξ := by
        rw [hsqrtDiv, htail]
        field_simp [ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hradOne)),
          hsqrtRpos.ne']
  have hmono := setIntegral_mono_on hJabs.integrableOn hTailScaled hEmeas hpoint
  have hEset : {ξ : Plane | S < ‖ξ‖} = E := by
    ext ξ
    simp [E, Metric.mem_closedBall, dist_zero_right]
  have hTailFn : spectralInverseSqrtTailAbove S =
      E.indicator spectralInverseSqrtTail := by
    funext ξ
    change ({x : Plane | S < ‖x‖}.indicator spectralInverseSqrtTail) ξ =
      (E.indicator spectralInverseSqrtTail) ξ
    rw [hEset]
  have hTailId : (∫ ξ, spectralInverseSqrtTailAbove S ξ ∂ν) =
      ∫ ξ in E, spectralInverseSqrtTail ξ ∂ν := by
    rw [hTailFn, integral_indicator hEmeas]
  have hTailOnE : (∫ ξ in E, spectralInverseSqrtTailAbove S ξ ∂ν) =
      ∫ ξ in E, spectralInverseSqrtTail ξ ∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hEmeas] with ξ hξ
    rw [hTailFn, Set.indicator_of_mem hξ]
  have hTailOnEGlobal : (∫ ξ in E, spectralInverseSqrtTailAbove S ξ ∂ν) =
      ∫ ξ, spectralInverseSqrtTailAbove S ξ ∂ν := by
    rw [hTailOnE, ← hTailId]
  constructor
  · simpa [E, S] using hJabs.integrableOn.mono_set (Set.subset_univ _)
  · change (∫ ξ in E, |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) ≤
      30 * A * spectralBallMass ν (R ^ 2) / Real.sqrt R
    calc
      (∫ ξ in E, |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) ≤
          ∫ ξ in E, 3 * Real.sqrt R * spectralInverseSqrtTailAbove S ξ ∂ν := hmono
      _ = 3 * Real.sqrt R * (∫ ξ, spectralInverseSqrtTailAbove S ξ ∂ν) := by
        rw [integral_const_mul, hTailOnEGlobal]
      _ ≤ 3 * Real.sqrt R *
          (10 * A * spectralBallMass ν S / Real.sqrt S) :=
        mul_le_mul_of_nonneg_left hTail.2 (by positivity)
      _ = 30 * A * spectralBallMass ν (R ^ 2) / Real.sqrt R := by
        dsimp [S]
        have hRnonneg : 0 ≤ R := le_of_lt hRpos
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRnonneg]
        field_simp [hRpos.ne', hsqrtRpos.ne']
        rw [Real.sq_sqrt hRpos.le]
        ring

/-- Spectral-mass squeeze makes the absolute Bessel integral beyond radius `R²` negligible compared with the
spectral mass inside radius `R`. Integrability is stated eventually alongside the limit. -/
theorem besselJ0_squareExterior_integral_div_mass_tendsto_zero (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν]
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    (∀ᶠ R : ℝ in atTop, IntegrableOn
      (fun ξ : Plane => |Spectral.besselJ0Angular (‖ξ‖ / R)|)
      (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ ν) ∧
    Tendsto (fun R =>
      (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
        |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) / spectralBallMass ν R)
      atTop (𝓝 0) := by
  obtain ⟨Ag, hAg, hGrowth0⟩ := spectralBallMass_logGrowth_of_tendsto ν hM
  obtain ⟨D, hDilationD⟩ := spectralBallMass_logDilationBound_of_tendsto ν hM
  let A : ℝ := max Ag D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hGrowth : ∀ s : ℝ, 1 ≤ s →
      spectralBallMass ν s ≤ A * (1 + Real.log s) := by
    intro s hs
    have hmass := hGrowth0 s hs
    have hfactor : 0 ≤ 1 + Real.log s := by
      have hlog := Real.log_nonneg hs
      linarith
    calc
      spectralBallMass ν s ≤ Ag * (1 + Real.log s) := hmass
      _ ≤ A * (1 + Real.log s) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hfactor
  have hpow : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  have hDilationEvent := hpow.eventually hDilationD
  have hgood : ∀ᶠ R : ℝ in atTop,
      1 ≤ R ∧ ∀ u : ℝ, 1 ≤ u →
        spectralBallMass ν (R ^ 2 * u) ≤
          A * (1 + Real.log u) * spectralBallMass ν (R ^ 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hDilationEvent] with R hR hD
    refine ⟨hR, ?_⟩
    intro u hu
    have hbase := hD u hu
    have hfactor : 0 ≤ 1 + Real.log u := by linarith [Real.log_nonneg hu]
    have hmass : 0 ≤ spectralBallMass ν (R ^ 2) := ENNReal.toReal_nonneg
    have hprod : 0 ≤ (1 + Real.log u) * spectralBallMass ν (R ^ 2) :=
      mul_nonneg hfactor hmass
    calc
      spectralBallMass ν (R ^ 2 * u) ≤
          D * ((1 + Real.log u) * spectralBallMass ν (R ^ 2)) := by
            simpa [mul_assoc] using hbase
      _ ≤ A * ((1 + Real.log u) * spectralBallMass ν (R ^ 2)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hprod
      _ = A * (1 + Real.log u) * spectralBallMass ν (R ^ 2) := by ring
  have hIntEvent : ∀ᶠ R : ℝ in atTop,
      IntegrableOn (fun ξ : Plane =>
        |Spectral.besselJ0Angular (‖ξ‖ / R)|)
        (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ ν := by
    filter_upwards [hgood] with R hR
    exact (integrableOn_besselJ0_squareExterior_bound ν hA hR.1 hGrowth hR.2).1
  have hratio := spectralBallMass_squareScale_ratio_of_tendsto ν hM
  have hcoef : Tendsto (fun R : ℝ =>
      30 * A * (spectralBallMass ν (R ^ 2) / spectralBallMass ν R)) atTop
      (𝓝 (30 * A)) := by
    simpa only [mul_one] using (tendsto_const_nhds (x := 30 * A)).mul hratio
  have hupper : Tendsto (fun R : ℝ =>
      30 * A * (spectralBallMass ν (R ^ 2) / spectralBallMass ν R) /
        Real.sqrt R) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcoef.div_atTop (Real.tendsto_sqrt_atTop)
  have hmassPos := spectralBallMass_pos_eventually_of_tendsto ν hM
  have hbound : ∀ᶠ R : ℝ in atTop,
      (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
        |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) / spectralBallMass ν R ≤
        30 * A * (spectralBallMass ν (R ^ 2) / spectralBallMass ν R) / Real.sqrt R := by
    filter_upwards [hgood, hmassPos] with R hR hMR
    have htail := integrableOn_besselJ0_squareExterior_bound ν hA hR.1 hGrowth hR.2
    have hdiv := div_le_div_of_nonneg_right htail.2 hMR.le
    have hsqrtPos : 0 < Real.sqrt R := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hR.1)
    have hEq : (30 * A * spectralBallMass ν (R ^ 2) / Real.sqrt R) /
        spectralBallMass ν R =
        30 * A * (spectralBallMass ν (R ^ 2) / spectralBallMass ν R) /
          Real.sqrt R := by
      field_simp [hMR.ne', hsqrtPos.ne']
    rw [hEq] at hdiv
    exact hdiv
  have hnonneg : ∀ᶠ R : ℝ in atTop,
      0 ≤ (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
        |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) / spectralBallMass ν R := by
    filter_upwards [hmassPos] with R hMR
    apply div_nonneg _ hMR.le
    exact integral_nonneg fun ξ => abs_nonneg _
  have hlim : Tendsto (fun R : ℝ =>
      (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
        |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) / spectralBallMass ν R)
      atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [hnonneg] with R hR
      exact lt_of_lt_of_le ha hR
    · intro b hb
      filter_upwards [hbound, hupper.eventually (Iio_mem_nhds hb)] with R hR hUpperR
      exact lt_of_le_of_lt hR hUpperR
  exact ⟨hIntEvent, hlim⟩

/-- Once the uncut Bessel kernel is integrable, the compensating unit-ball term in the
definition of `besselInversion` cancels exactly. -/
theorem besselInversion_eq_integral_besselJ0 (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] (z : Plane)
    (hJ : Integrable (fun ξ : Plane =>
      Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)) ν) :
    besselInversion ν z =
      ∫ ξ, Spectral.besselJ0Angular (‖ξ‖ * ‖z‖) ∂ν := by
  let B : Set Plane := Metric.closedBall (0 : Plane) 1
  have hBcompact : IsCompact B := by
    dsimp [B]
    exact isCompact_closedBall _ _
  have hBfinite : ν B ≠ ⊤ := hBcompact.measure_ne_top
  have hBmeas : MeasurableSet B := hBcompact.measurableSet
  have hindicator : Integrable
      (B.indicator (fun _ : Plane => (1 : ℝ))) ν := by
    exact (integrableOn_const (μ := ν) (s := B) (C := (1 : ℝ))
      (hs := hBfinite)).integrable_indicator hBmeas
  have hindicator_integral :
      (∫ ξ, B.indicator (fun _ : Plane => (1 : ℝ)) ξ ∂ν) = (ν B).toReal := by
    rw [integral_indicator hBmeas, setIntegral_const]
    simp [Measure.real]
  change (ν B).toReal +
    ∫ ξ, Spectral.besselJ0Angular (‖ξ‖ * ‖z‖) -
      B.indicator (fun _ : Plane => (1 : ℝ)) ξ ∂ν =
    ∫ ξ, Spectral.besselJ0Angular (‖ξ‖ * ‖z‖) ∂ν
  rw [integral_sub hJ hindicator, hindicator_integral]
  ring

/-- The reciprocal-scale Bessel inversion is bounded by the finite-ball squeeze and the
absolute exterior tail. The tail integrability is stated with the bounds. -/
theorem besselInversion_reciprocal_split_bound (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A R η : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hGrowth : ∀ s : ℝ, 1 ≤ s →
      spectralBallMass ν s ≤ A * (1 + Real.log s))
    (hDilation : ∀ u : ℝ, 1 ≤ u →
      spectralBallMass ν (R ^ 2 * u) ≤
        A * (1 + Real.log u) * spectralBallMass ν (R ^ 2)) :
    IntegrableOn (fun ξ : Plane => |Spectral.besselJ0Angular (‖ξ‖ / R)|)
        (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ ν ∧
      (1 - η ^ 2 / 2) * spectralBallMass ν (η * R) -
          (spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) -
          (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
            |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) ≤
        besselInversion ν
          (WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)) ∧
      besselInversion ν (WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)) ≤
        spectralBallMass ν (R ^ 2) +
          ∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
            |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν := by
  let z : Plane := WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)
  let C : Set Plane := Metric.closedBall (0 : Plane) (R ^ 2)
  let J : Plane → ℝ := fun ξ => Spectral.besselJ0Angular (‖ξ‖ / R)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hnormz : ‖z‖ = R⁻¹ := by
    dsimp [z]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    positivity
  have hJ : Integrable J ν := by
    simpa only [J] using integrable_besselJ0_scaled_of_logGrowth ν hA hRpos hGrowth
  have hJz : Integrable (fun ξ : Plane =>
      Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)) ν := by
    apply hJ.congr
    filter_upwards [] with ξ
    have harg : ‖ξ‖ * ‖z‖ = ‖ξ‖ / R := by
      rw [hnormz]
      field_simp [hRpos.ne']
    exact congrArg Spectral.besselJ0Angular harg.symm
  have hcomp : besselInversion ν z = ∫ ξ, J ξ ∂ν := by
    rw [besselInversion_eq_integral_besselJ0 ν z hJz]
    apply integral_congr_ae
    filter_upwards [] with ξ
    have harg : ‖ξ‖ * ‖z‖ = ‖ξ‖ / R := by
      rw [hnormz]
      field_simp [hRpos.ne']
    exact congrArg Spectral.besselJ0Angular harg
  have hball := besselJ0_integral_ball_squeeze ν hA hR hη hη1 hGrowth
  have htail := integrableOn_besselJ0_squareExterior_bound ν hA hR hGrowth hDilation
  have hCmeas : MeasurableSet C := (isCompact_closedBall (0 : Plane) (R ^ 2)).measurableSet
  have hTailmeas : MeasurableSet Cᶜ := hCmeas.compl
  have hJtail : IntegrableOn J Cᶜ ν := hJ.integrableOn.mono_set (Set.subset_univ _)
  have hAbsTail : IntegrableOn (fun ξ : Plane => |J ξ|) Cᶜ ν := by
    simpa only [J] using htail.1
  have hTailLower :
      -(∫ ξ in Cᶜ, |J ξ| ∂ν) ≤ ∫ ξ in Cᶜ, J ξ ∂ν := by
    have hmono := setIntegral_mono_on hAbsTail.neg hJtail hTailmeas
      (fun ξ _ => neg_abs_le (J ξ))
    calc
      -(∫ ξ in Cᶜ, |J ξ| ∂ν) = ∫ ξ in Cᶜ, -|J ξ| ∂ν := by rw [integral_neg]
      _ ≤ ∫ ξ in Cᶜ, J ξ ∂ν := hmono
  have hTailUpper :
      (∫ ξ in Cᶜ, J ξ ∂ν) ≤ ∫ ξ in Cᶜ, |J ξ| ∂ν := by
    exact setIntegral_mono_on hJtail hAbsTail hTailmeas
      (fun ξ _ => le_abs_self (J ξ))
  have hsplit :
      besselInversion ν z = (∫ ξ in C, J ξ ∂ν) + ∫ ξ in Cᶜ, J ξ ∂ν := by
    rw [hcomp]
    exact (integral_add_compl hCmeas hJ).symm
  have hlower :
      (1 - η ^ 2 / 2) * spectralBallMass ν (η * R) -
          (spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) -
          (∫ ξ in Cᶜ, |J ξ| ∂ν) ≤ besselInversion ν z := by
    calc
      (1 - η ^ 2 / 2) * spectralBallMass ν (η * R) -
          (spectralBallMass ν (R ^ 2) - spectralBallMass ν (η * R)) -
          (∫ ξ in Cᶜ, |J ξ| ∂ν) ≤
          (∫ ξ in C, J ξ ∂ν) + ∫ ξ in Cᶜ, J ξ ∂ν := by
            have h := add_le_add hball.2.1 hTailLower
            linarith
      _ = besselInversion ν z := hsplit.symm
  have hupper : besselInversion ν z ≤
      spectralBallMass ν (R ^ 2) + ∫ ξ in Cᶜ, |J ξ| ∂ν := by
    calc
      besselInversion ν z = (∫ ξ in C, J ξ ∂ν) + ∫ ξ in Cᶜ, J ξ ∂ν := hsplit
      _ ≤ spectralBallMass ν (R ^ 2) + ∫ ξ in Cᶜ, |J ξ| ∂ν :=
        add_le_add hball.2.2 hTailUpper
  exact ⟨htail.1, hlower, hupper⟩

/-- At reciprocal spatial radius, the Bessel inversion divided by the spectral mass at radius `R` tends to one. -/
theorem besselInversion_reciprocal_div_mass_tendsto_one (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν]
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    Tendsto (fun R =>
      besselInversion ν (WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)) /
        spectralBallMass ν R) atTop (𝓝 1) := by
  let m : ℝ → ℝ := spectralBallMass ν
  let T : ℝ → ℝ := fun R =>
    (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
      |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) / m R
  let U : ℝ → ℝ := fun R => m (R ^ 2) / m R + T R
  let L : ℝ → ℝ → ℝ := fun η R =>
    (1 - η ^ 2 / 2) * (m (η * R) / m R) -
      (m (R ^ 2) / m R - m (η * R) / m R) - T R
  let F : ℝ → ℝ := fun R =>
    besselInversion ν (WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)) / m R
  obtain ⟨Ag, hAg, hGrowth0⟩ := spectralBallMass_logGrowth_of_tendsto ν hM
  obtain ⟨D, hDilationD⟩ := spectralBallMass_logDilationBound_of_tendsto ν hM
  let A : ℝ := max Ag D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hGrowth : ∀ s : ℝ, 1 ≤ s → m s ≤ A * (1 + Real.log s) := by
    intro s hs
    have hmass := hGrowth0 s hs
    have hfactor : 0 ≤ 1 + Real.log s := by linarith [Real.log_nonneg hs]
    calc
      m s ≤ Ag * (1 + Real.log s) := hmass
      _ ≤ A * (1 + Real.log s) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hfactor
  have hpow : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  have hDilationEvent := hpow.eventually hDilationD
  have hgood : ∀ᶠ R : ℝ in atTop,
      1 ≤ R ∧ ∀ u : ℝ, 1 ≤ u →
        m (R ^ 2 * u) ≤ A * (1 + Real.log u) * m (R ^ 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hDilationEvent] with R hR hD
    refine ⟨hR, ?_⟩
    intro u hu
    have hbase := hD u hu
    have hfactor : 0 ≤ 1 + Real.log u := by linarith [Real.log_nonneg hu]
    have hmass : 0 ≤ m (R ^ 2) := ENNReal.toReal_nonneg
    have hprod : 0 ≤ (1 + Real.log u) * m (R ^ 2) := mul_nonneg hfactor hmass
    calc
      m (R ^ 2 * u) ≤ D * ((1 + Real.log u) * m (R ^ 2)) := by
        simpa [mul_assoc] using hbase
      _ ≤ A * ((1 + Real.log u) * m (R ^ 2)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hprod
      _ = A * (1 + Real.log u) * m (R ^ 2) := by ring
  have hmassPos := spectralBallMass_pos_eventually_of_tendsto ν hM
  have hratio2 := spectralBallMass_squareScale_ratio_of_tendsto ν hM
  have hTail := besselJ0_squareExterior_integral_div_mass_tendsto_zero ν hM
  have hTailT : Tendsto T atTop (𝓝 0) := by simpa [T, m] using hTail.2
  have hU : Tendsto U atTop (𝓝 1) := by
    simpa [U, T, m] using hratio2.add hTailT
  have hbounds : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ R : ℝ in atTop,
      L η R ≤ F R ∧ F R ≤ U R := by
    intro η hη hη1
    filter_upwards [hgood, hmassPos] with R hR hMR
    have hsplit := besselInversion_reciprocal_split_bound ν hA hR.1 hη hη1 hGrowth hR.2
    have hlowDiv := div_le_div_of_nonneg_right hsplit.2.1 hMR.le
    have hlowEq :
        ((1 - η ^ 2 / 2) * m (η * R) -
          (m (R ^ 2) - m (η * R)) -
          (∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
            |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν)) / m R = L η R := by
      dsimp [L, T, m]
      field_simp [hMR.ne']
    rw [hlowEq] at hlowDiv
    have hhighDiv := div_le_div_of_nonneg_right hsplit.2.2 hMR.le
    have hhighEq :
        (m (R ^ 2) +
          ∫ ξ in (Metric.closedBall (0 : Plane) (R ^ 2))ᶜ,
            |Spectral.besselJ0Angular (‖ξ‖ / R)| ∂ν) / m R = U R := by
      dsimp [U, T, m]
      field_simp [hMR.ne']
    rw [hhighEq] at hhighDiv
    exact ⟨by simpa [F, m] using hlowDiv, by simpa [F, m] using hhighDiv⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    have hgap : 0 < 1 - a := by linarith
    let η : ℝ := min 1 (Real.sqrt (1 - a))
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by norm_num) (Real.sqrt_pos.2 hgap)
    have hη1 : η ≤ 1 := by dsimp [η]; exact min_le_left _ _
    have hηsqrt : η ≤ Real.sqrt (1 - a) := by dsimp [η]; exact min_le_right _ _
    have hηsq : η ^ 2 ≤ 1 - a := by
      have habs : |η| ≤ |Real.sqrt (1 - a)| := by
        simpa [abs_of_nonneg hη.le, abs_of_nonneg (Real.sqrt_nonneg _)] using hηsqrt
      have hsq := (sq_le_sq).2 habs
      rw [Real.sq_sqrt hgap.le] at hsq
      exact hsq
    have hlimitGap : a < 1 - η ^ 2 / 2 := by nlinarith
    have hslow := spectralBallMass_slowlyVarying_of_tendsto ν η hη hM
    have hslow' : Tendsto (fun R => m (η * R) / m R) atTop (𝓝 1) := by
      apply hslow.congr'
      filter_upwards [] with R
      rw [mul_comm]
    have hL : Tendsto (L η) atTop (𝓝 (1 - η ^ 2 / 2)) := by
      have hfirst : Tendsto (fun R =>
          (1 - η ^ 2 / 2) * (m (η * R) / m R)) atTop
          (𝓝 (1 - η ^ 2 / 2)) := by
        simpa [m] using (tendsto_const_nhds.mul hslow')
      have hdiff : Tendsto (fun R => m (R ^ 2) / m R - m (η * R) / m R)
          atTop (𝓝 0) := by
        simpa [m] using hratio2.sub hslow'
      have hsub := hfirst.sub hdiff
      simpa [L, T] using hsub.sub hTailT
    have hLabove : ∀ᶠ R : ℝ in atTop, a < L η R :=
      hL.eventually (Ioi_mem_nhds hlimitGap)
    have hboundsη := hbounds η hη hη1
    filter_upwards [hLabove, hboundsη] with R hL hbound
    exact lt_of_lt_of_le hL hbound.1
  · intro b hb
    have hUbelow : ∀ᶠ R : ℝ in atTop, U R < b :=
      hU.eventually (Iio_mem_nhds hb)
    have hboundsOne := hbounds 1 (by norm_num) (by norm_num)
    filter_upwards [hUbelow, hboundsOne] with R hU hbound
    exact lt_of_le_of_lt hbound.2 hU

/-- Double-logarithmic spectral ball growth gives the sharp diagonal asymptotic of the Bessel inversion in Theorem 1.4(ii). -/
theorem besselInversion_diagonal_asymptotic_of_ballMass (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν]
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    Tendsto (fun z => besselInversion ν z / Real.log (Real.log ‖z‖⁻¹))
      (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
  let q : ℝ → Plane := fun R => WithLp.toLp 2 (![R⁻¹, 0] : Fin 2 → ℝ)
  have hmassRatio : Tendsto (fun R =>
      besselInversion ν (q R) / spectralBallMass ν R) atTop (𝓝 1) := by
    simpa only [q] using besselInversion_reciprocal_div_mass_tendsto_one ν hM
  have hmassPos := spectralBallMass_pos_eventually_of_tendsto ν hM
  have hscale : Tendsto (fun R =>
      besselInversion ν (q R) / Real.log (Real.log R)) atTop (𝓝 1) := by
    have hprod : Tendsto (fun R =>
        (besselInversion ν (q R) / spectralBallMass ν R) *
          (spectralBallMass ν R / Real.log (Real.log R))) atTop (𝓝 1) := by
      simpa only [one_mul] using hmassRatio.mul hM
    have hEq : (fun R =>
        (besselInversion ν (q R) / spectralBallMass ν R) *
          (spectralBallMass ν R / Real.log (Real.log R))) =ᶠ[atTop]
        fun R => besselInversion ν (q R) / Real.log (Real.log R) := by
      filter_upwards [hmassPos] with R hR
      field_simp [hR.ne']
    exact hprod.congr' hEq
  have hInvNorm : Tendsto (fun z : Plane => ‖z‖⁻¹)
      (nhdsWithin 0 {0}ᶜ) atTop := by
    convert tendsto_inv_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero using 1; rfl
  have hcomp := hscale.comp hInvNorm
  have hEq : (fun z : Plane =>
      besselInversion ν (q (‖z‖⁻¹)) / Real.log (Real.log (‖z‖⁻¹))) =ᶠ[nhdsWithin 0 {0}ᶜ]
      fun z => besselInversion ν z / Real.log (Real.log ‖z‖⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hqnorm : ‖q (‖z‖⁻¹)‖ = ‖z‖ := by
      dsimp [q]
      rw [EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_succ, Real.norm_eq_abs]
    rw [besselInversion_eq_of_norm ν hqnorm.symm]
  exact hcomp.congr' hEq

end Critical2DKPZ.CovarianceKernel

end
