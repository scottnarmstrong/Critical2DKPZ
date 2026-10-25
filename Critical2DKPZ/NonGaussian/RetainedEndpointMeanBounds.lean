/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.LaterComparisonRetainedMass
public import Critical2DKPZ.NonGaussian.CompactHeatLogMean
public import Critical2DKPZ.NonGaussian.CompactHeatEhrhard
public import Critical2DKPZ.NonGaussian.FlatHeatStartRatio
public import Critical2DKPZ.NonGaussian.ConditionalHeatStart
public import Critical2DKPZ.NonGaussian.LaterComparisonEndpointBound
public import Critical2DKPZ.NonGaussian.LaterComparisonLogRatios
public import Critical2DKPZ.SmallScales.Inputs
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-! Retained endpoint pairings satisfy positive mean bounds and conditional upper bounds. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Tsai Critical2DKPZ.SmallScales
open scoped BoundedContinuousFunction CompactlySupported Topology

namespace Critical2DKPZ.NonGaussian

universe u

/-- A nonzero nonnegative compact terminal test retains uniformly positive expected normalized endpoint mass when the flat two-horizon ratio is bounded below. -/
theorem retained_endpoint_pairing_mean_lower_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) (K : Set Plane) (hK : IsCompact K)
    (φ : C_c(Plane, ℝ)) (hφ : ∀ y, 0 ≤ φ y ∧ φ y ≤ 1) (hφne : φ ≠ 0) :
    ∃ a c r₀ : ℝ, 0 < a ∧ a < 1 ∧ 0 < c ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∀ x ∈ K,
        let R : Ω → ℝ :=
          fun ω => shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
            shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω
        let X : Ω → ℝ := fun ω => endpointPairing Z r t x φ ω
        Integrable (Set.indicator {ω | a ≤ R ω} X) P ∧
        c ≤ ∫ ω, Set.indicator {ω | a ≤ R ω} X ω ∂P := by
  obtain ⟨CR, rR, hrR, hRatio⟩ :=
    heatStart_log_ratio_integrable_lower_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense ht
  obtain ⟨Cc, rC, hrC, hCompact⟩ :=
    heatStartLog_mean_ge_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense ht φ hφ hφne
      K hK
  obtain ⟨Cf, rF, hrF, hFlat⟩ :=
    heatStartLog_mean_asymp_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense
      (τ₀ := t / 2) (τ₁ := t) (by positivity)
  let C : ℝ := |CR|
  let D : ℝ := |Cc| + |Cf|
  let r₀ : ℝ := min rR (min rC (min rF (t / 3)))
  let a : ℝ := Real.exp (-(2 * (1 + C) * Real.exp D))
  let c : ℝ := Real.exp (-D) - (1 + C) / (2 * (1 + C) * Real.exp D)
  have hr₀ : 0 < r₀ := lt_min hrR (lt_min hrC (lt_min hrF (by positivity)))
  have hMass (r : ℝ) (hr : 0 < r) (hrr₀ : r < r₀) (x : Plane) (hx : x ∈ K) :
      let R : Ω → ℝ := fun ω =>
        shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
          shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω
      let X : Ω → ℝ := fun ω => endpointPairing Z r t x φ ω
      Integrable (Set.indicator {ω | a ≤ R ω} X) P ∧
        c ≤ ∫ ω, Set.indicator {ω | a ≤ R ω} X ω ∂P := by
    let A : Ω → ℝ := fun ω =>
      shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω
    let A₀ : Ω → ℝ := fun ω =>
      shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω
    let V : Ω → ℝ := fun ω => shfPairing Z r t (fun y => heatKernel r (y - x)) φ ω
    let R : Ω → ℝ := fun ω => A ω / A₀ ω
    let X : Ω → ℝ := fun ω => endpointPairing Z r t x φ ω
    have hrrR : r < rR := hrr₀.trans_le (min_le_left _ _)
    have hrrC : r < rC := hrr₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hrrF : r < rF := hrr₀.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hrt : r < t / 3 := hrr₀.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hrtT : r < t := hrt.trans (by linarith [ht])
    have hdurLo : t / 2 ≤ t - r := by linarith
    have hdurHi : t - r ≤ t := by linarith
    have hVlog := hCompact r hr hrrC x hx
    have hAlog := hFlat r t r hr.le hdurLo hdurHi hr hrrF x
    have hRatioNow := hRatio r hr hrrR x
    have hMoment := integral_heatStart_div_le_one_of ϑ P Z hZ hsym hdense
      (r := r) (s := t / 3) (t := t) (δ := r) hr.le hrt
      (show t / 3 < t by linarith [ht]) hr x
    have hApos : ∀ᵐ ω ∂P, 0 < A ω := by
      have h := hsym.2.2.2.2.2.2 r t r x (0 : Plane →ᵇ ℝ) hr.le hrtT hr
      simpa only [A, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h.1
    have hA₀pos : ∀ᵐ ω ∂P, 0 < A₀ ω := by
      have h := hsym.2.2.2.2.2.2 r (t / 3) r x (0 : Plane →ᵇ ℝ) hr.le hrt hr
      simpa only [A₀, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h.1
    have hVpos : ∀ᵐ ω ∂P, 0 < V ω := by
      have h := heatStart_cc_pairing_pos_isEhrhardType ϑ P Z hZ hr.le hrtT hr x φ
        (fun y => (hφ y).1) hφne
      simpa only [V] using h.1
    have hXpackage := endpointPairing_between_zero_and_one_of ϑ P Z hZ hsym hr hrtT x φ hφ
    have hXint : Integrable X P := by simpa only [X] using hXpackage.2
    have hXle : X ≤ᵐ[P] fun _ => 1 := by
      filter_upwards [hXpackage.1] with ω hω
      exact hω.2
    have hXpos : ∀ᵐ ω ∂P, 0 < X ω := by
      filter_upwards [hVpos, hApos] with ω hV hA
      change 0 < V ω / A ω
      exact div_pos hV hA
    have hLogXeq : (fun ω => Real.log (X ω)) =ᵐ[P]
        fun ω => Real.log (V ω) - Real.log (A ω) := by
      filter_upwards [hVpos, hApos] with ω hV hA
      change Real.log (V ω / A ω) = _
      exact Real.log_div hV.ne' hA.ne'
    have hLogX : Integrable (fun ω => Real.log (X ω)) P :=
      (hVlog.1.sub hAlog.1).congr hLogXeq.symm
    have hLogXintegral : (∫ ω, Real.log (X ω) ∂P) =
        (∫ ω, Real.log (V ω) ∂P) - ∫ ω, Real.log (A ω) ∂P := by
      calc
        _ = ∫ ω, (Real.log (V ω) - Real.log (A ω)) ∂P := integral_congr_ae hLogXeq
        _ = _ := integral_sub hVlog.1 hAlog.1
    have hVlower : -(1 / 2) * Real.log (Real.log r⁻¹) - Cc ≤
        ∫ ω, Real.log (V ω) ∂P := by simpa only [V] using hVlog.2
    have hAupper : (∫ ω, Real.log (A ω) ∂P) +
        (1 / 2) * Real.log (Real.log r⁻¹) ≤ Cf := (abs_le.mp hAlog.2).2
    have hXlogmean : -D ≤ ∫ ω, Real.log (X ω) ∂P := by
      rw [hLogXintegral]
      dsimp [D]
      linarith [hVlower, hAupper, le_abs_self Cc, le_abs_self Cf]
    have hRint : Integrable R P := by simpa only [R, A, A₀] using hMoment.1
    have hRmean : (∫ ω, R ω ∂P) ≤ 1 := by
      simpa only [R, A, A₀] using hMoment.2
    have hRlog : Integrable (fun ω => Real.log (R ω)) P := by
      simpa only [R, A, A₀] using hRatioNow.1
    have hRlogmean : -C ≤ ∫ ω, Real.log (R ω) ∂P := by
      have hbound : -CR ≤ ∫ ω, Real.log (R ω) ∂P := by
        simpa only [R, A, A₀] using hRatioNow.2
      dsimp [C]
      exact (neg_le_neg (le_abs_self CR)).trans hbound
    have hRmeas : Measurable R := by
      let f : Plane → ℝ := fun y => heatKernel r (y - x)
      let η : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
      have hf : Measurable f := (measurable_heatKernel r).comp
        (measurable_id.sub measurable_const)
      have hPair : Measurable (fun ν : Measure (Plane × Plane) => ∫ p, f p.1 ∂ν) :=
        ((hf.comp measurable_fst).stronglyMeasurable.integral_kernel (κ := η)).measurable
      have hAmeas : Measurable A := by
        have h := hPair.comp (hZ.1 r t hr.le hrtT)
        convert h using 1
        ext ω
        simp [A, shfPairing, f]
      have hA₀meas : Measurable A₀ := by
        have h := hPair.comp (hZ.1 r (t / 3) hr.le hrt)
        convert h using 1
        ext ω
        simp [A₀, shfPairing, f]
      exact hAmeas.div hA₀meas
    have hRpos : ∀ᵐ ω ∂P, 0 < R ω := by
      filter_upwards [hApos, hA₀pos] with ω hA hA₀
      exact div_pos hA hA₀
    have hMass' := retained_mass_lower_of_log_bounds P R X C D
      (by dsimp [C]; positivity) hRmeas hRpos hRint hRmean hRlog hRlogmean
      hXpos hXle hXint hLogX hXlogmean
    have hMassPayload := hMass'.2.2.2
    simpa [R, X, A, A₀, a, c, C, D] using hMassPayload
  have hMass' : 0 < a ∧ a < 1 ∧ 0 < c := by
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have ha : 0 < a := Real.exp_pos _
    have ha1 : a < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have : 0 < 2 * (1 + C) * Real.exp D := by positivity
      linarith
    have hq : (1 + C) / (2 * (1 + C) * Real.exp D) = Real.exp (-D) / 2 := by
      rw [Real.exp_neg]
      field_simp [ne_of_gt (show 0 < 1 + C by linarith)]
    have hc : 0 < c := by
      rw [show c = Real.exp (-D) - (1 + C) / (2 * (1 + C) * Real.exp D) by rfl, hq]
      nlinarith [Real.exp_pos (-D)]
    exact ⟨ha, ha1, hc⟩
  refine ⟨a, c, r₀, hMass'.1, hMass'.2.1, hMass'.2.2, hr₀, ?_⟩
  intro r hr hrr₀ x hx
  exact hMass r hr hrr₀ x hx

/-- The conditional expectation of a retained compact endpoint pairing is bounded by a constant multiple of the later stochastic heat flow pairing. -/
theorem condExp_retained_endpoint_pairing_le_of (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hdense : DenseSHFAt ϑ P Z)
    {t r a : ℝ} (hr : 0 < r) (hrt : r < t / 3)
    (ha : 0 < a) (x : Plane) (g : C_c(Plane, ℝ))
    (hg : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    let R : Ω → ℝ := fun ω =>
      shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
        shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω
    let X : Ω → ℝ := fun ω => endpointPairing Z r t x g ω
    P[fun ω => Set.indicator {ω | a ≤ R ω} X ω |
      MeasurableSpace.comap (Z r (t / 3)) inferInstance ⊔
        MeasurableSpace.comap (Z (2 * t / 3) t) inferInstance]
      ≤ᵐ[P] fun ω => ((2 * Real.pi * (t / 3))⁻¹ / a) *
        shfPairing Z (2 * t / 3) t (fun _ => 1) g ω := by
  let A : Ω → ℝ := fun ω => shfPairing Z r t
    (fun y => heatKernel r (y - x)) (fun _ => 1) ω
  let A₀ : Ω → ℝ := fun ω => shfPairing Z r (t / 3)
    (fun y => heatKernel r (y - x)) (fun _ => 1) ω
  let V : Ω → ℝ := fun ω => shfPairing Z r t
    (fun y => heatKernel r (y - x)) g ω
  let R : Ω → ℝ := fun ω => A ω / A₀ ω
  let X : Ω → ℝ := fun ω => endpointPairing Z r t x g ω
  let W : Ω → ℝ := fun ω => Set.indicator {ω | a ≤ R ω} X ω
  let Y : Ω → ℝ := fun ω => V ω / A₀ ω
  have hmid : t / 3 < 2 * t / 3 := by linarith
  have hlast : 2 * t / 3 < t := by linarith
  have hrtT : r < t := by nlinarith [hr, hrt]
  let ambient : MeasurableSpace Ω := inferInstance
  have hData := condExp_heatStart_div_le_of ϑ P Z hZ hsym hdense
    (r := r) (s := t / 3) (t := 2 * t / 3) (u := t) (δ := r)
    (by positivity : 0 ≤ r) hrt hmid hlast hr x g hg
  have hYint : Integrable Y P := by
    simpa only [Y, V, A₀] using hData.1
  let m : MeasurableSpace Ω := MeasurableSpace.comap (Z r (t / 3)) inferInstance ⊔
    MeasurableSpace.comap (Z (2 * t / 3) t) inferInstance
  let : MeasurableSpace Ω := ambient
  have hmidEq : 2 * t / 3 - t / 3 = t / 3 := by ring
  have hApos : ∀ᵐ ω ∂P, 0 < A ω := by
    have h := hsym.2.2.2.2.2.2 r t r x (0 : Plane →ᵇ ℝ)
      (by positivity : 0 ≤ r) hrtT hr
    simpa only [A, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h.1
  have hA₀pos : ∀ᵐ ω ∂P, 0 < A₀ ω := by
    have h := hsym.2.2.2.2.2.2 r (t / 3) r x (0 : Plane →ᵇ ℝ)
      (by positivity : 0 ≤ r) hrt hr
    simpa only [A₀, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h.1
  have hRmeas : Measurable R := by
    let f : Plane → ℝ := fun y => heatKernel r (y - x)
    let η : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
    have hf : Measurable f := (measurable_heatKernel r).comp
      (measurable_id.sub measurable_const)
    have hIntegrand : Measurable (fun p : Plane × Plane => f p.1 * (1 : ℝ)) :=
      (hf.comp measurable_fst).mul_const 1
    have hPair : Measurable (fun ν : Measure (Plane × Plane) =>
        ∫ p, f p.1 * (1 : ℝ) ∂ν) :=
      (hIntegrand.stronglyMeasurable.integral_kernel (κ := η)).measurable
    have hAmeas : Measurable A := by
      have h := hPair.comp (hZ.1 r t (by positivity) hrtT)
      change Measurable (fun ω => ∫ p, f p.1 * (1 : ℝ) ∂Z r t ω)
      exact h
    have hA₀meas : Measurable A₀ := by
      have h := hPair.comp (hZ.1 r (t / 3) (by positivity) hrt)
      change Measurable (fun ω => ∫ p, f p.1 * (1 : ℝ) ∂Z r (t / 3) ω)
      exact h
    exact hAmeas.div hA₀meas
  have hXpackage := endpointPairing_between_zero_and_one_of ϑ P Z hZ hsym
    (r := r) (t := t) hr hrtT x g (fun y => ⟨hg y, hg1 y⟩)
  have hXint : Integrable X P := by simpa only [X] using hXpackage.2
  have hXnonneg : 0 ≤ᵐ[P] X := by
    filter_upwards [hXpackage.1] with ω hω
    exact hω.1
  have hWset : MeasurableSet {ω | a ≤ R ω} := measurableSet_le measurable_const hRmeas
  have hWint : Integrable W P := by
    exact hXint.indicator hWset
  have hVnonneg : ∀ ω, 0 ≤ V ω := fun ω => integral_nonneg fun p =>
    mul_nonneg (heatKernel_nonneg hr.le (p.1 - x)) (hg p.2)
  have hYnonneg : 0 ≤ᵐ[P] Y := by
    filter_upwards [hA₀pos] with ω hA₀
    exact div_nonneg (hVnonneg ω) hA₀.le
  have hWle : W ≤ᵐ[P] fun ω => Y ω / a := by
    filter_upwards [hApos, hA₀pos, hXnonneg, hYnonneg] with ω hA hA₀ hX hY
    by_cases hEvent : a ≤ R ω
    · have hXeq : X ω = V ω / A ω := by rfl
      have hYeq : Y ω = R ω * X ω := by
        change V ω / A₀ ω = (A ω / A₀ ω) * (V ω / A ω)
        field_simp [ne_of_gt hA, ne_of_gt hA₀]
      change Set.indicator {ω | a ≤ R ω} X ω ≤ Y ω / a
      have hWval : Set.indicator {ω | a ≤ R ω} X ω = X ω :=
        by simp [Set.indicator, hEvent]
      rw [hWval]
      rw [le_div_iff₀ ha]
      rw [hYeq]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hEvent hX
    · change Set.indicator {ω | a ≤ R ω} X ω ≤ Y ω / a
      have hWval : Set.indicator {ω | a ≤ R ω} X ω = 0 :=
        by simp [Set.indicator, hEvent]
      rw [hWval]
      exact div_nonneg hY ha.le
  have hYcond : P[Y | m] ≤ᵐ[P] fun ω =>
      (2 * Real.pi * (t / 3))⁻¹ * shfPairing Z (2 * t / 3) t (fun _ => 1) g ω := by
    simpa only [Y, V, A₀, m, hmidEq] using hData.2
  have hRetained := condExp_retained_ratio_le_of P m a
    ((2 * Real.pi * (t / 3))⁻¹) W Y
    (fun ω => shfPairing Z (2 * t / 3) t (fun _ => 1) g ω)
    ha hWint hYint hWle hYcond
  simpa only [W, R, X, m] using hRetained

end Critical2DKPZ.NonGaussian

end
