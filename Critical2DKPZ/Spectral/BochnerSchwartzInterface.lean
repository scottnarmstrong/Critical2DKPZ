/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.BochnerSchwartzGrowth
public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The Bochner--Schwartz measure in angular frequency -/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory
open Filter
open TopologicalSpace
open scoped CompactlySupported FourierTransform Topology

namespace Critical2DKPZ.Spectral

/-- The spectral measure in the paper's angular-frequency variable. `fourierCccRieszMeasure`
uses Mathlib's `2π`-normalized Fourier transform, so this pushforward converts cyclic frequency
to the convention `f̂(ξ) = ∫ exp(-i ξ·x) f(x) dx`. -/
noncomputable def fourierKPZRieszMeasure (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ f : TestFn, 0 ≤ ∫ p : Plane × Plane,
      f p.1 * f p.2 * C (p.1 - p.2)) : Measure Plane :=
  (fourierCccRieszMeasure C hC hgrowth heven hpos).map angularFrequencyEquiv.symm

/-- The angular-frequency Riesz measure is locally finite. -/
theorem fourierKPZRieszMeasure_isLocallyFinite (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ f : TestFn, 0 ≤ ∫ p : Plane × Plane,
      f p.1 * f p.2 * C (p.1 - p.2)) :
    IsLocallyFiniteMeasure (fourierKPZRieszMeasure C hC hgrowth heven hpos) := by
  let μ := fourierCccRieszMeasure C hC hgrowth heven hpos
  have hμ : IsLocallyFiniteMeasure μ :=
    fourierCccRieszMeasure_isLocallyFinite C hC hgrowth heven hpos
  refine ⟨fun x => ?_⟩
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have hK' : IsCompact (angularFrequencyEquiv.symm ⁻¹' K) :=
    angularFrequencyEquiv.symm.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr hK
  refine ⟨K, hxK, ?_⟩
  change (μ.map angularFrequencyEquiv.symm) K < ⊤
  rw [Measure.map_apply angularFrequencyEquiv.symm.continuous.measurable hK.measurableSet]
  letI : IsLocallyFiniteMeasure μ := hμ
  exact hK'.measure_lt_top

/-- The angular-frequency Riesz measure has polynomial ball growth. -/
theorem fourierKPZRieszMeasure_polynomial_ball_growth (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ f : TestFn, 0 ≤ ∫ p : Plane × Plane,
      f p.1 * f p.2 * C (p.1 - p.2)) :
    ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      ((fourierKPZRieszMeasure C hC hgrowth heven hpos)
        (Metric.closedBall 0 R)).toReal ≤ A * R ^ k := by
  obtain ⟨A, k, hA⟩ := fourierCccRieszMeasure_polynomial_ball_growth
    C hC hgrowth heven hpos
  refine ⟨A, k, fun R hR => ?_⟩
  let μ := fourierCccRieszMeasure C hC hgrowth heven hpos
  have hpre : angularFrequencyEquiv.symm ⁻¹' Metric.closedBall (0 : Plane) R ⊆
      Metric.closedBall (0 : Plane) R := by
    intro ξ hξ
    change angularFrequencyEquiv.symm ξ ∈ Metric.closedBall (0 : Plane) R at hξ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hξ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hscale : angularFrequencyEquiv.symm ξ = (2 * Real.pi) • ξ := by
      have hm : angularFrequencyEquiv ((2 * Real.pi) • ξ) = ξ := by
        change (2 * Real.pi)⁻¹ • ((2 * Real.pi) • ξ) = ξ
        rw [smul_smul]
        have hc : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := by
          field_simp
        rw [hc, one_smul]
      exact angularFrequencyEquiv.injective
        ((angularFrequencyEquiv.apply_symm_apply ξ).trans hm.symm)
    rw [hscale, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (show 0 < 2 * Real.pi by positivity))] at hξ
    have hfactor : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    nlinarith [norm_nonneg ξ, mul_le_mul_of_nonneg_right hfactor (norm_nonneg ξ)]
  rw [fourierKPZRieszMeasure, Measure.map_apply angularFrequencyEquiv.symm.continuous.measurable
    Metric.isClosed_closedBall.measurableSet]
  have hmono : μ (angularFrequencyEquiv.symm ⁻¹' Metric.closedBall (0 : Plane) R) ≤
      μ (Metric.closedBall (0 : Plane) R) := measure_mono hpre
  have hfinite : μ (Metric.closedBall (0 : Plane) R) ≠ ⊤ := by
    letI : IsLocallyFiniteMeasure μ :=
      fourierCccRieszMeasure_isLocallyFinite C hC hgrowth heven hpos
    exact (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne
  have hmonoReal := ENNReal.toReal_mono hfinite hmono
  exact hmonoReal.trans (hA R hR)

/-- A Schwartz function multiplied by a locally square-integrable, polynomially growing kernel is
integrable. -/
theorem integrable_kernel_mul_schwartz (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (g : SchwartzMap Plane ℂ) :
    Integrable (fun x : Plane => (C x : ℂ) * g x) volume := by
  let μ := absoluteKernelMeasure C
  letI : μ.HasTemperateGrowth := absoluteKernelMeasure_hasTemperateGrowth C hC hgrowth
  have hg : Integrable g μ := SchwartzMap.integrable (μ := μ) g
  have hloc := locallyIntegrable_of_compactMemLp_two C hC
  have hρ : AEMeasurable (fun x : Plane => ENNReal.ofReal |C x|) volume := by
    exact hloc.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  have hρtop : ∀ᵐ x : Plane ∂volume, ENNReal.ofReal |C x| < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hweighted : Integrable
      (fun x : Plane => (ENNReal.ofReal |C x|).toReal • g x) volume := by
    have hg' : Integrable g (volume.withDensity (fun x : Plane => ENNReal.ofReal |C x|)) := by
      simpa [μ, absoluteKernelMeasure] using hg
    exact (integrable_withDensity_iff_integrable_smul₀' hρ hρtop).mp hg'
  have hmeas : AEStronglyMeasurable
      (fun x : Plane => (C x : ℂ) * g x) volume := by
    exact (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      hloc.aestronglyMeasurable).mul g.continuous.aestronglyMeasurable
  refine hweighted.norm.mono' hmeas ?_
  filter_upwards with x
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_smul,
    Real.norm_eq_abs, ENNReal.toReal_ofReal (abs_nonneg (C x)),
    abs_of_nonneg (abs_nonneg (C x))]

/-- Compose a real smooth compactly supported test with a linear isometry. -/
def testFnCompLinearIsometry (R : Plane ≃ₗᵢ[ℝ] Plane) (f : TestFn) : TestFn where
  toFun := f ∘ R.toHomeomorph
  contDiff' := f.contDiff.comp R.contDiff
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph R.toHomeomorph
  tsupport_subset' := fun _ _ => trivial


/-- Mathlib's Fourier transform of the composed test is the original transform composed with the
same isometry. -/
theorem fourier_testFnCompLinearIsometry (R : Plane ≃ₗᵢ[ℝ] Plane)
    (f : TestFn) (ξ : Plane) :
    (𝓕 (testFnToSchwartzMap (testFnCompLinearIsometry R f))) ξ =
      (𝓕 (testFnToSchwartzMap f)) (R ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  change 𝓕 (fun x : Plane => ((f (R x) : ℝ) : ℂ)) ξ =
    𝓕 (fun x : Plane => ((f x : ℝ) : ℂ)) (R ξ)
  exact Real.fourier_comp_linearIsometry R (fun x : Plane => (f x : ℂ)) ξ

/-- The positive Fourier functional is invariant under isometries preserving the kernel almost
everywhere. -/
theorem fourierTestLinearMap_comp_linearIsometry (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ r : ℝ, 1 ≤ r →
      (∫ z in Metric.closedBall 0 r, |C z|) ≤ A * r ^ k)
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hrot : (fun z : Plane => C (R z)) =ᵐ[volume] C) (f : TestFn) :
    fourierTestLinearMap C hC hgrowth (testFnCompLinearIsometry R f) =
      fourierTestLinearMap C hC hgrowth f := by
  let F : SchwartzMap Plane ℂ := 𝓕 (testFnToSchwartzMap f)
  have hInt : Integrable (fun x : Plane => (C x : ℂ) * F x) volume :=
    integrable_kernel_mul_schwartz C hC hgrowth F
  have hrotInv : (fun x : Plane => C (R.symm x)) =ᵐ[volume] C := by
    have h := hrot.comp_tendsto
      (LinearIsometryEquiv.measurePreserving R.symm).quasiMeasurePreserving.tendsto_ae
    simpa only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] using h.symm
  have hIntInv : Integrable
      (fun x : Plane => (C (R.symm x) : ℂ) * F x) volume := by
    apply hInt.congr
    filter_upwards [hrotInv] with x hx
    rw [hx]
  let G : Plane → ℂ := fun x => (C (R.symm x) : ℂ) * F x
  have _hG : Integrable G volume := hIntInv
  have hchange : (∫ x : Plane, G (R x)) = ∫ x : Plane, G x := by
    simpa only [Homeomorph.coe_toEquiv] using
      (LinearIsometryEquiv.measurePreserving R).integral_comp
        R.toHomeomorph.measurableEmbedding G
  have hpoint (x : Plane) :
      (C x : ℂ) * (𝓕 (testFnToSchwartzMap (testFnCompLinearIsometry R f))) x =
        G (R x) := by
    rw [fourier_testFnCompLinearIsometry]
    simp [G, F]
  have hleft :
      (∫ x : Plane, (C x : ℂ) *
        (𝓕 (testFnToSchwartzMap (testFnCompLinearIsometry R f))) x) =
      ∫ x : Plane, G (R x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact hpoint x
  have hright : (∫ x : Plane, G x) =
      ∫ x : Plane, (C x : ℂ) * F x := by
    apply integral_congr_ae
    filter_upwards [hrotInv] with x hx
    simp [G, hx]
  change ((𝓕 (kernelTemperedDistribution C hC hgrowth)
    (testFnToSchwartzMap (testFnCompLinearIsometry R f))).re) =
      ((𝓕 (kernelTemperedDistribution C hC hgrowth)
        (testFnToSchwartzMap f)).re)
  rw [fourier_kernelTemperedDistribution_apply_schwartz,
    fourier_kernelTemperedDistribution_apply_schwartz]
  exact congrArg Complex.re (hleft.trans (hchange.trans hright))

/-- Compose a compactly supported continuous function with a plane isometry. -/
def cccCompLinearIsometry (R : Plane ≃ₗᵢ[ℝ] Plane) (f : C_c(Plane, ℝ)) :
    C_c(Plane, ℝ) := f.comp R.toHomeomorph.toCocompactMap


/-- The compactly supported continuous extension of the positive Fourier functional is invariant
under isometries preserving the kernel almost everywhere. -/
theorem fourierCccValue_comp_linearIsometry (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ r : ℝ, 1 ≤ r →
      (∫ z in Metric.closedBall 0 r, |C z|) ≤ A * r ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hrot : (fun z : Plane => C (R z)) =ᵐ[volume] C) (f : C_c(Plane, ℝ)) :
    fourierCccValue C hC hgrowth (cccCompLinearIsometry R f) =
      fourierCccValue C hC hgrowth f := by
  let k := Classical.choose (exists_localizer_uniform_testFn_approx f)
  let χ : TestFn := Critical2DKPZ.localizer k
  have hχ : IsCompact (tsupport χ) := χ.hasCompactSupport.isCompact
  let K : Set Plane := R.toHomeomorph ⁻¹' tsupport χ
  have hK : IsCompact K := R.toHomeomorph.isCompact_preimage.mpr hχ
  let ψ : ℕ → TestFn := uniformTestApproxSequence f
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hs (n : ℕ) : tsupport (ψ n) ⊆ tsupport χ := by
    simpa [ψ, χ, k] using uniformTestApproxSequence_support f n
  have hψsupport (n : ℕ) :
      tsupport (testFnCompLinearIsometry R (ψ n)) ⊆ K := by
    change tsupport ((ψ n) ∘ R.toHomeomorph) ⊆ K
    rw [tsupport_comp_eq_preimage (ψ n) R.toHomeomorph]
    exact Set.preimage_mono (hs n)
  have hψapprox (n : ℕ) (x : Plane) :
      |testFnCompLinearIsometry R (ψ n) x - cccCompLinearIsometry R f x| ≤ e n := by
    change |ψ n (R x) - f (R x)| ≤ e n
    exact (uniformTestApproxSequence_error f n (R x)).le
  have hleft := tendsto_fourierTestValue_of_uniform_approx C hC hgrowth heven hpos
    (cccCompLinearIsometry R f) (fun n => testFnCompLinearIsometry R (ψ n)) K hK
    hψsupport e he hψapprox
  have hright := tendsto_fourierTestApproxValues C hC hgrowth heven hpos f
  have hright' : Tendsto
      (fun n => fourierTestLinearMap C hC hgrowth
        (testFnCompLinearIsometry R (ψ n))) atTop
      (𝓝 (fourierCccValue C hC hgrowth f)) := by
    simpa only [fourierTestLinearMap_comp_linearIsometry C hC hgrowth R hrot]
      using hright
  exact tendsto_nhds_unique hleft hright'

/-- The Riesz measure is invariant under every linear isometry preserving the kernel almost
everywhere. -/
theorem fourierCccRieszMeasure_map_linearIsometry (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ r : ℝ, 1 ≤ r →
      (∫ z in Metric.closedBall 0 r, |C z|) ≤ A * r ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hrot : (fun z : Plane => C (R z)) =ᵐ[volume] C) :
    (fourierCccRieszMeasure C hC hgrowth heven hpos).map R =
      fourierCccRieszMeasure C hC hgrowth heven hpos := by
  let ν := fourierCccRieszMeasure C hC hgrowth heven hpos
  have hνInt (g : C_c(Plane, ℝ)) :
      (∫ x : Plane, g x ∂ν) = fourierCccValue C hC hgrowth g := by
    change (∫ x : Plane, g x ∂
      RealRMK.rieszMeasure (fourierCccPositiveLinearMap C hC hgrowth heven hpos)) = _
    rw [RealRMK.integral_rieszMeasure]
    rfl
  have hhomeo : ν.map R.toHomeomorph = ν := by
    letI : ν.Regular := by
      dsimp [ν, fourierCccRieszMeasure]
      infer_instance
    letI : (ν.map R.toHomeomorph).Regular := Measure.Regular.map R.toHomeomorph
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    calc
      (∫ x : Plane, g x ∂ν.map R.toHomeomorph) =
          ∫ x : Plane, g (R.toHomeomorph x) ∂ν :=
        R.toHomeomorph.measurableEmbedding.integral_map g
      _ = ∫ x : Plane, cccCompLinearIsometry R g x ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        rfl
      _ = fourierCccValue C hC hgrowth (cccCompLinearIsometry R g) :=
        hνInt (cccCompLinearIsometry R g)
      _ = fourierCccValue C hC hgrowth g :=
        fourierCccValue_comp_linearIsometry C hC hgrowth heven hpos R hrot g
      _ = ∫ x : Plane, g x ∂ν := (hνInt g).symm
  have hfun : (R : Plane → Plane) = R.toHomeomorph := by
    funext x
    rfl
  change ν.map (R : Plane → Plane) = ν
  rw [hfun]
  exact hhomeo

/-- The angular-frequency Riesz measure is invariant under every linear isometry preserving the
kernel almost everywhere. -/
theorem fourierKPZRieszMeasure_map_linearIsometry (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ r : ℝ, 1 ≤ r →
      (∫ z in Metric.closedBall 0 r, |C z|) ≤ A * r ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hrot : (fun z : Plane => C (R z)) =ᵐ[volume] C) :
    (fourierKPZRieszMeasure C hC hgrowth heven hpos).map R =
      fourierKPZRieszMeasure C hC hgrowth heven hpos := by
  let μ := fourierCccRieszMeasure C hC hgrowth heven hpos
  have hscale (ξ : Plane) : angularFrequencyEquiv.symm ξ = (2 * Real.pi) • ξ := by
    have hm : angularFrequencyEquiv ((2 * Real.pi) • ξ) = ξ := by
      change (2 * Real.pi)⁻¹ • ((2 * Real.pi) • ξ) = ξ
      rw [smul_smul]
      have hc : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := by field_simp
      rw [hc, one_smul]
    exact angularFrequencyEquiv.injective
      ((angularFrequencyEquiv.apply_symm_apply ξ).trans hm.symm)
  have hcomm : (fun ξ : Plane => R (angularFrequencyEquiv.symm ξ)) =
      fun ξ => angularFrequencyEquiv.symm (R ξ) := by
    funext ξ
    rw [hscale ξ, hscale (R ξ), map_smul]
  have hcyc := fourierCccRieszMeasure_map_linearIsometry
    C hC hgrowth heven hpos R hrot
  change (μ.map angularFrequencyEquiv.symm).map R = μ.map angularFrequencyEquiv.symm
  calc
    (μ.map angularFrequencyEquiv.symm).map R =
        μ.map (R ∘ angularFrequencyEquiv.symm) :=
      Measure.map_map R.continuous.measurable angularFrequencyEquiv.symm.continuous.measurable
    _ = μ.map (angularFrequencyEquiv.symm ∘ R) :=
      congrArg (fun f : Plane → Plane => μ.map f) hcomm
    _ = (μ.map R).map angularFrequencyEquiv.symm :=
      (Measure.map_map angularFrequencyEquiv.symm.continuous.measurable
        R.continuous.measurable).symm
    _ = μ.map angularFrequencyEquiv.symm := by rw [hcyc]

end Critical2DKPZ.Spectral

end
