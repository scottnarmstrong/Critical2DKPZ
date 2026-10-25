/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.PointMatchedComparison
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Tactic

/-! # The small-scale central limit theorem for the KPZ process -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

private theorem eLpNorm_one_le_of_integral_abs {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (B : ℝ) (hf : Integrable f P)
    (hB : ∫ ω, |f ω| ∂P ≤ B) : eLpNorm f 1 P ≤ ENNReal.ofReal B := by
  calc
    eLpNorm f 1 P = ENNReal.ofReal (∫ ω, ‖f ω‖ ∂P) := by
      rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm hf]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hB)

private theorem testFn_eq_zero_of_nonneg_integral_zero (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ0 : ∫ y, φ y = 0) : ∀ y, φ y = 0 := by
  have hφint : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  intro y
  by_contra hy
  have hypos : 0 < φ y := lt_of_le_of_ne (hφ y) (Ne.symm hy)
  have hySupport : y ∈ Function.support φ := Function.mem_support.mpr hy
  have hSupportPos : 0 < (volume : Measure Plane) (Function.support φ) :=
    IsOpen.measure_pos volume φ.continuous.isOpen_support ⟨y, hySupport⟩
  have hIntegralPos : 0 < ∫ y, φ y :=
    (integral_pos_iff_support_of_nonneg hφ hφint).2 hSupportPos
  linarith

/-- For a nonnegative test function, the shrinking KPZ pairing divided by the square root of the double logarithm of inverse scale converges to a centered Gaussian with variance equal to the squared test mass. -/
theorem criticalKPZ_smallScaleCLT_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC8 : SmallScaleSHFLogNormality.{u})
    (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (x : Plane) (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y) :
    TendstoInDistribution
      (fun ε ω => H t 0 ω (φ.dilate ε x) / Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (gaussianReal 0 ((∫ y, φ y) ^ 2).toNNReal) := by
  let m : ℝ := ∫ y, φ y
  have hmNonneg : 0 ≤ m := integral_nonneg hφ
  by_cases hm0 : m = 0
  · have hφzero := testFn_eq_zero_of_nonneg_integral_zero φ hφ (by simpa [m] using hm0)
    have hDilZero (ε : ℝ) : φ.dilate ε x = 0 := by
      ext y
      simp [TestFn.dilate, hφzero]
    let D : ℝ → ℝ := fun ε => Real.sqrt (Real.log (Real.log ε⁻¹))
    let base : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
    have hconst : TendstoInDistribution (fun _ : ℝ => fun _ : Ω => (0 : ℝ)) base
        id (fun _ => P) (gaussianReal 0 0) := by
      apply tendstoInDistribution_of_identDistrib (i := 0)
      · intro ε
        exact IdentDistrib.refl aemeasurable_const
      · refine ⟨aemeasurable_const, aemeasurable_id, ?_⟩
        simp [gaussianReal_zero_var]
    have hsource : ∀ ε : ℝ,
        (fun ω => H t 0 ω (φ.dilate ε x) / D ε) =ᵐ[P] fun _ => (0 : ℝ) := by
      intro ε
      filter_upwards [] with ω
      rw [hDilZero ε, map_zero]
      simp
    have hzero := TendstoInDistribution.congr (fun ε => (hsource ε).symm)
      (Filter.Eventually.of_forall fun _ => rfl) hconst
    simpa [m, D, hm0] using hzero
  · have hmpos : 0 < m := by
      have hmne : (0 : ℝ) ≠ m := Ne.symm hm0
      exact lt_of_le_of_ne hmNonneg hmne
    let ψ : TestFn := m⁻¹ • φ
    have hψnonneg : ∀ y, 0 ≤ ψ y := by
      intro y
      change 0 ≤ m⁻¹ * φ y
      exact mul_nonneg (le_of_lt (inv_pos.mpr hmpos)) (hφ y)
    have hψmass : ∫ y, ψ y = 1 := by
      calc
        ∫ y, ψ y = ∫ y, m⁻¹ * φ y := by simp [ψ]
        _ = m⁻¹ * ∫ y, φ y := integral_const_mul _ _
        _ = 1 := by simp [m, hmpos.ne']
    let S : Set ℝ := Set.Ioo 0 (Real.sqrt t)
    let base : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
    let ℓ : Filter S := Filter.comap (Subtype.val : S → ℝ) base
    let D : ℝ → ℝ := fun ε => Real.sqrt (Real.log (Real.log ε⁻¹))
    let F : S → Plane → Ω → ℝ := fun ε y ω =>
      heatStartLog Z ((ε : ℝ) ^ 2) t ((ε : ℝ) ^ 2) y ω
    let b : S → Plane := fun ε => x + (ε : ℝ) • barycentre ψ
    let G : S → Ω → ℝ := fun ε ω => F ε (b ε) ω - ∫ ω', F ε (b ε) ω' ∂P
    have hRange : Set.range (Subtype.val : S → ℝ) ∈ base := by
      rw [Subtype.range_val]
      change Set.Ioo (0 : ℝ) (Real.sqrt t) ∈ nhdsWithin 0 (Set.Ioi 0)
      have hupper : ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0), y < Real.sqrt t :=
        (show ∀ᶠ y : ℝ in 𝓝 0, y < Real.sqrt t from
          eventually_lt_nhds (Real.sqrt_pos.mpr ht)).filter_mono nhdsWithin_le_nhds
      filter_upwards [eventually_mem_nhdsWithin, hupper]
        with y hylo hyhi
      exact ⟨hylo, hyhi⟩
    have hmapFilter : Filter.map (Subtype.val : S → ℝ) ℓ = base :=
      Filter.map_comap_of_mem hRange
    have hℓNeBot : NeBot ℓ := by
      have hmapped : NeBot (Filter.map (Subtype.val : S → ℝ) ℓ) := by
        rw [hmapFilter]
        infer_instance
      exact Filter.NeBot.of_map hmapped
    let : NeBot ℓ := hℓNeBot
    have hval : Tendsto (fun ε : S => (ε : ℝ)) ℓ base := Filter.tendsto_comap
    have hvalNhd : Tendsto (fun ε : S => (ε : ℝ)) ℓ (𝓝 0) :=
      hval.mono_right nhdsWithin_le_nhds
    have hinv : Tendsto (fun ε : S => (ε : ℝ)⁻¹) ℓ atTop :=
      tendsto_inv_nhdsGT_zero.comp hval
    have hlog1 : Tendsto (fun ε : S => Real.log (ε : ℝ)⁻¹) ℓ atTop :=
      Real.tendsto_log_atTop.comp hinv
    have hlog2 : Tendsto (fun ε : S => Real.log (Real.log (ε : ℝ)⁻¹)) ℓ atTop :=
      Real.tendsto_log_atTop.comp hlog1
    have hD : Tendsto (fun ε : S => D (ε : ℝ)) ℓ atTop :=
      Real.tendsto_sqrt_atTop.comp hlog2
    have hDpos : ∀ᶠ ε : S in ℓ, 0 < D (ε : ℝ) := hD.eventually_gt_atTop 0
    have hεsqT (ε : S) : (ε : ℝ) ^ 2 < t := by
      have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
      have hsum : 0 < (ε : ℝ) + Real.sqrt t := add_pos ε.2.1 hsqrt
      have hprod : 0 < (Real.sqrt t - (ε : ℝ)) * ((ε : ℝ) + Real.sqrt t) :=
        mul_pos (sub_pos.mpr ε.2.2) hsum
      have hsqrtSq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
      nlinarith
    obtain ⟨C, εc, hεc, hcmp⟩ := kpz_point_matched_comparison_of ϑ P Z hZ hsym hC12
      hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput H hH ht ψ hψnonneg hψmass x
    have hsmall : ∀ᶠ ε : S in ℓ, (ε : ℝ) < εc :=
      (hval.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds hεc)
    let X : S → Ω → ℝ := fun ε =>
      if he : (ε : ℝ) < εc then
        Classical.choose (hcmp (ε : ℝ) ε.2.1 he)
      else fun ω => H t 0 ω (ψ.dilate (ε : ℝ) x)
    have hXspec (ε : S) (he : (ε : ℝ) < εc) :
        P.map (X ε) = P.map (fun ω => H t 0 ω (ψ.dilate (ε : ℝ) x)) ∧
          Integrable (fun ω => X ε ω - G ε ω) P ∧
          ∫ ω, |X ε ω - G ε ω| ∂P ≤ C := by
      simpa only [X, dite_eq_left he, F, b, G] using Classical.choose_spec (hcmp (ε : ℝ) ε.2.1 he)
    have hCnonneg : 0 ≤ C := by
      obtain ⟨ε, hε⟩ := hsmall.exists
      have hspec := hXspec ε hε
      exact (integral_nonneg (fun ω => abs_nonneg (X ε ω - G ε ω))).trans hspec.2.2
    have hRawIntegrable (ε : S) (y : Plane) : Integrable (F ε y) P := by
      exact heatStartLog_integrable_of ϑ P Z hZ (le_of_lt (sq_pos_of_pos ε.2.1))
        (hεsqT ε) (sq_pos_of_pos ε.2.1) y
    have hGint (ε : S) : Integrable (G ε) P := by
      exact (hRawIntegrable ε (b ε)).sub (integrable_const _)
    have hHae (χ : TestFn) : AEMeasurable (fun ω => H t 0 ω χ) P :=
      aemeasurable_isCriticalKPZ_of ϑ P Z hZ ht H hH χ
    have hXae (ε : S) : AEMeasurable (X ε) P := by
      by_cases he : (ε : ℝ) < εc
      · have hspec := hXspec ε he
        have hsum : Integrable (fun ω => (X ε ω - G ε ω) + G ε ω) P :=
          hspec.2.1.add (hGint ε)
        have hXint : Integrable (X ε) P := by
          apply hsum.congr
          filter_upwards [] with ω
          ring
        exact hXint.aemeasurable
      · simpa [X, he] using hHae (ψ.dilate (ε : ℝ) x)
    let Y : S → Ω → ℝ := fun ε ω => X ε ω / D (ε : ℝ)
    let V : S → Ω → ℝ := fun ε ω => G ε ω / D (ε : ℝ)
    have hYae (ε : S) : AEMeasurable (Y ε) P := (hXae ε).div_const _
    have hVae (ε : S) : AEMeasurable (V ε) P := (hGint ε).aemeasurable.div_const _
    have herrorLp : Tendsto (fun ε : S => eLpNorm (fun ω => Y ε ω - V ε ω) 1 P)
        ℓ (𝓝 0) := by
      have hupper : Tendsto (fun ε : S => ENNReal.ofReal (C / D (ε : ℝ))) ℓ (𝓝 0) := by
        have hratio : Tendsto (fun ε : S => C / D (ε : ℝ)) ℓ (𝓝 0) :=
          tendsto_const_nhds.div_atTop hD
        change Tendsto (ENNReal.ofReal ∘ fun ε : S => C / D (ε : ℝ)) ℓ (𝓝 0)
        simpa only [ENNReal.ofReal_zero] using
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp hratio
      have hbound : ∀ᶠ ε : S in ℓ,
          eLpNorm (fun ω => Y ε ω - V ε ω) 1 P ≤ ENNReal.ofReal (C / D (ε : ℝ)) := by
        filter_upwards [hsmall, hDpos] with ε hεsmall hεD
        have hspec := hXspec ε hεsmall
        have hdiff := hspec.2.1
        have hdiffBound := hspec.2.2
        have hdiffLp := eLpNorm_one_le_of_integral_abs P (fun ω => X ε ω - G ε ω)
          C hdiff hdiffBound
        have heq : (fun ω => Y ε ω - V ε ω) =
            fun ω => (D (ε : ℝ))⁻¹ • (X ε ω - G ε ω) := by
          funext ω
          simp [Y, V, smul_eq_mul, div_eq_mul_inv]
          ring
        rw [heq]
        change eLpNorm ((D (ε : ℝ))⁻¹ • (fun ω => X ε ω - G ε ω)) 1 P ≤ _
        rw [eLpNorm_const_smul]
        calc
              ‖(D (ε : ℝ))⁻¹‖ₑ * eLpNorm (fun ω => X ε ω - G ε ω) 1 P ≤
              ‖(D (ε : ℝ))⁻¹‖ₑ * ENNReal.ofReal C :=
            mul_le_mul_of_nonneg_left hdiffLp (bot_le)
          _ = ENNReal.ofReal (C / D (ε : ℝ)) := by
            rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hεD)]
            rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hεD.le)]
            congr 1
            field_simp
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
        (Filter.Eventually.of_forall fun ε =>
          (bot_le : (0 : ℝ≥0∞) ≤ eLpNorm (fun ω => Y ε ω - V ε ω) 1 P))
        hbound
    have herror : TendstoInMeasure P (fun ε ω => Y ε ω - V ε ω) ℓ 0 := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      simpa only [Pi.zero_apply, sub_zero] using herrorLp
    have hvalX (ε : S) (ω : Ω) :
        H t 0 ω (φ.dilate (ε : ℝ) x) = m * H t 0 ω (ψ.dilate (ε : ℝ) x) := by
      have hprofile : φ.dilate (ε : ℝ) x = m • ψ.dilate (ε : ℝ) x := by
        ext y
        simp [TestFn.dilate, ψ, smul_eq_mul]
        field_simp [hmpos.ne']
      rw [hprofile, map_smul, smul_eq_mul]
    have hrawH (ε : S) (y : Plane) :
        IdentDistrib (F ε y) (F ε 0) P P :=
      heatStartLog_identDistrib_of ϑ P Z hZ hsym (le_of_lt (sq_pos_of_pos ε.2.1))
        (hεsqT ε) (sq_pos_of_pos ε.2.1) y
    let Gx : S → Ω → ℝ := fun ε ω => F ε x ω - ∫ ω', F ε x ω' ∂P
    let Vx : S → Ω → ℝ := fun ε ω => Gx ε ω / D (ε : ℝ)
    have hVlaw (ε : S) : IdentDistrib (V ε) (Vx ε) P P := by
      have hB := hrawH ε (b ε)
      have hX := hrawH ε x
      have hmeanB : ∫ ω, F ε (b ε) ω ∂P = ∫ ω, F ε 0 ω ∂P := hB.integral_eq
      have hmeanX : ∫ ω, F ε x ω ∂P = ∫ ω, F ε 0 ω ∂P := hX.integral_eq
      let c : ℝ := ∫ ω, F ε 0 ω ∂P
      have hBc : IdentDistrib (fun ω => F ε (b ε) ω - c)
          (fun ω => F ε 0 ω - c) P P := by
        simpa only [Function.comp_def] using
          hB.comp (u := fun z : ℝ => z - c) (by fun_prop)
      have hXc : IdentDistrib (fun ω => F ε x ω - c)
          (fun ω => F ε 0 ω - c) P P := by
        simpa only [Function.comp_def] using
          hX.comp (u := fun z : ℝ => z - c) (by fun_prop)
      have hGcommon : IdentDistrib (G ε) (fun ω => F ε 0 ω - c) P P := by
        have heq : (fun ω => F ε (b ε) ω - c) =ᵐ[P] G ε := by
          filter_upwards [] with ω
          simp [G, c, hmeanB]
        exact (IdentDistrib.of_ae_eq hBc.aemeasurable_fst heq).symm.trans hBc
      have hXcommon : IdentDistrib (Gx ε) (fun ω => F ε 0 ω - c) P P := by
        have heq : (fun ω => F ε x ω - c) =ᵐ[P] Gx ε := by
          filter_upwards [] with ω
          simp [Gx, c, hmeanX]
        exact (IdentDistrib.of_ae_eq hXc.aemeasurable_fst heq).symm.trans hXc
      have hcenter : IdentDistrib (G ε) (Gx ε) P P := hGcommon.trans hXcommon.symm
      simpa only [Function.comp_def] using
        hcenter.comp (u := fun z : ℝ => z / D (ε : ℝ)) (by fun_prop)
    have hVclt : TendstoInDistribution V ℓ id (fun _ => P) (gaussianReal 0 1) := by
      refine ⟨hVae, aemeasurable_id, ?_⟩
      have hprob : (fun ε : S =>
          (⟨P.map (V ε), inferInstance⟩ : ProbabilityMeasure ℝ)) =ᶠ[ℓ]
          fun ε => (⟨P.map (Vx ε), inferInstance⟩ : ProbabilityMeasure ℝ) := by
        filter_upwards [] with ε
        exact Subtype.ext (hVlaw ε).map_eq
      exact Tendsto.congr' hprob.symm (heatStartLog_logNormality_of ϑ P Z hZ hsym hC8 ht x).tendsto
    have hYclt : TendstoInDistribution Y ℓ id (fun _ => P) (gaussianReal 0 1) :=
      tendstoInDistribution_of_tendstoInMeasure_sub (X := V) Y id hVclt herror hYae
    let mY : S → Ω → ℝ := fun ε ω => m * Y ε ω
    have hmYclt : TendstoInDistribution mY ℓ (fun z => m * z) (fun _ => P)
        (gaussianReal 0 1) := hYclt.continuous_comp (g := fun z : ℝ => m * z) (by fun_prop)
    have hgauss : (gaussianReal 0 1).map (fun z : ℝ => m * z) =
        gaussianReal 0 (m ^ 2).toNNReal := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · ring
      · apply NNReal.eq
        simp [Real.toNNReal_of_nonneg (sq_nonneg m)]
    let Q : S → Ω → ℝ := fun ε ω => H t 0 ω (φ.dilate (ε : ℝ) x) / D (ε : ℝ)
    have hQae (ε : S) : AEMeasurable (Q ε) P := (hHae (φ.dilate (ε : ℝ) x)).div_const _
    have hQlaw : ∀ᶠ ε : S in ℓ,
        P.map (mY ε) = P.map (Q ε) := by
      filter_upwards [hsmall] with ε hεsmall
      have hspec := hXspec ε hεsmall
      let q : ℝ → ℝ := fun z => m * z / D (ε : ℝ)
      have hq : Measurable q := by fun_prop
      have hXmap : (P.map (X ε)).map q = P.map (fun ω => q (X ε ω)) := by
        simpa only [Function.comp_def, q] using
          (AEMeasurable.map_map_of_aemeasurable hq.aemeasurable (hXae ε))
      have hHmap : (P.map (fun ω => H t 0 ω (ψ.dilate (ε : ℝ) x))).map q =
          P.map (fun ω => q (H t 0 ω (ψ.dilate (ε : ℝ) x))) := by
        simpa only [Function.comp_def, q] using
          (AEMeasurable.map_map_of_aemeasurable hq.aemeasurable
            (hHae (ψ.dilate (ε : ℝ) x)))
      calc
        P.map (mY ε) = P.map (fun ω => q (X ε ω)) := by
          apply Measure.map_congr
          filter_upwards [] with ω
          simp [mY, Y, q]
          ring
        _ = (P.map (X ε)).map q := hXmap.symm
        _ = (P.map (fun ω => H t 0 ω (ψ.dilate (ε : ℝ) x))).map q := by rw [hspec.1]
        _ = P.map (fun ω => q (H t 0 ω (ψ.dilate (ε : ℝ) x))) := hHmap
        _ = P.map (Q ε) := by
          apply Measure.map_congr
          filter_upwards [] with ω
          simp [q, Q, hvalX ε ω]
    have hQsub : TendstoInDistribution Q ℓ id (fun _ => P)
        (gaussianReal 0 (m ^ 2).toNNReal) := by
      refine ⟨hQae, aemeasurable_id, ?_⟩
      have hprob : (fun ε : S =>
          (⟨P.map (Q ε), inferInstance⟩ : ProbabilityMeasure ℝ)) =ᶠ[ℓ]
          fun ε => (⟨P.map (mY ε), inferInstance⟩ : ProbabilityMeasure ℝ) := by
        filter_upwards [hQlaw] with ε hε
        exact Subtype.ext hε.symm
      have htend := Tendsto.congr' hprob.symm hmYclt.tendsto
      have htarget :
          (⟨Measure.map (fun z : ℝ => m * z) (gaussianReal 0 1), inferInstance⟩ :
            ProbabilityMeasure ℝ) =
          (⟨gaussianReal 0 (m ^ 2).toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ) :=
        Subtype.ext hgauss
      rw [htarget] at htend
      have hmapId :
          (⟨Measure.map id (gaussianReal 0 (m ^ 2).toNNReal), inferInstance⟩ :
            ProbabilityMeasure ℝ) =
          (⟨gaussianReal 0 (m ^ 2).toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ) :=
        Subtype.ext Measure.map_id
      rw [hmapId]
      exact htend
    let Qreal : ℝ → Ω → ℝ := fun ε ω => H t 0 ω (φ.dilate ε x) / D ε
    have hQrealAe (ε : ℝ) : AEMeasurable (Qreal ε) P :=
      (hHae (φ.dilate ε x)).div_const _
    let qreal : ℝ → ProbabilityMeasure ℝ := fun ε => ⟨P.map (Qreal ε), inferInstance⟩
    have hqsub : Tendsto (fun ε : S => qreal (ε : ℝ)) ℓ
        (𝓝 ⟨gaussianReal 0 (m ^ 2).toNNReal, inferInstance⟩) := by
      simpa [qreal, Qreal, Q, D] using hQsub.tendsto
    have hqreal : Tendsto qreal base
        (𝓝 ⟨gaussianReal 0 (m ^ 2).toNNReal, inferInstance⟩) := by
      rw [← hmapFilter, tendsto_map'_iff]
      exact hqsub
    refine ⟨hQrealAe, aemeasurable_id, ?_⟩
    simpa only [Measure.map_id] using hqreal

end Critical2DKPZ.SmallScales

end

end
