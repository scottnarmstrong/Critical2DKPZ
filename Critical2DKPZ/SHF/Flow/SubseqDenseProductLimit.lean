/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseProductCutoff
import Critical2DKPZ.SHF.Flow.SlabSmoothedFinite
import Mathlib.Tactic

/-! # Uniform square-moment bounds for products with spatial cutoffs -/

@[expose] public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai

/-- A compactly supported function bounded above by a constant has its integral bounded by that
constant times the measure of its compact support window. -/
theorem integral_compactProductTest_le_windowMass
    (μ ν : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν]
    (K : Set ((Plane × Plane) × (Plane × Plane))) (hK : IsCompact K)
    (F : ((Plane × Plane) × (Plane × Plane)) → ℝ)
    (hFcont : Continuous F) (hFsupport : tsupport F ⊆ K)
    {c : ℝ} (hFbound : ∀ q, F q ≤ c) :
    Integrable F (μ.prod ν) ∧
      ∫ q, F q ∂(μ.prod ν) ≤ c * (μ.prod ν).real K := by
  have hFcompact : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport F).trans hFsupport
  have hFint : Integrable F (μ.prod ν) := hFcont.integrable_of_hasCompactSupport hFcompact
  have hprodCompact : IsFiniteMeasureOnCompacts (μ.prod ν) :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
      ((Plane × Plane) × (Plane × Plane)) _ _ _ inferInstance
  have hKfinite : (μ.prod ν) K < ⊤ := hprodCompact.lt_top_of_isCompact hK
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hmajorInt : Integrable (K.indicator (fun _ => c)) (μ.prod ν) := by
    apply (integrableOn_const hKfinite.ne).integrable_indicator hKmeas
  have hmajor (q : (Plane × Plane) × (Plane × Plane)) :
      F q ≤ K.indicator (fun _ => c) q := by
    by_cases hq : q ∈ K
    · rw [Set.indicator_of_mem hq]
      exact hFbound q
    · have hzero : F q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hq (hFsupport h)
      rw [Set.indicator_of_notMem hq, hzero]
  refine ⟨hFint, ?_⟩
  calc
    ∫ q, F q ∂(μ.prod ν) ≤ ∫ q, K.indicator (fun _ => c) q ∂(μ.prod ν) :=
      integral_mono hFint hmajorInt hmajor
    _ = c * (μ.prod ν).real K := by
      simpa [Measure.real, smul_eq_mul, mul_comm] using
        (integral_indicator_const c hKmeas (μ := μ.prod ν) (s := K))

/-- A sum of square-integrable observables is square-integrable, with the elementary factor-two
bound used for cutoff and approximation errors. -/
theorem integrable_sq_add_le_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A B : Ω → ℝ}
    (hA : AEStronglyMeasurable A P) (hB : AEStronglyMeasurable B P)
    (hA2 : Integrable (fun ω => A ω ^ 2) P)
    (hB2 : Integrable (fun ω => B ω ^ 2) P) :
    Integrable (fun ω => (A ω + B ω) ^ 2) P ∧
      ∫ ω, (A ω + B ω) ^ 2 ∂P ≤
        2 * ((∫ ω, A ω ^ 2 ∂P) + ∫ ω, B ω ^ 2 ∂P) := by
  have hsumMeas : AEStronglyMeasurable (fun ω => (A ω + B ω) ^ 2) P :=
    (continuous_id.pow 2).comp_aestronglyMeasurable (hA.add hB)
  have hmajorInt : Integrable (fun ω => 2 * (A ω ^ 2 + B ω ^ 2)) P :=
    (hA2.add hB2).const_mul 2
  have hpoint (ω : Ω) : (A ω + B ω) ^ 2 ≤ 2 * (A ω ^ 2 + B ω ^ 2) := by
    nlinarith [sq_nonneg (A ω - B ω)]
  have hsumInt : Integrable (fun ω => (A ω + B ω) ^ 2) P := by
    refine hmajorInt.mono' hsumMeas ?_
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (sq_nonneg (A ω + B ω))]
    exact hpoint ω
  refine ⟨hsumInt, ?_⟩
  calc
    ∫ ω, (A ω + B ω) ^ 2 ∂P ≤ ∫ ω, 2 * (A ω ^ 2 + B ω ^ 2) ∂P :=
      integral_mono hsumInt hmajorInt hpoint
    _ = 2 * ((∫ ω, A ω ^ 2 ∂P) + ∫ ω, B ω ^ 2 ∂P) := by
      rw [integral_const_mul, integral_add hA2 hB2]

/-- The intermediate-variable cutoff is nondecreasing in its radius. -/
theorem ballCutoff_mono {R S : ℝ} (hRS : R ≤ S) (x : Plane) :
    ballCutoff R x ≤ ballCutoff S x := by
  unfold ballCutoff
  gcongr

/-- Increasing the two intermediate cutoffs increases a nonnegative compact-test pairing. -/
theorem cutoffProduct_pairing_mono
    (μ ν : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν]
    (Φ : C_c(Plane × Plane, ℝ)) (hΦ : ∀ p, 0 ≤ Φ p)
    (k : Plane → ℝ) (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x)
    {R S : ℝ} (hRS : R ≤ S) :
    ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν) ≤
      ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff S q.1.2 * ballCutoff S q.2.1 ∂(μ.prod ν) := by
  obtain ⟨KR, hKR, _, _, _, _, _, _, _, hRsupport⟩ :=
    exists_cutoffProduct_compactTensor_approximation Φ k hk R
  obtain ⟨KS, hKS, _, _, _, _, _, _, _, hSsupport⟩ :=
    exists_cutoffProduct_compactTensor_approximation Φ k hk S
  let FR : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1
  let FS : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff S q.1.2 * ballCutoff S q.2.1
  have hRcont : Continuous FR := by
    change Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1)
    have hEndpoint : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => (q.1.1, q.2.2)) := by fun_prop
    have hMiddle : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => q.1.2 - q.2.1) := by fun_prop
    have hCut₁ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff R q.1.2) :=
      (continuous_ballCutoff R).comp (by fun_prop)
    have hCut₂ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff R q.2.1) :=
      (continuous_ballCutoff R).comp (by fun_prop)
    exact (((Φ.continuous.comp hEndpoint).mul (hk.comp hMiddle)).mul hCut₁).mul hCut₂
  have hScont : Continuous FS := by
    change Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff S q.1.2 * ballCutoff S q.2.1)
    have hEndpoint : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => (q.1.1, q.2.2)) := by fun_prop
    have hMiddle : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => q.1.2 - q.2.1) := by fun_prop
    have hCut₁ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff S q.1.2) :=
      (continuous_ballCutoff S).comp (by fun_prop)
    have hCut₂ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff S q.2.1) :=
      (continuous_ballCutoff S).comp (by fun_prop)
    exact (((Φ.continuous.comp hEndpoint).mul (hk.comp hMiddle)).mul hCut₁).mul hCut₂
  have hRsupport' : tsupport FR ⊆ KR := by exact hRsupport
  have hSsupport' : tsupport FS ⊆ KS := by exact hSsupport
  have hRcompact : HasCompactSupport FR := by
    apply HasCompactSupport.of_support_subset_isCompact hKR
    exact (subset_tsupport FR).trans hRsupport'
  have hScompact : HasCompactSupport FS := by
    apply HasCompactSupport.of_support_subset_isCompact hKS
    exact (subset_tsupport FS).trans hSsupport'
  have hRint : Integrable FR (μ.prod ν) := hRcont.integrable_of_hasCompactSupport hRcompact
  have hSint : Integrable FS (μ.prod ν) := hScont.integrable_of_hasCompactSupport hScompact
  have hpoint (q : (Plane × Plane) × (Plane × Plane)) : FR q ≤ FS q := by
    have hcut₁ := ballCutoff_mono hRS q.1.2
    have hcut₂ := ballCutoff_mono hRS q.2.1
    have hbase : 0 ≤ Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) :=
      mul_nonneg (hΦ _) (hk0 _)
    have hR₂ : 0 ≤ ballCutoff R q.2.1 := (ballCutoff_mem_Icc R _).1
    have hS₁ : 0 ≤ ballCutoff S q.1.2 := (ballCutoff_mem_Icc S _).1
    dsimp [FR, FS]
    calc
      _ ≤ Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff S q.1.2 * ballCutoff R q.2.1 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcut₁ hbase) hR₂
      _ ≤ Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff S q.1.2 * ballCutoff S q.2.1 := by
        exact mul_le_mul_of_nonneg_left hcut₂ (mul_nonneg hbase hS₁)
  exact integral_mono hRint hSint hpoint

/-- Spatial monotone convergence identifies the increasing cutoff integrals with the full
nonnegative product integral. -/
theorem cutoffProduct_pairing_lintegral_tendsto
    (μ ν : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν]
    (Φ : C_c(Plane × Plane, ℝ)) (hΦ : ∀ p, 0 ≤ Φ p)
    (k : Plane → ℝ) (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x)
    (R : ℕ → ℝ) (hRmono : Monotone R)
    (hRtop : Tendsto R atTop atTop) :
    Tendsto
      (fun n => ∫⁻ q, ENNReal.ofReal
        (Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff (R n) q.1.2 * ballCutoff (R n) q.2.1) ∂(μ.prod ν))
      atTop
      (𝓝 (∫⁻ q, ENNReal.ofReal
        (Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1)) ∂(μ.prod ν))) := by
  let G : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1)
  let F : ℕ → ((Plane × Plane) × (Plane × Plane)) → ℝ := fun n q =>
    G q * ballCutoff (R n) q.1.2 * ballCutoff (R n) q.2.1
  have hGnonneg (q : (Plane × Plane) × (Plane × Plane)) : 0 ≤ G q :=
    mul_nonneg (hΦ _) (hk0 _)
  have hFnonneg (n : ℕ) (q : (Plane × Plane) × (Plane × Plane)) : 0 ≤ F n q := by
    dsimp [F]
    exact mul_nonneg (mul_nonneg (hGnonneg q) (ballCutoff_mem_Icc (R n) _).1)
      (ballCutoff_mem_Icc (R n) _).1
  have hmeas (n : ℕ) : Measurable (fun q => ENNReal.ofReal (F n q)) := by
    apply ENNReal.measurable_ofReal.comp
    have hEndpoint : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => (q.1.1, q.2.2)) := by fun_prop
    have hMiddle : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => q.1.2 - q.2.1) := by fun_prop
    have hCut₁ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff (R n) q.1.2) :=
      (continuous_ballCutoff (R n)).comp (by fun_prop)
    have hCut₂ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff (R n) q.2.1) :=
      (continuous_ballCutoff (R n)).comp (by fun_prop)
    have hGcont : Continuous G := (Φ.continuous.comp hEndpoint).mul (hk.comp hMiddle)
    have hFcont : Continuous (F n) := (((hGcont.mul hCut₁).mul hCut₂))
    exact hFcont.measurable
  have hmono : ∀ q, Monotone (fun n => ENNReal.ofReal (F n q)) := by
    intro q i j hij
    apply ENNReal.ofReal_le_ofReal
    have hcut₁ := ballCutoff_mono (hRmono hij) q.1.2
    have hcut₂ := ballCutoff_mono (hRmono hij) q.2.1
    have hbase : 0 ≤ G q := hGnonneg q
    have hcutR₂ : 0 ≤ ballCutoff (R i) q.2.1 := (ballCutoff_mem_Icc _ _).1
    have hcutS₁ : 0 ≤ ballCutoff (R j) q.1.2 := (ballCutoff_mem_Icc _ _).1
    dsimp [F]
    calc
      _ ≤ G q * ballCutoff (R j) q.1.2 * ballCutoff (R i) q.2.1 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcut₁ hbase) hcutR₂
      _ ≤ G q * ballCutoff (R j) q.1.2 * ballCutoff (R j) q.2.1 :=
        mul_le_mul_of_nonneg_left hcut₂ (mul_nonneg hbase hcutS₁)
  have hpointTendsto (q : (Plane × Plane) × (Plane × Plane)) :
      Tendsto (fun n => ENNReal.ofReal (F n q)) atTop
        (𝓝 (ENNReal.ofReal (G q))) := by
    have hcut₁ : Tendsto (fun n => ballCutoff (R n) q.1.2) atTop (𝓝 1) :=
      (tendsto_ballCutoff q.1.2).comp hRtop
    have hcut₂ : Tendsto (fun n => ballCutoff (R n) q.2.1) atTop (𝓝 1) :=
      (tendsto_ballCutoff q.2.1).comp hRtop
    have hF : Tendsto (fun n => F n q) atTop (𝓝 (G q)) := by
      dsimp [F]
      simpa only [mul_one] using
        (tendsto_const_nhds.mul hcut₁).mul hcut₂
    exact (ENNReal.continuous_ofReal.tendsto (G q)).comp hF
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := μ.prod ν)
    (fun n => (hmeas n).aemeasurable) (Filter.Eventually.of_forall hmono)
    (Filter.Eventually.of_forall hpointTendsto)
  apply h.congr
  intro n
  apply lintegral_congr_ae
  filter_upwards [] with q
  rfl

/-- Compactly cut-off products have uniformly bounded second moments along the subsequence, by domination with the fourth moments of flat marginals. -/
theorem eventually_polymerSubseq_cutoffProduct_sq_bound
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (D : Set ℝ) (ψ : ℕ → ℕ)
    (hψ : StrictMono ψ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (Φ : C_c(Plane × Plane, ℝ)) (hΦ : ∀ p, 0 ≤ Φ p)
    (k : Plane → ℝ) (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x) (R : ℝ) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => (∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
          ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
            (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2) disorderLaw ∧
      ∫ ω, (∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
          ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
            (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2 ∂disorderLaw ≤ C := by
  classical
  let cutoffTest : C_c(Plane, ℝ) :=
    ⟨⟨ballCutoff R, continuous_ballCutoff R⟩, hasCompactSupport_ballCutoff R⟩
  let Bcut : C_c(Plane × Plane, ℝ) :=
    ⟨⟨fun p => (cutoffTest p.1 * cutoffTest p.2) * k (p.1 - p.2), by fun_prop⟩,
      by
        have hc : HasCompactSupport (fun p : Plane × Plane => cutoffTest p.1 * cutoffTest p.2) :=
          (compactTensorTest cutoffTest cutoffTest).hasCompactSupport
        exact hc.mul_right⟩
  have hBnonneg (p : Plane × Plane) : 0 ≤ Bcut p := by
    have h₁ := (ballCutoff_mem_Icc R p.1).1
    have h₂ := (ballCutoff_mem_Icc R p.2).1
    dsimp [Bcut, cutoffTest]
    exact mul_nonneg (mul_nonneg h₁ h₂) (hk0 (p.1 - p.2))
  let c : ℝ := ‖Φ.toBoundedContinuousFunction‖ * ‖Bcut.toBoundedContinuousFunction‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨K, hK, _, _, _, _, _, _, _, htest_support⟩ :=
    exists_cutoffProduct_compactTensor_approximation Φ k hk R
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1
  have hFcont : Continuous F := by
    change Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1)
    have hEndpoint : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => (q.1.1, q.2.2)) := by fun_prop
    have hMiddle : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => q.1.2 - q.2.1) := by fun_prop
    have hCut₁ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff R q.1.2) :=
      (continuous_ballCutoff R).comp (by fun_prop)
    have hCut₂ : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => ballCutoff R q.2.1) :=
      (continuous_ballCutoff R).comp (by fun_prop)
    exact (((Φ.continuous.comp hEndpoint).mul (hk.comp hMiddle)).mul hCut₁).mul hCut₂
  have hFsupport : tsupport F ⊆ K := by
    exact htest_support
  have hFnonneg (q : (Plane × Plane) × (Plane × Plane)) : 0 ≤ F q := by
    dsimp [F]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hΦ _) (hk0 _))
      (ballCutoff_mem_Icc R _).1) (ballCutoff_mem_Icc R _).1
  have hFfactor (q : (Plane × Plane) × (Plane × Plane)) :
      F q = Φ (q.1.1, q.2.2) * Bcut (q.1.2, q.2.1) := by
    dsimp [F, Bcut, cutoffTest]
    ring
  have hFbound (q : (Plane × Plane) × (Plane × Plane)) : F q ≤ c := by
    rw [hFfactor q]
    have hΦnorm : Φ (q.1.1, q.2.2) ≤ ‖Φ.toBoundedContinuousFunction‖ := by
      have h := Φ.toBoundedContinuousFunction.norm_coe_le_norm (q.1.1, q.2.2)
      change |Φ (q.1.1, q.2.2)| ≤ _ at h
      exact (le_abs_self _).trans h
    have hBnorm : Bcut (q.1.2, q.2.1) ≤ ‖Bcut.toBoundedContinuousFunction‖ := by
      have h := Bcut.toBoundedContinuousFunction.norm_coe_le_norm (q.1.2, q.2.1)
      change |Bcut (q.1.2, q.2.1)| ≤ _ at h
      exact (le_abs_self _).trans h
    calc
      Φ (q.1.1, q.2.2) * Bcut (q.1.2, q.2.1) ≤
          ‖Φ.toBoundedContinuousFunction‖ * Bcut (q.1.2, q.2.1) :=
        mul_le_mul_of_nonneg_right hΦnorm (hBnonneg _)
      _ ≤ ‖Φ.toBoundedContinuousFunction‖ * ‖Bcut.toBoundedContinuousFunction‖ :=
        mul_le_mul_of_nonneg_left hBnorm (norm_nonneg _)
      _ = c := rfl
  obtain ⟨χ₀, χ₁, hχ₀, hχ₁, hmass⟩ := compact_product_mass_le_flatCutoffs K hK
  obtain ⟨C₀, hC₀⟩ := eventually_polymerSubseq_flatMarginal_fourthMoment_of
    ϑ hFlatSixthMomentInput ψ hψ (hs := hs₀) (hst := hs₀₁) χ₀ hχ₀
  obtain ⟨C₁, hC₁⟩ := eventually_polymerSubseq_flatMarginal_fourthMoment_of
    ϑ hFlatSixthMomentInput ψ hψ (hs := show 0 ≤ s₁ from hs₀.trans hs₀₁.le) (hst := hs₁₂) χ₁ hχ₁
  let s : Fin 2 → ℝ := fun i => if (i : ℕ) = 0 then s₀ else s₁
  let t : Fin 2 → ℝ := fun i => if (i : ℕ) = 0 then s₁ else s₂
  let φ : Fin 2 → C_c(Plane × Plane, ℝ) := fun _ => 0
  let χ : Fin 2 → C_c(Plane, ℝ) := fun i => if (i : ℕ) = 0 then χ₀ else χ₁
  have htimes : ∀ i : Fin 2, s i ∈ D ∧ t i ∈ D ∧ s i < t i := by
    intro i
    fin_cases i <;> simp [s, t, hs₀D, hs₁D, hs₂D, hs₀₁, hs₁₂]
  let Hflat : (Fin 2 → ℝ × ℝ) → (Fin 2 → ℝ) := fun v i => (v i).2
  have hHflat : Continuous Hflat := by fun_prop
  have hflatDist : TendstoInDistribution
      (fun n (ω : Disorder) (i : Fin 2) =>
        ∫ x, χ i x ∂((polymerMeasure ϑ (ψ n) (s i) (t i) ω).map Prod.fst))
      atTop
      (fun ω i => ∫ x, χ i x ∂((Z (s i) (t i) ω).map Prod.fst))
      (fun _ => disorderLaw) P := by
    have h := (hZ.2 2 s t htimes φ χ).continuous_comp hHflat
    apply h.congr
    · intro n
      filter_upwards [] with ω
      funext i
      simp [Hflat, s, t, φ, χ]
    · filter_upwards [] with ω
      funext i
      simp [Hflat, s, t, φ, χ]
  let U : ℕ → Disorder → ℝ := fun n ω =>
    ∫ x, χ₀ x ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).map Prod.fst)
  let V : ℕ → Disorder → ℝ := fun n ω =>
    ∫ x, χ₁ x ∂((polymerMeasure ϑ (ψ n) s₁ s₂ ω).map Prod.fst)
  let T : ℕ → Disorder → ℝ := fun n ω =>
    ∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
      (polymerMeasure ϑ (ψ n) s₁ s₂ ω))
  have hUmeas (n : ℕ) : AEMeasurable (U n) disorderLaw := by
    have h := (measurable_pi_apply (0 : Fin 2)).comp_aemeasurable
      (hflatDist.forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [U, s, t, χ])
  have hVmeas (n : ℕ) : AEMeasurable (V n) disorderLaw := by
    have h := (measurable_pi_apply (1 : Fin 2)).comp_aemeasurable
      (hflatDist.forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [V, s, t, χ])
  have hU4int : ∀ᶠ n : ℕ in atTop, Integrable (fun ω => U n ω ^ 4) disorderLaw := by
    filter_upwards [hC₀] with n hn
    simpa [U] using hn.1
  have hV4int : ∀ᶠ n : ℕ in atTop, Integrable (fun ω => V n ω ^ 4) disorderLaw := by
    filter_upwards [hC₁] with n hn
    simpa [V] using hn.1
  have hU4bound : ∀ᶠ n : ℕ in atTop,
      ∫ ω, U n ω ^ 4 ∂disorderLaw ≤ C₀ := by
    filter_upwards [hC₀] with n hn
    simpa [U] using hn.2
  have hV4bound : ∀ᶠ n : ℕ in atTop,
      ∫ ω, V n ω ^ 4 ∂disorderLaw ≤ C₁ := by
    filter_upwards [hC₁] with n hn
    simpa [V] using hn.2
  have hTdist := polymerSubseqLimit_cutoffProduct_joint_tendstoInDistribution
    ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ Φ k hk R
  have hTmeas (n : ℕ) : AEMeasurable (T n) disorderLaw := by
    have h := measurable_fst.comp_aemeasurable (hTdist.forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [T, F])
  have hpoint (n : ℕ) (ω : Disorder) : T n ω ≤ c * (U n ω * V n ω) := by
    let μ := polymerMeasure ϑ (ψ n) s₀ s₁ ω
    let ν := polymerMeasure ϑ (ψ n) s₁ s₂ ω
    have hμ : IsLocallyFiniteMeasure μ :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₀ s₁ ω
    have hν : IsLocallyFiniteMeasure ν :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₁ s₂ ω
    have hFintbound := @integral_compactProductTest_le_windowMass μ ν hμ hν
      K hK F hFcont hFsupport c hFbound
    have hmass' : (μ.prod ν).real K ≤ U n ω * V n ω := by
      have h := @hmass μ ν (inferInstance : IsLocallyFiniteMeasure ν)
        (isLocallyFiniteMeasure_polymerMarginal ϑ (ψ n) s₀ s₁ ω)
        (isLocallyFiniteMeasure_polymerMarginal ϑ (ψ n) s₁ s₂ ω)
      simpa [μ, ν, U, V] using h
    have hcmass := mul_le_mul_of_nonneg_left hmass' hc
    change (∫ q, F q ∂(μ.prod ν)) ≤ c * (U n ω * V n ω)
    exact hFintbound.2.trans hcmass
  refine ⟨c ^ 2 * (C₀ + C₁), ?_⟩
  filter_upwards [hU4int.and hV4int, hU4bound.and hV4bound] with n hnInt hnBound
  have hU4 : Integrable (fun ω => U n ω ^ 4) disorderLaw := hnInt.1
  have hV4 : Integrable (fun ω => V n ω ^ 4) disorderLaw := hnInt.2
  have hT2meas : AEStronglyMeasurable (fun ω => T n ω ^ 2) disorderLaw :=
    (continuous_id.pow 2).comp_aestronglyMeasurable (hTmeas n).aestronglyMeasurable
  have hmajorInt : Integrable (fun ω => c ^ 2 * (U n ω ^ 4 + V n ω ^ 4)) disorderLaw :=
    (hU4.add hV4).const_mul (c ^ 2)
  have hT2int : Integrable (fun ω => T n ω ^ 2) disorderLaw := by
    refine hmajorInt.mono' hT2meas ?_
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (sq_nonneg (T n ω))]
    have hU0 : 0 ≤ U n ω := integral_nonneg fun x => hχ₀ x
    have hV0 : 0 ≤ V n ω := integral_nonneg fun x => hχ₁ x
    have hT0 : 0 ≤ T n ω := by
      dsimp [T]
      exact integral_nonneg hFnonneg
    have hB0 : 0 ≤ c * (U n ω * V n ω) := by positivity
    have hsquare : (T n ω) ^ 2 ≤ (c * (U n ω * V n ω)) ^ 2 := by
      nlinarith [hpoint n ω]
    have hYoung : U n ω ^ 2 * V n ω ^ 2 ≤ U n ω ^ 4 + V n ω ^ 4 := by
      nlinarith [sq_nonneg (U n ω ^ 2 - V n ω ^ 2)]
    calc
      (T n ω) ^ 2 ≤ (c * (U n ω * V n ω)) ^ 2 := hsquare
      _ = c ^ 2 * (U n ω ^ 2 * V n ω ^ 2) := by ring
      _ ≤ c ^ 2 * (U n ω ^ 4 + V n ω ^ 4) :=
        mul_le_mul_of_nonneg_left hYoung (sq_nonneg c)
  refine ⟨hT2int, ?_⟩
  calc
    ∫ ω, T n ω ^ 2 ∂disorderLaw ≤
        ∫ ω, c ^ 2 * (U n ω ^ 4 + V n ω ^ 4) ∂disorderLaw := by
      apply integral_mono hT2int hmajorInt
      intro ω
      have hU0 : 0 ≤ U n ω := integral_nonneg fun x => hχ₀ x
      have hV0 : 0 ≤ V n ω := integral_nonneg fun x => hχ₁ x
      have hT0 : 0 ≤ T n ω := by
        dsimp [T]
        exact integral_nonneg hFnonneg
      have hsquare : (T n ω) ^ 2 ≤ (c * (U n ω * V n ω)) ^ 2 := by
        nlinarith [hpoint n ω]
      have hYoung : U n ω ^ 2 * V n ω ^ 2 ≤ U n ω ^ 4 + V n ω ^ 4 := by
        nlinarith [sq_nonneg (U n ω ^ 2 - V n ω ^ 2)]
      calc
        (T n ω) ^ 2 ≤ (c * (U n ω * V n ω)) ^ 2 := hsquare
        _ = c ^ 2 * (U n ω ^ 2 * V n ω ^ 2) := by ring
        _ ≤ c ^ 2 * (U n ω ^ 4 + V n ω ^ 4) :=
          mul_le_mul_of_nonneg_left hYoung (sq_nonneg c)
    _ = c ^ 2 * (∫ ω, U n ω ^ 4 ∂disorderLaw +
        ∫ ω, V n ω ^ 4 ∂disorderLaw) := by
      rw [integral_const_mul, integral_add hU4 hV4]
    _ ≤ c ^ 2 * (C₀ + C₁) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hnBound.1 hnBound.2) (sq_nonneg c)

end Critical2DKPZ.SHF.Flow

end
