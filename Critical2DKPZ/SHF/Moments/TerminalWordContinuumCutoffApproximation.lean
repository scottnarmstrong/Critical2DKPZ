/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitTimeWindow
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialCutoffGeometry
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Uniform continuum space-time cutoff approximation -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.DeltaBose
namespace Critical2DKPZ.SHF.Moments

private def closureRamp (η x : ℝ) : ℝ := max 0 (min 1 ((x - η) / η))
private def closureTimeWeight (τ η : ℝ) (q : ℝ × ℝ) : ℝ :=
  closureRamp η q.1 * closureRamp η q.2 * closureRamp η (τ - q.1 - q.2)

private theorem closureRamp_bounds (η x : ℝ) :
    0 ≤ closureRamp η x ∧ closureRamp η x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem closureTimeWeight_bounds (τ η : ℝ) (q : ℝ × ℝ) :
    0 ≤ closureTimeWeight τ η q ∧ closureTimeWeight τ η q ≤ 1 := by
  obtain ⟨ha, ha1⟩ := closureRamp_bounds η q.1
  obtain ⟨hb, hb1⟩ := closureRamp_bounds η q.2
  obtain ⟨hc, hc1⟩ := closureRamp_bounds η (τ - q.1 - q.2)
  exact ⟨mul_nonneg (mul_nonneg ha hb) hc,
    (mul_le_mul (mul_le_mul ha1 hb1 hb (by norm_num)) hc1 hc (by norm_num)).trans_eq (by norm_num)⟩

private theorem measurable_closureTimeWeight (τ η : ℝ) :
    Measurable (closureTimeWeight τ η) := by
  unfold closureTimeWeight closureRamp
  fun_prop

private theorem closureRamp_one {η x : ℝ} (hη : 0 < η) (hx : 2 * η ≤ x) :
    closureRamp η x = 1 := by
  have hh : 1 ≤ (x - η) / η := (le_div_iff₀ hη).mpr (by linarith only [hx])
  rw [closureRamp, min_eq_left hh, max_eq_right (by norm_num)]

private theorem closureRamp_zero {η x : ℝ} (hη : 0 < η) (hx : x ≤ η) :
    closureRamp η x = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hη.le)

private theorem closureTimeWeight_zero_outside {τ η : ℝ} (hη : 0 < η)
    (q : ℝ × ℝ) (hq : q ∉ wordInteriorTimeWindow τ (η / 2)) :
    closureTimeWeight τ η q = 0 := by
  by_cases h1 : η / 2 ≤ q.1
  · by_cases h2 : η / 2 ≤ q.2
    · have h3 : ¬ q.1 + q.2 ≤ τ - η / 2 := fun hh => hq ⟨h1, h2, hh⟩
      have hz := closureRamp_zero hη (show τ - q.1 - q.2 ≤ η by linarith only [h3, hη])
      simp only [closureTimeWeight, hz, mul_zero]
    · have hz := closureRamp_zero hη (show q.2 ≤ η by linarith only [h2, hη])
      simp only [closureTimeWeight, hz, mul_zero, zero_mul]
  · have hz := closureRamp_zero hη (show q.1 ≤ η by linarith only [h1, hη])
    simp only [closureTimeWeight, hz, zero_mul]

private theorem closure_eta_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hh := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) at hh
  simpa only [Nat.cast_add, Nat.cast_one] using hh

private theorem closureTimeWeight_eventually_one {τ : ℝ} (q : ℝ × ℝ)
    (hq : 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ) :
    ∀ᶠ n : ℕ in atTop, closureTimeWeight τ (1 / ((n : ℝ) + 1)) q = 1 := by
  have hη := closure_eta_tendsto
  have h1 := hη.eventually (Iio_mem_nhds (half_pos hq.1))
  have h2 := hη.eventually (Iio_mem_nhds (half_pos hq.2.1))
  have h3 := hη.eventually (Iio_mem_nhds (half_pos (show 0 < τ - q.1 - q.2 by linarith only [hq.2.2])))
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  unfold closureTimeWeight
  rw [closureRamp_one hp (by linarith only [hn1]), closureRamp_one hp (by linarith only [hn2]),
    closureRamp_one hp (by linarith only [hn3]), one_mul, one_mul]

private theorem measurableSet_closureSimplex (τ : ℝ) :
    MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ} := by
  exact ((isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))).measurableSet

private theorem closure_integrable_multiplier {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F b : X → ℝ} (hF : Integrable F μ)
    (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, b x ≤ 1) :
    Integrable (fun x => b x * F x) μ := by
  apply hF.bdd_mul hb.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 x)]
    exact hb1 x

private theorem closure_time_error_tendsto {P : Type*} [MeasurableSpace P]
    (ν : Measure P) [SFinite ν] (τ : ℝ)
    (F : (ℝ × ℝ) × P → ℝ)
    (hF : Integrable F ((volume.restrict
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod ν)) :
    Tendsto (fun n : ℕ => ∫ z, (1 - closureTimeWeight τ (1 / ((n : ℝ) + 1)) z.1) * ‖F z‖
      ∂((volume.restrict {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod ν))
      atTop (𝓝 0) := by
  let μ : Measure ((ℝ × ℝ) × P) := (volume.restrict
    {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod ν
  let E : ℕ → ((ℝ × ℝ) × P) → ℝ := fun n z =>
    (1 - closureTimeWeight τ (1 / ((n : ℝ) + 1)) z.1) * ‖F z‖
  have hmeas (n : ℕ) : AEStronglyMeasurable (E n) μ :=
    (measurable_const.sub ((measurable_closureTimeWeight τ _).comp measurable_fst)).aestronglyMeasurable.mul
      hF.norm.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ z ∂μ, ‖E n z‖ ≤ ‖F z‖ := by
    exact Eventually.of_forall fun z => by
      obtain ⟨ha, ha1⟩ := closureTimeWeight_bounds τ (1 / ((n : ℝ) + 1)) z.1
      change ‖(1 - closureTimeWeight τ (1 / ((n : ℝ) + 1)) z.1) * ‖F z‖‖ ≤ ‖F z‖
      rw [norm_mul, norm_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha1)]
      exact (mul_le_mul_of_nonneg_right (sub_le_self 1 ha) (norm_nonneg _)).trans_eq (one_mul _)
  have hpoint : ∀ᵐ z ∂μ, Tendsto (fun n => E n z) atTop (𝓝 0) := by
    have ht := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}) (ν := ν)).ae
      (ae_restrict_mem (measurableSet_closureSimplex τ))
    filter_upwards [ht] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [closureTimeWeight_eventually_one z.1 hz] with n hn
    simp only [E, hn, sub_self, zero_mul]
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖F z‖) (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hF.norm hpoint

private theorem closure_weighted_integral_eq {P : Type*} [MeasurableSpace P]
    (ν : Measure P) [SFinite ν] {τ η : ℝ} (hη : 0 < η)
    (F : (ℝ × ℝ) × P → ℝ) (χ : P → ℝ) (hχm : Measurable χ)
    (hχ0 : ∀ p, 0 ≤ χ p) (hχ1 : ∀ p, χ p ≤ 1)
    (hF : Integrable F ((volume.restrict
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod ν)) :
    let μ := (volume.restrict {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod ν
    Integrable (fun z => closureTimeWeight τ η z.1 * χ z.2 * F z) μ ∧
    IntegrableOn (fun q => closureTimeWeight τ η q * ∫ p, χ p * F (q, p) ∂ν)
      (wordInteriorTimeWindow τ (η / 2)) ∧
    (∫ z, closureTimeWeight τ η z.1 * χ z.2 * F z ∂μ) =
      ∫ q in wordInteriorTimeWindow τ (η / 2),
        closureTimeWeight τ η q * ∫ p, χ p * F (q, p) ∂ν := by
  dsimp only
  let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
  let G : (ℝ × ℝ) × P → ℝ := fun z => closureTimeWeight τ η z.1 * χ z.2 * F z
  have hi : Integrable G ((volume.restrict D).prod ν) :=
    closure_integrable_multiplier hF
      (((measurable_closureTimeWeight τ η).comp measurable_fst).mul (hχm.comp measurable_snd))
      (fun z => mul_nonneg (closureTimeWeight_bounds τ η z.1).1 (hχ0 z.2))
      (fun z => (mul_le_mul (closureTimeWeight_bounds τ η z.1).2 (hχ1 z.2)
        (hχ0 z.2) zero_le_one).trans_eq (one_mul _))
  have hsub : wordInteriorTimeWindow τ (η / 2) ⊆ D := by
    intro q hq
    exact ⟨(half_pos hη).trans_le hq.1, (half_pos hη).trans_le hq.2.1,
      by have hh := hq.2.2; linarith only [hh, hη]⟩
  have he (q : ℝ × ℝ) : (∫ p, G (q, p) ∂ν) =
      closureTimeWeight τ η q * ∫ p, χ p * F (q, p) ∂ν := by
    simp only [G, mul_assoc, integral_const_mul]
  have hiD : IntegrableOn (fun q => closureTimeWeight τ η q * ∫ p, χ p * F (q, p) ∂ν) D := by
    change Integrable (fun q => closureTimeWeight τ η q * ∫ p, χ p * F (q, p) ∂ν) (volume.restrict D)
    simpa only [he] using hi.integral_prod_left
  refine ⟨hi, hiD.mono_set hsub, ?_⟩
  rw [integral_prod _ hi]
  simp only [he]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_closureSimplex τ) hsub
  intro q hq
  rw [closureTimeWeight_zero_outside hη q hq.2, zero_mul]

/-- A jointly integrable signed continuum integrand is uniformly approximated
by enlarging a fixed spatial cutoff and exhausting the three time boundaries.
All weighted product and restricted iterated integrals are integrable. -/
theorem exists_wordCons_continuum_cutoff_approximation
    {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (hτ : 0 < τ)
    (F : (ℝ × ℝ) × (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (hF : Integrable F
      ((volume.restrict {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod volume)) :
    ∀ ε > 0, ∃ χ₀ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
      (∀ p, 0 ≤ χ₀ p ∧ χ₀ p ≤ 1) ∧
      (∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ₀ p ≠ 0 →
        ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
          δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) ∧
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
        (∀ p, χ₀ p ≤ χ p ∧ χ p ≤ 1) →
        let η : ℝ := 1 / ((n : ℝ) + 1)
        let a : (ℝ × ℝ) → ℝ := fun q =>
          max 0 (min 1 ((q.1 - η) / η)) * max 0 (min 1 ((q.2 - η) / η)) *
            max 0 (min 1 (((τ - q.1 - q.2) - η) / η))
        let μ := (volume.restrict
          {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod
            (volume : Measure (FusedConfiguration α × FusedConfiguration α))
        Integrable (fun z => a z.1 * χ z.2 * F z) μ ∧
        IntegrableOn (fun q => a q * ∫ p, χ p * F (q, p))
          (wordInteriorTimeWindow τ (η / 2)) ∧
        |(∫ z, F z ∂μ) -
          (∫ q in wordInteriorTimeWindow τ (η / 2), a q * ∫ p, χ p * F (q, p))| ≤ ε := by
  classical
  have hFusedSC : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have hFusedOpen : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  have hSpecVol : IsFiniteMeasureOnCompacts (volume : Measure (Spectator α → Plane)) := by infer_instance
  have hFusedVol : IsFiniteMeasureOnCompacts (volume : Measure (FusedConfiguration α)) := by infer_instance
  have hSpecFinite : SFinite (volume : Measure (Spectator α → Plane)) := by
    change SFinite (Measure.pi (fun _ : Spectator α => (volume : Measure Plane)))
    infer_instance
  have hFusedFinite : SFinite (volume : Measure (FusedConfiguration α)) := by
    change SFinite ((volume : Measure Plane).prod (volume : Measure (Spectator α → Plane)))
    infer_instance
  let P := FusedConfiguration α × FusedConfiguration α
  have hPFinite : SFinite (volume : Measure P) := by
    change SFinite ((volume : Measure (FusedConfiguration α)).prod volume)
    infer_instance
  have hPOpen : OpensMeasurableSpace P := by dsimp [P]; infer_instance
  let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
  let μ : Measure ((ℝ × ℝ) × P) := (volume.restrict D).prod volume
  let B : P → ℝ := fun p => ∫ q, ‖F (q, p)‖ ∂volume.restrict D
  have hB : Integrable B := hF.integral_norm_prod_right
  have hB0 (p : P) : 0 ≤ B p := integral_nonneg fun q => norm_nonneg _
  intro ε hε
  obtain ⟨χ₀, hχ₀, hwindow, hIχ₀, hSχ₀⟩ :=
    exists_wordSpatialCutoff_integral_small α w hw B hB hB0 (ε / 2) (half_pos hε)
  have hmχ₀ : Measurable (fun p : P => χ₀ p) := χ₀.continuous.measurable
  let S : ((ℝ × ℝ) × P) → ℝ := fun z => (1 - χ₀ z.2) * ‖F z‖
  have hiS : Integrable S μ := closure_integrable_multiplier hF.norm
    (measurable_const.sub (hmχ₀.comp measurable_snd))
    (fun z => sub_nonneg.mpr (hχ₀ z.2).2) (fun z => sub_le_self 1 (hχ₀ z.2).1)
  have hspace : (∫ z, S z ∂μ) ≤ ε / 2 := by
    have he : (∫ z, S z ∂μ) = ∫ p, B p * |1 - χ₀ p| := by
      rw [integral_prod _ hiS, integral_integral_swap hiS]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        simp only [S, integral_const_mul, B, abs_of_nonneg (sub_nonneg.mpr (hχ₀ p).2)]
        ring
    exact he ▸ hSχ₀
  have hlim := closure_time_error_tendsto (volume : Measure P) τ F hF
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (∫ z, (1 - closureTimeWeight τ (1 / ((n : ℝ) + 1)) z.1) * ‖F z‖ ∂μ) ≤ ε / 2 :=
    (hlim.eventually (Iio_mem_nhds (half_pos hε))).mono fun _ h => h.le
  have hcutoffInside := closure_eta_tendsto.eventually (Iio_mem_nhds hτ)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hsmall.and hcutoffInside)
  refine ⟨χ₀, hχ₀, hwindow, n₀, ?_⟩
  intro n hn χ hχ
  let η : ℝ := 1 / ((n : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hχ0 (p : P) : 0 ≤ χ p := (hχ₀ p).1.trans (hχ p).1
  have hχ1 (p : P) : χ p ≤ 1 := (hχ p).2
  have hmχ : Measurable (fun p : P => χ p) := χ.continuous.measurable
  obtain ⟨hiG, hiW, heq⟩ := closure_weighted_integral_eq (volume : Measure P) hη F χ hmχ hχ0 hχ1 hF
  change Integrable (fun z => closureTimeWeight τ η z.1 * χ z.2 * F z) μ ∧
    IntegrableOn (fun q => closureTimeWeight τ η q * ∫ p, χ p * F (q, p))
      (wordInteriorTimeWindow τ (η / 2)) ∧
    |(∫ z, F z ∂μ) - (∫ q in wordInteriorTimeWindow τ (η / 2),
      closureTimeWeight τ η q * ∫ p, χ p * F (q, p))| ≤ ε
  refine ⟨hiG, hiW, ?_⟩
  rw [← heq]
  let G : ((ℝ × ℝ) × P) → ℝ := fun z => closureTimeWeight τ η z.1 * χ z.2 * F z
  let E : ((ℝ × ℝ) × P) → ℝ := fun z => (1 - closureTimeWeight τ η z.1) * ‖F z‖
  have hiE : Integrable E μ := closure_integrable_multiplier hF.norm
    (measurable_const.sub ((measurable_closureTimeWeight τ η).comp measurable_fst))
    (fun z => sub_nonneg.mpr (closureTimeWeight_bounds τ η z.1).2)
    (fun z => sub_le_self 1 (closureTimeWeight_bounds τ η z.1).1)
  have hpoint (z : (ℝ × ℝ) × P) : ‖F z - G z‖ ≤ E z + S z := by
    obtain ⟨ha, ha1⟩ := closureTimeWeight_bounds τ η z.1
    have hc0 := hχ0 z.2
    have hc1 := hχ1 z.2
    have hccomp := (hχ z.2).1
    have hac : closureTimeWeight τ η z.1 * χ z.2 ≤ 1 :=
      (mul_le_mul ha1 hc1 hc0 zero_le_one).trans_eq (one_mul _)
    have hp := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1)
    have hs : 1 - closureTimeWeight τ η z.1 * χ z.2 ≤
        (1 - closureTimeWeight τ η z.1) + (1 - χ₀ z.2) := by nlinarith only [hp, hccomp]
    have he : F z - G z = (1 - closureTimeWeight τ η z.1 * χ z.2) * F z := by dsimp [G]; ring
    rw [he, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hac)]
    have hh := mul_le_mul_of_nonneg_right hs (norm_nonneg (F z))
    simpa only [E, S, add_mul] using hh
  calc
    _ = ‖∫ z, F z - G z ∂μ‖ := by rw [integral_sub hF hiG, Real.norm_eq_abs]
    _ ≤ ∫ z, ‖F z - G z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, E z + S z ∂μ := integral_mono (hF.sub hiG).norm (hiE.add hiS) hpoint
    _ = (∫ z, E z ∂μ) + (∫ z, S z ∂μ) := integral_add hiE hiS
    _ ≤ ε / 2 + ε / 2 := add_le_add (hn₀ n hn).1 hspace
    _ = ε := by ring

end Critical2DKPZ.SHF.Moments
