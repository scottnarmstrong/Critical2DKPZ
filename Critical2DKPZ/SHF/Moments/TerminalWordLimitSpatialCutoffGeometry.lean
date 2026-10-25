/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedSample
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitUniformSpatialBound
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSamplePotential
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-! # Compact spatial windows away from the next collision diagonal -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

private theorem continuous_fused_collision_coordinate {h : ℕ} (α : CollisionPair h) (i : Fin h) :
    Continuous (fun p : FusedConfiguration α => collisionEmbedding α p i) := by
  unfold collisionEmbedding
  split_ifs <;> fun_prop

/-- A bounded spatial window separated from the next word diagonal. -/
def wordSpatialSeparatedWindow {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (R δ : ℝ) : Set (FusedConfiguration α × FusedConfiguration α) :=
  {p | ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
    δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖}

/-- Separation windows are closed, including for the empty tail word. -/
theorem isClosed_wordSpatialSeparatedWindow {h : ℕ} (α : CollisionPair h)
    (w : List (CollisionPair h)) (R δ : ℝ) :
    IsClosed (wordSpatialSeparatedWindow α w R δ) := by
  have hc (β : CollisionPair h) : Continuous (fun p : FusedConfiguration α × FusedConfiguration α =>
      ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) :=
    (((continuous_fused_collision_coordinate α β.1.2).comp continuous_snd).sub
      ((continuous_fused_collision_coordinate α β.1.1).comp continuous_snd)).norm
  have hnorm : Continuous (fun p : FusedConfiguration α × FusedConfiguration α => ‖p‖) :=
    continuous_norm
  have hball : IsClosed {p : FusedConfiguration α × FusedConfiguration α | ‖p‖ ≤ R} :=
    isClosed_le hnorm continuous_const
  cases w with
  | nil => simpa [wordSpatialSeparatedWindow] using hball
  | cons β w =>
      have hgap : IsClosed {p : FusedConfiguration α × FusedConfiguration α |
          δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖} :=
        isClosed_le continuous_const (hc β)
      simpa [wordSpatialSeparatedWindow, Set.ofPred_and] using hball.inter hgap

/-- Separation windows are compact in the finite-dimensional fused space. -/
theorem isCompact_wordSpatialSeparatedWindow {h : ℕ} (α : CollisionPair h)
    (w : List (CollisionPair h)) (R δ : ℝ) :
    IsCompact (wordSpatialSeparatedWindow α w R δ) := by
  have : ProperSpace (FusedConfiguration α) := by infer_instance
  apply (isCompact_closedBall (0 : FusedConfiguration α × FusedConfiguration α) R).of_isClosed_subset
    (isClosed_wordSpatialSeparatedWindow α w R δ)
  intro p hp
  simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1

/-- The next word diagonal is negligible in the full pair of fused spaces. -/
theorem ae_wordSpatial_next_gap_pos {h : ℕ} (α : CollisionPair h)
    (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·)) :
    ∀ᵐ p : FusedConfiguration α × FusedConfiguration α,
      ∀ β ∈ w.head?, 0 < ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖ := by
  have hv : ∀ᵐ v : FusedConfiguration α,
      ∀ β ∈ w.head?, collisionEmbedding α v β.1.1 ≠ collisionEmbedding α v β.1.2 := by
    cases w with
    | nil => filter_upwards with v; simp
    | cons β w =>
      have hab : α ≠ β := (List.isChain_cons_cons.mp hw).1
      simpa using ae_collisionEmbedding_pair_ne α β hab
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (FusedConfiguration α)))
    (ν := (volume : Measure (FusedConfiguration α)))).ae hv
  filter_upwards [hp] with p hp
  intro β hβ
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (hp β hβ).symm)

/-- Every integrable envelope has arbitrarily small mass outside a bounded
window separated from the next collision diagonal. Integrability on the
complement is stated as part of the estimate. -/
theorem exists_wordSpatialSeparatedWindow_integral_compl_small
    {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·))
    (B : FusedConfiguration α × FusedConfiguration α → ℝ) (hB : Integrable B) :
    ∀ ε > 0, ∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧
      IntegrableOn B (wordSpatialSeparatedWindow α w R δ)ᶜ ∧
      (∫ p in (wordSpatialSeparatedWindow α w R δ)ᶜ, B p) ≤ ε := by
  have : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let K := fun n : ℕ => wordSpatialSeparatedWindow α w n (δ n)
  let F := fun n : ℕ => (K n)ᶜ.indicator B
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) at h
    simpa only [δ, Nat.cast_add, Nat.cast_one] using h
  have hpoint : ∀ᵐ p : FusedConfiguration α × FusedConfiguration α,
      Tendsto (fun n => F n p) atTop (𝓝 0) := by
    filter_upwards [ae_wordSpatial_next_gap_pos α w hw] with p hp
    have hsep : ∀ᶠ n : ℕ in atTop, ∀ β ∈ w.head?,
        δ n ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖ := by
      cases w with
      | nil => exact Eventually.of_forall fun _ => by simp
      | cons β w =>
          have he := hδ.eventually (Iio_mem_nhds (hp β (by simp)))
          filter_upwards [he] with n hn
          intro γ hγ
          have hγeq : γ = β := by simpa using hγ.symm
          subst γ
          exact hn.le
    have hnorm : ∀ᶠ n : ℕ in atTop, ‖p‖ ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop ‖p‖)
    apply tendsto_const_nhds.congr'
    filter_upwards [hsep, hnorm] with n hnsep hnnorm
    have hk : p ∈ K n := ⟨hnnorm, hnsep⟩
    exact (Set.indicator_of_notMem (show p ∉ (K n)ᶜ from fun hp => hp hk) B).symm
  have hlim : Tendsto (fun n => ∫ p, F n p) atTop (𝓝 0) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable (F n) volume :=
      hB.aestronglyMeasurable.indicator (isClosed_wordSpatialSeparatedWindow α w n (δ n)).measurableSet.compl
    have hbound (n : ℕ) : ∀ᵐ p, ‖F n p‖ ≤ ‖B p‖ :=
      Eventually.of_forall fun p => norm_indicator_le_norm_self _ _
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun p => ‖B p‖) (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hB.norm hpoint
  intro ε hε
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.mp hlim) ε hε).exists
  refine ⟨n, δ n, Nat.cast_nonneg _, by dsimp [δ]; positivity, hB.integrableOn, ?_⟩
  rw [Real.dist_eq, sub_zero] at hn
  have he : (∫ p, F n p) = ∫ p in (K n)ᶜ, B p :=
    integral_indicator (isClosed_wordSpatialSeparatedWindow α w n (δ n)).measurableSet.compl
  rw [he] at hn
  exact (le_abs_self _).trans hn.le

private theorem integrable_envelope_cutoff_error {h : ℕ} (α : CollisionPair h)
    (B : FusedConfiguration α × FusedConfiguration α → ℝ) (hB : Integrable B)
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχ : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1)
    (f : (FusedConfiguration α × FusedConfiguration α) →
      (FusedConfiguration α × FusedConfiguration α)) (hf : Measurable f) :
    Integrable (fun p => B p * |1 - χ (f p)|) := by
  have : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  have hχm : AEStronglyMeasurable (fun p => χ (f p)) volume :=
    (χ.continuous.measurable.comp hf).aestronglyMeasurable
  have hdiff : AEStronglyMeasurable (fun p => (1 : ℝ) - χ (f p)) volume :=
    aestronglyMeasurable_const.sub hχm
  have habs : AEStronglyMeasurable (fun p => |1 - χ (f p)|) volume := by
    simpa only [Real.norm_eq_abs] using hdiff.norm
  have hm : AEStronglyMeasurable (fun p => B p * |1 - χ (f p)|) volume :=
    hB.aestronglyMeasurable.mul habs
  apply hB.norm.mono' hm
  apply Eventually.of_forall
  intro p
  have he : |1 - χ (f p)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hχ _).2)]
    exact sub_le_self 1 (hχ _).1
  simp only [Real.norm_eq_abs, abs_mul, abs_abs]
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans_eq (mul_one _)

/-- An integrable nonnegative envelope admits a continuous compact cutoff
away from the next diagonal, with arbitrarily small weighted error. -/
theorem exists_wordSpatialCutoff_integral_small
    {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·))
    (B : FusedConfiguration α × FusedConfiguration α → ℝ)
    (hB : Integrable B) (hB0 : ∀ p, 0 ≤ B p) :
    ∀ ε > 0, ∃ χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
      (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
      (∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ p ≠ 0 →
        ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
          δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) ∧
      Integrable (fun p => B p * |1 - χ p|) ∧
      (∫ p, B p * |1 - χ p|) ≤ ε := by
  have : ProperSpace (FusedConfiguration α) := by infer_instance
  have : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  intro ε hε
  obtain ⟨R, δ, _hR, hδ, _hi, hsmall⟩ :=
    exists_wordSpatialSeparatedWindow_integral_compl_small α w hw B hB ε hε
  let K := wordSpatialSeparatedWindow α w R δ
  let U : Set (FusedConfiguration α × FusedConfiguration α) :=
    {p | ∀ β ∈ w.head?, δ / 2 <
      ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖}
  have hU : IsOpen U := by
    cases w with
    | nil => simp [U]
    | cons β w =>
        have hc : Continuous (fun p : FusedConfiguration α × FusedConfiguration α =>
            ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) :=
          (((continuous_fused_collision_coordinate α β.1.2).comp continuous_snd).sub
            ((continuous_fused_collision_coordinate α β.1.1).comp continuous_snd)).norm
        simpa [U] using isOpen_lt continuous_const hc
  have hKU : K ⊆ U := by
    intro p hp β hβ
    exact (by linarith only [hδ] : δ / 2 < δ).trans_le (hp.2 β hβ)
  obtain ⟨g, hone, hcompact, hsupport, hrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (isCompact_wordSpatialSeparatedWindow α w R δ) hU hKU
  let χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ) := ⟨g, hcompact⟩
  have hχ (p) : 0 ≤ χ p ∧ χ p ≤ 1 := hrange p
  have hχone (p) (hp : p ∈ K) : χ p = 1 := hone hp
  have hiχ : Integrable (fun p => B p * |1 - χ p|) :=
    integrable_envelope_cutoff_error α B hB χ hχ id measurable_id
  obtain ⟨R', hR'⟩ := hcompact.isBounded.exists_norm_le
  refine ⟨χ, hχ, ⟨max 0 R', δ / 2, le_max_left _ _, half_pos hδ, ?_⟩, hiχ, ?_⟩
  · intro p hp
    have hmem : p ∈ tsupport (g : (FusedConfiguration α × FusedConfiguration α) → ℝ) :=
      subset_closure (show p ∈ Function.support g from hp)
    refine ⟨(hR' p hmem).trans (le_max_right _ _), ?_⟩
    intro β hβ
    exact (hsupport hmem β hβ).le
  · have hbound (p : FusedConfiguration α × FusedConfiguration α) :
        B p * |1 - χ p| ≤ Kᶜ.indicator B p := by
      by_cases hp : p ∈ K
      · rw [hχone p hp, sub_self, abs_zero, mul_zero,
          Set.indicator_of_notMem (show p ∉ Kᶜ from fun hp' => hp' hp)]
      · rw [Set.indicator_of_mem (show p ∈ Kᶜ from hp)]
        have he : |1 - χ p| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr (hχ p).2)]
          exact sub_le_self 1 (hχ p).1
        exact (mul_le_mul_of_nonneg_left he (hB0 p)).trans_eq (mul_one _)
    have hK : MeasurableSet K := (isClosed_wordSpatialSeparatedWindow α w R δ).measurableSet
    have hb := integral_mono hiχ (hB.indicator hK.compl) hbound
    rw [integral_indicator hK.compl] at hb
    exact hb.trans hsmall

private theorem measurable_fusedPair_sample_shift {h : ℕ} (α : CollisionPair h)
    (N k l : ℕ) (d e : FusedConfiguration α) :
    Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      wordFusedPairRepresentative N k l α p + (d, e)) := by
  have : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  have hrep : Measurable (wordFusedPairRepresentative N k l α) :=
    ((measurable_wordFusedPhaseRepresentative N k α).comp measurable_fst).prodMk
      ((measurable_wordFusedPhaseRepresentative N l α).comp measurable_snd)
  have hshift : Continuous (fun q : FusedConfiguration α × FusedConfiguration α => q + (d, e)) :=
    continuous_id.add continuous_const
  exact hshift.measurable.comp hrep

private theorem norm_fusedPair_sample_shift_sub_le {h N : ℕ} (hN : 0 < N)
    (α : CollisionPair h) (k l : ℕ) (d e : FusedConfiguration α)
    (hd : ‖d‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹)
    (he : ‖e‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹)
    (p : FusedConfiguration α × FusedConfiguration α) :
    ‖wordFusedPairRepresentative N k l α p + (d, e) - p‖ ≤
      2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
  have hc (k : ℕ) (d v : FusedConfiguration α)
      (hd : ‖d‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹) :
      ‖wordFusedPhaseRepresentative N k α v + d - v‖ ≤
        2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
    calc
      _ = ‖(wordFusedPhaseRepresentative N k α v - v) + d‖ := by congr 1; abel
      _ ≤ ‖wordFusedPhaseRepresentative N k α v - v‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ + (Real.sqrt ((N : ℝ) / 2))⁻¹ :=
        add_le_add (norm_wordFusedPhaseRepresentative_sub_le hN k α v) hd
      _ = _ := by ring
  rw [Prod.norm_def, max_le_iff]
  exact ⟨hc k d p.1 hd, hc l e p.2 he⟩

/-- Compact cutoffs approximate an integrable envelope uniformly over all
sampling phases and all shifts of at most one lattice mesh. -/
theorem exists_wordSpatialCutoff_of_integrable_majorant
    {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·))
    (B : FusedConfiguration α × FusedConfiguration α → ℝ)
    (hB : Integrable B) (hB0 : ∀ p, 0 ≤ B p) :
    ∀ ε > 0, ∃ χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
      (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
      (∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ p ≠ 0 →
        ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
          δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) ∧
      (∀ (N k l : ℕ) (d e : FusedConfiguration α),
        Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
          B p * |1 - χ (wordFusedPairRepresentative N k l α p + (d, e))|)) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (k l : ℕ) (d e : FusedConfiguration α),
        ‖d‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ →
        ‖e‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ →
        (∫ p : FusedConfiguration α × FusedConfiguration α,
          B p * |1 - χ (wordFusedPairRepresentative N k l α p + (d, e))|) ≤ ε := by
  intro ε hε
  obtain ⟨χ, hχ, hsupport, hiχ, hsmall⟩ :=
    exists_wordSpatialCutoff_integral_small α w hw B hB hB0 (ε / 2) (half_pos hε)
  have hi (N k l : ℕ) (d e : FusedConfiguration α) :
      Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
        B p * |1 - χ (wordFusedPairRepresentative N k l α p + (d, e))|) :=
    integrable_envelope_cutoff_error α B hB χ hχ _ (measurable_fusedPair_sample_shift α N k l d e)
  refine ⟨χ, hχ, hsupport, hi, ?_⟩
  let I : ℝ := ∫ p, B p
  have hI : 0 ≤ I := integral_nonneg hB0
  let a : ℝ := ε / (2 * (I + 1))
  have ha : 0 < a := div_pos hε (by positivity)
  have hden : I + 1 ≠ 0 := ne_of_gt (by linarith only [hI] : 0 < I + 1)
  have hbudget : a * I ≤ ε / 2 := by
    calc
      _ ≤ a * (I + 1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) ha.le
      _ = ε / 2 := by dsimp [a]; rw [← div_div, div_mul_cancel₀ _ hden]
  have huc := χ.hasCompactSupport.uniformContinuous_of_continuous χ.continuous
  obtain ⟨δ, hδ, hcont⟩ := (Metric.uniformContinuous_iff.mp huc) a ha
  have hmesh : Tendsto (fun N : ℕ => 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_lattice_mesh.const_mul 2
  filter_upwards [hmesh.eventually (Iio_mem_nhds hδ), eventually_gt_atTop 0] with N hmeshN hN
  intro k l d e hd he
  let f := fun p : FusedConfiguration α × FusedConfiguration α =>
    wordFusedPairRepresentative N k l α p + (d, e)
  have hbound (p : FusedConfiguration α × FusedConfiguration α) :
      B p * |1 - χ (f p)| ≤ B p * |1 - χ p| + a * B p := by
    have hclose : dist p (f p) < δ := by
      rw [dist_eq_norm, norm_sub_rev]
      exact (norm_fusedPair_sample_shift_sub_le hN α k l d e hd he p).trans_lt hmeshN
    have hdiff : |χ p - χ (f p)| ≤ a := by
      have hc : dist (χ p) (χ (f p)) < a := hcont hclose
      simpa only [Real.dist_eq] using hc.le
    have herr : |1 - χ (f p)| ≤ |1 - χ p| + a := by
      calc
        _ = |(1 - χ p) + (χ p - χ (f p))| := by congr 1; ring
        _ ≤ |1 - χ p| + |χ p - χ (f p)| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl hdiff
    exact (mul_le_mul_of_nonneg_left herr (hB0 p)).trans_eq (by ring)
  have hb := integral_mono (hi N k l d e) (hiχ.add (hB.const_mul a)) hbound
  simp only [Pi.add_apply] at hb
  rw [integral_add hiχ (hB.const_mul a), integral_const_mul] at hb
  linarith only [hb, hsmall, hbudget]

end Critical2DKPZ.SHF.Moments
