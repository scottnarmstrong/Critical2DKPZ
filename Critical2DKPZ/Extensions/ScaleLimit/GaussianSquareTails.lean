/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SeqReduction
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Truncated second moments under Gaussian weak limits

The tail square is the full square minus a continuous clipped square, plus a
constant times a tail indicator. This isolates the boundary regularity needed
by weak convergence from the integrability needed by the second moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A continuous clipped square, bounded by the square of its clipping radius. -/
def clippedSquare (c : ℝ) : ℝ →ᵇ ℝ where
  toFun y := min (y ^ 2) (c ^ 2)
  continuous_toFun := (continuous_id.pow 2).min continuous_const
  map_bounded' := by
    refine ⟨c ^ 2, ?_⟩
    intro x y
    rw [Real.dist_eq]
    apply abs_le.mpr
    have hx0 : 0 ≤ min (x ^ 2) (c ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    have hy0 : 0 ≤ min (y ^ 2) (c ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    constructor
    · linarith only [hx0, min_le_right (y ^ 2) (c ^ 2)]
    · linarith only [hy0, min_le_right (x ^ 2) (c ^ 2)]

/-- The tail square splits into a continuous term and a tail probability. -/
theorem tail_square_identity {c : ℝ} (hc : 0 ≤ c) (y : ℝ) :
    y ^ 2 * Set.indicator {z : ℝ | c < |z|} (fun _ : ℝ => (1 : ℝ)) y =
      y ^ 2 - clippedSquare c y + c ^ 2 * Set.indicator {z : ℝ | c < |z|} (fun _ : ℝ => (1 : ℝ)) y := by
  change _ = y ^ 2 - min (y ^ 2) (c ^ 2) + _
  by_cases hy : c < |y|
  · have hsq : c ^ 2 ≤ y ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hc (abs_nonneg y)).mpr hy.le
    have hymem : y ∈ {z : ℝ | c < |z|} := hy
    simp only [Set.indicator_of_mem hymem, mul_one, min_eq_right hsq,
      sub_add_cancel]
  · have hsq : y ^ 2 ≤ c ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hc).mpr (le_of_not_gt hy)
    have hymem : y ∉ {z : ℝ | c < |z|} := hy
    simp only [Set.indicator_of_notMem hymem, mul_zero, min_eq_left hsq, sub_self, add_zero]

/-- A real Gaussian has zero mass at every nonzero point when its mean is zero. -/
theorem gaussianReal_zero_mean_singleton (v : ℝ≥0) {c : ℝ} (hc : c ≠ 0) :
    gaussianReal 0 v {c} = 0 := by
  by_cases hv : v = 0
  · subst v
    rw [gaussianReal_zero_var, Measure.dirac_apply' _ (measurableSet_singleton c)]
    exact Set.indicator_of_notMem (show (0 : ℝ) ∉ {c} from hc.symm) _
  · let : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
    exact measure_singleton c

/-- The tail event is a continuity set for every centred Gaussian, including variance zero. -/
theorem gaussian_tail_null_frontier (v : ℝ≥0) {c : ℝ} (hc : 0 < c) :
    gaussianReal 0 v (frontier {y : ℝ | c < |y|}) = 0 := by
  have hset : {y : ℝ | c < |y|} = (Metric.closedBall (0 : ℝ) c)ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_closedBall,
      Real.dist_eq, sub_zero, not_le]
  have hs : frontier {y : ℝ | c < |y|} ⊆ {c} ∪ {-c} := by
    rw [hset, frontier_compl]
    intro y hy
    have hn : |y| = c := by
      simpa only [Metric.mem_sphere, Real.dist_eq, sub_zero] using
        Metric.frontier_closedBall_subset_sphere hy
    rcases (abs_eq hc.le).mp hn with h | h
    · exact Or.inl h
    · exact Or.inr h
  apply measure_mono_null hs
  have hp := gaussianReal_zero_mean_singleton v hc.ne'
  have hn := gaussianReal_zero_mean_singleton v (neg_ne_zero.mpr hc.ne')
  exact le_antisymm ((measure_union_le _ _).trans (by rw [hp, hn, zero_add])) bot_le

/-- Integrating the clipped-square identity separates the tail probability. -/
theorem integral_tail_square_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P)
    (h2 : Integrable (fun ω => X ω ^ 2) P) {c : ℝ} (hc : 0 ≤ c) :
    (∫ ω, X ω ^ 2 * Set.indicator {y : ℝ | c < |y|} (fun _ : ℝ => (1 : ℝ)) (X ω) ∂P) =
      (∫ ω, X ω ^ 2 ∂P) - (∫ ω, clippedSquare c (X ω) ∂P) +
        c ^ 2 * (P {ω | c < |X ω|}).toReal := by
  let A : Set ℝ := {y : ℝ | c < |y|}
  have hA : MeasurableSet A := by
    simpa only [Real.norm_eq_abs] using
      (isOpen_lt continuous_const (continuous_norm : Continuous (fun y : ℝ => ‖y‖))).measurableSet
  have hg : Integrable (fun ω => clippedSquare c (X ω)) P :=
    (integrable_map_measure (clippedSquare c).continuous.aestronglyMeasurable hX).mp
      ((clippedSquare c).integrable (μ := P.map X))
  have hI : Integrable (fun ω => A.indicator (fun _ : ℝ => (1 : ℝ)) (X ω)) P := by
    apply Integrable.of_bound
      ((((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator hA).comp_aemeasurable hX).aestronglyMeasurable) 1
    filter_upwards [] with ω
    change ‖A.indicator (fun _ : ℝ => (1 : ℝ)) (X ω)‖ ≤ 1
    by_cases hω : X ω ∈ A
    · simp only [Set.indicator_of_mem hω, norm_one, le_refl]
    · simp only [Set.indicator_of_notMem hω, norm_zero, zero_le_one]
  have hImean : (∫ ω, A.indicator (fun _ : ℝ => (1 : ℝ)) (X ω) ∂P) = (P {ω | c < |X ω|}).toReal := by
    rw [← integral_map hX (((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator hA).aestronglyMeasurable),
      integral_indicator_const 1 hA, smul_eq_mul, mul_one, Measure.real,
      Measure.map_apply_of_aemeasurable hX hA]
    rfl
  have heq : (fun ω => X ω ^ 2 * A.indicator (fun _ : ℝ => (1 : ℝ)) (X ω)) =
      fun ω => X ω ^ 2 - clippedSquare c (X ω) + c ^ 2 * A.indicator (fun _ : ℝ => (1 : ℝ)) (X ω) := by
    funext ω
    exact tail_square_identity hc (X ω)
  change (∫ ω, X ω ^ 2 * A.indicator (fun _ : ℝ => (1 : ℝ)) (X ω) ∂P) = _
  have hdiff : Integrable (fun ω => X ω ^ 2 - clippedSquare c (X ω)) P := h2.sub hg
  have hconst : Integrable (fun ω => c ^ 2 * A.indicator (fun _ : ℝ => (1 : ℝ)) (X ω)) P :=
    hI.const_mul _
  rw [heq, integral_add hdiff hconst, integral_sub h2 hg,
    integral_const_mul, hImean]

/-- Weak convergence and second-moment convergence determine truncated moments at null boundaries. -/
theorem truncated_second_moment_tendsto_of_null_frontier
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι}
    (P : Measure Ω) [IsProbabilityMeasure P] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, AEMeasurable (X i) P)
    (hInt : ∀ i, Integrable (fun ω => X i ω ^ 2) P)
    (hμInt : Integrable (fun y : ℝ => y ^ 2) μ)
    (hlaw : TendstoInDistribution X l id (fun _ => P) μ)
    (h2 : Tendsto (fun i => ∫ ω, X i ω ^ 2 ∂P) l (𝓝 (∫ y : ℝ, y ^ 2 ∂μ)))
    {c : ℝ} (hc : 0 ≤ c) (hNull : μ (frontier {y : ℝ | c < |y|}) = 0) :
    Tendsto (fun i => ∫ ω, X i ω ^ 2 * Set.indicator {y : ℝ | c < |y|} (fun _ : ℝ => (1 : ℝ)) (X i ω) ∂P) l
      (𝓝 (∫ y : ℝ, y ^ 2 * Set.indicator {z : ℝ | c < |z|} (fun _ : ℝ => (1 : ℝ)) y ∂μ)) := by
  let A : Set ℝ := {y : ℝ | c < |y|}
  have hA : MeasurableSet A := by
    simpa only [Real.norm_eq_abs] using
      (isOpen_lt continuous_const (continuous_norm : Continuous (fun y : ℝ => ‖y‖))).measurableSet
  have hclip : Tendsto (fun i => ∫ ω, clippedSquare c (X i ω) ∂P) l
      (𝓝 (∫ y, clippedSquare c y ∂μ)) :=
    (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hX aemeasurable_id).mp
      hlaw (clippedSquare c)
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlaw.tendsto
    (E := A) (by
      change (μ.map id) (frontier A) = 0
      simpa only [Measure.map_id, A] using hNull)
  have hmap (i : ι) : (P.map (X i)) A = P {ω | c < |X i ω|} :=
    Measure.map_apply_of_aemeasurable (hX i) hA
  have hp' : Tendsto (fun i => P {ω | c < |X i ω|}) l (𝓝 (μ A)) := by
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id, hmap] using hp
  have hpr := (ENNReal.tendsto_toReal (measure_ne_top μ A)).comp hp'
  have ht := (h2.sub hclip).add (hpr.const_mul (c ^ 2))
  have hμeq := integral_tail_square_identity μ id aemeasurable_id hμInt hc
  simp only [id_eq] at hμeq
  rw [hμeq]
  apply ht.congr
  intro i
  exact (integral_tail_square_identity P (X i) (hX i) (hInt i) hc).symm

/-- The second moment of a centred real Gaussian is its variance parameter. -/
theorem integral_sq_centered_gaussianReal (v : ℝ≥0) :
    (∫ y : ℝ, y ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) aemeasurable_id, integral_id_gaussianReal] at h
  simpa only [sub_zero] using h

/-- Truncated second moments converge under a Gaussian limit and convergent second moments. -/
theorem truncated_second_moment_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Set.Ioi (0 : ℝ) → Ω → ℝ}
    (hX : ∀ L, AEMeasurable (X L) P)
    (hInt : ∀ L, Integrable (fun ω => X L ω ^ 2) P) {v : ℝ≥0}
    (hlaw : TendstoInDistribution X atTop id (fun _ => P) (gaussianReal 0 v))
    (h2 : Tendsto (fun L => ∫ ω, X L ω ^ 2 ∂P) atTop (𝓝 (v : ℝ)))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L => ∫ ω, X L ω ^ 2 * Set.indicator {y : ℝ | c < |y|} (fun _ : ℝ => (1 : ℝ)) (X L ω) ∂P)
      atTop (𝓝 (∫ y : ℝ, y ^ 2 * Set.indicator {z : ℝ | c < |z|} (fun _ : ℝ => (1 : ℝ)) y ∂gaussianReal 0 v)) := by
  apply truncated_second_moment_tendsto_of_null_frontier P hX hInt
    (memLp_id_gaussianReal 2).integrable_sq hlaw
    (by simpa only [integral_sq_centered_gaussianReal] using h2) hc.le
  exact gaussian_tail_null_frontier v hc

end Critical2DKPZ.Extensions.ScaleLimit
