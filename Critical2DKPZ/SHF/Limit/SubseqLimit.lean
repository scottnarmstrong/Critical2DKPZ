/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.JointTightness
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # First marginals of subsequential polymer limits

Gaussian tail bounds identify the first-marginal coordinate of a joint vague polymer limit with the projection of its pair-measure coordinate. -/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped CompactlySupported Topology BoundedContinuousFunction ENNReal

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.SHF.Limit

/-- The truncation of a real observable to the interval `[0, 1]`. -/
def boundedReadoutClip (x : ℝ) : ℝ := min 1 (max 0 x)

private theorem boundedReadoutClip_nonneg (x : ℝ) : 0 ≤ boundedReadoutClip x := by
  exact le_min (by norm_num) (le_max_left _ _)

private theorem boundedReadoutClip_le_one (x : ℝ) : boundedReadoutClip x ≤ 1 := min_le_left _ _

private theorem continuous_boundedReadoutClip : Continuous boundedReadoutClip := by
  fun_prop [boundedReadoutClip]

private noncomputable def unitClipBCF {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => boundedReadoutClip (f x), continuous_boundedReadoutClip.comp hf⟩ 1 (by
      intro x y
      change dist (boundedReadoutClip (f x)) (boundedReadoutClip (f y)) ≤ 1
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [boundedReadoutClip_nonneg (f x),
        boundedReadoutClip_nonneg (f y),
        boundedReadoutClip_le_one (f x), boundedReadoutClip_le_one (f y)])

private noncomputable def polymerTensorTest
    (f g : C_c(Plane, ℝ)) : C_c(Plane × Plane, ℝ) := by
  refine ⟨⟨fun p => f p.1 * g p.2,
    (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)⟩, ?_⟩
  have hK : IsCompact (tsupport (f : Plane → ℝ) ×ˢ tsupport (g : Plane → ℝ)) :=
    f.hasCompactSupport.prod g.hasCompactSupport
  have hsupport : Function.support (fun p : Plane × Plane => f p.1 * g p.2) ⊆
      tsupport (f : Plane → ℝ) ×ˢ tsupport (g : Plane → ℝ) := by
    intro p hp
    have hprod : f p.1 * g p.2 ≠ 0 := by
      simpa only [Function.mem_support] using hp
    have hf : f p.1 ≠ 0 := fun h => hprod (by simp [h])
    have hg : g p.2 ≠ 0 := fun h => hprod (by simp [h])
    exact ⟨subset_closure (by simpa only [Function.mem_support] using hf),
      subset_closure (by simpa only [Function.mem_support] using hg)⟩
  exact IsCompact.of_isClosed_subset hK (isClosed_tsupport _)
    (closure_minimal hsupport hK.isClosed)


/-- Compact tensor pairings are bounded by the flat first-coordinate pairing.
Both are integrable by `RandomMeasure.integrable_vagueTest`. -/
private theorem vaguePairing_polymerTensor_le_marginal
    (μ : RandomMeasure.PlanePairRadonMeasure) (ν : RandomMeasure.PlaneRadonMeasure)
    (hmap : Measure.map Prod.fst (μ.1 : Measure (Plane × Plane)) = ν.1)
    (f g : C_c(Plane, ℝ)) (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, g y ≤ 1) :
    RandomMeasure.vaguePairing μ (polymerTensorTest f g) ≤
      RandomMeasure.vaguePairing ν f := by
  change (∫ p, f p.1 * g p.2 ∂μ.1) ≤ ∫ x, f x ∂ν.1
  have hleft : Integrable (fun p : Plane × Plane => f p.1 * g p.2) μ.1 :=
    RandomMeasure.integrable_vagueTest μ (polymerTensorTest f g)
  have hfν : Integrable f (Measure.map Prod.fst μ.1) := by
    simpa [hmap] using RandomMeasure.integrable_vagueTest ν f
  have hfirst : Integrable (fun p : Plane × Plane => f p.1) μ.1 :=
    (integrable_map_measure hfν.aestronglyMeasurable measurable_fst.aemeasurable).mp hfν
  have hpoint (p : Plane × Plane) : f p.1 * g p.2 ≤ f p.1 := by
    calc
      f p.1 * g p.2 ≤ f p.1 * 1 := mul_le_mul_of_nonneg_left (hg p.2) (hf p.1)
      _ = f p.1 := mul_one _
  have hmapInt : ∫ x, f x ∂Measure.map Prod.fst μ.1 =
      ∫ p, f p.1 ∂μ.1 :=
    integral_map measurable_fst.aemeasurable hfν.aestronglyMeasurable
  calc
    ∫ p, f p.1 * g p.2 ∂μ.1 ≤ ∫ p, f p.1 ∂μ.1 := integral_mono hleft hfirst hpoint
    _ = ∫ x, f x ∂ν.1 := by rw [← hmap]; exact hmapInt.symm

private theorem vaguePairing_polymerTensor_error_le_tail
    (μ : RandomMeasure.PlanePairRadonMeasure) (ν : RandomMeasure.PlaneRadonMeasure)
    (hmap : Measure.map Prod.fst (μ.1 : Measure (Plane × Plane)) = ν.1)
    (f g : C_c(Plane, ℝ)) (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (R : ℝ) (hgone : ∀ y, ‖y‖ ≤ R → g y = 1)
    (A T : Set Plane) (hA : MeasurableSet A) (hT : MeasurableSet T)
    (hsupport : tsupport (f : Plane → ℝ) ⊆ A)
    (hTdef : T = {y : Plane | R ≤ ‖y‖})
    (hfinite : μ.1 (A ×ˢ T) < ∞) :
    RandomMeasure.vaguePairing ν f -
        RandomMeasure.vaguePairing μ (polymerTensorTest f g) ≤
      (μ.1 (A ×ˢ T)).toReal := by
  have hfν : Integrable f (Measure.map Prod.fst μ.1) := by
    simpa [hmap] using RandomMeasure.integrable_vagueTest ν f
  have hfirst : Integrable (fun p : Plane × Plane => f p.1) μ.1 :=
    (integrable_map_measure hfν.aestronglyMeasurable measurable_fst.aemeasurable).mp hfν
  have htest : Integrable (fun p : Plane × Plane => f p.1 * g p.2) μ.1 :=
    RandomMeasure.integrable_vagueTest μ (polymerTensorTest f g)
  let e : Plane × Plane → ℝ := fun p => f p.1 * (1 - g p.2)
  have hemeas : AEStronglyMeasurable e μ.1 := by
    exact ((f.continuous.comp continuous_fst).mul
      (continuous_const.sub (g.continuous.comp continuous_snd))).aestronglyMeasurable
  have hebound (p : Plane × Plane) : ‖e p‖ ≤ ‖f p.1‖ := by
    have hg0 := hg p.2
    have hgap0 : 0 ≤ 1 - g p.2 := by linarith [hg1 p.2]
    have hgap1 : 1 - g p.2 ≤ 1 := by linarith [hg p.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf p.1) hgap0)]
    calc
      f p.1 * (1 - g p.2) ≤ f p.1 * 1 :=
        mul_le_mul_of_nonneg_left hgap1 (hf p.1)
      _ = f p.1 := mul_one _
      _ ≤ ‖f p.1‖ := le_abs_self _
  have heint : Integrable e μ.1 :=
    hfirst.norm.mono' hemeas (Filter.Eventually.of_forall hebound)
  have hdiff :
      RandomMeasure.vaguePairing ν f -
          RandomMeasure.vaguePairing μ (polymerTensorTest f g) = ∫ p, e p ∂μ.1 := by
    change (∫ x, f x ∂ν.1) - ∫ p, f p.1 * g p.2 ∂μ.1 = _
    have hmapInt : ∫ x, f x ∂Measure.map Prod.fst μ.1 =
        ∫ p, f p.1 ∂μ.1 :=
      integral_map measurable_fst.aemeasurable hfν.aestronglyMeasurable
    have hmapInt' : ∫ x, f x ∂ν.1 = ∫ p, f p.1 ∂μ.1 := by
      rw [← hmap]
      exact hmapInt
    rw [hmapInt', ← integral_sub hfirst htest]
    congr 1
    funext p
    dsimp [e]
    ring
  have herr_nonneg (p : Plane × Plane) : 0 ≤ e p :=
    mul_nonneg (hf p.1) (by linarith [hg p.2, hg1 p.2])
  have herror_le_indicator (p : Plane × Plane) :
      e p ≤ (A ×ˢ T).indicator (fun _ => (1 : ℝ)) p := by
    by_cases hp : p ∈ A ×ˢ T
    · rw [Set.indicator_of_mem hp]
      have hgap0 : 0 ≤ 1 - g p.2 := by linarith [hg p.2, hg1 p.2]
      have hgap1 : 1 - g p.2 ≤ 1 := by linarith [hg p.2]
      calc
        e p = f p.1 * (1 - g p.2) := rfl
        _ ≤ f p.1 * 1 := mul_le_mul_of_nonneg_left hgap1 (hf p.1)
        _ ≤ 1 * 1 := by nlinarith [hf1 p.1]
        _ = 1 := by norm_num
    · rw [Set.indicator_of_notMem hp]
      have hp' : p.1 ∉ A ∨ p.2 ∉ T := by
        exact not_and_or.mp (by simpa only [Set.mem_prod] using hp)
      rcases hp' with hx | hy
      · have hfx : f p.1 = 0 := by
          by_contra hne
          exact hx (hsupport (subset_closure (Function.mem_support.mpr hne)))
        simp [e, hfx]
      · have hyR : ‖p.2‖ < R := by
          have : ¬ R ≤ ‖p.2‖ := by simpa [hTdef] using hy
          exact lt_of_not_ge this
        have hgone' : g p.2 = 1 := hgone p.2 (le_of_lt hyR)
        simp [e, hgone']
  have hindOn : IntegrableOn (fun _ : Plane × Plane => (1 : ℝ))
      (A ×ˢ T) μ.1 := integrableOn_const hfinite.ne
  have hind : Integrable ((A ×ˢ T).indicator (fun _ : Plane × Plane => (1 : ℝ))) μ.1 :=
    hindOn.integrable_indicator (hA.prod hT)
  have hle := integral_mono heint hind herror_le_indicator
  calc
    RandomMeasure.vaguePairing ν f -
        RandomMeasure.vaguePairing μ (polymerTensorTest f g) = ∫ p, e p ∂μ.1 := hdiff
    _ ≤ ∫ p, (A ×ˢ T).indicator (fun _ => (1 : ℝ)) p ∂μ.1 := hle
    _ = μ.1.real (A ×ˢ T) := integral_indicator_one (hA.prod hT)
    _ = (μ.1 (A ×ˢ T)).toReal := rfl

private def polymerCutoffPairing (f g : C_c(Plane, ℝ))
    (z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) : ℝ :=
  RandomMeasure.vaguePairing z.1 (polymerTensorTest f g)

/-- The marginal component of a polymer state paired with a compact continuous test. -/
def polymerFlatPairing (f : C_c(Plane, ℝ))
    (z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) : ℝ :=
  RandomMeasure.vaguePairing z.2 f

private theorem polymerFinite_clip_error_le_tail
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (f g : C_c(Plane, ℝ)) (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (R : ℝ) (hgone : ∀ y, ‖y‖ ≤ R → g y = 1)
    (A T : Set Plane) (hA : MeasurableSet A) (hT : MeasurableSet T)
    (hsupport : tsupport (f : Plane → ℝ) ⊆ A)
    (hTdef : T = {y : Plane | R ≤ ‖y‖})
    (hfinite : polymerMeasure ϑ N s t ω (A ×ˢ T) < ∞) :
    boundedReadoutClip
        (polymerFlatPairing f (polymerPairMarginalRadonMeasure ϑ N s t ω) -
          polymerCutoffPairing f g (polymerPairMarginalRadonMeasure ϑ N s t ω)) ≤
      (polymerMeasure ϑ N s t ω (A ×ˢ T)).toReal := by
  let z := polymerPairMarginalRadonMeasure ϑ N s t ω
  have hmap : Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane)) = z.2.1 := by
    simp [z, polymerPairMarginalRadonMeasure, polymerRadonMeasure,
      polymerMarginalRadonMeasure]
  have hupper := vaguePairing_polymerTensor_le_marginal z.1 z.2 hmap f g hf hg1
  have hdiff : 0 ≤ polymerFlatPairing f z - polymerCutoffPairing f g z := by
    exact sub_nonneg.mpr (by simpa [polymerFlatPairing, polymerCutoffPairing] using hupper)
  have hfinite' : z.1.1 (A ×ˢ T) < ∞ := by
    change polymerMeasure ϑ N s t ω (A ×ˢ T) < ∞
    exact hfinite
  have herror := vaguePairing_polymerTensor_error_le_tail z.1 z.2 hmap f g hf hf1 hg hg1
    R hgone A T hA hT hsupport hTdef hfinite'
  have hclip : boundedReadoutClip
      (polymerFlatPairing f z - polymerCutoffPairing f g z) ≤
        polymerFlatPairing f z - polymerCutoffPairing f g z := by
    dsimp [boundedReadoutClip]
    rw [max_eq_right hdiff]
    exact min_le_right _ _
  calc
    boundedReadoutClip
        (polymerFlatPairing f z - polymerCutoffPairing f g z) ≤
      polymerFlatPairing f z - polymerCutoffPairing f g z := hclip
    _ ≤ (z.1.1 (A ×ˢ T)).toReal := herror
    _ = (polymerMeasure ϑ N s t ω (A ×ˢ T)).toReal := rfl


/-- Suppose increasing continuous observables are almost surely bounded above by a continuous target under each approximating law. If the limsup of their clipped-error expectations tends to zero with the approximation index, the observables converge to the target almost surely under the weak limit. -/
theorem ae_tendsto_of_bounded_weak_approximation {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] (Qn : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hweak : Tendsto Qn atTop (𝓝 Q)) (A : ℕ → X → ℝ) (B : X → ℝ)
    (hAcont : ∀ R, Continuous (A R)) (hBcont : Continuous B)
    (hAmono : ∀ x, Monotone (fun R => A R x))
    (hupper : ∀ n R, ∀ᵐ x ∂(Qn n : Measure X), A R x ≤ B x)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hclip : ∀ R, ∀ᶠ n in atTop,
      Integrable (fun x => boundedReadoutClip (B x - A R x)) (Qn n : Measure X) ∧
        ∫ x, boundedReadoutClip (B x - A R x) ∂(Qn n : Measure X) ≤ ε R) :
    ∀ᵐ x ∂(Q : Measure X), Tendsto (fun R => A R x) atTop (𝓝 (B x)) := by
  let clipNeg (R : ℕ) : X →ᵇ ℝ := unitClipBCF (A R - B)
    ((hAcont R).sub hBcont)
  have hclipNeg_integral (R : ℕ) :
      ∫ x, clipNeg R x ∂(Q : Measure X) = 0 := by
    have hseq : Tendsto (fun n => ∫ x, clipNeg R x ∂(Qn n : Measure X))
        atTop (𝓝 (∫ x, clipNeg R x ∂(Q : Measure X))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) (clipNeg R)
    have hzero (n : ℕ) : ∫ x, clipNeg R x ∂(Qn n : Measure X) = 0 := by
      have hvanish : clipNeg R =ᵐ[(Qn n : Measure X)] 0 := by
        filter_upwards [hupper n R] with x hx
        simp [clipNeg, unitClipBCF, boundedReadoutClip, sub_nonpos.mpr hx]
      exact integral_eq_zero_of_ae hvanish
    have heq : (fun n => ∫ x, clipNeg R x ∂(Qn n : Measure X)) = fun _ => 0 :=
      funext hzero
    have hseq0 : Tendsto (fun n => ∫ x, clipNeg R x ∂(Qn n : Measure X))
        atTop (𝓝 0) := by
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hseq hseq0
  have hupperQ : ∀ R, ∀ᵐ x ∂(Q : Measure X), A R x ≤ B x := by
    intro R
    have hInt : Integrable (fun x => boundedReadoutClip (A R x - B x))
        (Q : Measure X) := by
      simpa [clipNeg, unitClipBCF] using (clipNeg R).integrable (Q : Measure X)
    have hzero := (integral_eq_zero_iff_of_nonneg
      (fun x => boundedReadoutClip_nonneg _) hInt).mp
        (by simpa [clipNeg, unitClipBCF] using hclipNeg_integral R)
    filter_upwards [hzero] with x hx
    have hnotpos : ¬ 0 < A R x - B x := by
      intro hpos
      have : 0 < boundedReadoutClip (A R x - B x) := by
        dsimp [boundedReadoutClip]
        exact lt_min (by norm_num) (lt_max_of_lt_right hpos)
      have hx0 : boundedReadoutClip (A R x - B x) = 0 := by simpa using hx
      exact (ne_of_gt this) hx0
    have hnot : ¬ B x < A R x := by
      intro hlt
      exact hnotpos (sub_pos.mpr hlt)
    exact le_of_not_gt hnot
  have hclipUpperQ : ∀ R,
      ∫ x, boundedReadoutClip (B x - A R x) ∂(Q : Measure X) ≤ ε R := by
    intro R
    let f : X →ᵇ ℝ := unitClipBCF (B - A R) (hBcont.sub (hAcont R))
    have hlim : Tendsto (fun n => ∫ x, f x ∂(Qn n : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(Q : Measure X))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) f
    have hbound : ∀ᶠ n in atTop, ∫ x, f x ∂(Qn n : Measure X) ≤ ε R := by
      filter_upwards [hclip R] with n hn
      simpa [f, unitClipBCF] using hn.2
    have hle := le_of_tendsto hlim hbound
    simpa [f, unitClipBCF] using hle
  have hupperAll : ∀ᵐ x ∂(Q : Measure X), ∀ R, A R x ≤ B x := by
    rw [ae_all_iff]
    exact hupperQ
  let L : X → ℝ := fun x => ⨆ R, A R x
  have hpointwise : ∀ᵐ x ∂(Q : Measure X),
      Tendsto (fun R => boundedReadoutClip (B x - A R x)) atTop
        (𝓝 (boundedReadoutClip (B x - L x))) := by
    filter_upwards [hupperAll] with x hxs
    have hmono := hAmono x
    have hbounded : BddAbove (Set.range fun R => A R x) := by
      refine ⟨B x, ?_⟩
      rintro y ⟨R, rfl⟩
      exact hxs R
    have hA : Tendsto (fun R => A R x) atTop (𝓝 (L x)) := by
      exact tendsto_atTop_ciSup hmono hbounded
    exact continuous_boundedReadoutClip.continuousAt.tendsto.comp (tendsto_const_nhds.sub hA)
  have hclipLimitMeas : AEStronglyMeasurable (fun x => boundedReadoutClip (B x - L x))
      (Q : Measure X) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun R => (continuous_boundedReadoutClip.comp (hBcont.sub (hAcont R))).aestronglyMeasurable)
      hpointwise
  have hclipLimitInt : Integrable (fun x => boundedReadoutClip (B x - L x)) (Q : Measure X) := by
    apply (integrable_const (1 : ℝ)).mono' hclipLimitMeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedReadoutClip_nonneg _)]
    exact boundedReadoutClip_le_one _
  have hDCT : Tendsto
      (fun R => ∫ x, boundedReadoutClip (B x - A R x) ∂(Q : Measure X)) atTop
      (𝓝 (∫ x, boundedReadoutClip (B x - L x) ∂(Q : Measure X))) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 1)
    · exact Filter.Eventually.of_forall fun R =>
        (continuous_boundedReadoutClip.comp (hBcont.sub (hAcont R))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (boundedReadoutClip_nonneg _)]
        exact boundedReadoutClip_le_one _
    · exact integrable_const 1
    · exact hpointwise
  have hLimitZero : ∫ x, boundedReadoutClip (B x - L x) ∂(Q : Measure X) = 0 := by
    have hnonneg : 0 ≤ ∫ x, boundedReadoutClip (B x - L x) ∂(Q : Measure X) :=
      integral_nonneg (fun x => boundedReadoutClip_nonneg _)
    by_contra hne
    have hpos : 0 < ∫ x, boundedReadoutClip (B x - L x) ∂(Q : Measure X) :=
      lt_of_le_of_ne hnonneg (by intro heq; exact hne heq.symm)
    let c := (∫ x, boundedReadoutClip (B x - L x) ∂(Q : Measure X)) / 2
    have hc : c < ∫ x, boundedReadoutClip (B x - L x) ∂(Q : Measure X) := by
      dsimp [c]
      linarith
    have hseqgt : ∀ᶠ R in atTop,
        c < ∫ x, boundedReadoutClip (B x - A R x) ∂(Q : Measure X) :=
      hDCT.eventually (isOpen_Ioi.mem_nhds hc)
    have hcpos : 0 < c := by dsimp [c]; linarith
    have hεsmall : ∀ᶠ R in atTop, ε R < c :=
      hε.eventually (isOpen_Iio.mem_nhds hcpos)
    have hpair := hseqgt.and hεsmall
    obtain ⟨R, hR⟩ := hpair.exists
    rcases hR with ⟨h1, h2⟩
    exact (not_lt_of_ge (hclipUpperQ R)) (lt_trans h2 h1)
  have hclipLimitZero :
      (fun x => boundedReadoutClip (B x - L x)) =ᵐ[(Q : Measure X)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => boundedReadoutClip_nonneg _)
      hclipLimitInt).mp hLimitZero
  have hL : L =ᵐ[(Q : Measure X)] B := by
    filter_upwards [hclipLimitZero, hupperAll] with x hx hxs
    have hLB : L x ≤ B x := by
      change sSup (Set.range fun R => A R x) ≤ B x
      apply csSup_le
      · exact ⟨A 0 x, ⟨0, rfl⟩⟩
      · rintro y ⟨R, rfl⟩
        exact hxs R
    have hnotpos : ¬ 0 < B x - L x := by
      intro hpos
      have hclippos : 0 < boundedReadoutClip (B x - L x) := by
        dsimp [boundedReadoutClip]
        exact lt_min (by norm_num) (lt_max_of_lt_right hpos)
      have hx0 : boundedReadoutClip (B x - L x) = 0 := by simpa using hx
      exact (ne_of_gt hclippos) hx0
    have hBL : B x - L x ≤ 0 := le_of_not_gt hnotpos
    have hBL' : B x - L x = 0 := le_antisymm hBL (sub_nonneg.mpr hLB)
    exact (sub_eq_zero.mp hBL').symm
  filter_upwards [hL, hupperAll] with x hx hxs
  have hmono := hAmono x
  have hbounded : BddAbove (Set.range fun R => A R x) := by
    refine ⟨B x, ?_⟩
    rintro y ⟨R, rfl⟩
    exact hxs R
  have hA : Tendsto (fun R => A R x) atTop (𝓝 (L x)) :=
    tendsto_atTop_ciSup hmono hbounded
  simpa [hx] using hA

/-- A compactly supported second-coordinate cutoff that equals one on the
radius-`R` ball and increases with `R`. -/
noncomputable def polymerTailCutoff (R : ℝ) (_hR : 0 ≤ R) : C_c(Plane, ℝ) := by
  let f : Plane → ℝ := fun y => min 1 (max 0 (R + 1 - ‖y‖))
  have hf : Continuous f := by
    change Continuous (fun y : Plane => min 1 (max 0 (R + 1 - ‖y‖)))
    fun_prop
  have hsupp : (Function.support f : Set Plane) ⊆ Metric.closedBall (0 : Plane) (R + 1) :=
    fun y hy => by
    have hyne : f y ≠ 0 := Function.mem_support.mp hy
    have hypos : 0 < f y := by
      have hnonneg : 0 ≤ f y := by dsimp [f]; exact le_min (by norm_num) (le_max_left _ _)
      exact lt_of_le_of_ne hnonneg (Ne.symm hyne)
    have hinner : 0 < max 0 (R + 1 - ‖y‖) := by
      exact lt_of_lt_of_le hypos (min_le_right _ _)
    have hradpos : 0 < R + 1 - ‖y‖ := by
      by_contra hnot
      have hle : R + 1 - ‖y‖ ≤ 0 := le_of_not_gt hnot
      rw [max_eq_left hle] at hinner
      exact (lt_irrefl 0) hinner
    have hrad : ‖y‖ < R + 1 := by
      linarith
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hrad.le
  have hclosure : tsupport f ⊆ Metric.closedBall (0 : Plane) (R + 1) := by
    simpa only [tsupport] using closure_minimal hsupp Metric.isClosed_closedBall
  have hK : IsCompact (tsupport f) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Plane) (R + 1))
      (isClosed_tsupport f) hclosure
  exact ⟨⟨f, hf⟩, hK⟩

/-- The polymer tail cutoff is nonnegative. -/
theorem polymerTailCutoff_nonneg (R : ℝ) (hR : 0 ≤ R) (y : Plane) :
    0 ≤ polymerTailCutoff R hR y := by
  dsimp [polymerTailCutoff]
  exact le_min (by norm_num) (le_max_left _ _)

/-- The polymer tail cutoff is bounded above by one. -/
theorem polymerTailCutoff_le_one (R : ℝ) (hR : 0 ≤ R) (y : Plane) :
    polymerTailCutoff R hR y ≤ 1 := by
  dsimp [polymerTailCutoff]
  exact min_le_left _ _

/-- The polymer tail cutoff equals one inside its defining ball. -/
theorem polymerTailCutoff_eq_one (R : ℝ) (hR : 0 ≤ R) (y : Plane)
    (hy : ‖y‖ ≤ R) : polymerTailCutoff R hR y = 1 := by
  dsimp [polymerTailCutoff]
  have hrad : 1 ≤ R + 1 - ‖y‖ := by linarith
  have hnonneg : 0 ≤ R + 1 - ‖y‖ := (by norm_num : 0 ≤ (1 : ℝ)).trans hrad
  change min 1 (max 0 (R + 1 - ‖y‖)) = 1
  rw [max_eq_right hnonneg, min_eq_left hrad]

/-- The polymer tail cutoff increases with its radius. -/
theorem polymerTailCutoff_mono {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hRS : R ≤ S) (y : Plane) :
    polymerTailCutoff R hR y ≤ polymerTailCutoff S hS y := by
  dsimp [polymerTailCutoff]
  apply min_le_min le_rfl
  exact max_le_max le_rfl (by linarith)

private theorem exists_eventually_polymerPairMarginal_clip_tail
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (f : C_c(Plane, ℝ))
    (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (hbox : ∀ x ∈ tsupport (f : Plane → ℝ), ‖x‖ ≤ B) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ R, ∀ hR : B + 8 ≤ R, ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => boundedReadoutClip
        (polymerFlatPairing f (polymerPairMarginalRadonMeasure ϑ N s t ω) -
          polymerCutoffPairing f (polymerTailCutoff R (le_trans hB (by linarith [hR])))
            (polymerPairMarginalRadonMeasure ϑ N s t ω))) disorderLaw ∧
      ∫ ω, boundedReadoutClip
        (polymerFlatPairing f (polymerPairMarginalRadonMeasure ϑ N s t ω) -
          polymerCutoffPairing f (polymerTailCutoff R (le_trans hB (by linarith [hR])))
            (polymerPairMarginalRadonMeasure ϑ N s t ω)) ∂disorderLaw ≤
        (ENNReal.ofReal (C * Real.exp (a * B ^ 2)) *
          ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) *
            volume (tsupport (f : Plane → ℝ))).toReal := by
  let A : Set Plane := tsupport (f : Plane → ℝ)
  have hA : MeasurableSet A := (isClosed_tsupport f).measurableSet
  have hAcompact : IsCompact A := f.hasCompactSupport
  obtain ⟨C, a, hC, ha, htail⟩ :=
    eventually_expected_polymerMeasure_pair_tail_le ϑ hs hst A hA B hB hbox
  refine ⟨C, a, hC, ha, ?_⟩
  intro R hR
  have hR0 : 0 ≤ R := le_trans hB (by linarith [hR])
  let T : Set Plane := {y : Plane | R ≤ ‖y‖}
  have hT : MeasurableSet T := (isClosed_le continuous_const continuous_norm).measurableSet
  let S : Set (Plane × Plane) := A ×ˢ T
  have hS : MeasurableSet S := hA.prod hT
  let E : ℝ≥0∞ := ENNReal.ofReal (C * Real.exp (a * B ^ 2)) *
    ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) * volume A
  have hEtop : E < ∞ := by
    dsimp [E]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      hAcompact.measure_lt_top
  filter_upwards [htail R hR] with N htailN
  have hTmeas : Measurable (fun ω : Disorder => polymerMeasure ϑ N s t ω S) :=
    (Measure.measurable_coe hS).comp (measurable_polymerMeasure ϑ N s t)
  have htailfinite : ∀ᵐ ω ∂disorderLaw, polymerMeasure ϑ N s t ω S < ∞ := by
    apply ae_lt_top hTmeas
    exact ne_of_lt (lt_of_le_of_lt htailN hEtop)
  have htailInt : Integrable
      (fun ω => (polymerMeasure ϑ N s t ω S).toReal) disorderLaw :=
    integrable_toReal_of_lintegral_ne_top hTmeas.aemeasurable
      (ne_of_lt (lt_of_le_of_lt htailN hEtop))
  let z (ω : Disorder) := polymerPairMarginalRadonMeasure ϑ N s t ω
  have hz : Measurable z := measurable_polymerPairMarginalRadonMeasure ϑ N s t
  have hpairmeas : Measurable (fun ω =>
      polymerCutoffPairing f (polymerTailCutoff R hR0) (z ω)) := by
    exact (RandomMeasure.measurable_vaguePairing_eval
      (polymerTensorTest f (polymerTailCutoff R hR0))).comp
      (measurable_fst.comp hz)
  have hflatmeas : Measurable (fun ω => polymerFlatPairing f (z ω)) := by
    exact (RandomMeasure.measurable_vaguePairing_eval f).comp (measurable_snd.comp hz)
  have hclipmeas : Measurable (fun ω => boundedReadoutClip
      (polymerFlatPairing f (z ω) -
        polymerCutoffPairing f (polymerTailCutoff R hR0) (z ω))) :=
    continuous_boundedReadoutClip.measurable.comp (hflatmeas.sub hpairmeas)
  have hclipInt : Integrable (fun ω => boundedReadoutClip
      (polymerFlatPairing f (z ω) -
        polymerCutoffPairing f (polymerTailCutoff R hR0) (z ω)))
      disorderLaw := by
    apply (integrable_const (1 : ℝ)).mono' hclipmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedReadoutClip_nonneg _)]
    exact boundedReadoutClip_le_one _
  have hpoint : ∀ᵐ ω ∂disorderLaw,
      boundedReadoutClip (polymerFlatPairing f (z ω) -
        polymerCutoffPairing f (polymerTailCutoff R hR0) (z ω)) ≤
        (polymerMeasure ϑ N s t ω S).toReal := by
    filter_upwards [htailfinite] with ω hω
    have hcutnonneg (y : Plane) :
        0 ≤ polymerTailCutoff R hR0 y :=
      polymerTailCutoff_nonneg R hR0 y
    have hcutle (y : Plane) : polymerTailCutoff R hR0 y ≤ 1 :=
      polymerTailCutoff_le_one R hR0 y
    have hcutone (y : Plane) (hy : ‖y‖ ≤ R) :
        polymerTailCutoff R hR0 y = 1 :=
      polymerTailCutoff_eq_one R hR0 y hy
    exact polymerFinite_clip_error_le_tail ϑ N s t ω f
      (polymerTailCutoff R hR0) hf hf1 hcutnonneg hcutle R hcutone
      A T hA hT (by rfl) (by rfl) (by simpa [S] using hω)
  have hmono := integral_mono_ae hclipInt htailInt hpoint
  have htoReal : ∫ ω, (polymerMeasure ϑ N s t ω S).toReal ∂disorderLaw =
      (∫⁻ ω, polymerMeasure ϑ N s t ω S ∂disorderLaw).toReal :=
    integral_toReal hTmeas.aemeasurable htailfinite
  have hrealBound : (∫⁻ ω, polymerMeasure ϑ N s t ω S ∂disorderLaw).toReal ≤ E.toReal :=
    ENNReal.toReal_mono hEtop.ne htailN
  have hmassBound : ∫ ω, boundedReadoutClip
      (polymerFlatPairing f (z ω) -
        polymerCutoffPairing f (polymerTailCutoff R hR0) (z ω))
      ∂disorderLaw ≤ E.toReal := by
    calc
      _ ≤ ∫ ω, (polymerMeasure ϑ N s t ω S).toReal ∂disorderLaw := hmono
      _ = (∫⁻ ω, polymerMeasure ϑ N s t ω S ∂disorderLaw).toReal := htoReal
      _ ≤ E.toReal := hrealBound
  refine ⟨?_, ?_⟩
  · simpa [z] using hclipInt
  · simpa [E, A, S, z] using hmassBound

private theorem ae_polymerPairMarginal_cutoff_tendsto
    (ϑ : ℝ) (D : Set ℝ) (hD0 : ∀ s ∈ D, 0 ≤ s)
    (i : PolymerPairIndex D) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (f : C_c(Plane, ℝ)) (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hbox : ∀ x ∈ tsupport (f : Plane → ℝ), ‖x‖ ≤ B)
    (Q : ProbabilityMeasure
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
    letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.vagueTopology (Plane × Plane)
    letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.polishSpace_positiveRadonMeasure_planePair
    letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
    letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
    letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
      RandomMeasure.vagueTopology Plane
    letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
    letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel⟩
    letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
    letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    Tendsto
        (fun n => polymerPairMarginalCoordinateLaw ϑ (ψ n) D i)
        atTop (𝓝 Q) →
      ∀ᵐ z ∂(Q : Measure _),
        Tendsto (fun k : ℕ => polymerCutoffPairing f
          (polymerTailCutoff (B + 8 + (k : ℝ)) (by
            have hk : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
            linarith [hB, hk])) z)
          atTop (𝓝 (polymerFlatPairing f z)) := by
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
  letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel⟩
  letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
  letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  intro hweak
  let Qn : ℕ → ProbabilityMeasure
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
    fun n => polymerPairMarginalCoordinateLaw ϑ (ψ n) D i
  let radius : ℕ → ℝ := fun k => B + 8 + (k : ℝ)
  have hradius (k : ℕ) : 0 ≤ radius k := by
    dsimp [radius]
    linarith [hB]
  let cutoff (k : ℕ) : C_c(Plane, ℝ) := polymerTailCutoff (radius k) (hradius k)
  let A (k : ℕ) (z : RandomMeasure.PlanePairRadonMeasure ×
      RandomMeasure.PlaneRadonMeasure) := polymerCutoffPairing f (cutoff k) z
  let Bfun (z : RandomMeasure.PlanePairRadonMeasure ×
      RandomMeasure.PlaneRadonMeasure) := polymerFlatPairing f z
  have hAcont (k : ℕ) : Continuous (A k) := by
    exact (RandomMeasure.continuous_vaguePairing (polymerTensorTest f (cutoff k))).comp
      continuous_fst
  have hBcont : Continuous Bfun :=
    (RandomMeasure.continuous_vaguePairing f).comp continuous_snd
  have hAmono (z : RandomMeasure.PlanePairRadonMeasure ×
      RandomMeasure.PlaneRadonMeasure) : Monotone (fun k => A k z) := by
    apply monotone_nat_of_le_succ
    intro k
    have hradiusMono : radius k ≤ radius (k + 1) := by
      dsimp [radius]
      norm_num
    have hcutMono (y : Plane) : cutoff k y ≤ cutoff (k + 1) y := by
      exact polymerTailCutoff_mono (hradius k) (hradius (k + 1)) hradiusMono y
    change (∫ p, f p.1 * cutoff k p.2 ∂z.1.1) ≤
      ∫ p, f p.1 * cutoff (k + 1) p.2 ∂z.1.1
    apply integral_mono
      (RandomMeasure.integrable_vagueTest z.1 (polymerTensorTest f (cutoff k)))
      (RandomMeasure.integrable_vagueTest z.1 (polymerTensorTest f (cutoff (k + 1))))
    intro p
    exact mul_le_mul_of_nonneg_left (hcutMono p.2) (hf p.1)
  have hupper : ∀ n k, ∀ᵐ z ∂(Qn n : Measure _), A k z ≤ Bfun z := by
    intro n k
    let F : Disorder →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
      fun ω => polymerPairMarginalRadonMeasure ϑ (ψ n)
        (i.1.1 : ℝ) (i.1.2 : ℝ) ω
    have hFmeas : Measurable F :=
      measurable_polymerPairMarginalRadonMeasure ϑ (ψ n)
        (i.1.1 : ℝ) (i.1.2 : ℝ)
    have hQn : (Qn n : Measure _) = Measure.map F disorderLaw := by
      exact polymerPairMarginalCoordinateLaw_eq_map_disorder ϑ (ψ n) D i
    let E : Set (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
      {z | A k z ≤ Bfun z}
    have hE : MeasurableSet E := (isClosed_le (hAcont k) hBcont).measurableSet
    have hAE : ∀ᵐ z ∂(Measure.map F disorderLaw), A k z ≤ Bfun z := by
      rw [ae_map_iff hFmeas.aemeasurable hE]
      exact Filter.Eventually.of_forall fun ω => by
        have hmap : Measure.map Prod.fst
            ((polymerPairMarginalRadonMeasure ϑ (ψ n)
              (i.1.1 : ℝ) (i.1.2 : ℝ) ω).1.1) =
            (polymerPairMarginalRadonMeasure ϑ (ψ n)
              (i.1.1 : ℝ) (i.1.2 : ℝ) ω).2.1 := rfl
        exact vaguePairing_polymerTensor_le_marginal _ _ hmap f (cutoff k) hf
          (fun y => polymerTailCutoff_le_one (radius k) (hradius k) y)
    rw [hQn]
    exact hAE
  obtain ⟨C, a, hC, ha, hclipTail⟩ :=
    exists_eventually_polymerPairMarginal_clip_tail ϑ
      (hD0 (i.1.1 : ℝ) i.1.1.2) i.2 f hf hf1 B hB hbox
  let ε (k : ℕ) : ℝ :=
    (ENNReal.ofReal (C * Real.exp (a * B ^ 2)) *
      ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * radius k ^ 2 / 4)) *
        volume (tsupport (f : Plane → ℝ))).toReal
  have hclip : ∀ k, ∀ᶠ n in atTop,
      Integrable (fun z => boundedReadoutClip (Bfun z - A k z)) (Qn n : Measure _) ∧
        ∫ z, boundedReadoutClip (Bfun z - A k z) ∂(Qn n : Measure _) ≤ ε k := by
    intro k
    have hN := hclipTail (radius k) (by dsimp [radius]; linarith [hB])
    filter_upwards [hψ.tendsto_atTop.eventually hN] with n hn
    rcases hn with ⟨hIntSource, hBoundSource⟩
    let F : Disorder →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
      fun ω => polymerPairMarginalRadonMeasure ϑ (ψ n)
        (i.1.1 : ℝ) (i.1.2 : ℝ) ω
    have hFmeas : Measurable F :=
      measurable_polymerPairMarginalRadonMeasure ϑ (ψ n)
        (i.1.1 : ℝ) (i.1.2 : ℝ)
    have hQn : (Qn n : Measure _) = Measure.map F disorderLaw := by
      exact polymerPairMarginalCoordinateLaw_eq_map_disorder ϑ (ψ n) D i
    have hsource : Integrable
        (fun ω => boundedReadoutClip (Bfun (F ω) - A k (F ω))) disorderLaw := by
      simpa [F, A, Bfun, cutoff, radius, ε] using hIntSource
    have hcMeas : Measurable (fun z => boundedReadoutClip (Bfun z - A k z)) :=
      continuous_boundedReadoutClip.measurable.comp (hBcont.sub (hAcont k)).measurable
    have hstate : Integrable (fun z => boundedReadoutClip (Bfun z - A k z))
        (Measure.map F disorderLaw) :=
      (integrable_map_measure hcMeas.aestronglyMeasurable
        hFmeas.aemeasurable).mpr hsource
    have hstateQ : Integrable (fun z => boundedReadoutClip (Bfun z - A k z))
        (Qn n : Measure _) := by rw [hQn]; exact hstate
    have hmapInt : ∫ z, boundedReadoutClip (Bfun z - A k z)
        ∂(Measure.map F disorderLaw) =
        ∫ ω, boundedReadoutClip (Bfun (F ω) - A k (F ω)) ∂disorderLaw :=
      integral_map hFmeas.aemeasurable hstate.aestronglyMeasurable
    have hbound : ∫ z, boundedReadoutClip (Bfun z - A k z) ∂(Qn n : Measure _) ≤ ε k := by
      rw [hQn, hmapInt]
      simpa [F, A, Bfun, cutoff, radius, ε] using hBoundSource
    exact ⟨hstateQ, hbound⟩
  letI : TopologicalSpace (RandomMeasure.PlanePairRadonMeasure ×
      RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : BorelSpace (RandomMeasure.PlanePairRadonMeasure ×
      RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace (RandomMeasure.PlanePairRadonMeasure ×
      RandomMeasure.PlaneRadonMeasure) := inferInstance
  have hε : Tendsto ε atTop (𝓝 0) := by
    let r : ℕ → ℝ := fun k => radius k
    let K : ℝ := C * Real.exp (a * B ^ 2) * (4 * Real.pi / a) *
      (volume (tsupport (f : Plane → ℝ))).toReal
    have hεeq (k : ℕ) : ε k = K * Real.exp (-a * r k ^ 2 / 4) := by
      dsimp [ε, K, r]
      calc
        _ = (ENNReal.ofReal (C * Real.exp (a * B ^ 2)) *
            ENNReal.ofReal ((4 * Real.pi / a) * Real.exp
              (-a * (B + 8 + (k : ℝ)) ^ 2 / 4)) *
            volume (tsupport (f : Plane → ℝ))).toReal := rfl
        _ = (C * Real.exp (a * B ^ 2)) *
            ((4 * Real.pi / a) * Real.exp
              (-a * (B + 8 + (k : ℝ)) ^ 2 / 4)) *
            (volume (tsupport (f : Plane → ℝ))).toReal := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
                ENNReal.toReal_ofReal (by positivity),
                ENNReal.toReal_ofReal (by positivity)]
        _ = K * Real.exp (-a * (B + 8 + (k : ℝ)) ^ 2 / 4) := by
              dsimp [K]
              ring
    have hr : Tendsto r atTop atTop := by
      apply tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ))
      · intro k
        dsimp [r, radius]
        linarith [hB]
      · exact tendsto_natCast_atTop_atTop
    have hpow := (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hr
    have harg : Tendsto (fun k : ℕ => -a * r k ^ 2 / 4) atTop atBot := by
      have hconst : (-(a / 4 : ℝ)) < 0 := by linarith [ha]
      have h' := hpow.const_mul_atTop_of_neg hconst
      convert h' using 1
      ext k
      simp only [Function.comp_apply]
      ring
    have hexp : Tendsto (fun k : ℕ => Real.exp (-a * r k ^ 2 / 4)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    rw [show ε = fun k => K * Real.exp (-a * r k ^ 2 / 4) from funext hεeq]
    simpa using tendsto_const_nhds.mul hexp
  exact ae_tendsto_of_bounded_weak_approximation Qn Q hweak A Bfun hAcont hBcont
    hAmono hupper ε hε hclip

private theorem polymerCutoffPairing_tendsto_map_fst
    (μ : RandomMeasure.PlanePairRadonMeasure)
    (ν : RandomMeasure.PlaneRadonMeasure) (f : C_c(Plane, ℝ))
    (hf : ∀ x, 0 ≤ f x)
    (B : ℝ) (hB : 0 ≤ B)
    (hlim : Tendsto
      (fun k : ℕ => polymerCutoffPairing f
        (polymerTailCutoff (B + 8 + (k : ℝ)) (by
          have hk : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
          linarith [hB, hk]))
        (μ, ν))
      atTop (𝓝 (polymerFlatPairing f (μ, ν)))) :
    Integrable f (Measure.map Prod.fst (μ.1 : Measure (Plane × Plane))) ∧
      polymerFlatPairing f (μ, ν) =
        ∫ x, f x ∂Measure.map Prod.fst (μ.1 : Measure (Plane × Plane)) := by
  let radius : ℕ → ℝ := fun k => B + 8 + (k : ℝ)
  have hradius (k : ℕ) : 0 ≤ radius k := by
    dsimp [radius]
    linarith [hB]
  let cutoff (k : ℕ) : C_c(Plane, ℝ) := polymerTailCutoff (radius k) (hradius k)
  let A (k : ℕ) : ℝ := polymerCutoffPairing f (cutoff k) (μ, ν)
  let Bval : ℝ := polymerFlatPairing f (μ, ν)
  have hAeq (k : ℕ) : A k =
      ∫ p, f p.1 * cutoff k p.2 ∂μ.1 := by
    rfl
  have hAmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro k
    rw [hAeq, hAeq]
    apply integral_mono
      (RandomMeasure.integrable_vagueTest μ (polymerTensorTest f (cutoff k)))
      (RandomMeasure.integrable_vagueTest μ (polymerTensorTest f (cutoff (k + 1))))
    intro p
    have hrad : radius k ≤ radius (k + 1) := by
      dsimp [radius]
      norm_num
    exact mul_le_mul_of_nonneg_left
      (polymerTailCutoff_mono (hradius k) (hradius (k + 1)) hrad p.2) (hf p.1)
  have hA_nonneg (k : ℕ) : 0 ≤ A k := by
    rw [hAeq]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun p =>
      mul_nonneg (hf p.1) (polymerTailCutoff_nonneg (radius k) (hradius k) p.2))
  have hAtoB : Tendsto A atTop (𝓝 Bval) := by
    simpa only [A, Bval, cutoff, radius] using hlim
  have hsupA : (⨆ k, ENNReal.ofReal (A k)) = ENNReal.ofReal Bval := by
    apply iSup_eq_of_tendsto
    · intro i j hij
      exact ENNReal.ofReal_le_ofReal (hAmono hij)
    · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hAtoB
  have hlintegral_each (k : ℕ) :
      ∫⁻ p, ENNReal.ofReal (f p.1 * cutoff k p.2) ∂μ.1 =
        ENNReal.ofReal (A k) := by
    rw [hAeq]
    symm
    apply ofReal_integral_eq_lintegral_ofReal
      (RandomMeasure.integrable_vagueTest μ (polymerTensorTest f (cutoff k)))
    exact Filter.Eventually.of_forall fun p =>
      mul_nonneg (hf p.1) (polymerTailCutoff_nonneg (radius k) (hradius k) p.2)
  have hfun_mono : Monotone fun k (p : Plane × Plane) =>
      ENNReal.ofReal (f p.1 * cutoff k p.2) := by
    intro k j hkj p
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (polymerTailCutoff_mono (hradius k) (hradius j) (by
        have hcast : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
        dsimp [radius]
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_left hcast (B + 8)) p.2) (hf p.1)
  have hpoint_sup (p : Plane × Plane) :
      (⨆ k, ENNReal.ofReal (f p.1 * cutoff k p.2)) = ENNReal.ofReal (f p.1) := by
    apply le_antisymm
    · refine iSup_le fun k => ?_
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_of_le_one_right (hf p.1) (polymerTailCutoff_le_one
        (radius k) (hradius k) p.2)
    · obtain ⟨k, hk⟩ := exists_nat_gt (‖p.2‖ - B - 8)
      have hinside : ‖p.2‖ ≤ radius k := by
        dsimp [radius]
        have hk' : (k : ℝ) > ‖p.2‖ - B - 8 := by exact_mod_cast hk
        linarith
      have hone : cutoff k p.2 = 1 := polymerTailCutoff_eq_one (radius k)
        (hradius k) p.2 hinside
      calc
        ENNReal.ofReal (f p.1) = ENNReal.ofReal (f p.1 * cutoff k p.2) := by
          rw [hone, mul_one]
        _ ≤ ⨆ j, ENNReal.ofReal (f p.1 * cutoff j p.2) :=
          le_iSup (fun j => ENNReal.ofReal (f p.1 * cutoff j p.2)) k
  have hlintegral_sup :
      (∫⁻ p, ENNReal.ofReal (f p.1) ∂μ.1) =
        ⨆ k, ∫⁻ p, ENNReal.ofReal (f p.1 * cutoff k p.2) ∂μ.1 := by
    let u : ℕ → Plane × Plane → ℝ≥0∞ := fun k p =>
      ENNReal.ofReal (f p.1 * cutoff k p.2)
    have hu (k : ℕ) : Measurable (u k) := by
      change Measurable (fun p : Plane × Plane =>
        ENNReal.ofReal (f p.1 * cutoff k p.2))
      exact ((f.continuous.comp continuous_fst).mul
        ((cutoff k).continuous.comp continuous_snd)).measurable.ennreal_ofReal
    calc
      _ = ∫⁻ p, ⨆ k, u k p ∂μ.1 := by
        congr 1
        funext p
        exact (hpoint_sup p).symm
      _ = ⨆ k, ∫⁻ p, u k p ∂μ.1 := lintegral_iSup hu hfun_mono
  have hpair_to_marginal :
      ∫⁻ p, ENNReal.ofReal (f p.1) ∂μ.1 =
        ∫⁻ x, ENNReal.ofReal (f x) ∂ν.1 := by
    calc
      _ = ⨆ k, ∫⁻ p, ENNReal.ofReal (f p.1 * cutoff k p.2) ∂μ.1 := hlintegral_sup
      _ = ⨆ k, ENNReal.ofReal (A k) := by
        congr 1
        funext k
        exact hlintegral_each k
      _ = ENNReal.ofReal Bval := hsupA
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ν.1 := by
        simpa [Bval, polymerFlatPairing, RandomMeasure.vaguePairing] using
          (ofReal_integral_eq_lintegral_ofReal
          (RandomMeasure.integrable_vagueTest ν f)
          (Filter.Eventually.of_forall hf))
  have hmap_lintegral :
      ∫⁻ x, ENNReal.ofReal (f x) ∂Measure.map Prod.fst μ.1 =
        ∫⁻ p, ENNReal.ofReal (f p.1) ∂μ.1 := by
    exact lintegral_map (f.continuous.measurable.ennreal_ofReal) measurable_fst
  have hmap_lintegral_eq :
      ∫⁻ x, ENNReal.ofReal (f x) ∂Measure.map Prod.fst μ.1 = ENNReal.ofReal Bval := by
    calc
      _ = ∫⁻ p, ENNReal.ofReal (f p.1) ∂μ.1 := hmap_lintegral
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ν.1 := hpair_to_marginal
      _ = ENNReal.ofReal Bval := by
        simpa [Bval, polymerFlatPairing, RandomMeasure.vaguePairing] using
          (ofReal_integral_eq_lintegral_ofReal
            (RandomMeasure.integrable_vagueTest ν f)
            (Filter.Eventually.of_forall hf)).symm
  have hfmap_nonneg : 0 ≤ᵐ[Measure.map Prod.fst μ.1] f :=
    Filter.Eventually.of_forall hf
  have hmap_integrable : Integrable f (Measure.map Prod.fst μ.1) := by
    refine ⟨f.continuous.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hfmap_nonneg, hmap_lintegral_eq]
    exact ENNReal.ofReal_lt_top
  refine ⟨hmap_integrable, ?_⟩
  calc
    Bval = ENNReal.toReal (ENNReal.ofReal Bval) := by
      rw [ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall hf)
    _ = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (f x)
        ∂Measure.map Prod.fst μ.1) := congrArg ENNReal.toReal hmap_lintegral_eq.symm
    _ = ∫ x, f x ∂Measure.map Prod.fst μ.1 := by
      symm
      exact integral_eq_lintegral_of_nonneg_ae hfmap_nonneg
        f.continuous.aestronglyMeasurable

private theorem ae_polymerPairMarginal_test_eq_projection
    (ϑ : ℝ) (D : Set ℝ) (hD0 : ∀ s ∈ D, 0 ≤ s)
    (i : PolymerPairIndex D) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (f : C_c(Plane, ℝ)) (hf : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hbox : ∀ x ∈ tsupport (f : Plane → ℝ), ‖x‖ ≤ B)
    (Q : ProbabilityMeasure
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
    letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.vagueTopology (Plane × Plane)
    letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.polishSpace_positiveRadonMeasure_planePair
    letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
    letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
    letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
      RandomMeasure.vagueTopology Plane
    letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
    letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel⟩
    letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
    letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    Tendsto (fun n => polymerPairMarginalCoordinateLaw ϑ (ψ n) D i)
      atTop (𝓝 Q) → ∀ᵐ z ∂(Q : Measure _),
        Integrable f (Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane))) ∧
          polymerFlatPairing f z =
            ∫ x, f x ∂Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane)) := by
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
  letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel⟩
  letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
  letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  intro hweak
  filter_upwards [ae_polymerPairMarginal_cutoff_tendsto ϑ D hD0 i ψ hψ f hf hf1
      B hB hbox Q hweak] with z hz
  exact polymerCutoffPairing_tendsto_map_fst z.1 z.2 f hf B hB hz

private theorem exists_polymer_support_radius (f : C_c(Plane, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport (f : Plane → ℝ), ‖x‖ ≤ B := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp f.hasCompactSupport.isBounded
  let B : ℝ := max R 0
  refine ⟨B, le_max_right _ _, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.closedBall (0 : Plane) R := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at hxball
  exact hxball.trans (le_max_left _ _)

private theorem exists_vagueMassTest_radius (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport
        (RandomMeasure.vagueMassTest
          (RandomMeasure.vagueCompactExhaustion Plane) n : Plane → ℝ),
          ‖x‖ ≤ B := by
  let K : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  have hcompact : IsCompact (K (n + 1)) := K.isCompact (n + 1)
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hcompact.isBounded
  let B : ℝ := max R 0
  refine ⟨B, le_max_right _ _, ?_⟩
  intro x hx
  have hsupport := (RandomMeasure.vagueMassTest_spec K n).2.2.2
  have hxK : x ∈ K (n + 1) := hsupport hx
  have hxball : x ∈ Metric.closedBall (0 : Plane) R := hR hxK
  rw [Metric.mem_closedBall, dist_zero_right] at hxball
  exact hxball.trans (le_max_left _ _)

/-- In a subsequential polymer limit, the first projection of the pair measure is locally finite almost surely. -/
theorem ae_polymerPairMarginal_projection_locallyFinite
    (ϑ : ℝ) (D : Set ℝ) (hD0 : ∀ s ∈ D, 0 ≤ s)
    (i : PolymerPairIndex D) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (Q : ProbabilityMeasure
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
    letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.vagueTopology (Plane × Plane)
    letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.polishSpace_positiveRadonMeasure_planePair
    letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
    letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
    letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
      RandomMeasure.vagueTopology Plane
    letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
    letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel⟩
    letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
    letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    Tendsto (fun n => polymerPairMarginalCoordinateLaw ϑ (ψ n) D i)
      atTop (𝓝 Q) →
    ∀ᵐ z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure
      ∂(Q : Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)),
      IsLocallyFiniteMeasure
      (Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane))) := by
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
  letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel⟩
  letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
  letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  intro hweak
  let K : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  have hfinite (n : ℕ) :
      ∀ᵐ z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure
        ∂(Q : Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)),
      Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane)) (K n) < ∞ := by
    obtain ⟨B, hB, hbox⟩ := exists_vagueMassTest_radius n
    let f : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest K n
    have hspec := RandomMeasure.vagueMassTest_spec K n
    filter_upwards [ae_polymerPairMarginal_test_eq_projection ϑ D hD0 i ψ hψ
      f hspec.1 hspec.2.1 B hB hbox Q hweak] with z hz
    let ρ : Measure Plane := Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane))
    have hρnonneg : 0 ≤ᵐ[ρ] f := Filter.Eventually.of_forall hspec.1
    have hlinfinite : ∫⁻ x, ENNReal.ofReal (f x) ∂ρ < ∞ := by
      rw [← hasFiniteIntegral_iff_ofReal hρnonneg]
      exact hz.1.hasFiniteIntegral
    have hmass : ρ (K n) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ρ := by
      rw [← lintegral_indicator_one ((K.isCompact n).isClosed.measurableSet)]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K n
      · rw [Set.indicator_of_mem hx]
        change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (f x)
        rw [show f x = 1 from hspec.2.2.1 x hx]
        norm_num
      · rw [Set.indicator_of_notMem hx]
        positivity
    exact lt_of_le_of_lt hmass hlinfinite
  have hfiniteAll :
      ∀ᵐ z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure
        ∂(Q : Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)),
      ∀ n,
      Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane)) (K n) < ∞ := by
    rw [ae_all_iff]
    exact hfinite
  filter_upwards [hfiniteAll] with z hz
  exact (RandomMeasure.locallyFinite_iff_finite_compactExhaustion K
    (Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane)))).2 hz

/-- In a subsequential polymer limit, compact-test pairings of the marginal agree with the first projection almost surely. -/
theorem ae_polymerPairMarginal_pairing_eq_projection
    (ϑ : ℝ) (D : Set ℝ) (hD0 : ∀ s ∈ D, 0 ≤ s)
    (i : PolymerPairIndex D) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (Q : ProbabilityMeasure
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
    (f : C_c(Plane, ℝ)) :
    letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.vagueTopology (Plane × Plane)
    letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.polishSpace_positiveRadonMeasure_planePair
    letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
    letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
    letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
      RandomMeasure.vagueTopology Plane
    letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
    letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel⟩
    letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
    letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    Tendsto (fun n => polymerPairMarginalCoordinateLaw ϑ (ψ n) D i)
      atTop (𝓝 Q) →
    ∀ᵐ z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure
      ∂(Q : Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)),
      polymerFlatPairing f z =
        ∫ x, f x ∂Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane)) := by
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
  letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel⟩
  letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
  letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  intro hweak
  let K : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  obtain ⟨n, hsupport⟩ := RandomMeasure.exists_vagueExhaustionWindow_support K f
  let h : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest K n
  have hspec := RandomMeasure.vagueMassTest_spec K n
  have hcompactImage : IsCompact ((fun x : Plane => |f x|) '' K n) :=
    (K.isCompact n).image (_root_.continuous_abs.comp f.continuous)
  obtain ⟨M₀, hM₀⟩ := hcompactImage.bddAbove
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hfzero (x : Plane) (hx : x ∉ K n) : f x = 0 := by
    by_contra hne
    apply hx
    exact hsupport (subset_closure (Function.mem_support.mpr hne))
  have hfab (x : Plane) : |f x| ≤ M := by
    by_cases hx : x ∈ K n
    · exact (hM₀ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · simp [hfzero x hx, M]
  let C : ℝ := 2 * M + 1
  have hC : 0 < C := by dsimp [C, M]; positivity
  have hCne : C ≠ 0 := hC.ne'
  let g : C_c(Plane, ℝ) := C⁻¹ • (f + M • h)
  have hg_nonneg (x : Plane) : 0 ≤ g x := by
    by_cases hx : x ∈ K n
    · have hlower : -M ≤ f x := (abs_le.mp (hfab x)).1
      have hone := hspec.2.2.1 x hx
      change 0 ≤ C⁻¹ * (f x + M * h x)
      rw [hone]
      exact mul_nonneg (inv_nonneg.mpr hC.le) (by linarith)
    · change 0 ≤ C⁻¹ * (f x + M * h x)
      rw [hfzero x hx]
      have hhpos : 0 ≤ h x := by simpa [h] using hspec.1 x
      simpa only [zero_add] using
        (mul_nonneg (inv_nonneg.mpr hC.le) (mul_nonneg hM hhpos))
  have hg_le_one (x : Plane) : g x ≤ 1 := by
    have hupper : f x + M * h x ≤ 2 * M := by
      calc
        f x + M * h x ≤ M + M * 1 :=
          add_le_add (le_trans (le_abs_self _) (hfab x))
            (mul_le_mul_of_nonneg_left (hspec.2.1 x) hM)
        _ = 2 * M := by ring
    calc
      g x = (f x + M * h x) / C := by
        change C⁻¹ * (f x + M * h x) = _
        field_simp [hCne]
      _ ≤ 1 := (div_le_iff₀ hC).2 (by dsimp [C]; linarith)
  have hrepr : f = C • g - M • h := by
    ext x
    simp [g, h, smul_eq_mul]
    field_simp [hCne]
    ring
  obtain ⟨Bg, hBg, hboxg⟩ := exists_polymer_support_radius g
  obtain ⟨Bh, hBh, hboxh⟩ := exists_vagueMassTest_radius n
  have hgoodg := ae_polymerPairMarginal_test_eq_projection ϑ D hD0 i ψ hψ
    g hg_nonneg hg_le_one Bg hBg hboxg Q hweak
  have hgoodh := ae_polymerPairMarginal_test_eq_projection ϑ D hD0 i ψ hψ
    h hspec.1 hspec.2.1 Bh hBh hboxh Q hweak
  filter_upwards [hgoodg, hgoodh] with z hzG hzH
  let ρ : Measure Plane := Measure.map Prod.fst (z.1.1 : Measure (Plane × Plane))
  have hfint : Integrable f ρ := by
    rw [hrepr]
    exact (hzG.1.const_mul C).sub (hzH.1.const_mul M)
  have hgSourceInt : Integrable (C • g) z.2.1 :=
    (RandomMeasure.integrable_vagueTest z.2 g).const_mul C
  have hhSourceInt : Integrable (M • h) z.2.1 :=
    (RandomMeasure.integrable_vagueTest z.2 h).const_mul M
  have hgEq : ∫ x, g x ∂z.2.1 = ∫ x, g x ∂ρ := by
    simpa [polymerFlatPairing, RandomMeasure.vaguePairing] using hzG.2
  have hhEq : ∫ x, h x ∂z.2.1 = ∫ x, h x ∂ρ := by
    simpa [polymerFlatPairing, RandomMeasure.vaguePairing] using hzH.2
  calc
    polymerFlatPairing f z = ∫ x, f x ∂z.2.1 := rfl
    _ = ∫ x, (C • g - M • h) x ∂z.2.1 := by rw [hrepr]
    _ = (∫ x, C * g x ∂z.2.1) - ∫ x, M * h x ∂z.2.1 :=
      integral_sub hgSourceInt hhSourceInt
    _ = C * (∫ x, g x ∂z.2.1) - M * (∫ x, h x ∂z.2.1) := by
      rw [integral_const_mul, integral_const_mul]
    _ = C * (∫ x, g x ∂ρ) - M * (∫ x, h x ∂ρ) := by rw [hgEq, hhEq]
    _ = ∫ x, f x ∂ρ := by
      calc
        _ = (∫ x, C * g x ∂ρ) - ∫ x, M * h x ∂ρ := by
          rw [integral_const_mul, integral_const_mul]
        _ = ∫ x, (C * g x - M * h x) ∂ρ := (integral_sub
          ((hzG.1.const_mul C)) ((hzH.1.const_mul M))).symm
        _ = ∫ x, f x ∂ρ := by
          have hfun : (fun x : Plane => C * g x - M * h x) = f := by
            funext x
            have hval := congrArg (fun q : C_c(Plane, ℝ) => q x) hrepr.symm
            simpa [smul_eq_mul] using hval
          rw [hfun]



end Critical2DKPZ.SHF.Limit

end
