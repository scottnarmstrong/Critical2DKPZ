/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Seminorm
public import Critical2DKPZ.Analysis.Sobolev.WeightedFourierIntegrability
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# The L¹ action bound for convolution on L²

An integrable scalar kernel acts on an L² function by integrating its translated L² classes.
The resulting Bochner integral is the L² convolution operator and has norm at most the L¹ norm
of the kernel times the L² norm of the input. This is the unweighted operator estimate used in
the weighted Fourier convolution argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace Critical2DKPZ.Analysis.Sobolev

/-- The continuous translation map used to represent an `L²` shift. -/
def l2TranslationMap (η : Plane) : C(Plane, Plane) :=
  ⟨fun x => x - η, by fun_prop⟩

/-- Translation preserves planar volume. -/
theorem measurePreserving_l2TranslationMap (η : Plane) :
    MeasurePreserving (l2TranslationMap η) (volume : Measure Plane) volume := by
  change MeasurePreserving (fun x : Plane => x - η) volume volume
  simpa only [sub_eq_add_neg] using
    (MeasureTheory.measurePreserving_add_right (volume : Measure Plane) (-η))

/-- The family of translation maps varies continuously in the translation parameter. -/
theorem continuous_l2TranslationMap : Continuous l2TranslationMap := by
  let G : C(Plane × Plane, Plane) := ⟨fun p => p.2 - p.1, by fun_prop⟩
  have h : (fun η : Plane => l2TranslationMap η) = G.curry := by
    funext η
    ext x
    rfl
  change Continuous (fun η : Plane => l2TranslationMap η)
  exact h ▸ G.curry.continuous

/-- Translation of an `L²` class by the map `x ↦ x - η`. -/
noncomputable def translateL2 (η : Plane) (f : Lp ℂ 2 (volume : Measure Plane)) :
    Lp ℂ 2 (volume : Measure Plane) :=
  Lp.compMeasurePreserving (l2TranslationMap η) (measurePreserving_l2TranslationMap η) f

private theorem continuous_translateL2 (f : Lp ℂ 2 (volume : Measure Plane)) :
    Continuous (fun η : Plane => translateL2 η f) := by
  exact continuous_const.compMeasurePreservingLp continuous_l2TranslationMap
    measurePreserving_l2TranslationMap (by norm_num)

/-- The square root of the negative Sobolev Fourier weight. -/
noncomputable def negSobolevWeightSqrt (a : ℝ) (ξ : Plane) : ℝ :=
  Real.sqrt ((1 + ‖ξ‖ ^ 2) ^ (-a))

/-- The pointwise multiplier that compares the weighted norm before and after one frequency
translation. -/
noncomputable def negSobolevTranslationMultiplier (a : ℝ) (η ξ : Plane) : ℝ :=
  negSobolevWeightSqrt a ξ / negSobolevWeightSqrt a (ξ - η)

private theorem continuous_negSobolevWeightSqrt (a : ℝ) :
    Continuous (negSobolevWeightSqrt a) := by
  have hb : Continuous (fun ξ : Plane => (1 : ℝ) + ‖ξ‖ ^ 2) := by fun_prop
  have hp : Continuous (fun ξ : Plane => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) :=
    hb.rpow_const fun ξ => Or.inl (by positivity)
  have hpos : ∀ ξ : Plane, 0 < ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a) := by
    intro ξ
    exact Real.rpow_pos_of_pos (by positivity) _
  have hhalf : Continuous (fun ξ : Plane =>
      (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ)) :=
    hp.rpow_const fun ξ => Or.inl (ne_of_gt (hpos ξ))
  have heq : negSobolevWeightSqrt a = fun ξ : Plane =>
      (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ) := by
    funext ξ
    simp [negSobolevWeightSqrt, Real.sqrt_eq_rpow]
  exact heq ▸ hhalf

private theorem negSobolevWeightSqrt_pos (a : ℝ) (ξ : Plane) :
    0 < negSobolevWeightSqrt a ξ := by
  unfold negSobolevWeightSqrt
  exact Real.sqrt_pos.2 (Real.rpow_pos_of_pos (by positivity) _)

private theorem continuous_negSobolevTranslationMultiplier (a : ℝ) (η : Plane) :
    Continuous (fun ξ => negSobolevTranslationMultiplier a η ξ) := by
  change Continuous (fun ξ : Plane =>
    negSobolevWeightSqrt a ξ / negSobolevWeightSqrt a (ξ - η))
  exact (continuous_negSobolevWeightSqrt a).div₀
    ((continuous_negSobolevWeightSqrt a).comp (continuous_id.sub continuous_const))
    (fun ξ => ne_of_gt (negSobolevWeightSqrt_pos a (ξ - η)))

private theorem continuous_negSobolevTranslationMultiplier_left (a : ℝ) (ξ : Plane) :
    Continuous (fun η : Plane => negSobolevTranslationMultiplier a η ξ) := by
  change Continuous (fun η : Plane =>
    negSobolevWeightSqrt a ξ / negSobolevWeightSqrt a (ξ - η))
  exact continuous_const.div₀
    ((continuous_negSobolevWeightSqrt a).comp (continuous_const.sub continuous_id))
    (fun η => ne_of_gt (negSobolevWeightSqrt_pos a (ξ - η)))

/-- Finite negative Sobolev energy gives an ordinary `L²` representative after multiplying
the localized Fourier transform by the square root of its frequency weight. -/
theorem memLp_negSobolevWeightedLocalizedFourier (a : ℝ) (T : Distr) (χ : TestFn)
    (hfinite : localNegSobolevSq a T χ < ⊤) :
    MemLp (fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) *
      localizedFourier T χ ξ) 2 (volume : Measure Plane) := by
  let B : Plane → ℝ := fun ξ => (1 + ‖ξ‖ ^ 2) ^ (-a) *
    ‖localizedFourier T χ ξ‖ ^ 2
  have hweight : Continuous (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ (-a)) := by
    have hb : Continuous (fun ξ : Plane => (1 : ℝ) + ‖ξ‖ ^ 2) := by fun_prop
    exact hb.rpow_const fun ξ => Or.inl (by positivity)
  have hBcont : Continuous B := by
    change Continuous (fun ξ : Plane =>
      (1 + ‖ξ‖ ^ 2) ^ (-a) * ‖localizedFourier T χ ξ‖ ^ 2)
    exact hweight.mul ((continuous_localizedFourier T χ).norm.pow 2)
  have hBnonneg (ξ : Plane) : 0 ≤ B ξ := by
    dsimp [B]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  have hBmeas : AEStronglyMeasurable B volume := hBcont.measurable.aestronglyMeasurable
  have hEnergyInt :
      (∫⁻ ξ : Plane, ENNReal.ofReal (B ξ)) < ⊤ := by
    have hEq : (∫⁻ ξ : Plane, ENNReal.ofReal (B ξ)) =
        ∫⁻ ξ : Plane, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a) *
          ((T (χ.mulCos ξ)) ^ 2 + (T (χ.mulSin ξ)) ^ 2)) := by
      apply lintegral_congr
      intro ξ
      dsimp [B]
      rw [norm_localizedFourier_sq]
    have h := hfinite
    unfold localNegSobolevSq at h
    rw [← hEq] at h
    have hcpos : 0 < ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hsplit := (ENNReal.mul_lt_top_iff.mp h)
    rcases hsplit with ⟨_, hI⟩ | hc0 | hI0
    · exact hI
    · exact (ne_of_gt hcpos hc0).elim
    · simp [hI0]
  have hBint : Integrable B volume := by
    apply (lintegral_ofReal_ne_top_iff_integrable hBmeas
      (Filter.Eventually.of_forall hBnonneg)).1
    exact ne_of_lt hEnergyInt
  have hweightedSq : Integrable (fun ξ : Plane =>
      ‖(negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T χ ξ‖ ^ 2) volume := by
    have heq : (fun ξ : Plane =>
        ‖(negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T χ ξ‖ ^ 2) = B := by
      funext ξ
      dsimp [B, negSobolevWeightSqrt]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ Real.sqrt ((1 + ‖ξ‖ ^ 2) ^ (-a))),
        mul_pow, Real.sq_sqrt (Real.rpow_nonneg (by positivity) _)]
    rw [heq]
    exact hBint
  have hsm : AEStronglyMeasurable
      (fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T χ ξ)
      (volume : Measure Plane) := by
    exact ((Complex.continuous_ofReal.comp (continuous_negSobolevWeightSqrt a)).mul
      (continuous_localizedFourier T χ)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hsm).mpr hweightedSq

private theorem ofReal_norm_sq_eq_enorm_sq (z : ℂ) :
    ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg z)]
  simp

private theorem negSobolevTranslationMultiplier_le {a : ℝ} (ha : 0 ≤ a) (η ξ : Plane) :
    negSobolevTranslationMultiplier a η ξ ≤
      Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) := by
  have hshift := sqrt_negSobolevWeight_shift_le ha ξ η
  have hden : 0 < negSobolevWeightSqrt a (ξ - η) := by
    unfold negSobolevWeightSqrt
    exact Real.sqrt_pos.2 (Real.rpow_pos_of_pos (by positivity) _)
  exact (div_le_iff₀ hden).2 (by simpa [negSobolevTranslationMultiplier,
    negSobolevWeightSqrt] using hshift)

/-- Multiplication by a translated Sobolev weight preserves square integrability. -/
theorem memLp_weightedMultiplierL2 {a : ℝ} (ha : 0 ≤ a) (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    MemLp (fun ξ => (negSobolevTranslationMultiplier a η ξ : ℂ) * f ξ)
      2 (volume : Measure Plane) := by
  have hmul : Continuous (fun ξ : Plane =>
      (negSobolevTranslationMultiplier a η ξ : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_negSobolevTranslationMultiplier a η)
  have hsm : AEStronglyMeasurable
      (fun ξ : Plane => (negSobolevTranslationMultiplier a η ξ : ℂ) * f ξ)
      (volume : Measure Plane) :=
    hmul.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  apply MemLp.of_le_mul (Lp.memLp f) hsm
  filter_upwards with ξ
  rw [norm_mul, Complex.norm_real]
  have hr : 0 ≤ negSobolevTranslationMultiplier a η ξ := by
    unfold negSobolevTranslationMultiplier negSobolevWeightSqrt
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right (negSobolevTranslationMultiplier_le ha η ξ)
    (norm_nonneg _)

/-- Applying the polynomially bounded multiplier that compares the negative Sobolev weights at
`ξ` and `ξ - η`. -/
noncomputable def weightedMultiplierL2 {a : ℝ} (ha : 0 ≤ a) (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) : Lp ℂ 2 (volume : Measure Plane) :=
  (memLp_weightedMultiplierL2 ha η f).toLp
    (fun ξ => (negSobolevTranslationMultiplier a η ξ : ℂ) * f ξ)

/-- The norm of the weighted multiplier action is bounded by its polynomial shift factor. -/
theorem norm_weightedMultiplierL2_le {a : ℝ} (ha : 0 ≤ a) (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    ‖weightedMultiplierL2 ha η f‖ ≤
      Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hcoe : weightedMultiplierL2 ha η f =ᵐ[volume] fun ξ =>
      (negSobolevTranslationMultiplier a η ξ : ℂ) * f ξ :=
    MemLp.coeFn_toLp (memLp_weightedMultiplierL2 ha η f)
  filter_upwards [hcoe] with ξ hξ
  rw [hξ, norm_mul, Complex.norm_real]
  have hr : 0 ≤ negSobolevTranslationMultiplier a η ξ := by
    unfold negSobolevTranslationMultiplier negSobolevWeightSqrt
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right (negSobolevTranslationMultiplier_le ha η ξ)
    (norm_nonneg _)

/-- The weighted multiplier action is linear in its `L²` input. -/
theorem weightedMultiplierL2_sub {a : ℝ} (ha : 0 ≤ a) (η : Plane)
    (f g : Lp ℂ 2 (volume : Measure Plane)) :
    weightedMultiplierL2 ha η (f - g) =
      weightedMultiplierL2 ha η f - weightedMultiplierL2 ha η g := by
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp (memLp_weightedMultiplierL2 ha η (f - g)),
    Lp.coeFn_sub f g,
    MemLp.coeFn_toLp (memLp_weightedMultiplierL2 ha η f),
    MemLp.coeFn_toLp (memLp_weightedMultiplierL2 ha η g),
    Lp.coeFn_sub (weightedMultiplierL2 ha η f) (weightedMultiplierL2 ha η g)]
      with ξ hleft hfg hf hg hright
  rw [hright]
  simp only [Pi.sub_apply] at hfg
  simp only [weightedMultiplierL2, Pi.sub_apply]
  rw [hleft, hf, hg, hfg]
  ring_nf

/-- The weighted multiplier varies continuously in its frequency-shift parameter on `L²`.
Pointwise continuity and the shift bound give dominated convergence for the square of the `L²`
distance. -/
theorem continuous_weightedMultiplierL2 {a : ℝ} (ha : 0 ≤ a)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    Continuous (fun η : Plane => weightedMultiplierL2 ha η f) := by
  apply continuous_iff_continuousAt.mpr
  intro η₀
  let Q : Plane → Plane → ℂ := fun η ξ =>
    ((negSobolevTranslationMultiplier a η ξ : ℂ) -
      (negSobolevTranslationMultiplier a η₀ ξ : ℂ)) * f ξ
  have hQmeas (η : Plane) : AEStronglyMeasurable (Q η) volume := by
    have hm : Continuous (fun ξ : Plane =>
        (negSobolevTranslationMultiplier a η ξ : ℂ) -
          (negSobolevTranslationMultiplier a η₀ ξ : ℂ)) := by
      exact (Complex.continuous_ofReal.comp
          (continuous_negSobolevTranslationMultiplier a η)).sub
        (Complex.continuous_ofReal.comp (continuous_negSobolevTranslationMultiplier a η₀))
    exact hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hQae (η : Plane) :
      (⇑(weightedMultiplierL2 ha η f - weightedMultiplierL2 ha η₀ f)) =ᵐ[volume] Q η := by
    filter_upwards [Lp.coeFn_sub (weightedMultiplierL2 ha η f)
        (weightedMultiplierL2 ha η₀ f),
      MemLp.coeFn_toLp (memLp_weightedMultiplierL2 ha η f),
      MemLp.coeFn_toLp (memLp_weightedMultiplierL2 ha η₀ f)] with ξ hsub hη h₀
    rw [hsub]
    change ((memLp_weightedMultiplierL2 ha η f).toLp _ ξ) -
        ((memLp_weightedMultiplierL2 ha η₀ f).toLp _ ξ) = Q η ξ
    rw [hη, h₀]
    simp only [Q]
    ring
  have hIntSq : Integrable (fun ξ : Plane => ‖f ξ‖ ^ 2) volume := by
    exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  let R : ℝ := ‖η₀‖ + 1
  let M : ℝ := Real.sqrt (2 ^ a * (1 + R ^ 2) ^ a)
  let M₀ : ℝ := Real.sqrt (2 ^ a * (1 + ‖η₀‖ ^ 2) ^ a)
  let C : ℝ := M + M₀
  have hCnonneg : 0 ≤ C := by positivity
  let D : Plane → ℝ≥0∞ := fun ξ => ENNReal.ofReal (C ^ 2 * ‖f ξ‖ ^ 2)
  have hCint : AEStronglyMeasurable (fun ξ : Plane => C ^ 2 * ‖f ξ‖ ^ 2) volume := by
    exact (((Lp.aestronglyMeasurable f).norm.pow 2).const_mul (C ^ 2))
  have hDfin : ∫⁻ ξ, D ξ ∂volume ≠ ∞ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hCint
      (Filter.Eventually.of_forall fun ξ => mul_nonneg (sq_nonneg C) (sq_nonneg ‖f ξ‖))).2
    simpa [D, mul_comm] using hIntSq.const_mul (C ^ 2)
  have hbound : ∀ᶠ η in 𝓝 η₀, ∀ᵐ ξ ∂volume,
      ENNReal.ofReal (‖Q η ξ‖ ^ 2) ≤ D ξ := by
    filter_upwards [Metric.ball_mem_nhds η₀ zero_lt_one] with η hη
    have hηnorm : ‖η‖ ≤ R := by
      have hdist : dist η η₀ < 1 := by simpa [Metric.mem_ball] using hη
      rw [dist_eq_norm] at hdist
      dsimp [R]
      calc
        ‖η‖ = ‖(η - η₀) + η₀‖ := by congr 1; abel
        _ ≤ ‖η - η₀‖ + ‖η₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖η₀‖ := by linarith
        _ = ‖η₀‖ + 1 := by ring
    filter_upwards with ξ
    have hbase : 1 + ‖η‖ ^ 2 ≤ 1 + R ^ 2 := by
      have hnormNonneg : 0 ≤ ‖η‖ := norm_nonneg _
      have hRNonneg : 0 ≤ R := by dsimp [R]; positivity
      have hsq : ‖η‖ ^ 2 ≤ R ^ 2 :=
        (sq_le_sq₀ hnormNonneg hRNonneg).2 hηnorm
      nlinarith [hsq]
    have hweight : (1 + ‖η‖ ^ 2) ^ a ≤ (1 + R ^ 2) ^ a :=
      Real.rpow_le_rpow (by positivity) hbase ha
    have hfactor :
        Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) ≤ M := by
      dsimp [M]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hweight (by positivity))
    have hmη : negSobolevTranslationMultiplier a η ξ ≤ M :=
      (negSobolevTranslationMultiplier_le ha η ξ).trans hfactor
    have hm₀ : negSobolevTranslationMultiplier a η₀ ξ ≤ M₀ := by
      exact negSobolevTranslationMultiplier_le ha η₀ ξ
    have hmη0 : 0 ≤ negSobolevTranslationMultiplier a η ξ := by
      unfold negSobolevTranslationMultiplier negSobolevWeightSqrt
      positivity
    have hm₀0 : 0 ≤ negSobolevTranslationMultiplier a η₀ ξ := by
      unfold negSobolevTranslationMultiplier negSobolevWeightSqrt
      positivity
    have hq : ‖Q η ξ‖ ≤ C * ‖f ξ‖ := by
      dsimp [Q]
      rw [norm_mul]
      have hsub : ‖(negSobolevTranslationMultiplier a η ξ : ℂ) -
          (negSobolevTranslationMultiplier a η₀ ξ : ℂ)‖ ≤
          negSobolevTranslationMultiplier a η ξ + negSobolevTranslationMultiplier a η₀ ξ := by
        calc
          _ ≤ ‖(negSobolevTranslationMultiplier a η ξ : ℂ)‖ +
              ‖(negSobolevTranslationMultiplier a η₀ ξ : ℂ)‖ := norm_sub_le _ _
          _ = _ := by
            rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hmη0, abs_of_nonneg hm₀0]
      dsimp [C]
      calc
        ‖(negSobolevTranslationMultiplier a η ξ : ℂ) -
            (negSobolevTranslationMultiplier a η₀ ξ : ℂ)‖ * ‖f ξ‖ ≤
          (M + M₀) * ‖f ξ‖ := by
            exact mul_le_mul_of_nonneg_right
              (hsub.trans (add_le_add hmη hm₀)) (norm_nonneg _)
        _ = (M + M₀) * ‖f ξ‖ := rfl
    have hq2 : ‖Q η ξ‖ ^ 2 ≤ C ^ 2 * ‖f ξ‖ ^ 2 := by
      nlinarith [hq, norm_nonneg (Q η ξ), norm_nonneg (f ξ), sq_nonneg C]
    exact ENNReal.ofReal_le_ofReal hq2
  have hlim : ∀ᵐ ξ ∂volume, Tendsto (fun η : Plane =>
      ENNReal.ofReal (‖Q η ξ‖ ^ 2)) (𝓝 η₀) (𝓝 0) := by
    filter_upwards with ξ
    have hη : Tendsto (fun η : Plane => negSobolevTranslationMultiplier a η ξ)
        (𝓝 η₀) (𝓝 (negSobolevTranslationMultiplier a η₀ ξ)) :=
      (continuous_negSobolevTranslationMultiplier_left a ξ).continuousAt.tendsto
    have hq : Tendsto (fun η : Plane => Q η ξ) (𝓝 η₀) (𝓝 0) := by
      dsimp [Q]
      have hc : Tendsto (fun η : Plane =>
          ((negSobolevTranslationMultiplier a η ξ : ℝ) : ℂ))
          (𝓝 η₀) (𝓝 ((negSobolevTranslationMultiplier a η₀ ξ : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hη
      have hsub := hc.sub_const ((negSobolevTranslationMultiplier a η₀ ξ : ℝ) : ℂ)
      simpa using hsub.mul_const (f ξ)
    have hn' : Tendsto (fun η : Plane => ‖Q η ξ‖)
        (𝓝 η₀) (𝓝 ‖(0 : ℂ)‖) := by
      change Tendsto ((fun z : ℂ => ‖z‖) ∘ fun η : Plane => Q η ξ) _ _
      exact continuous_norm.continuousAt.tendsto.comp hq
    have hn : Tendsto (fun η : Plane => ‖Q η ξ‖) (𝓝 η₀) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using hn'
    have hsq' : Tendsto (fun η : Plane => ‖Q η ξ‖ ^ 2)
        (𝓝 η₀) (𝓝 ((0 : ℝ) ^ 2)) := by
      change Tendsto ((fun x : ℝ => x ^ 2) ∘ fun η : Plane => ‖Q η ξ‖) _ _
      exact (continuous_id.pow 2).continuousAt.tendsto.comp hn
    have hsq : Tendsto (fun η : Plane => ‖Q η ξ‖ ^ 2) (𝓝 η₀) (𝓝 (0 : ℝ)) := by
      simpa using hsq'
    have hof' : Tendsto (fun η : Plane => ENNReal.ofReal (‖Q η ξ‖ ^ 2))
        (𝓝 η₀) (𝓝 (ENNReal.ofReal 0)) := by
      change Tendsto (ENNReal.ofReal ∘ fun η : Plane => ‖Q η ξ‖ ^ 2) _ _
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsq
    simpa only [ENNReal.ofReal_zero] using hof'
  have hInt : Tendsto (fun η : Plane =>
      ∫⁻ ξ, ENNReal.ofReal (‖Q η ξ‖ ^ 2) ∂volume) (𝓝 η₀) (𝓝 0) := by
    simpa only [lintegral_zero, Pi.zero_apply] using
      tendsto_lintegral_filter_of_dominated_convergence'
      (μ := volume) (F := fun η ξ => ENNReal.ofReal (‖Q η ξ‖ ^ 2)) (f := 0) D
      (Filter.Eventually.of_forall fun η =>
        (hQmeas η).norm.pow 2 |>.aemeasurable.ennreal_ofReal)
      hbound hDfin hlim
  have hIntEnorm : Tendsto (fun η : Plane =>
      ∫⁻ ξ, ‖Q η ξ‖ₑ ^ 2 ∂volume) (𝓝 η₀) (𝓝 0) := by
    apply hInt.congr'
    filter_upwards with η
    apply lintegral_congr
    intro ξ
    exact ofReal_norm_sq_eq_enorm_sq (Q η ξ)
  have hIntEnormRpow : Tendsto (fun η : Plane =>
      ∫⁻ ξ, ‖Q η ξ‖ₑ ^ (2 : ℝ) ∂volume) (𝓝 η₀) (𝓝 0) := by
    apply hIntEnorm.congr'
    filter_upwards with η
    apply lintegral_congr
    intro ξ
    exact (ENNReal.rpow_natCast (‖Q η ξ‖ₑ) 2).symm
  have hpow : Tendsto (fun η : Plane =>
      (∫⁻ ξ, ‖Q η ξ‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ))
      (𝓝 η₀) (𝓝 0) := by
    have hroot : Continuous (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ)) :=
      ENNReal.continuous_rpow_const (y := 1 / 2)
    change Tendsto ((fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ)) ∘
      fun η : Plane => ∫⁻ ξ, ‖Q η ξ‖ₑ ^ (2 : ℝ) ∂volume) _ _
    simpa using hroot.continuousAt.tendsto.comp hIntEnormRpow
  have hnorm : Tendsto (fun η : Plane =>
      eLpNorm (Q η) 2 volume) (𝓝 η₀) (𝓝 0) := by
    have hformula (η : Plane) : eLpNorm (Q η) 2 volume =
        (∫⁻ ξ, ‖Q η ξ‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (hQmeas η)]
      norm_num only [ENNReal.toReal_ofNat, one_div]
    simpa only [hformula] using hpow
  have hnorm' : Tendsto (fun η : Plane =>
      eLpNorm (⇑(weightedMultiplierL2 ha η f - weightedMultiplierL2 ha η₀ f))
        2 volume) (𝓝 η₀) (𝓝 0) := by
    apply hnorm.congr'
    filter_upwards with η
    exact eLpNorm_congr_ae (hQae η).symm
  have hLp : Tendsto (fun η : Plane =>
      weightedMultiplierL2 ha η f - weightedMultiplierL2 ha η₀ f)
      (𝓝 η₀) (𝓝 (0 : Lp ℂ 2 volume)) := by
    have hnorm'' : Tendsto (fun η : Plane => eLpNorm
        (⇑(weightedMultiplierL2 ha η f - weightedMultiplierL2 ha η₀ f) -
          (fun _ : Plane => (0 : ℂ))) 2 volume) (𝓝 η₀) (𝓝 0) := by
      apply hnorm'.congr'
      filter_upwards with η
      apply eLpNorm_congr_ae
      filter_upwards with ξ
      simp
    have hzero : (MemLp.zero : MemLp (fun _ : Plane => (0 : ℂ)) 2 volume).toLp
        (fun _ : Plane => (0 : ℂ)) = (0 : Lp ℂ 2 volume) := by
      exact MemLp.toLp_zero _
    rw [← hzero]
    exact Lp.tendsto_Lp_of_tendsto_eLpNorm
        (f := fun η : Plane => weightedMultiplierL2 ha η f -
          weightedMultiplierL2 ha η₀ f)
        (f_lim := fun _ : Plane => (0 : ℂ))
        (f_lim_ℒp := MemLp.zero) hnorm''
  change Tendsto (fun η : Plane => weightedMultiplierL2 ha η f)
    (𝓝 η₀) (𝓝 (weightedMultiplierL2 ha η₀ f))
  simpa only [sub_add_cancel, zero_add] using
    hLp.add_const (weightedMultiplierL2 ha η₀ f)

/-- The weighted frequency-translation operator on `L²`, obtained by conjugating translation by
the square root of the Sobolev weight. -/
noncomputable def weightedTranslateL2 {a : ℝ} (ha : 0 ≤ a) (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) : Lp ℂ 2 (volume : Measure Plane) :=
  weightedMultiplierL2 ha η (translateL2 η f)

/-- The represented function of a weighted frequency translation is square-integrable. -/
theorem memLp_weightedTranslateL2 {a : ℝ} (ha : 0 ≤ a) (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    MemLp (fun ξ => (negSobolevTranslationMultiplier a η ξ : ℂ) * translateL2 η f ξ)
      2 (volume : Measure Plane) :=
  memLp_weightedMultiplierL2 ha η (translateL2 η f)

/-- A weighted frequency translation has operator norm at most its polynomial shift factor. -/
theorem norm_weightedTranslateL2_le {a : ℝ} (ha : 0 ≤ a) (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    ‖weightedTranslateL2 ha η f‖ ≤
      Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) * ‖f‖ := by
  calc
    ‖weightedTranslateL2 ha η f‖ ≤
        Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) * ‖translateL2 η f‖ :=
      norm_weightedMultiplierL2_le ha η (translateL2 η f)
    _ = Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) * ‖f‖ := by
      rw [translateL2, Lp.norm_compMeasurePreserving]

/-- For positive order, the weighted frequency translations are continuous as `L²` classes.
The proof combines shift continuity with fixed-input continuity of the multiplier. -/
theorem continuous_weightedTranslateL2 {a : ℝ} (ha : 0 ≤ a)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    Continuous (fun η : Plane => weightedTranslateL2 ha η f) := by
  apply continuous_iff_continuousAt.mpr
  intro η₀
  let g : Lp ℂ 2 (volume : Measure Plane) := translateL2 η₀ f
  let d : Plane → Lp ℂ 2 (volume : Measure Plane) :=
    fun η => translateL2 η f - g
  have hd : Tendsto d (𝓝 η₀)
      (𝓝 (0 : Lp ℂ 2 (volume : Measure Plane))) := by
    have htranslate : Tendsto (fun η : Plane => translateL2 η f)
        (𝓝 η₀) (𝓝 (translateL2 η₀ f)) :=
      (continuous_translateL2 f).continuousAt.tendsto
    have hdiff := htranslate.sub_const (translateL2 η₀ f)
    simpa [d, g] using hdiff
  have hnormD : Tendsto (fun η => ‖d η‖) (𝓝 η₀) (𝓝 (0 : ℝ)) := by
    have hnormD' : Tendsto (fun η => ‖d η‖)
        (𝓝 η₀) (𝓝 ‖(0 : Lp ℂ 2 (volume : Measure Plane))‖) := by
      change Tendsto ((fun x : Lp ℂ 2 (volume : Measure Plane) => ‖x‖) ∘ d) _ _
      exact continuous_norm.continuousAt.tendsto.comp hd
    simpa only [norm_zero] using hnormD'
  have hweight : Continuous (fun η : Plane =>
      Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) := by
    have hb : Continuous (fun η : Plane => (1 : ℝ) + ‖η‖ ^ 2) := by fun_prop
    have hp : Continuous (fun η : Plane => (1 + ‖η‖ ^ 2) ^ a) :=
      hb.rpow_const fun η => Or.inl (by positivity)
    exact Real.continuous_sqrt.comp (continuous_const.mul hp)
  have hprod : Tendsto (fun η : Plane =>
      Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) * ‖d η‖)
      (𝓝 η₀) (𝓝 0) := by
    have hK : Tendsto (fun η : Plane =>
        Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) (𝓝 η₀)
        (𝓝 (Real.sqrt (2 ^ a * (1 + ‖η₀‖ ^ 2) ^ a))) :=
      (hweight.continuousAt (x := η₀)).tendsto
    have hKprod := hK.mul hnormD
    simpa using hKprod
  have huNorm : Tendsto (fun η : Plane =>
      ‖weightedMultiplierL2 ha η (d η)‖) (𝓝 η₀) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod ?_ ?_
    · filter_upwards with η
      exact norm_nonneg _
    · filter_upwards with η
      exact norm_weightedMultiplierL2_le ha η (d η)
  have hu : Tendsto (fun η : Plane => weightedMultiplierL2 ha η (d η))
      (𝓝 η₀) (𝓝 (0 : Lp ℂ 2 (volume : Measure Plane))) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr huNorm
  have hv : Tendsto (fun η : Plane =>
      weightedMultiplierL2 ha η g - weightedMultiplierL2 ha η₀ g)
      (𝓝 η₀) (𝓝 (0 : Lp ℂ 2 (volume : Measure Plane))) := by
    have hmult : Tendsto (fun η : Plane => weightedMultiplierL2 ha η g)
        (𝓝 η₀) (𝓝 (weightedMultiplierL2 ha η₀ g)) :=
      ((continuous_weightedMultiplierL2 ha g).continuousAt (x := η₀)).tendsto
    have hdiff := hmult.sub_const (weightedMultiplierL2 ha η₀ g)
    simpa using hdiff
  have hdecomp (η : Plane) :
      weightedTranslateL2 ha η f - weightedTranslateL2 ha η₀ f =
        weightedMultiplierL2 ha η (d η) +
          (weightedMultiplierL2 ha η g - weightedMultiplierL2 ha η₀ g) := by
    rw [weightedTranslateL2, weightedTranslateL2, weightedMultiplierL2_sub]
    dsimp [d, g]
    abel
  have hdiff : Tendsto (fun η : Plane =>
      weightedTranslateL2 ha η f - weightedTranslateL2 ha η₀ f)
      (𝓝 η₀) (𝓝 (0 : Lp ℂ 2 (volume : Measure Plane))) := by
    have hsum : Tendsto (fun η : Plane =>
        weightedMultiplierL2 ha η (d η) +
          (weightedMultiplierL2 ha η g - weightedMultiplierL2 ha η₀ g))
        (𝓝 η₀) (𝓝 (0 : Lp ℂ 2 (volume : Measure Plane))) := by
      simpa only [zero_add] using hu.add hv
    exact hsum.congr' <| Filter.Eventually.of_forall fun η =>
      (hdecomp η).symm
  change Tendsto (fun η : Plane => weightedTranslateL2 ha η f)
    (𝓝 η₀) (𝓝 (weightedTranslateL2 ha η₀ f))
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add_const (weightedTranslateL2 ha η₀ f)

/-- At order zero the weighted translation is exactly the usual measure-preserving translation. -/
theorem weightedTranslateL2_zero_eq_translateL2 (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    weightedTranslateL2 (a := 0) (by norm_num) η f = translateL2 η f := by
  simp only [weightedTranslateL2, weightedMultiplierL2]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
    (memLp_weightedTranslateL2 (a := 0) (by norm_num) η f)] with ξ hξ
  have hm : negSobolevTranslationMultiplier 0 η ξ = 1 := by
    simp [negSobolevTranslationMultiplier, negSobolevWeightSqrt]
  rw [hξ, hm]
  simp

/-- Continuity of the order-zero weighted translations follows from continuity of ordinary L²
translations. -/
theorem continuous_weightedTranslateL2_zero (f : Lp ℂ 2 (volume : Measure Plane)) :
    Continuous (fun η : Plane => weightedTranslateL2 (a := 0) (by norm_num) η f) := by
  have heq : (fun η : Plane => weightedTranslateL2 (a := 0) (by norm_num) η f) =
      fun η => translateL2 η f := by
    funext η
    exact weightedTranslateL2_zero_eq_translateL2 η f
  rw [heq]
  exact continuous_translateL2 f

/-- The weighted `L²` convolution bound for a finitely supported frequency kernel. Its operator
norm is controlled by the kernel's discrete weighted `L¹` norm. -/
theorem norm_weightedTranslationSum_le {a : ℝ} (ha : 0 ≤ a) {ι : Type*} [Fintype ι]
    (η : ι → Plane) (c : ι → ℂ) (f : Lp ℂ 2 (volume : Measure Plane)) :
    ‖∑ i, c i • weightedTranslateL2 ha (η i) f‖ ≤
      (∑ i, ‖c i‖ * Real.sqrt (2 ^ a * (1 + ‖η i‖ ^ 2) ^ a)) * ‖f‖ := by
  calc
    ‖∑ i, c i • weightedTranslateL2 ha (η i) f‖ ≤
        ∑ i, ‖c i • weightedTranslateL2 ha (η i) f‖ := norm_sum_le Finset.univ _
    _ = ∑ i, ‖c i‖ * ‖weightedTranslateL2 ha (η i) f‖ := by
      simp only [norm_smul]
    _ ≤ ∑ i, ‖c i‖ *
        (Real.sqrt (2 ^ a * (1 + ‖η i‖ ^ 2) ^ a) * ‖f‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (norm_weightedTranslateL2_le ha (η i) f)
        (norm_nonneg _)
    _ = (∑ i, ‖c i‖ * Real.sqrt (2 ^ a * (1 + ‖η i‖ ^ 2) ^ a)) * ‖f‖ := by
      calc
        ∑ i, ‖c i‖ *
            (Real.sqrt (2 ^ a * (1 + ‖η i‖ ^ 2) ^ a) * ‖f‖) =
            ∑ i, (‖c i‖ * Real.sqrt (2 ^ a * (1 + ‖η i‖ ^ 2) ^ a)) * ‖f‖ := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (∑ i, ‖c i‖ * Real.sqrt (2 ^ a * (1 + ‖η i‖ ^ 2) ^ a)) * ‖f‖ := by
          rw [Finset.sum_mul]

/-- The weighted Young bound for a Bochner integral of frequency translations. The hypotheses
state exactly the two analytic conditions needed to form the integral: strong measurability of the
translated family and integrability of the kernel with its polynomial shift loss. -/
theorem norm_integral_weightedTranslateL2_le {a : ℝ} (ha : 0 ≤ a)
    (k : Plane → ℂ) (f : Lp ℂ 2 (volume : Measure Plane))
    (hF : AEStronglyMeasurable
      (fun η : Plane => k η • weightedTranslateL2 ha η f) (volume : Measure Plane))
    (hk : Integrable (fun η : Plane =>
      ‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a))) :
    Integrable (fun η : Plane => k η • weightedTranslateL2 ha η f) ∧
      ‖∫ η : Plane, k η • weightedTranslateL2 ha η f‖ ≤
        (∫ η : Plane, ‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖ := by
  let F : Plane → Lp ℂ 2 (volume : Measure Plane) :=
    fun η => k η • weightedTranslateL2 ha η f
  have hF' : AEStronglyMeasurable F (volume : Measure Plane) := hF
  have hnorm : Integrable (fun η : Plane => ‖F η‖) := by
    have hmajor : Integrable (fun η : Plane =>
        (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖) :=
      hk.mul_const ‖f‖
    refine hmajor.mono' hF'.norm ?_
    filter_upwards with η
    change ‖‖k η • weightedTranslateL2 ha η f‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_smul]
    calc
      ‖k η‖ * ‖weightedTranslateL2 ha η f‖ ≤
          ‖k η‖ * (Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (norm_weightedTranslateL2_le ha η f) (norm_nonneg _)
      _ = (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖ := by ring
  have hFint : Integrable F := (integrable_norm_iff hF').mp hnorm
  refine ⟨hFint, ?_⟩
  have hbound (η : Plane) : ‖F η‖ ≤
      (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖ := by
    change ‖k η • weightedTranslateL2 ha η f‖ ≤ _
    rw [norm_smul]
    calc
      ‖k η‖ * ‖weightedTranslateL2 ha η f‖ ≤
          ‖k η‖ * (Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (norm_weightedTranslateL2_le ha η f) (norm_nonneg _)
      _ = (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖ := by ring
  have hmajor : Integrable (fun η : Plane =>
      (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖) :=
    hk.mul_const ‖f‖
  calc
    ‖∫ η : Plane, F η‖ ≤ ∫ η : Plane, ‖F η‖ := norm_integral_le_integral_norm F
    _ ≤ ∫ η : Plane,
        (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖ :=
      integral_mono hnorm hmajor hbound
    _ = (∫ η : Plane,
        ‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖ := integral_mul_const _ _

/-- The weighted Young bound when the Bochner parameter is sent to a varying frequency shift. -/
theorem norm_integral_weightedTranslateL2_map_le {a : ℝ} (ha : 0 ≤ a)
    (κ : Plane → Plane) (k : Plane → ℂ) (f : Lp ℂ 2 (volume : Measure Plane))
    (hF : AEStronglyMeasurable
      (fun η : Plane => k η • weightedTranslateL2 ha (κ η) f) (volume : Measure Plane))
    (hk : Integrable (fun η : Plane => ‖k η‖ *
      Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a))) :
    Integrable (fun η : Plane => k η • weightedTranslateL2 ha (κ η) f) ∧
      ‖∫ η : Plane, k η • weightedTranslateL2 ha (κ η) f‖ ≤
        (∫ η : Plane, ‖k η‖ *
          Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖ := by
  let F : Plane → Lp ℂ 2 (volume : Measure Plane) :=
    fun η => k η • weightedTranslateL2 ha (κ η) f
  have hF' : AEStronglyMeasurable F (volume : Measure Plane) := hF
  have hnorm : Integrable (fun η : Plane => ‖F η‖) := by
    have hmajor : Integrable (fun η : Plane =>
        (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖) :=
      hk.mul_const ‖f‖
    refine hmajor.mono' hF'.norm ?_
    filter_upwards with η
    change ‖‖k η • weightedTranslateL2 ha (κ η) f‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_smul]
    calc
      ‖k η‖ * ‖weightedTranslateL2 ha (κ η) f‖ ≤
          ‖k η‖ * (Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (norm_weightedTranslateL2_le ha (κ η) f)
          (norm_nonneg _)
      _ = (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖ := by ring
  have hFint : Integrable F := (integrable_norm_iff hF').mp hnorm
  refine ⟨hFint, ?_⟩
  have hbound (η : Plane) : ‖F η‖ ≤
      (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖ := by
    change ‖k η • weightedTranslateL2 ha (κ η) f‖ ≤ _
    rw [norm_smul]
    calc
      ‖k η‖ * ‖weightedTranslateL2 ha (κ η) f‖ ≤
          ‖k η‖ * (Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (norm_weightedTranslateL2_le ha (κ η) f)
          (norm_nonneg _)
      _ = (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖ := by ring
  have hmajor : Integrable (fun η : Plane =>
      (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖) :=
    hk.mul_const ‖f‖
  calc
    ‖∫ η : Plane, F η‖ ≤ ∫ η : Plane, ‖F η‖ := norm_integral_le_integral_norm F
    _ ≤ ∫ η : Plane,
        (‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖ :=
      integral_mono hnorm hmajor hbound
    _ = (∫ η : Plane,
        ‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) * ‖f‖ := integral_mul_const _ _

/-- The weighted convolution bound applies to the Fourier transform of every test
function. Continuity of weighted translations supplies Bochner measurability; Schwartz decay
supplies the polynomially weighted kernel integrability. -/
theorem norm_integral_fourier_weightedTranslateL2_le {a : ℝ} (ha : 0 ≤ a)
    (χ : TestFn) (f : Lp ℂ 2 (volume : Measure Plane)) :
    Integrable (fun η : Plane => (𝓕 (testFnSchwartz χ)) η • weightedTranslateL2 ha η f) ∧
      ‖∫ η : Plane, (𝓕 (testFnSchwartz χ)) η • weightedTranslateL2 ha η f‖ ≤
        (∫ η : Plane, ‖(𝓕 (testFnSchwartz χ)) η‖ *
          Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) * ‖f‖ := by
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  have hF : AEStronglyMeasurable
      (fun η : Plane => k η • weightedTranslateL2 ha η f) volume := by
    have hcont : Continuous
        (fun η : Plane => k η • weightedTranslateL2 ha η f) := by
      exact (𝓕 (testFnSchwartz χ)).continuous.smul
        (continuous_weightedTranslateL2 ha f)
    exact hcont.aestronglyMeasurable
  have hk0 := integrable_sqrt_negSobolevWeight_mul_norm_fourier_testFn ha χ
  have hk : Integrable (fun η : Plane =>
      ‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) := by
    have heq : (fun η : Plane =>
        ‖k η‖ * Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a)) =
        fun η : Plane => Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) *
          ‖(𝓕 (testFnSchwartz χ)) η‖ := by
      funext η
      dsimp [k]
      ring
    rw [heq]
    exact hk0
  simpa only [k] using norm_integral_weightedTranslateL2_le ha k f hF hk

/-- The Fourier-side weighted convolution estimate with the frequency scaling that matches the
angular modulation `cos ⟪ξ,x⟫` and Mathlib's Fourier inversion phase `2π⟪η,x⟫`. -/
theorem norm_integral_scaledFourier_weightedTranslateL2_le {a : ℝ} (ha : 0 ≤ a)
    (χ : TestFn) (f : Lp ℂ 2 (volume : Measure Plane)) :
    Integrable (fun η : Plane => (𝓕 (testFnSchwartz χ)) η •
      weightedTranslateL2 ha ((2 * Real.pi) • η) f) ∧
      ‖∫ η : Plane, (𝓕 (testFnSchwartz χ)) η •
          weightedTranslateL2 ha ((2 * Real.pi) • η) f‖ ≤
        (∫ η : Plane, ‖(𝓕 (testFnSchwartz χ)) η‖ *
          Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) * ‖f‖ := by
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  let κ : Plane → Plane := fun η => (2 * Real.pi) • η
  have hF : AEStronglyMeasurable
      (fun η : Plane => k η • weightedTranslateL2 ha (κ η) f) volume := by
    have hκ : Continuous κ := by fun_prop
    have hcont : Continuous
        (fun η : Plane => k η • weightedTranslateL2 ha (κ η) f) := by
      exact (𝓕 (testFnSchwartz χ)).continuous.smul
        ((continuous_weightedTranslateL2 ha f).comp hκ)
    exact hcont.aestronglyMeasurable
  have hk0 := integrable_scaled_sqrt_negSobolevWeight_mul_norm_fourier_testFn ha χ
  have hk : Integrable (fun η : Plane => ‖k η‖ *
      Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) := by
    have heq : (fun η : Plane => ‖k η‖ *
        Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)) =
        fun η : Plane => Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a) *
          ‖(𝓕 (testFnSchwartz χ)) η‖ := by
      funext η
      dsimp [k, κ]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_comm]
    rw [heq]
    exact hk0
  have hbound := norm_integral_weightedTranslateL2_map_le ha κ k f hF hk
  simpa [k, κ, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_comm] using hbound


/-- The L² convolution operator defined as a Bochner integral of translated L² classes. -/
noncomputable def l2ConvolutionAction (k : Plane → ℂ)
    (f : Lp ℂ 2 (volume : Measure Plane)) : Lp ℂ 2 (volume : Measure Plane) :=
  ∫ η : Plane, k η • translateL2 η f

/-- The Bochner-valued convolution operator has norm bounded by the L¹ kernel norm. -/
theorem norm_l2ConvolutionAction_le {k : Plane → ℂ} (hk : Integrable k)
    (hkc : Continuous k) (f : Lp ℂ 2 (volume : Measure Plane)) :
    Integrable (fun η : Plane => k η • translateL2 η f) ∧
      ‖l2ConvolutionAction k f‖ ≤ (∫ η : Plane, ‖k η‖) * ‖f‖ := by
  let F : Plane → Lp ℂ 2 (volume : Measure Plane) :=
    fun η => k η • translateL2 η f
  have hFcont : Continuous F := by
    exact hkc.smul (continuous_translateL2 f)
  have hFnorm : ∀ η, ‖F η‖ = ‖k η‖ * ‖f‖ := by
    intro η
    calc
      ‖F η‖ = ‖k η‖ * ‖translateL2 η f‖ := by
        simp only [F, norm_smul]
      _ = ‖k η‖ * ‖f‖ := by
        rw [translateL2, Lp.norm_compMeasurePreserving]
  have hnorm : Integrable (fun η : Plane => ‖F η‖) := by
    have heq : (fun η : Plane => ‖F η‖) = fun η => ‖k η‖ * ‖f‖ := by
      funext η
      exact hFnorm η
    rw [heq]
    exact hk.norm.mul_const ‖f‖
  have hFint : Integrable F :=
    (integrable_norm_iff hFcont.aestronglyMeasurable).mp hnorm
  refine ⟨hFint, ?_⟩
  calc
    ‖l2ConvolutionAction k f‖ = ‖∫ η : Plane, F η‖ := by rfl
    _ ≤ ∫ η : Plane, ‖F η‖ := norm_integral_le_integral_norm F
    _ = (∫ η : Plane, ‖k η‖) * ‖f‖ := by
      rw [show (fun η : Plane => ‖F η‖) = fun η => ‖k η‖ * ‖f‖ from by
        funext η
        exact hFnorm η,
        integral_mul_const]

end Critical2DKPZ.Analysis.Sobolev

end
