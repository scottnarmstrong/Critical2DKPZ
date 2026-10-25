/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-! # Convergence in law under an asymptotically accurate approximation -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.JointConvergence

/-- A bounded Lipschitz test changes its integral by at most its Lipschitz constant times the
mean distance between the inputs. -/
theorem integral_lipschitz_comp_sub_le {Ω : Type*} {k : ℕ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → Fin k → ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {F : (Fin k → ℝ) → ℝ} {K : NNReal} (hF : LipschitzWith K F)
    (hFbd : ∃ M : ℝ, ∀ x y, dist (F x) (F y) ≤ M) {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∫⁻ ω, ENNReal.ofReal ‖X ω - Y ω‖ ∂μ ≤ ENNReal.ofReal η) :
    |(∫ ω, F (X ω) ∂μ) - (∫ ω, F (Y ω) ∂μ)| ≤ (K : ℝ) * η := by
  have hdiffSM : AEStronglyMeasurable (fun ω => X ω - Y ω) μ :=
    hX.aestronglyMeasurable.sub hY.aestronglyMeasurable
  have hdiffFin : HasFiniteIntegral (fun ω => X ω - Y ω) μ := by
    rw [hasFiniteIntegral_iff_enorm]
    have hle : ∫⁻ ω, ‖X ω - Y ω‖ₑ ∂μ ≤ ENNReal.ofReal η := by
      simpa only [ofReal_norm] using hbound
    exact hle.trans_lt ENNReal.ofReal_lt_top
  have hdiffInt : Integrable (fun ω => X ω - Y ω) μ := ⟨hdiffSM, hdiffFin⟩
  have hnormInt : Integrable (fun ω => ‖X ω - Y ω‖) μ := hdiffInt.norm
  have hnormBound : ∫ ω, ‖X ω - Y ω‖ ∂μ ≤ η := by
    have hnormIntegral := integral_norm_eq_lintegral_enorm hdiffSM
    have hle : ∫⁻ ω, ‖X ω - Y ω‖ₑ ∂μ ≤ ENNReal.ofReal η := by
      simpa only [ofReal_norm] using hbound
    rw [hnormIntegral]
    calc
      (∫⁻ ω, ‖X ω - Y ω‖ₑ ∂μ).toReal ≤ (ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = η := ENNReal.toReal_ofReal hη
  obtain ⟨M, hM⟩ := hFbd
  have hFbound (x : Fin k → ℝ) : ‖F x‖ ≤ ‖F 0‖ + M := by
    have hdist := hM x (0 : Fin k → ℝ)
    rw [Real.dist_eq] at hdist
    have hnorm : ‖F x - F 0‖ ≤ M := by simpa only [Real.norm_eq_abs] using hdist
    calc
      ‖F x‖ ≤ ‖F 0‖ + ‖F x - F 0‖ := by
        simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (F 0) (F x)
      _ ≤ ‖F 0‖ + M := add_le_add (le_refl _) hnorm
  have hFX : Integrable (fun ω => F (X ω)) μ :=
    Integrable.of_bound
      ((hF.continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable) (‖F 0‖ + M)
      (Eventually.of_forall fun ω => hFbound (X ω))
  have hFY : Integrable (fun ω => F (Y ω)) μ :=
    Integrable.of_bound
      ((hF.continuous.measurable.comp_aemeasurable hY).aestronglyMeasurable) (‖F 0‖ + M)
      (Eventually.of_forall fun ω => hFbound (Y ω))
  have hFdiffInt : Integrable (fun ω => F (X ω) - F (Y ω)) μ := hFX.sub hFY
  have hmajorInt : Integrable (fun ω => (K : ℝ) * ‖X ω - Y ω‖) μ :=
    hnormInt.const_mul (K : ℝ)
  rw [← integral_sub hFX hFY, ← Real.norm_eq_abs]
  calc
    ‖∫ ω, (F (X ω) - F (Y ω)) ∂μ‖ ≤ ∫ ω, ‖F (X ω) - F (Y ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (K : ℝ) * ‖X ω - Y ω‖ ∂μ := by
      apply integral_mono hFdiffInt.norm hmajorInt
      intro ω
      simpa only [Real.norm_eq_abs] using hF.norm_sub_le (X ω) (Y ω)
    _ = (K : ℝ) * ∫ ω, ‖X ω - Y ω‖ ∂μ := integral_const_mul _ _
    _ ≤ (K : ℝ) * η := mul_le_mul_of_nonneg_left hnormBound (by exact_mod_cast K.coe_nonneg)

/-- Approximation in `L¹` and convergence in law imply convergence in law as in Billingsley's Theorem 3.2. -/
theorem tendstoInDistribution_of_approx {k : ℕ} {Ω' Ω : Type*} [MeasurableSpace Ω']
    [MeasurableSpace Ω] {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    (X : ℕ → Ω' → Fin k → ℝ) (Y : ℕ → ℕ → Ω' → Fin k → ℝ)
    (Yl : ℕ → Ω → Fin k → ℝ) (L : Ω → Fin k → ℝ)
    (hY : ∀ j, TendstoInDistribution (fun N => Y j N) atTop (Yl j) μ P)
    (hYl : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖Yl j ω - L ω‖ ∂P ≤ ENNReal.ofReal ε)
    (hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᶠ N in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖X N ω - Y j N ω‖ ∂(μ N) ≤ ENNReal.ofReal ε)
    (hXm : ∀ N, AEMeasurable (X N) (μ N)) (hLm : AEMeasurable L P) :
    TendstoInDistribution X atTop L μ P := by
  refine ⟨hXm, hLm, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto (Ω := Fin k → ℝ)).2 ?_
  intro F hFbounded hFlipschitz
  obtain ⟨K, hF⟩ := hFlipschitz
  obtain ⟨M, hFbounded'⟩ := hFbounded
  have htest : Tendsto (fun N => ∫ ω, F (X N ω) ∂(μ N)) atTop
      (𝓝 (∫ ω, F (L ω) ∂P)) := by
    rw [Metric.tendsto_nhds]
    intro e he
    let η : ℝ := e / (6 * ((K : ℝ) + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨j, hj⟩ := ((hYl η hη).and (hXY η hη)).exists
    have hYtest : Tendsto (fun N => ∫ ω, F (Y j N ω) ∂(μ N)) atTop
        (𝓝 (∫ ω, F (Yl j ω) ∂P)) := by
      have hmap :=
        (tendsto_iff_forall_lipschitz_integral_tendsto.mp (hY j).tendsto)
          F ⟨M, hFbounded'⟩ ⟨K, hF⟩
      have hmapN (N : ℕ) :
          (∫ z, F z ∂(μ N).map (Y j N)) = ∫ ω, F (Y j N ω) ∂(μ N) :=
        integral_map ((hY j).forall_aemeasurable N)
          (hF.continuous.measurable.aestronglyMeasurable)
      have hmapLim :
          (∫ z, F z ∂P.map (Yl j)) = ∫ ω, F (Yl j ω) ∂P :=
        integral_map (hY j).aemeasurable_limit
          (hF.continuous.measurable.aestronglyMeasurable)
      simpa only [ProbabilityMeasure.coe_mk, hmapN, hmapLim] using hmap
    have hfirst : ∀ᶠ N in atTop,
        |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (Y j N ω) ∂(μ N))| ≤ (K : ℝ) * η := by
      filter_upwards [hj.2] with N hN
      exact integral_lipschitz_comp_sub_le (μ N) (hXm N) ((hY j).forall_aemeasurable N) hF
        ⟨M, hFbounded'⟩
        hη.le hN
    have hlast : |(∫ ω, F (Yl j ω) ∂P) - (∫ ω, F (L ω) ∂P)| ≤ (K : ℝ) * η :=
      integral_lipschitz_comp_sub_le P (hY j).aemeasurable_limit hLm hF
        ⟨M, hFbounded'⟩ hη.le hj.1
    have hmiddle : ∀ᶠ N in atTop,
        |(∫ ω, F (Y j N ω) ∂(μ N)) - (∫ ω, F (Yl j ω) ∂P)| < e / 3 := by
      simpa only [Real.dist_eq] using
        (Metric.tendsto_nhds.mp hYtest (e / 3) (by linarith : 0 < e / 3))
    have hsum : 2 * ((K : ℝ) * η) + e / 3 < e := by
      dsimp [η]
      have hKnonneg : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
      field_simp
      linarith
    filter_upwards [hfirst, hmiddle] with N hfirstN hmiddleN
    calc
      |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (L ω) ∂P)| ≤
          |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (Y j N ω) ∂(μ N))| +
            |(∫ ω, F (Y j N ω) ∂(μ N)) - (∫ ω, F (Yl j ω) ∂P)| +
              |(∫ ω, F (Yl j ω) ∂P) - (∫ ω, F (L ω) ∂P)| := by
        calc
          _ ≤ |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (Yl j ω) ∂P)| +
              |(∫ ω, F (Yl j ω) ∂P) - (∫ ω, F (L ω) ∂P)| := abs_sub_le _ _ _
          _ ≤ _ := by gcongr; exact abs_sub_le _ _ _
      _ ≤ 2 * ((K : ℝ) * η) + e / 3 := by linarith [hfirstN, hmiddleN, hlast]
      _ < e := hsum
  have hmapX (N : ℕ) :
      (∫ z, F z ∂(μ N).map (X N)) = ∫ ω, F (X N ω) ∂(μ N) :=
    integral_map (hXm N) (hF.continuous.measurable.aestronglyMeasurable)
  have hmapLim : (∫ z, F z ∂P.map L) = ∫ ω, F (L ω) ∂P :=
    integral_map hLm (hF.continuous.measurable.aestronglyMeasurable)
  simpa only [ProbabilityMeasure.coe_mk, hmapX, hmapLim] using htest

end Critical2DKPZ.JointConvergence

end
