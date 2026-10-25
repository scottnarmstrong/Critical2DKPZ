/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
import Critical2DKPZ.JointConvergence.KPZRegularizedReversal
import Critical2DKPZ.SHF.Symmetries.LatticeReversal
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-! # Reversal laws for the KPZ fields -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal

universe u

namespace Critical2DKPZ.LocalSobolev

open Critical2DKPZ.SHF.Limit

private theorem integral_eq_of_map_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hlaw : P.map X = P.map Y) : (∫ ω, X ω ∂P) = ∫ ω, Y ω ∂P := by
  let hidX : AEStronglyMeasurable (fun x : ℝ => x) (P.map X) :=
    measurable_id.aestronglyMeasurable
  let hidY : AEStronglyMeasurable (fun x : ℝ => x) (P.map Y) :=
    measurable_id.aestronglyMeasurable
  by_cases hIX : Integrable X P
  · have hIpushX : Integrable (fun x : ℝ => x) (P.map X) := by
      have h := (integrable_map_measure hidX hX).2 hIX
      simpa only [Function.comp_def] using h
    have hIpushY : Integrable (fun x : ℝ => x) (P.map Y) := by
      rw [← hlaw]
      exact hIpushX
    have hIY : Integrable Y P := by
      have h := (integrable_map_measure hidY hY).1 hIpushY
      simpa only [Function.comp_def] using h
    have hmapX := integral_map hX hidX
    have hmapY := integral_map hY hidY
    calc
      (∫ ω, X ω ∂P) = ∫ x, x ∂P.map X := hmapX.symm
      _ = ∫ x, x ∂P.map Y := by rw [hlaw]
      _ = ∫ ω, Y ω ∂P := hmapY
  · have hIpushX : ¬ Integrable (fun x : ℝ => x) (P.map X) := by
      intro h
      apply hIX
      have h' := (integrable_map_measure hidX hX).1 h
      simpa only [Function.comp_def] using h'
    have hIpushY : ¬ Integrable (fun x : ℝ => x) (P.map Y) := by
      intro h
      apply hIpushX
      rw [← hlaw] at h
      exact h
    have hIY : ¬ Integrable Y P := by
      intro h
      apply hIpushY
      have h' := (integrable_map_measure hidY hY).2 h
      simpa only [Function.comp_def] using h'
    rw [integral_undef hIX, integral_undef hIY]

private theorem measurable_log_heatPairing (δ : ℝ) (hδ : 0 < δ) (x : Plane)
    (g : Plane → ℝ) (hg : Measurable g) (hgn : ∀ y, 0 ≤ g y) :
    Measurable (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ)) := by
  let f : Plane × Plane → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (heatKernel δ (p.1 - x) * g p.2)
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_heatKernel δ).comp (measurable_fst.sub_const x) |>.mul
        (hg.comp measurable_snd))
  have hlin : Measurable (fun μ : Measure (Plane × Plane) => ∫⁻ p, f p ∂μ) :=
    Measure.measurable_lintegral hf
  have heq : (fun μ : Measure (Plane × Plane) =>
      ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) =
        fun μ => (∫⁻ p, f p ∂μ).toReal := by
    funext μ
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (heatKernel_nonneg hδ.le _) (hgn p.2)
    · exact ((measurable_heatKernel δ).comp
        (measurable_fst.sub_const x) |>.mul (hg.comp measurable_snd)).aestronglyMeasurable
  have hlog : (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ)) =
        fun μ => Real.log ((∫⁻ p, f p ∂μ).toReal) := by
    funext μ
    exact congrArg Real.log (congrFun heq μ)
  rw [hlog]
  exact Real.measurable_log.comp hlin.ennreal_toReal

/-- Time-reversal symmetry of the stochastic heat flow identifies the laws of finite vectors of reversed interval measures. -/
theorem shfReversal_measureLaw_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (T : ℝ) :
    ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      P.map (fun ω i => (Z (T - t i) (T - s i) ω).map Prod.swap) =
        P.map (fun ω i => Z (s i) (t i) ω) := by
  intro k s t hst
  exact Critical2DKPZ.SHF.Symmetries.isCriticalSHF_reverse_fdd
    ϑ P Z hZ T k s t hst

/-- At finitely many points, the forward regularized field has the law of its time-reversed form. -/
theorem kpzRegularized_reverse_pointLaw_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (T : ℝ) (k : ℕ) (t δ : Fin k → ℝ)
    (h₀ : Fin k → (Plane →ᵇ ℝ)) (x : Fin k → Plane)
    (ht : ∀ i, 0 < δ i ∧ δ i < t i ∧ t i ≤ T) :
    P.map (fun ω i => kpzRegularized P Z (t i) (δ i) (h₀ i) (x i) ω) =
      P.map (fun ω i => kpzRegularizedReversed P Z (T - t i) T (δ i) (h₀ i) (x i) ω) := by
  classical
  have _hsym : ShfSymmetriesAt ϑ P Z := hsym
  let s : Fin k → ℝ := fun i => T - t i + δ i
  let Zrev : ℝ → ℝ → Ω → Measure (Plane × Plane) :=
    fun a b ω => (Z (T - b) (T - a) ω).map Prod.swap
  let W : Ω → Fin k → Measure (Plane × Plane) := fun ω i => Zrev (s i) T ω
  let V : Ω → Fin k → Measure (Plane × Plane) := fun ω i => Z (s i) T ω
  have hs : ∀ i, 0 ≤ s i ∧ s i < T ∧ T ≤ T := by
    intro i
    rcases ht i with ⟨hδ, hδt, htT⟩
    constructor
    · dsimp [s]
      linarith
    constructor
    · dsimp [s]
      linarith
    · exact le_rfl
  have hmeasureLaw : P.map W = P.map V := by
    have h := shfReversal_measureLaw_of ϑ P Z hZ T k s (fun _ => T) hs
    simpa only [W, V, Zrev, s, sub_self,
      show ∀ i : Fin k, T - (T - t i + δ i) = t i - δ i by
        intro i
        ring] using h
  have hW : Measurable W := by
    apply measurable_pi_iff.mpr
    intro i
    have htd : 0 < t i - δ i := by
      rcases ht i with ⟨hδ, hδt, _⟩
      linarith
    have hsT : T - s i = t i - δ i := by
      dsimp [s]
      ring
    dsimp [W, Zrev]
    simpa only [sub_self, hsT, Function.comp_def] using
      (Measure.measurable_map Prod.swap measurable_swap).comp
        (hZ.1 0 (t i - δ i) le_rfl htd)
  have hV : Measurable V := by
    apply measurable_pi_iff.mpr
    intro i
    exact hZ.1 (s i) T (hs i).1 (hs i).2.1
  let C : (Fin k → Measure (Plane × Plane)) → Fin k → ℝ := fun m i =>
    Real.log (∫ p, heatKernel (δ i) p.1 * (1 : ℝ) ∂m i)
  have hC : Measurable C := by
    apply measurable_pi_iff.mpr
    intro i
    simpa only [C, sub_zero, Function.comp_def] using
      (measurable_log_heatPairing (δ i) (ht i).1 (0 : Plane) (fun _ => 1)
        measurable_const (fun _ => by norm_num)).comp (measurable_pi_apply i)
  have hCcoord (i : Fin k) : Measurable (fun m => C m i) :=
    (measurable_pi_apply i).comp hC
  have hClaw : P.map (fun ω => C (W ω)) = P.map (fun ω => C (V ω)) := by
    calc
      P.map (fun ω => C (W ω)) = (P.map W).map C :=
        (AEMeasurable.map_map_of_aemeasurable hC.aemeasurable hW.aemeasurable).symm
      _ = (P.map V).map C := congrArg (fun μ : Measure (Fin k → Measure (Plane × Plane)) => μ.map C)
        hmeasureLaw
      _ = P.map (fun ω => C (V ω)) :=
        AEMeasurable.map_map_of_aemeasurable hC.aemeasurable hV.aemeasurable
  have hCeq (i : Fin k) :
      (∫ ω, C (W ω) i ∂P) = ∫ ω, C (V ω) i ∂P := by
    have hproj : Measurable (fun z : Fin k → ℝ => z i) := measurable_pi_apply i
    have hlaw : P.map (fun ω => C (W ω) i) = P.map (fun ω => C (V ω) i) := by
      calc
        P.map (fun ω => C (W ω) i) = (P.map (fun ω => C (W ω))).map (fun z => z i) :=
          (AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable
            (hC.comp hW).aemeasurable).symm
        _ = (P.map (fun ω => C (V ω))).map (fun z => z i) :=
          congrArg (fun μ : Measure (Fin k → ℝ) => μ.map (fun z => z i)) hClaw
        _ = P.map (fun ω => C (V ω) i) :=
          AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable
            (hC.comp hV).aemeasurable
    exact integral_eq_of_map_eq P ((hCcoord i).comp hW).aemeasurable
      ((hCcoord i).comp hV).aemeasurable hlaw
  let cW : Fin k → ℝ := fun i => ∫ ω, C (W ω) i ∂P
  let cV : Fin k → ℝ := fun i => ∫ ω, C (V ω) i ∂P
  have hc : cW = cV := by
    funext i
    exact hCeq i
  let F : (Fin k → Measure (Plane × Plane)) → Fin k → ℝ := fun m i =>
    Real.log (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ i p.2) ∂m i) - cW i
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    have hg : Measurable (fun y : Plane => Real.exp (h₀ i y)) :=
      Real.continuous_exp.measurable.comp (h₀ i).continuous.measurable
    have hgn (y : Plane) : 0 ≤ Real.exp (h₀ i y) := (Real.exp_pos _).le
    exact ((measurable_log_heatPairing (δ i) (ht i).1 (x i)
      (fun y => Real.exp (h₀ i y)) hg hgn).comp (measurable_pi_apply i)).sub_const (cW i)
  have hFlaw : P.map (fun ω => F (W ω)) = P.map (fun ω => F (V ω)) := by
    calc
      P.map (fun ω => F (W ω)) = (P.map W).map F :=
        (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hW.aemeasurable).symm
      _ = (P.map V).map F := congrArg (fun μ : Measure (Fin k → Measure (Plane × Plane)) => μ.map F)
        hmeasureLaw
      _ = P.map (fun ω => F (V ω)) :=
        AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hV.aemeasurable
  have hleft : (fun ω i => kpzRegularized P Z (t i) (δ i) (h₀ i) (x i) ω) =
      fun ω i => F (W ω) i := by
    funext ω i
    calc
      kpzRegularized P Z (t i) (δ i) (h₀ i) (x i) ω =
          kpzRegularizedReversed P Zrev (T - t i) T (δ i) (h₀ i) (x i) ω := by
            simpa only [Zrev] using
              Critical2DKPZ.JointConvergence.kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure
                P Z T (t i) (δ i) (h₀ i) (x i) ω
      _ = F (W ω) i := by
        simp [F, W, cW, C, Zrev, s, kpzRegularizedReversed, shfPairing]
  have hright : (fun ω i => kpzRegularizedReversed P Z (T - t i) T (δ i) (h₀ i) (x i) ω) =
      fun ω i => F (V ω) i := by
    funext ω i
    simp [F, V, cW, cV, C, s, kpzRegularizedReversed, shfPairing, hc]
  rw [hleft, hright]
  exact hFlaw

end Critical2DKPZ.LocalSobolev

end
