/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.KPZRegularizedReversal
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
public import Critical2DKPZ.Definitions.IsCriticalSHF
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Time reversal in law for regularized KPZ fields -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.JointConvergence

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

private theorem measurable_log_heatPairing (δ : ℝ) (hδ : 0 < δ) (g : Plane → ℝ)
    (hg : Measurable g) (hgn : ∀ y, 0 ≤ g y) :
    Measurable (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ p.1 * g p.2 ∂μ)) := by
  let f : Plane × Plane → ℝ≥0∞ := fun p => ENNReal.ofReal (heatKernel δ p.1 * g p.2)
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_heatKernel δ).comp measurable_fst |>.mul (hg.comp measurable_snd))
  have hlin : Measurable (fun μ : Measure (Plane × Plane) => ∫⁻ p, f p ∂μ) :=
    Measure.measurable_lintegral hf
  have heq : (fun μ : Measure (Plane × Plane) => ∫ p, heatKernel δ p.1 * g p.2 ∂μ) =
      fun μ => (∫⁻ p, f p ∂μ).toReal := by
    funext μ
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (heatKernel_nonneg hδ.le _) (hgn p.2)
    · exact ((measurable_heatKernel δ).comp measurable_fst |>.mul
        (hg.comp measurable_snd)).aestronglyMeasurable
  have hEqFun : (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ p.1 * g p.2 ∂μ)) =
      fun μ => Real.log ((∫⁻ p, f p ∂μ).toReal) := by
    funext μ
    exact congrArg Real.log (congrFun heq μ)
  rw [hEqFun]
  exact Real.measurable_log.comp hlin.ennreal_toReal

set_option linter.style.haveILetI false in
private theorem isLocallyFinite_of_closedBall_mass (μ : Measure (Plane × Plane))
    (hμ : ∀ n : ℕ, μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) < ∞) :
    IsLocallyFiniteMeasure μ := by
  have hfc : IsFiniteMeasureOnCompacts μ := by
    refine ⟨?_⟩
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Plane × Plane)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    calc
      μ K ≤ μ (Metric.closedBall (0 : Plane × Plane) r) := measure_mono hr
      _ ≤ μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) :=
        measure_mono (Metric.closedBall_subset_closedBall (le_of_lt hn))
      _ < ∞ := hμ n
  letI : IsFiniteMeasureOnCompacts μ := hfc
  infer_instance

set_option linter.style.haveILetI false in
/-- A joint reversal law for the heat flow gives the corresponding joint law for tested regularized KPZ fields. -/
theorem kpzRegularized_reverse_law_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (T : ℝ) (hrev : ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      P.map (fun ω i => (Z (T - t i) (T - s i) ω).map Prod.swap) = P.map (fun ω i => Z (s i) (t i) ω))
    (k : ℕ) (t δ : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn)
    (ht : ∀ i, 0 < δ i ∧ δ i < t i ∧ t i ≤ T) :
    P.map (fun ω i => ∫ x, φ i x * kpzRegularized P Z (t i) (δ i) (h₀ i) x ω) =
      P.map (fun ω i => ∫ x, φ i x * kpzRegularizedReversed P Z (T - t i) T (δ i) (h₀ i) x ω) := by
  classical
  let s : Fin k → ℝ := fun i => T - t i + δ i
  let W : Ω → Fin k → Measure (Plane × Plane) := fun ω i => Z (s i) T ω
  let R : Ω → Fin k → Measure (Plane × Plane) := fun ω i => (Z 0 (t i - δ i) ω).map Prod.swap
  have hsvalid : ∀ i, 0 ≤ s i ∧ s i < T ∧ T ≤ T := by
    intro i
    have hi := ht i
    constructor
    · dsimp [s]
      linarith
    constructor
    · dsimp [s]
      linarith
    · exact le_rfl
  have hWmeas : Measurable W := by
    apply measurable_pi_iff.mpr
    intro i
    exact hZ.1 (s i) T (hsvalid i).1 (hsvalid i).2.1
  have hRmeas : Measurable R := by
    apply measurable_pi_iff.mpr
    intro i
    have hi := ht i
    have hti : 0 < t i - δ i := by linarith
    exact (Measure.measurable_map Prod.swap measurable_swap).comp
      (hZ.1 0 (t i - δ i) le_rfl hti)
  have hRfun : (fun ω i => (Z (T - T) (T - s i) ω).map Prod.swap) = R := by
    funext ω i
    dsimp [R, s]
    congr 2 <;> ring
  have hWfun : (fun ω i => Z (s i) T ω) = W := rfl
  have hlaw : P.map R = P.map W := by
    have h := hrev k s (fun _ => T) hsvalid
    rw [hRfun, hWfun] at h
    exact h
  let K : ℕ → Set (Plane × Plane) := fun n => Metric.closedBall 0 (n : ℝ)
  have hKmeas : ∀ n, MeasurableSet (K n) := fun n =>
    Metric.isClosed_closedBall.measurableSet
  let S : Set (Fin k → Measure (Plane × Plane)) :=
    {m | ∀ i n, m i (K n) < ∞}
  have hSmeas : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun n =>
      measurableSet_lt
        ((Measure.measurable_coe (hKmeas n)).comp (measurable_pi_apply i)) measurable_const
  have hsourceFinite : ∀ᵐ ω ∂P, ∀ i n, W ω i (K n) < ∞ := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    have hi := ht i
    have hlocal := (hZ.2.1 (s i) T (hsvalid i).1 (hsvalid i).2.1).mono
      (fun ω hh => hh.1)
    filter_upwards [hlocal] with ω hω
    letI : IsLocallyFiniteMeasure (W ω i) := hω
    exact (isCompact_closedBall (0 : Plane × Plane) (n : ℝ)).measure_lt_top
  have hmassLaw : ∀ᵐ m ∂P.map W, m ∈ S := by
    exact (ae_map_iff hWmeas.aemeasurable hSmeas).2 hsourceFinite
  have hlocalLaw (i : Fin k) :
      ∀ᵐ m ∂P.map W, IsLocallyFiniteMeasure (m i) := by
    filter_upwards [hmassLaw] with m hm
    apply isLocallyFinite_of_closedBall_mass
    intro n
    exact hm i n
  let C : Fin k → ℝ := fun i => ∫ ω, Real.log
    (shfPairing Z (s i) T (fun y => heatKernel (δ i) y) (fun _ => 1) ω) ∂P
  let G : (Fin k → Measure (Plane × Plane)) → Fin k → ℝ := fun m i =>
    ∫ x, φ i x *
      (Real.log (∫ p, heatKernel (δ i) (p.1 - x) * Real.exp (h₀ i p.2) ∂m i) - C i)
      ∂volume
  have hGcoord (i : Fin k) : AEMeasurable (fun m => G m i) (P.map W) := by
    have hδi : 0 < δ i := (ht i).1
    have hg : Measurable (fun y : Plane => Real.exp (h₀ i y)) :=
      Real.continuous_exp.comp (h₀ i).continuous |>.measurable
    have hφ : Measurable (φ i : Plane → ℝ) := (φ i).continuous.measurable
    exact aemeasurable_integral_log_heatPairing (P.map W) (fun m => m i)
      (measurable_pi_apply i) (hlocalLaw i) (δ i) (C i) hδi (fun y => Real.exp (h₀ i y))
      (φ i) hg (fun y => (Real.exp_pos (h₀ i y)).le) hφ
  have hG : AEMeasurable G (P.map W) := by
    apply aemeasurable_pi_iff.mpr
    exact hGcoord
  let Q : Fin k → Measure (Plane × Plane) → ℝ := fun i m =>
    Real.log (∫ p, heatKernel (δ i) p.1 * (fun _ : Plane => (1 : ℝ)) p.2 ∂m)
  have hQ (i : Fin k) : Measurable (Q i) := by
    apply measurable_log_heatPairing (δ i) (ht i).1 (fun _ => 1)
    · exact measurable_const
    · intro y
      norm_num
  let H (i : Fin k) : (Fin k → Measure (Plane × Plane)) → ℝ := fun m => Q i (m i)
  have hH (i : Fin k) : Measurable (H i) :=
    (hQ i).comp (measurable_pi_apply i)
  have hcenterLaw (i : Fin k) :
      P.map (fun ω => H i (R ω)) = P.map (fun ω => H i (W ω)) := by
    calc
      P.map (fun ω => H i (R ω)) = (P.map R).map (H i) :=
        (AEMeasurable.map_map_of_aemeasurable (hH i).aemeasurable hRmeas.aemeasurable).symm
      _ = (P.map W).map (H i) := by rw [hlaw]
      _ = P.map (fun ω => H i (W ω)) :=
        AEMeasurable.map_map_of_aemeasurable (hH i).aemeasurable hWmeas.aemeasurable
  have hcenterEq (i : Fin k) :
      (∫ ω, Q i (R ω i) ∂P) = ∫ ω, Q i (W ω i) ∂P := by
    apply integral_eq_of_map_eq P
      ((hH i).comp_aemeasurable hRmeas.aemeasurable)
      ((hH i).comp_aemeasurable hWmeas.aemeasurable)
    simpa only [H, Function.comp_def] using hcenterLaw i
  have hcenterR (i : Fin k) (ω : Ω) : Q i (R ω i) =
      Real.log (shfPairing Z 0 (t i - δ i) (fun _ => 1)
        (fun y => heatKernel (δ i) y) ω) := by
    have hrevPair := shfPairing_reverse Z T 0 (t i - δ i) (fun _ => 1)
      (fun y => heatKernel (δ i) y) ω
    have hraw : (∫ p, heatKernel (δ i) p.1 * (fun _ : Plane => (1 : ℝ)) p.2
        ∂(Z 0 (t i - δ i) ω).map Prod.swap) =
        shfPairing (fun s t ω => (Z (T - t) (T - s) ω).map Prod.swap)
          (T - (t i - δ i)) T (fun y => heatKernel (δ i) y) (fun _ => 1) ω := by
      simp [shfPairing, sub_sub_cancel]
    have hrevPair' :
        shfPairing Z 0 (t i - δ i) (fun _ => 1) (fun y => heatKernel (δ i) y) ω =
          shfPairing (fun s t ω => (Z (T - t) (T - s) ω).map Prod.swap)
            (T - (t i - δ i)) T (fun y => heatKernel (δ i) y) (fun _ => 1) ω := by
      simpa only [sub_zero] using hrevPair
    have hpair :
        shfPairing Z 0 (t i - δ i) (fun _ => 1) (fun y => heatKernel (δ i) y) ω =
          ∫ p, heatKernel (δ i) p.1 * (fun _ : Plane => (1 : ℝ)) p.2
            ∂(Z 0 (t i - δ i) ω).map Prod.swap := by
      calc
        _ = shfPairing (fun s t ω => (Z (T - t) (T - s) ω).map Prod.swap)
            (T - (t i - δ i)) T (fun y => heatKernel (δ i) y) (fun _ => 1) ω := hrevPair'
        _ = _ := hraw.symm
    change Real.log (∫ p, heatKernel (δ i) p.1 * (fun _ : Plane => (1 : ℝ)) p.2
        ∂(Z 0 (t i - δ i) ω).map Prod.swap) = _
    exact congrArg Real.log hpair.symm
  have hCeq (i : Fin k) : C i =
      ∫ ω, Real.log (shfPairing Z 0 (t i - δ i) (fun _ => 1)
        (fun y => heatKernel (δ i) y) ω) ∂P := by
    calc
      C i = ∫ ω, Q i (W ω i) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rfl
      _ = ∫ ω, Q i (R ω i) ∂P := (hcenterEq i).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hcenterR i ω
  have hpoint (i : Fin k) (x : Plane) (ω : Ω) :
      kpzRegularized P Z (t i) (δ i) (h₀ i) x ω =
        Real.log (∫ p, heatKernel (δ i) (p.1 - x) * Real.exp (h₀ i p.2)
          ∂R ω i) - C i := by
    let Zrev : ℝ → ℝ → Ω → Measure (Plane × Plane) :=
      fun a b ω => (Z (T - b) (T - a) ω).map Prod.swap
    have hpt := kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure P Z T
      (t i) (δ i) (h₀ i) x ω
    have hcenterPoint (ω' : Ω) :
        Real.log (shfPairing Zrev (T - t i + δ i) T
          (fun y => heatKernel (δ i) y) (fun _ => 1) ω') = Q i (R ω' i) := by
      have hpair := shfPairing_reverse Z T 0 (t i - δ i) (fun _ => 1)
        (fun y => heatKernel (δ i) y) ω'
      have hpair' :
          shfPairing Zrev (T - t i + δ i) T (fun y => heatKernel (δ i) y)
            (fun _ => 1) ω' =
          shfPairing Z 0 (t i - δ i) (fun _ => 1)
            (fun y => heatKernel (δ i) y) ω' := by
        simpa only [Zrev, sub_zero,
          show T - (t i - δ i) = T - t i + δ i by ring] using hpair.symm
      calc
        _ = Real.log (shfPairing Z 0 (t i - δ i) (fun _ => 1)
            (fun y => heatKernel (δ i) y) ω') := congrArg Real.log hpair'
        _ = Q i (R ω' i) := (hcenterR i ω').symm
    have hcenter :
        (∫ ω', Real.log (shfPairing Zrev (T - t i + δ i) T
          (fun y => heatKernel (δ i) y) (fun _ => 1) ω') ∂P) = C i := by
      calc
        _ = ∫ ω', Q i (R ω' i) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω'
          exact hcenterPoint ω'
        _ = ∫ ω', Q i (W ω' i) ∂P := hcenterEq i
        _ = C i := by
          symm
          apply integral_congr_ae
          filter_upwards [] with ω'
          rfl
    rw [hpt]
    unfold kpzRegularizedReversed
    rw [hcenter]
    unfold shfPairing
    dsimp only [sub_self]
    rw [show T - (T - t i + δ i) = t i - δ i by ring]
    dsimp [R]
    rw [sub_self]
  have hleftFun : (fun ω i => ∫ x, φ i x *
      kpzRegularized P Z (t i) (δ i) (h₀ i) x ω ∂volume) = fun ω => G (R ω) := by
    funext ω i
    dsimp [G]
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg (fun r : ℝ => φ i x * r) (hpoint i x ω)
  have hrightFun : (fun ω i => ∫ x, φ i x *
      kpzRegularizedReversed P Z (T - t i) T (δ i) (h₀ i) x ω ∂volume) = fun ω => G (W ω) := by
    funext ω i
    dsimp [G, W, C, s]
    rfl
  have hGlaw : P.map (fun ω => G (R ω)) = P.map (fun ω => G (W ω)) := by
    have hG_R : AEMeasurable G (P.map R) := by rw [hlaw]; exact hG
    calc
      P.map (fun ω => G (R ω)) = (P.map R).map G :=
        (AEMeasurable.map_map_of_aemeasurable hG_R hRmeas.aemeasurable).symm
      _ = (P.map W).map G := by rw [hlaw]
      _ = P.map (fun ω => G (W ω)) :=
        AEMeasurable.map_map_of_aemeasurable hG hWmeas.aemeasurable
  rw [hleftFun, hrightFun, hGlaw]

end Critical2DKPZ.JointConvergence

end
