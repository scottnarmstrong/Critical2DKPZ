/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.Basic
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.SmallScales.HeatStartMoments
public import Critical2DKPZ.SHF.Symmetries.DenseTransport
import Critical2DKPZ.EhrhardType.Moments
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-! # Pointwise second moments for regularized KPZ fields -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The map `μ ↦ log ∫ heatKernel δ (p.1 - x) dμ` on measures of the plane pair is measurable. -/
theorem measurable_log_heatPairingMeasure (δ : ℝ) (hδ : 0 < δ) (x : Plane) :
    Measurable (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ (p.1 - x) ∂μ)) := by
  let F : Plane × Plane → ℝ≥0∞ := fun p => ENNReal.ofReal (heatKernel δ (p.1 - x))
  have hF : Measurable F := by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_heatKernel δ).comp (measurable_fst.sub_const x)
  have hlin : Measurable (fun μ : Measure (Plane × Plane) => ∫⁻ p, F p ∂μ) :=
    Measure.measurable_lintegral hF
  have hpair (μ : Measure (Plane × Plane)) :
      (∫ p, heatKernel δ (p.1 - x) ∂μ) = (∫⁻ p, F p ∂μ).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p => heatKernel_nonneg hδ.le _
    · exact ((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).aestronglyMeasurable
  have hEq : (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ (p.1 - x) ∂μ)) =
      fun μ => Real.log ((∫⁻ p, F p ∂μ).toReal) := by
    funext μ
    exact congrArg Real.log (hpair μ)
  rw [hEq]
  exact Real.measurable_log.comp hlin.ennreal_toReal

/-- The logarithmic heat-start pairing after swapping the two coordinates of the SHF measure. -/
def swappedHeatStartLog {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (x : Plane) (ω : Ω) : ℝ :=
  Real.log (∫ p, heatKernel δ (p.1 - x) ∂((Z 0 (t - δ) ω).map Prod.swap))

/-- The flat regularized field is the swapped heat-start log, centered by its value's mean at zero. -/
theorem kpzRegularized_eq_swappedHeatStartLog_sub_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {t δ : ℝ} (x : Plane) :
    kpzRegularized P Z t δ 0 x = fun ω => swappedHeatStartLog Z t δ x ω -
      ∫ ω', swappedHeatStartLog Z t δ 0 ω' ∂P := by
  let T : ℝ := t - δ
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  have hnum (ω : Ω) :
      shfPairing Z 0 T (fun _ => (1 : ℝ)) (fun y => heatKernel δ (y - x)) ω =
        ∫ p, heatKernel δ (p.1 - x) ∂S ω := by
    have hmap := integral_map (μ := M ω) measurable_swap.aemeasurable
      ((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).aestronglyMeasurable
    simpa [shfPairing, S, M, one_mul] using hmap.symm
  have hcenter :
      (∫ ω', Real.log (shfPairing Z 0 T (fun _ => (1 : ℝ))
        (fun y => heatKernel δ y) ω') ∂P) =
        ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    have hmap := integral_map (μ := M ω) measurable_swap.aemeasurable
      ((measurable_heatKernel δ).comp measurable_fst).aestronglyMeasurable
    simpa [swappedHeatStartLog, S, M, T, shfPairing, one_mul] using congrArg Real.log hmap.symm
  funext ω
  unfold kpzRegularized
  have hexp0 : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) = fun _ => (1 : ℝ) := by
    funext y
    simp
  rw [hexp0, hnum ω, hcenter]
  rfl

/-- Two measurable maps whose one-coordinate vector laws agree have the same law. -/
theorem map_singleton_eq_of_map_pi_eq {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] (P : Measure Ω) (F G : Ω → α)
    (hF : Measurable F) (hG : Measurable G)
    (hLaw : P.map (fun ω (_ : Fin 1) => F ω) = P.map (fun ω (_ : Fin 1) => G ω)) :
    P.map F = P.map G := by
  let F₁ : Ω → Fin 1 → α := fun ω _ => F ω
  let G₁ : Ω → Fin 1 → α := fun ω _ => G ω
  have hF₁ : Measurable F₁ := by
    apply measurable_pi_iff.mpr
    intro i
    exact hF
  have hG₁ : Measurable G₁ := by
    apply measurable_pi_iff.mpr
    intro i
    exact hG
  have hEval : Measurable (fun f : Fin 1 → α => f 0) := measurable_pi_apply 0
  have hmapF := AEMeasurable.map_map_of_aemeasurable (μ := P)
    hEval.aemeasurable hF₁.aemeasurable
  have hmapG := AEMeasurable.map_map_of_aemeasurable (μ := P)
    hEval.aemeasurable hG₁.aemeasurable
  calc
    P.map F = (P.map F₁).map (fun f => f 0) := by
      calc
        P.map F = P.map (fun ω => F₁ ω 0) := by rfl
        _ = (P.map F₁).map (fun f => f 0) := hmapF.symm
    _ = (P.map G₁).map (fun f => f 0) := by rw [hLaw]
    _ = P.map G := by
      calc
        (P.map G₁).map (fun f => f 0) = P.map (fun ω => G₁ ω 0) := hmapG
        _ = P.map G := by rfl

/-- At any positive interval, the time-reversal bridge gives invariance in law of the SHF
measure under swapping its two endpoints. -/
theorem shfInterval_map_swap_law_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z) {T : ℝ} (hT : 0 < T) :
    P.map (fun ω => (Z 0 T ω).map Prod.swap) = P.map (fun ω => Z 0 T ω) := by
  let F : Ω → Measure (Plane × Plane) := fun ω => (Z 0 T ω).map Prod.swap
  let G : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  have hF : Measurable F := by
    exact (Measure.measurable_map Prod.swap measurable_swap).comp
      (hZ.1 _ _ le_rfl hT)
  have hG : Measurable G := by
    exact hZ.1 _ _ le_rfl hT
  have hLaw := hrevL T 1 (fun _ => 0) (fun _ => T) (by
    intro i
    constructor
    · norm_num
    constructor
    · exact hT
    · exact le_rfl)
  apply map_singleton_eq_of_map_pi_eq P F G hF hG
  simpa [F, G] using hLaw

/-- Spatial translation invariance of an SHF gives the same translation-invariant law for each
individual interval measure. -/
theorem shfInterval_translate_law_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z) (z : Plane)
    {T : ℝ} (hT : 0 < T) :
    P.map (fun ω => Z 0 T ω) =
      P.map (fun ω => (Z 0 T ω).map (fun p => (p.1 + z, p.2 + z))) := by
  let τ : Plane × Plane → Plane × Plane := fun p => (p.1 + z, p.2 + z)
  let Zτ : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s t ω => (Z s t ω).map τ
  let F : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let G : Ω → Measure (Plane × Plane) := fun ω => (Z 0 T ω).map τ
  have hZτ : IsCriticalSHF ϑ P Zτ := by
    simpa [Zτ, τ] using hsym.1 z
  have hlaw := SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P Z Zτ hZ hZτ 1
    (fun _ => 0) (fun _ => T) (by
      intro i
      constructor
      · norm_num
      · exact hT)
  have hF : Measurable F := hZ.1 0 T le_rfl hT
  have hG : Measurable G := by
    exact (Measure.measurable_map τ (by fun_prop)).comp hF
  apply map_singleton_eq_of_map_pi_eq P F G hF hG
  simpa [F, G, Zτ, τ] using hlaw

/-- The logarithm of a heat-start pairing is square-integrable when its law is Ehrhard type.
The heat-start mean-one identity supplies the positive exponential moment. -/
theorem log_heatStartPairing_memLp_two_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    {s T δ : ℝ} (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) (x : Plane) :
    MemLp (fun ω => Real.log (shfPairing Z s T
      (fun y => heatKernel δ (y - x)) (fun _ => (1 : ℝ)) ω)) 2 P := by
  let L : Ω → ℝ := fun ω => Real.log (shfPairing Z s T
    (fun y => heatKernel δ (y - x)) (fun _ => (1 : ℝ)) ω)
  let Y : Ω → ℝ := fun ω => shfPairing Z s T
    (fun y => heatKernel δ (y - x)) (fun _ => (1 : ℝ)) ω
  have hpackage := hsym.2.2.2.2.2.2 s T δ x (0 : Plane →ᵇ ℝ) hs hsT hδ
  have hpos : ∀ᵐ ω ∂P, 0 < Y ω := by
    filter_upwards [hpackage.1] with ω hω
    simpa [Y] using hω
  have hmeasL : AEMeasurable L P := by
    simpa [L] using hpackage.2.1
  have hEhrhard : IsEhrhardType (P.map L) := by
    have hL : L =ᵐ[P] fun ω => Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x))
        (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω) := by
      filter_upwards [] with ω
      simp [L]
    rw [Measure.map_congr hL]
    exact hpackage.2.2
  obtain ⟨hYint, hYmean⟩ := SmallScales.heatStart_integral_eq_one
    ϑ P Z hZ hs hsT hδ x
  have hExpL : (fun ω => Real.exp (L ω)) =ᵐ[P] Y := by
    filter_upwards [hpos] with ω hω
    exact Real.exp_log hω
  have hExpInt : Integrable (fun ω => Real.exp (L ω)) P := hYint.congr hExpL.symm
  have hExpLaw : Integrable (fun r : ℝ => Real.exp r) (P.map L) :=
    (integrable_map_measure (by fun_prop) hmeasL).2 hExpInt
  have hSqLaw : Integrable (fun r : ℝ => r ^ 2) (P.map L) :=
    EhrhardType.integrable_sq_of_isEhrhardType hEhrhard hExpLaw
  have hSq : Integrable (fun ω => L ω ^ 2) P :=
    (integrable_map_measure (by fun_prop) hmeasL).mp hSqLaw
  have hLstrong : AEStronglyMeasurable L P := hmeasL.aestronglyMeasurable
  simpa only [L] using (memLp_two_iff_integrable_sq hLstrong).2 hSq

/-- The swapped heat-start log retains its square-integrable Ehrhard moment under the reversal
bridge. -/
theorem swappedHeatStartLog_memLp_two_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (x : Plane) :
    MemLp (swappedHeatStartLog Z t δ x) 2 P := by
  let T : ℝ := t - δ
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  let Q : Measure (Plane × Plane) → ℝ := fun μ =>
    Real.log (∫ p, heatKernel δ (p.1 - x) ∂μ)
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hMmeas : Measurable M := hZ.1 0 T le_rfl hTpos
  have hSmeas : Measurable S := (Measure.measurable_map Prod.swap measurable_swap).comp hMmeas
  have hQmeas : Measurable Q := by
    dsimp [Q]
    exact measurable_log_heatPairingMeasure δ hδ x
  have hswapLaw : P.map S = P.map M := by
    simpa [S, M, T] using shfInterval_map_swap_law_of ϑ P Z hZ hrevL hTpos
  have hQmem : MemLp (fun ω => Q (M ω)) 2 P := by
    have hbase := log_heatStartPairing_memLp_two_of ϑ P Z hZ hsym
      (s := 0) (T := T) le_rfl hTpos hδ x
    simpa [Q, M, T, shfPairing] using hbase
  have hSqMap : Integrable (fun μ : Measure (Plane × Plane) => Q μ ^ 2) (P.map M) :=
    (integrable_map_measure (by fun_prop) hMmeas.aemeasurable).2 hQmem.integrable_sq
  have hSq : Integrable (fun μ : Measure (Plane × Plane) => Q μ ^ 2) (P.map S) := by
    rw [hswapLaw]
    exact hSqMap
  have hSq' := (integrable_map_measure (by fun_prop) hSmeas.aemeasurable).mp hSq
  have hstrong : AEStronglyMeasurable (fun ω => Q (S ω)) P :=
    (hQmeas.comp_aemeasurable hSmeas.aemeasurable).aestronglyMeasurable
  have hmem := (memLp_two_iff_integrable_sq hstrong).2 hSq'
  change MemLp (fun ω => Q (S ω)) 2 P at hmem
  change MemLp (fun ω => Q (S ω)) 2 P
  exact hmem

/-- Every pointwise flat regularized field is square-integrable, including widths larger than half
the available horizon. The reversal bridge transfers the swapped heat-start Ehrhard moment. -/
theorem kpzRegularized_point_memLp_two_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (x : Plane) :
    MemLp (kpzRegularized P Z t δ 0 x) 2 P := by
  let T : ℝ := t - δ
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  let Q : Measure (Plane × Plane) → ℝ := fun μ =>
    Real.log (∫ p, heatKernel δ (p.1 - x) ∂μ)
  let Q₀ : Measure (Plane × Plane) → ℝ := fun μ =>
    Real.log (∫ p, heatKernel δ p.1 ∂μ)
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hMmeas : Measurable M := hZ.1 0 T le_rfl hTpos
  have hSmeas : Measurable S := (Measure.measurable_map Prod.swap measurable_swap).comp hMmeas
  have hQmeas : Measurable Q := by
    dsimp [Q]
    exact measurable_log_heatPairingMeasure δ hδ x
  have hQ₀meas : Measurable Q₀ := by
    dsimp [Q₀]
    simpa [sub_zero] using measurable_log_heatPairingMeasure δ hδ (0 : Plane)
  let W : Ω → Fin 1 → Measure (Plane × Plane) := fun ω _ => M ω
  let R : Ω → Fin 1 → Measure (Plane × Plane) := fun ω _ => S ω
  have hswapLaw : P.map S = P.map M := by
    have hRW := hrevL T 1 (fun _ => 0) (fun _ => T) (by
      intro i
      constructor
      · norm_num
      constructor
      · exact hTpos
      · exact le_rfl)
    have hRmeas : Measurable R := by
      apply measurable_pi_iff.mpr
      intro i
      exact hSmeas
    have hWmeas : Measurable W := by
      apply measurable_pi_iff.mpr
      intro i
      exact hMmeas
    have heval : Measurable (fun m : Fin 1 → Measure (Plane × Plane) => m 0) :=
      measurable_pi_apply 0
    have hmapR := AEMeasurable.map_map_of_aemeasurable (μ := P)
      heval.aemeasurable hRmeas.aemeasurable
    have hmapW := AEMeasurable.map_map_of_aemeasurable (μ := P)
      heval.aemeasurable hWmeas.aemeasurable
    have hRW' : P.map R = P.map W := by
      simpa [R, W, S, M, T] using hRW
    calc
      P.map S = (P.map R).map (fun m => m 0) := by
        calc
          P.map S = P.map (fun ω => R ω 0) := by rfl
          _ = (P.map R).map (fun m => m 0) := hmapR.symm
      _ = (P.map W).map (fun m => m 0) := by rw [hRW']
      _ = P.map M := by
        calc
          (P.map W).map (fun m => m 0) = P.map (fun ω => W ω 0) := hmapW
          _ = P.map M := by rfl
  have hQmem : MemLp (fun ω => Q (M ω)) 2 P := by
    have hbase := log_heatStartPairing_memLp_two_of ϑ P Z hZ hsym
      (s := 0) (T := T) le_rfl hTpos hδ x
    simpa [Q, M, T, shfPairing] using hbase
  have hQ₀mem : MemLp (fun ω => Q₀ (M ω)) 2 P := by
    have hbase := log_heatStartPairing_memLp_two_of ϑ P Z hZ hsym
      (s := 0) (T := T) le_rfl hTpos hδ 0
    simpa [Q₀, M, T, shfPairing, sub_zero] using hbase
  have hQSqMap : Integrable (fun μ : Measure (Plane × Plane) => Q μ ^ 2) (P.map M) :=
    (integrable_map_measure (by fun_prop) hMmeas.aemeasurable).2 hQmem.integrable_sq
  have hQ₀SqMap : Integrable (fun μ : Measure (Plane × Plane) => Q₀ μ ^ 2) (P.map M) :=
    (integrable_map_measure (by fun_prop) hMmeas.aemeasurable).2 hQ₀mem.integrable_sq
  have hQSwap : MemLp (fun ω => Q (S ω)) 2 P := by
    have hsq : Integrable (fun μ : Measure (Plane × Plane) => Q μ ^ 2) (P.map S) := by
      rw [hswapLaw]
      exact hQSqMap
    have hsq' := (integrable_map_measure (by fun_prop) hSmeas.aemeasurable).mp hsq
    have hstrong : AEStronglyMeasurable (fun ω => Q (S ω)) P :=
      (hQmeas.comp_aemeasurable hSmeas.aemeasurable).aestronglyMeasurable
    exact (memLp_two_iff_integrable_sq hstrong).2 hsq'
  have hQ₀Swap : MemLp (fun ω => Q₀ (S ω)) 2 P := by
    have hsq : Integrable (fun μ : Measure (Plane × Plane) => Q₀ μ ^ 2) (P.map S) := by
      rw [hswapLaw]
      exact hQ₀SqMap
    have hsq' := (integrable_map_measure (by fun_prop) hSmeas.aemeasurable).mp hsq
    have hstrong : AEStronglyMeasurable (fun ω => Q₀ (S ω)) P :=
      (hQ₀meas.comp_aemeasurable hSmeas.aemeasurable).aestronglyMeasurable
    exact (memLp_two_iff_integrable_sq hstrong).2 hsq'
  let c : ℝ := ∫ ω, Q₀ (S ω) ∂P
  have hc : Integrable (fun ω => Q₀ (S ω)) P := hQ₀Swap.integrable (by norm_num)
  have hnum (ω : Ω) :
      shfPairing Z 0 T (fun _ => (1 : ℝ)) (fun y => heatKernel δ (y - x)) ω =
        ∫ p, heatKernel δ (p.1 - x) ∂S ω := by
    have hmap := integral_map (μ := M ω) measurable_swap.aemeasurable
      ((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).aestronglyMeasurable
    simpa [shfPairing, S, M, one_mul] using hmap.symm
  have hcenter :
      (∫ ω', Real.log (shfPairing Z 0 T (fun _ => (1 : ℝ))
        (fun y => heatKernel δ y) ω') ∂P) = c := by
    calc
      (∫ ω', Real.log (shfPairing Z 0 T (fun _ => (1 : ℝ))
          (fun y => heatKernel δ y) ω') ∂P) =
          ∫ ω, Q₀ (S ω) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            have hmap := integral_map (μ := M ω) measurable_swap.aemeasurable
              ((measurable_heatKernel δ).comp measurable_fst).aestronglyMeasurable
            simpa [Q₀, S, M, shfPairing, one_mul] using congrArg Real.log hmap.symm
      _ = c := rfl
  have hfield : kpzRegularized P Z t δ 0 x = fun ω => Q (S ω) - c := by
    funext ω
    unfold kpzRegularized
    have hexp0 : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) = fun _ => (1 : ℝ) := by
      funext y
      simp
    rw [hexp0, hnum ω, hcenter]
  rw [hfield]
  exact hQSwap.sub (memLp_const c)

end Critical2DKPZ.CovarianceKernel

end
