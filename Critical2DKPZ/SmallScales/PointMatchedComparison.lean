/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.HeatStartLogCLT
public import Critical2DKPZ.SmallScales.ShrinkingRegularizedReversed
public import Critical2DKPZ.JointConvergence.ThmToyJointLimit
import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
import Mathlib.Tactic

/-! # The point-matched local comparison -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.JointConvergence
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

private theorem integral_abs_le_eLpNorm_two {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (C : ℝ)
    (hbound : eLpNorm f 2 P ≤ ENNReal.ofReal C) :
    Integrable f P ∧ ∫ ω, |f ω| ∂P ≤ max C 0 := by
  have hbound' : eLpNorm f 2 P ≤ ENNReal.ofReal (max C 0) :=
    hbound.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))
  have hfinite : eLpNorm f 2 P < ⊤ := hbound'.trans_lt ENNReal.ofReal_lt_top
  have hsm : AEStronglyMeasurable f P := aestronglyMeasurable_of_eLpNorm_ne_top hfinite.ne
  have hbound1 : eLpNorm f 1 P ≤ ENNReal.ofReal (max C 0) := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans hbound'
  have hfinite1 : eLpNorm f 1 P < ⊤ := hbound1.trans_lt ENNReal.ofReal_lt_top
  have hmem1 : MemLp f 1 P := hfinite1
  have hint : Integrable f P := memLp_one_iff_integrable.mp hmem1
  have habs : ∫ ω, |f ω| ∂P = (eLpNorm f 1 P).toReal := by
    calc
      ∫ ω, |f ω| ∂P = ∫ ω, ‖f ω‖ ∂P := by simp only [Real.norm_eq_abs]
      _ = (∫⁻ ω, ‖f ω‖ₑ ∂P).toReal := integral_norm_eq_lintegral_enorm hsm
      _ = (eLpNorm f 1 P).toReal := by rw [← eLpNorm_one_eq_lintegral_enorm hsm]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound1
  rw [ENNReal.toReal_ofReal (le_max_right C 0)] at hreal
  exact ⟨hint, habs ▸ hreal⟩

private theorem heatStartLog_test_integrable_of (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {σ T : ℝ} (hσ : 0 < σ) (hσT : σ < T) (φ : TestFn) :
    ∀ᵐ ω ∂P, Integrable (fun y => φ y * heatStartLog Z σ T σ y ω) := by
  have hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane)
      (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P := by
    intro s t δ hs hst hδ x g
    exact isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hjoint := isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
  have hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P := by
    intro s t δ x h₀ hs hst hδ
    have h := isCriticalSHF_heat_pairing_pos_isEhrhardType
      ϑ P Z hZ s t δ x h₀ hs hst hδ
    exact ⟨h.1, h.2.1⟩
  let μ : Ω → Measure (Plane × Plane) := Z σ T
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 σ T (le_of_lt hσ) hσT] with ω hω
    exact hω.1
  have hg : Measurable (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) := by fun_prop
  have hF : AEMeasurable (fun q : Plane × Ω => heatStartLog Z σ T σ q.1 q.2)
      (volume.prod P) := by
    have h := aemeasurable_log_heatPairing_joint P μ (hZ.1 σ T (le_of_lt hσ) hσT)
      hlocal σ hσ (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) hg
      (fun y => Real.exp_nonneg _)
    simpa [μ, heatStartLog, shfPairing, Real.exp_zero] using h
  have hFsec (x : Plane) : AEStronglyMeasurable
      (fun ω => heatStartLog Z σ T σ x ω) P := by
    have h := hpos σ T σ x 0 (le_of_lt hσ) hσT hσ
    change AEStronglyMeasurable (fun ω => Real.log
      (shfPairing Z σ T (fun y => heatKernel σ (y - x)) (fun _ => 1) ω)) P
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using
      h.2.aestronglyMeasurable
  obtain ⟨M, hM, hSq⟩ := shf_heatStartLogField_square_bound ϑ P Z hZ hpair hjoint hpos
    T 0 (s := σ) (δ := σ) (le_of_lt hσ) hσT hσ
  have hSq' : ∀ x : Plane, Integrable (fun ω =>
      |heatStartLog Z σ T σ x ω| ^ 2) P ∧
      ∫ ω, |heatStartLog Z σ T σ x ω| ^ 2 ∂P ≤ M := by
    intro x
    simpa only [heatStartLog, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      Real.exp_zero] using hSq x
  have hprod := integrable_test_mul_joint P hF hFsec hM hSq' φ
  exact Integrable.prod_left_ae hprod

private theorem kpzRegularizedReversed_integral_sub_ae (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {T α β : ℝ} (hα : 0 < α) (hαT : α < T) (hβ : 0 < β) (hβT : β < T)
    (φ : TestFn) :
    (fun ω => ∫ y, φ y * (kpzRegularizedReversed P Z 0 T α 0 y ω -
      kpzRegularizedReversed P Z 0 T β 0 y ω)) =ᵐ[P]
      fun ω => (∫ y, φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) -
        (∫ y, φ y * kpzRegularizedReversed P Z 0 T β 0 y ω) := by
  have hαint := heatStartLog_test_integrable_of ϑ P Z hZ hα hαT φ
  have hβint := heatStartLog_test_integrable_of ϑ P Z hZ hβ hβT φ
  filter_upwards [hαint, hβint] with ω hαω hβω
  have hαc : Integrable (fun y => φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) := by
    let cα : ℝ := ∫ ω', heatStartLog Z α T α 0 ω' ∂P
    have heq : (fun y => φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) =
        fun y => φ y * heatStartLog Z α T α y ω - φ y * cα := by
      funext y
      simp [cα, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
      ring
    rw [heq]
    exact hαω.sub ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const cα)
  have hβc : Integrable (fun y => φ y * kpzRegularizedReversed P Z 0 T β 0 y ω) := by
    let cβ : ℝ := ∫ ω', heatStartLog Z β T β 0 ω' ∂P
    have heq : (fun y => φ y * kpzRegularizedReversed P Z 0 T β 0 y ω) =
        fun y => φ y * heatStartLog Z β T β y ω - φ y * cβ := by
      funext y
      simp [cβ, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
      ring
    rw [heq]
    exact hβω.sub ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const cβ)
  have hfun : (fun y => φ y * (kpzRegularizedReversed P Z 0 T α 0 y ω -
      kpzRegularizedReversed P Z 0 T β 0 y ω)) =
      fun y => φ y * kpzRegularizedReversed P Z 0 T α 0 y ω -
        φ y * kpzRegularizedReversed P Z 0 T β 0 y ω := by
    funext y
    rw [mul_sub]
  calc
    (∫ y, φ y * (kpzRegularizedReversed P Z 0 T α 0 y ω -
        kpzRegularizedReversed P Z 0 T β 0 y ω)) =
        ∫ y, φ y * kpzRegularizedReversed P Z 0 T α 0 y ω -
          φ y * kpzRegularizedReversed P Z 0 T β 0 y ω := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => congrFun hfun y
    _ = (∫ y, φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) -
        ∫ y, φ y * kpzRegularizedReversed P Z 0 T β 0 y ω := integral_sub hαc hβc

private theorem kpzRegularizedReversed_average_centered_ae (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {T ε : ℝ} (_hT : 0 < T) (hε : 0 < ε)
    (hεT : ε ^ 2 < T) (φ : TestFn) (hφ₁ : ∫ y, φ y = 1) (x : Plane) :
    (fun ω => (∫ y, (φ.dilate ε x) y *
      kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) -
      (heatStartLog Z (ε ^ 2) T (ε ^ 2) (x + ε • barycentre φ) ω -
        ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2)
          (x + ε • barycentre φ) ω' ∂P)) =ᵐ[P]
      fun ω => (∫ y, (φ.dilate ε x) y *
        heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
          heatStartLog Z (ε ^ 2) T (ε ^ 2) (x + ε • barycentre φ) ω := by
  let base : TestFn := φ.dilate ε x
  let b : Plane := x + ε • barycentre φ
  have hδ : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hmass : ∫ y, base y = 1 := by
    simpa only [base, hφ₁, mul_one] using
      integral_testFn_dilate_mul φ hε x (fun _ => (1 : ℝ))
  have hlogInt := heatStartLog_test_integrable_of ϑ P Z hZ hδ hεT base
  have hbaseInt : Integrable base :=
    base.continuous.integrable_of_hasCompactSupport base.hasCompactSupport
  have hInt0 := heatStartLog_integrable_of ϑ P Z hZ (le_of_lt hδ) hεT hδ (0 : Plane)
  have hIntb := heatStartLog_integrable_of ϑ P Z hZ (le_of_lt hδ) hεT hδ b
  have hident := heatStartLog_identDistrib_of ϑ P Z hZ hsym
    (le_of_lt hδ) hεT hδ b
  have hmean : (∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P) =
      ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) 0 ω' ∂P := hident.integral_eq
  let c : ℝ := ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) 0 ω' ∂P
  filter_upwards [hlogInt] with ω hlogω
  have hregInt : Integrable (fun y => base y *
      kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) := by
    have heq : (fun y => base y * kpzRegularizedReversed P Z 0 T
        (ε ^ 2) 0 y ω) = fun y => base y * heatStartLog Z (ε ^ 2) T
          (ε ^ 2) y ω - base y * c := by
      funext y
      simp [c, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
      ring
    rw [heq]
    exact hlogω.sub (hbaseInt.mul_const c)
  have hregEq : (∫ y, base y * kpzRegularizedReversed P Z 0 T
      (ε ^ 2) 0 y ω) =
      (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
        ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P := by
    calc
      _ = (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
          ∫ y, base y * c := by
        rw [show (fun y => base y * kpzRegularizedReversed P Z 0 T
            (ε ^ 2) 0 y ω) = fun y => base y * heatStartLog Z (ε ^ 2) T
              (ε ^ 2) y ω - base y * c by
              funext y
              simp [c, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
              ring]
        exact integral_sub hlogω (hbaseInt.mul_const c)
      _ = (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) - c := by
        rw [integral_mul_const, hmass]
        ring
      _ = (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
          ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P := by rw [hmean]
  change (∫ y, base y * kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) -
      (heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω -
        ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P) = _
  rw [hregEq]
  ring

/-- Every critical KPZ test pairing is almost everywhere measurable. -/
theorem aemeasurable_isCriticalKPZ_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {T : ℝ} (hT : 0 < T) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hH : IsCriticalKPZ P Z H) (φ : TestFn) :
    AEMeasurable (fun ω => H T 0 ω φ) P := by
  let δseq : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  have hδseq : Tendsto δseq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    · exact div_pos hT (by positivity)
  have hconv := (hH T hT 0 φ).comp hδseq
  apply hconv.aemeasurable
  intro n
  have hδn : 0 < δseq n := div_pos hT (by positivity)
  have hδnT : δseq n < T := by
    dsimp [δseq]
    have hden : (1 : ℝ) < (n : ℝ) + (2 : ℝ) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact div_lt_self hT hden
  exact Critical2DKPZ.JointConvergence.aemeasurable_integral_kpzRegularized
    ϑ P Z hZ T (δseq n) hδnT hδn 0 φ

/-- Under the heat-start convergence and smoothing hypotheses, a KPZ pairing with a shrinking unit-mass nonnegative test can be coupled to the centered heat-start logarithm at its barycentre with uniformly bounded mean absolute error. -/
theorem kpz_point_matched_comparison_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {T : ℝ} (hT : 0 < T) (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y)
    (hφ₁ : ∫ y, φ y = 1) (x : Plane) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ X : Ω → ℝ, P.map X = P.map (fun ω => H T 0 ω (φ.dilate ε x)) ∧
        Integrable (fun ω => X ω - (heatStartLog Z (ε ^ 2) T (ε ^ 2)
          (x + ε • barycentre φ) ω -
            ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2)
              (x + ε • barycentre φ) ω' ∂P)) P ∧
        ∫ ω, |X ω - (heatStartLog Z (ε ^ 2) T (ε ^ 2)
          (x + ε • barycentre φ) ω -
            ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2)
              (x + ε • barycentre φ) ω' ∂P)| ∂P ≤ C := by
  have _hHeatStartLogInputAvailable : HeatStartLogAt ϑ P Z := hHeatStartLogInput
  have _hHeatStartLogInputFieldAvailable : HeatStartLogFieldAt ϑ P Z := hHeatStartLogFieldInput
  obtain ⟨X, _hXmeas, _hXrate, hXconv, _hXlat, hXlaw⟩ := hC12 T hT
  obtain ⟨Creg, εreg, hεreg, hreg⟩ :=
    kpzRegularizedReversed_shrinking_le_of ϑ P Z hZ hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput hT φ
  let ε₀ : ℝ := min εreg (Real.sqrt T / 2)
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min hεreg (half_pos (Real.sqrt_pos.mpr hT))
  refine ⟨1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2, ε₀, hε₀, ?_⟩
  intro ε hε hε₀'
  have hεreg' : ε < εreg := lt_of_lt_of_le hε₀' (min_le_left _ _)
  have hεsqrt : ε < Real.sqrt T / 2 := lt_of_lt_of_le hε₀' (min_le_right _ _)
  have hεT : ε ^ 2 < T := by
    have hsq : ε ^ 2 < (Real.sqrt T / 2) ^ 2 := by
      nlinarith [sq_nonneg (ε - Real.sqrt T / 2)]
    rw [div_pow, Real.sq_sqrt hT.le] at hsq
    nlinarith
  let base : TestFn := φ.dilate ε x
  let Aε : Ω → ℝ := fun ω => ∫ y, base y *
    kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω
  let F : Ω → ℝ := fun ω => X 0 0 base ω
  let G : Ω → ℝ := fun ω => heatStartLog Z (ε ^ 2) T (ε ^ 2)
    (x + ε • barycentre φ) ω -
      ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2)
        (x + ε • barycentre φ) ω' ∂P
  have hXlaw : P.map (F) = P.map (fun ω => H T 0 ω base) := by
    have h := hXlaw H hH 1 (fun _ : Fin 1 => 0)
      (fun _ : Fin 1 => (0 : Plane →ᵇ ℝ)) (fun _ : Fin 1 => base)
      (by intro i; simp [hT])
    have hSigmaLe : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
      dsimp [shfSigma]
      apply iSup_le
      intro s
      apply iSup_le
      intro u
      apply iSup_le
      intro hsu
      exact (hZ.1 s u hsu.1 hsu.2).comap_le
    have hXscalarMeas : Measurable (X 0 0 base) :=
      (_hXmeas 0 0 base (by norm_num) hT).mono hSigmaLe le_rfl
    have hXvecMeas : Measurable (fun ω (i : Fin 1) => X 0 0 base ω) :=
      Measurable.of_eval fun _ => hXscalarMeas
    let δseq : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    have hδseq : Tendsto δseq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · exact tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      · exact div_pos hT (by positivity)
    have hHconv := (hH T hT 0 base).comp hδseq
    have hHscalarMeas : AEMeasurable (fun ω => H T 0 ω base) P := by
      apply hHconv.aemeasurable
      intro n
      have hδn : 0 < δseq n := div_pos hT (by positivity)
      have hδnT : δseq n < T := by
        dsimp [δseq]
        have hden : (1 : ℝ) < (n : ℝ) + (2 : ℝ) := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact div_lt_self hT hden
      exact Critical2DKPZ.JointConvergence.aemeasurable_integral_kpzRegularized
        ϑ P Z hZ T (δseq n) hδnT hδn 0 base
    have hHvecMeas : AEMeasurable (fun ω (i : Fin 1) => H T 0 ω base) P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact hHscalarMeas
    have hXmap : (P.map (fun ω (i : Fin 1) => X 0 0 base ω)).map
        (fun v => v 0) = P.map (X 0 0 base) := by
      simpa only [Function.comp_def] using
        (Measure.map_map (measurable_pi_apply (0 : Fin 1)) hXvecMeas)
    have hHmap : (P.map (fun ω (i : Fin 1) => H T 0 ω base)).map
        (fun v => v 0) = P.map (fun ω => H T 0 ω base) := by
      simpa only [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable
          (measurable_pi_apply (0 : Fin 1)).aemeasurable hHvecMeas)
    have h' : Measure.map (fun ω (i : Fin 1) => X 0 0 base ω) P =
        Measure.map (fun ω (i : Fin 1) => H T 0 ω base) P := by
      simpa only [sub_zero] using h
    have heval := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (fun v => v 0)) h'
    rw [hXmap, hHmap] at heval
    simpa [F, base] using heval
  have hconv := hXconv 0 0 base 2 (by norm_num) hT (by norm_num) (by norm_num)
  have happroxEvent : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      eLpNorm (fun ω => (∫ y, base y *
        kpzRegularizedReversed P Z 0 T δ 0 y ω) - F ω) 2 P < 1 :=
    hconv.eventually (Iio_mem_nhds (by norm_num))
  have hδsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < ε ^ 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨δ, ⟨⟨hδconv, hδε⟩, hδpos⟩⟩ :=
    ((happroxEvent.and hδsmall).and eventually_mem_nhdsWithin).exists
  have hδle : δ ≤ ε ^ 2 := le_of_lt hδε
  let Aδ : Ω → ℝ := fun ω => ∫ y, base y *
    kpzRegularizedReversed P Z 0 T δ 0 y ω
  have happrox' : eLpNorm (fun ω => F ω -
      (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P ≤ ENNReal.ofReal 1 := by
    have hneg := le_of_lt hδconv
    have hEq : (fun ω => F ω -
        (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω)) =
        fun ω => -((∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) - F ω) := by
      funext ω
      ring
    rw [hEq]
    change eLpNorm (-fun ω =>
      (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) - F ω) 2 P ≤ _
    rw [eLpNorm_neg]
    simpa using hneg
  have hreg' := hreg ε hε hεreg' x δ hδpos hδle
  have hmidAE := kpzRegularizedReversed_integral_sub_ae ϑ P Z hZ
    (T := T) (α := ε ^ 2) (β := δ) (sq_pos_of_pos hε) hεT hδpos
    (lt_of_le_of_lt hδle hεT) base
  let f₁ : Ω → ℝ := fun ω => F ω - Aδ ω
  let f₂ : Ω → ℝ := fun ω => Aδ ω - Aε ω
  let f₃ : Ω → ℝ := fun ω => Aε ω - G ω
  have hf₁bound : eLpNorm f₁ 2 P ≤ ENNReal.ofReal 1 := by
    have hEq : f₁ = fun ω => F ω -
        (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) := by
      funext ω
      rfl
    simpa only [f₁, Aδ] using happrox'
  have hf₂bound : eLpNorm f₂ 2 P ≤ ENNReal.ofReal Creg := by
    have hEq : f₂ =ᵐ[P] fun ω => -∫ y, base y *
        (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
          kpzRegularizedReversed P Z 0 T δ 0 y ω) := by
      filter_upwards [hmidAE] with ω hω
      dsimp [f₂, Aδ, Aε]
      rw [hω]
      ring
    calc
      eLpNorm f₂ 2 P = eLpNorm (fun ω => -∫ y, base y *
          (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P := eLpNorm_congr_ae hEq
      _ = eLpNorm (fun ω => ∫ y, base y *
          (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P := by
        change eLpNorm (-fun ω => ∫ y, base y *
          (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P = _
        exact eLpNorm_neg (fun ω => ∫ y, base y *
          (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P
      _ ≤ ENNReal.ofReal Creg := hreg'
  have hf₁ := integral_abs_le_eLpNorm_two P f₁ 1 hf₁bound
  have hf₂ := integral_abs_le_eLpNorm_two P f₂ Creg hf₂bound
  have hcenterAE := kpzRegularizedReversed_average_centered_ae ϑ P Z hZ hsym
    hT hε hεT φ hφ₁ x
  have haverage := heatStartLog_average_sub_le_of ϑ P Z hZ hsym hT φ hφ hφ₁ x hε hεT
  have hf₃eq : f₃ =ᵐ[P] fun ω => (∫ y, base y *
      heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
        heatStartLog Z (ε ^ 2) T (ε ^ 2)
          (x + ε • barycentre φ) ω := by
    filter_upwards [hcenterAE] with ω hω
    dsimp [f₃, Aε, G, base] at hω ⊢
    exact hω
  have hf₃ : Integrable f₃ P := haverage.1.congr hf₃eq.symm
  have hf₃bound : ∫ ω, |f₃ ω| ∂P ≤ ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
    calc
      ∫ ω, |f₃ ω| ∂P = ∫ ω, |(∫ y, base y *
          heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
            heatStartLog Z (ε ^ 2) T (ε ^ 2)
              (x + ε • barycentre φ) ω| ∂P := by
        apply integral_congr_ae
        filter_upwards [hf₃eq] with ω hω
        rw [hω]
      _ ≤ ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := haverage.2
  have hdecomp : (fun ω => F ω - G ω) = fun ω => f₁ ω + f₂ ω + f₃ ω := by
    funext ω
    simp only [f₁, f₂, f₃, Aδ, Aε]
    ring
  have hsumInt : Integrable (fun ω => f₁ ω + f₂ ω + f₃ ω) P :=
    (hf₁.1.add hf₂.1).add hf₃
  have htargetInt : Integrable (fun ω => F ω - G ω) P := hsumInt.congr
    (Filter.Eventually.of_forall fun ω => (congrFun hdecomp ω).symm)
  have hsumAbsInt : Integrable (fun ω => |f₁ ω| + |f₂ ω| + |f₃ ω|) P :=
    (hf₁.1.abs.add hf₂.1.abs).add hf₃.abs
  have hsumAbs : ∫ ω, |f₁ ω + f₂ ω + f₃ ω| ∂P ≤
      ∫ ω, (|f₁ ω| + |f₂ ω| + |f₃ ω|) ∂P := by
    apply integral_mono (hsumInt.abs) hsumAbsInt
    intro ω
    calc
      |f₁ ω + f₂ ω + f₃ ω| ≤ |f₁ ω + f₂ ω| + |f₃ ω| := abs_add_le _ _
      _ ≤ |f₁ ω| + |f₂ ω| + |f₃ ω| := by
        calc
          |f₁ ω + f₂ ω| + |f₃ ω| ≤ (|f₁ ω| + |f₂ ω|) + |f₃ ω| :=
            add_le_add (abs_add_le _ _) (le_refl _)
          _ = |f₁ ω| + |f₂ ω| + |f₃ ω| := rfl
  have hsumBound : ∫ ω, (|f₁ ω| + |f₂ ω| + |f₃ ω|) ∂P ≤
      1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
    have h12 : (∫ ω, |f₁ ω| + |f₂ ω| ∂P) =
        (∫ ω, |f₁ ω| ∂P) + ∫ ω, |f₂ ω| ∂P := integral_add hf₁.1.abs hf₂.1.abs
    calc
      (∫ ω, (|f₁ ω| + |f₂ ω|) + |f₃ ω| ∂P) =
          (∫ ω, |f₁ ω| + |f₂ ω| ∂P) + ∫ ω, |f₃ ω| ∂P :=
        integral_add (hf₁.1.abs.add hf₂.1.abs) hf₃.abs
      _ = (∫ ω, |f₁ ω| ∂P) + ∫ ω, |f₂ ω| ∂P + ∫ ω, |f₃ ω| ∂P := by rw [h12]
      _ ≤
          max 1 0 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
        exact add_le_add (add_le_add hf₁.2 hf₂.2) hf₃bound
      _ = 1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by simp
  refine ⟨F, ?_, htargetInt, ?_⟩
  · simpa only [F, base] using hXlaw
  · calc
      ∫ ω, |F ω - G ω| ∂P = ∫ ω, |f₁ ω + f₂ ω + f₃ ω| ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [congrFun hdecomp ω]
      _ ≤ ∫ ω, (|f₁ ω| + |f₂ ω| + |f₃ ω|) ∂P := hsumAbs
      _ ≤ 1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := hsumBound

end Critical2DKPZ.SmallScales

end
