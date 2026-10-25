/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.LimitCutoffTail
public import Critical2DKPZ.SHF.Positivity.CompactConvergence
public import Critical2DKPZ.JointConvergence.Approximation
import Mathlib.Tactic

/-! # Convergence in law for bounded-terminal heat-start pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.JointConvergence
open scoped BoundedContinuousFunction CompactlySupported ENNReal Topology

namespace Critical2DKPZ.SHF.Positivity

private theorem expected_heatBoundedTerminal_cutoff_error_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    {δ : ℝ} (hδ : 0 < δ) (x : Plane) (g : Plane →ᵇ ℝ) (R : ℝ)
    (hKae : ∀ᵐ ω ∂P,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (μ ω))
    (hKint : Integrable (fun ω => ∫ p, heatKernel δ (p.1 - x) ∂(μ ω)) P) :
    Integrable (fun ω => (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(μ ω)) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂(μ ω)) P ∧
    (∫ ω, ‖(∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(μ ω)) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂(μ ω)‖ ∂P) ≤
      ‖g‖ * ∫ ω, ∫ p, heatPairingCutoffTail δ x R p ∂(μ ω) ∂P := by
  have hFullAE : ∀ᵐ ω ∂P,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (μ ω) :=
    hKae.mono fun ω hω => integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x g hω
  have hCutAE : ∀ᵐ ω ∂P,
      Integrable (heatBoundedTerminalCutoffTest δ x g R) (μ ω) :=
    hKae.mono fun ω hω => integrable_heatBoundedTerminalCutoffTest (μ ω) hδ x g R hω
  have hFullMeas := aemeasurable_integral_of_measurable_measure P μ hμ
    (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2)
    (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
      (g.continuous.comp continuous_snd)).measurable hFullAE
  have hCutMeas := aemeasurable_integral_of_measurable_measure P μ hμ
    (heatBoundedTerminalCutoffTest δ x g R)
    (heatBoundedTerminalCutoffTest δ x g R).continuous_toFun.measurable hCutAE
  let D : Ω → ℝ := fun ω =>
    (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(μ ω)) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂(μ ω)
  have hDmeas : AEMeasurable D P := by
    dsimp [D]
    exact hFullMeas.sub hCutMeas
  have hTailInt := integrable_random_heatPairingCutoffTail P μ hμ hδ x R hKae hKint
  have hError : ∀ᵐ ω ∂P, ‖D ω‖ ≤ ‖g‖ *
      ∫ p, heatPairingCutoffTail δ x R p ∂(μ ω) := by
    filter_upwards [hKae] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_integral_heatBoundedTerminal_cutoff_error_le (μ ω) hδ x g R hω
  have hMajor : Integrable (fun ω => ‖g‖ *
      ∫ p, heatPairingCutoffTail δ x R p ∂(μ ω)) P := hTailInt.const_mul ‖g‖
  have hDint : Integrable D P := by
    apply hMajor.mono' hDmeas.aestronglyMeasurable
    filter_upwards [hError] with ω hω
    exact hω
  refine ⟨hDint, ?_⟩
  calc
    (∫ ω, ‖D ω‖ ∂P) ≤
        ∫ ω, ‖g‖ * ∫ p, heatPairingCutoffTail δ x R p ∂(μ ω) ∂P :=
      integral_mono_ae hDint.norm hMajor hError
    _ = ‖g‖ * ∫ ω, ∫ p, heatPairingCutoffTail δ x R p ∂(μ ω) ∂P :=
      integral_const_mul _ _

private theorem pi_norm_le_sum_norm {k : ℕ} (v : Fin k → ℝ) :
    ‖v‖ ≤ ∑ i : Fin k, ‖v i‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i hi => norm_nonneg (v i))).2
  intro i
  exact (Finset.single_le_sum (fun j hj => norm_nonneg (v j)) (Finset.mem_univ i))

private theorem lintegral_norm_pi_le_of_component_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (D : Ω → Fin k → ℝ) (hD : AEMeasurable D P)
    (hDint : ∀ i, Integrable (fun ω => ‖D ω i‖) P)
    (B : Fin k → ℝ)
    (hB : ∀ i, ∫ ω, ‖D ω i‖ ∂P ≤ B i) :
    ∫⁻ ω, ENNReal.ofReal ‖D ω‖ ∂P ≤ ENNReal.ofReal (∑ i, B i) := by
  have hsumInt : Integrable (fun ω => ∑ i : Fin k, ‖D ω i‖) P :=
    integrable_finsetSum Finset.univ (fun i hi => hDint i)
  have hnormInt : Integrable (fun ω => ‖D ω‖) P := by
    apply hsumInt.mono' hD.aestronglyMeasurable.norm
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      pi_norm_le_sum_norm (D ω)
  have hbound : ∫ ω, ‖D ω‖ ∂P ≤ ∑ i, B i := by
    calc
      _ ≤ ∫ ω, ∑ i : Fin k, ‖D ω i‖ ∂P := by
        apply integral_mono hnormInt hsumInt
        intro ω
        exact pi_norm_le_sum_norm (D ω)
      _ = ∑ i, ∫ ω, ‖D ω i‖ ∂P := by
        rw [integral_finsetSum Finset.univ (fun i hi => hDint i)]
      _ ≤ ∑ i, B i := Finset.sum_le_sum fun i hi => hB i
  have hnonneg : 0 ≤ᵐ[P] fun ω => ‖D ω‖ :=
    Filter.Eventually.of_forall fun ω => norm_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hnormInt hnonneg]
  exact ENNReal.ofReal_le_ofReal hbound

private theorem polymerMeasure_zero_for_boundedPairing (ϑ : ℝ) (s t : ℝ)
    (ω : Disorder) : polymerMeasure ϑ 0 s t ω = 0 := by
  rw [polymerMeasure]
  ext A hA
  simp [rescaledP2P]

private theorem ae_integrable_polymer_heat_start_all (ϑ : ℝ) (N : ℕ)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) :
    ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x))
        (polymerMeasure ϑ N s t ω) := by
  by_cases hN : N = 0
  · subst N
    have hzero (ω : Disorder) : polymerMeasure ϑ 0 s t ω = 0 :=
      polymerMeasure_zero_for_boundedPairing ϑ s t ω
    filter_upwards [] with ω
    rw [hzero]
    exact integrable_zero_measure
  · exact ae_integrable_polymer_heat_start ϑ
      (Nat.one_le_iff_ne_zero.mpr hN) s t δ hδ x

private theorem integrable_polymer_heat_start_all (ϑ : ℝ) (N : ℕ)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) :
    Integrable (fun ω => ∫ p, heatKernel δ (p.1 - x)
      ∂(polymerMeasure ϑ N s t ω)) disorderLaw := by
  by_cases hN : N = 0
  · subst N
    have hzero (ω : Disorder) : polymerMeasure ϑ 0 s t ω = 0 :=
      polymerMeasure_zero_for_boundedPairing ϑ s t ω
    have heq : (fun ω => ∫ p, heatKernel δ (p.1 - x)
        ∂(polymerMeasure ϑ 0 s t ω)) = fun _ => 0 := by
      funext ω
      rw [hzero]
      simp
    rw [heq]
    exact integrable_const _
  · exact (integral_polymer_heat_start_pairing_eq_one ϑ
      (Nat.one_le_iff_ne_zero.mpr hN) s t δ hδ x).1

/-- Joint convergence in law for a finite family of bounded-terminal heat-start pairings. -/
theorem isCriticalSHF_heat_bounded_pairing_joint (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
    (g : Fin k → (Plane →ᵇ ℝ))
    (h : ∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
        ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
          ∂(polymerMeasure ϑ N (s i) (t i) ω))
      atTop
      (fun ω i => shfPairing Z (s i) (t i)
        (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
      (fun _ => disorderLaw) P := by
  let X : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
      ∂(polymerMeasure ϑ N (s i) (t i) ω)
  let Y : ℕ → ℕ → Disorder → Fin k → ℝ := fun j N ω i =>
    ∫ p, heatBoundedTerminalCutoffTest (δ i) (x i) (g i) (j : ℝ) p
      ∂(polymerMeasure ϑ N (s i) (t i) ω)
  let Yl : ℕ → Ω → Fin k → ℝ := fun j ω i =>
    ∫ p, heatBoundedTerminalCutoffTest (δ i) (x i) (g i) (j : ℝ) p
      ∂(Z (s i) (t i) ω)
  let L : Ω → Fin k → ℝ := fun ω i =>
    ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2 ∂(Z (s i) (t i) ω)
  have htimes : ∀ i, 0 ≤ s i ∧ s i < t i := fun i => ⟨(h i).1, (h i).2.1⟩
  have hY (j : ℕ) : TendstoInDistribution (fun N ω i => Y j N ω i) atTop
      (Yl j) (fun _ => disorderLaw) P := by
    let φ : Fin k → C_c(Plane × Plane, ℝ) := fun i =>
      heatBoundedTerminalCutoffTest (δ i) (x i) (g i) (j : ℝ)
    have hcompact := isCriticalSHF_compact_pairings_tendsto P Z hZ s t htimes φ
    simpa only [Y, Yl, φ] using hcompact
  have hXm (N : ℕ) : AEMeasurable (X N) disorderLaw := by
    apply aemeasurable_pi_iff.mpr
    intro i
    have hμ := measurable_polymerMeasure ϑ N (s i) (t i)
    have hpair := ae_integrable_polymer_heat_start_all ϑ N
      (s := s i) (t := t i) (h i).2.2 (x i)
    have hpair' := hpair.mono fun ω hω =>
      integrable_heatKernel_mul_boundedTerminal _ (h i).2.2 (x i) (g i) hω
    have hm := aemeasurable_integral_of_measurable_measure disorderLaw
      (polymerMeasure ϑ N (s i) (t i)) hμ
      (fun p => heatKernel (δ i) (p.1 - x i) * g i p.2)
      (((continuous_heatKernel (δ i)).comp (continuous_fst.sub continuous_const)).mul
        ((g i).continuous.comp continuous_snd)).measurable hpair'
    simpa only [X] using hm
  have hLm : AEMeasurable L P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    have hpair := isCriticalSHF_ae_integrable_heat_start ϑ P Z hZ
      (htimes i).1 (htimes i).2 (h i).2.2 (x i)
    have hpair' := hpair.mono fun ω hω =>
      integrable_heatKernel_mul_boundedTerminal _ (h i).2.2 (x i) (g i) hω
    have hm := aemeasurable_integral_of_measurable_measure P (Z (s i) (t i))
      (hZ.1 (s i) (t i) (htimes i).1 (htimes i).2)
      (fun p => heatKernel (δ i) (p.1 - x i) * g i p.2)
      (((continuous_heatKernel (δ i)).comp (continuous_fst.sub continuous_const)).mul
        ((g i).continuous.comp continuous_snd)).measurable hpair'
    simpa only [L] using hm
  have hYl : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖Yl j ω - L ω‖ ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    let c : ℝ := ∑ i : Fin k, ‖g i‖
    let α : ℝ := ε / (c + 1)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hα : 0 < α := by dsimp [α]; positivity
    have hsumBound : (∑ i : Fin k, ‖g i‖ * α) ≤ ε := by
      calc
        (∑ i : Fin k, ‖g i‖ * α) = c * α := by
          dsimp [c]
          rw [Finset.sum_mul]
        _ ≤ ε := by
          dsimp [α]
          have hc' : 0 < c + 1 := by linarith
          calc
            c * (ε / (c + 1)) = ε * (c / (c + 1)) := by ring
            _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
              ((div_le_iff₀ hc').2 (by linarith)) hε.le
            _ = ε := by ring
    have hcoord (i : Fin k) : ∀ᶠ j in atTop,
        Integrable (fun ω => ‖Yl j ω i - L ω i‖) P ∧
        ∫ ω, ‖Yl j ω i - L ω i‖ ∂P ≤ ‖g i‖ * α := by
      obtain ⟨R₀, htail⟩ := isCriticalSHF_heat_pairing_cutoff_le ϑ P Z hZ
        (htimes i).1 (htimes i).2 (h i).2.2 (x i) α hα
      have hR := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R₀)
      filter_upwards [hR] with j hj
      have he := expected_heatBoundedTerminal_cutoff_error_le P (Z (s i) (t i))
        (hZ.1 (s i) (t i) (htimes i).1 (htimes i).2)
        (h i).2.2 (x i) (g i) (j : ℝ)
        (isCriticalSHF_ae_integrable_heat_start ϑ P Z hZ
          (htimes i).1 (htimes i).2 (h i).2.2 (x i))
        (isCriticalSHF_heat_start_integrable_bound ϑ P Z hZ
          (htimes i).1 (htimes i).2 (h i).2.2 (x i)).1
      have htail' := htail (j : ℝ) hj
      constructor
      · simpa only [Yl, L, norm_sub_rev] using he.1.norm
      · have hb := he.2.trans
          (mul_le_mul_of_nonneg_left htail' (norm_nonneg _))
        simpa only [Yl, L, norm_sub_rev] using hb
    have hcoordAll : ∀ᶠ j in atTop, ∀ i, Integrable
        (fun ω => ‖Yl j ω i - L ω i‖) P ∧
        ∫ ω, ‖Yl j ω i - L ω i‖ ∂P ≤ ‖g i‖ * α :=
      Filter.eventually_all.mpr hcoord
    filter_upwards [hcoordAll] with j hj
    have hDmeas : AEMeasurable (fun ω => Yl j ω - L ω) P :=
      (hY j).aemeasurable_limit.sub hLm
    have hvec := lintegral_norm_pi_le_of_component_bounds P
      (fun ω => Yl j ω - L ω) hDmeas
      (fun i => (hj i).1) (fun i => ‖g i‖ * α)
      (fun i => (hj i).2)
    exact hvec.trans (ENNReal.ofReal_le_ofReal hsumBound)
  have hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᶠ N in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖X N ω - Y j N ω‖ ∂disorderLaw ≤ ENNReal.ofReal ε := by
    intro ε hε
    let c : ℝ := ∑ i : Fin k, ‖g i‖
    let α : ℝ := ε / (c + 1)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hα : 0 < α := by dsimp [α]; positivity
    have hsumBound : (∑ i : Fin k, ‖g i‖ * α) ≤ ε := by
      calc
        (∑ i : Fin k, ‖g i‖ * α) = c * α := by
          dsimp [c]
          rw [Finset.sum_mul]
        _ ≤ ε := by
          dsimp [α]
          have hc' : 0 < c + 1 := by linarith
          calc
            c * (ε / (c + 1)) = ε * (c / (c + 1)) := by ring
            _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
              ((div_le_iff₀ hc').2 (by linarith)) hε.le
            _ = ε := by ring
    have hcoord (i : Fin k) : ∀ᶠ j in atTop, ∀ᶠ N in atTop,
        ∫ ω, ‖X N ω i - Y j N ω i‖ ∂disorderLaw ≤ ‖g i‖ * α := by
      obtain ⟨R₀, htail⟩ := integral_polymer_heat_pairing_cutoff_le ϑ
        (htimes i).1 (htimes i).2 (h i).2.2 (x i) α hα
      have hR := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R₀)
      filter_upwards [hR] with j hj
      filter_upwards [htail (j : ℝ) hj] with N htailN
      have he := expected_heatBoundedTerminal_cutoff_error_le disorderLaw
        (polymerMeasure ϑ N (s i) (t i)) (measurable_polymerMeasure ϑ N (s i) (t i))
        (h i).2.2 (x i) (g i) (j : ℝ)
        (ae_integrable_polymer_heat_start_all ϑ N (s := s i) (t := t i)
          (h i).2.2 (x i))
        (integrable_polymer_heat_start_all ϑ N (s := s i) (t := t i)
          (h i).2.2 (x i))
      have hb := he.2.trans
        (mul_le_mul_of_nonneg_left htailN (norm_nonneg _))
      simpa only [X, Y] using hb
    have hJ : ∀ᶠ j in atTop, ∀ i, ∀ᶠ N in atTop,
        ∫ ω, ‖X N ω i - Y j N ω i‖ ∂disorderLaw ≤ ‖g i‖ * α :=
      Filter.eventually_all.mpr hcoord
    filter_upwards [hJ] with j hj
    have hN : ∀ᶠ N in atTop, ∀ i,
        ∫ ω, ‖X N ω i - Y j N ω i‖ ∂disorderLaw ≤ ‖g i‖ * α :=
      Filter.eventually_all.mpr hj
    filter_upwards [hN] with N hN
    have hYmeas : AEMeasurable (fun ω => Y j N ω) disorderLaw := by
      simpa only [Y] using (hY j).forall_aemeasurable N
    have hDmeas : AEMeasurable (fun ω => X N ω - Y j N ω) disorderLaw :=
      (hXm N).sub hYmeas
    have hDint (i : Fin k) : Integrable
        (fun ω => ‖X N ω i - Y j N ω i‖) disorderLaw := by
      have he := expected_heatBoundedTerminal_cutoff_error_le disorderLaw
        (polymerMeasure ϑ N (s i) (t i)) (measurable_polymerMeasure ϑ N (s i) (t i))
        (h i).2.2 (x i) (g i) (j : ℝ)
        (ae_integrable_polymer_heat_start_all ϑ N (s := s i) (t := t i)
          (h i).2.2 (x i))
        (integrable_polymer_heat_start_all ϑ N (s := s i) (t := t i)
          (h i).2.2 (x i))
      simpa only [X, Y] using he.1.norm
    have hvec := lintegral_norm_pi_le_of_component_bounds disorderLaw
      (fun ω => X N ω - Y j N ω) hDmeas hDint
      (fun i => ‖g i‖ * α) hN
    exact hvec.trans (ENNReal.ofReal_le_ofReal hsumBound)
  exact tendstoInDistribution_of_approx X Y Yl L hY hYl hXY hXm hLm

/-- The heat-start pairing with bounded continuous terminal data is spatially integrable almost surely and has expected absolute value at most the terminal sup norm. Its polymer approximants converge to it in distribution. -/
theorem isCriticalSHF_heat_bounded_pairing (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) :
    (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
      heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
    Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
    (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) =>
        ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
      atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
      (fun _ => disorderLaw) P := by
  have hmoment := isCriticalSHF_heat_bounded_pairing_integrable_bound ϑ P Z hZ
    hs hst hδ x g
  have hjoint := isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ 1
    (fun _ => s) (fun _ => t) (fun _ => δ) (fun _ => x) (fun _ => g)
    (fun _ => ⟨hs, hst, hδ⟩)
  have hscalar := hjoint.continuous_comp
    (g := fun v : Fin 1 → ℝ => v 0) (by fun_prop)
  have hconv : TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) =>
        ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
      atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
      (fun _ => disorderLaw) P := by
    simpa only [Function.comp_def] using hscalar
  exact ⟨hmoment.1, hmoment.2.1, hmoment.2.2, hconv⟩

end Critical2DKPZ.SHF.Positivity

end
