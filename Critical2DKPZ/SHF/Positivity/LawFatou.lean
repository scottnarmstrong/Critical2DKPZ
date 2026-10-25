/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.SHF.Limit.FirstMoment
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic

/-! # Portmanteau bounds for critical stochastic heat-flow pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped CompactlySupported ENNReal Topology

namespace Critical2DKPZ.SHF.Positivity

/-- Fatou's inequality for nonnegative real-valued variables under convergence in distribution. -/
theorem lintegral_ofReal_le_liminf_of_tendstoInDistribution_nonneg
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y μ P)
    (hXnn : ∀ N ω, 0 ≤ X N ω) (hYnn : ∀ ω, 0 ≤ Y ω) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤
      liminf (fun N => ∫⁻ ω, ENNReal.ofReal (X N ω) ∂(μ N)) atTop := by
  let νN : ℕ → ProbabilityMeasure ℝ := fun N => ⟨(μ N).map (X N), inferInstance⟩
  let ν : ProbabilityMeasure ℝ := ⟨P.map Y, inferInstance⟩
  have hν : Tendsto νN atTop (𝓝 ν) := by
    simpa only [νN, ν] using hX.tendsto
  have hopen : ∀ G, IsOpen G → (ν : Measure ℝ) G ≤
      atTop.liminf (fun N => (νN N : Measure ℝ) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν hG
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (ν : Measure ℝ)) (μs := fun N => (νN N : Measure ℝ))
    (f := fun x : ℝ => max x 0) (continuous_id.max continuous_const)
    (fun _ => le_max_right _ _) hopen
  have hport' :
      ∫⁻ x, ENNReal.ofReal (max x 0) ∂P.map Y ≤
        liminf (fun N => ∫⁻ x, ENNReal.ofReal (max x 0) ∂(μ N).map (X N)) atTop := by
    simpa [ν, νN] using hport
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (max x 0)) := by fun_prop
  have hmapY : ∫⁻ x, ENNReal.ofReal (max x 0) ∂P.map Y =
      ∫⁻ ω, ENNReal.ofReal (max (Y ω) 0) ∂P :=
    lintegral_map' hmeas.aemeasurable hX.aemeasurable_limit
  have hmapN (N : ℕ) : ∫⁻ x, ENNReal.ofReal (max x 0) ∂(μ N).map (X N) =
      ∫⁻ ω, ENNReal.ofReal (max (X N ω) 0) ∂(μ N) :=
    lintegral_map' hmeas.aemeasurable (hX.forall_aemeasurable N)
  rw [hmapY] at hport'
  simp_rw [hmapN] at hport'
  have hmaxN (N : ℕ) (ω : Ω') : max (X N ω) 0 = X N ω :=
    max_eq_left (hXnn N ω)
  simpa only [max_eq_left (hYnn _), hmaxN] using hport'

/-- Fatou in law for compact nonnegative pairings of a critical SHF. -/
theorem isCriticalSHF_lintegral_pairing_le_liminf (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (f : C_c(Plane × Plane, ℝ)) (hf : ∀ p, 0 ≤ f p) :
    ∫⁻ ω, ENNReal.ofReal (∫ p, f p ∂(Z s t ω)) ∂P ≤
      liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
        (∫ p, f p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop := by
  let s₁ : Fin 1 → ℝ := fun _ => s
  let t₁ : Fin 1 → ℝ := fun _ => t
  have hvec := hZ.2.2 1 s₁ t₁
    (by intro i; exact ⟨hs, hst⟩) (fun _ => f) (fun _ => (0 : C_c(Plane, ℝ)))
  have hscalar := hvec.continuous_comp
    (g := fun v : Fin 1 → ℝ × ℝ => (v 0).1) (by fun_prop)
  have hdist : TendstoInDistribution
      (fun N ω => ∫ p, f p ∂(polymerMeasure ϑ N s t ω)) atTop
      (fun ω => ∫ p, f p ∂(Z s t ω)) (fun _ => disorderLaw) P := by
    simpa only [Function.comp_def, s₁, t₁, integral_polymerMeasure] using hscalar
  apply lintegral_ofReal_le_liminf_of_tendstoInDistribution_nonneg hdist
  · intro N ω
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun p => hf p)
  · intro ω
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun p => hf p)

end Critical2DKPZ.SHF.Positivity

end
