/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.DenseTransportHelpers
public import Critical2DKPZ.SHF.Tsai.TwoBlockReadouts
public import Critical2DKPZ.SHF.Tsai.ProbabilityLimitTransport
public import Critical2DKPZ.RandomMeasure.GeneralTests
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Composition convergence under equality of finite-dimensional laws

The canonical two-block readouts are measurable functions of the input measures. Equality of the
joint laws of the two adjacent blocks and their coarse block therefore transports convergence in
measure, once absolute integrability is known on both realizations.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped Topology CompactlySupported ENNReal

namespace Critical2DKPZ.SHF.Symmetries

private def modifiedCutoffReadout (E : CompactExhaustion (Plane × Plane))
    (w : Plane → ℝ) (f : Plane × Plane → ℝ)
    (q : Measure (Plane × Plane) × Measure (Plane × Plane)) : ℝ≥0∞ :=
  ∫⁻ p, ‖f p‖ₑ ∂chainProduct
    (fun k => if k = 0 then
      RandomMeasure.locallyFiniteMeasureModification E id q.1 else
      RandomMeasure.locallyFiniteMeasureModification E id q.2)
    (fun _ => w) 1

private theorem measurable_modifiedCutoffReadout
    (E : CompactExhaustion (Plane × Plane)) (w : Plane → ℝ) (hw : Measurable w)
    (f : Plane × Plane → ℝ) (hf : Measurable f) :
    Measurable (modifiedCutoffReadout E w f) := by
  let B (k : ℕ) (q : Measure (Plane × Plane) × Measure (Plane × Plane)) :=
    if k = 0 then RandomMeasure.locallyFiniteMeasureModification E id q.1 else
      RandomMeasure.locallyFiniteMeasureModification E id q.2
  have hBm : ∀ k ≤ 1, Measurable (B k) := by
    intro k hk
    by_cases hk0 : k = 0
    · simp only [B, ite_eq_left hk0]
      exact (RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id).comp
        measurable_fst
    · have hk1 : k = 1 := by omega
      simp only [B, ite_eq_right hk0]
      exact (RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id).comp
        measurable_snd
  have hlf : ∀ q, ∀ k ≤ 1, IsLocallyFiniteMeasure (B k q) := by
    intro q k hk
    dsimp only [B]
    split_ifs <;> exact RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id _
  have hchain := measurable_chainProduct 1 B hBm hlf (fun _ => w)
    (fun _ => hw)
  have hread := (Measure.measurable_lintegral hf.enorm).comp hchain
  have hEq : modifiedCutoffReadout E w f =
      fun q => ∫⁻ p, ‖f p‖ₑ ∂chainProduct (fun k => B k q) (fun _ => w) 1 := by
    funext q
    simp only [modifiedCutoffReadout, B]
  rw [hEq]
  exact hread

private theorem modifiedCutoffReadout_eq_smoothedProduct
    (E : CompactExhaustion (Plane × Plane)) (w : Plane → ℝ)
    (f : Plane × Plane → ℝ) (μ ν : Measure (Plane × Plane))
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν) :
    modifiedCutoffReadout E w f (μ, ν) =
      ∫⁻ p, ‖f p‖ₑ ∂smoothedProductMeasure μ w ν := by
  have hμ' := RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id μ hμ
  have hν' := RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id ν hν
  have hseq : (fun k => if k = 0 then
      RandomMeasure.locallyFiniteMeasureModification E id (μ, ν).1 else
      RandomMeasure.locallyFiniteMeasureModification E id (μ, ν).2) =
      fun k => if k = 0 then μ else ν := by
    funext k
    by_cases hk : k = 0
    · simp only [ite_eq_left hk]
      simpa only [id_eq] using hμ'
    · simp only [ite_eq_right hk]
      simpa only [id_eq] using hν'
  calc
    modifiedCutoffReadout E w f (μ, ν) =
        ∫⁻ p, ‖f p‖ₑ ∂chainProduct
          (fun k => if k = 0 then μ else ν) (fun _ => w) 1 := by
      unfold modifiedCutoffReadout
      rw [hseq]
    _ = ∫⁻ p, ‖f p‖ₑ ∂smoothedProductMeasure μ w ν := by
      simp only [chainProduct]
      rfl

private theorem modifiedCutoffReadout_lt_top_iff_integrable
    (E : CompactExhaustion (Plane × Plane)) (w : Plane → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hwm : Measurable w) (f : C_c(Plane × Plane, ℝ))
    (μ ν : Measure (Plane × Plane)) (hμ : IsLocallyFiniteMeasure μ)
    (hν : IsLocallyFiniteMeasure ν) :
    modifiedCutoffReadout E w (f : Plane × Plane → ℝ) (μ, ν) < ⊤ ↔
      Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
        f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)) (μ.prod ν) := by
  rw [modifiedCutoffReadout_eq_smoothedProduct E w f μ ν hμ hν]
  constructor
  · intro hfinite
    have hfinite' : (∫⁻ p, ‖(f : Plane × Plane → ℝ) p‖ₑ ∂
        smoothedProductMeasure μ w ν) < ⊤ := hfinite
    have hInt : Integrable (f : Plane × Plane → ℝ) (smoothedProductMeasure μ w ν) := by
      refine ⟨f.continuous.measurable.aestronglyMeasurable, ?_⟩
      rwa [hasFiniteIntegral_iff_enorm]
    exact (integrable_smoothedProductMeasure_iff μ w ν hw hwm
      (f : Plane × Plane → ℝ) f.continuous.measurable).1 hInt
  · intro hInt
    have hInt' := (integrable_smoothedProductMeasure_iff μ w ν hw hwm
      (f : Plane × Plane → ℝ) f.continuous.measurable).2 hInt
    have hfi := hInt'.hasFiniteIntegral
    rwa [hasFiniteIntegral_iff_enorm] at hfi

/-- Equality of pair laws transfers almost-sure integrability of the smoothed product pairing. -/
theorem ae_integrable_product_of_pair_law {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    (E : CompactExhaustion (Plane × Plane)) (w : Plane → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hwm : Measurable w) (f : C_c(Plane × Plane, ℝ))
    (U V : Ω → Measure (Plane × Plane)) (U' V' : Ω' → Measure (Plane × Plane))
    (hU : Measurable U) (hV : Measurable V) (hU' : Measurable U') (hV' : Measurable V')
    (hLaw : P.map (fun ω => (U ω, V ω)) = P'.map (fun ω => (U' ω, V' ω)))
    (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (U ω) ∧ IsLocallyFiniteMeasure (V ω))
    (hLF' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (U' ω) ∧ IsLocallyFiniteMeasure (V' ω))
    (hInt : ∀ᵐ ω ∂P, Integrable
      (fun q : (Plane × Plane) × (Plane × Plane) =>
        f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)) ((U ω).prod (V ω))) :
    ∀ᵐ ω ∂P', Integrable
      (fun q : (Plane × Plane) × (Plane × Plane) =>
        f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)) ((U' ω).prod (V' ω)) := by
  let R := modifiedCutoffReadout E w (f : Plane × Plane → ℝ)
  have hR : Measurable R := measurable_modifiedCutoffReadout E w hwm f f.continuous.measurable
  have hsource : ∀ᵐ ω ∂P, R (U ω, V ω) < ⊤ := by
    filter_upwards [hLF, hInt] with ω hLFω hIntω
    exact (modifiedCutoffReadout_lt_top_iff_integrable E w hw hwm f (U ω) (V ω)
      hLFω.1 hLFω.2).2 hIntω
  have hsourceMap : ∀ᵐ q ∂P.map (fun ω => (U ω, V ω)), R q < ⊤ :=
    (ae_map_iff (μ := P) (f := fun ω => (U ω, V ω))
      (hU.prodMk hV).aemeasurable
      (measurableSet_lt hR measurable_const)).2 hsource
  have htargetMap : ∀ᵐ q ∂P'.map (fun ω => (U' ω, V' ω)), R q < ⊤ := by
    rw [← hLaw]
    exact hsourceMap
  have htarget : ∀ᵐ ω ∂P', R (U' ω, V' ω) < ⊤ :=
    (ae_map_iff (μ := P') (f := fun ω => (U' ω, V' ω))
      (hU'.prodMk hV').aemeasurable
      (measurableSet_lt hR measurable_const)).1 htargetMap
  filter_upwards [htarget, hLF'] with ω hRω hLFω
  exact (modifiedCutoffReadout_lt_top_iff_integrable E w hw hwm f (U' ω) (V' ω)
    hLFω.1 hLFω.2).1 hRω

/-- Equality of the joint laws of the two adjacent random measures and the measure on their combined interval transfers smoothed composition convergence, provided the smoothed pairings are almost surely absolutely integrable in both realizations. -/
theorem compositionLimit_of_fdd_eq_of_wellDefined {θ : ℝ} {D : Set ℝ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω))
    {a b c : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hab : a < b) (hbc : b < c)
    (w : ℕ → Plane → ℝ) (hw : IsL2ApplicableMollifier w)
    (hwell : ∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z a b ω) (w ℓ) (Z b c ω))
    (hconv : ∀ f : C_c(Plane × Plane, ℝ),
      TendstoInMeasure P (fun ℓ ω => smoothedProductPairing (Z a b ω) (w ℓ) (Z b c ω) f -
        ∫ p, f p ∂Z a c ω) atTop (fun _ => 0))
    (hwell' : ∀ ℓ, ∀ᵐ ω ∂P', SmoothedProductWellDefined (Z' a b ω) (w ℓ) (Z' b c ω))
    (hLF₀' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' a b ω))
    (hLF₁' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' b c ω))
    (hLF₂' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' a c ω)) :
    ∀ f : C_c(Plane × Plane, ℝ),
      TendstoInMeasure P' (fun ℓ ω => smoothedProductPairing (Z' a b ω) (w ℓ) (Z' b c ω) f -
        ∫ p, f p ∂Z' a c ω) atTop (fun _ => 0) := by
  intro f
  classical
  let s : Fin 3 → ℝ := ![a, b, a]
  let t : Fin 3 → ℝ := ![b, c, c]
  let X : Ω → Fin 3 → Measure (Plane × Plane) := fun ω i => Z (s i) (t i) ω
  let Y : Ω' → Fin 3 → Measure (Plane × Plane) := fun ω i => Z' (s i) (t i) ω
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> simp [X, s, t] <;>
      first | exact (hZ.1 a ha b hb hab).1 | exact (hZ.1 b hb c hc hbc).1 |
        exact (hZ.1 a ha c hc (hab.trans hbc)).1
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> simp [Y, s, t] <;>
      first | exact hmeas a ha b hb hab | exact hmeas b hb c hc hbc |
        exact hmeas a ha c hc (hab.trans hbc)
  have hLaw : P.map X = P'.map Y := by
    exact hfdd 3 s t (by
      intro i
      fin_cases i <;> simp [s, t] <;>
        first | exact ⟨ha, hb, hab⟩ | exact ⟨hb, hc, hbc⟩ |
          exact ⟨ha, hc, hab.trans hbc⟩)
  let E := CompactExhaustion.choice (Plane × Plane)
  let readout (μ : Measure (Plane × Plane)) : ℝ := ∫ p, f p ∂μ
  let κ : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
  have hreadout : Measurable readout := by
    dsimp only [readout]
    exact (((map_continuous f).measurable).stronglyMeasurable.integral_kernel
      (κ := κ)).measurable
  let v (ℓ : ℕ) (m : Fin 3 → Measure (Plane × Plane)) : ℝ :=
    modifiedTwoBlockReadout E (w ℓ) f (m 0, m 1) - readout (m 2)
  have hv (ℓ : ℕ) : Measurable (v ℓ) := by
    have hp : Measurable (fun m : Fin 3 → Measure (Plane × Plane) => (m 0, m 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have hpair := (measurable_modifiedTwoBlockReadout E (w ℓ)
      (hw.2.1 ℓ).measurable f f.continuous.measurable).comp hp
    exact hpair.sub (hreadout.comp (measurable_pi_apply 2))
  have hsourceEq (ℓ : ℕ) : (fun ω => v ℓ (X ω)) =ᵐ[P]
      fun ω => smoothedProductPairing (Z a b ω) (w ℓ) (Z b c ω) f -
        ∫ p, f p ∂Z a c ω := by
    filter_upwards [hwell ℓ, (hZ.1 a ha b hb hab).2, (hZ.1 b hb c hc hbc).2,
      (hZ.1 a ha c hc (hab.trans hbc)).2] with ω hwellω hLF₀ hLF₁ hLF₂
    let _ : IsLocallyFiniteMeasure (Z a b ω) := hLF₀
    let _ : IsLocallyFiniteMeasure (Z b c ω) := hLF₁
    let _ : IsLocallyFiniteMeasure (Z a c ω) := hLF₂
    change modifiedTwoBlockReadout E (w ℓ) f (Z a b ω, Z b c ω) - readout (Z a c ω) = _
    rw [modifiedTwoBlockReadout_eq_of_locallyFinite E (Z a b ω) (Z b c ω) (w ℓ) f,
      integral_smoothedProductMeasure (Z a b ω) (w ℓ) (Z b c ω)
        (hw.1 ℓ) (hw.2.1 ℓ).measurable f hwellω]
  have htargetEq (ℓ : ℕ) : (fun ω => v ℓ (Y ω)) =ᵐ[P']
      fun ω => smoothedProductPairing (Z' a b ω) (w ℓ) (Z' b c ω) f -
        ∫ p, f p ∂Z' a c ω := by
    filter_upwards [hwell' ℓ, hLF₀', hLF₁', hLF₂'] with ω hwellω hLF₀ hLF₁ hLF₂
    let _ : IsLocallyFiniteMeasure (Z' a b ω) := hLF₀
    let _ : IsLocallyFiniteMeasure (Z' b c ω) := hLF₁
    let _ : IsLocallyFiniteMeasure (Z' a c ω) := hLF₂
    change modifiedTwoBlockReadout E (w ℓ) f (Z' a b ω, Z' b c ω) - readout (Z' a c ω) = _
    rw [modifiedTwoBlockReadout_eq_of_locallyFinite E (Z' a b ω) (Z' b c ω) (w ℓ) f,
      integral_smoothedProductMeasure (Z' a b ω) (w ℓ) (Z' b c ω)
        (hw.1 ℓ) (hw.2.1 ℓ).measurable f hwellω]
  have hconvV : TendstoInMeasure P (fun ℓ ω => v ℓ (X ω)) atTop (fun _ => 0) := by
    exact (hconv f).congr_left (fun ℓ => (hsourceEq ℓ).symm)
  have hconvV' := tendstoInMeasure_comp_of_map_eq P P' X Y hX hY hLaw v hv
    (fun _ => 0) measurable_const hconvV
  exact hconvV'.congr_left (fun ℓ => htargetEq ℓ)

end Critical2DKPZ.SHF.Symmetries

end
