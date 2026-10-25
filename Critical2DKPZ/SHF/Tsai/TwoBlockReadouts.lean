/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainReadoutLaws

/-! # Measurable pairings of two-block products

Locally finite modifications give a measurable pairing map on all pairs of endpoint
measures, agreeing with the smoothed product pairing on locally finite inputs.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- The two-block product pairing after locally finite modification, defined for all pairs of endpoint measures. -/
def modifiedTwoBlockReadout (E : CompactExhaustion (Plane × Plane))
    (w : Plane → ℝ) (F : Plane × Plane → ℝ)
    (q : Measure (Plane × Plane) × Measure (Plane × Plane)) : ℝ :=
  modifiedChainReadout E 1 (fun _ => w) F ![q.1, q.2]

/-- Measurable tests and connectors give a measurable two-block product pairing. -/
theorem measurable_modifiedTwoBlockReadout (E : CompactExhaustion (Plane × Plane))
    (w : Plane → ℝ) (hw : Measurable w) (F : Plane × Plane → ℝ) (hF : Measurable F) :
    Measurable (modifiedTwoBlockReadout E w F) := by
  have htuple : Measurable (fun q : Measure (Plane × Plane) × Measure (Plane × Plane) =>
      (![q.1, q.2] : Fin 2 → Measure (Plane × Plane))) := by
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd
  exact (measurable_modifiedChainReadout E 1 (fun _ => w) (fun _ => hw) F hF).comp htuple

/-- On locally finite inputs the modified pairing equals the integral against the smoothed endpoint product. -/
theorem modifiedTwoBlockReadout_eq_of_locallyFinite (E : CompactExhaustion (Plane × Plane))
    (μ ν : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (w : Plane → ℝ) (F : Plane × Plane → ℝ) :
    modifiedTwoBlockReadout E w F (μ, ν) = ∫ p, F p ∂smoothedProductMeasure μ w ν := by
  let B (k : ℕ) := if k = 0 then μ else ν
  have hB (k : ℕ) (_hk : k ≤ 1) : IsLocallyFiniteMeasure (B k) := by
    by_cases hk : k = 0
    · simpa only [B, ite_eq_left hk] using (inferInstance : IsLocallyFiniteMeasure μ)
    · simpa only [B, ite_eq_right hk] using (inferInstance : IsLocallyFiniteMeasure ν)
  have hfin : (![μ, ν] : Fin 2 → Measure (Plane × Plane)) = fun (k : Fin 2) => B k := by
    funext k
    fin_cases k <;> rfl
  change modifiedChainReadout E 1 (fun _ => w) F ![μ, ν] = _
  rw [hfin, modifiedChainReadout_eq_of_locallyFinite E 1 B hB]
  rfl

/-- Measurable almost surely locally finite inputs give an almost everywhere measurable smoothed product pairing. -/
theorem aemeasurable_integral_smoothedProduct {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Ω → Measure (Plane × Plane))
    (hA : Measurable A) (hB : Measurable B)
    (hAlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (A ω))
    (hBlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω))
    (w : Plane → ℝ) (hw : Measurable w) (F : Plane × Plane → ℝ) (hF : Measurable F) :
    AEMeasurable (fun ω => ∫ p, F p ∂smoothedProductMeasure (A ω) w (B ω)) P := by
  let E := CompactExhaustion.choice (Plane × Plane)
  apply ((measurable_modifiedTwoBlockReadout E w hw F hF).comp (hA.prodMk hB)).aemeasurable.congr
  filter_upwards [hAlf, hBlf] with ω hωA hωB
  let : IsLocallyFiniteMeasure (A ω) := hωA
  let : IsLocallyFiniteMeasure (B ω) := hωB
  exact modifiedTwoBlockReadout_eq_of_locallyFinite E (A ω) (B ω) w F

end Critical2DKPZ.SHF.Tsai

end
