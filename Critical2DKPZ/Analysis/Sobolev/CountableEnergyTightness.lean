/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Tightness from countably many expected energies with compact joint sublevels -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Analysis.Sobolev

/-- Markov's inequality and a countable union bound give tightness when finite simultaneous
energy bounds define compact sets. The constants may depend on the energy coordinate. -/
theorem isTightMeasureSet_of_expected_countable_energies
    {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E] [Countable ι]
    (μ : ℕ → Measure E) (F : ι → E → ℝ≥0∞) (hF : ∀ i, Measurable (F i))
    (hcompact : ∀ K : ι → ℝ≥0∞, (∀ i, K i ≠ ⊤) →
      IsCompact {x | ∀ i, F i x ≤ K i})
    (hE : ∀ i, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n, ∫⁻ x, F i x ∂μ n ≤ M) :
    IsTightMeasureSet (Set.range μ) := by
  classical
  choose M hM hbound using hE
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ :=
    ENNReal.exists_pos_tsum_mul_lt_of_countable hε.ne' M hM
  let K : ι → ℝ≥0∞ := fun i => (δ i : ℝ≥0∞)⁻¹
  have hK : ∀ i, K i ≠ ⊤ := fun i =>
    ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr (hδ i).ne')
  refine ⟨{x | ∀ i, F i x ≤ K i}, hcompact K hK, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hbad : {x | ∀ i, F i x ≤ K i}ᶜ = ⋃ i, {x | K i < F i x} := by
    ext x
    simp
  rw [hbad]
  apply (measure_iUnion_le _).trans
  apply (ENNReal.tsum_le_tsum ?_).trans hsum.le
  intro i
  calc
    μ n {x | K i < F i x} ≤ μ n {x | K i ≤ F i x} :=
      measure_mono (fun x hx => (show K i < F i x from hx).le)
    _ ≤ (∫⁻ x, F i x ∂μ n) / K i :=
      meas_ge_le_lintegral_div (hF i).aemeasurable
        (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top) (hK i)
    _ ≤ M i / K i := ENNReal.div_le_div_right (hbound i n) _
    _ = M i * (δ i : ℝ≥0∞) := by simp [K, div_eq_mul_inv]

end Critical2DKPZ.Analysis.Sobolev

end
