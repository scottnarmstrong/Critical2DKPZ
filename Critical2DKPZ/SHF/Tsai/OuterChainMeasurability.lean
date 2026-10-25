/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SplitCopyBlocks
public import Critical2DKPZ.SHF.Tsai.ChainPairingMeasurability

/-! # Measurability after replacing one chain block

Replacing one block by a measurable locally finite measure-valued map preserves measurability
of the chain pairing when the other blocks depend measurably on the remaining coordinates.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Replacing one block by a measurable locally finite measure-valued map gives measurable chain pairings. -/
theorem measurable_integral_outerCopyChain_update {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] (K : ℕ) (j : Fin (K + 1))
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    (a : A → Fin K → Ω) (ha : Measurable a)
    (Z : A → Measure (Plane × Plane)) (hZ : Measurable Z)
    (hZlf : ∀ x, IsLocallyFiniteMeasure (Z x))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k))
    (F : Plane × Plane → ℝ) (hF : Measurable F) :
    Measurable (fun x => ∫ p, F p ∂chainProduct
      (Function.update (outerCopyBlock K j B (a x)) j (Z x)) w K) := by
  classical
  let C (k : ℕ) (x : A) := Function.update (outerCopyBlock K j B (a x)) j (Z x) k
  have hCm (k) (hk : k ≤ K) : Measurable (C k) := by
    by_cases hkj : k = (j : ℕ)
    · subst k
      simpa only [C, Function.update_self] using hZ
    · simpa only [C, Function.update_of_ne hkj, Function.comp_def] using
        (measurable_outerCopyBlock K j B hB k hk).comp ha
  have hClf (x : A) (k) (_hk : k ≤ K) : IsLocallyFiniteMeasure (C k x) := by
    by_cases hkj : k = (j : ℕ)
    · subst k
      simpa only [C, Function.update_self] using hZlf x
    · simpa only [C, Function.update_of_ne hkj] using locallyFinite_outerCopyBlock K j B hlf (a x) k
  exact measurable_integral_chainProduct K C hCm hClf w hw F hF

end Critical2DKPZ.SHF.Tsai

end
