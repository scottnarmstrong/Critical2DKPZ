/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Scalar moments of dense-time flow pairings

The moment axiom includes integrability. Repeating one pair of spatial tests
extracts each scalar power moment and places the pairing in `L⁴`. These facts
justify the binomial and Taylor manipulations in the uniqueness argument.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

variable {θ : ℝ} {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}

/-- Each scalar power through order four is integrable. -/
theorem isDenseSHF_integrable_pairing_pow (hZ : IsDenseSHF θ D P Z)
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    {g g' : Plane → ℝ} (hg : MemLp g 2) (hg' : MemLp g' 2)
    {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 4) :
    Integrable (fun ω => (∫ p, g p.1 * g' p.2 ∂Z s t ω) ^ n) P := by
  have h := (hZ.2.2.2 n hn hn' s hs t ht hst
    (fun _ => g) (fun _ => g') (fun _ => hg) (fun _ => hg')).2.1
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h


/-- The scalar pairing has a genuine finite fourth moment. -/
theorem isDenseSHF_memLp_pairing_four (hZ : IsDenseSHF θ D P Z)
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    {g g' : Plane → ℝ} (hg : MemLp g 2) (hg' : MemLp g' 2) :
    MemLp (fun ω => ∫ p, g p.1 * g' p.2 ∂Z s t ω) 4 P := by
  have h1 := isDenseSHF_integrable_pairing_pow hZ hs ht hst hg hg'
    (n := 1) (by omega) (by omega)
  simp only [pow_one] at h1
  have h4 := isDenseSHF_integrable_pairing_pow hZ hs ht hst hg hg'
    (n := 4) (by omega) (by omega)
  apply (integrable_norm_rpow_iff h1.aestronglyMeasurable
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).1
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs,
    Even.pow_abs (show Even 4 from ⟨2, rfl⟩)] using h4

end Critical2DKPZ.SHF.Tsai

end
