/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Increasing positive products of random-measure pairings

All factors use a common increasing approximation index. Positivity permits
moving the supremum through the finite product and the two positive integrals,
even when the limiting moment is infinite.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Increasing positive factors commute with the diagonal supremum. -/
theorem iSup_mul_of_monotone {f g : ℕ → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ N, f N) * (⨆ N, g N) = ⨆ N, f N * g N := by
  apply le_antisymm
  · rw [ENNReal.iSup_mul]
    apply iSup_le
    intro i
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro j
    exact (mul_le_mul' (hf (le_max_left i j)) (hg (le_max_right i j))).trans
      (le_iSup (fun N => f N * g N) (max i j))
  · exact iSup_le fun N => mul_le_mul' (le_iSup f N) (le_iSup g N)

/-- A finite product of increasing positive sequences commutes with their common supremum. -/
theorem iSup_finset_prod_of_monotone {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ≥0∞)
    (hf : ∀ i, Monotone (f i)) :
    (⨆ N, ∏ i ∈ s, f i N) = ∏ i ∈ s, ⨆ N, f i N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, iSup_const]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    rw [← ih, iSup_mul_of_monotone (hf i)
      (fun N M hNM => Finset.prod_le_prod fun j _ => hf j hNM)]

/-- Monotone convergence for a finite product of random-measure pairings. -/
theorem lintegral_prod_lintegral_iSup {α Ω ι : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) (B : Ω → Measure α) (hB : Measurable B)
    (F : ι → ℕ → α → ℝ≥0∞) (hFm : ∀ i N, Measurable (F i N)) (hF : ∀ i, Monotone (F i)) :
    (∫⁻ ω, ∏ i, (∫⁻ x, (⨆ N, F i N x) ∂B ω) ∂P) =
      ⨆ N, ∫⁻ ω, ∏ i, (∫⁻ x, F i N x ∂B ω) ∂P := by
  have hinner (i : ι) (ω : Ω) :
      (∫⁻ x, (⨆ N, F i N x) ∂B ω) = ⨆ N, ∫⁻ x, F i N x ∂B ω :=
    lintegral_iSup (hFm i) (hF i)
  have hmono (i : ι) (ω : Ω) : Monotone (fun N => ∫⁻ x, F i N x ∂B ω) :=
    fun N M hNM => lintegral_mono (hF i hNM)
  simp_rw [hinner, ← iSup_finset_prod_of_monotone Finset.univ _ (fun i => hmono i _)]
  apply lintegral_iSup
  · intro N
    apply Finset.measurable_prod
    intro i _
    exact (Measure.measurable_lintegral (hFm i N)).comp hB
  · intro N M hNM ω
    exact Finset.prod_le_prod fun i _ => hmono i ω hNM

end Critical2DKPZ.SHF.Tsai

end
