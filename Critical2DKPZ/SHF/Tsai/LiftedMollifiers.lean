/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MollifierOperators
public import Critical2DKPZ.SHF.Tsai.FiberwiseL2Limits
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Applying planar mollifiers to one coordinate of a product space

Almost every planar fiber of a product-space `L²` function is in `L²`.
The uniform mollifier bound controls its squared approximation error by one
integrable fiber norm. Dominated convergence then gives the product-space
approximation, retaining the actual scalar convolution integral.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Convolve the planar coordinate while holding the second coordinate fixed. -/
def leftMollifierAction {Y : Type*} (w : Plane → ℝ) (F : Plane × Y → ℝ) (q : Plane × Y) : ℝ :=
  ∫ y, w (q.1 - y) * F (y, q.2)

/-- Mollification in the first coordinate preserves joint measurability. -/
theorem measurable_leftMollifierAction {Y : Type*} [MeasurableSpace Y]
    {w : Plane → ℝ} (hw : Measurable w) {F : Plane × Y → ℝ} (hF : Measurable F) :
    Measurable (leftMollifierAction w F) := by
  have hm : Measurable (fun q : (Plane × Y) × Plane => w (q.1.1 - q.2) * F (q.2, q.1.2)) :=
    (hw.comp (measurable_fst.fst.sub measurable_snd)).mul
      (hF.comp (measurable_snd.prodMk measurable_fst.snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable


/-- A planar convolution norm bound lifts to the product without changing its constant. -/
theorem eLpNorm_leftMollifierAction_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : Plane → ℝ} (hwm : Measurable w) {M : ℝ≥0∞}
    (hM : ∀ (φ : Plane → ℝ), MemLp φ 2 → eLpNorm (mollifierAction w φ) 2 ≤ M * eLpNorm φ 2)
    {F : Plane × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (volume.prod μ)) :
    eLpNorm (leftMollifierAction w F) 2 (volume.prod μ) ≤ M * eLpNorm F 2 (volume.prod μ) := by
  exact eLpNorm_fiberAction_le volume μ (mollifierAction w) hM hFm hF
    (measurable_leftMollifierAction hwm hFm)

/-- Planar approximation on fibers gives actual `L²` convolutions and approximation on the product. -/
theorem leftMollifierAction_memLp_and_tendsto {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w)
    {F : Plane × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (volume.prod μ)) :
    (∀ j, MemLp (leftMollifierAction (w j) F) 2 (volume.prod μ)) ∧
    Tendsto (fun j => eLpNorm (fun q => leftMollifierAction (w j) F q - F q) 2 (volume.prod μ))
      atTop (𝓝 0) := by
  obtain ⟨M, hMfin, hM⟩ := exists_mollifierAction_uniform_bound hw
  exact fiberAction_memLp_and_tendsto volume μ (fun j => mollifierAction (w j)) hMfin hM
    (fun φ _ hφ => hw.2.2.2.2 φ hφ) hFm hF
    (fun j => measurable_leftMollifierAction (hw.2.1 j).measurable hFm)

end Critical2DKPZ.SHF.Tsai

end
