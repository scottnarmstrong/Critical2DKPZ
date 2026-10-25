/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryLaw

/-! # Lipschitz maps preserve convergence in probability -/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Composition by a Lipschitz real function preserves convergence in measure. -/
theorem tendstoInMeasure_lipschitz_comp {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter ι} {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hfg : TendstoInMeasure P f l g) {H : ℝ → ℝ} {c : ℝ≥0}
    (hH : LipschitzWith c H) (hc : 0 < c) :
    TendstoInMeasure P (fun i ω => H (f i ω)) l (fun ω => H (g ω)) := by
  rw [tendstoInMeasure_iff_dist] at hfg ⊢
  intro ε hε
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hh := hfg (ε / c) (div_pos hε hcR)
  rw [ENNReal.tendsto_nhds_zero] at hh ⊢
  intro a ha
  filter_upwards [hh a ha] with i hi
  apply le_trans _ hi
  apply measure_mono
  intro ω hω
  apply (div_le_iff₀ hcR).mpr
  exact (hω.trans (hH.dist_le_mul (f i ω) (g ω))).trans_eq (mul_comm _ _)

end Critical2DKPZ.Extensions.ScaleLimit
