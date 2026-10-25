/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Compact tensor tests and dense endpoint approximations

Products of compactly supported continuous endpoint functions give compact
continuous tests on the plane pair. Every spatial `L²` representative is the
`L²` limit of such endpoint tests.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The compactly supported tensor of two spatial endpoint tests. -/
def compactTensorTest (g g' : C_c(Plane, ℝ)) : C_c(Plane × Plane, ℝ) where
  toFun p := g p.1 * g' p.2
  continuous_toFun := (g.continuous.comp continuous_fst).mul
    (g'.continuous.comp continuous_snd)
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (g.hasCompactSupport.prod g'.hasCompactSupport)
    intro p hp
    have hne : g p.1 * g' p.2 ≠ 0 := hp
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hne),
      subset_tsupport _ (right_ne_zero_of_mul hne)⟩

/-- The tensor test has the intended pointwise value. -/
theorem compactTensorTest_apply (g g' : C_c(Plane, ℝ)) (p : Plane × Plane) :
    compactTensorTest g g' p = g p.1 * g' p.2 := rfl

/-- Compact continuous tests approximate every actual `L²` representative in seminorm. -/
theorem exists_compactTest_tendsto_eLpNorm_sub (g : Plane → ℝ) (hg : MemLp g 2) :
    ∃ f : ℕ → C_c(Plane, ℝ), (∀ j, MemLp (f j) 2) ∧
      Tendsto (fun j => eLpNorm (g - (f j : Plane → ℝ)) 2) atTop (𝓝 0) := by
  have happrox (j : ℕ) := hg.exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (ε := ENNReal.ofReal (1 / ((j : ℝ) + 1)))
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  choose f hfcompact hfbound hfcont hfmem using happrox
  refine ⟨fun j => ⟨⟨f j, hfcont j⟩, hfcompact j⟩, hfmem, ?_⟩
  have ht : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hENN : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hENN
    (fun _ => zero_le) hfbound

end Critical2DKPZ.SHF.Tsai

end
