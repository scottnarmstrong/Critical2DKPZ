/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs

/-! # Diverging reindexings of applicable mollifiers

Each pointwise condition is inherited from the selected original index.
The approximation condition follows by composition with the diverging index
map; monotonicity of that map is unnecessary.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Every reindexing tending to infinity preserves `L²` applicability. -/
theorem IsL2ApplicableMollifier.comp_tendsto {w : ℕ → Plane → ℝ}
    (hw : IsL2ApplicableMollifier w) {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) :
    IsL2ApplicableMollifier (fun j => w (σ j)) := by
  refine ⟨fun j => hw.1 (σ j), fun j => hw.2.1 (σ j), fun j => hw.2.2.1 (σ j),
    fun j => hw.2.2.2.1 (σ j), ?_⟩
  intro φ hφ
  simpa only [Function.comp_def] using (hw.2.2.2.2 φ hφ).comp hσ

end Critical2DKPZ.SHF.Tsai

end
