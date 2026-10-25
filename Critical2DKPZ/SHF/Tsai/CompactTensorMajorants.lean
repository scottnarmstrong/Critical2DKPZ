/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Positive tensor majorants on compact windows

Endpoint cutoffs equal one on the projections of a compact plane-pair window.
Their positive tensor controls every supported test and every uniform test
approximation error after integration against a locally finite measure.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- A compact plane-pair window admits a positive compact tensor equal to one on that window. -/
theorem exists_compactTensor_majorant (K : Set (Plane × Plane)) (hK : IsCompact K) :
    ∃ g g' : C_c(Plane, ℝ), (∀ x, 0 ≤ g x) ∧ (∀ x, 0 ≤ g' x) ∧
      ∀ p ∈ K, g p.1 * g' p.2 = 1 := by
  obtain ⟨g, hgone, hgc, _hgU, hg01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (hK.image continuous_fst) isOpen_univ (subset_univ _)
  obtain ⟨g', hg'one, hg'c, _hg'U, hg'01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (hK.image continuous_snd) isOpen_univ (subset_univ _)
  refine ⟨⟨g, hgc⟩, ⟨g', hg'c⟩, fun x => (hg01 x).1, fun x => (hg'01 x).1, ?_⟩
  intro p hp
  change g p.1 * g' p.2 = 1
  simpa only [Pi.one_apply, mul_one] using congrArg₂ (· * ·) (hgone ⟨p, hp, rfl⟩) (hg'one ⟨p, hp, rfl⟩)



end Critical2DKPZ.SHF.Tsai

end
