/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedEquiv
import Mathlib.Tactic

/-! # Joint free coordinates for the two sides of a collision run -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Moments

/-- Put the incoming and outgoing fused coordinates on separate summands
of a finite coordinate type. -/
def fusedPairSumMeasurableEquiv (ι X : Type*) [MeasurableSpace X] :
    ((X × (ι → X)) × (X × (ι → X))) ≃ᵐ ((Option ι ⊕ Option ι) → X) :=
  ((fusedOptionMeasurableEquiv ι X).prodCongr (fusedOptionMeasurableEquiv ι X)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Option ι ⊕ Option ι => X)).symm



/-- The disjoint-coordinate identification preserves product volume on the two collision spaces. -/
theorem measurePreserving_fusedPairSumMeasurableEquiv (ι X : Type*) [Fintype ι]
    [MeasureSpace X] [SigmaFinite (volume : Measure X)] :
    MeasurePreserving (fusedPairSumMeasurableEquiv ι X) := by
  exact (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Option ι ⊕ Option ι => X)).comp
      ((measurePreserving_fusedOptionMeasurableEquiv ι X).prod
        (measurePreserving_fusedOptionMeasurableEquiv ι X))

end Critical2DKPZ.SHF.Moments
