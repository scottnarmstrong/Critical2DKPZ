/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.PairingSlabComparisonHeatTest

/-! # Replica identity for a cut-off slab connector -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- The cut-off finite-slab connector pairing has the four-replica integral as its square.
Continuity of the step-valued slab kernel is not required. -/
theorem integral_slabCutoffReplicaValue_eq_sq {μ ν : Measure (Plane × Plane)}
    [SigmaFinite μ] [SigmaFinite ν] (ϑ : ℝ) (N : ℕ) (t v R : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) :
    (∫ q : Fin 4 → Plane × Plane,
      slabCutoffReplicaValue ϑ N t v R Φ q ∂
        slabTwoBlockPiMeasure μ ν) =
      (∫ p, slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2 ∂(μ.prod ν)) ^ 2 := by
  have h := integral_slabReplicaFunction_sq
    (X := Plane × Plane) (μ := μ) (ν := ν)
    (fun p : (Plane × Plane) × (Plane × Plane) =>
      slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2)
  have hpoint (q : Fin 4 → Plane × Plane) :
      slabCutoffReplicaValue ϑ N t v R Φ q =
        (fun p : (Plane × Plane) × (Plane × Plane) =>
          slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2) (q 0, q 2) *
        (fun p : (Plane × Plane) × (Plane × Plane) =>
          slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2) (q 1, q 3) := rfl
  rw [show (∫ q : Fin 4 → Plane × Plane,
      slabCutoffReplicaValue ϑ N t v R Φ q ∂slabTwoBlockPiMeasure μ ν) =
      ∫ q : Fin 4 → Plane × Plane,
        (fun p : (Plane × Plane) × (Plane × Plane) =>
          slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2) (q 0, q 2) *
        (fun p : (Plane × Plane) × (Plane × Plane) =>
          slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2) (q 1, q 3)
          ∂slabTwoBlockPiMeasure μ ν from by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint]
  simpa only [slabTwoBlockPiMeasure] using h

/-- The explicit cut-off integral is the cut-off connector pairing by unfolding its definition. -/
theorem integral_slabCutoffConnectorValue_eq_cutoffPairing
    (μ ν : Measure (Plane × Plane)) (ϑ : ℝ) (N : ℕ) (t v R : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) :
    (∫ p, slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2 ∂(μ.prod ν)) =
      ∫ q, Φ (q.1.1, q.2.2) * slabMeanKernel ϑ N t (t + v) q.1.2 q.2.1 *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν) := by
  rfl

end Critical2DKPZ.SHF.Flow

end
