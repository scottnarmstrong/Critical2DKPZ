/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabAdjacentMomentLimit
public import Critical2DKPZ.SHF.Flow.PairingSlabReplicaCoordinates

/-! Compactly cut off connector pairings admit second-moment limits. -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open Critical2DKPZ.SHF.Limit
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- A compact continuous-connector test with cutoffs in the two middle coordinates. -/
def slabCutoffConnectorTest (Φ : C_c(Plane × Plane, ℝ)) (κ : C(Plane × Plane, ℝ)) (R : ℝ) :
    C_c(((Plane × Plane) × (Plane × Plane)), ℝ) := by
  let χ : C_c(Plane, ℝ) := ⟨⟨ballCutoff R, continuous_ballCutoff R⟩,
    hasCompactSupport_ballCutoff R⟩
  let f (q : (Plane × Plane) × (Plane × Plane)) : ℝ :=
    Φ (q.1.1, q.2.2) * κ (q.1.2, q.2.1) * χ q.1.2 * χ q.2.1
  have hf : Continuous f := by
    dsimp [f]
    have hEndpoint : Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
        (q.1.1, q.2.2)) := by fun_prop
    have hConnector : Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
        κ (q.1.2, q.2.1)) := by fun_prop
    have hCutLeft : Continuous (fun q : (Plane × Plane) × (Plane × Plane) => χ q.1.2) :=
      χ.continuous.comp (continuous_snd.comp continuous_fst)
    have hCutRight : Continuous (fun q : (Plane × Plane) × (Plane × Plane) => χ q.2.1) :=
      χ.continuous.comp (continuous_fst.comp continuous_snd)
    exact (Φ.continuous.comp hEndpoint).mul hConnector |>.mul hCutLeft |>.mul hCutRight
  let A : Set Plane := Prod.fst '' tsupport (Φ : (Plane × Plane) → ℝ)
  let B : Set Plane := Prod.snd '' tsupport (Φ : (Plane × Plane) → ℝ)
  let C : Set Plane := tsupport (χ : Plane → ℝ)
  let K : Set ((Plane × Plane) × (Plane × Plane)) :=
    (A ×ˢ C) ×ˢ (C ×ˢ B)
  have hA : IsCompact A := Φ.hasCompactSupport.image continuous_fst
  have hB : IsCompact B := Φ.hasCompactSupport.image continuous_snd
  have hC : IsCompact C := χ.hasCompactSupport
  have hK : IsCompact K := (hA.prod hC).prod (hC.prod hB)
  refine ⟨⟨f, hf⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro q hq
  have hΦ : Φ (q.1.1, q.2.2) ≠ 0 := by
    intro hz
    apply hq
    simp [f, hz]
  have hχ₁ : χ q.1.2 ≠ 0 := by
    intro hz
    apply hq
    simp [f, hz]
  have hχ₂ : χ q.2.1 ≠ 0 := by
    intro hz
    apply hq
    simp [f, hz]
  change (q.1.1 ∈ A ∧ q.1.2 ∈ C) ∧ (q.2.1 ∈ C ∧ q.2.2 ∈ B)
  exact ⟨⟨⟨(q.1.1, q.2.2), subset_tsupport _ hΦ, rfl⟩,
      subset_tsupport _ hχ₁⟩,
    ⟨subset_tsupport _ hχ₂,
      ⟨(q.1.1, q.2.2), subset_tsupport _ hΦ, rfl⟩⟩⟩




end Critical2DKPZ.SHF.Flow

end
