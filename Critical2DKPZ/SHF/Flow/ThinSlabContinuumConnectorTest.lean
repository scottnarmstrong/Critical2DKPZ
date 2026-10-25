/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabConnectorSecondMoment
import Mathlib.Tactic

/-! # Continuum connector replica tests and their middle cutoffs -/

@[expose] public noncomputable section
open MeasureTheory Filter Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology
namespace Critical2DKPZ.SHF.Flow

/-- The explicit uncut two-block continuum replica test. -/
def slabConnectorReplicaValue (Φ : Plane × Plane → ℝ) (κ : Plane × Plane → ℝ)
    (z : Fin 2 → Configuration 2 × Configuration 2) : ℝ :=
  ∏ i : Fin 2, Φ ((z 0).1 i, (z 1).2 i) * κ ((z 0).2 i, (z 1).1 i)

/-- The four middle-coordinate cutoffs in the two-replica integral. -/
def slabConnectorMiddleCutoff (R : ℝ) (z : Fin 2 → Configuration 2 × Configuration 2) : ℝ :=
  ∏ i : Fin 2, ballCutoff R ((z 0).2 i) * ballCutoff R ((z 1).1 i)

/-- The replica value is continuous when the endpoint and connector tests are. -/
theorem continuous_slabConnectorReplicaValue {Φ κ : Plane × Plane → ℝ}
    (hΦ : Continuous Φ) (hκ : Continuous κ) : Continuous (slabConnectorReplicaValue Φ κ) := by
  unfold slabConnectorReplicaValue
  apply continuous_finsetProd
  intro i _
  exact (hΦ.comp (by fun_prop)).mul (hκ.comp (by fun_prop))

/-- Middle cutoff weights lie in the unit interval. -/
theorem slabConnectorMiddleCutoff_mem_Icc (R : ℝ) (z : Fin 2 → Configuration 2 × Configuration 2) :
    slabConnectorMiddleCutoff R z ∈ Set.Icc 0 1 := by
  have hterm (i : Fin 2) :
      ballCutoff R ((z 0).2 i) * ballCutoff R ((z 1).1 i) ∈ Set.Icc 0 1 := by
    have h₁ := ballCutoff_mem_Icc R ((z 0).2 i)
    have h₂ := ballCutoff_mem_Icc R ((z 1).1 i)
    exact ⟨mul_nonneg h₁.1 h₂.1, by
      simpa only [mul_one] using mul_le_mul h₁.2 h₂.2 h₂.1 zero_le_one⟩
  constructor
  · exact Finset.prod_nonneg fun i _ => (hterm i).1
  · exact Finset.prod_le_one₀ (fun i _ => (hterm i).1) (fun i _ => (hterm i).2)

/-- Each fixed middle configuration eventually lies inside all cutoffs. -/
theorem eventually_slabConnectorMiddleCutoff_eq_one (z : Fin 2 → Configuration 2 × Configuration 2) :
    ∀ᶠ R : ℝ in atTop, slabConnectorMiddleCutoff R z = 1 := by
  have h₁ : ∀ᶠ R : ℝ in atTop, ∀ i : Fin 2, ballCutoff R ((z 0).2 i) = 1 :=
    Filter.eventually_all.mpr fun i => eventually_ballCutoff_eq_one _
  have h₂ : ∀ᶠ R : ℝ in atTop, ∀ i : Fin 2, ballCutoff R ((z 1).1 i) = 1 :=
    Filter.eventually_all.mpr fun i => eventually_ballCutoff_eq_one _
  filter_upwards [h₁, h₂] with R hR₁ hR₂
  unfold slabConnectorMiddleCutoff
  exact Finset.prod_eq_one fun i _ => by rw [hR₁ i, hR₂ i, one_mul]

/-- The compact replica test is exactly the uncut value times the middle cutoff weight. -/
theorem slabSeparatedGroupedTest_cutoffConnector (Φ : C_c(Plane × Plane, ℝ))
    (κ : C(Plane × Plane, ℝ)) (R : ℝ) (z : Fin 2 → Configuration 2 × Configuration 2) :
    slabSeparatedGroupedTest (slabReplicaSourceTest (slabCutoffConnectorTest Φ κ R)) z =
      slabConnectorReplicaValue Φ κ z * slabConnectorMiddleCutoff R z := by
  simp only [slabSeparatedGroupedTest_apply, slabReplicaSourceTest, slabReplicaTensorTest,
    slabReplicaArrayHomeomorph, slabReplicaArrayEquiv, slabSeparatedArrayHomeomorph,
    slabSeparatedArrayEquiv, slabCutoffConnectorTest, slabConnectorReplicaValue,
    slabConnectorMiddleCutoff, Fin.prod_univ_two]
  dsimp
  change (Φ ((z 0).1 0, (z 1).2 0) * κ ((z 0).2 0, (z 1).1 0) *
      ballCutoff R ((z 0).2 0) * ballCutoff R ((z 1).1 0)) *
    (Φ ((z 0).1 1, (z 1).2 1) * κ ((z 0).2 1, (z 1).1 1) *
      ballCutoff R ((z 0).2 1) * ballCutoff R ((z 1).1 1)) = _
  ring

end Critical2DKPZ.SHF.Flow
end
