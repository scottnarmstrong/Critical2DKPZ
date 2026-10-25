/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.Basic
public import Critical2DKPZ.Blocks.Expansion
import Mathlib.Tactic

/-! # Deterministic identities for future-profile estimates -/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks

/-- Scaling a finitely supported profile scales its future energy quadratically. -/
theorem futureEnergy_smul (β : ℝ) (a b : ℕ) (c : ℝ) (η : Site → ℝ) (A : Finset Site)
    (hη : ∀ w ∉ A, η w = 0) :
    futureEnergy β a b (c • η) = c ^ 2 * futureEnergy β a b η := by
  have hprofile (ω : Disorder) :
      profileP2Fun β a b (c • η) (fun _ => 1) ω =
        c * profileP2Fun β a b η (fun _ => 1) ω := by
    rw [Polymer.profileP2Fun_eq_sum β a b (c • η) (fun _ => 1) A
      (by intro w hw; simp [hη w hw]),
      Polymer.profileP2Fun_eq_sum β a b η (fun _ => 1) A hη]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  unfold futureEnergy
  calc
    _ = ∫ ω, (c * profileP2Fun β a b η (fun _ => 1) ω) ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [hprofile ω]
    _ = ∫ ω, c ^ 2 * profileP2Fun β a b η (fun _ => 1) ω ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = c ^ 2 * futureEnergy β a b η := by
      rw [integral_const_mul]
      rfl

/-- The common correction splits at an intermediate block index. -/
theorem commonCorrection_sub_eq (β : ℝ) (t : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b)
    (ω : Disorder) (y : Site) :
    commonCorrection β t 1 b ω y - commonCorrection β t (a + 1) b ω y =
      ∑ u ∈ Finset.Icc 1 a, openCorrector β t u b ω y := by
  unfold commonCorrection
  have hpartition : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Icc (a + 1) b := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint : Disjoint (Finset.Icc 1 a) (Finset.Icc (a + 1) b) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    simp only [Finset.mem_Icc] at hu hv
    omega
  rw [hpartition, Finset.sum_union hdisjoint]
  ring

end Critical2DKPZ.FutureProfiles

end
