/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # A finite window cover for short increments -/

public section

namespace Critical2DKPZ.Extensions.ScaleLimit

open MeasureTheory

/-- A short ordered increment is contained in an overlapping window of length
twice the mesh size. The endpoint at the horizon is included. -/
theorem short_increment_mesh_cover {h s t : ℝ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hs : 0 ≤ s) (ht : t ≤ (m : ℝ) * h) (hshort : t - s ≤ h) :
    ∃ k : ℕ, k < m ∧ (k : ℝ) * h ≤ s ∧ t ≤ ((k : ℝ) + 2) * h := by
  let j := ⌊s / h⌋₊
  let k := min j (m - 1)
  have hkm : k < m := by dsimp [k]; omega
  have hkj : (k : ℝ) ≤ j := by exact_mod_cast (min_le_left j (m - 1))
  have hjlow : (j : ℝ) * h ≤ s :=
    (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hs hh.le))
  refine ⟨k, hkm, (mul_le_mul_of_nonneg_right hkj hh.le).trans hjlow, ?_⟩
  by_cases hjm : j < m
  · have hkeq : k = j := by dsimp [k]; omega
    have hjhi : s < ((j : ℝ) + 1) * h :=
      (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (s / h))
    rw [hkeq]
    linarith only [hjhi, hshort]
  · have hkeq : k + 1 = m := by dsimp [k]; omega
    have hcast : (k : ℝ) + 1 = m := by exact_mod_cast hkeq
    nlinarith only [ht, hh, hcast]

/-- The short-increment event is contained in the finite union of overlapping
window events. No measurability or continuity is needed for this containment. -/
theorem short_increment_event_subset {Ω : Type*} (X : ℝ → Ω → ℝ)
    {h : ℝ} {m : ℕ} (hh : 0 < h) (hm : 0 < m) (η : ℝ) :
    {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ (m : ℝ) * h ∧ t - s ≤ h ∧
      η < |X t ω - X s ω|} ⊆
    ⋃ k ∈ Finset.range m, {ω | ∃ s t : ℝ,
      (k : ℝ) * h ≤ s ∧ s ≤ t ∧ t ≤ ((k : ℝ) + 2) * h ∧ η < |X t ω - X s ω|} := by
  rintro ω ⟨s, t, hs, hst, ht, hshort, hX⟩
  obtain ⟨k, hkm, hks, htk⟩ := short_increment_mesh_cover hh hm hs ht hshort
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
    ⟨Finset.mem_range.mpr hkm, s, t, hks, hst, htk, hX⟩⟩

/-- The finite-window union bound is valid for outer measures, without an
extra measurability assumption on the uncountable oscillation events. -/
theorem short_increment_measure_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → ℝ) {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : 0 < m) (η : ℝ) :
    P {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ (m : ℝ) * h ∧ t - s ≤ h ∧
      η < |X t ω - X s ω|} ≤
      ∑ k ∈ Finset.range m, P {ω | ∃ s t : ℝ,
        (k : ℝ) * h ≤ s ∧ s ≤ t ∧ t ≤ ((k : ℝ) + 2) * h ∧ η < |X t ω - X s ω|} :=
  (measure_mono (short_increment_event_subset X hh hm η)).trans
    (measure_biUnion_finset_le (Finset.range m) _)

end Critical2DKPZ.Extensions.ScaleLimit
