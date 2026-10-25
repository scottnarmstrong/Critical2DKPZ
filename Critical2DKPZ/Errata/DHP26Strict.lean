/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Lattice gap envelopes and diffusion clocks -/

public section

open scoped ENNReal

namespace Critical2DKPZ.Errata.DHP26

/-- These lattice sites specify a configuration for testing the gap envelope. -/
abbrev LatticePoint := ℤ × ℤ

/-- These four-walk states specify a configuration for testing the gap envelope. -/
abbrev FourWalkState := Fin 4 → LatticePoint

/-- The gap for the concrete pair partition `{{1,2},{3},{4}}` in the
source's convention (smaller index first). -/
def pair12Gap (x : FourWalkState) : LatticePoint := x 0 - x 1

/-- Euclidean norm on the lattice gap, viewed as a real number. -/
noncomputable def latticeNorm (x : LatticePoint) : ℝ :=
  Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)

/-- The source's logarithmic cutoff, `|log x| 1_{x<1}`. -/
noncomputable def logMinus (x : ℝ) : ℝ := if x < 1 then |Real.log x| else 0

/-- The exact lattice slice mass in the `u.b.` estimate, for the concrete
pair above. The outer `tsum` is restricted to `0 ≤ r ≤ t`, and the inner one
to the states whose pair gap is `y`. -/
noncomputable def sourceGapSliceMass
    (p : ℕ → ℕ → FourWalkState → FourWalkState → ℝ≥0∞)
    (N t : ℕ) (a : FourWalkState) (y : LatticePoint) : ℝ≥0∞ :=
  ∑' r : ℕ, if r ≤ t then
    ∑' b : FourWalkState, if pair12Gap b = y then p N r a b else 0
    else 0

/-- The zero-time identity kernel contributes mass one to the gap slice
through the diagonal state, whenever `y` is the starting gap. -/
private theorem sourceGapSliceMass_ge_one
    (p : ℕ → ℕ → FourWalkState → FourWalkState → ℝ≥0∞)
    (hp0 : ∀ N a b, p N 0 a b = if a = b then 1 else 0)
    (N : ℕ) (a : FourWalkState) (y : LatticePoint)
    (hy : pair12Gap a = y) :
    1 ≤ sourceGapSliceMass p N 1 a y := by
  have hb : 1 ≤ ∑' b : FourWalkState,
      if pair12Gap b = y then p N 0 a b else 0 := by
    calc
      1 = (if pair12Gap a = y then p N 0 a a else 0) := by simp [hy, hp0]
      _ ≤ ∑' b : FourWalkState,
          if pair12Gap b = y then p N 0 a b else 0 :=
            ENNReal.le_tsum (f := fun b : FourWalkState =>
              if pair12Gap b = y then p N 0 a b else 0) a
  unfold sourceGapSliceMass
  calc
    1 ≤ (if (0 : ℕ) ≤ 1 then
          ∑' b : FourWalkState,
            if pair12Gap b = y then p N 0 a b else 0 else 0) := by simpa using hb
    _ ≤ ∑' r : ℕ, if r ≤ 1 then
          ∑' b : FourWalkState,
            if pair12Gap b = y then p N r a b else 0 else 0 :=
              ENNReal.le_tsum (f := fun r : ℕ => if r ≤ 1 then
                ∑' b : FourWalkState,
                  if pair12Gap b = y then p N r a b else 0 else 0) 0

/-- The time-zero transition identity gives a positive gap-envelope value at unit gap, contradicting an upper bound proportional to `log_-(1)`. -/
theorem dhp26_12_printed_gap_envelope_false
    (p : ℕ → ℕ → FourWalkState → FourWalkState → ℝ≥0∞)
    (hp0 : ∀ N a b, p N 0 a b = if a = b then 1 else 0) :
    ¬ ∃ H : ℝ → ℝ, ∃ C : ℝ,
      (∀ x, 0 < x → 0 ≤ H x) ∧
      (∀ x, 0 < x → x ≤ 1 → H x ≤ C * logMinus x) ∧
      (∀ N t a y, 1 ≤ t →
        sourceGapSliceMass p N t a y ≤
          ENNReal.ofReal (H (Real.sqrt (t : ℝ)⁻¹ * latticeNorm (pair12Gap a)))) := by
  rintro ⟨H, C, hHnonneg, hHbound, hclaim⟩
  let a : FourWalkState := fun i => if i = 0 then (1, 0) else (0, 0)
  have hgap : pair12Gap a = (1, 0) := by
    norm_num [pair12Gap, a]
  have hnorm : latticeNorm (pair12Gap a) = 1 := by
    rw [hgap]
    norm_num [latticeNorm]
  have hH1_nonneg : 0 ≤ H 1 := hHnonneg 1 (by norm_num)
  have hH1_le : H 1 ≤ 0 := by
    have h := hHbound 1 (by norm_num) (by norm_num)
    simpa [logMinus] using h
  have hH1 : H 1 = 0 := le_antisymm hH1_le hH1_nonneg
  have hmass : 1 ≤ sourceGapSliceMass p 1 1 a (pair12Gap a) :=
    sourceGapSliceMass_ge_one p hp0 1 a (pair12Gap a) rfl
  have hupper := hclaim 1 1 a (pair12Gap a) (by norm_num)
  rw [hnorm] at hupper
  have harg : Real.sqrt ((1 : ℕ) : ℝ)⁻¹ * 1 = 1 := by norm_num
  rw [harg] at hupper
  have hzero : ENNReal.ofReal (H 1) = 0 := by rw [hH1, ENNReal.ofReal_zero]
  rw [hzero] at hupper
  exact (not_le_of_gt (by norm_num : (0 : ℝ≥0∞) < 1)) (le_trans hmass hupper)

end Critical2DKPZ.Errata.DHP26

