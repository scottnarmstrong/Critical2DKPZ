/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Cell
public import Critical2DKPZ.Definitions.SiteToPlane
public import Critical2DKPZ.Lattice.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Nearest-even-lattice cells form a measurable partition with an explicit covering-radius bound in the Euclidean norm. -/

public section

noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ

/-- The squared Euclidean norm is the sum of the squared planar coordinates. -/
theorem plane_norm_sq (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x

/-- Rounding is Borel measurable, including the specified half-integer tie rule. -/
theorem measurable_round_real : Measurable (round : ℝ → ℤ) := by
  have he : (round : ℝ → ℤ) = fun x => ⌊x + 1 / 2⌋ := funext round_eq
  rw [he]
  exact (measurable_id.add_const (1 / 2 : ℝ)).floor

/-- Rounding to the nearest even lattice site is measurable. -/
theorem measurable_nearestEven : Measurable nearestEven := by
  have h0 : Measurable (fun x : Plane => x 0) := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).measurable
  have h1 : Measurable (fun x : Plane => x 1) := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).measurable
  have ha := measurable_round_real.comp ((h0.add h1).div_const 2)
  have hb := measurable_round_real.comp ((h0.sub h1).div_const 2)
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact ha.add hb
  · exact ha.sub hb

/-- The rescaled lattice-site map is measurable. -/
theorem measurable_latticePoint (N : ℕ) : Measurable (latticePoint N) := by
  have hc : Continuous (fun x : Plane => Real.sqrt (N / 2) • x) :=
    (continuous_id : Continuous (fun x : Plane => x)).const_smul (Real.sqrt (N / 2))
  exact measurable_nearestEven.comp hc.measurable

/-- Every lattice cell is measurable. -/
theorem measurableSet_cell (N : ℕ) (z : Site) : MeasurableSet (cell N z) :=
  (measurable_latticePoint N) (measurableSet_singleton z)

/-- A point belongs to a cell exactly when its lattice-site map selects that cell. -/
@[simp] theorem mem_cell_iff (N : ℕ) (z : Site) (x : Plane) :
    x ∈ cell N z ↔ latticePoint N x = z := Iff.rfl

/-- Every point belongs to its selected lattice cell. -/
@[simp] theorem mem_cell_latticePoint (N : ℕ) (x : Plane) :
    x ∈ cell N (latticePoint N x) := rfl

/-- The lattice-site map always selects a site of the even lattice. -/
theorem latticePoint_mem_evenLattice (N : ℕ) (x : Plane) :
    latticePoint N x ∈ evenLattice := nearestEven_mem_evenLattice _

/-- Distinct lattice cells are disjoint. -/
theorem pairwise_disjoint_cell (N : ℕ) :
    Pairwise (fun z w : Site => Disjoint (cell N z) (cell N w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hw
  exact hzw ((mem_cell_iff N z x).mp hx |>.symm.trans ((mem_cell_iff N w x).mp hw))


/-- A cell indexed by a site outside the even lattice is empty. -/
theorem cell_eq_empty_of_not_even {N : ℕ} {z : Site} (hz : z ∉ evenLattice) :
    cell N z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hz ((mem_cell_iff N z x).mp hx ▸ latticePoint_mem_evenLattice N x)

/-- The covering radius of the nearest even lattice is one. -/
theorem norm_sub_nearestEven_le_one (x : Plane) : ‖x - siteToPlane (nearestEven x)‖ ≤ 1 := by
  let u := (x 0 + x 1) / 2
  let v := (x 0 - x 1) / 2
  have hu : (u - round u) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_sub_round u) 2
  have hv : (v - round v) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_sub_round v) 2
  have he : ‖x - siteToPlane (nearestEven x)‖ ^ 2 =
      2 * ((u - round u) ^ 2 + (v - round v) ^ 2) := by
    rw [plane_norm_sq]
    change (x 0 - ((round u + round v : ℤ) : ℝ)) ^ 2 +
      (x 1 - ((round u - round v : ℤ) : ℝ)) ^ 2 = _
    push_cast
    dsimp only [u, v]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [he]
  linarith only [hu, hv]

/-- A sampled point is within `√(2/N)` of the represented continuum point. -/
theorem norm_sub_latticePoint_le {N : ℕ} (hN : 0 < N) (x : Plane) :
    ‖x - (Real.sqrt (N / 2))⁻¹ • siteToPlane (latticePoint N x)‖ ≤
      (Real.sqrt (N / 2))⁻¹ := by
  have hscale : 0 < Real.sqrt (N / 2) := Real.sqrt_pos.mpr (by positivity)
  have he : x - (Real.sqrt (N / 2))⁻¹ • siteToPlane (latticePoint N x) =
      (Real.sqrt (N / 2))⁻¹ •
        (Real.sqrt (N / 2) • x - siteToPlane (latticePoint N x)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
  exact mul_le_of_le_one_right (inv_pos.mpr hscale).le (norm_sub_nearestEven_le_one _)


end Critical2DKPZ

end
