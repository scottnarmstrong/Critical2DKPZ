/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Basic
public import Critical2DKPZ.Definitions.CellAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Volume of the even-lattice cells

The coordinates `(x₀+x₁)/2`, `(x₀-x₁)/2` turn a nearest-point cell into a half-open unit square.
Their determinant is `-1/2`; after diffusive scaling this gives the exact cell volume `4/N`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ

/-- Integer coordinates for the nearest-even-lattice convention. -/
theorem nearestEven_eq_iff (x : Plane) (a b : ℤ) :
    nearestEven x = ![a + b, a - b] ↔
      round ((x 0 + x 1) / 2) = a ∧ round ((x 0 - x 1) / 2) = b := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [nearestEven, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h0 h1
    constructor <;> omega
  · rintro ⟨ha, hb⟩
    simp only [nearestEven, ha, hb]

/-- Volume of a scaled nearest-even cell, before choosing the diffusive scale. -/
theorem volume_nearestEven_fiber {r : ℝ} (hr : 0 < r) (a b : ℤ) :
    volume {x : Plane | nearestEven (r • x) = ![a + b, a - b]} =
      ENNReal.ofReal (2 / r ^ 2) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := ![![r / 2, r / 2], ![r / 2, -(r / 2)]]
  let v : Fin 2 → ℝ := ![(a : ℝ), (b : ℝ)]
  let B : Set (Fin 2 → ℝ) := pi univ (fun i => Ico (v i - 1 / 2) (v i + 1 / 2))
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hM : M.det = -(r ^ 2 / 2) := by
    rw [Matrix.det_fin_two]
    change (r / 2) * (-(r / 2)) - (r / 2) * (r / 2) = -(r ^ 2 / 2)
    ring
  have hM0 : M.det ≠ 0 := by rw [hM]; exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hr.ne') (by norm_num))
  have hm : Measurable (Matrix.toLin' M) := (LinearMap.continuous_on_pi _).measurable
  have hBM : MeasurableSet ((Matrix.toLin' M) ⁻¹' B) := hm hB
  have hv : volume B = 1 := by
    rw [volume_pi_pi]
    simp only [Real.volume_Ico]
    norm_num [B, v, Fin.prod_univ_two]
  have hdet : |M.det|⁻¹ = 2 / r ^ 2 := by
    rw [hM, abs_neg, abs_of_nonneg (by positivity : 0 ≤ r ^ 2 / 2)]
    field_simp
  have he : {x : Plane | nearestEven (r • x) = ![a + b, a - b]} =
      WithLp.ofLp ⁻¹' ((Matrix.toLin' M) ⁻¹' B) := by
    ext x
    rw [mem_ofPred_eq, nearestEven_eq_iff]
    simp only [mem_preimage, B, mem_pi, mem_univ, forall_const, round_eq_iff,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    constructor
    · rintro ⟨ha, hb⟩ i
      fin_cases i
      · convert ha using 1 <;> dsimp [M, v]
        ring
      · convert hb using 1 <;> dsimp [M, v]
        ring
    · intro h
      constructor
      · convert h 0 using 1 <;> dsimp [M, v]
        ring
      · convert h 1 using 1 <;> dsimp [M, v]
        ring
  rw [he, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hBM.nullMeasurableSet]
  rw [← Measure.map_apply hm hB, Real.map_matrix_volume_pi_eq_smul_volume_pi hM0,
    Measure.smul_apply, smul_eq_mul, hv, mul_one, abs_inv, hdet]

/-- Exact area of every even cell at every positive lattice scale. -/
theorem volume_cell {N : ℕ} (hN : 0 < N) {z : Site} (hz : z ∈ evenLattice) :
    volume (cell N z) = ENNReal.ofReal (4 / (N : ℝ)) := by
  obtain ⟨a, ha⟩ := hz
  let b : ℤ := z 0 - a
  have hz' : z = ![a + b, a - b] := by
    ext i
    fin_cases i
    · change z 0 = a + (z 0 - a)
      ring
    · change z 1 = a - (z 0 - a)
      omega
  have hr : 0 < Real.sqrt (N / 2) := Real.sqrt_pos.mpr (by positivity)
  change volume {x : Plane | nearestEven (Real.sqrt (N / 2) • x) = z} = _
  rw [hz', volume_nearestEven_fiber hr, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
  congr 1
  field_simp
  norm_num


/-- Every even lattice cell has finite area at positive scale. -/
theorem volume_cell_lt_top {N : ℕ} (hN : 0 < N) {z : Site} (hz : z ∈ evenLattice) :
    volume (cell N z) < ⊤ := by
  rw [volume_cell hN hz]
  exact ENNReal.ofReal_lt_top

/-- Every even lattice cell has area four divided by the positive scale. -/
theorem volume_cell_toReal {N : ℕ} (hN : 0 < N) {z : Site} (hz : z ∈ evenLattice) :
    (volume (cell N z)).toReal = 4 / (N : ℝ) := by
  rw [volume_cell hN hz, ENNReal.toReal_ofReal (by positivity)]

/-- Averaging a constant over an even lattice cell preserves that constant. -/
@[simp] theorem cellAverage_const {N : ℕ} (hN : 0 < N) {z : Site}
    (hz : z ∈ evenLattice) (c : ℝ) : cellAverage N (fun _ => c) z = c := by
  rw [cellAverage, setIntegral_const, measureReal_def, smul_eq_mul,
    volume_cell_toReal hN hz]
  exact inv_mul_cancel_left₀ (by positivity : (4 : ℝ) / N ≠ 0) c

end Critical2DKPZ

end
