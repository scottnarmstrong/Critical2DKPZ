/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseInputs
import Mathlib.MeasureTheory.Integral.Pi

/-! Compact tensor tests describe the moments of two polymer blocks. -/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- The compactly supported product test associated with finitely many endpoint tests. -/
def slabCompactPiTensorTest {n : ℕ} (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    C_c((Fin n → Plane × Plane), ℝ) := by
  let K : Set (Fin n → Plane × Plane) := Set.univ.pi fun i => tsupport (φ i)
  have hK : IsCompact K := isCompact_univ_pi fun i => (φ i).hasCompactSupport
  refine ⟨⟨fun q => ∏ i, φ i (q i), by fun_prop⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro q hq
  apply Set.mem_univ_pi.mpr
  intro i
  by_contra hi
  have hzero : φ i (q i) = 0 := image_eq_zero_of_notMem_tsupport hi
  apply hq
  simp only [Finset.prod_eq_zero (Finset.mem_univ i), hzero]

/-- Evaluation of the compact tensor test is the corresponding pointwise product. -/
theorem slabCompactPiTensorTest_apply {n : ℕ} (φ : Fin n → C_c(Plane × Plane, ℝ))
    (q : Fin n → Plane × Plane) : slabCompactPiTensorTest φ q = ∏ i, φ i (q i) := rfl

/-- Integrating a compact tensor test against a product measure factors into its coordinates. -/
theorem integral_slabCompactPiTensorTest {n : ℕ} (μ : Measure (Plane × Plane))
    (hμ : SigmaFinite μ) (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    (∫ q, slabCompactPiTensorTest φ q ∂Measure.pi (fun _ : Fin n => μ)) =
      ∏ i, ∫ p, φ i p ∂μ := by
  change (∫ q, ∏ i, φ i (q i) ∂Measure.pi (fun _ : Fin n => μ)) = _
  exact @MeasureTheory.integral_fintype_prod_eq_prod ℝ (Fin n) inferInstance inferInstance
    (fun _ => Plane × Plane) (fun i p => φ i p)
    (mE := fun _ => inferInstance) (μ := fun _ => μ) (fun _ => hμ)

/-- The tensor integral formula for a product of possibly different measures. -/
theorem integral_slabCompactPiTensorTest_general {n : ℕ}
    (μ : Fin n → Measure (Plane × Plane)) (hμ : ∀ i, SigmaFinite (μ i))
    (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    (∫ q, slabCompactPiTensorTest φ q ∂Measure.pi μ) =
      ∏ i, ∫ p, φ i p ∂(μ i) := by
  change (∫ q, ∏ i, φ i (q i) ∂Measure.pi μ) = _
  exact @MeasureTheory.integral_fintype_prod_eq_prod ℝ (Fin n) inferInstance inferInstance
    (fun _ => Plane × Plane) (fun i p => φ i p)
    (mE := fun _ => inferInstance) (μ := μ) hμ

/-- The four-replica product law formed from two replicas of each of two measures. -/
noncomputable def slabTwoBlockPiMeasure (μ ν : Measure (Plane × Plane)) :
    Measure (Fin 4 → Plane × Plane) :=
  Measure.pi fun i => if i.val < 2 then μ else ν

/-- A tensor test integrates against the two-block product law as a product of the two
two-replica tensor integrals. -/
theorem integral_slabCompactPiTensorTest_twoBlock {μ ν : Measure (Plane × Plane)}
    (hμ : SigmaFinite μ) (hν : SigmaFinite ν) (φ : Fin 4 → C_c(Plane × Plane, ℝ)) :
    (∫ q, slabCompactPiTensorTest φ q ∂slabTwoBlockPiMeasure μ ν) =
      (∏ i : Fin 2, ∫ p, φ (i.castAdd 2) p ∂μ) *
        ∏ i : Fin 2, ∫ p, φ (i.natAdd 2) p ∂ν := by
  have h := integral_slabCompactPiTensorTest_general
    (fun i : Fin 4 => if i.val < 2 then μ else ν) (by
      intro i
      split_ifs <;> assumption) φ
  change (∫ q, ∏ i, φ i (q i) ∂
      Measure.pi (fun i : Fin 4 => if i.val < 2 then μ else ν)) = _ at h
  rw [Fin.prod_univ_four] at h
  norm_num at h
  calc
    _ = (((∫ p, φ 0 p ∂μ) * ∫ p, φ 1 p ∂μ) *
        ∫ p, φ 2 p ∂ν) * ∫ p, φ 3 p ∂ν := by
      simpa [slabTwoBlockPiMeasure, Fin.prod_univ_two, Fin.val_castAdd,
        Fin.val_natAdd, slabCompactPiTensorTest] using h
    _ = _ := by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      simp only [show Fin.castAdd 2 (0 : Fin 2) = (0 : Fin 4) by decide,
        show Fin.castAdd 2 (1 : Fin 2) = (1 : Fin 4) by decide,
        show Fin.natAdd 2 (0 : Fin 2) = (2 : Fin 4) by decide,
        show Fin.natAdd 2 (1 : Fin 2) = (3 : Fin 4) by decide]
      ring

end Critical2DKPZ.SHF.Flow

end
