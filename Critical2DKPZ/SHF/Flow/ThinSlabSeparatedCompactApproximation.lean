/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedCoordinates
public import Critical2DKPZ.SHF.Flow.PiMomentConvergence
public import Critical2DKPZ.SHF.Tsai.CompactTensorMajorants

/-! # Compact-test approximation bounds for two separated slabs -/

@[expose] public section

open MeasureTheory Set Filter
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- A uniform approximation on a common compact coordinate window is controlled by the product
of positive one-block tensor masses on the two separated slabs. -/
theorem abs_integral_sub_le_slabSeparatedCompactMass
    (μ ν : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (K : Set (Plane × Plane))
    (g g' : C_c(Plane, ℝ)) (hg : ∀ x, 0 ≤ g x) (hg' : ∀ x, 0 ≤ g' x)
    (hone : ∀ p ∈ K, g p.1 * g' p.2 = 1)
    (F G : C_c((Fin 4 → Plane × Plane), ℝ))
    (hFs : tsupport (F : (Fin 4 → Plane × Plane) → ℝ) ⊆ Set.univ.pi fun _ => K)
    (hGs : tsupport (G : (Fin 4 → Plane × Plane) → ℝ) ⊆ Set.univ.pi fun _ => K)
    (δ : ℝ) (hδ : 0 ≤ δ) (happrox : ∀ q, |F q - G q| ≤ δ) :
    |(∫ q, F q ∂slabTwoBlockPiMeasure μ ν) - ∫ q, G q ∂slabTwoBlockPiMeasure μ ν| ≤
      δ * (∫ p, g p.1 * g' p.2 ∂μ) ^ 2 * (∫ p, g p.1 * g' p.2 ∂ν) ^ 2 := by
  let ψ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  let T : C_c((Fin 4 → Plane × Plane), ℝ) := slabCompactPiTensorTest (fun _ => ψ)
  have hTnonneg (q : Fin 4 → Plane × Plane) : 0 ≤ T q := by
    simp only [T, slabCompactPiTensorTest_apply]
    exact Finset.prod_nonneg fun i hi => by
      simp only [ψ, compactTensorTest_apply]
      exact mul_nonneg (hg _) (hg' _)
  have hTintegrable : Integrable (fun q => T q) (slabTwoBlockPiMeasure μ ν) := by
    have hSigmaμ : SigmaFinite μ := by infer_instance
    have hSigmaν : SigmaFinite ν := by infer_instance
    have hLF : IsLocallyFiniteMeasure (slabTwoBlockPiMeasure μ ν) := by
      exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
        (Fin 4) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
        (fun i => if i.val < 2 then μ else ν) (by intro i; split_ifs <;> assumption)
        (fun _ => inferInstance) (by intro i; split_ifs <;> assumption)
    exact integrable_compactTest_of_locallyFinite _ hLF T
  have hFint : Integrable (fun q => F q) (slabTwoBlockPiMeasure μ ν) := by
    have hSigmaμ : SigmaFinite μ := by infer_instance
    have hSigmaν : SigmaFinite ν := by infer_instance
    have hLF : IsLocallyFiniteMeasure (slabTwoBlockPiMeasure μ ν) := by
      exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
        (Fin 4) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
        (fun i => if i.val < 2 then μ else ν) (by intro i; split_ifs <;> assumption)
        (fun _ => inferInstance) (by intro i; split_ifs <;> assumption)
    exact integrable_compactTest_of_locallyFinite _ hLF F
  have hGint : Integrable (fun q => G q) (slabTwoBlockPiMeasure μ ν) := by
    have hSigmaμ : SigmaFinite μ := by infer_instance
    have hSigmaν : SigmaFinite ν := by infer_instance
    have hLF : IsLocallyFiniteMeasure (slabTwoBlockPiMeasure μ ν) := by
      exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
        (Fin 4) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
        (fun i => if i.val < 2 then μ else ν) (by intro i; split_ifs <;> assumption)
        (fun _ => inferInstance) (by intro i; split_ifs <;> assumption)
    exact integrable_compactTest_of_locallyFinite _ hLF G
  let R : Set (Fin 4 → Plane × Plane) := Set.univ.pi fun _ => K
  have hpoint (q : Fin 4 → Plane × Plane) : ‖F q - G q‖ ≤ δ * T q := by
    by_cases hq : q ∈ R
    · have hprod : ∏ i : Fin 4, ψ (q i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hKi : q i ∈ K := (Set.mem_univ_pi.mp hq) i
        have honei := hone (q i) hKi
        simp [ψ, compactTensorTest_apply, honei]
      have hTq : T q = 1 := by
        simp only [T, slabCompactPiTensorTest_apply]
        exact hprod
      rw [Real.norm_eq_abs, hTq]
      simpa only [mul_one] using happrox q
    · have hnot : ¬ ∀ i : Fin 4, q i ∈ K := by
        simpa only [R, Set.mem_univ_pi] using hq
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      have hFzero : F q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hsupport
        apply hq
        simpa only [R] using hFs hsupport
      have hGzero : G q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hsupport
        apply hq
        simpa only [R] using hGs hsupport
      rw [hFzero, hGzero]
      simp only [sub_self, norm_zero]
      exact mul_nonneg hδ (hTnonneg q)
  have hDiffInt : Integrable (fun q => F q - G q) (slabTwoBlockPiMeasure μ ν) := hFint.sub hGint
  have hMajorInt : Integrable (fun q => δ * T q) (slabTwoBlockPiMeasure μ ν) := hTintegrable.const_mul δ
  have hnorm := norm_integral_le_of_norm_le hMajorInt (Filter.Eventually.of_forall hpoint)
  have hsub : (∫ q, F q - G q ∂slabTwoBlockPiMeasure μ ν) =
      (∫ q, F q ∂slabTwoBlockPiMeasure μ ν) - ∫ q, G q ∂slabTwoBlockPiMeasure μ ν :=
    integral_sub hFint hGint
  have hTcalc : (∫ q, T q ∂slabTwoBlockPiMeasure μ ν) =
      (∫ p, g p.1 * g' p.2 ∂μ) ^ 2 * (∫ p, g p.1 * g' p.2 ∂ν) ^ 2 := by
    have h := integral_slabCompactPiTensorTest_twoBlock
      (by infer_instance : SigmaFinite μ) (by infer_instance : SigmaFinite ν) (fun _ => ψ)
    simpa [T, ψ, compactTensorTest_apply, Finset.prod_const, Finset.card_fin] using h
  have hscale : ∫ q, δ * T q ∂slabTwoBlockPiMeasure μ ν =
      δ * ((∫ p, g p.1 * g' p.2 ∂μ) ^ 2 * (∫ p, g p.1 * g' p.2 ∂ν) ^ 2) := by
    rw [integral_const_mul, hTcalc]
  rw [hsub, Real.norm_eq_abs] at hnorm
  rw [hscale] at hnorm
  simpa only [mul_assoc] using hnorm

end Critical2DKPZ.SHF.Flow

end
