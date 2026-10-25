/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioInverseExpectation
import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! # Inverse moment through the tilted law -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- Independence factors the integral of a finite product of block inverse masses. -/
theorem integral_prod_inv_blockMass (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {r s : ℕ} (hr : 1 ≤ r) :
    ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw =
      ∏ i ∈ Finset.Icc r s, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
  classical
  let ι := {i : ℕ // i ∈ Finset.Icc r s}
  let emb : ι → {i : ℕ // 1 ≤ i} := fun i =>
    ⟨i.val, hr.trans (Finset.mem_Icc.mp i.property).1⟩
  have hemb : Function.Injective emb := by
    intro i j hij
    apply Subtype.ext
    have hval : (emb i).val = (emb j).val :=
      congrArg (fun q : {i : ℕ // 1 ≤ i} => q.val) hij
    simpa [emb] using hval
  have hIndMass := (Critical2DKPZ.Blocks.iIndepFun_blockMass β t ht).precomp hemb
  have hIndInv :
      iIndepFun (fun i : ι => fun ω => (blockMass β t i.val ω)⁻¹) disorderLaw := by
    have h := hIndMass.comp (fun _ : ι => fun z : ℝ => z⁻¹) (fun _ => measurable_inv)
    convert h using 1
    ext i ω
    rfl
  have hInvInt (i : ι) : Integrable (fun ω => (blockMass β t i.val ω)⁻¹) disorderLaw := by
    have hpow := integrable_rpow_smoothedP2Plane β (t (i.val - 1)) (t i.val) 0 (-1)
    have heq : (fun ω => (blockMass β t i.val ω)⁻¹) =
        fun ω => blockMass β t i.val ω ^ (-1 : ℝ) := by
      funext ω
      rw [Real.rpow_neg_one]
    simpa only [blockMass] using heq.symm ▸ hpow
  have hprodSub :
      ∫ ω, ∏ i : ι, (blockMass β t i.val ω)⁻¹ ∂disorderLaw =
        ∏ i : ι, ∫ ω, (blockMass β t i.val ω)⁻¹ ∂disorderLaw :=
    hIndInv.integral_fun_prod_eq_prod_integral fun i => (hInvInt i).aestronglyMeasurable
  have hprodAttach (f : ℕ → ℝ) :
      (∏ i : ι, f i.val) = ∏ i ∈ Finset.Icc r s, f i := by
    rw [Finset.univ_eq_attach, Finset.prod_attach]
  calc
    ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw =
        ∫ ω, ∏ i : ι, (blockMass β t i.val ω)⁻¹ ∂disorderLaw := by
          congr 1
          funext ω
          exact (hprodAttach fun i => (blockMass β t i ω)⁻¹).symm
    _ = ∏ i : ι, ∫ ω, (blockMass β t i.val ω)⁻¹ ∂disorderLaw := hprodSub
    _ = ∏ i ∈ Finset.Icc r s, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw :=
      hprodAttach fun i => ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw

/-- The inverse moment of a long smoothed mass equals its normalized tilted ratio moment times
the independent block inverse moments. -/
theorem integral_inv_smoothedP2Plane_eq_tilted (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) :
    ∫ ω, (smoothedP2Plane β (t (r - 1)) (t s) 0 ω)⁻¹ ∂disorderLaw =
      ((∫ ω, (blockRatio β t r s ω)⁻¹ *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw) /
          ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw) *
        ∏ i ∈ Finset.Icc r s, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
  have hfactor := integral_prod_inv_blockMass β t ht hr (s := s)
  have hprodLower :
      1 ≤ ∏ i ∈ Finset.Icc r s, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    rw [← Finset.prod_const_one]
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      exact one_le_integral_inv_blockMass β t i
  have hdenpos : 0 < ∫ ω, ∏ i ∈ Finset.Icc r s,
      (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    rw [hfactor]
    linarith
  have hpoint (ω : Disorder) :
      (smoothedP2Plane β (t (r - 1)) (t s) 0 ω)⁻¹ =
        (blockRatio β t r s ω)⁻¹ * ∏ i ∈ Finset.Icc r s,
          (blockMass β t i ω)⁻¹ := by
    have hdecomp := smoothedP2Plane_eq_prod_blockMass_mul_blockRatio β t r s ω
    rw [hdecomp, mul_inv, Finset.prod_inv_distrib]
    ring
  have hnum :
      ∫ ω, (smoothedP2Plane β (t (r - 1)) (t s) 0 ω)⁻¹ ∂disorderLaw =
        ∫ ω, (blockRatio β t r s ω)⁻¹ *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpoint
  calc
    ∫ ω, (smoothedP2Plane β (t (r - 1)) (t s) 0 ω)⁻¹ ∂disorderLaw =
        ∫ ω, (blockRatio β t r s ω)⁻¹ *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw := hnum
    _ = ((∫ ω, (blockRatio β t r s ω)⁻¹ *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw) /
          ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw) *
        ∏ i ∈ Finset.Icc r s, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
          rw [← hfactor]
          exact (div_mul_cancel₀ _ hdenpos.ne').symm

end Critical2DKPZ.OnePoint

end
