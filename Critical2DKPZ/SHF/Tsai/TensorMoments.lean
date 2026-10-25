/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockMoments
public import Critical2DKPZ.SHF.Tsai.MomentOperators
import Mathlib.MeasureTheory.Integral.Pi

/-! # Tensor tests for the block moment operators

Spatial tensor tests belong to configuration `L²`. Their norm is the product
of the one-particle norms. Thus the moment formula is the literal pairing of
the bounded moment operator, with quantitative control uniform in the tests.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Products of one-particle `L²` tests belong to configuration `L²`. -/
theorem memLp_configuration_tensor {n : ℕ} (g : Fin n → Plane → ℝ)
    (hg : ∀ i, MemLp (g i) 2) :
    MemLp (fun x : Configuration n => ∏ i, g i (x i)) 2 := by
  have hm : AEStronglyMeasurable (fun x : Configuration n => ∏ i, g i (x i)) volume := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hg i).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure Plane)) i)
  apply (memLp_two_iff_integrable_sq hm).2
  have h := Integrable.fintype_prod (fun i => (hg i).integrable_sq)
  simpa only [Finset.prod_pow, ← volume_pi] using h

/-- A configuration tensor as an `L²` vector, retaining its actual representative. -/
def tensorLp {n : ℕ} (g : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) :
    Lp ℝ 2 (volume : Measure (Configuration n)) :=
  (memLp_configuration_tensor g hg).toLp (fun x => ∏ i, g i (x i))

/-- The norm of a spatial tensor factors into the one-particle `L²` norms. -/
theorem norm_tensorLp {n : ℕ} (g : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) :
    ‖tensorLp g hg‖ = ∏ i, ‖(hg i).toLp (g i)‖ := by
  have hnorm {α : Type} [MeasurableSpace α] {μ : Measure α}
      {f : α → ℝ} (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)).1
  rw [tensorLp, hnorm, ← Finset.prod_pow]
  simp_rw [hnorm]
  simp_rw [← Finset.prod_pow]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => (volume : Measure Plane))
    (fun i x => g i x ^ 2)



end Critical2DKPZ.SHF.Tsai

end
