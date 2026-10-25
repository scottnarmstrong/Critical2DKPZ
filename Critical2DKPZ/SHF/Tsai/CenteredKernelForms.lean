/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredKernel
public import Critical2DKPZ.SHF.Tsai.MixedBlockFormBounds
import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms

/-! # Integrable signed forms of the centered moment kernel

At positive times the real centered kernel is exactly the finite signed sum
of the mixed positive kernels. Their finite L² form bounds justify all signed
integrals and the passage of the finite inclusion-exclusion sum through them.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The real centered kernel is the signed sum of the mixed-block kernels at nonnegative times. -/
theorem centeredMomentKernel_eq_sum_mixedBlockKernel (n : ℕ) (θ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (x y : Configuration n) :
    centeredMomentKernel n θ τ x y = ∑ S : Finset (Fin n),
      (-1 : ℝ) ^ (n - S.card) * (mixedBlockKernel n θ τ S x y).toReal := by
  classical
  unfold centeredMomentKernel
  apply Finset.sum_congr rfl
  intro S _
  rw [mixedBlockKernel, ENNReal.toReal_mul, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg hτ _), mul_assoc]


private theorem centered_form_integrand_eq_sum (n : ℕ) (θ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (G F : Configuration n → ℝ) :
    (fun q : Configuration n × Configuration n => G q.1 * centeredMomentKernel n θ τ q.1 q.2 * F q.2) =
      fun q => ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        (G q.1 * (mixedBlockKernel n θ τ S q.1 q.2).toReal * F q.2) := by
  funext q
  rw [centeredMomentKernel_eq_sum_mixedBlockKernel n θ hτ, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Every L² signed form of the centered moment kernel is absolutely integrable. -/
theorem integrable_centeredMomentKernel_real_form (n : ℕ) (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    Integrable (fun q : Configuration n × Configuration n =>
      G q.1 * centeredMomentKernel n θ τ q.1 q.2 * F q.2) (volume.prod volume) := by
  classical
  have hI (S : Finset (Fin n)) : Integrable (fun q : Configuration n × Configuration n =>
      G q.1 * (mixedBlockKernel n θ τ S q.1 q.2).toReal * F q.2) (volume.prod volume) := by
    obtain ⟨c, hc, hQ⟩ := exists_formBound_mixedBlockKernel n S θ hτ
    exact (configurationKernel_real_form_bound (measurable_mixedBlockKernel n θ τ S)
      hc hQ G F hG hF).1
  rw [centered_form_integrand_eq_sum n θ hτ.le G F]
  exact integrable_finsetSum _ (fun S _ => (hI S).const_mul _)

/-- The absolutely integrable centered form equals the finite signed sum of mixed forms. -/
theorem integral_centeredMomentKernel_real_form_eq_sum (n : ℕ) (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    (∫ x, ∫ y, G x * centeredMomentKernel n θ τ x y * F y) =
      ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        ∫ x, ∫ y, G x * (mixedBlockKernel n θ τ S x y).toReal * F y := by
  classical
  have hI (S : Finset (Fin n)) : Integrable (fun q : Configuration n × Configuration n =>
      G q.1 * (mixedBlockKernel n θ τ S q.1 q.2).toReal * F q.2) (volume.prod volume) := by
    obtain ⟨c, hc, hQ⟩ := exists_formBound_mixedBlockKernel n S θ hτ
    exact (configurationKernel_real_form_bound (measurable_mixedBlockKernel n θ τ S)
      hc hQ G F hG hF).1
  rw [← integral_prod _ (integrable_centeredMomentKernel_real_form n θ hτ G F hG hF)]
  rw [centered_form_integrand_eq_sum n θ hτ.le G F, integral_finsetSum _ (fun S _ => (hI S).const_mul _)]
  apply Finset.sum_congr rfl
  intro S _
  rw [integral_const_mul, integral_prod _ (hI S)]

/-- The integrable centered form in complementary-subset notation used by centered chain moments. -/
theorem integral_centeredMomentKernel_real_form_eq_sum_compl (n : ℕ) (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    (∫ x, ∫ y, G x * centeredMomentKernel n θ τ x y * F y) =
      ∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card *
        ∫ x, ∫ y, G x * (mixedBlockKernel n θ τ Sᶜ x y).toReal * F y := by
  classical
  rw [integral_centeredMomentKernel_real_form_eq_sum n θ hτ G F hG hF]
  apply Finset.sum_bij (fun S _ => Sᶜ)
  · intro S _
    exact Finset.mem_univ _
  · intro S _ T _ hST
    exact compl_injective hST
  · intro S _
    exact ⟨Sᶜ, Finset.mem_univ _, compl_compl S⟩
  · intro S _
    simp only [compl_compl, Finset.card_compl, Fintype.card_fin]

end Critical2DKPZ.SHF.Tsai

end
