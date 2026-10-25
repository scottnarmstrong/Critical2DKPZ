/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredKernelForms
public import Critical2DKPZ.SHF.Tsai.CenteredChainMoments
import Critical2DKPZ.SHF.Tsai.TensorMoments
import Critical2DKPZ.SHF.Tsai.HeatMollifier

/-! # Actual centered block moments and the signed centered kernel

The zero-connector chain moment identity and finite inclusion-exclusion give
Tsai's centered block kernel form. Both the random-variable product and the
signed spatial form are absolutely integrable.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Products of centered block tensor pairings equal the absolutely integrable signed centered-kernel form. -/
theorem HasDeltaBoseMoments.integral_prod_centered_eq_kernel {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Ω → Measure (Plane × Plane)} (hA : HasDeltaBoseMoments θ τ P A) (hτ : 0 < τ)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    Integrable (fun ω => ∏ i, ((∫ p, g i p.1 * g' i p.2 ∂A ω) -
      ∫ p, g i p.1 * g' i p.2 ∂heatBlock τ)) P ∧
    Integrable (fun q : Configuration n × Configuration n =>
      (∏ i, g i (q.1 i)) * centeredMomentKernel n θ τ q.1 q.2 * ∏ i, g' i (q.2 i)) (volume.prod volume) ∧
    (∫ ω, ∏ i, ((∫ p, g i p.1 * g' i p.2 ∂A ω) -
      ∫ p, g i p.1 * g' i p.2 ∂heatBlock τ) ∂P) =
      ∫ x, ∫ y, (∏ i, g i (x i)) * centeredMomentKernel n θ τ x y * ∏ i, g' i (y i) := by
  have hind : iIndepFun (fun _ : Fin 1 => A) P := iIndepFun.of_subsingleton
  have hMom := integral_prod_centeredChainPairings_eq 0 0 le_rfl (fun _ => τ)
    (fun _ _ => hτ) (fun _ => A) (fun _ _ => hA) hind hn1 hn
    (fun _ _ => heatMollifier) (fun _ _ => isL2ApplicableMollifier_heatMollifier) 0 g g' hg hg'
  simp only [chainProduct, Function.update_self, chainKernel, Finset.powerset_univ] at hMom
  have hG : MemLp (fun x : Configuration n => ∏ i, g i (x i)) 2 := memLp_configuration_tensor g hg
  have hF : MemLp (fun y : Configuration n => ∏ i, g' i (y i)) 2 := memLp_configuration_tensor g' hg'
  exact ⟨hMom.1, integrable_centeredMomentKernel_real_form n θ hτ _ _ hG hF,
    hMom.2.trans (integral_centeredMomentKernel_real_form_eq_sum_compl n θ hτ _ _ hG hF).symm⟩

end Critical2DKPZ.SHF.Tsai

end
