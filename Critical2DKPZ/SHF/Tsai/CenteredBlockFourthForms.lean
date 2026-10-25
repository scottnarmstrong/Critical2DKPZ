/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredBlockKernelMoments
public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
import Critical2DKPZ.SHF.Tsai.FourthMomentSumLimits
import Critical2DKPZ.SHF.Tsai.TensorMoments

/-! # The deterministic single-block centered fourth form

The ordered fourth-power expansion and the actual centered block moment
identity give the finite deterministic kernel form exactly. All random and
spatial terms are absolutely integrable, and the resulting form is nonnegative
whenever the prescribed moment block is present.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped CompactlySupported
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The explicit centered kernel form for a finite sum of single-block tensor pairings. -/
def centeredBlockFourthForm (θ t : ℝ) {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ)) : ℝ :=
  ∑ a, ∑ q : Fin 4 → Fin r, ∫ x, ∫ y,
    (∏ i, g a (q i) (x i)) * centeredMomentKernel 4 θ t x y * ∏ i, g' a (q i) (y i)


/-- The integrable centered fourth remainder of a single block equals its nonnegative deterministic kernel form. -/
theorem HasDeltaBoseMoments.integral_sum_centered_four_eq_form {θ t : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Ω → Measure (Plane × Plane)} (hA : HasDeltaBoseMoments θ t P A) (ht : 0 < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ)) :
    Integrable (fun ω => ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂A ω) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂heatBlock t) ^ 4) P ∧
    0 ≤ centeredBlockFourthForm θ t g g' ∧
    (∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂A ω) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂heatBlock t) ^ 4 ∂P) = centeredBlockFourthForm θ t g g' := by
  classical
  let X (a : Fin m) (b : Fin r) (ω : Ω) :=
    (∫ p, g a b p.1 * g' a b p.2 ∂A ω) - ∫ p, g a b p.1 * g' a b p.2 ∂heatBlock t
  have hMom (a : Fin m) (q : Fin 4 → Fin r) := hA.integral_prod_centered_eq_kernel ht
    (n := 4) (by norm_num) (by norm_num) (fun i => g a (q i)) (fun i => g' a (q i))
    (fun i => (g a (q i)).continuous.memLp_of_hasCompactSupport (g a (q i)).hasCompactSupport)
    (fun i => (g' a (q i)).continuous.memLp_of_hasCompactSupport (g' a (q i)).hasCompactSupport)
  have hData (a : Fin m) := integral_sum_pow_four_eq_sum_integral_prod P (X a) (fun q => (hMom a q).1)
  have hI : Integrable (fun ω => ∑ a, (∑ b, X a b ω) ^ 4) P :=
    integrable_finsetSum _ (fun a _ => (hData a).1)
  have hEq : (∫ ω, ∑ a, (∑ b, X a b ω) ^ 4 ∂P) = centeredBlockFourthForm θ t g g' := by
    rw [integral_finsetSum _ (fun a _ => (hData a).1)]
    apply Finset.sum_congr rfl
    intro a _
    rw [(hData a).2]
    apply Finset.sum_congr rfl
    intro q _
    exact (hMom a q).2.2
  have hNonneg : 0 ≤ centeredBlockFourthForm θ t g g' :=
    hEq ▸ integral_nonneg (fun ω => Finset.sum_nonneg
      (fun a _ => (show Even 4 from ⟨2, rfl⟩).pow_nonneg _))
  simpa only [X, Finset.sum_sub_distrib] using And.intro hI (And.intro hNonneg hEq)

end Critical2DKPZ.SHF.Tsai

end
