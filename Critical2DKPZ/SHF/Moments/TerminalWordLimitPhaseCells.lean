/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.LongWordLimitCells
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSampling
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic

/-! # Exact finite cell integration with coordinatewise parity phases -/

@[expose] public noncomputable section

open MeasureTheory Measure
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The finite configuration-cell formula is unchanged by distinct parity
phases at the different coordinates. Translation of the physical cells and
the site supports makes the phase convention explicit. -/
theorem integrable_integral_configurationPhaseStep {m N : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (S : Finset (Fin m → Site))
    (hS : ∀ z ∈ S, ∀ i, Even (z i 0 + z i 1 + (k i : ℤ)))
    (G : (Fin m → Site) → ℝ) (hzero : ∀ z ∉ S, G z = 0) :
    Integrable (fun x : Configuration m => G (fun i => pairTwoFutureSampleSite N (k i) (x i))) ∧
      (∫ x : Configuration m, G (fun i => pairTwoFutureSampleSite N (k i) (x i))) =
        (4 / (N : ℝ)) ^ m * ∑ z ∈ S, G z := by
  classical
  let q : Fin m → Site := fun i => entranceParityShift (k i)
  let δ : Configuration m := fun i => latticeRepresentative N (q i)
  let A := S.image (fun z => z - q)
  let F : (Fin m → Site) → ℝ := fun z => G (z + q)
  have hA : ∀ z ∈ A, ∀ i, z i ∈ evenLattice := by
    intro z hz i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hp := hS y hy i
    have hq := entranceParityShift_phase (k i) (a := 0)
      (by change Even ((0 : ℤ) + 0); simp)
    change Even ((y - q) i 0 + (y - q) i 1)
    rw [Int.even_iff] at hp hq ⊢
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero] at hq ⊢
    dsimp only [q]
    omega
  have hFzero (z : Fin m → Site) (hz : z ∉ A) : F z = 0 := by
    apply hzero (z + q)
    intro hmem
    apply hz
    apply Finset.mem_image.mpr
    exact ⟨z + q, hmem, add_sub_cancel_right z q⟩
  obtain ⟨hint, hintEq⟩ := integrable_integral_configurationLatticeStep hN A hA F hFzero
  have hsum : (∑ z ∈ A, F z) = ∑ z ∈ S, G z := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro z hz
      exact congrArg G (sub_add_cancel z q)
    · intro x hx y hy hxy
      exact sub_left_injective hxy
  have : IsAddHaarMeasure (volume : Measure Plane) := by
    rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).addHaar_eq_volume]
    infer_instance
  have : IsAddHaarMeasure (volume : Measure (Configuration m)) := by infer_instance
  let e : Configuration m ≃ᵐ Configuration m := MeasurableEquiv.addRight δ
  have he : MeasurePreserving e := measurePreserving_add_right volume δ
  let H : Configuration m → ℝ := fun x => G (fun i => pairTwoFutureSampleSite N (k i) (x i))
  have hcomp : H ∘ e = fun x : Configuration m => F (fun i => latticePoint N (x i)) := by
    funext x
    apply congrArg G
    funext i
    simp only [e, MeasurableEquiv.coe_addRight, Pi.add_apply,
      pairTwoFutureSampleSite, δ, q, add_sub_cancel_right]
  refine ⟨?_, ?_⟩
  · exact (he.integrable_comp_emb e.measurableEmbedding).mp (hcomp ▸ hint)
  · have hi := he.integral_comp' H
    change (∫ x, (H ∘ e) x) = (∫ y, H y) at hi
    rw [hcomp, hintEq, hsum] at hi
    exact hi.symm

end Critical2DKPZ.SHF.Moments
