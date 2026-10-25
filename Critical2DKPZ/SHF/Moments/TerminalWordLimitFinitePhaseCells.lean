/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitPhaseCells
import Mathlib.Tactic

/-! # Parity-correct cell integration on arbitrary finite coordinate sets -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- The configuration phase-cell integration formula holds on any finite set of free coordinates, including fused collision spaces. -/
theorem integrable_integral_finitePhaseStep {ι : Type*} [Fintype ι] {N : ℕ} (hN : 0 < N)
    (k : ι → ℕ) (S : Finset (ι → Site))
    (hS : ∀ z ∈ S, ∀ i, Even (z i 0 + z i 1 + (k i : ℤ)))
    (G : (ι → Site) → ℝ) (hzero : ∀ z ∉ S, G z = 0) :
    Integrable (fun x : ι → Plane => G (fun i => pairTwoFutureSampleSite N (k i) (x i))) ∧
      (∫ x : ι → Plane, G (fun i => pairTwoFutureSampleSite N (k i) (x i))) =
        (4 / (N : ℝ)) ^ Fintype.card ι * ∑ z ∈ S, G z := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (Fin (Fintype.card ι) → Site) ≃ (ι → Site) := Equiv.piCongrLeft (fun _ => Site) e
  let A := S.image E.symm
  let G' : (Fin (Fintype.card ι) → Site) → ℝ := fun z => G (E z)
  have hA : ∀ z ∈ A, ∀ i, Even (z i 0 + z i 1 + (k (e i) : ℤ)) := by
    intro z hz i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    simpa only [E, Equiv.piCongrLeft_symm_apply] using hS y hy (e i)
  have hG' (z : Fin (Fintype.card ι) → Site) (hz : z ∉ A) : G' z = 0 := by
    apply hzero (E z)
    intro hmem
    exact hz (Finset.mem_image.mpr ⟨E z, hmem, E.symm_apply_apply z⟩)
  obtain ⟨hint, hi⟩ := integrable_integral_configurationPhaseStep hN (fun i => k (e i)) A hA G' hG'
  have hsum : (∑ z ∈ A, G' z) = ∑ z ∈ S, G z := by
    change (∑ z ∈ S.image E.symm, G' z) = _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro z hz
      exact congrArg G (E.apply_symm_apply z)
    · intro x hx y hy hxy
      exact E.symm.injective hxy
  let ep : (Fin (Fintype.card ι) → Plane) ≃ᵐ (ι → Plane) :=
    MeasurableEquiv.piCongrLeft (fun _ => Plane) e
  have hep : MeasurePreserving ep := volume_measurePreserving_piCongrLeft (fun _ => Plane) e
  let H : (ι → Plane) → ℝ := fun x => G (fun i => pairTwoFutureSampleSite N (k i) (x i))
  have hcomp : H ∘ ep = fun x : Fin (Fintype.card ι) → Plane =>
      G' (fun i => pairTwoFutureSampleSite N (k (e i)) (x i)) := by
    funext x
    apply congrArg G
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp only [ep, MeasurableEquiv.coe_piCongrLeft, E, Equiv.piCongrLeft_apply_apply]
  refine ⟨(hep.integrable_comp_emb ep.measurableEmbedding).mp (hcomp ▸ hint), ?_⟩
  have heq := hep.integral_comp' H
  change (∫ x, (H ∘ ep) x) = (∫ y, H y) at heq
  rw [hcomp, hi, hsum] at heq
  exact heq.symm

end Critical2DKPZ.SHF.Moments
