/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! # The next collision diagonal is null in a distinct collision space -/

@[expose] public noncomputable section

open MeasureTheory Measure
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

private def wordLimitFusedCoordinate {h : ℕ} (α : CollisionPair h) (i : Fin h) :
    FusedConfiguration α →ₗ[ℝ] Plane where
  toFun z := collisionEmbedding α z i
  map_add' := by
    intro z w
    simp only [collisionEmbedding]
    split_ifs <;> rfl
  map_smul' := by
    intro c z
    simp only [collisionEmbedding]
    split_ifs <;> rfl

private theorem wordLimit_distinctPairs_not_both_inside {h : ℕ}
    (α β : CollisionPair h) (hαβ : α ≠ β) :
    ¬ ((β.1.1 = α.1.1 ∨ β.1.1 = α.1.2) ∧
      (β.1.2 = α.1.1 ∨ β.1.2 = α.1.2)) := by
  rintro ⟨h0, h1⟩
  have ha := α.2
  have hb := β.2
  have he0 : β.1.1 = α.1.1 := by rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
  have he1 : β.1.2 = α.1.2 := by rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
  apply hαβ
  apply Subtype.ext
  exact (Prod.ext he0 he1).symm

/-- For distinct consecutive pairs, the intermediate configuration lies off
the next pair's diagonal almost everywhere on the first collision space. -/
theorem ae_collisionEmbedding_pair_ne {h : ℕ} (α β : CollisionPair h) (hαβ : α ≠ β) :
    ∀ᵐ z : FusedConfiguration α,
      collisionEmbedding α z β.1.1 ≠ collisionEmbedding α z β.1.2 := by
  classical
  let L := wordLimitFusedCoordinate α β.1.1 - wordLimitFusedCoordinate α β.1.2
  obtain ⟨p, hp⟩ := exists_ne (0 : Plane)
  have hwitness : ∃ z : FusedConfiguration α, L z ≠ 0 := by
    have hne : β.1.2 ≠ β.1.1 := ne_of_gt β.2
    by_cases h0 : β.1.1 = α.1.1 ∨ β.1.1 = α.1.2
    · have h1 : ¬ (β.1.2 = α.1.1 ∨ β.1.2 = α.1.2) := by
        intro h1
        exact wordLimit_distinctPairs_not_both_inside α β hαβ ⟨h0, h1⟩
      refine ⟨(p, fun _ => 0), ?_⟩
      simpa [L, wordLimitFusedCoordinate, collisionEmbedding, h0, h1] using hp
    · refine ⟨(0, fun i => if i.1 = β.1.1 then p else 0), ?_⟩
      have hfirst : collisionEmbedding α
          (0, fun i : Spectator α => if i.1 = β.1.1 then p else 0) β.1.1 = p := by
        simp [collisionEmbedding, h0]
      have hsecond : collisionEmbedding α
          (0, fun i : Spectator α => if i.1 = β.1.1 then p else 0) β.1.2 = 0 := by
        simp only [collisionEmbedding]
        split_ifs <;> simp_all
      change collisionEmbedding α _ β.1.1 - collisionEmbedding α _ β.1.2 ≠ 0
      rw [hfirst, hsecond, sub_zero]
      exact hp
  have hproper : L.ker ≠ ⊤ := by
    intro heq
    obtain ⟨z, hz⟩ := hwitness
    have hzmem : z ∈ L.ker := by rw [heq]; trivial
    exact hz hzmem
  have : IsAddHaarMeasure (volume : Measure Plane) := by
    rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).addHaar_eq_volume]
    infer_instance
  have : IsAddHaarMeasure (volume : Measure (Spectator α → Plane)) := by infer_instance
  have : IsAddHaarMeasure (volume : Measure (FusedConfiguration α)) := by
    change IsAddHaarMeasure ((volume : Measure Plane).prod (volume : Measure (Spectator α → Plane)))
    infer_instance
  have hnull := Measure.addHaar_submodule (volume : Measure (FusedConfiguration α)) L.ker hproper
  have hae : ∀ᵐ z : FusedConfiguration α, L z ≠ 0 := by
    exact compl_mem_ae_iff.mpr hnull
  filter_upwards [hae] with z hz
  exact sub_ne_zero.mp hz

/-- The initial pair diagonal is null for the full configuration volume, as
needed when moving-start limits are integrated over compact initial tests. -/
theorem ae_configuration_pair_ne {h : ℕ} (α : CollisionPair h) :
    ∀ᵐ x : Configuration h, x α.1.1 ≠ x α.1.2 := by
  classical
  let L : Configuration h →ₗ[ℝ] Plane := LinearMap.proj (R := ℝ) (φ := fun _ : Fin h => Plane) α.1.1 -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin h => Plane) α.1.2
  obtain ⟨p, hp⟩ := exists_ne (0 : Plane)
  have hproper : L.ker ≠ ⊤ := by
    intro heq
    let x : Configuration h := fun i => if i = α.1.1 then p else 0
    have hx : x ∈ L.ker := by rw [heq]; trivial
    have hne : α.1.2 ≠ α.1.1 := ne_of_gt α.2
    have hLx : L x = p := by simp [L, x, hne]
    exact hp (hLx.symm.trans hx)
  have : IsAddHaarMeasure (volume : Measure Plane) := by
    rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).addHaar_eq_volume]
    infer_instance
  have : IsAddHaarMeasure (volume : Measure (Configuration h)) := by infer_instance
  have hnull := Measure.addHaar_submodule (volume : Measure (Configuration h)) L.ker hproper
  have hae : ∀ᵐ x : Configuration h, L x ≠ 0 := compl_mem_ae_iff.mpr hnull
  filter_upwards [hae] with x hx
  exact sub_ne_zero.mp hx

end Critical2DKPZ.SHF.Moments
