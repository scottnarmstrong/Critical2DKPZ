/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpatialPieces

/-! # Laws of finite families of set integrals

The vector integral of finitely many spatial pieces identifies the joint law
of their set integrals. This is the integration step in the stationary maximal
inequality; one-point laws alone do not suffice for it.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace α] [IsProbabilityMeasure P] [MeasurableSpace Ω] in
/-- A coordinate of the spatial-piece vector is the corresponding indicator. -/
theorem spatialPieces_single_apply (A : ι → Set α) (g : α → Ω → ℝ)
    (y : α) (ω : Ω) (j : ι) :
    spatialPieces A (fun i => ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i) g y ω j =
      (A j).indicator (fun y => g y ω) y := by
  classical
  change (∑ i, (A i).indicator
    (fun y => ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i (g y ω)) y) j = _
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hy : y ∈ A j
    · simp only [indicator_of_mem hy, ContinuousLinearMap.single_apply, Pi.single_eq_same]
    · simp only [indicator_of_notMem hy, Pi.zero_apply]
  · intro i _ hij
    by_cases hy : y ∈ A i
    · simp only [indicator_of_mem hy, ContinuousLinearMap.single_apply,
        Pi.single_eq_of_ne hij.symm]
    · simp only [indicator_of_notMem hy, Pi.zero_apply]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- The integral of the class-valued spatial pieces represents the vector of
pathwise set integrals. -/
theorem integral_spatialPiecesL1_ae_eq (μ : Measure α) [SFinite μ]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (X : α → Lp ℝ 1 P) (g : α → Ω → ℝ)
    (hXi : Integrable X μ) (hg : Integrable (Function.uncurry g) (μ.prod P))
    (hX : ∀ y, (X y : Ω → ℝ) =ᵐ[P] g y) :
    ((∫ y, spatialPiecesL1 A
        (fun i => ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i) X y ∂μ :
        Lp (ι → ℝ) 1 P) : Ω → ι → ℝ) =ᵐ[P]
      fun ω i => ∫ y in A i, g y ω ∂μ := by
  classical
  let L := fun i => ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i
  have hgi := integrable_spatialPieces μ A hA L hg
  have he := integral_L1_ae_eq μ (spatialPiecesL1 A L X)
    (integrable_spatialPiecesL1 μ A hA L hXi) hgi
    (spatialPiecesL1_ae_eq A L X g hX)
  filter_upwards [he, hgi.prod_left_ae] with ω hω hi
  rw [hω]
  ext j
  have hp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).integral_comp_comm hi
  change (∫ y, spatialPieces A L g y ω j ∂μ) =
    (∫ y, spatialPieces A L g y ω ∂μ) j at hp
  change (∫ y, spatialPieces A L g y ω ∂μ) j = _
  rw [← hp]
  simp_rw [show L = (fun i => ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i) from rfl,
    spatialPieces_single_apply]
  exact integral_indicator (hA j)

/-- Equality of all finite-family laws of jointly integrable fields passes to
every finite family of spatial set integrals. -/
theorem identDistrib_setIntegrals [Nonempty α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (X Y : α → Lp ℝ 1 P) (f g : α → Ω → ℝ)
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y μ)
    (hfi : Integrable (Function.uncurry f) (μ.prod P))
    (hgi : Integrable (Function.uncurry g) (μ.prod P))
    (hXrep : ∀ y, (X y : Ω → ℝ) =ᵐ[P] f y)
    (hYrep : ∀ y, (Y y : Ω → ℝ) =ᵐ[P] g y)
    (hid : ∀ (n : ℕ) (y : Fin n → α),
      IdentDistrib (fun ω i => f (y i) ω) (fun ω i => g (y i) ω) P P) :
    IdentDistrib (fun ω i => ∫ y in A i, f y ω ∂μ)
      (fun ω i => ∫ y in A i, g y ω ∂μ) P P := by
  classical
  let L := fun i => ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i
  have h := identDistrib_integral_L1 μ (spatialPiecesL1 A L X) (spatialPiecesL1 A L Y)
    (stronglyMeasurable_spatialPiecesL1 A hA L hX)
    (stronglyMeasurable_spatialPiecesL1 A hA L hY)
    (integrable_spatialPiecesL1 μ A hA L hXi)
    (integrable_spatialPiecesL1 μ A hA L hYi)
    (identDistrib_spatialPiecesL1 A L X Y f g hXrep hYrep hid)
  have hx := integral_spatialPiecesL1_ae_eq μ A hA X f hXi hfi hXrep
  have hy := integral_spatialPiecesL1_ae_eq μ A hA Y g hYi hgi hYrep
  exact (IdentDistrib.of_ae_eq h.aemeasurable_fst hx).symm.trans
    (h.trans (IdentDistrib.of_ae_eq h.aemeasurable_snd hy))

end Critical2DKPZ.Extensions.ScaleLimit

end
