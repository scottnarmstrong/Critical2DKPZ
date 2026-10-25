/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.IntegralLaw
public import Critical2DKPZ.Extensions.ScaleLimit.StationaryFubini

/-! # Finite spatial pieces of random fields

Finite collections of ball integrals can be treated as one vector-valued
integral. The deterministic spatial indicators in this construction do not
affect the finite-family law argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply finitely many deterministic linear maps on their assigned spatial sets. -/
def spatialPieces (A : ι → Set α) (L : ι → ℝ →L[ℝ] E)
    (g : α → Ω → ℝ) (y : α) (ω : Ω) : E :=
  ∑ i, (A i).indicator (fun y => L i (g y ω)) y

/-- The same operation on random `L¹` classes. -/
def spatialPiecesL1 (A : ι → Set α) (L : ι → ℝ →L[ℝ] E)
    (X : α → Lp ℝ 1 P) (y : α) : Lp E 1 P :=
  ∑ i, (A i).indicator (fun y => (L i).compLp (X y)) y

/-- The spatial-piece construction preserves strong measurability into `L¹`. -/
theorem stronglyMeasurable_spatialPiecesL1 (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (L : ι → ℝ →L[ℝ] E) {X : α → Lp ℝ 1 P} (hX : StronglyMeasurable X) :
    StronglyMeasurable (spatialPiecesL1 A L X) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact ((L i).compLpL 1 P).continuous.comp_stronglyMeasurable hX |>.indicator (hA i)

/-- Integrability of the `L¹` spatial-piece construction. -/
theorem integrable_spatialPiecesL1 (μ : Measure α) (A : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i)) (L : ι → ℝ →L[ℝ] E)
    {X : α → Lp ℝ 1 P} (hX : Integrable X μ) :
    Integrable (spatialPiecesL1 A L X) μ := by
  apply integrable_finsetSum
  intro i _
  exact (((L i).compLpL 1 P).integrable_comp hX).indicator (hA i)


/-- Joint integrability of the spatial pieces. -/
theorem integrable_spatialPieces (μ : Measure α) (A : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i)) (L : ι → ℝ →L[ℝ] E)
    {g : α → Ω → ℝ} (hg : Integrable (Function.uncurry g) (μ.prod P)) :
    Integrable (Function.uncurry (spatialPieces A L g)) (μ.prod P) := by
  apply integrable_finsetSum
  intro i _
  exact ((L i).integrable_comp hg).indicator ((hA i).preimage measurable_fst)

omit [MeasurableSpace α] in
/-- Almost everywhere identification of the class and the pointwise construction. -/
theorem spatialPiecesL1_ae_eq (A : ι → Set α) (L : ι → ℝ →L[ℝ] E)
    (X : α → Lp ℝ 1 P) (g : α → Ω → ℝ)
    (hX : ∀ y, (X y : Ω → ℝ) =ᵐ[P] g y) (y : α) :
    (spatialPiecesL1 A L X y : Ω → E) =ᵐ[P] spatialPieces A L g y := by
  classical
  apply (Lp.coeFn_fun_finsetSum Finset.univ _).trans
  have he (i : ι) :
      (((A i).indicator (fun y => (L i).compLp (X y)) y : Lp E 1 P) : Ω → E) =ᵐ[P]
        fun ω => (A i).indicator (fun y => L i (g y ω)) y := by
    by_cases hy : y ∈ A i
    · simp only [indicator_of_mem hy]
      filter_upwards [(L i).coeFn_compLp' (X y), hX y] with ω hω hrep
      exact hω.trans (congrArg (L i) hrep)
    · simp only [indicator_of_notMem hy]
      filter_upwards [Lp.coeFn_zero E 1 P] with ω hω
      exact hω
  filter_upwards [ae_all_iff.mpr he] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

omit [MeasurableSpace α] in
/-- Finite-family laws pass to deterministic spatial pieces of `L¹` classes. -/
theorem identDistrib_spatialPiecesL1
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (A : ι → Set α) (L : ι → ℝ →L[ℝ] E)
    (X Y : α → Lp ℝ 1 P) (f g : α → Ω → ℝ)
    (hX : ∀ y, (X y : Ω → ℝ) =ᵐ[P] f y)
    (hY : ∀ y, (Y y : Ω → ℝ) =ᵐ[P] g y)
    (hid : ∀ (n : ℕ) (y : Fin n → α),
      IdentDistrib (fun ω i => f (y i) ω) (fun ω i => g (y i) ω) P P)
    (n : ℕ) (y : Fin n → α) :
    IdentDistrib (fun ω i => spatialPiecesL1 A L X (y i) ω)
      (fun ω i => spatialPiecesL1 A L Y (y i) ω) P P := by
  have hm : Measurable (fun v : Fin n → ℝ => fun j =>
      ∑ i, (A i).indicator (fun _ => L i (v j)) (y j)) := by
    classical
    apply Measurable.of_eval
    intro j
    apply Finset.measurable_sum
    intro i _
    by_cases hy : y j ∈ A i
    · simpa only [indicator_of_mem hy, Function.comp_def] using (L i).continuous.measurable.comp (measurable_pi_apply j)
    · simpa only [indicator_of_notMem hy] using (measurable_const (a := (0 : E)))
  have hx : (fun ω i => spatialPiecesL1 A L X (y i) ω) =ᵐ[P]
      fun ω i => spatialPieces A L f (y i) ω := by
    filter_upwards [ae_all_iff.mpr (fun i => spatialPiecesL1_ae_eq A L X f hX (y i))] with ω hω
    exact funext hω
  have hy : (fun ω i => spatialPiecesL1 A L Y (y i) ω) =ᵐ[P]
      fun ω i => spatialPieces A L g (y i) ω := by
    filter_upwards [ae_all_iff.mpr (fun i => spatialPiecesL1_ae_eq A L Y g hY (y i))] with ω hω
    exact funext hω
  have hh := (hid n y).comp hm
  exact (IdentDistrib.of_ae_eq (Measurable.of_eval
    (fun i => (Lp.stronglyMeasurable (spatialPiecesL1 A L X (y i))).measurable)).aemeasurable hx).trans
      (hh.trans (IdentDistrib.of_ae_eq (Measurable.of_eval
        (fun i => (Lp.stronglyMeasurable (spatialPiecesL1 A L Y (y i))).measurable)).aemeasurable hy).symm)

end Critical2DKPZ.Extensions.ScaleLimit

end
