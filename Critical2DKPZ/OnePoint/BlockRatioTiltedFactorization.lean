/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioPairFactorization
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! # Independent factors for tilted pair integrals -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- The inverse block-mass product attached to a component or uncovered block. -/
noncomputable def pairFactorInverseProduct {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (F G : Finset (ℕ × ℕ)) (x : pairFactorIndex r s F G) (ω : Disorder) : ℝ := by
  classical
  cases x with
  | inl c => exact ∏ i ∈ Finset.Icc c.1.1 c.1.2, (blockMass β t i ω)⁻¹
  | inr i => exact (blockMass β t i.1 ω)⁻¹

/-- A pair factor weighted by the inverse masses on its own block span. -/
noncomputable def pairWeightedFactorValue {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (F G : Finset (ℕ × ℕ)) (x : pairFactorIndex r s F G) (ω : Disorder) : ℝ :=
  pairFactorValue β t F G x ω * pairFactorInverseProduct β t F G x ω

/-- The local inverse-mass product is measurable on the factor's time block. -/
theorem measurable_pairFactorInverseProduct_block {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {F G : Finset (ℕ × ℕ)} (x : pairFactorIndex r s F G) :
    Measurable[Gaussian.disorderBlock
      (t (pairComponentStart r s F G x - 1))
      (t (pairComponentStop r s F G x))]
      (pairFactorInverseProduct β t F G x) := by
  classical
  cases x with
  | inl c =>
      change Measurable[Gaussian.disorderBlock (t (c.1.1 - 1)) (t c.1.2)]
        (fun ω => ∏ i ∈ Finset.Icc c.1.1 c.1.2, (blockMass β t i ω)⁻¹)
      apply Finset.measurable_prod
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hstart : t (c.1.1 - 1) ≤ t (i - 1) := ht (by omega)
      have hstop : t i ≤ t c.1.2 := ht hi'.2
      exact ((measurable_blockMass β t i).mono
        (Gaussian.disorderBlock_mono hstart hstop) le_rfl).inv
  | inr i =>
      change Measurable[Gaussian.disorderBlock (t (i.1 - 1)) (t i.1)]
        (fun ω => (blockMass β t i.1 ω)⁻¹)
      exact (measurable_blockMass β t i.1).inv

/-- The local inverse-mass products are independent across component spans. -/
theorem pairFactorInverseProduct_iIndepFun {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {F G : Finset (ℕ × ℕ)} :
    iIndepFun (pairFactorInverseProduct (r := r) (s := s) β t F G) disorderLaw := by
  let a := pairComponentStart r s F G
  let b := pairComponentStop r s F G
  have hdisj : Pairwise (fun x y => Disjoint (Set.Ioc (t (a x - 1)) (t (b x)))
      (Set.Ioc (t (a y - 1)) (t (b y)))) := by
    intro x y hxy
    exact pairFactorIndex_time_disjoint t ht hxy
  have hmeas : ∀ x : pairFactorIndex r s F G,
      Measurable[Gaussian.disorderBlock (t (a x - 1)) (t (b x))]
        (pairFactorInverseProduct β t F G x) := by
    intro x
    exact measurable_pairFactorInverseProduct_block β t ht x
  exact Polymer.independent_of_blockMeasurable (fun x => t (a x - 1))
    (fun x => t (b x)) hdisj (pairFactorInverseProduct β t F G) hmeas

/-- Integrals of the independent inverse-mass factors split when each factor is integrable. -/
theorem integral_pairFactorInverseProduct_prod_eq_prod_integral {r s : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t) {F G : Finset (ℕ × ℕ)}
    (hInt : ∀ x : pairFactorIndex r s F G,
      Integrable (pairFactorInverseProduct β t F G x) disorderLaw) :
    ∫ ω, ∏ x : pairFactorIndex r s F G,
        pairFactorInverseProduct β t F G x ω ∂disorderLaw =
      ∏ x : pairFactorIndex r s F G,
        ∫ ω, pairFactorInverseProduct β t F G x ω ∂disorderLaw := by
  have hInd := pairFactorInverseProduct_iIndepFun (r := r) (s := s) β t ht
    (F := F) (G := G)
  exact hInd.integral_fun_prod_eq_prod_integral fun x => (hInt x).aestronglyMeasurable

/-- The weighted factors remain measurable on their disjoint time spans. -/
theorem measurable_pairWeightedFactorValue_block {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {F G : Finset (ℕ × ℕ)}
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s)
    (x : pairFactorIndex r s F G) :
    Measurable[Gaussian.disorderBlock
      (t (pairComponentStart r s F G x - 1))
      (t (pairComponentStop r s F G x))]
      (pairWeightedFactorValue β t F G x) := by
  exact (measurable_pairFactorValue_block β t ht hF hG x).mul
    (measurable_pairFactorInverseProduct_block β t ht x)

/-- The weighted component and uncovered-block factors are jointly independent. -/
theorem pairWeightedFactorValue_iIndepFun {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {F G : Finset (ℕ × ℕ)}
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s) :
    iIndepFun (pairWeightedFactorValue (r := r) (s := s) β t F G) disorderLaw := by
  let a := pairComponentStart r s F G
  let b := pairComponentStop r s F G
  have hdisj : Pairwise (fun x y => Disjoint (Set.Ioc (t (a x - 1)) (t (b x)))
      (Set.Ioc (t (a y - 1)) (t (b y)))) := by
    intro x y hxy
    exact pairFactorIndex_time_disjoint t ht hxy
  have hmeas : ∀ x : pairFactorIndex r s F G,
      Measurable[Gaussian.disorderBlock (t (a x - 1)) (t (b x))]
        (pairWeightedFactorValue β t F G x) := by
    intro x
    exact measurable_pairWeightedFactorValue_block β t ht hF hG x
  exact Polymer.independent_of_blockMeasurable (fun x => t (a x - 1))
    (fun x => t (b x)) hdisj (pairWeightedFactorValue β t F G) hmeas

/-- The product of local inverse-mass factors reconstructs the full inverse-mass product. -/
theorem pairFactorInverseProduct_prod_eq_global {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (F G : Finset (ℕ × ℕ)) (ω : Disorder) :
    (∏ x : pairFactorIndex r s F G, pairFactorInverseProduct β t F G x ω) =
      ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ := by
  classical
  have hCattach (f : ℕ × ℕ → ℝ) :
      ∏ c : pairComponentIndex r s F G, f c.1 =
        ∏ c ∈ pairComponents r s F G, f c := by
    rw [Finset.univ_eq_attach, Finset.prod_attach]
  have hUattach (f : ℕ → ℝ) :
      ∏ i : pairUncoveredIndex r s F G, f i.1 =
        ∏ i ∈ pairUncoveredBlocks r s F G, f i := by
    rw [Finset.univ_eq_attach, Finset.prod_attach]
  rw [Fintype.prod_sum_type]
  simp only [pairFactorInverseProduct]
  have hC :
      (∏ c : pairComponentIndex r s F G,
        ∏ i ∈ Finset.Icc c.1.1 c.1.2, (blockMass β t i ω)⁻¹) =
        ∏ c ∈ pairComponents r s F G,
          ∏ i ∈ Finset.Icc c.1 c.2, (blockMass β t i ω)⁻¹ := by
    simpa only [pairComponentIndex] using hCattach
      (fun c => ∏ i ∈ Finset.Icc c.1 c.2, (blockMass β t i ω)⁻¹)
  have hU :
      (∏ i : pairUncoveredIndex r s F G, (blockMass β t i.1 ω)⁻¹) =
        ∏ i ∈ pairUncoveredBlocks r s F G, (blockMass β t i ω)⁻¹ := by
    simpa only [pairUncoveredIndex] using hUattach
      (fun i => (blockMass β t i ω)⁻¹)
  rw [hC, hU]
  exact (pairBlockwise_prod_eq_components_mul_uncovered F G
    (fun i => (blockMass β t i ω)⁻¹)).symm

/-- The weighted factors reconstruct the good-set pair integrand with its inverse-mass density. -/
theorem pairWeightedFactorValue_prod_eq_global_indicator {r s : ℕ} (β : ℝ)
    (t : ℕ → ℕ) {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r)
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s)
    (ω : Disorder) :
    ∏ x : pairFactorIndex r s F G, pairWeightedFactorValue β t F G x ω =
      Set.indicator (blockGoodSet β t r s)
        (fun ω => familyTerm β t F ω * familyTerm β t G ω *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹) ω := by
  classical
  simp only [pairWeightedFactorValue]
  rw [Finset.prod_mul_distrib, pairFactorValue_prod_eq_global_indicator β t hr hF hG,
    pairFactorInverseProduct_prod_eq_global β t F G ω]
  by_cases hω : ω ∈ blockGoodSet β t r s
  · simp [Set.indicator_of_mem hω, mul_assoc]
  · simp [Set.indicator_of_notMem hω]

/-- Integrals of the independent tilted factors split when each factor is integrable. -/
theorem integral_pairWeightedFactor_prod_eq_prod_integral {r s : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s)
    (hInt : ∀ x : pairFactorIndex r s F G,
      Integrable (pairWeightedFactorValue β t F G x) disorderLaw) :
    ∫ ω, ∏ x : pairFactorIndex r s F G,
        pairWeightedFactorValue β t F G x ω ∂disorderLaw =
      ∏ x : pairFactorIndex r s F G,
        ∫ ω, pairWeightedFactorValue β t F G x ω ∂disorderLaw := by
  have hInd := pairWeightedFactorValue_iIndepFun (r := r) (s := s) β t ht hF hG
  exact hInd.integral_fun_prod_eq_prod_integral fun x => (hInt x).aestronglyMeasurable

/-- The tilted good-set pair integral factors over the components and uncovered blocks. -/
theorem setIntegral_familyTermPair_mul_invBlockProduct_eq_pairWeightedIntegrals {r s : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t) (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s)
    (hInt : ∀ x : pairFactorIndex r s F G,
      Integrable (pairWeightedFactorValue β t F G x) disorderLaw) :
    ∫ ω in blockGoodSet β t r s,
        familyTerm β t F ω * familyTerm β t G ω *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw =
      ∏ x : pairFactorIndex r s F G,
        ∫ ω, pairWeightedFactorValue β t F G x ω ∂disorderLaw := by
  classical
  have hgoodMeas : MeasurableSet (blockGoodSet β t r s) :=
    measurableSet_blockGoodSet β t r s
  rw [← integral_indicator hgoodMeas]
  calc
    ∫ ω, (blockGoodSet β t r s).indicator
        (fun ω => familyTerm β t F ω * familyTerm β t G ω *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹) ω ∂disorderLaw =
      ∫ ω, ∏ x : pairFactorIndex r s F G,
        pairWeightedFactorValue β t F G x ω ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω =>
            (pairWeightedFactorValue_prod_eq_global_indicator β t hr hF hG ω).symm
    _ = ∏ x : pairFactorIndex r s F G,
        ∫ ω, pairWeightedFactorValue β t F G x ω ∂disorderLaw :=
      integral_pairWeightedFactor_prod_eq_prod_integral β t ht hF hG hInt

end Critical2DKPZ.OnePoint

end
