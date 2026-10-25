/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FiniteOperators
import Mathlib.Tactic

/-! # Constrained subsets of independent finite parameter choices -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- A finite family of parameters for one kernel in a word. -/
structure CCR25KernelParameterFamily (δ α : Type*) where
  parameters : Finset δ
  kernel : δ → α → α → ℝ

/-- Apply the word after summing each parameter independently. -/
def finiteKernelParameterFamilyWordApply {δ α : Type*}
    (s : Finset α) : List (CCR25KernelParameterFamily δ α) →
      (α → ℝ) → α → ℝ
  | [], f, x => f x
  | family :: families, f, x =>
      ∑ d ∈ family.parameters, ∑ y ∈ s,
        family.kernel d x y * finiteKernelParameterFamilyWordApply s families f y

/-- All independent parameter lists for a sequence of kernel families. -/
noncomputable def ccr25ParameterChoices {δ α : Type*} [DecidableEq δ] :
    List (CCR25KernelParameterFamily δ α) → Finset (List δ)
  | [] => {[]}
  | family :: families =>
      family.parameters.biUnion fun d =>
        (ccr25ParameterChoices families).image fun ds => d :: ds

/-- The kernel word chosen by a parameter list. -/
def ccr25ParameterChoiceKernelWord {δ α : Type*} :
    List (CCR25KernelParameterFamily δ α) → List δ → List (α → α → ℝ)
  | [], _ => []
  | family :: families, d :: ds =>
      family.kernel d :: ccr25ParameterChoiceKernelWord families ds
  | _ :: _, [] => []

/-- The sum over all parameter lists equals the independent parameter-family
word action. -/
theorem ccr25ParameterChoices_sum_kernelWord_eq_familyApply
    {δ α : Type*} [DecidableEq δ] (s : Finset α) :
    ∀ (families : List (CCR25KernelParameterFamily δ α))
      (f : α → ℝ) (x : α),
      (∑ ds ∈ ccr25ParameterChoices families,
        finiteKernelWordApply s
          (ccr25ParameterChoiceKernelWord families ds) f x) =
        finiteKernelParameterFamilyWordApply s families f x := by
  intro families
  induction families with
  | nil =>
      intro f x
      simp [ccr25ParameterChoices, ccr25ParameterChoiceKernelWord,
        finiteKernelWordApply, finiteKernelParameterFamilyWordApply]
  | cons family families ih =>
      intro f x
      classical
      let F : δ → Finset (List δ) := fun d =>
        (ccr25ParameterChoices families).image fun ds => d :: ds
      have hdis : Set.PairwiseDisjoint (↑family.parameters) F := by
        intro d hd d' hd' hne
        apply Finset.disjoint_left.mpr
        intro ds hds hds'
        obtain ⟨tail, htail, heq⟩ := Finset.mem_image.mp (by simpa [F] using hds)
        obtain ⟨tail', htail', heq'⟩ := Finset.mem_image.mp (by simpa [F] using hds')
        have hhead := congrArg List.head? (heq.trans heq'.symm)
        simp only [List.head?_cons] at hhead
        exact hne (Option.some.inj hhead)
      change (∑ ds ∈ family.parameters.biUnion F,
          finiteKernelWordApply s
            (ccr25ParameterChoiceKernelWord (family :: families) ds) f x) = _
      rw [Finset.sum_biUnion hdis]
      simp only [F, finiteKernelParameterFamilyWordApply]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_image (fun tail htail tail' htail' heq =>
        (List.cons.inj heq).2)]
      simp only [ccr25ParameterChoiceKernelWord, finiteKernelWordApply]
      calc
        (∑ tail ∈ ccr25ParameterChoices families,
            ∑ y ∈ s, family.kernel d x y *
              finiteKernelWordApply s
                (ccr25ParameterChoiceKernelWord families tail) f y) =
          ∑ y ∈ s, family.kernel d x y *
            (∑ tail ∈ ccr25ParameterChoices families,
              finiteKernelWordApply s
                (ccr25ParameterChoiceKernelWord families tail) f y) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.mul_sum]
        _ = ∑ y ∈ s, family.kernel d x y *
            finiteKernelParameterFamilyWordApply s families f y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [ih f y]

/-- Summing over a constrained subset of parameter lists is bounded by the
full independent parameter-family word when all full-word contributions are
nonnegative. -/
theorem ccr25ParameterChoices_subset_sum_kernelWord_le_familyApply
    {δ α : Type*} [DecidableEq δ] (s : Finset α)
    (families : List (CCR25KernelParameterFamily δ α))
    (S : Finset (List δ)) (hS : S ⊆ ccr25ParameterChoices families)
    (f : α → ℝ) (x : α)
    (hnonneg : ∀ ds ∈ ccr25ParameterChoices families,
      0 ≤ finiteKernelWordApply s
        (ccr25ParameterChoiceKernelWord families ds) f x) :
    (∑ ds ∈ S,
      finiteKernelWordApply s
        (ccr25ParameterChoiceKernelWord families ds) f x) ≤
      finiteKernelParameterFamilyWordApply s families f x := by
  calc
    (∑ ds ∈ S,
        finiteKernelWordApply s
          (ccr25ParameterChoiceKernelWord families ds) f x) ≤
      ∑ ds ∈ ccr25ParameterChoices families,
        finiteKernelWordApply s
          (ccr25ParameterChoiceKernelWord families ds) f x :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (by
        intro ds hds hnot
        exact hnonneg ds hds)
    _ = finiteKernelParameterFamilyWordApply s families f x :=
      ccr25ParameterChoices_sum_kernelWord_eq_familyApply s families f x

end Critical2DKPZ.MomentBounds

end
