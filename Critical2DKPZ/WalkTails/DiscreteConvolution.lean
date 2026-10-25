/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Finite two-by-two Cauchy–Binet identity

The two-by-two minors of a finite kernel product are sums of products of minors of its factors.
This identity shows that convolution preserves nonnegative Toeplitz minors of size two.
-/

@[expose] public section

namespace Critical2DKPZ.WalkTails

/-- The two-by-two minor identity for finite sums.  It is a scalar form of the
Cauchy--Binet formula, with the ordered-pair sum accounting for both orders. -/
theorem finset_twoByTwo_minor_identity {ι : Type*} (s : Finset ι)
    (a b c d : ι → ℝ) :
    (∑ i ∈ s, a i * b i) * (∑ i ∈ s, c i * d i) -
        (∑ i ∈ s, a i * d i) * (∑ i ∈ s, c i * b i) =
      (1 / 2 : ℝ) *
        (∑ i ∈ s, ∑ j ∈ s,
          (a i * c j - a j * c i) * (b i * d j - d i * b j)) := by
  classical
  let T₁ := ∑ i ∈ s, ∑ j ∈ s, a i * c j * b i * d j
  let T₂ := ∑ i ∈ s, ∑ j ∈ s, a i * c j * d i * b j
  let T₃ := ∑ i ∈ s, ∑ j ∈ s, a j * c i * b i * d j
  let T₄ := ∑ i ∈ s, ∑ j ∈ s, a j * c i * d i * b j
  have hT₁ : T₁ = (∑ i ∈ s, a i * b i) * (∑ j ∈ s, c j * d j) := by
    dsimp [T₁]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hT₂ : T₂ = (∑ i ∈ s, a i * d i) * (∑ j ∈ s, c j * b j) := by
    dsimp [T₂]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hT₃ : T₃ = T₂ := by
    dsimp [T₃, T₂]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hT₄ : T₄ = T₁ := by
    dsimp [T₄, T₁]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hinner (i : ι) :
      (∑ j ∈ s, (a i * c j - a j * c i) * (b i * d j - d i * b j)) =
        (∑ j ∈ s, a i * c j * b i * d j) -
          (∑ j ∈ s, a i * c j * d i * b j) -
          (∑ j ∈ s, a j * c i * b i * d j) +
          (∑ j ∈ s, a j * c i * d i * b j) := by
    calc
      _ = ∑ j ∈ s,
          (a i * c j * b i * d j - a i * c j * d i * b j -
            a j * c i * b i * d j + a j * c i * d i * b j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hexpand :
      (∑ i ∈ s, ∑ j ∈ s,
        (a i * c j - a j * c i) * (b i * d j - d i * b j)) =
        T₁ - T₂ - T₃ + T₄ := by
    calc
      _ = ∑ i ∈ s,
          ((∑ j ∈ s, a i * c j * b i * d j) -
            (∑ j ∈ s, a i * c j * d i * b j) -
            (∑ j ∈ s, a j * c i * b i * d j) +
            (∑ j ∈ s, a j * c i * d i * b j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hinner i
      _ = T₁ - T₂ - T₃ + T₄ := by
          dsimp [T₁, T₂, T₃, T₄]
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hexpand, hT₃, hT₄, hT₁, hT₂]
  ring

/-- Finite kernel composition preserves nonnegative two-by-two minors. -/
theorem finiteComposition_preserves_TP2
    {α β ι : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder ι]
    (s : Finset ι) (A : α → ι → ℝ) (B : ι → β → ℝ)
    (hA : ∀ ⦃i j : α⦄ ⦃x y : ι⦄, i < j → x < y →
      0 ≤ A i x * A j y - A i y * A j x)
    (hB : ∀ ⦃x y : ι⦄ ⦃k l : β⦄, x < y → k < l →
      0 ≤ B x k * B y l - B x l * B y k)
    {i j : α} {k l : β} (hij : i < j) (hkl : k < l) :
    0 ≤ (∑ x ∈ s, A i x * B x k) * (∑ x ∈ s, A j x * B x l) -
      (∑ x ∈ s, A i x * B x l) * (∑ x ∈ s, A j x * B x k) := by
  have hterm : ∀ x ∈ s, ∀ y ∈ s,
      0 ≤ (A i x * A j y - A i y * A j x) *
        (B x k * B y l - B x l * B y k) := by
    intro x hx y hy
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · exact mul_nonneg (hA hij hxy) (hB hxy hkl)
    · subst y
      simp
    · have hA' := hA hij hyx
      have hB' := hB hyx hkl
      have hAeq : A i x * A j y - A i y * A j x =
          -(A i y * A j x - A i x * A j y) := by ring
      have hBeq : B x k * B y l - B x l * B y k =
          -(B y k * B x l - B y l * B x k) := by ring
      rw [hAeq, hBeq]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hA') (neg_nonpos.mpr hB')
  have hsum : 0 ≤ ∑ x ∈ s, ∑ y ∈ s,
      (A i x * A j y - A i y * A j x) *
        (B x k * B y l - B x l * B y k) :=
    Finset.sum_nonneg fun x hx => Finset.sum_nonneg fun y hy => hterm x hx y hy
  have hident := finset_twoByTwo_minor_identity s
    (fun x => A i x) (fun x => B x k) (fun x => A j x) (fun x => B x l)
  calc
    0 ≤ (1 / 2 : ℝ) * ∑ x ∈ s, ∑ y ∈ s,
        (A i x * A j y - A i y * A j x) *
          (B x k * B y l - B x l * B y k) := mul_nonneg (by positivity) hsum
    _ = _ := hident.symm

/-- The convolution sum restricted to the finite index set `s`. -/
def finiteConvolution (s : Finset ℤ) (f g : ℤ → ℝ) (z : ℤ) : ℝ :=
  ∑ a ∈ s, f a * g (z - a)

/-- Every two-by-two minor of the sequence's Toeplitz matrix is nonnegative. -/
def toeplitzTP2 (f : ℤ → ℝ) : Prop :=
  ∀ ⦃i j k l : ℤ⦄, i < j → k < l →
    0 ≤ f (k - i) * f (l - j) - f (l - i) * f (k - j)

/-- Finite convolution preserves nonnegative Toeplitz minors of size two when the summation set
contains the first factor's support. -/
theorem finiteConvolution_toeplitzTP2 (s : Finset ℤ) (f g : ℤ → ℝ)
    (hfsupp : ∀ a, a ∉ s → f a = 0)
    (hf : toeplitzTP2 f) (hg : toeplitzTP2 g) :
    toeplitzTP2 (finiteConvolution s f g) := by
  classical
  intro i j k l hij hkl
  let L : Finset ℤ := s.image (fun a => i + a)
  let R : Finset ℤ := s.image (fun a => j + a)
  let T : Finset ℤ := L ∪ R
  have hshift (r c : ℤ) :
      (∑ t ∈ s.image (fun a => r + a), f (t - r) * g (c - t)) =
        finiteConvolution s f g (c - r) := by
    unfold finiteConvolution
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      congr 2 <;> ring
    · intro a ha b hb hab
      exact add_left_cancel hab
  have hrowI (c : ℤ) :
      (∑ t ∈ T, f (t - i) * g (c - t)) =
        finiteConvolution s f g (c - i) := by
    have hsub : L ⊆ T := Finset.subset_union_left
    have hzero : ∀ t ∈ T, t ∉ L → f (t - i) * g (c - t) = 0 := by
      intro t ht htL
      have htR : t ∈ R := (Finset.mem_union.mp ht).resolve_left htL
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp htR
      have hnot : j + a - i ∉ s := by
        intro hs
        apply htL
        exact Finset.mem_image.mpr ⟨j + a - i, hs, by omega⟩
      rw [hfsupp _ hnot, zero_mul]
    calc
      _ = ∑ t ∈ L, f (t - i) * g (c - t) := (Finset.sum_subset hsub hzero).symm
      _ = finiteConvolution s f g (c - i) := hshift i c
  have hrowJ (c : ℤ) :
      (∑ t ∈ T, f (t - j) * g (c - t)) =
        finiteConvolution s f g (c - j) := by
    have hsub : R ⊆ T := Finset.subset_union_right
    have hzero : ∀ t ∈ T, t ∉ R → f (t - j) * g (c - t) = 0 := by
      intro t ht htR
      have htL : t ∈ L := (Finset.mem_union.mp ht).resolve_right htR
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp htL
      have hnot : i + a - j ∉ s := by
        intro hs
        apply htR
        exact Finset.mem_image.mpr ⟨i + a - j, hs, by omega⟩
      rw [hfsupp _ hnot, zero_mul]
    calc
      _ = ∑ t ∈ R, f (t - j) * g (c - t) := (Finset.sum_subset hsub hzero).symm
      _ = finiteConvolution s f g (c - j) := hshift j c
  have hTP := finiteComposition_preserves_TP2 T
    (fun r t => f (t - r)) (fun t c => g (c - t))
    (by
      intro r r' t t' hrr htt
      exact hf hrr htt)
    (by
      intro t t' c c' htt hcc
      exact hg htt hcc)
    hij hkl
  rw [← hrowI k, ← hrowJ l, ← hrowI l, ← hrowJ k]
  exact hTP

end Critical2DKPZ.WalkTails
