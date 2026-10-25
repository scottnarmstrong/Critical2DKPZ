/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.LZ21Finite
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! # Absolute-sum LZ21 estimate for equality-stratum-supported functions -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The explicit finite LZ21 constant obtained from the elementary lattice row bound. -/
noncomputable def lz21BilinearConstant (h : ℕ) (p q : ℝ) : ℝ :=
  4 ^ ((h : ℝ) - 1) * 4 * (9 : ℝ) ^ (h - 3) * 1188 * (p * q)

/-- Absolute convergence and the LZ21 bilinear estimate on two admissible
equality strata. The functions are extended by zero outside their strata; the
statement is an unconditional sum over the full lattice configuration space. -/
theorem summable_abs_replicaGreen_bilinear {h : ℕ}
    (I J : ReplicaPartition h) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcommon : ∀ α : DeltaBose.CollisionPair h,
      ¬(I = pairPartition α ∧ J = pairPartition α))
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (f g : LatticeConfiguration h → ℝ)
    (hfSupport : ∀ x, ¬ IsEqualityConfiguration I x → f x = 0)
    (hgSupport : ∀ y, ¬ IsEqualityConfiguration J y → g y = 0)
    (hf : Summable (fun x => |f x| ^ p)) (hg : Summable (fun y => |g y| ^ q)) :
    Summable (fun z : LatticeConfiguration h × LatticeConfiguration h =>
      |f z.1| * replicaGreenKernel z.1 z.2 * |g z.2|) ∧
    (∑' z : LatticeConfiguration h × LatticeConfiguration h,
      |f z.1| * replicaGreenKernel z.1 z.2 * |g z.2|) ≤
      lz21BilinearConstant h p q *
        (∑' x, |f x| ^ p) ^ (1 / p) * (∑' y, |g y| ^ q) ^ (1 / q) := by
  classical
  let F : LatticeConfiguration h × LatticeConfiguration h → ℝ := fun z =>
    |f z.1| * replicaGreenKernel z.1 z.2 * |g z.2|
  let TF : ℝ := ∑' x : LatticeConfiguration h, |f x| ^ p
  let TG : ℝ := ∑' y : LatticeConfiguration h, |g y| ^ q
  let C : ℝ := lz21BilinearConstant h p q
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hpInv : 0 ≤ 1 / p := (one_div_pos.mpr hp).le
  have hqInv : 0 ≤ 1 / q := (one_div_pos.mpr hq).le
  have hfn (x : LatticeConfiguration h) : 0 ≤ |f x| ^ p :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hgn (y : LatticeConfiguration h) : 0 ≤ |g y| ^ q :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hTF : 0 ≤ TF := tsum_nonneg hfn
  have hTG : 0 ≤ TG := tsum_nonneg hgn
  have hFnonneg (z : LatticeConfiguration h × LatticeConfiguration h) : 0 ≤ F z := by
    dsimp [F]
    exact mul_nonneg
      (mul_nonneg (abs_nonneg _) (replicaGreenKernel_pos z.1 z.2).le) (abs_nonneg _)
  have hfinite (u : Finset (LatticeConfiguration h × LatticeConfiguration h)) :
      (∑ z ∈ u, F z) ≤ C * TF ^ (1 / p) * TG ^ (1 / q) := by
    let v := u.filter (fun z => IsEqualityConfiguration I z.1 ∧
      IsEqualityConfiguration J z.2)
    have hfilterZero : ∑ z ∈ u, F z = ∑ z ∈ v, F z := by
      have hzero : ∑ z ∈ u.filter (fun z =>
          ¬(IsEqualityConfiguration I z.1 ∧ IsEqualityConfiguration J z.2)), F z = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        rcases Finset.mem_filter.mp hz with ⟨_, hnot⟩
        have hzeroFactor : f z.1 = 0 ∨ g z.2 = 0 := by
          by_cases hx : IsEqualityConfiguration I z.1
          · by_cases hy : IsEqualityConfiguration J z.2
            · exact False.elim (hnot ⟨hx, hy⟩)
            · exact Or.inr (hgSupport z.2 hy)
          · exact Or.inl (hfSupport z.1 hx)
        dsimp [F]
        rcases hzeroFactor with hx | hy
        · simp [hx]
        · simp [hy]
      calc
        (∑ z ∈ u, F z) =
            (∑ z ∈ u.filter (fun z =>
              IsEqualityConfiguration I z.1 ∧ IsEqualityConfiguration J z.2), F z) +
            (∑ z ∈ u.filter (fun z =>
              ¬(IsEqualityConfiguration I z.1 ∧ IsEqualityConfiguration J z.2)), F z) := by
                rw [← Finset.sum_filter_add_sum_filter_not u
                  (fun z => IsEqualityConfiguration I z.1 ∧ IsEqualityConfiguration J z.2) F]
        _ = ∑ z ∈ v, F z := by
          simp only [hzero, add_zero, v]
    let s := v.image Prod.fst
    let t := v.image Prod.snd
    have hs : ∀ x ∈ s, IsEqualityConfiguration I x := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      exact (Finset.mem_filter.mp hz).2.1
    have ht : ∀ y ∈ t, IsEqualityConfiguration J y := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      exact (Finset.mem_filter.mp hz).2.2
    have hsubset : v ⊆ s ×ˢ t := by
      intro z hz
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
      · exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hrect : (∑ z ∈ v, F z) ≤ ∑ z ∈ s ×ˢ t, F z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z hz₁ hz₂ => hFnonneg z)
    have hproduct : (∑ z ∈ s ×ˢ t, F z) =
        ∑ x ∈ s, ∑ y ∈ t, |f x| * replicaGreenKernel x y * |g y| := by
      simpa only [Prod.eta, F] using
        (Finset.sum_product' s t (fun x y => |f x| * replicaGreenKernel x y * |g y|))
    have hLZ := finite_equalityStratum_bilinear_le I J hI hJ hcommon hpq s t hs ht f g
    have hfp : (∑ x ∈ s, |f x| ^ p) ≤ TF := hf.sum_le_tsum s (fun x hx => hfn x)
    have hgp : (∑ y ∈ t, |g y| ^ q) ≤ TG := hg.sum_le_tsum t (fun y hy => hgn y)
    have hnorm :
        (∑ x ∈ s, |f x| ^ p) ^ (1 / p) * (∑ y ∈ t, |g y| ^ q) ^ (1 / q) ≤
          TF ^ (1 / p) * TG ^ (1 / q) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity) hfp hpInv
      · exact Real.rpow_le_rpow (by positivity) hgp hqInv
      · exact Real.rpow_nonneg (by positivity) _
      · exact Real.rpow_nonneg (by positivity) _
    have hC : 0 ≤ C := by
      dsimp [C, lz21BilinearConstant]
      positivity
    calc
      (∑ z ∈ u, F z) = ∑ z ∈ v, F z := hfilterZero
      _ ≤ ∑ z ∈ s ×ˢ t, F z := hrect
      _ = ∑ x ∈ s, ∑ y ∈ t, |f x| * replicaGreenKernel x y * |g y| := hproduct
      _ ≤ C * (∑ x ∈ s, |f x| ^ p) ^ (1 / p) * (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := by
        simpa [C, lz21BilinearConstant] using hLZ
      _ ≤ C * TF ^ (1 / p) * TG ^ (1 / q) := by
        calc
          _ = C * ((∑ x ∈ s, |f x| ^ p) ^ (1 / p) *
              (∑ y ∈ t, |g y| ^ q) ^ (1 / q)) := by ring
          _ ≤ C * (TF ^ (1 / p) * TG ^ (1 / q)) := mul_le_mul_of_nonneg_left hnorm hC
          _ = _ := by ring
  have hFsum : Summable F := summable_of_sum_le hFnonneg hfinite
  have hFtsum : (∑' z, F z) ≤ C * TF ^ (1 / p) * TG ^ (1 / q) :=
    Real.tsum_le_of_sum_le hFnonneg hfinite
  exact ⟨by simpa [F] using hFsum, by simpa [F, C, TF, TG] using hFtsum⟩

end Critical2DKPZ.MomentBounds
