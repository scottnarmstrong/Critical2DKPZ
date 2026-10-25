/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockGaussianSupportTail
public import Critical2DKPZ.SHF.Moments.PairBlockGaussianList
public import Critical2DKPZ.SHF.Moments.PairBlockCompositionProfile
import Mathlib.Tactic

/-! # Gaussianized composition laws on the integer lattice -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Filter

private theorem sum_range_cast_eq_Icc (m : ℕ) (f : ℤ → ℝ) :
    (∑ k ∈ Finset.range (m + 1), f (k : ℤ)) =
      ∑ j ∈ Finset.Icc (0 : ℤ) m, f j := by
  classical
  refine Finset.sum_bij (fun k _ => (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast (Nat.zero_le k)
    · exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  · intro k hk l hl hEq
    exact_mod_cast hEq
  · intro j hj
    have hj0 : 0 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjm : j ≤ (m : ℤ) := (Finset.mem_Icc.mp hj).2
    refine ⟨j.toNat, ?_, Int.toNat_of_nonneg hj0⟩
    simp only [Finset.mem_range]
    have hcast : ((j.toNat : ℕ) : ℤ) ≤ (m : ℤ) := by
      simpa [Int.toNat_of_nonneg hj0] using hjm
    exact Nat.lt_succ_of_le (by exact_mod_cast hcast)
  · intro k hk
    rfl

/-- Extend a finitely supported natural law by zero to the integer lattice. -/
def naturalBlockLawExtension (n : ℕ) (f : ℕ → ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ (n : ℤ) then f j.toNat else 0

private theorem finiteNaturalConvolution_eq_intTsum
    (m n j : ℕ) (p q : ℕ → ℝ) :
    finiteNaturalConvolution m n p q j =
      ∑' k : ℤ, naturalBlockLawExtension m p k *
        naturalBlockLawExtension n q ((j : ℤ) - k) := by
  classical
  let F := ((Finset.range (m + 1)).product (Finset.range (n + 1))).filter
    (fun ij => ij.1 + ij.2 = j)
  let G := (Finset.Icc (0 : ℤ) m).filter
    (fun k => 0 ≤ (j : ℤ) - k ∧ (j : ℤ) - k ≤ (n : ℤ))
  have hzero : ∀ k : ℤ, k ∉ G →
      naturalBlockLawExtension m p k *
        naturalBlockLawExtension n q ((j : ℤ) - k) = 0 := by
    intro k hk
    by_cases hk' : 0 ≤ k ∧ k ≤ (m : ℤ)
    · have hq' : ¬ (0 ≤ (j : ℤ) - k ∧ (j : ℤ) - k ≤ (n : ℤ)) := by
        intro hq
        have hG : k ∈ G := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_Icc.mpr hk', hq⟩
        exact (hk hG).elim
      have hqzero : naturalBlockLawExtension n q ((j : ℤ) - k) = 0 := by
        by_cases hq : 0 ≤ (j : ℤ) - k ∧ (j : ℤ) - k ≤ (n : ℤ)
        · exact (hq' hq).elim
        · have hnot : ¬ (k ≤ (j : ℤ) ∧ (j : ℤ) ≤ (n : ℤ) + k) := by omega
          simp [naturalBlockLawExtension, hnot]
      rw [hqzero]
      simp [naturalBlockLawExtension, hk']
    · have hpzero : naturalBlockLawExtension m p k = 0 := by
        by_cases hp : 0 ≤ k ∧ k ≤ (m : ℤ)
        · exact (hk' hp).elim
        · simp [naturalBlockLawExtension, hp]
      rw [hpzero]
      simp
  rw [show (∑' k : ℤ,
      naturalBlockLawExtension m p k *
        naturalBlockLawExtension n q ((j : ℤ) - k)) =
      ∑ k ∈ G, naturalBlockLawExtension m p k *
        naturalBlockLawExtension n q ((j : ℤ) - k) by
      exact tsum_eq_sum hzero]
  change (∑ ij ∈ F, p ij.1 * q ij.2) =
    ∑ k ∈ G, naturalBlockLawExtension m p k *
      naturalBlockLawExtension n q ((j : ℤ) - k)
  refine Finset.sum_bij (s := F) (t := G) (fun ij _ => (ij.1 : ℤ)) ?_ ?_ ?_ ?_
  · intro ij hij
    rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
    rcases Finset.mem_product.mp hprod with ⟨hi, hq⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_Icc]
      constructor
      · exact_mod_cast (Nat.zero_le ij.1)
      · exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    · constructor
      · have hsum' : (ij.1 : ℤ) + (ij.2 : ℤ) = (j : ℤ) := by exact_mod_cast hsum
        omega
      · have hq' : ij.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
        have hsum' : (ij.1 : ℤ) + (ij.2 : ℤ) = (j : ℤ) := by exact_mod_cast hsum
        have hdiff : (j : ℤ) - (ij.1 : ℤ) = (ij.2 : ℤ) := by omega
        rw [hdiff]
        exact_mod_cast hq'
  · intro ij hij ij' hij' hEq
    rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
    rcases Finset.mem_filter.mp hij' with ⟨hprod', hsum'⟩
    have hfst : ij.1 = ij'.1 := by exact_mod_cast hEq
    have hsnd : ij.2 = ij'.2 := by omega
    exact Prod.ext hfst hsnd
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIcc, hkrem⟩
    have hk0 : 0 ≤ k := (Finset.mem_Icc.mp hkIcc).1
    have hkm : k ≤ (m : ℤ) := (Finset.mem_Icc.mp hkIcc).2
    let i : ℕ := k.toNat
    let l : ℕ := j - i
    have hcasti : (i : ℤ) = k := by simp [i, Int.toNat_of_nonneg hk0]
    have hij : i ≤ j := by
      have : (i : ℤ) ≤ (j : ℤ) := by omega
      exact_mod_cast this
    have hli : (l : ℤ) = (j : ℤ) - k := by
      dsimp [l]
      rw [Nat.cast_sub hij, hcasti]
    have hl : l ≤ n := by
      have hbound := hkrem.2
      rw [← hli] at hbound
      exact_mod_cast hbound
    have hkm' : (i : ℤ) ≤ (m : ℤ) := by rw [hcasti]; exact hkm
    have hile : i ≤ m := by exact_mod_cast hkm'
    refine ⟨(i, l), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hile),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hl)⟩
      · dsimp [l]
        omega
    · exact hcasti
  · intro ij hij
    rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
    rcases Finset.mem_product.mp hprod with ⟨hi, hq⟩
    have hi0 : 0 ≤ (ij.1 : ℤ) := by exact_mod_cast (Nat.zero_le ij.1)
    have him : (ij.1 : ℤ) ≤ (m : ℤ) := by
      exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    have hq' : (ij.2 : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hq))
    have hsum' : (ij.1 : ℤ) + (ij.2 : ℤ) = (j : ℤ) := by exact_mod_cast hsum
    have hdiff : (j : ℤ) - (ij.1 : ℤ) = (ij.2 : ℤ) := by omega
    have hjrem : 0 ≤ (j : ℤ) - (ij.1 : ℤ) ∧
        (j : ℤ) - (ij.1 : ℤ) ≤ (n : ℤ) := by
      rw [hdiff]
      exact ⟨by exact_mod_cast (Nat.zero_le ij.2), hq'⟩
    have hcasti : ((ij.1 : ℤ).toNat) = ij.1 := by
      exact_mod_cast Int.toNat_of_nonneg hi0
    have hcastq : (((j : ℤ) - (ij.1 : ℤ)).toNat) = ij.2 := by
      rw [hdiff]
      simp
    have hijLe : ij.1 ≤ j := by omega
    simp [naturalBlockLawExtension, hi0, him, hjrem, hcasti, hcastq, hijLe]

private theorem finiteNaturalConvolution_eq_zero_of_gt
    (m n j : ℕ) (p q : ℕ → ℝ) (h : m + n < j) :
    finiteNaturalConvolution m n p q j = 0 := by
  classical
  unfold finiteNaturalConvolution
  apply Finset.sum_eq_zero
  intro ij hij
  rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
  rcases Finset.mem_product.mp hprod with ⟨hi, hj⟩
  have hi' : ij.1 ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hj' : ij.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  omega

/-- The integer extension of a finite natural convolution is the convolution
of the two integer extensions, at every lattice point. -/
private theorem finiteNaturalConvolution_extension_eq_intTsum
    (m n : ℕ) (p q : ℕ → ℝ) (j : ℤ) :
    naturalBlockLawExtension (m + n)
        (finiteNaturalConvolution m n p q) j =
      ∑' k : ℤ, naturalBlockLawExtension m p k *
        naturalBlockLawExtension n q (j - k) := by
  by_cases hj0 : 0 ≤ j
  · have hjcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have hsumCast : ((m + n : ℕ) : ℤ) = (m : ℤ) + (n : ℤ) := by
      exact_mod_cast Nat.cast_add m n
    have hconv : finiteNaturalConvolution m n p q j.toNat =
        ∑' k : ℤ, naturalBlockLawExtension m p k *
          naturalBlockLawExtension n q (j - k) := by
      simpa only [hjcast] using finiteNaturalConvolution_eq_intTsum m n j.toNat p q
    by_cases hjmn : j ≤ (m + n : ℕ)
    · have hjmnInt' : j ≤ (m : ℤ) + (n : ℤ) := by
        rw [← hsumCast]
        exact hjmn
      simpa [naturalBlockLawExtension, hj0, hjmnInt'] using hconv
    · have hjgt : m + n < j.toNat := by
        have hjgtInt : (m : ℤ) + (n : ℤ) < j := by
          by_contra h
          have hle := le_of_not_gt h
          rw [← hsumCast] at hle
          exact hjmn hle
        have hgtCast : ((m + n : ℕ) : ℤ) < (j.toNat : ℤ) := by
          rw [hjcast, hsumCast]
          exact hjgtInt
        exact_mod_cast hgtCast
      have hzero := finiteNaturalConvolution_eq_zero_of_gt m n j.toNat p q hjgt
      have hjgtInt : (m : ℤ) + (n : ℤ) < j := by
        by_contra h
        have hle := le_of_not_gt h
        rw [← hsumCast] at hle
        exact hjmn hle
      have hnot : ¬ j ≤ (m : ℤ) + (n : ℤ) := not_le_of_gt hjgtInt
      simpa [naturalBlockLawExtension, hj0, hnot, hzero] using hconv
  · have hzero (k : ℤ) :
        naturalBlockLawExtension m p k * naturalBlockLawExtension n q (j - k) = 0 := by
      by_cases hk : 0 ≤ k ∧ k ≤ (m : ℤ)
      · have hqzero : naturalBlockLawExtension n q (j - k) = 0 := by
          by_cases hq : 0 ≤ j - k ∧ j - k ≤ (n : ℤ)
          · have hj : 0 ≤ j := by omega
            exact (hj0 hj).elim
          · have hnot : ¬ (k ≤ j ∧ j ≤ (n : ℤ) + k) := by omega
            simp [naturalBlockLawExtension, hnot]
        rw [hqzero]
        simp
      · have hpzero : naturalBlockLawExtension m p k = 0 := by
          by_cases hp : 0 ≤ k ∧ k ≤ (m : ℤ)
          · exact (hk hp).elim
          · simp [naturalBlockLawExtension, hp]
        rw [hpzero]
        simp
    have htsum :
        (∑' k : ℤ, naturalBlockLawExtension m p k *
          naturalBlockLawExtension n q (j - k)) = 0 := by
      have heq : (fun k : ℤ => naturalBlockLawExtension m p k *
          naturalBlockLawExtension n q (j - k)) = fun _ => 0 := by
        funext k
        exact hzero k
      rw [heq, tsum_zero]
    rw [htsum]
    simp [naturalBlockLawExtension, hj0]

/-- The integer law of a composition of independent normalized sampled-Gaussian
block marks. -/
def sampledGaussianBlockListProbability : List ℕ → ℤ → ℝ
  | [] , j => if j = 0 then 1 else 0
  | [m], j => gaussianizedBlockIntProbability m j
  | m :: n :: ms, j =>
      ∑' k : ℤ, gaussianizedBlockIntProbability m k *
        sampledGaussianBlockListProbability (n :: ms) (j - k)

private theorem gaussianizedBlockIntProbability_eq_extension (m : ℕ) (j : ℤ) :
    gaussianizedBlockIntProbability m j =
      naturalBlockLawExtension m (normalizedSampledHypergeometricGaussianWeight m) j := rfl

/-- The integer convolution of sampled Gaussian block laws is exactly the
integer extension of the finite natural composition law. -/
theorem sampledGaussianBlockListProbability_eq_normalizedGaussianBlockListLaw_extension :
    ∀ ms j,
      sampledGaussianBlockListProbability ms j =
        naturalBlockLawExtension ms.sum (normalizedGaussianBlockListLaw ms) j := by
  intro ms
  induction ms with
  | nil =>
      intro j
      by_cases hj : j = 0
      · subst j
        simp [sampledGaussianBlockListProbability,
          normalizedGaussianBlockListLaw, naturalBlockLawExtension]
      · have hnot : ¬ (0 ≤ j ∧ j ≤ (0 : ℤ)) := by omega
        simp [sampledGaussianBlockListProbability,
          naturalBlockLawExtension, hj, hnot]
  | cons m ms ih =>
      cases ms with
      | nil =>
          intro j
          let p : ℕ → ℝ := normalizedSampledHypergeometricGaussianWeight m
          let δ : ℕ → ℝ := fun k => if k = 0 then 1 else 0
          have hconv := finiteNaturalConvolution_extension_eq_intTsum m 0 p δ j
          have hdelta (k : ℤ) : naturalBlockLawExtension 0 δ (j - k) =
              if j = k then 1 else 0 := by
            by_cases hEq : j = k
            · subst k
              simp [naturalBlockLawExtension, δ]
            · have hnot : ¬ (k ≤ j ∧ j ≤ k) := by omega
              simp [naturalBlockLawExtension, δ, hnot, hEq]
          have hsum :
              (∑' k : ℤ, naturalBlockLawExtension m p k *
                naturalBlockLawExtension 0 δ (j - k)) =
              naturalBlockLawExtension m p j := by
            calc
              _ = ∑' k : ℤ,
                  naturalBlockLawExtension m p k * (if j = k then 1 else 0) := by
                    apply tsum_congr
                    intro k
                    rw [hdelta]
              _ = naturalBlockLawExtension m p j := by
                    rw [tsum_eq_single j]
                    · simp
                    · intro k hk
                      have hne : j ≠ k := fun h => hk h.symm
                      simp [hne]
          have hconv' :
              naturalBlockLawExtension m
                  (normalizedGaussianBlockListLaw [m]) j =
                ∑' k : ℤ, naturalBlockLawExtension m p k *
                  naturalBlockLawExtension 0 δ (j - k) := by
            simpa [p, δ, normalizedGaussianBlockListLaw] using hconv
          calc
            sampledGaussianBlockListProbability [m] j =
                gaussianizedBlockIntProbability m j := rfl
            _ = naturalBlockLawExtension m p j := by
              exact gaussianizedBlockIntProbability_eq_extension m j
            _ = ∑' k : ℤ, naturalBlockLawExtension m p k *
                  naturalBlockLawExtension 0 δ (j - k) := hsum.symm
            _ = naturalBlockLawExtension m
                  (normalizedGaussianBlockListLaw [m]) j := hconv'.symm
      | cons n ms =>
          intro j
          have hconv := finiteNaturalConvolution_extension_eq_intTsum
            m (n :: ms).sum
            (normalizedSampledHypergeometricGaussianWeight m)
            (normalizedGaussianBlockListLaw (n :: ms)) j
          calc
            sampledGaussianBlockListProbability (m :: n :: ms) j =
                ∑' k : ℤ, naturalBlockLawExtension m
                    (normalizedSampledHypergeometricGaussianWeight m) k *
                  naturalBlockLawExtension (n :: ms).sum
                    (normalizedGaussianBlockListLaw (n :: ms)) (j - k) := by
              change ∑' k : ℤ, gaussianizedBlockIntProbability m k *
                sampledGaussianBlockListProbability (n :: ms) (j - k) = _
              apply tsum_congr
              intro k
              rw [gaussianizedBlockIntProbability_eq_extension, ih]
            _ = naturalBlockLawExtension (m + (n :: ms).sum)
                  (finiteNaturalConvolution m (n :: ms).sum
                    (normalizedSampledHypergeometricGaussianWeight m)
                    (normalizedGaussianBlockListLaw (n :: ms))) j := hconv.symm
            _ = naturalBlockLawExtension (m :: n :: ms).sum
                  (normalizedGaussianBlockListLaw (m :: n :: ms)) j := by
              rfl

/-- If every duration crosses the hybrid cutoff, the hybrid composition is
the normalized sampled-Gaussian composition at every natural mark. -/
theorem largeBlockGaussianListLaw_eq_normalized_of_all_ge
    (mCut : ℕ) (ms : List ℕ) (hall : ∀ m ∈ ms, mCut ≤ m) (j : ℕ) :
    largeBlockGaussianListLaw mCut ms j = normalizedGaussianBlockListLaw ms j := by
  induction ms generalizing j with
  | nil => simp [largeBlockGaussianListLaw, normalizedGaussianBlockListLaw]
  | cons m ms ih =>
      have hm : mCut ≤ m := hall m (by simp)
      have htail : ∀ a ∈ ms, mCut ≤ a := by
        intro a ha
        exact hall a (by simp [ha])
      have htailLaw : largeBlockGaussianListLaw mCut ms =
          normalizedGaussianBlockListLaw ms := by
        funext k
        exact ih htail k
      change finiteNaturalConvolution m ms.sum
          (largeBlockGaussianWeight mCut m) (largeBlockGaussianListLaw mCut ms) j =
        finiteNaturalConvolution m ms.sum
          (normalizedSampledHypergeometricGaussianWeight m)
          (normalizedGaussianBlockListLaw ms) j
      have hweight : largeBlockGaussianWeight mCut m =
          normalizedSampledHypergeometricGaussianWeight m := by
        funext k
        simp [largeBlockGaussianWeight, hm]
      rw [hweight, htailLaw]

private theorem gaussianizedBlockIntProbability_summable (m : ℕ) :
    Summable (gaussianizedBlockIntProbability m) := by
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.Icc (0 : ℤ) m)).subset
  intro j hj
  by_contra hnot
  have hj' : ¬ (0 ≤ j ∧ j ≤ (m : ℤ)) := by
    simpa [Finset.mem_Icc] using hnot
  have hz : gaussianizedBlockIntProbability m j = 0 := by
    simp [gaussianizedBlockIntProbability, hj']
  exact hj hz

private theorem gaussianizedBlockIntProbability_nonneg_of_mass
    (m : ℕ) (hden : 0 < ∑ k ∈ Finset.range (m + 1),
      sampledHypergeometricGaussianWeight m k) (j : ℤ) :
    0 ≤ gaussianizedBlockIntProbability m j := by
  by_cases hj : 0 ≤ j ∧ j ≤ (m : ℤ)
  · simp [gaussianizedBlockIntProbability, hj]
    unfold normalizedSampledHypergeometricGaussianWeight sampledHypergeometricGaussianWeight
    exact div_nonneg (by positivity) hden.le
  · simp [gaussianizedBlockIntProbability, hj]

private theorem gaussianizedBlockIntProbability_sum_one
    (m : ℕ)
    (hnorm : ∑ k ∈ Finset.range (m + 1),
      normalizedSampledHypergeometricGaussianWeight m k = 1) :
    ∑' j : ℤ, gaussianizedBlockIntProbability m j = 1 := by
  let F : Finset ℤ := Finset.Icc 0 m
  have hzero : ∀ j ∉ F, gaussianizedBlockIntProbability m j = 0 := by
    intro j hj
    have hj' : ¬ (0 ≤ j ∧ j ≤ (m : ℤ)) := by
      simpa [F, Finset.mem_Icc] using hj
    simp [gaussianizedBlockIntProbability, hj']
  rw [tsum_eq_sum hzero]
  have hsum : (∑ j ∈ F, gaussianizedBlockIntProbability m j) =
      ∑ k ∈ Finset.range (m + 1),
        normalizedSampledHypergeometricGaussianWeight m k := by
    classical
    calc
      _ = ∑ j ∈ Finset.Icc (0 : ℤ) m, gaussianizedBlockIntProbability m j := by
        rfl
      _ = ∑ k ∈ Finset.range (m + 1),
          gaussianizedBlockIntProbability m (k : ℤ) :=
        (sum_range_cast_eq_Icc m _).symm
      _ = ∑ k ∈ Finset.range (m + 1),
          normalizedSampledHypergeometricGaussianWeight m k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk0 : 0 ≤ (k : ℤ) := by exact_mod_cast (Nat.zero_le k)
        have hkm : (k : ℤ) ≤ (m : ℤ) := by
          exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
        simp [gaussianizedBlockIntProbability, hk0, hkm,
          normalizedSampledHypergeometricGaussianWeight]
  rw [hsum, hnorm]

private theorem sampledGaussianBlockListProbability_nonneg_le_one
    (ms : List ℕ)
    (hden : ∀ m ∈ ms, 0 < ∑ k ∈ Finset.range (m + 1),
      sampledHypergeometricGaussianWeight m k)
    (hnorm : ∀ m ∈ ms, ∑ k ∈ Finset.range (m + 1),
      normalizedSampledHypergeometricGaussianWeight m k = 1) :
    ∀ j : ℤ, 0 ≤ sampledGaussianBlockListProbability ms j ∧
      sampledGaussianBlockListProbability ms j ≤ 1 := by
  induction ms with
  | nil =>
      intro j
      by_cases hj : j = 0 <;> simp [sampledGaussianBlockListProbability, hj]
  | cons m ms ih =>
      have hmden : 0 < ∑ k ∈ Finset.range (m + 1),
          sampledHypergeometricGaussianWeight m k := hden m (by simp)
      have hmnorm : ∑ k ∈ Finset.range (m + 1),
          normalizedSampledHypergeometricGaussianWeight m k = 1 := hnorm m (by simp)
      have htailden : ∀ a ∈ ms, 0 < ∑ k ∈ Finset.range (a + 1),
          sampledHypergeometricGaussianWeight a k := by
        intro a ha
        exact hden a (by simp [ha])
      have htailnorm : ∀ a ∈ ms, ∑ k ∈ Finset.range (a + 1),
          normalizedSampledHypergeometricGaussianWeight a k = 1 := by
        intro a ha
        exact hnorm a (by simp [ha])
      cases ms with
      | nil =>
          intro j
          have hmass := gaussianizedBlockIntProbability_sum_one m hmnorm
          have hnonneg := gaussianizedBlockIntProbability_nonneg_of_mass m hmden
          have hsummable := gaussianizedBlockIntProbability_summable m
          have hbound := hsummable.sum_le_tsum {j} (fun i hi => hnonneg i)
          rw [hmass] at hbound
          constructor
          · exact hnonneg j
          · simpa [sampledGaussianBlockListProbability] using hbound
      | cons n ms =>
          have htailBound := ih htailden htailnorm
          have hPmass := gaussianizedBlockIntProbability_sum_one m hmnorm
          have hPnonneg := gaussianizedBlockIntProbability_nonneg_of_mass m hmden
          have hPsum := gaussianizedBlockIntProbability_summable m
          intro j
          let f : ℤ → ℝ := fun k => gaussianizedBlockIntProbability m k *
            sampledGaussianBlockListProbability (n :: ms) (j - k)
          have hf : Summable f := by
            apply Summable.of_nonneg_of_le
              (fun k => mul_nonneg (hPnonneg k) (htailBound (j - k)).1)
              (fun k => by
                calc
                  _ ≤ gaussianizedBlockIntProbability m k * 1 :=
                    mul_le_mul_of_nonneg_left (htailBound (j - k)).2 (hPnonneg k)
                  _ = gaussianizedBlockIntProbability m k := by ring)
              hPsum
          have hsumUpper : (∑' k : ℤ, f k) ≤ 1 := by
            calc
              _ ≤ ∑' k : ℤ, gaussianizedBlockIntProbability m k :=
                hf.tsum_le_tsum (fun k => by
                  dsimp [f]
                  calc
                    _ ≤ gaussianizedBlockIntProbability m k * 1 :=
                      mul_le_mul_of_nonneg_left (htailBound (j - k)).2 (hPnonneg k)
                    _ = gaussianizedBlockIntProbability m k := by ring)
                  hPsum
              _ = 1 := hPmass
          change 0 ≤ ∑' k : ℤ, f k ∧ ∑' k : ℤ, f k ≤ 1
          constructor
          · exact tsum_nonneg fun k => mul_nonneg (hPnonneg k)
              (htailBound (j - k)).1
          · exact hsumUpper

/-- Replacing each normalized sampled Gaussian block by its full-lattice law
changes a composition atom by at most the sum of the one-block `L¹` errors. -/
theorem sampledGaussianBlockListProbability_profileError_bound
    (ms : List ℕ)
    (hpositive : ∀ m ∈ ms, 0 < m)
    (hden : ∀ m ∈ ms, 0 < ∑ k ∈ Finset.range (m + 1),
      sampledHypergeometricGaussianWeight m k)
    (hnorm : ∀ m ∈ ms, ∑ k ∈ Finset.range (m + 1),
      normalizedSampledHypergeometricGaussianWeight m k = 1) :
    ∀ j : ℤ,
      |sampledGaussianBlockListProbability ms j -
        fullGaussianBlockListProbability ms j| ≤
      (ms.map fun m =>
        ∑' k : ℤ, |gaussianizedBlockIntProbability m k -
          fullGaussianBlockProbability m k|).sum := by
  induction ms with
  | nil =>
      intro j
      simp [sampledGaussianBlockListProbability, fullGaussianBlockListProbability]
  | cons m ms ih =>
      have hmpos : 0 < m := hpositive m (by simp)
      have htailPositive : ∀ a ∈ ms, 0 < a := by
        intro a ha
        exact hpositive a (by simp [ha])
      have hmden : 0 < ∑ k ∈ Finset.range (m + 1),
          sampledHypergeometricGaussianWeight m k := hden m (by simp)
      have hmnorm : ∑ k ∈ Finset.range (m + 1),
          normalizedSampledHypergeometricGaussianWeight m k = 1 := hnorm m (by simp)
      have htailden : ∀ a ∈ ms, 0 < ∑ k ∈ Finset.range (a + 1),
          sampledHypergeometricGaussianWeight a k := by
        intro a ha
        exact hden a (by simp [ha])
      have htailnorm : ∀ a ∈ ms, ∑ k ∈ Finset.range (a + 1),
          normalizedSampledHypergeometricGaussianWeight a k = 1 := by
        intro a ha
        exact hnorm a (by simp [ha])
      have htailError (j : ℤ) :
          |sampledGaussianBlockListProbability ms j -
            fullGaussianBlockListProbability ms j| ≤
          (ms.map fun a =>
            ∑' k : ℤ, |gaussianizedBlockIntProbability a k -
              fullGaussianBlockProbability a k|).sum :=
        ih htailPositive htailden htailnorm j
      cases ms with
      | nil =>
          intro j
          have hPsum := gaussianizedBlockIntProbability_summable m
          have hQsum := summable_fullGaussianBlockProbability m hmpos
          have hdiff : Summable (fun k : ℤ =>
              ‖gaussianizedBlockIntProbability m k -
                fullGaussianBlockProbability m k‖) := (hPsum.sub hQsum).norm
          have hbound := hdiff.sum_le_tsum {j} (fun k hk => norm_nonneg _)
          simpa [sampledGaussianBlockListProbability,
            fullGaussianBlockListProbability, Real.norm_eq_abs] using hbound
      | cons n ms =>
        let E₁ : ℝ := ∑' k : ℤ,
          |gaussianizedBlockIntProbability m k - fullGaussianBlockProbability m k|
        let E₂ : ℝ := ((n :: ms).map fun a =>
          ∑' k : ℤ, |gaussianizedBlockIntProbability a k -
            fullGaussianBlockProbability a k|).sum
        have hsampleBounds := sampledGaussianBlockListProbability_nonneg_le_one
          (n :: ms) htailden htailnorm
        have hfullBounds := fullGaussianBlockListProbability_nonneg_le_one
          (n :: ms) htailPositive
        have hPnonneg (k : ℤ) : 0 ≤ gaussianizedBlockIntProbability m k :=
          gaussianizedBlockIntProbability_nonneg_of_mass m hmden k
        have hPmass : ∑' k : ℤ, gaussianizedBlockIntProbability m k = 1 :=
          gaussianizedBlockIntProbability_sum_one m hmnorm
        have hPsum : Summable (gaussianizedBlockIntProbability m) :=
          gaussianizedBlockIntProbability_summable m
        have hQnonneg (k : ℤ) : 0 ≤ fullGaussianBlockProbability m k :=
          (fullGaussianBlockProbability_nonneg_le_one m hmpos k).1
        have hQmass : ∑' k : ℤ, fullGaussianBlockProbability m k = 1 :=
          tsum_fullGaussianBlockProbability m hmpos
        have hQsum : Summable (fullGaussianBlockProbability m) :=
          summable_fullGaussianBlockProbability m hmpos
        have hsampleTermSummable (j : ℤ) :
            Summable (fun k : ℤ => gaussianizedBlockIntProbability m k *
              sampledGaussianBlockListProbability (n :: ms) (j - k)) := by
          apply Summable.of_nonneg_of_le
            (fun k => mul_nonneg (hPnonneg k) (hsampleBounds (j - k)).1)
            (fun k => by
              calc
                _ ≤ gaussianizedBlockIntProbability m k * 1 :=
                  mul_le_mul_of_nonneg_left (hsampleBounds (j - k)).2 (hPnonneg k)
                _ = gaussianizedBlockIntProbability m k := by ring)
            hPsum
        have hfullTermSummable (j : ℤ) :
            Summable (fun k : ℤ => fullGaussianBlockProbability m k *
              fullGaussianBlockListProbability (n :: ms) (j - k)) := by
          apply Summable.of_nonneg_of_le
            (fun k => mul_nonneg (hQnonneg k) (hfullBounds (j - k)).1)
            (fun k => by
              calc
                _ ≤ fullGaussianBlockProbability m k * 1 :=
                  mul_le_mul_of_nonneg_left (hfullBounds (j - k)).2 (hQnonneg k)
                _ = fullGaussianBlockProbability m k := by ring)
            hQsum
        have hblockDiffSummable : Summable (fun k : ℤ =>
            |gaussianizedBlockIntProbability m k - fullGaussianBlockProbability m k|) := by
          simpa [Real.norm_eq_abs] using (hPsum.sub hQsum).norm
        have hpoint (j k : ℤ) :
            |gaussianizedBlockIntProbability m k *
                sampledGaussianBlockListProbability (n :: ms) (j - k) -
              fullGaussianBlockProbability m k *
                fullGaussianBlockListProbability (n :: ms) (j - k)| ≤
            |gaussianizedBlockIntProbability m k - fullGaussianBlockProbability m k| *
                sampledGaussianBlockListProbability (n :: ms) (j - k) +
              fullGaussianBlockProbability m k * E₂ := by
          let p := gaussianizedBlockIntProbability m k
          let q := fullGaussianBlockProbability m k
          let a := sampledGaussianBlockListProbability (n :: ms) (j - k)
          let b := fullGaussianBlockListProbability (n :: ms) (j - k)
          have ha := hsampleBounds (j - k)
          have hab : |a - b| ≤ E₂ := by simpa [a, b, E₂] using htailError (j - k)
          have hdecomp : p * a - q * b = (p - q) * a + q * (a - b) := by ring
          rw [hdecomp]
          calc
            |(p - q) * a + q * (a - b)| ≤ |(p - q) * a| + |q * (a - b)| :=
              abs_add_le _ _
            _ = |p - q| * a + q * |a - b| := by
              calc
                _ = |p - q| * |a| + |q| * |a - b| := by rw [abs_mul, abs_mul]
                _ = |p - q| * a + q * |a - b| := by
                  rw [abs_of_nonneg ha.1, abs_of_nonneg (hQnonneg k)]
            _ ≤ |p - q| * a + q * E₂ := by
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_left hab (hQnonneg k))
        have hfirstSummable (j : ℤ) : Summable (fun k : ℤ =>
            |gaussianizedBlockIntProbability m k - fullGaussianBlockProbability m k| *
                sampledGaussianBlockListProbability (n :: ms) (j - k)) := by
          apply Summable.of_nonneg_of_le
            (fun k => mul_nonneg (abs_nonneg _) (hsampleBounds (j - k)).1)
            (fun k => by
              calc
                _ ≤ |gaussianizedBlockIntProbability m k -
                      fullGaussianBlockProbability m k| * 1 :=
                  mul_le_mul_of_nonneg_left (hsampleBounds (j - k)).2 (abs_nonneg _)
                _ = |gaussianizedBlockIntProbability m k -
                    fullGaussianBlockProbability m k| := by ring)
            hblockDiffSummable
        have hsecondSummable : Summable (fun k : ℤ =>
            fullGaussianBlockProbability m k * E₂) := hQsum.mul_right E₂
        have hfirstBound (j : ℤ) :
            (∑' k : ℤ,
              |gaussianizedBlockIntProbability m k -
                fullGaussianBlockProbability m k| *
                sampledGaussianBlockListProbability (n :: ms) (j - k)) ≤ E₁ := by
          have h := (hfirstSummable j).tsum_le_tsum
            (fun k => mul_le_mul_of_nonneg_left
              (hsampleBounds (j - k)).2 (abs_nonneg _))
            (by simpa using hblockDiffSummable)
          simpa [E₁] using h
        have hsumMajor (j : ℤ) :
            (∑' k : ℤ,
              (|gaussianizedBlockIntProbability m k -
                  fullGaussianBlockProbability m k| *
                  sampledGaussianBlockListProbability (n :: ms) (j - k) +
                fullGaussianBlockProbability m k * E₂)) ≤ E₁ + E₂ := by
          calc
            _ = (∑' k : ℤ,
                  |gaussianizedBlockIntProbability m k -
                    fullGaussianBlockProbability m k| *
                    sampledGaussianBlockListProbability (n :: ms) (j - k)) +
                (∑' k : ℤ, fullGaussianBlockProbability m k * E₂) := by
                exact (hfirstSummable j).tsum_add hsecondSummable
            _ ≤ (∑' k : ℤ,
                  |gaussianizedBlockIntProbability m k -
                    fullGaussianBlockProbability m k|) +
                (∑' k : ℤ, fullGaussianBlockProbability m k * E₂) := by
              exact add_le_add (hfirstBound j) le_rfl
            _ = E₁ + E₂ := by
                rw [tsum_mul_right, hQmass]
                simp [E₁]
        intro j
        let f : ℤ → ℝ := fun k => gaussianizedBlockIntProbability m k *
          sampledGaussianBlockListProbability (n :: ms) (j - k)
        let g : ℤ → ℝ := fun k => fullGaussianBlockProbability m k *
          fullGaussianBlockListProbability (n :: ms) (j - k)
        have hdiffSummable : Summable (fun k : ℤ => f k - g k) :=
          (hsampleTermSummable j).sub (hfullTermSummable j)
        have hmajorSummable : Summable (fun k : ℤ =>
            (|gaussianizedBlockIntProbability m k -
                fullGaussianBlockProbability m k| *
                sampledGaussianBlockListProbability (n :: ms) (j - k) +
              fullGaussianBlockProbability m k * E₂)) :=
          (hfirstSummable j).add hsecondSummable
        have hsumdiff :
            ‖(∑' k : ℤ, f k) - (∑' k : ℤ, g k)‖ ≤ E₁ + E₂ := by
          rw [← (hsampleTermSummable j).tsum_sub (hfullTermSummable j)]
          calc
            _ ≤ ∑' k : ℤ, ‖f k - g k‖ :=
              norm_tsum_le_tsum_norm hdiffSummable.norm
            _ ≤ ∑' k : ℤ,
                (|gaussianizedBlockIntProbability m k -
                    fullGaussianBlockProbability m k| *
                    sampledGaussianBlockListProbability (n :: ms) (j - k) +
                  fullGaussianBlockProbability m k * E₂) :=
              hdiffSummable.norm.tsum_le_tsum
                (fun k => by rw [Real.norm_eq_abs]; exact hpoint j k)
                hmajorSummable
            _ ≤ E₁ + E₂ := hsumMajor j
        have hrewrite :
            sampledGaussianBlockListProbability (m :: n :: ms) j = ∑' k : ℤ, f k := by
          rfl
        have hfullrewrite :
            fullGaussianBlockListProbability (m :: n :: ms) j = ∑' k : ℤ, g k := by
          rfl
        have hfinal :
            |sampledGaussianBlockListProbability (m :: n :: ms) j -
              fullGaussianBlockListProbability (m :: n :: ms) j| ≤ E₁ + E₂ := by
          rw [hrewrite, hfullrewrite]
          simpa [Real.norm_eq_abs] using hsumdiff
        simpa [E₁, E₂, List.map_cons, List.sum_cons] using hfinal

/-- The two independent rotated coordinates inherit twice the one-coordinate
profile error when every block law is replaced by its full-lattice Gaussian. -/
theorem sampledGaussianBlockListPairProbability_profileError_bound
    (ms : List ℕ)
    (hpositive : ∀ m ∈ ms, 0 < m)
    (hden : ∀ m ∈ ms, 0 < ∑ k ∈ Finset.range (m + 1),
      sampledHypergeometricGaussianWeight m k)
    (hnorm : ∀ m ∈ ms, ∑ k ∈ Finset.range (m + 1),
      normalizedSampledHypergeometricGaussianWeight m k = 1)
    (j₁ j₂ : ℤ) :
    |sampledGaussianBlockListProbability ms j₁ *
        sampledGaussianBlockListProbability ms j₂ -
      fullGaussianBlockListProbability ms j₁ *
        fullGaussianBlockListProbability ms j₂| ≤
      2 * (ms.map fun m =>
        ∑' k : ℤ, |gaussianizedBlockIntProbability m k -
          fullGaussianBlockProbability m k|).sum := by
  let E := (ms.map fun m =>
    ∑' k : ℤ, |gaussianizedBlockIntProbability m k -
      fullGaussianBlockProbability m k|).sum
  let a := sampledGaussianBlockListProbability ms j₁
  let b := sampledGaussianBlockListProbability ms j₂
  let c := fullGaussianBlockListProbability ms j₁
  let d := fullGaussianBlockListProbability ms j₂
  have hab := sampledGaussianBlockListProbability_profileError_bound
    ms hpositive hden hnorm j₁
  have hdb := sampledGaussianBlockListProbability_profileError_bound
    ms hpositive hden hnorm j₂
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    simpa [a] using sampledGaussianBlockListProbability_nonneg_le_one ms hden hnorm j₁
  have hb : 0 ≤ b ∧ b ≤ 1 := by
    simpa [b] using sampledGaussianBlockListProbability_nonneg_le_one ms hden hnorm j₂
  have hc : 0 ≤ c ∧ c ≤ 1 := by
    simpa [c] using fullGaussianBlockListProbability_nonneg_le_one ms hpositive j₁
  have hd : 0 ≤ d ∧ d ≤ 1 := by
    simpa [d] using fullGaussianBlockListProbability_nonneg_le_one ms hpositive j₂
  have hE1 : |a - c| ≤ E := by simpa [a, c, E] using hab
  have hE2 : |b - d| ≤ E := by simpa [b, d, E] using hdb
  have hE : 0 ≤ E := by
    have hlist : ∀ xs : List ℕ, 0 ≤ (xs.map fun m =>
        ∑' k : ℤ, |gaussianizedBlockIntProbability m k -
          fullGaussianBlockProbability m k|).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons m xs ih =>
          simp only [List.map_cons, List.sum_cons]
          exact add_nonneg (tsum_nonneg fun k => abs_nonneg _) ih
    exact hlist ms
  have hdecomp : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [hdecomp]
  calc
    |(a - c) * b + c * (b - d)| ≤ |(a - c) * b| + |c * (b - d)| :=
      abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]
    _ ≤ E + E := by
      apply add_le_add
      · have hAbsB : |b| ≤ 1 := by rw [abs_of_nonneg hb.1]; exact hb.2
        calc
          |a - c| * |b| ≤ E * 1 :=
            mul_le_mul hE1 hAbsB (abs_nonneg _) hE
          _ = E := by ring
      · have hAbsC : |c| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2
        calc
          |c| * |b - d| ≤ 1 * E :=
            mul_le_mul hAbsC hE2 (abs_nonneg _) (by norm_num)
          _ = E := by ring
    _ = 2 * E := by ring

end Critical2DKPZ.SHF.Moments

end

