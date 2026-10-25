/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockCompositionProfile
public import Critical2DKPZ.Collision.SpatialRenewalComposition
import Mathlib.Tactic

/-! # Pointwise smoothing for pair-block compositions -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

private theorem finiteNaturalConvolution_comm {m n : ℕ} (p q : ℕ → ℝ) (k : ℕ) :
    finiteNaturalConvolution m n p q k = finiteNaturalConvolution n m q p k := by
  classical
  let A := Finset.range (m + 1)
  let B := Finset.range (n + 1)
  let F := (A.product B).filter (fun ij => ij.1 + ij.2 = k)
  let G := (B.product A).filter (fun ij => ij.1 + ij.2 = k)
  change (∑ ij ∈ F, p ij.1 * q ij.2) = ∑ ij ∈ G, q ij.1 * p ij.2
  refine Finset.sum_bij (s := F) (t := G) (fun ij _ => ij.swap) ?_ ?_ ?_ ?_
  · intro ij hij
    rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
    rcases Finset.mem_product.mp hprod with ⟨hi, hj⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hj, hi⟩, ?_⟩
    simpa [Prod.swap, Nat.add_comm] using hsum
  · intro ij hij ij' hij' hmap
    cases ij with
    | mk i j =>
      cases ij' with
      | mk i' j' =>
        simp only [Prod.swap, Prod.mk.injEq] at hmap
        rcases hmap with ⟨hji, hii⟩
        subst i'
        subst j'
        rfl
  · intro ij hij
    rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
    rcases Finset.mem_product.mp hprod with ⟨hi, hj⟩
    refine ⟨ij.swap, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hj, hi⟩, ?_⟩
      simpa [Prod.swap, Nat.add_comm] using hsum
    · cases ij
      rfl
  · intro ij hij
    simp only [Prod.swap]
    ring

/-- A pointwise bound on the second factor smooths the discrete convolution
by the `L¹` mass of its first factor. -/
theorem finiteNaturalConvolution_abs_le_rightPointwise {m n : ℕ}
    (p q : ℕ → ℝ) (L B : ℝ) (k : ℕ)
    (hB : 0 ≤ B)
    (hp : ∑ i ∈ Finset.range (m + 1), |p i| ≤ L)
    (hq : ∀ j ∈ Finset.range (n + 1), |q j| ≤ B) :
    |finiteNaturalConvolution m n p q k| ≤ L * B := by
  rw [finiteNaturalConvolution_comm]
  have h := finiteNaturalConvolution_abs_le_leftPointwise
    q p B L k hB hq hp
  simpa [mul_comm] using h

private theorem finiteNaturalConvolution_delta_right {m : ℕ} (p : ℕ → ℝ)
    {k : ℕ} (hk : k ≤ m) :
    finiteNaturalConvolution m 0 p (fun j => if j = 0 then 1 else 0) k = p k := by
  classical
  let F := (Finset.range (m + 1)).product (Finset.range (0 + 1)) |>.filter
    (fun ij => ij.1 + ij.2 = k)
  unfold finiteNaturalConvolution
  change (∑ ij ∈ F, p ij.1 * (if ij.2 = 0 then 1 else 0)) = p k
  have hpair : (k, 0) ∈ F := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ?_⟩, ?_⟩
    · simp
    · simp
  have hsub : ({(k, 0)} : Finset (ℕ × ℕ)) ⊆ F := by
    intro ij hij
    have hij' : ij = (k, 0) := by simpa using hij
    simpa [hij'] using hpair
  have hzero : ∀ ij ∈ F, ij ∉ ({(k, 0)} : Finset (ℕ × ℕ)) →
      p ij.1 * (if ij.2 = 0 then 1 else 0) = 0 := by
    intro ij hij hnot
    by_cases hj : ij.2 = 0
    · have hsum := (Finset.mem_filter.mp hij).2
      have hEq : ij = (k, 0) := by
        apply Prod.ext
        · omega
        · exact hj
      exact (hnot (by simp [hEq])).elim
    · simp [hj]
  calc
    _ = ∑ ij ∈ ({(k, 0)} : Finset (ℕ × ℕ)),
        p ij.1 * (if ij.2 = 0 then 1 else 0) :=
      (Finset.sum_subset hsub hzero).symm
    _ = p k := by simp

/-- Exact hypergeometric block atoms have a uniform Gaussian-scale upper
bound, including the finitely many short durations. -/
theorem exists_hypergeometricWeight_pointwise_atom_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ k ∈ Finset.range (m + 1),
      |WalkTails.hypergeometricWeight m k| ≤ C / Real.sqrt (m : ℝ) := by
  have hlocal := eventually_hypergeometricWeight_localGaussian (ε := 1) (by norm_num)
  obtain ⟨mG, hmG⟩ := Filter.eventually_atTop.1 hlocal
  let C : ℝ := 3 + Real.sqrt (mG : ℝ)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro m hm k hk
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
    have hpnonneg := WalkTails.hypergeometricWeight_nonneg m k
    by_cases hlarge : mG ≤ m
    · have hlocalM :
          |Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k -
            2 / Real.sqrt Real.pi *
              Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))| < 1 := by
        have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        exact hmG m hlarge k hk'
      have hpiRoot : 1 ≤ Real.sqrt Real.pi := by
        calc
          1 = Real.sqrt 1 := by norm_num
          _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      have hcoef : 2 / Real.sqrt Real.pi ≤ 2 := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
        nlinarith
      have harg : -(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith [sq_nonneg (2 * (k : ℝ) - (m : ℝ))]
        · positivity
      have hgaussian :
          2 / Real.sqrt Real.pi *
            Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) ≤ 2 := by
        calc
          _ ≤ 2 * Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
          _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left
            (Real.exp_le_one_iff.mpr harg) (by norm_num)
          _ = 2 := by norm_num
      have hscaled : Real.sqrt (m : ℝ) *
          WalkTails.hypergeometricWeight m k ≤ 3 := by
        have hupper := (abs_lt.mp hlocalM).2
        linarith
      have hpUpper : WalkTails.hypergeometricWeight m k ≤ 3 / Real.sqrt (m : ℝ) := by
        rw [le_div_iff₀ hmsqrt]
        simpa [mul_comm] using hscaled
      have hCthree : (3 : ℝ) ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg (mG : ℝ)]
      rw [abs_of_nonneg hpnonneg]
      calc
        WalkTails.hypergeometricWeight m k ≤ 3 / Real.sqrt (m : ℝ) := hpUpper
        _ ≤ C / Real.sqrt (m : ℝ) :=
          div_le_div_of_nonneg_right hCthree (Real.sqrt_nonneg _)
    · have hmLt : (m : ℝ) < (mG : ℝ) := by exact_mod_cast (Nat.lt_of_not_ge hlarge)
      have hmass := WalkTails.sum_hypergeometricWeight m
      have hsingle : WalkTails.hypergeometricWeight m k ≤ 1 := by
        calc
          _ ≤ ∑ i ∈ Finset.range (m + 1), WalkTails.hypergeometricWeight m i :=
            Finset.single_le_sum
              (fun i hi => WalkTails.hypergeometricWeight_nonneg m i) hk
          _ = 1 := hmass
      have hrootle : Real.sqrt (m : ℝ) ≤ Real.sqrt (mG : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hlarge)))
      have hrootC : Real.sqrt (m : ℝ) ≤ C := by dsimp [C]; linarith
      have hone : (1 : ℝ) ≤ C / Real.sqrt (m : ℝ) := by
        rw [le_div_iff₀ hmsqrt]
        nlinarith
      rw [abs_of_nonneg hpnonneg]
      exact hsingle.trans hone

/-- The largest duration in a list of pair-block lengths. -/
def pairBlockListMaxDuration : List ℕ → ℕ
  | [] => 0
  | m :: ms => max m (pairBlockListMaxDuration ms)

/-- The law of a finite composition has a Gaussian-scale atom bound controlled
by its longest block. -/
theorem exists_hypergeometricBlockListLaw_max_atom_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ms : List ℕ, ms ≠ [] →
      (∀ m ∈ ms, 0 < m) → ∀ j ∈ Finset.range (ms.sum + 1),
        |hypergeometricBlockListLaw ms j| ≤
          C / Real.sqrt (pairBlockListMaxDuration ms : ℝ) := by
  obtain ⟨C, hC, hatom⟩ := exists_hypergeometricWeight_pointwise_atom_bound
  refine ⟨C, hC, ?_⟩
  intro ms
  induction ms with
  | nil =>
      intro hne
      cases hne rfl
  | cons m ms ih =>
      intro hne hpositive j hj
      have hmpos : 0 < m := hpositive m (by simp)
      have hsingle := hatom m hmpos
      by_cases hms : ms = []
      · subst ms
        have hj' : j ∈ Finset.range (m + 1) := by simpa using hj
        have hlaw : hypergeometricBlockListLaw [m] j =
            WalkTails.hypergeometricWeight m j := by
          simp only [hypergeometricBlockListLaw, List.sum_nil]
          exact finiteNaturalConvolution_delta_right _ (Nat.le_of_lt_succ
            (Finset.mem_range.mp hj'))
        rw [hlaw]
        simpa [pairBlockListMaxDuration] using hsingle j hj'
      · have htailPositive : ∀ a ∈ ms, 0 < a := by
          intro a ha
          exact hpositive a (by simp [ha])
        have htail := ih hms htailPositive
        have htailMass :
            ∑ k ∈ Finset.range (ms.sum + 1), |hypergeometricBlockListLaw ms k| = 1 := by
          calc
            _ = ∑ k ∈ Finset.range (ms.sum + 1), hypergeometricBlockListLaw ms k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [abs_of_nonneg (hypergeometricBlockListLaw_nonneg ms k)]
            _ = 1 := hypergeometricBlockListLaw_sum_one ms
        have hfirstMass :
            ∑ k ∈ Finset.range (m + 1),
              |WalkTails.hypergeometricWeight m k| = 1 := by
          calc
            _ = ∑ k ∈ Finset.range (m + 1), WalkTails.hypergeometricWeight m k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [abs_of_nonneg (WalkTails.hypergeometricWeight_nonneg m k)]
            _ = 1 := WalkTails.sum_hypergeometricWeight m
        by_cases hmMax : pairBlockListMaxDuration ms ≤ m
        · have hconv := finiteNaturalConvolution_abs_le_leftPointwise
            (WalkTails.hypergeometricWeight m) (hypergeometricBlockListLaw ms)
            (C / Real.sqrt (m : ℝ)) 1 j (by positivity) (by
              intro k hk
              exact hsingle k hk) htailMass.le
          have hmax : pairBlockListMaxDuration (m :: ms) = m := by
            simp [pairBlockListMaxDuration, Nat.max_eq_left hmMax]
          rw [show hypergeometricBlockListLaw (m :: ms) j =
            finiteNaturalConvolution m ms.sum (WalkTails.hypergeometricWeight m)
              (hypergeometricBlockListLaw ms) j by rfl, hmax]
          simpa using hconv
        · have hmLt : m < pairBlockListMaxDuration ms := Nat.lt_of_not_ge hmMax
          have hconv := finiteNaturalConvolution_abs_le_rightPointwise
            (WalkTails.hypergeometricWeight m) (hypergeometricBlockListLaw ms)
            1 (C / Real.sqrt (pairBlockListMaxDuration ms : ℝ)) j (by positivity)
            hfirstMass.le (fun k hk => htail k hk)
          have hmax : pairBlockListMaxDuration (m :: ms) =
              pairBlockListMaxDuration ms := by
            simp [pairBlockListMaxDuration, Nat.max_eq_right hmLt.le]
          rw [show hypergeometricBlockListLaw (m :: ms) j =
            finiteNaturalConvolution m ms.sum (WalkTails.hypergeometricWeight m)
              (hypergeometricBlockListLaw ms) j by rfl, hmax]
          simpa [one_mul] using hconv

private theorem finiteNaturalConvolution_sub_split {m n : ℕ}
    (p q r s : ℕ → ℝ) (j : ℕ) :
    finiteNaturalConvolution m n p r j - finiteNaturalConvolution m n q s j =
      finiteNaturalConvolution m n (fun k => p k - q k) r j +
        finiteNaturalConvolution m n q (fun k => r k - s k) j := by
  classical
  let F := ((Finset.range (m + 1)).product (Finset.range (n + 1))).filter
    (fun ij => ij.1 + ij.2 = j)
  change (∑ ij ∈ F, p ij.1 * r ij.2) - (∑ ij ∈ F, q ij.1 * s ij.2) =
    (∑ ij ∈ F, (p ij.1 - q ij.1) * r ij.2) +
      (∑ ij ∈ F, q ij.1 * (r ij.2 - s ij.2))
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- Uniformly over positive block lists, the exact law and its hybrid
Gaussianization differ pointwise by the longest-block local error plus a
smoothed total-variation error. -/
theorem exists_hypergeometricBlockListLaw_hybrid_pointwise_error :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ m₀ : ℕ,
      ∀ mCut : ℕ, m₀ ≤ mCut → 0 < mCut →
      ∀ ms : List ℕ, ms ≠ [] → (∀ m ∈ ms, 0 < m) →
      mCut ≤ pairBlockListMaxDuration ms →
      ∀ j ∈ Finset.range (ms.sum + 1),
        |hypergeometricBlockListLaw ms j - largeBlockGaussianListLaw mCut ms j| ≤
          C₁ / (pairBlockListMaxDuration ms : ℝ) +
            C₂ * (ms.length : ℝ) /
              (Real.sqrt (pairBlockListMaxDuration ms : ℝ) *
                Real.sqrt (mCut : ℝ)) := by
  obtain ⟨Ccons, hCcons, mcons, hcons⟩ :=
    exists_hypergeometricBlockListLaw_cons_pointwise_hybrid_error
  obtain ⟨Cblock, hCblock, mblock, hBlockL1⟩ :=
    exists_normalized_hypergeometricGaussian_L1_error
  obtain ⟨Ca, hCa, hatom⟩ := exists_hypergeometricBlockListLaw_max_atom_bound
  let C₁ : ℝ := Ccons
  let C₂ : ℝ := Ccons + Cblock * Ca
  let m₀ := max mcons mblock
  have hmcons : mcons ≤ m₀ := by simp [m₀]
  have hmblock : mblock ≤ m₀ := by simp [m₀]
  refine ⟨C₁, ?_, C₂, ?_, m₀, ?_⟩
  · exact hCcons
  · dsimp [C₂]
    positivity
  · intro mCut hm₀cut hmCutPos ms
    induction ms with
    | nil =>
        intro hne
        cases hne rfl
    | cons m ms ih =>
        intro hne hpositive hcutMax j hj
        let Mtail := pairBlockListMaxDuration ms
        let M := pairBlockListMaxDuration (m :: ms)
        let p : ℕ → ℝ := WalkTails.hypergeometricWeight m
        let w : ℕ → ℝ := largeBlockGaussianWeight mCut m
        let r : ℕ → ℝ := hypergeometricBlockListLaw ms
        let s : ℕ → ℝ := largeBlockGaussianListLaw mCut ms
        have hM : M = max m Mtail := by rfl
        have hexact : hypergeometricBlockListLaw (m :: ms) j =
            finiteNaturalConvolution m ms.sum p r j := rfl
        have hhybrid : largeBlockGaussianListLaw mCut (m :: ms) j =
            finiteNaturalConvolution m ms.sum w s j := rfl
        have hdecomp :
            hypergeometricBlockListLaw (m :: ms) j -
                largeBlockGaussianListLaw mCut (m :: ms) j =
              finiteNaturalConvolution m ms.sum (fun k => p k - w k) r j +
                finiteNaturalConvolution m ms.sum w (fun k => r k - s k) j := by
          rw [hexact, hhybrid]
          exact finiteNaturalConvolution_sub_split p w r s j
        have hmpos : 0 < m := hpositive m (by simp)
        have hfirstMass :
            ∑ k ∈ Finset.range (m + 1), |WalkTails.hypergeometricWeight m k| = 1 := by
          calc
            _ = ∑ k ∈ Finset.range (m + 1), WalkTails.hypergeometricWeight m k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [abs_of_nonneg (WalkTails.hypergeometricWeight_nonneg m k)]
            _ = 1 := WalkTails.sum_hypergeometricWeight m
        have htailPositive : ∀ a ∈ ms, 0 < a := by
          intro a ha
          exact hpositive a (by simp [ha])
        by_cases hmShort : m < mCut
        · have hcutTail : mCut ≤ Mtail := by
            simp only [pairBlockListMaxDuration] at hcutMax
            omega
          have htailNe : ms ≠ [] := by
            intro hempty
            simp [hempty, Mtail, pairBlockListMaxDuration] at hcutTail
            omega
          have hweight : w = p := by
            funext k
            simp [w, p, largeBlockGaussianWeight, Nat.not_le_of_gt hmShort]
          have hTailBound := ih htailNe htailPositive hcutTail
          have hTailE : ∀ k ∈ Finset.range (ms.sum + 1),
              |r k - s k| ≤
                C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
                  (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by
            intro k hk
            simpa [Mtail, r, s, C₁, C₂] using hTailBound k hk
          have hshortEq :
              hypergeometricBlockListLaw (m :: ms) j -
                  largeBlockGaussianListLaw mCut (m :: ms) j =
                finiteNaturalConvolution m ms.sum p (fun k => r k - s k) j := by
            rw [hdecomp, hweight]
            simp [finiteNaturalConvolution]
          have hshortBound := finiteNaturalConvolution_abs_le_rightPointwise
            p (fun k => r k - s k) 1
            (C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
              (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ))) j (by positivity)
            hfirstMass.le hTailE
          have hmaxEq : M = Mtail := by
            rw [hM]
            exact Nat.max_eq_right (le_of_lt (lt_of_lt_of_le hmShort hcutTail))
          have hlen : (ms.length : ℝ) ≤ ((m :: ms).length : ℝ) := by simp
          have hden : 0 < Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ) := by
            have hMpos : 0 < Mtail := lt_of_lt_of_le hmCutPos hcutTail
            positivity
          have hbound :
              C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
                  (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) ≤
                C₁ / (M : ℝ) + C₂ * ((m :: ms).length : ℝ) /
                  (Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ)) := by
            rw [hmaxEq]
            exact add_le_add le_rfl
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlen (le_of_lt (by positivity))) hden.le)
          rw [hshortEq]
          have hshortBound' :
              |finiteNaturalConvolution m ms.sum p (fun k => r k - s k) j| ≤
                C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
                  (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by
            simpa [one_mul] using hshortBound
          exact hshortBound'.trans hbound
        · have hmCutm : mCut ≤ m := Nat.le_of_not_gt hmShort
          by_cases htailLe : Mtail ≤ m
          · have hM_eq : M = m := by
              rw [hM]
              exact Nat.max_eq_left htailLe
            have hconsBound := hcons mCut m (le_trans hmcons hm₀cut)
              hmCutPos hmCutm ms j
            have hCcons₂ : Ccons ≤ C₂ := by
              change Ccons ≤ Ccons + Cblock * Ca
              exact le_add_of_nonneg_right (mul_nonneg hCblock.le hCa.le)
            have htailLen : (ms.length : ℝ) ≤ ((m :: ms).length : ℝ) := by simp
            have hden : 0 < Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ) := by
              have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
              positivity
            have hbound :
                Ccons / (m : ℝ) + Ccons * (ms.length : ℝ) /
                    (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ)) ≤
                  C₁ / (M : ℝ) + C₂ * ((m :: ms).length : ℝ) /
                    (Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ)) := by
              rw [hM_eq]
              change Ccons / (m : ℝ) + Ccons * (ms.length : ℝ) /
                  (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ)) ≤
                Ccons / (m : ℝ) + C₂ * ((m :: ms).length : ℝ) /
                  (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ))
              exact add_le_add le_rfl
                (div_le_div_of_nonneg_right
                  (calc
                    Ccons * (ms.length : ℝ) ≤ C₂ * (ms.length : ℝ) :=
                      mul_le_mul_of_nonneg_right hCcons₂ (Nat.cast_nonneg _)
                    _ ≤ C₂ * ((m :: ms).length : ℝ) :=
                      mul_le_mul_of_nonneg_left htailLen (le_of_lt (by dsimp [C₂]; positivity)))
                  hden.le)
            simpa [C₁, M, hM_eq] using hconsBound.trans hbound
          · have hmaxLt : m < Mtail := Nat.lt_of_not_ge htailLe
            have hcutTail : mCut ≤ Mtail := by
              simp only [pairBlockListMaxDuration] at hcutMax
              omega
            have hMtailPos : 0 < Mtail := lt_of_lt_of_le hmCutPos hcutTail
            have htailNe : ms ≠ [] := by
              intro hempty
              simp [hempty, Mtail, pairBlockListMaxDuration] at hmaxLt
            have hTailBound := ih htailNe htailPositive hcutTail
            have hTailE : ∀ k ∈ Finset.range (ms.sum + 1),
                |r k - s k| ≤
                  C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
                    (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by
              intro k hk
              simpa [Mtail, r, s, C₁, C₂] using hTailBound k hk
            have hAtomTail : ∀ k ∈ Finset.range (ms.sum + 1),
                |r k| ≤ Ca / Real.sqrt (Mtail : ℝ) := by
              intro k hk
              exact hatom ms htailNe htailPositive k hk
            have hprofile := hBlockL1 m (le_trans hmblock (le_trans hm₀cut hmCutm))
            have hL1m :
                ∑ k ∈ Finset.range (m + 1),
                  |WalkTails.hypergeometricWeight m k -
                    normalizedSampledHypergeometricGaussianWeight m k| ≤
                  Cblock / Real.sqrt (m : ℝ) := by
              simpa [normalizedSampledHypergeometricGaussianWeight,
                sampledHypergeometricGaussianWeight] using hprofile.2.2.2
            have hqMass :
                ∑ k ∈ Finset.range (m + 1),
                  |normalizedSampledHypergeometricGaussianWeight m k| = 1 := by
              have hqnonneg : ∀ k ∈ Finset.range (m + 1),
                  0 ≤ normalizedSampledHypergeometricGaussianWeight m k := by
                intro k hk
                dsimp [normalizedSampledHypergeometricGaussianWeight,
                  sampledHypergeometricGaussianWeight]
                positivity
              calc
                _ = ∑ k ∈ Finset.range (m + 1),
                    normalizedSampledHypergeometricGaussianWeight m k := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [abs_of_nonneg (hqnonneg k hk)]
                _ = 1 := hprofile.2.2.1
            have hweightLong : w =
                normalizedSampledHypergeometricGaussianWeight m := by
              funext k
              simp [w, largeBlockGaussianWeight, hmCutm]
            have hL1m' :
                ∑ k ∈ Finset.range (m + 1), |p k - w k| ≤
                  Cblock / Real.sqrt (m : ℝ) := by
              simpa [p, hweightLong] using hL1m
            have hwMass :
                ∑ k ∈ Finset.range (m + 1), |w k| = 1 := by
              simpa [hweightLong] using hqMass
            have hterm1 := finiteNaturalConvolution_abs_le_rightPointwise
              (fun k => p k - w k) r (Cblock / Real.sqrt (m : ℝ))
              (Ca / Real.sqrt (Mtail : ℝ)) j (by positivity) hL1m' hAtomTail
            have hterm2 := finiteNaturalConvolution_abs_le_rightPointwise
              w (fun k => r k - s k) 1
              (C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
                (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)))
              j (by dsimp [C₁, C₂]; positivity) hwMass.le hTailE
            have hrootCompare : Real.sqrt (mCut : ℝ) ≤ Real.sqrt (m : ℝ) :=
              Real.sqrt_le_sqrt (by exact_mod_cast hmCutm)
            have hClDiv : Cblock / Real.sqrt (m : ℝ) ≤ Cblock / Real.sqrt (mCut : ℝ) :=
              div_le_div_of_nonneg_left hCblock.le
                (Real.sqrt_pos.mpr (by exact_mod_cast hmCutPos)) hrootCompare
            have hterm1' :
                |finiteNaturalConvolution m ms.sum (fun k => p k - w k) r j| ≤
                  C₂ / (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by
              have hraw :
                  (Cblock / Real.sqrt (mCut : ℝ)) * (Ca / Real.sqrt (Mtail : ℝ)) =
                    (Cblock * Ca) /
                      (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by ring
              have hprod : Cblock * Ca ≤ C₂ := by dsimp [C₂]; linarith
              calc
                _ ≤ (Cblock / Real.sqrt (m : ℝ)) * (Ca / Real.sqrt (Mtail : ℝ)) := hterm1
                _ ≤ (Cblock / Real.sqrt (mCut : ℝ)) * (Ca / Real.sqrt (Mtail : ℝ)) :=
                  mul_le_mul_of_nonneg_right hClDiv (div_nonneg hCa.le (Real.sqrt_nonneg _))
                _ = (Cblock * Ca) /
                    (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := hraw
                _ ≤ C₂ / (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) :=
                  div_le_div_of_nonneg_right hprod (by positivity)
            have hterm2' :
                |finiteNaturalConvolution m ms.sum w (fun k => r k - s k) j| ≤
                  C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
                    (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by
              simpa [one_mul] using hterm2
            have htriangle :
                |hypergeometricBlockListLaw (m :: ms) j -
                  largeBlockGaussianListLaw mCut (m :: ms) j| ≤
                |finiteNaturalConvolution m ms.sum (fun k => p k - w k) r j| +
                  |finiteNaturalConvolution m ms.sum w (fun k => r k - s k) j| := by
              rw [hdecomp]
              exact abs_add_le _ _
            have hlenEq : ((m :: ms).length : ℝ) = (ms.length : ℝ) + 1 := by simp
            have hmixEq :
                C₂ / (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) +
                  C₂ * (ms.length : ℝ) /
                    (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) =
                C₂ * ((m :: ms).length : ℝ) /
                  (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by
              rw [hlenEq]
              ring
            have hM_eq : M = Mtail := by
              rw [hM]
              exact Nat.max_eq_right hmaxLt.le
            have hbound :
                C₁ / (Mtail : ℝ) + C₂ * ((m :: ms).length : ℝ) /
                    (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) ≤
                  C₁ / (M : ℝ) + C₂ * ((m :: ms).length : ℝ) /
                    (Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ)) := by
              rw [hM_eq]
            calc
              _ ≤ |finiteNaturalConvolution m ms.sum (fun k => p k - w k) r j| +
                  |finiteNaturalConvolution m ms.sum w (fun k => r k - s k) j| := htriangle
              _ ≤ C₂ / (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) +
                  (C₁ / (Mtail : ℝ) + C₂ * (ms.length : ℝ) /
                    (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ))) :=
                add_le_add hterm1' hterm2'
              _ = C₁ / (Mtail : ℝ) + C₂ * ((m :: ms).length : ℝ) /
                  (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)) := by
                rw [← add_assoc, add_comm
                  (C₂ / (Real.sqrt (Mtail : ℝ) * Real.sqrt (mCut : ℝ)))
                  (C₁ / (Mtail : ℝ)), add_assoc, hmixEq]
              _ ≤ C₁ / (M : ℝ) + C₂ * ((m :: ms).length : ℝ) /
                  (Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ)) := hbound

private theorem finiteConvolution_eq_finiteNaturalConvolution
    {m n : ℕ} (pI qI : ℤ → ℝ) (pN qN : ℕ → ℝ)
    (hp : ∀ a ∈ Finset.Icc (0 : ℤ) m, pI a = pN a.toNat)
    (hq : ∀ b ∈ Finset.Icc (0 : ℤ) n, qI b = qN b.toNat)
    (hqzero : ∀ b : ℤ, b ∉ Finset.Icc (0 : ℤ) n → qI b = 0)
    (j : ℕ) :
    WalkTails.finiteConvolution (Finset.Icc (0 : ℤ) m) pI qI (j : ℤ) =
      finiteNaturalConvolution m n pN qN j := by
  classical
  let A : Finset ℤ := Finset.Icc (0 : ℤ) m
  let F : Finset (ℕ × ℕ) :=
    ((Finset.range (m + 1)).product (Finset.range (n + 1))).filter
      (fun ij => ij.1 + ij.2 = j)
  let G : Finset ℤ := A.filter (fun a => (j : ℤ) - a ∈ Finset.Icc (0 : ℤ) n)
  have hrestrict :
      WalkTails.finiteConvolution A pI qI (j : ℤ) =
        ∑ a ∈ G, pI a * qI ((j : ℤ) - a) := by
    unfold WalkTails.finiteConvolution
    symm
    apply Finset.sum_subset
    · intro a ha
      exact (Finset.mem_filter.mp ha).1
    · intro a ha haG
      have hnot : (j : ℤ) - a ∉ Finset.Icc (0 : ℤ) n := by
        intro hb
        exact haG (Finset.mem_filter.mpr ⟨ha, hb⟩)
      rw [hqzero _ hnot]
      simp
  have hbij :
      (∑ ij ∈ F, pN ij.1 * qN ij.2) =
        ∑ a ∈ G, pI a * qI ((j : ℤ) - a) := by
    refine Finset.sum_bij (s := F) (t := G)
      (fun ij _ => (ij.1 : ℤ)) ?_ ?_ ?_ ?_
    · intro ij hij
      rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
      rcases Finset.mem_product.mp hprod with ⟨hi, hb⟩
      have hiLe : ij.1 ≤ m := by simp only [Finset.mem_range] at hi; omega
      have hbLe : ij.2 ≤ n := by simp only [Finset.mem_range] at hb; omega
      have hdiff : (j : ℤ) - (ij.1 : ℤ) = (ij.2 : ℤ) := by
        have hnat : j - ij.1 = ij.2 := by omega
        have hiLej : ij.1 ≤ j := by omega
        rw [← Int.natCast_sub hiLej]
        exact_mod_cast hnat
      simp only [G, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ?_, ?_⟩
      · constructor
        · exact_mod_cast (Nat.zero_le ij.1)
        · exact_mod_cast hiLe
      · rw [hdiff]
        exact Finset.mem_Icc.mpr ⟨by exact_mod_cast (Nat.zero_le ij.2), by exact_mod_cast hbLe⟩
    · intro ij hij ij' hij' heq
      have hfst : ij.1 = ij'.1 := by exact_mod_cast heq
      have hsum := (Finset.mem_filter.mp hij).2
      have hsum' := (Finset.mem_filter.mp hij').2
      apply Prod.ext
      · exact hfst
      · omega
    · intro a ha
      rcases Finset.mem_filter.mp ha with ⟨haA, hbA⟩
      rcases Finset.mem_Icc.mp haA with ⟨ha0, ham⟩
      rcases Finset.mem_Icc.mp hbA with ⟨hb0, hbn⟩
      let i : ℕ := a.toNat
      let k : ℕ := ((j : ℤ) - a).toNat
      have hiCast : (i : ℤ) = a := by
        exact Int.toNat_of_nonneg ha0
      have hkCast : (k : ℤ) = (j : ℤ) - a := by
        exact Int.toNat_of_nonneg hb0
      have hiLe : i ≤ m := by
        have hiLe' : (i : ℤ) ≤ (m : ℤ) := by rw [hiCast]; exact ham
        exact_mod_cast hiLe'
      have hkLe : k ≤ n := by
        have hkLe' : (k : ℤ) ≤ (n : ℤ) := by rw [hkCast]; exact hbn
        exact_mod_cast hkLe'
      have hsum : i + k = j := by
        have hsumInt : (i : ℤ) + (k : ℤ) = (j : ℤ) := by
          rw [hiCast, hkCast]
          omega
        exact_mod_cast hsumInt
      refine ⟨(i, k), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ?_, hsum⟩
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hiLe),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hkLe)⟩
      · simp [i, hiCast]
    · intro ij hij
      rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
      rcases Finset.mem_product.mp hprod with ⟨hi, hb⟩
      have hiA : (ij.1 : ℤ) ∈ Finset.Icc (0 : ℤ) m := by
        simp only [Finset.mem_Icc]
        constructor
        · exact_mod_cast (Nat.zero_le ij.1)
        · exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      have hbA : (j : ℤ) - (ij.1 : ℤ) ∈ Finset.Icc (0 : ℤ) n := by
        have hdiff : (j : ℤ) - (ij.1 : ℤ) = (ij.2 : ℤ) := by
          have hnat : j - ij.1 = ij.2 := by omega
          have hiLej : ij.1 ≤ j := by omega
          rw [← Int.natCast_sub hiLej]
          exact_mod_cast hnat
        rw [hdiff]
        simp only [Finset.mem_Icc]
        constructor
        · exact_mod_cast (Nat.zero_le ij.2)
        · exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hb))
      rw [hp (ij.1 : ℤ) hiA, hq ((j : ℤ) - (ij.1 : ℤ)) hbA]
      have hdiff : (j : ℤ) - (ij.1 : ℤ) = (ij.2 : ℤ) := by
        have hnat : j - ij.1 = ij.2 := by omega
        have hiLej : ij.1 ≤ j := by omega
        rw [← Int.natCast_sub hiLej]
        exact_mod_cast hnat
      rw [hdiff]
      simp
  calc
    _ = ∑ a ∈ G, pI a * qI ((j : ℤ) - a) := hrestrict
    _ = ∑ ij ∈ F, pN ij.1 * qN ij.2 := hbij.symm
    _ = finiteNaturalConvolution m n pN qN j := by
      simp [finiteNaturalConvolution, F]

/-- The natural-indexed composition law is exactly the canonical
integer-indexed convolution of squared-binomial increments on its support. -/
theorem squaredBinomialConvolution_eq_hypergeometricBlockListLaw
    (ms : List ℕ) (j : ℕ) :
    WalkTails.squaredBinomialConvolution ms (j : ℤ) =
      hypergeometricBlockListLaw ms j := by
  induction ms generalizing j with
  | nil =>
      simp [WalkTails.squaredBinomialConvolution, WalkTails.deltaCoeff,
        hypergeometricBlockListLaw]
  | cons m ms ih =>
      let pI : ℤ → ℝ := WalkTails.hypergeometricIntWeight m
      let pN : ℕ → ℝ := WalkTails.hypergeometricWeight m
      let qI : ℤ → ℝ := WalkTails.squaredBinomialConvolution ms
      let qN : ℕ → ℝ := hypergeometricBlockListLaw ms
      have hp : ∀ a ∈ Finset.Icc (0 : ℤ) m, pI a = pN a.toNat := by
        intro a ha
        have ha0 : 0 ≤ a := (Finset.mem_Icc.mp ha).1
        have hcast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
        have h := WalkTails.hypergeometricIntWeight_eq_nat m a.toNat
        rw [hcast] at h
        exact h
      have hq : ∀ b ∈ Finset.Icc (0 : ℤ) ms.sum, qI b = qN b.toNat := by
        intro b hb
        have hb0 : 0 ≤ b := (Finset.mem_Icc.mp hb).1
        have hcast : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
        have h := ih b.toNat
        rw [hcast] at h
        exact h
      have hqzero : ∀ b : ℤ, b ∉ Finset.Icc (0 : ℤ) ms.sum → qI b = 0 := by
        intro b hb
        exact WalkTails.squaredBinomialConvolution_eq_zero_of_notMem hb
      change WalkTails.finiteConvolution (Finset.Icc (0 : ℤ) m) pI qI (j : ℤ) =
        finiteNaturalConvolution m ms.sum pN qN j
      exact finiteConvolution_eq_finiteNaturalConvolution pI qI pN qN hp hq hqzero j

/-- The exact composition expansion, written as the scalar composition
weight times the product law of its two independent rotated marks. -/
theorem spatialRenewal_eq_compositionPairLaw (σ2 : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (z : Site) (j₁ j₂ : ℕ)
    (h₁ : 2 * (j₁ : ℤ) = (n : ℤ) + z 0 + z 1)
    (h₂ : 2 * (j₂ : ℤ) = (n : ℤ) + z 0 - z 1) :
    Collision.spatialRenewal σ2 n z =
      ∑ c : Composition n,
        σ2 ^ c.length * (c.blocks.map fun k => srwKernel (2 * k) 0).prod *
          hypergeometricBlockListPairLaw c.blocks j₁ j₂ := by
  rw [Collision.spatialRenewal_eq_sum_compositions σ2 hn z]
  apply Finset.sum_congr rfl
  intro c hc
  have h₁' : 2 * (j₁ : ℤ) = (c.blocks.sum : ℤ) + z 0 + z 1 := by
    simpa only [c.blocks_sum] using h₁
  have h₂' : 2 * (j₂ : ℤ) = (c.blocks.sum : ℤ) + z 0 - z 1 := by
    simpa only [c.blocks_sum] using h₂
  rw [Collision.squareConvolution_eq c.blocks z (j₁ : ℤ) (j₂ : ℤ) h₁' h₂',
    squaredBinomialConvolution_eq_hypergeometricBlockListLaw,
    squaredBinomialConvolution_eq_hypergeometricBlockListLaw]
  simp only [hypergeometricBlockListPairLaw]
  ring

end Critical2DKPZ.SHF.Moments

end
