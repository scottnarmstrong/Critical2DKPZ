/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.FirstCollisionRunCombinatorics
public import Critical2DKPZ.Definitions.RescaledP2P
public import Critical2DKPZ.SHF.Limit.FirstMoment
import Critical2DKPZ.SHF.Flow.SlabProductsCore
import Mathlib.Tactic

/-! # Finite pair-simple collision expansions -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose
attribute [local instance] Classical.propDecidable

private theorem wordHead_fixed_run {h : ℕ} (σ2 : ℝ) (α : CollisionPair h)
    {n s r : ℕ} (hs : s ∈ Finset.Icc 1 n) (hr : r < n - s + 1)
    (x y : Fin h → Site) :
    (∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
      if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
        ∑' u : Fin h → Site, ∑' v : Fin h → Site,
          (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * σ2 *
            Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
            (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
              srwKernel r (v i - u i)) *
            blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y else 0) =
      ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * σ2 *
          Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
          (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
            srwKernel r (v i - u i)) *
          wordSumFrom σ2 (Finset.univ.erase α) (n - s - r) v y := by
  classical
  let k := n - s - r
  let Ru := configurationEndpointSet s x
  let Rv := configurationEndpointSet k y
  let F (m : ℕ) (w : CollisionWord h m) (u v : Fin h → Site) :=
    if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
      (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
        (∏ i, srwKernel s (u i - x i)) * σ2 *
        Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
        (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
          srwKernel r (v i - u i)) *
        blockWordKernel σ2 (List.ofFn w.1) k v y else 0
  have hwordExchange (m : ℕ) :
      (∑ w : CollisionWord h m, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        F m w u v) =
        ∑' u : Fin h → Site, ∑' v : Fin h → Site,
          ∑ w : CollisionWord h m, F m w u v := by
    apply sum_tsum_tsum_eq_tsum_tsum_sum_of_support Finset.univ Ru Rv
      (fun w u v => F m w u v)
    · intro w hw u hu v
      have hz := freeKernelProduct_zero_of_not_mem s x u hu
      simp [F, hz]
    · intro w hw u v hv
      have hz := blockWordKernel_zero_of_start_endpoint_not_mem σ2
        (List.ofFn w.1) k v y hv
      simp [F, hz]
  have hsIcc := Finset.mem_Icc.mp hs
  have hspos : 1 ≤ s := hsIcc.1
  have hsle : s ≤ n := hsIcc.2
  have hduration : s + r ≤ n := by omega
  have hklt : k < n := by
    dsimp [k]
    omega
  have hmExchange :
      (∑ m ∈ Finset.range n, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        ∑ w : CollisionWord h m, F m w u v) =
        ∑' u : Fin h → Site, ∑' v : Fin h → Site,
          ∑ m ∈ Finset.range n, ∑ w : CollisionWord h m, F m w u v := by
    apply sum_tsum_tsum_eq_tsum_tsum_sum_of_support (Finset.range n) Ru Rv
    · intro m hm u hu v
      apply Finset.sum_eq_zero
      intro w hw
      have hz := freeKernelProduct_zero_of_not_mem s x u hu
      simp [F, hz]
    · intro m hm u v hv
      apply Finset.sum_eq_zero
      intro w hw
      have hz := blockWordKernel_zero_of_start_endpoint_not_mem σ2
        (List.ofFn w.1) k v y hv
      simp [F, hz]
  calc
    _ = ∑ m ∈ Finset.range n, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
          ∑ w : CollisionWord h m, F m w u v := by
      apply Finset.sum_congr rfl
      intro m hm
      calc
        _ = ∑ w : CollisionWord h m, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
            F m w u v := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hcond : ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α
          · simp [F, hcond, k]
          · simp [F, hcond, k]
        _ = _ := hwordExchange m
    _ = _ := by
      rw [hmExchange]
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      let B : ℝ :=
        (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * σ2 *
          Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
          (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
            srwKernel r (v i - u i))
      have hwordSum (m : ℕ) :
          (∑ w : CollisionWord h m, F m w u v) =
            B * ∑ w : CollisionWord h m,
              if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
                blockWordKernel σ2 (List.ofFn w.1) k v y else 0 := by
        calc
          _ = ∑ w : CollisionWord h m,
              B * (if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
                blockWordKernel σ2 (List.ofFn w.1) k v y else 0) := by
            apply Finset.sum_congr rfl
            intro w hw
            simp only [F]
            by_cases hcond : ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α
            · simp [hcond, B]
            · simp [hcond, B]
          _ = _ := by rw [Finset.mul_sum]
      have hfactor :
          (∑ m ∈ Finset.range n, ∑ w : CollisionWord h m, F m w u v) =
            B * ∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
              if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
                blockWordKernel σ2 (List.ofFn w.1) k v y else 0 := by
        calc
          _ = ∑ m ∈ Finset.range n, B *
              (∑ w : CollisionWord h m,
                if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
                  blockWordKernel σ2 (List.ofFn w.1) k v y else 0) := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hwordSum m
          _ = _ := by rw [Finset.mul_sum]
      rw [hfactor, filteredTailWordSum_eq_wordSumFrom σ2 α hklt v y]

/-- The recursion for the word sum, obtained by peeling its first letter and
then its first run. -/
private theorem wordSumFrom_firstRun_decomp {h : ℕ} (σ2 : ℝ)
    (L : Finset (CollisionPair h)) (n : ℕ) (x y : Fin h → Site) :
    wordSumFrom σ2 L n x y =
      (∏ i, srwKernel n (y i - x i)) +
        ∑ α ∈ L, ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' u : Fin h → Site, ∑' v : Fin h → Site,
            (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
              (∏ i, srwKernel s (u i - x i)) * σ2 *
              Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
              (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                srwKernel r (v i - u i)) *
              wordSumFrom σ2 (Finset.univ.erase α) (n - s - r) v y := by
  classical
  rw [wordSumFrom_length_decomp]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  -- Move the finite word sum across the head-run time sums.
  simp only [blockWordKernel]
  have hword (m : ℕ) :
      (∑ w : CollisionWord h m,
        if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
          ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            ∑' u : Fin h → Site, ∑' v : Fin h → Site,
              (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) * σ2 *
                Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) *
                blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
        else 0) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑ w : CollisionWord h m,
          if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
            ∑' u : Fin h → Site, ∑' v : Fin h → Site,
              (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) * σ2 *
                Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) *
                blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
          else 0 := by
    calc
      _ = ∑ w : CollisionWord h m, ∑ s ∈ Finset.Icc 1 n,
          ∑ r ∈ Finset.range (n - s + 1),
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              ∑' u : Fin h → Site, ∑' v : Fin h → Site,
                (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                  (∏ i, srwKernel s (u i - x i)) * σ2 *
                  Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                    srwKernel r (v i - u i)) *
                  blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
            else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hc : ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α
          · simp [hc]
          · simp [hc]
      _ = ∑ s ∈ Finset.Icc 1 n, ∑ w : CollisionWord h m,
          ∑ r ∈ Finset.range (n - s + 1),
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              ∑' u : Fin h → Site, ∑' v : Fin h → Site,
                (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                  (∏ i, srwKernel s (u i - x i)) * σ2 *
                  Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                    srwKernel r (v i - u i)) *
                  blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
            else 0 := by rw [Finset.sum_comm]
      _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑ w : CollisionWord h m,
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              ∑' u : Fin h → Site, ∑' v : Fin h → Site,
                (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                  (∏ i, srwKernel s (u i - x i)) * σ2 *
                  Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                    srwKernel r (v i - u i)) *
                  blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
            else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_comm]
  have hmain :
      (∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
        if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
          ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            ∑' u : Fin h → Site, ∑' v : Fin h → Site,
              (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) * σ2 *
                Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) *
                blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
        else 0) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
          if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
            ∑' u : Fin h → Site, ∑' v : Fin h → Site,
              (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) * σ2 *
                Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) *
                blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
          else 0 := by
    calc
      _ = ∑ m ∈ Finset.range n, ∑ s ∈ Finset.Icc 1 n,
          ∑ r ∈ Finset.range (n - s + 1), ∑ w : CollisionWord h m,
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              ∑' u : Fin h → Site, ∑' v : Fin h → Site,
                (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                  (∏ i, srwKernel s (u i - x i)) * σ2 *
                  Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                    srwKernel r (v i - u i)) *
                  blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
            else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          exact hword m
      _ = ∑ s ∈ Finset.Icc 1 n, ∑ m ∈ Finset.range n,
          ∑ r ∈ Finset.range (n - s + 1), ∑ w : CollisionWord h m,
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              ∑' u : Fin h → Site, ∑' v : Fin h → Site,
                (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                  (∏ i, srwKernel s (u i - x i)) * σ2 *
                  Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                    srwKernel r (v i - u i)) *
                  blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
            else 0 := by rw [Finset.sum_comm]
      _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              ∑' u : Fin h → Site, ∑' v : Fin h → Site,
                (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                  (∏ i, srwKernel s (u i - x i)) * σ2 *
                  Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                    srwKernel r (v i - u i)) *
                  blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
            else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_comm]
  calc
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              ∑' u : Fin h → Site, ∑' v : Fin h → Site,
                (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                  (∏ i, srwKernel s (u i - x i)) * σ2 *
                  Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                    srwKernel r (v i - u i)) *
                  blockWordKernel σ2 (List.ofFn w.1) (n - s - r) v y
            else 0 := hmain
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' u : Fin h → Site, ∑' v : Fin h → Site,
            (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
              (∏ i, srwKernel s (u i - x i)) * σ2 *
              Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
              (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                srwKernel r (v i - u i)) *
              wordSumFrom σ2 (Finset.univ.erase α) (n - s - r) v y := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      exact wordHead_fixed_run σ2 α hs (by simpa using hr) x y

private theorem firstRun_tail_sum_eq {h : ℕ} (σ2 : ℝ) (n : ℕ)
    (α : CollisionPair h) {s r m : ℕ} (hs : s ∈ Finset.Icc 1 n)
    (hdecomp : s + r + m = n)
    (x y : Fin h → Site)
    (hIH : ∀ m' < n, ∀ (L : Finset (CollisionPair h)) (x' y' : Fin h → Site),
      (∑ A' ∈ (collisionEdges m' h).powerset.filter
          (fun A' => IsPairSimple A' ∧ FirstPairIn L A'),
        σ2 ^ A'.card * collisionSubsetCoefficient m' h A' x' y') =
        wordSumFrom σ2 L m' x' y') :
    (∑ S ∈ runTimeSets r, ∑ A' ∈ (collisionEdges m h).powerset.filter
        (fun A' => IsPairSimple A' ∧ FirstPairIn (Finset.univ.erase α) A'),
      σ2 ^ (runEdges α s S ∪ shiftEdges (s + r) A').card *
        collisionSubsetCoefficient (s + r + m) h
          (runEdges α s S ∪ shiftEdges (s + r) A') x y) =
      ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * σ2 *
          (if v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
          Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
          (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
            srwKernel r (v i - u i)) *
          wordSumFrom σ2 (Finset.univ.erase α) m v y := by
  classical
  let Aset := (collisionEdges m h).powerset.filter
    (fun A' => IsPairSimple A' ∧ FirstPairIn (Finset.univ.erase α) A')
  let Ru := configurationEndpointSet s x
  let Rv := configurationEndpointSet m y
  have hmain :
      (∑ S ∈ runTimeSets r, ∑ A' ∈ Aset,
        σ2 ^ (runEdges α s S ∪ shiftEdges (s + r) A').card *
          collisionSubsetCoefficient (s + r + m) h
            (runEdges α s S ∪ shiftEdges (s + r) A') x y) =
      ∑ S ∈ runTimeSets r, ∑ A' ∈ Aset, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) * σ2 ^ A'.card *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
          collisionSubsetCoefficient m h A' v y := by
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro A' hA
    have hSsub : S ⊆ Finset.Icc 1 r :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hAsub : A' ⊆ collisionEdges m h := Finset.mem_powerset.mp
      (Finset.mem_filter.mp hA).1
    exact weighted_firstRun_coefficient_eq σ2 α
      (Finset.mem_Icc.mp hs).1 hSsub hAsub x y
  have hAexchange (S : Finset ℕ) (hS : S ∈ runTimeSets r) :
      (∑ A' ∈ Aset, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) * σ2 ^ A'.card *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
          collisionSubsetCoefficient m h A' v y) =
      ∑' u : Fin h → Site, ∑' v : Fin h → Site, ∑ A' ∈ Aset,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) * σ2 ^ A'.card *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
          collisionSubsetCoefficient m h A' v y := by
    apply sum_tsum_tsum_eq_tsum_tsum_sum_of_support Aset Ru Rv
    · intro A' hA u hu v
      have hz := freeKernelProduct_zero_of_not_mem s x u hu
      simp [hz]
    · intro A' hA u v hv
      have hz := collisionSubsetCoefficient_zero_of_startSet_not_mem A' v y hv
      simp [hz]
  have htailSum (S : Finset ℕ) (hS : S ∈ runTimeSets r)
      (u v : Fin h → Site) :
      (∑ A' ∈ Aset,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) * σ2 ^ A'.card *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
          collisionSubsetCoefficient m h A' v y) =
      ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
        (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
        collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
        wordSumFrom σ2 (Finset.univ.erase α) m v y := by
    calc
      _ = ∑ A' ∈ Aset,
          (((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
            collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
            (σ2 ^ A'.card * collisionSubsetCoefficient m h A' v y)) := by
          apply Finset.sum_congr rfl
          intro A' hA
          ring
      _ = ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
            collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
            ∑ A' ∈ Aset, σ2 ^ A'.card * collisionSubsetCoefficient m h A' v y := by
          rw [← Finset.mul_sum]
      _ = _ := by
          congr 1
          have hmn : m < n := by
            have hs' := (Finset.mem_Icc.mp hs).1
            omega
          exact hIH m hmn (Finset.univ.erase α) v y
  have hSexchange :
      (∑ S ∈ runTimeSets r, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
          wordSumFrom σ2 (Finset.univ.erase α) m v y) =
      ∑' u : Fin h → Site, ∑' v : Fin h → Site, ∑ S ∈ runTimeSets r,
        ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
          wordSumFrom σ2 (Finset.univ.erase α) m v y := by
    let Ru' := configurationEndpointSet s x
    let Rv' := configEndpointBiUnion Ru' r
    apply sum_tsum_tsum_eq_tsum_tsum_sum_of_support (runTimeSets r) Ru' Rv'
    · intro S hS u hu v
      have hz := freeKernelProduct_zero_of_not_mem s x u hu
      simp [hz]
    · intro S hS u v hv
      by_cases hu : u ∈ Ru'
      · have hz := runCoefficient_zero_of_endpoint_biUnion_not_mem
          (A := S.image fun t => (t, α)) hu hv
        simp [hz]
      · have hz := freeKernelProduct_zero_of_not_mem s x u hu
        simp [hz]
  have hfactor (u v : Fin h → Site) :
      (∑ S ∈ runTimeSets r,
        ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
          wordSumFrom σ2 (Finset.univ.erase α) m v y) =
      ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
        (∏ i, srwKernel s (u i - x i)) * σ2 *
        wordSumFrom σ2 (Finset.univ.erase α) m v y) *
        ∑ S ∈ runTimeSets r, σ2 ^ S.card *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v := by
    calc
      _ = ∑ S ∈ runTimeSets r,
          (((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * σ2 *
            wordSumFrom σ2 (Finset.univ.erase α) m v y) *
            (σ2 ^ S.card * collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v)) := by
          apply Finset.sum_congr rfl
          intro S hS
          ring
      _ = _ := by rw [← Finset.mul_sum]
  calc
    _ = ∑ S ∈ runTimeSets r, ∑ A' ∈ Aset, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) * σ2 ^ A'.card *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
          collisionSubsetCoefficient m h A' v y := hmain
    _ = ∑ S ∈ runTimeSets r, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        ∑ A' ∈ Aset,
          (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) * σ2 ^ A'.card *
            collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
            collisionSubsetCoefficient m h A' v y := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hAexchange S hS
    _ = ∑ S ∈ runTimeSets r, ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
          wordSumFrom σ2 (Finset.univ.erase α) m v y := by
      apply Finset.sum_congr rfl
      intro S hS
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      exact htailSum S hS u v
    _ = ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        ∑ S ∈ runTimeSets r,
          ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * (σ2 * σ2 ^ S.card) *
            collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) *
            wordSumFrom σ2 (Finset.univ.erase α) m v y := hSexchange
    _ = ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        ((if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) * σ2 *
          wordSumFrom σ2 (Finset.univ.erase α) m v y) *
          ∑ S ∈ runTimeSets r, σ2 ^ S.card *
            collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v := by
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      exact hfactor u v
    _ = _ := by
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      by_cases hu : u α.1.1 = u α.1.2
      · rw [sum_runTimeSets_coefficient_eq σ2 α r u v hu]
        ring
      · simp [hu]

/-- Pair-simple selected-edge sums agree with the recursive word kernels when the first selected pair lies in `L`. -/
theorem sum_pairSimple_firstPairIn_eq_wordSumFrom {h : ℕ} (σ2 : ℝ) :
    ∀ (n : ℕ) (L : Finset (CollisionPair h)) (x y : Fin h → Site),
      ∑ A ∈ (collisionEdges n h).powerset.filter
          (fun A => IsPairSimple A ∧ FirstPairIn L A),
        σ2 ^ A.card * collisionSubsetCoefficient n h A x y =
        wordSumFrom σ2 L n x y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro L x y
      rw [sum_pairSimple_firstRun, wordSumFrom_firstRun_decomp]
      have hempty :
          σ2 ^ (∅ : Finset (ℕ × CollisionPair h)).card *
            collisionSubsetCoefficient n h ∅ x y =
              ∏ i, srwKernel n (y i - x i) := by
        simp [collisionSubsetCoefficient_empty_eq_prod_srwKernel]
      rw [hempty]
      congr 1
      apply Finset.sum_congr rfl
      intro α hα
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      have hsIcc := Finset.mem_Icc.mp hs
      have hrlt : r < n - s + 1 := by simpa using hr
      have hrle : r ≤ n - s := by omega
      have hm_lt : n - s - r < n := by omega
      have hdecomp : s + r + (n - s - r) = n := by omega
      have hrun := firstRun_tail_sum_eq σ2 n α hs hdecomp x y
        (by
          intro m hm L' x' y'
          exact ih m hm L' x' y')
      have hrun' :
          (∑ S ∈ runTimeSets r, ∑ A' ∈ (collisionEdges (n - s - r) h).powerset.filter
              (fun A' => IsPairSimple A' ∧ FirstPairIn (Finset.univ.erase α) A'),
            σ2 ^ (runEdges α s S ∪ shiftEdges (s + r) A').card *
              collisionSubsetCoefficient n h
                (runEdges α s S ∪ shiftEdges (s + r) A') x y) =
            ∑' u : Fin h → Site, ∑' v : Fin h → Site,
              (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) * σ2 *
                (if v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) *
                wordSumFrom σ2 (Finset.univ.erase α) (n - s - r) v y := by
        simpa only [hdecomp] using hrun
      calc
        _ = ∑' u : Fin h → Site, ∑' v : Fin h → Site,
              (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) * σ2 *
                (if v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) *
                wordSumFrom σ2 (Finset.univ.erase α) (n - s - r) v y := hrun'
        _ = ∑' u : Fin h → Site, ∑' v : Fin h → Site,
              (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) * σ2 *
                Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) *
                wordSumFrom σ2 (Finset.univ.erase α) (n - s - r) v y := by
            apply tsum_congr
            intro u
            apply tsum_congr
            intro v
            by_cases hu : u α.1.1 = u α.1.2 <;>
              by_cases hv : v α.1.1 = v α.1.2 <;>
              simp [hu, hv]

/-- The exact point-to-point moment resummation into words of maximal
same-pair runs. -/
theorem pointToPoint_moment_eq_wordSum (β : ℝ) (a n h : ℕ)
    (x y : Fin h → Site) :
    (∫ ω, ∏ i, pointToPoint β a n (x i) (y i) ω ∂disorderLaw) =
      (∑' m : ℕ, ∑ w : CollisionWord h m,
        blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y) +
        nonpairCollisionRemainder β n h x y := by
  rw [pointToPoint_collision_expansion_split]
  have hfirst (A : Finset (ℕ × CollisionPair h)) :
      IsPairSimple A ↔ IsPairSimple A ∧ FirstPairIn Finset.univ A := by
    constructor
    · intro hA
      exact ⟨hA, fun e _ _ => Finset.mem_univ _⟩
    · exact And.left
  have hpair :
      (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple,
        sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) =
      (∑ A ∈ (collisionEdges n h).powerset.filter
          (fun A => IsPairSimple A ∧ FirstPairIn Finset.univ A),
        sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) := by
    apply Finset.sum_congr
    · exact Finset.filter_congr fun A _ => hfirst A
    · intro A hA
      rfl
  have hword : wordSumFrom (sigmaSq β) Finset.univ n x y =
      ∑' m : ℕ, ∑ w : CollisionWord h m,
        blockWordKernel (sigmaSq β) (List.ofFn w.1) n x y := by
    unfold wordSumFrom
    simp
  rw [hpair, sum_pairSimple_firstPairIn_eq_wordSumFrom, hword]

private theorem pairing_cellTestWeight_eq_tsum_pointToPoint
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (φ : C_c(Plane × Plane, ℝ))
    (ω : Disorder) :
    (∫ p, φ p * rescaledP2P ϑ N s t p ω) =
      ∑' q : Site × Site,
        cellTestWeight N φ q.1 q.2 *
          pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω := by
  rw [← Critical2DKPZ.SHF.Limit.integral_polymerMeasure ϑ N s t ω φ,
    Critical2DKPZ.SHF.Flow.integral_polymerMeasure_cellTsum]
  unfold cellTestWeight
  apply tsum_congr
  intro q
  ring

private theorem integrable_prod_pointToPoint_config {h : ℕ} (β : ℝ) (a n : ℕ)
    (x y : Fin h → Site) :
    Integrable (fun ω => ∏ i, pointToPoint β a n (x i) (y i) ω) disorderLaw := by
  classical
  by_cases hh : h = 0
  · subst h
    simp
  · have hhpos : 0 < h := Nat.pos_of_ne_zero hh
    have hfactor (i : Fin h) :
        MemLp (fun ω => pointToPoint β a n (x i) (y i) ω) (h : ENNReal) disorderLaw :=
      Polymer.memLp_pointToPoint β a n (x i) (y i) (h : ENNReal) (by simp)
    have hmem := MemLp.fun_prod (s := (Finset.univ : Finset (Fin h)))
      (p := fun _ : Fin h => (h : ENNReal))
      (f := fun i ω => pointToPoint β a n (x i) (y i) ω)
      (by
        intro i hi
        exact hfactor i)
    have hsum :
        ∑ i ∈ (Finset.univ : Finset (Fin h)), ((h : ENNReal)⁻¹) = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hhpos.ne') (ENNReal.natCast_ne_top _)
    have hmemOne :
        MemLp (fun ω => ∏ i, pointToPoint β a n (x i) (y i) ω) 1 disorderLaw := by
      simpa [hsum] using hmem
    exact hmemOne.integrable (by norm_num)

private theorem prod_pairing_eq_cellConfigSum (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∏ i, ∫ p, φ i p * rescaledP2P ϑ N s t p ω) =
      ∑ q ∈ Fintype.piFinset
          (fun i : Fin h => (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset),
        ∏ i, cellTestWeight N (φ i) (q i).1 (q i).2 *
          pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            (q i).1 (q i).2 ω := by
  classical
  let S : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  have hzero (i : Fin h) (q : Site × Site) (hq : q ∉ S i) :
      cellTestWeight N (φ i) q.1 q.2 = 0 := by
    dsimp [S] at hq
    by_contra hne
    have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, φ i p) ≠ 0 := by
      intro hz
      apply hne
      simp [cellTestWeight, hz]
    exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).mem_toFinset.mpr hcell)
  have hcell (i : Fin h) :
      (∫ p, φ i p * rescaledP2P ϑ N s t p ω) =
        ∑ q ∈ S i,
          cellTestWeight N (φ i) q.1 q.2 *
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω := by
    rw [pairing_cellTestWeight_eq_tsum_pointToPoint]
    rw [tsum_eq_sum (s := S i)]
    intro q hq
    simp [hzero i q hq]
  calc
    _ = ∏ i, ∑ q ∈ S i,
          cellTestWeight N (φ i) q.1 q.2 *
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hcell i
    _ = _ := by
      rw [Finset.prod_univ_sum]

private theorem integral_prod_pairing_eq_finiteCellSum (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    (∫ ω, ∏ i, (∫ p, φ i p * rescaledP2P ϑ N s t p ω) ∂disorderLaw) =
      ∑ q ∈ Fintype.piFinset
          (fun i : Fin h => (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset),
        (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          ((∑' m : ℕ, ∑ w : CollisionWord h m,
              blockWordKernel (sigmaSq (criticalBeta ϑ N)) (List.ofFn w.1)
                (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
                (fun i => (q i).1) (fun i => (q i).2)) +
            nonpairCollisionRemainder (criticalBeta ϑ N)
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) h
              (fun i => (q i).1) (fun i => (q i).2)) := by
  classical
  let β := criticalBeta ϑ N
  let a := evenCeil ((N : ℝ) * s)
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let S : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  have hcell (ω : Disorder) := prod_pairing_eq_cellConfigSum ϑ N s t φ ω
  have htermInt (q : Fin h → Site × Site) :
      Integrable (fun ω => ∏ i,
        cellTestWeight N (φ i) (q i).1 (q i).2 *
          pointToPoint β a n (q i).1 (q i).2 ω) disorderLaw := by
    have hbase := integrable_prod_pointToPoint_config β a n
      (fun i => (q i).1) (fun i => (q i).2)
    have hfactor :
        (fun ω => ∏ i,
          cellTestWeight N (φ i) (q i).1 (q i).2 *
            pointToPoint β a n (q i).1 (q i).2 ω) =
        fun ω => (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          (∏ i, pointToPoint β a n (q i).1 (q i).2 ω) := by
      funext ω
      rw [Finset.prod_mul_distrib]
    rw [hfactor]
    exact hbase.const_mul _
  have hrew (ω : Disorder) :
      (∏ i, (∫ p, φ i p * rescaledP2P ϑ N s t p ω)) =
        ∑ q ∈ Fintype.piFinset S,
          ∏ i, cellTestWeight N (φ i) (q i).1 (q i).2 *
            pointToPoint β a n (q i).1 (q i).2 ω := by
    simpa [β, a, n, S] using hcell ω
  rw [show (fun ω => ∏ i, (∫ p, φ i p * rescaledP2P ϑ N s t p ω)) =
      fun ω => ∑ q ∈ Fintype.piFinset S,
        ∏ i, cellTestWeight N (φ i) (q i).1 (q i).2 *
          pointToPoint β a n (q i).1 (q i).2 ω from funext hrew]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    have hfactor :
        (fun ω => ∏ i, cellTestWeight N (φ i) (q i).1 (q i).2 *
          pointToPoint β a n (q i).1 (q i).2 ω) =
        fun ω => (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          (∏ i, pointToPoint β a n (q i).1 (q i).2 ω) := by
      funext ω
      rw [Finset.prod_mul_distrib]
    rw [hfactor, integral_const_mul, pointToPoint_moment_eq_wordSum]
  · intro q hq
    exact htermInt q

private def sitePairConfigEquiv (h : ℕ) :
    (Fin h → Site × Site) ≃ ((Fin h → Site) × (Fin h → Site)) where
  toFun q := (fun i => (q i).1, fun i => (q i).2)
  invFun xy := fun i => (xy.1 i, xy.2 i)
  left_inv q := by
    funext i
    exact Prod.eta (q i)
  right_inv xy := by
    rcases xy with ⟨x, y⟩
    rfl

private theorem tsum_cellConfig_reindex {h : ℕ} (N : ℕ)
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    (G : (Fin h → Site) → (Fin h → Site) → ℝ) :
    (∑' x : Fin h → Site, ∑' y : Fin h → Site,
        (∏ i, cellTestWeight N (φ i) (x i) (y i)) * G x y) =
      ∑ q ∈ Fintype.piFinset
          (fun i : Fin h =>
            (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset),
        (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          G (fun i => (q i).1) (fun i => (q i).2) := by
  classical
  let S : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  let Q : Finset (Fin h → Site × Site) := Fintype.piFinset S
  let e := sitePairConfigEquiv h
  let R : Finset ((Fin h → Site) × (Fin h → Site)) := Q.image e
  let f : ((Fin h → Site) × (Fin h → Site)) → ℝ :=
    fun xy => (∏ i, cellTestWeight N (φ i) (xy.1 i) (xy.2 i)) * G xy.1 xy.2
  have hweightzero (i : Fin h) (q : Site × Site) (hq : q ∉ S i) :
      cellTestWeight N (φ i) q.1 q.2 = 0 := by
    dsimp [S] at hq
    by_contra hne
    have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, φ i p) ≠ 0 := by
      intro hz
      apply hne
      simp [cellTestWeight, hz]
    exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).mem_toFinset.mpr hcell)
  have hfzero (xy : (Fin h → Site) × (Fin h → Site)) (hxy : xy ∉ R) : f xy = 0 := by
    by_contra hne
    have hweight : ∀ i, cellTestWeight N (φ i) (xy.1 i) (xy.2 i) ≠ 0 := by
      intro i hi
      apply hne
      dsimp [f]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
      simp
    let q : Fin h → Site × Site := fun i => (xy.1 i, xy.2 i)
    have hq : q ∈ Q := by
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hweight i (hweightzero i (q i) hi)
    apply hxy
    refine Finset.mem_image.mpr ⟨q, hq, ?_⟩
    rcases xy with ⟨x, y⟩
    simp [e, sitePairConfigEquiv, q]
  have hsum : Summable f := by
    apply summable_of_hasFiniteSupport
    apply R.finite_toSet.subset
    intro xy hxy
    by_contra hxyR
    exact hxy (hfzero xy hxyR)
  calc
    _ = ∑' xy : (Fin h → Site) × (Fin h → Site), f xy :=
      (hsum.tsum_prod).symm
    _ = ∑ xy ∈ R, f xy := by
      rw [tsum_eq_sum (s := R)]
      intro xy hxy
      exact hfzero xy hxy
    _ = ∑ q ∈ Q, f (e q) := by
      dsimp [R]
      rw [Finset.sum_image e.injective.injOn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [f, e, sitePairConfigEquiv]

private theorem tsum_testedBlockWord_eq_cellConfigSum (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    (∑' m : ℕ, ∑ w : CollisionWord h m,
        testedBlockWord ϑ N s t φ (List.ofFn w.1)) =
      ∑ q ∈ Fintype.piFinset
          (fun i : Fin h =>
            (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset),
        (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          (∑' m : ℕ, ∑ w : CollisionWord h m,
            blockWordKernel (sigmaSq (criticalBeta ϑ N)) (List.ofFn w.1)
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
              (fun i => (q i).1) (fun i => (q i).2)) := by
  classical
  let σ2 := sigmaSq (criticalBeta ϑ N)
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let S : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  let Q := Fintype.piFinset S
  have hword (m : ℕ) (w : CollisionWord h m) :
      testedBlockWord ϑ N s t φ (List.ofFn w.1) =
        ∑ q ∈ Q,
          (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
            blockWordKernel σ2 (List.ofFn w.1) n
              (fun i => (q i).1) (fun i => (q i).2) := by
    dsimp [testedBlockWord, σ2, n, Q, S]
    exact tsum_cellConfig_reindex N φ
      (fun x y => blockWordKernel (sigmaSq (criticalBeta ϑ N)) (List.ofFn w.1)
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) x y)
  have hlength (m : ℕ) (hm : m ∉ Finset.range (n + 1))
      (w : CollisionWord h m) (x y : Fin h → Site) :
      blockWordKernel σ2 (List.ofFn w.1) n x y = 0 := by
    have hmn : n < m := by
      simp only [Finset.mem_range, not_lt] at hm
      omega
    apply blockWordKernel_eq_zero_of_length_gt σ2
    simpa using hmn
  have htail (m : ℕ) (hm : m ∉ Finset.range (n + 1)) :
      (∑ w : CollisionWord h m, testedBlockWord ϑ N s t φ (List.ofFn w.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    have hkernel (x y : Fin h → Site) :
        blockWordKernel (sigmaSq (criticalBeta ϑ N)) (List.ofFn w.1)
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) x y = 0 := by
      simpa [σ2, n] using hlength m hm w x y
    unfold testedBlockWord
    simp_rw [hkernel]
    simp
  have hfinite :
      (∑' m : ℕ, ∑ w : CollisionWord h m,
        testedBlockWord ϑ N s t φ (List.ofFn w.1)) =
        ∑ m ∈ Finset.range (n + 1), ∑ w : CollisionWord h m,
          testedBlockWord ϑ N s t φ (List.ofFn w.1) := by
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    intro m hm
    exact htail m hm
  rw [hfinite]
  calc
    _ = ∑ m ∈ Finset.range (n + 1), ∑ w : CollisionWord h m,
          ∑ q ∈ Q,
            (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
              blockWordKernel σ2 (List.ofFn w.1) n
                (fun i => (q i).1) (fun i => (q i).2) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro w hw
      exact hword m w
    _ = ∑ m ∈ Finset.range (n + 1), ∑ q ∈ Q, ∑ w : CollisionWord h m,
          (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
            blockWordKernel σ2 (List.ofFn w.1) n
              (fun i => (q i).1) (fun i => (q i).2) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, ∑ m ∈ Finset.range (n + 1), ∑ w : CollisionWord h m,
          (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
            blockWordKernel σ2 (List.ofFn w.1) n
              (fun i => (q i).1) (fun i => (q i).2) := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          (∑ m ∈ Finset.range (n + 1), ∑ w : CollisionWord h m,
            blockWordKernel σ2 (List.ofFn w.1) n
              (fun i => (q i).1) (fun i => (q i).2)) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc
        _ = ∑ m ∈ Finset.range (n + 1),
              (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
                ∑ w : CollisionWord h m,
                  blockWordKernel σ2 (List.ofFn w.1) n
                    (fun i => (q i).1) (fun i => (q i).2) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [← Finset.mul_sum]
        _ = _ := by rw [← Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      symm
      rw [tsum_eq_sum (s := Finset.range (n + 1))]
      intro m hm
      have hmn : n < m := by
        simp only [Finset.mem_range, not_lt] at hm
        omega
      apply Finset.sum_eq_zero
      intro w hw
      apply blockWordKernel_eq_zero_of_length_gt σ2
      simpa using hmn

/-- The moment of compactly supported random pairings is exactly the sum of
their tested word contributions and their non-pair remainder. -/
theorem integral_prod_pairing_eq_wordSum (ϑ : ℝ) (N : ℕ) {s t : ℝ}
    (_hs : 0 ≤ s) (_hst : s ≤ t) {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∫ ω, ∏ i, (∫ p, φ i p * rescaledP2P ϑ N s t p ω) ∂disorderLaw =
      (∑' m : ℕ, ∑ w : CollisionWord h m,
        testedBlockWord ϑ N s t φ (List.ofFn w.1)) +
        testedNonpairRemainder ϑ N s t φ := by
  let β := criticalBeta ϑ N
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let S : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  let Q := Fintype.piFinset S
  let W : (Fin h → Site × Site) → ℝ := fun q =>
    ∏ i, cellTestWeight N (φ i) (q i).1 (q i).2
  have hword := tsum_testedBlockWord_eq_cellConfigSum ϑ N s t φ
  have hrem :
      testedNonpairRemainder ϑ N s t φ =
        ∑ q ∈ Q, W q * nonpairCollisionRemainder β n h
          (fun i => (q i).1) (fun i => (q i).2) := by
    dsimp [testedNonpairRemainder]
    simpa [β, n, Q, S, W] using
      (tsum_cellConfig_reindex N φ fun x y =>
        nonpairCollisionRemainder (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) h x y)
  rw [integral_prod_pairing_eq_finiteCellSum]
  calc
    _ = (∑ q ∈ Q, W q *
          (∑' m : ℕ, ∑ w : CollisionWord h m,
            blockWordKernel (sigmaSq β) (List.ofFn w.1) n
              (fun i => (q i).1) (fun i => (q i).2))) +
        ∑ q ∈ Q, W q * nonpairCollisionRemainder β n h
          (fun i => (q i).1) (fun i => (q i).2) := by
      calc
        _ = ∑ q ∈ Q,
              (W q * (∑' m : ℕ, ∑ w : CollisionWord h m,
                blockWordKernel (sigmaSq β) (List.ofFn w.1) n
                  (fun i => (q i).1) (fun i => (q i).2)) +
                W q * nonpairCollisionRemainder β n h
                  (fun i => (q i).1) (fun i => (q i).2)) := by
            apply Finset.sum_congr rfl
            intro q hq
            simp [β, n, W, mul_add]
        _ = _ := Finset.sum_add_distrib
    _ = _ := by
      rw [← hword, ← hrem]


end Critical2DKPZ.SHF.Moments

end
