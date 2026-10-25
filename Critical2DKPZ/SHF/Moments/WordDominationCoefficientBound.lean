/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationFlatProduct
public import Critical2DKPZ.SHF.Moments.WordDominationPositivity
public import Critical2DKPZ.SHF.Moments.WordDominationTestDomination
public import Critical2DKPZ.SHF.Moments.CollisionWordMomentExpansion
import Mathlib.Tactic

/-! # Uniform coefficient bounds from the sixth flat moment -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open DeltaBose Polymer

private theorem tsum_testedBlockWord_eq_sum_range (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    (∑' m : ℕ, ∑ w : CollisionWord h m,
      testedBlockWord ϑ N s t φ (List.ofFn w.1)) =
      ∑ m ∈ Finset.range
        (evenCeil (N * t) - evenCeil (N * s) + 1),
        ∑ w : CollisionWord h m,
          testedBlockWord ϑ N s t φ (List.ofFn w.1) := by
  let n := evenCeil (N * t) - evenCeil (N * s)
  have htail (m : ℕ) (hm : m ∉ Finset.range (n + 1)) :
      (∑ w : CollisionWord h m,
        testedBlockWord ϑ N s t φ (List.ofFn w.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    have hmn : n < m := by
      simp only [Finset.mem_range, not_lt] at hm
      omega
    have hkernel (x y : Fin h → Site) :
        blockWordKernel (sigmaSq (criticalBeta ϑ N)) (List.ofFn w.1) n x y = 0 := by
      apply blockWordKernel_eq_zero_of_length_gt
      simpa using hmn
    have hkernel' (x y : Fin h → Site) :
        blockWordKernel (sigmaSq (criticalBeta ϑ N)) (List.ofFn w.1)
          (evenCeil (N * t) - evenCeil (N * s)) x y = 0 := by
      simpa [n] using hkernel x y
    unfold testedBlockWord
    simp_rw [hkernel']
    simp
  rw [tsum_eq_sum (s := Finset.range (n + 1))]
  intro m hm
  exact htail m hm

/-- At fixed lattice duration the word expansion has finite support in its
length, so the sixth flat-marginal bound gives a uniform bound on every
nonnegative tested coefficient. -/
theorem eventually_sum_abs_testedBlockWord_le_flatMoment
    (ϑ : ℝ) {h : ℕ} (hh : h ≤ 4)
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    {τ T : ℝ} (hτ : 0 < τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord h m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ B := by
  let ψ : Fin h → C_c(Plane × Plane, ℝ) := fun i => compactAbs (φ i)
  have hψ (i : Fin h) (p : Plane × Plane) : 0 ≤ ψ i p := by
    change 0 ≤ |φ i p|
    positivity
  obtain ⟨B, hB, hN⟩ :=
    eventually_integral_compactAbs_pairing_product_fin_le ϑ hh φ hτ
  refine ⟨B, hB, ?_⟩
  filter_upwards [hN] with N hN
  intro s t hs hτst ht m
  obtain ⟨hProdInt, hProdBound⟩ := hN s t hs hτst ht
  have hst : s ≤ t := by linarith [hτ, hτst]
  have hEq := integral_prod_pairing_eq_wordSum ϑ N hs hst ψ
  let F : ℕ → ℝ := fun k =>
    ∑ w : CollisionWord h k, testedBlockWord ϑ N s t ψ (List.ofFn w.1)
  have hFnonneg (k : ℕ) : 0 ≤ F k := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro w hw
    exact testedBlockWord_nonneg ϑ N s t ψ hψ (List.ofFn w.1)
  have hFfinite : (∑' k : ℕ, F k) =
      ∑ k ∈ Finset.range
        (evenCeil (N * t) - evenCeil (N * s) + 1), F k := by
    simpa [F] using tsum_testedBlockWord_eq_sum_range ϑ N s t ψ
  have hrem : 0 ≤ testedNonpairRemainder ϑ N s t ψ :=
    testedNonpairRemainder_nonneg ϑ N s t ψ hψ
  have htotal :
      (∑ k ∈ Finset.range
        (evenCeil (N * t) - evenCeil (N * s) + 1), F k) ≤ B := by
    calc
      _ ≤ (∑ k ∈ Finset.range
            (evenCeil (N * t) - evenCeil (N * s) + 1), F k) +
            testedNonpairRemainder ϑ N s t ψ := le_add_of_nonneg_right hrem
      _ = ∫ ω, ∏ i : Fin h,
            (∫ p : Plane × Plane, ψ i p * rescaledP2P ϑ N s t p ω ∂volume)
            ∂disorderLaw := by
          rw [← hFfinite]
          simpa [F] using hEq.symm
      _ ≤ B := hProdBound
  have hFbound : F m ≤ B := by
    by_cases hm : m < evenCeil (N * t) - evenCeil (N * s) + 1
    · calc
        F m ≤ ∑ k ∈ Finset.range
            (evenCeil (N * t) - evenCeil (N * s) + 1), F k :=
          Finset.single_le_sum (fun k hk => hFnonneg k)
            (Finset.mem_range.mpr hm)
        _ ≤ B := htotal
    · have hm' : evenCeil (N * t) - evenCeil (N * s) < m := by omega
      have hz := tsum_testedBlockWord_eq_sum_range ϑ N s t ψ
      have hzero : F m = 0 := by
        dsimp [F]
        apply Finset.sum_eq_zero
        intro w hw
        have hkernel (x y : Fin h → Site) :
            blockWordKernel (sigmaSq (criticalBeta ϑ N)) (List.ofFn w.1)
              (evenCeil (N * t) - evenCeil (N * s)) x y = 0 := by
          apply blockWordKernel_eq_zero_of_length_gt
          simpa using hm'
        unfold testedBlockWord
        simp_rw [hkernel]
        simp
      rw [hzero]
      exact hB
  calc
    _ ≤ F m := by
      dsimp [F]
      apply Finset.sum_le_sum
      intro w hw
      exact abs_testedBlockWord_le_abs_testedBlockWord ϑ N s t φ
        (List.ofFn w.1)
    _ ≤ B := hFbound

end Critical2DKPZ.SHF.Moments

end
