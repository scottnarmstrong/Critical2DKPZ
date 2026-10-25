/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichNet
public import Critical2DKPZ.Analysis.Sobolev.Rellich.SobolevTestDuality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Uniform Sobolev and distribution-pairing bounds for compact smooth kernel families.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- A compact smooth family with one compact support has uniformly finite Sobolev norms. -/
theorem exists_uniform_sobolev_kernel_bound {d : ℕ} {α : Type*}
    [TopologicalSpace α] [CompactSpace α] (g : α → Space d → ℝ)
    {K : Set (Space d)} (hK : IsCompact K)
    (hsm : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (g p))
    (hsupp : ∀ p, tsupport (g p) ⊆ K)
    (hcont : ∀ n : ℕ,
      Continuous (fun z : α × Space d => iteratedFDeriv ℝ n (g z.1) z.2))
    (s : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p, sobolevNormSq d s (g p) ≤ ENNReal.ofReal A := by
  classical
  obtain ⟨m, C, hC, hres⟩ := rkResidual_diff_bound hK s
  have hbounds : ∀ n : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (g p) x‖ ≤ B := by
    intro n
    obtain ⟨b, hb⟩ := (isCompact_univ.prod hK).bddAbove_image
      (hcont n).norm.continuousOn
    refine ⟨max b 0 + 1, by positivity, ?_⟩
    intro p x
    by_cases hx : x ∈ K
    · have hn : ‖iteratedFDeriv ℝ n (g p) x‖ ≤ b :=
        hb ⟨(p, x), ⟨mem_univ p, hx⟩, rfl⟩
      exact hn.trans (by linarith [le_max_left b 0])
    · have hz : iteratedFDeriv ℝ n (g p) x = 0 := by
        by_contra hn
        exact hx (hsupp p (support_iteratedFDeriv_subset n hn))
      rw [hz, norm_zero]
      positivity
  choose B hB hbound using hbounds
  let t := Finset.range (m + 1)
  have ht : t.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  let R := t.sup' ht B
  have hR : 0 < R := (hB 0).trans_le (Finset.le_sup' B (by simp [t]))
  refine ⟨C * R ^ 2, by positivity, ?_⟩
  intro p
  exact hres (g p) (hsm p) (hsupp p) R hR (by
    intro k hk x
    exact (hbound k p x).trans (Finset.le_sup' B (by simp [t]; omega)))

/-- Uniform pairing bounds against a compact smooth family, at every real order. -/
theorem exists_uniform_test_pairing_bound {d : ℕ} {α : Type*}
    [TopologicalSpace α] [CompactSpace α] (g : α → Space d → ℝ)
    {K : Set (Space d)} (hK : IsCompact K)
    (hsm : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (g p))
    (hsupp : ∀ p, tsupport (g p) ⊆ K)
    (hcont : ∀ n : ℕ,
      Continuous (fun z : α × Space d => iteratedFDeriv ℝ n (g z.1) z.2))
    (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p (D : Set (Space d)) (φ : Space d → ℝ),
      IsTestFn D φ → sobolevNormSq d s φ ≤ 1 → |∫ x, φ x * g p x| ≤ C := by
  obtain ⟨A, hA, hkernel⟩ :=
    exists_uniform_sobolev_kernel_bound g hK hsm hsupp hcont (-s)
  refine ⟨A + 1, by linarith, ?_⟩
  intro p D φ hφ hunit
  have hg : IsTestFn K (g p) :=
    ⟨hsm p, hK.of_isClosed_subset (isClosed_tsupport _) (hsupp p), hsupp p⟩
  have hp := sobolevDualityBound_of_isTestFn s hφ hg
  have he : ENNReal.ofReal (|∫ x, φ x * g p x| ^ 2) ≤ ENNReal.ofReal A :=
    hp.trans ((mul_le_mul_left hunit _).trans (by simpa using hkernel p))
  have hsquare : |∫ x, φ x * g p x| ^ 2 ≤ A :=
    (ENNReal.ofReal_le_ofReal_iff hA).1 he
  nlinarith [sq_nonneg (|∫ x, φ x * g p x| - 1), abs_nonneg (∫ x, φ x * g p x)]

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
