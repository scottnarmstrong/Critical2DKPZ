/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevFourierReadout
public import Critical2DKPZ.LocalSobolev.LimitDistribution

/-! # Distribution limits under bounds on the countable local energies -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ.Analysis.Sobolev

/-- Finiteness along the fixed cutoff exhaustion implies finiteness at every smooth localizer. -/
theorem memLocalNegSobolev_of_localizer_energy_lt_top
    {a : ℝ} (ha : 0 ≤ a) (T : Distr)
    (hT : ∀ m, localNegSobolevSq a T (localizer m) < ⊤) :
    MemLocalNegSobolev a T := by
  intro χ
  obtain ⟨m, hm⟩ := exists_testFnMul_localizer_eq χ
  have hmul : testFnMul χ (localizer m) = χ := by
    rw [testFnMul_comm]
    exact hm m le_rfl
  have hbound := (localNegSobolevSq_testFnMul_le ha T (localizer m) χ (hT m)).2
  rw [hmul] at hbound
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hT m))

/-- Bounds on the countable local energies yield a distributional subsequential limit,
and every bound is retained by that limit. -/
theorem exists_subseq_pairings_of_localizer_energy_bound
    (a : ℝ) (T : ℕ → Distr) (K : ℕ → ℝ≥0∞) (hK : ∀ m, K m ≠ ⊤)
    (hT : ∀ n m, localNegSobolevSq a (T n) (localizer m) ≤ K m) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ U : Distr,
      (∀ φ : TestFn, Tendsto (fun n => T (f n) φ) atTop (𝓝 (U φ))) ∧
      ∀ m, localNegSobolevSq a U (localizer m) ≤ K m := by
  have hlocal : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      Rellich.negSobolevNorm 2 a (Rellich.compactnessDomain m)
        (Rellich.distributionFunctional (T n)) ≤ ENNReal.ofReal M := by
    intro m
    let B : ℝ≥0∞ := (K m) ^ (1 / 2 : ℝ)
    have hB : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hK m)
    refine ⟨B.toReal, ENNReal.toReal_nonneg, fun n => ?_⟩
    calc
      _ ≤ (localNegSobolevSq a (T n) (localizer m)) ^ (1 / 2 : ℝ) :=
        Rellich.distributionFunctional_negSobolevNorm_le_localEnergy (T n) (localizer m) a
          (fun x hx => localizer_eq_one_of_mem_closedBall m
            (Metric.ball_subset_closedBall hx))
      _ ≤ B := ENNReal.rpow_le_rpow (hT n m) (by norm_num)
      _ = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hB).symm
  obtain ⟨f, hf, U, hU⟩ :=
    Rellich.exists_strictMono_subseq_frozen_distribution_pairings a T hlocal
  refine ⟨f, hf, U, hU, fun m => ?_⟩
  exact (LocalSobolev.localNegSobolevSq_le_liminf_of_pairings hU a (localizer m)).trans
    (liminf_le_of_frequently_le' (Filter.Eventually.of_forall
      (fun n => hT (f n) m)).frequently)

end Critical2DKPZ.Analysis.Sobolev

end
