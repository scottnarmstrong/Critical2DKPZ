/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.KernelLimit
public import Critical2DKPZ.SHF.Moments.FirstMoment
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.Tactic

/-! # Moving local limit of the independent entrance strands -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The entrance normalization is the product of the canonical phase-correct
walk local limits, with no extra covariance or parity convention. -/
theorem tendsto_scaled_wordEntrance_moving {h : ℕ} {t : ℝ} (ht : 0 < t)
    (sN : ℕ → ℕ)
    (hs : Tendsto (fun N : ℕ => (sN N : ℝ) / N) atTop (𝓝 t))
    (xN uN : ℕ → Fin h → Site) (x u : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hu : ∀ i, Tendsto (fun N => latticeRepresentative N (uN N i)) atTop (𝓝 (u i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop,
      Even ((uN N i - xN N i) 0 + (uN N i - xN N i) 1 + (sN N : ℤ))) :
    Tendsto (fun N : ℕ => ((N : ℝ) / 4) ^ h *
      ∏ i, srwKernel (sN N) (uN N i - xN N i)) atTop (𝓝 (freeKernel h t x u)) := by
  have hfactor (i : Fin h) := tendsto_scaled_srwKernel ht hs
    (by simpa only [latticeRepresentative_sub] using (hu i).sub (hx i)) (hphase i)
  have hprod := tendsto_finsetProd Finset.univ (fun i hi => hfactor i)
  apply hprod.congr'
  filter_upwards with N
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Critical2DKPZ.SHF.Moments
