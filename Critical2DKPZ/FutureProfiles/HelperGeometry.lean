/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.GridAlignment
public import Critical2DKPZ.MomentBounds.CSZ25AssemblyLemmas
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-! # Geometric and clock estimates for future profiles -/

@[expose] public section

open Filter Set
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.MomentBounds

/-- The logarithm of the horizon is bounded by the number of geometric blocks. -/
theorem log_le_blockCount_mul_log {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ≤ (blockCount N ρ : ℝ) * Real.log ρ := by
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogbNonneg : 0 ≤ Real.logb ρ (N : ℝ) := Real.logb_nonneg hρ (by exact_mod_cast hN)
  have hfloor : (⌊Real.logb ρ (N : ℝ)⌋₊ : ℝ) ≤ Real.logb ρ (N : ℝ) :=
    Nat.floor_le hlogbNonneg
  have hcount : (blockCount N ρ : ℝ) =
      (⌊Real.logb ρ (N : ℝ)⌋₊ : ℝ) + 1 := by
    simp [blockCount]
  have hlogbLe : Real.logb ρ (N : ℝ) ≤ (blockCount N ρ : ℝ) := by
    rw [hcount]
    exact (Nat.lt_floor_add_one (Real.logb ρ (N : ℝ))).le
  have hlogId : Real.log (N : ℝ) = Real.logb ρ (N : ℝ) * Real.log ρ := by
    rw [Real.logb]
    exact (div_mul_cancel₀ _ hlogρ.ne').symm
  rw [hlogId]
  exact mul_le_mul_of_nonneg_right hlogbLe hlogρ.le

/-- The number of lattice sites in a Euclidean ball of radius `r ≥ 1` is bounded by a constant times `r²`. -/
theorem card_ball_sites_le : ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
    (((boxSites ⌈r⌉₊).filter fun y => ‖siteToPlane y‖ ≤ r).card : ℝ) ≤ C * r ^ 2 := by
  refine ⟨25, ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := by linarith
  let k : ℕ := ⌈r⌉₊
  have hrk : r ≤ (k : ℝ) := by dsimp [k]; exact Nat.le_ceil r
  have hkLt : (k : ℝ) < r + 1 := by
    dsimp [k]
    exact Nat.ceil_lt_add_one hr0
  have hboxeq (m : ℕ) : boxSites m = latticeBox m := by
    ext z
    simp only [boxSites, Fintype.mem_piFinset, Finset.mem_Icc]
    rw [mem_latticeBox, latticeRadius, max_le_iff]
    have hcoord (a : ℤ) : (-(m : ℤ) ≤ a ∧ a ≤ m) ↔ a.natAbs ≤ m := by
      rw [← abs_le, ← Int.natCast_natAbs, Nat.cast_le (α := ℤ)]
    exact ⟨fun hz => ⟨(hcoord (z 0)).mp (hz 0), (hcoord (z 1)).mp (hz 1)⟩,
      fun hz i => by
        fin_cases i
        · exact (hcoord (z 0)).mpr hz.1
        · exact (hcoord (z 1)).mpr hz.2⟩
  have hcard : (boxSites k).card = (2 * k + 1) ^ 2 := by
    rw [hboxeq, card_latticeBox]
  have hfilter : ((boxSites k).filter fun y => ‖siteToPlane y‖ ≤ r).card ≤
      (boxSites k).card := Finset.card_filter_le _ _
  have hsize : (2 * (k : ℝ) + 1) ≤ 5 * r := by nlinarith
  have hsizeNonneg : 0 ≤ (2 * (k : ℝ) + 1) := by positivity
  have hrNonneg : 0 ≤ 5 * r := by positivity
  have hsq : (2 * (k : ℝ) + 1) ^ 2 ≤ (5 * r) ^ 2 :=
    (sq_le_sq₀ hsizeNonneg hrNonneg).2 hsize
  have hcardReal : ((boxSites k).card : ℝ) = (2 * (k : ℝ) + 1) ^ 2 := by
    exact_mod_cast hcard
  have hfilterReal :
      (((boxSites k).filter fun y => ‖siteToPlane y‖ ≤ r).card : ℝ) ≤ (boxSites k).card := by
    exact_mod_cast hfilter
  calc
    (((boxSites ⌈r⌉₊).filter fun y => ‖siteToPlane y‖ ≤ r).card : ℝ) ≤
        (boxSites k).card := by simpa [k] using hfilterReal
    _ ≤ (5 * r) ^ 2 := by rw [hcardReal]; exact hsq
    _ = 25 * r ^ 2 := by ring

/-- A block endpoint retains enough geometric scale to control its logarithmic distance from `N`. -/
theorem log_div_blockTime_le (ρ₀ ρ₁ : ℝ) (hρ₀ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      s ≤ blockCount N ρ →
        Real.log ((N : ℝ) / blockTime N ρ s) ≤
          C * ((blockCount N ρ : ℝ) + 1 - s) := by
  let C : ℝ := Real.log (max ρ₁ ρ₀)
  have hCpos : 0 < C := by
    dsimp [C]
    apply Real.log_pos
    exact lt_of_lt_of_le hρ₀ (le_max_right ρ₁ ρ₀)
  refine ⟨C, ?_⟩
  intro ρ hρmem
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρmem.1
  have hρpos : 0 < ρ := by linarith
  have hρC : Real.log ρ ≤ C := by
    dsimp [C]
    exact Real.log_le_log (by linarith) (le_trans hρmem.2 (le_max_left ρ₁ ρ₀))
  filter_upwards [eventually_ge_atTop 1] with N hN
  intro s hs hsK
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let K : ℝ := blockCount N ρ
  have hsne : s ≠ 0 := by omega
  have hKpos : 0 < blockCount N ρ := by omega
  by_cases hsEq : s = blockCount N ρ
  · have ht : blockTime N ρ s = N := by
      simp [blockTime, hsEq, hKpos.ne']
    have hright : C * ((blockCount N ρ : ℝ) + 1 - (s : ℝ)) = C := by
      rw [hsEq]
      ring
    rw [ht, Real.log_div hNpos.ne' hNpos.ne', sub_self, hright]
    exact hCpos.le
  · have hsLt : s < blockCount N ρ := by omega
    have ht : blockTime N ρ s =
        evenCeil ((N : ℝ) * ρ ^ ((s : ℝ) - (blockCount N ρ : ℝ))) := by
      simp [blockTime, hsne, hsLt]
    have htimeScale : (N : ℝ) * ρ ^ ((s : ℝ) - K) ≤ (blockTime N ρ s : ℝ) := by
      rw [ht]
      exact Critical2DKPZ.le_evenCeil _
    have htimePos : 0 < (blockTime N ρ s : ℝ) :=
      lt_of_lt_of_le (mul_pos hNpos (Real.rpow_pos_of_pos hρpos _)) htimeScale
    have hpowCancel : ρ ^ (K - (s : ℝ)) * ρ ^ ((s : ℝ) - K) = 1 := by
      rw [← Real.rpow_add hρpos]
      have hexp : K - (s : ℝ) + ((s : ℝ) - K) = 0 := by ring
      rw [hexp, Real.rpow_zero]
    have hNle : (N : ℝ) ≤ ρ ^ (K - (s : ℝ)) * (blockTime N ρ s : ℝ) := by
      calc
        (N : ℝ) = (N : ℝ) * (ρ ^ (K - (s : ℝ)) * ρ ^ ((s : ℝ) - K)) := by
          rw [hpowCancel, mul_one]
        _ = ρ ^ (K - (s : ℝ)) * ((N : ℝ) * ρ ^ ((s : ℝ) - K)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htimeScale (Real.rpow_nonneg hρpos.le _)
    have hratio : (N : ℝ) / blockTime N ρ s ≤ ρ ^ (K - (s : ℝ)) := by
      apply (div_le_iff₀ htimePos).2
      simpa [mul_comm] using hNle
    have hlog : Real.log ((N : ℝ) / blockTime N ρ s) ≤
        (K - (s : ℝ)) * Real.log ρ := by
      calc
        Real.log ((N : ℝ) / blockTime N ρ s) ≤ Real.log (ρ ^ (K - (s : ℝ))) :=
          Real.log_le_log (div_pos hNpos htimePos) hratio
        _ = (K - (s : ℝ)) * Real.log ρ := Real.log_rpow hρpos _
    have hdiff : 0 ≤ K - (s : ℝ) := by
      dsimp [K]
      exact sub_nonneg.mpr (by exact_mod_cast hsK)
    calc
      Real.log ((N : ℝ) / blockTime N ρ s) ≤ (K - (s : ℝ)) * Real.log ρ := hlog
      _ ≤ (K - (s : ℝ)) * C := mul_le_mul_of_nonneg_left hρC hdiff
      _ ≤ C * (K + 1 - (s : ℝ)) := by
        rw [show K + 1 - (s : ℝ) = (K - (s : ℝ)) + 1 by ring]
        nlinarith [mul_nonneg hCpos.le hdiff]

end Critical2DKPZ.FutureProfiles

end
