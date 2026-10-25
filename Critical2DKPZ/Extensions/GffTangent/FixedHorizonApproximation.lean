/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonWindowLimit
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonOrthogonality
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlockClocks
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonHeatPartition
import Mathlib.Tactic

/-! # L2 recovery of the full pairing from independent linear-time windows -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A window with no free entrance is precisely the full centered polymer. -/
theorem latticeWindowFluctuation_zero_start (β c : ℝ) (n : ℕ) (S : Finset Site)
    (ν : Site → ℝ) :
    latticeWindowFluctuation β c 0 n S ν = finiteEntranceFluctuation β c 0 n S ν := by
  funext ω
  simp [latticeWindowFluctuation, finiteEntranceFluctuation, freeEntranceWindowMass,
    Polymer.walkPosition_zero]

/-- For every fixed positive number of windows, their sum recovers the full
quasi-critical pairing in L2. The independence and projection identity are
proved for the actual disorder windows. -/
theorem tendsto_integral_sq_quasiCritical_window_error
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    (n : ℕ → ℕ) {T : ℝ} (hT : 0 < T)
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 T))
    {M : ℕ} (hM : 0 < M) (f : TestFn)
    (S : ℕ → Finset Site) (hS : ∀ N x, f x ≠ 0 → latticePoint N x ∈ S N) :
    Tendsto (fun N : ℕ => ∫ ω,
      (finiteEntranceFluctuation (β N) (Real.sqrt (l N)) 0 (n N) (S N)
          (fun w => ∫ x in cell N w, f x) ω -
        ∑ i : Fin M, latticeWindowFluctuation (β N) (Real.sqrt (l N))
          (quasiCriticalBlockClock (n N) M i)
          (quasiCriticalBlockClock (n N) M ((i : ℕ) + 1)) (S N)
          (fun w => ∫ x in cell N w, f x) ω) ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
  let H : ℝ → ℝ := fun t => ∫ p : Plane × Plane,
    f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)
  let W : ℕ → Fin M → Disorder → ℝ := fun N i =>
    latticeWindowFluctuation (β N) (Real.sqrt (l N))
      (quasiCriticalBlockClock (n N) M i)
      (quasiCriticalBlockClock (n N) M ((i : ℕ) + 1)) (S N)
      (fun w => ∫ x in cell N w, f x)
  let X : ℕ → Disorder → ℝ := fun N =>
    finiteEntranceFluctuation (β N) (Real.sqrt (l N)) 0 (n N) (S N)
      (fun w => ∫ x in cell N w, f x)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hclock (i : ℕ) : Tendsto
      (fun N : ℕ => (quasiCriticalBlockClock (n N) M i : ℝ) / N) atTop
      (𝓝 (T * (i : ℝ) / M)) := by
    simpa only [mul_div_assoc] using tendsto_quasiCriticalBlockClock_div n hn hM i
  have hinterval (i : Fin M) : T * ((i : ℕ) : ℝ) / M <
      T * (((i : ℕ) : ℝ) + 1) / M := by
    apply (div_lt_div_iff_of_pos_right hMr).mpr
    nlinarith
  have hvar (i : Fin M) : Tendsto (fun N => ∫ ω, W N i ω ^ 2 ∂disorderLaw) atTop
      (𝓝 (4 * Real.pi * ∫ t in Ioo (T * ((i : ℕ) : ℝ) / M)
        (T * (((i : ℕ) : ℝ) + 1) / M), H t)) := by
    apply tendsto_integral_sq_quasiCritical_cell_window l β hl hratio hβ hσ
      (by positivity) (hinterval i) _ _ (hclock i) _ (f : Plane → ℝ)
      f.continuous f.hasCompactSupport S hS
    simpa only [Nat.cast_add, Nat.cast_one] using hclock ((i : ℕ) + 1)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hvar i)
  rw [← Finset.mul_sum, sum_integral_fixedHorizon_partition hT hM H
    (integrableOn_fixedHorizon_heat_energy f hT)] at hsum
  have hzero : Tendsto (fun N : ℕ => (0 : ℝ) / N) atTop (𝓝 0) := by simp
  have hfull := tendsto_integral_sq_quasiCritical_cell_window l β hl hratio hβ hσ
    (le_refl (0 : ℝ)) hT (fun _ => 0) n (by simpa only [Nat.cast_zero] using hzero) hn (f : Plane → ℝ)
    f.continuous f.hasCompactSupport S hS
  simp_rw [latticeWindowFluctuation_zero_start] at hfull
  have hlim := hfull.sub hsum
  simp only [H, sub_self] at hlim
  apply hlim.congr'
  filter_upwards [] with N
  have hab (i : Fin M) : quasiCriticalBlockClock (n N) M i ≤
      quasiCriticalBlockClock (n N) M ((i : ℕ) + 1) :=
    monotone_quasiCriticalBlockClock _ _ (Nat.le_succ _)
  have hend (i : Fin M) : quasiCriticalBlockClock (n N) M ((i : ℕ) + 1) ≤ n N :=
    quasiCriticalBlockClock_succ_le _ _ i.isLt
  have hdisj : Pairwise fun i j : Fin M =>
      Disjoint (Ioc (quasiCriticalBlockClock (n N) M i)
          (quasiCriticalBlockClock (n N) M ((i : ℕ) + 1)))
        (Ioc (quasiCriticalBlockClock (n N) M j)
          (quasiCriticalBlockClock (n N) M ((j : ℕ) + 1))) := by
    intro i j hij
    have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · apply Set.disjoint_left.mpr
      intro k hk hjk
      simp only [Set.mem_Ioc] at hk hjk
      have hbound := monotone_quasiCriticalBlockClock (n N) M (show (i : ℕ) + 1 ≤ j by omega)
      omega
    · apply Set.disjoint_left.mpr
      intro k hk hjk
      simp only [Set.mem_Ioc] at hk hjk
      have hbound := monotone_quasiCriticalBlockClock (n N) M (show (j : ℕ) + 1 ≤ i by omega)
      omega
  exact (integral_sq_lattice_window_error (β N) (Real.sqrt (l N)) (n N) Finset.univ
    (fun i : Fin M => quasiCriticalBlockClock (n N) M i)
    (fun i : Fin M => quasiCriticalBlockClock (n N) M ((i : ℕ) + 1)) hab hend hdisj
    (S N) (fun w => ∫ x in cell N w, f x)).2.symm

end Critical2DKPZ.Extensions.GffTangent
