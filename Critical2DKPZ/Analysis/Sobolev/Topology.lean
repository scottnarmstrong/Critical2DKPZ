/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.FiniteSeminorm
public import Critical2DKPZ.Definitions.LocNegSobolevTopTopologicalSpace
import Mathlib.Topology.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Abel

/-! Convergence in the local negative Sobolev topology is characterized by localized difference energies. -/

public section

noncomputable section

open Filter TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ

/-- The localized negative Sobolev seminorm is the square root of its energy. -/
theorem localNegSobolevENorm_eq_rpow (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevENorm a T χ = localNegSobolevSq a T χ ^ (1 / 2 : ℝ) := by
  rw [← localNegSobolevENorm_sq, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- Convergence of every localized difference energy implies convergence in the local negative Sobolev topology. -/
theorem tendsto_locNegSobolevTop_of_localNegSobolevSq {ι : Type*} {l : Filter ι} {a : ℝ}
    {S : ι → LocNegSobolevTop a} {T : LocNegSobolevTop a}
    (h : ∀ χ : TestFn, Tendsto (fun i => localNegSobolevSq a ((S i).toDistr - T.toDistr) χ)
      l (𝓝 0)) : Tendsto S l (𝓝 T) := by
  apply tendsto_nhds_generateFrom_iff.mpr
  rintro U ⟨V, χ, ε, _, rfl⟩ hT
  change localNegSobolevSq a (T.toDistr - V) χ < ε at hT
  have hE : Tendsto (fun i => localNegSobolevENorm a ((S i).toDistr - T.toDistr) χ)
      l (𝓝 0) := by
    simpa only [← localNegSobolevENorm_eq_rpow,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
      (h χ).ennrpow_const (1 / 2 : ℝ)
  have hB := (hE.add_const (localNegSobolevENorm a (T.toDistr - V) χ)).ennrpow_const (2 : ℝ)
  simp only [zero_add, ENNReal.rpow_two, localNegSobolevENorm_sq] at hB
  have hev := (tendsto_order.mp hB).2 ε hT
  filter_upwards [hev] with i hi
  change localNegSobolevSq a ((S i).toDistr - V) χ < ε
  have hs : (S i).toDistr - V = ((S i).toDistr - T.toDistr) + (T.toDistr - V) := by abel
  rw [← localNegSobolevENorm_sq, hs]
  apply lt_of_le_of_lt _ hi
  exact pow_le_pow_left₀ zero_le
    (localNegSobolevENorm_add_le a _ _ χ) 2

/-- Convergence in the local negative Sobolev topology implies convergence of every localized difference energy to zero. -/
theorem tendsto_localNegSobolevSq_of_locNegSobolevTop {ι : Type*} {l : Filter ι} {a : ℝ}
    {S : ι → LocNegSobolevTop a} {T : LocNegSobolevTop a}
    (h : Tendsto S l (𝓝 T)) (χ : TestFn) :
    Tendsto (fun i => localNegSobolevSq a ((S i).toDistr - T.toDistr) χ) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have ho : IsOpen {R : LocNegSobolevTop a |
      localNegSobolevSq a (R.toDistr - T.toDistr) χ < ε} :=
    isOpen_generateFrom_of_mem ⟨T.toDistr, χ, ε, hε, rfl⟩
  have hm : T ∈ {R : LocNegSobolevTop a |
      localNegSobolevSq a (R.toDistr - T.toDistr) χ < ε} := by
    simpa only [Set.mem_ofPred_eq, sub_self, localNegSobolevSq_zero] using hε
  have hev : ∀ᶠ i in l, localNegSobolevSq a ((S i).toDistr - T.toDistr) χ < ε :=
    h (ho.mem_nhds hm)
  exact hev.mono fun _ hi => hi.le

/-- Convergence in the local negative Sobolev topology is equivalent to convergence of every localized difference energy to zero. -/
theorem tendsto_locNegSobolevTop_iff {ι : Type*} {l : Filter ι} {a : ℝ}
    {S : ι → LocNegSobolevTop a} {T : LocNegSobolevTop a} :
    Tendsto S l (𝓝 T) ↔ ∀ χ : TestFn,
      Tendsto (fun i => localNegSobolevSq a ((S i).toDistr - T.toDistr) χ) l (𝓝 0) :=
  ⟨fun h χ => tendsto_localNegSobolevSq_of_locNegSobolevTop h χ,
    tendsto_locNegSobolevTop_of_localNegSobolevSq⟩

end Critical2DKPZ

end
