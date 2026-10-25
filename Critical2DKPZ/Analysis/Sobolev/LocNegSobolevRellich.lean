/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevEnergyConvergence
public import Mathlib.Topology.Sequences

/-! # Compact sublevels of stronger local Sobolev energies -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ.Analysis.Sobolev

/-- A common energy bound gives a finite uniform bound for differences from a limit satisfying
the same bound. -/
theorem localEnergy_sub_bound {a : ℝ} {T U : Distr} {χ : TestFn} {K : ℝ≥0∞}
    (hT : localNegSobolevSq a T χ ≤ K) (hU : localNegSobolevSq a U χ ≤ K) :
    localNegSobolevSq a (T - U) χ ≤ (K ^ (1 / 2 : ℝ) + K ^ (1 / 2 : ℝ)) ^ 2 := by
  rw [← localNegSobolevENorm_sq]
  apply pow_le_pow_left₀ zero_le _ 2
  have h := localNegSobolevENorm_add_le a T (-U) χ
  rw [← sub_eq_add_neg] at h
  apply h.trans
  simp only [localNegSobolevENorm_eq_rpow, localNegSobolevSq_neg]
  exact add_le_add (ENNReal.rpow_le_rpow hT (by norm_num))
    (ENNReal.rpow_le_rpow hU (by norm_num))

/-- Distributional convergence under common stronger local bounds upgrades to convergence in
the weaker carrier topology. -/
theorem tendsto_carrier_of_pairings_of_localizer_bounds
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (T : ℕ → LocNegSobolevCarrier b) (U : LocNegSobolevCarrier b)
    (K : ℕ → ℝ≥0∞) (hK : ∀ m, K m ≠ ⊤)
    (hT : ∀ n m, localNegSobolevSq a (T n).1.toDistr (localizer m) ≤ K m)
    (hU : ∀ m, localNegSobolevSq a U.1.toDistr (localizer m) ≤ K m)
    (hpair : ∀ φ : TestFn, Tendsto (fun n => (T n).1.toDistr φ) atTop
      (𝓝 (U.1.toDistr φ))) :
    Tendsto T atTop (𝓝 U) := by
  rw [tendsto_subtype_rng]
  apply tendsto_locNegSobolevTop_of_localNegSobolevSq
  intro χ
  let S : ℕ → Distr := fun n => (T n).1.toDistr - U.1.toDistr
  have hSpair : ∀ φ : TestFn, Tendsto (fun n => S n φ) atTop (𝓝 0) := by
    intro φ
    simpa [S] using (hpair φ).sub
      (tendsto_const_nhds (x := U.1.toDistr φ) (f := atTop))
  have hSbound : ∀ m, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      ∀ n, localNegSobolevSq a (S n) (localizer m) ≤ B := by
    intro m
    have hroot := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hK m)
    refine ⟨(K m ^ (1 / 2 : ℝ) + K m ^ (1 / 2 : ℝ)) ^ 2,
      ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨hroot, hroot⟩), fun n => ?_⟩
    exact localEnergy_sub_bound (hT n m) (hU m)
  exact tendsto_localEnergy_zero_of_pairings_zero ha hab S hSpair hSbound χ

/-- The stronger local-energy sublevels are compact in every strictly weaker local Sobolev
carrier topology. -/
theorem isCompact_localizer_energy_sublevels {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (K : ℕ → ℝ≥0∞) (hK : ∀ m, K m ≠ ⊤) :
    IsCompact {T : LocNegSobolevCarrier b |
      ∀ m, localNegSobolevSq a T.1.toDistr (localizer m) ≤ K m} := by
  let : PseudoMetrizableSpace (LocNegSobolevCarrier b) :=
    (isInducing_locNegSobolevFourierReadout b (ha.trans hab.le)).pseudoMetrizableSpace
  apply IsSeqCompact.isCompact
  intro T hT
  obtain ⟨f, hf, U, hpair, hU⟩ := exists_subseq_pairings_of_localizer_energy_bound a
    (fun n => (T n).1.toDistr) K hK hT
  have hmem : MemLocalNegSobolev b U :=
    (memLocalNegSobolev_of_localizer_energy_lt_top ha U
      (fun m => (hU m).trans_lt (lt_top_iff_ne_top.mpr (hK m)))).mono hab.le
  let V : LocNegSobolevCarrier b := ⟨U, hmem⟩
  refine ⟨V, hU, f, hf, ?_⟩
  exact tendsto_carrier_of_pairings_of_localizer_bounds ha hab (fun n => T (f n)) V K hK
    (fun n m => hT (f n) m) hU hpair

end Critical2DKPZ.Analysis.Sobolev

end
