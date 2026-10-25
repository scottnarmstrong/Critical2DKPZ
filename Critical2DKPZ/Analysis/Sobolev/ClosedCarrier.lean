/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Topology

/-! Distributions with finite local negative Sobolev energy form a closed set in the topology defined by the extended energies. -/

public section

noncomputable section

open Filter TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ


/-- Infinite energy at a localizer cannot be approached from finite energy in this topology. -/
theorem isClosed_localNegSobolevSq_lt_top (a : ℝ) (χ : TestFn) :
    IsClosed {T : LocNegSobolevTop a | localNegSobolevSq a T.toDistr χ < ⊤} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro T hT
  have ho : IsOpen {S : LocNegSobolevTop a |
      localNegSobolevSq a (S.toDistr - T.toDistr) χ < ⊤} :=
    isOpen_generateFrom_of_mem ⟨T.toDistr, χ, ⊤, ENNReal.zero_lt_top, rfl⟩
  have hm : T ∈ {S : LocNegSobolevTop a |
      localNegSobolevSq a (S.toDistr - T.toDistr) χ < ⊤} := by
    simp only [Set.mem_ofPred_eq, sub_self, localNegSobolevSq_zero, ENNReal.zero_lt_top]
  apply Filter.mem_of_superset (ho.mem_nhds hm)
  intro S hST hS
  have heST := (localNegSobolevENorm_lt_top_iff a (S.toDistr - T.toDistr) χ).mpr hST
  have heS := (localNegSobolevENorm_lt_top_iff a S.toDistr χ).mpr hS
  have hsum := localNegSobolevENorm_add_le a (-(S.toDistr - T.toDistr)) S.toDistr χ
  rw [show -(S.toDistr - T.toDistr) + S.toDistr = T.toDistr by abel,
    localNegSobolevENorm_neg] at hsum
  exact hT ((localNegSobolevENorm_lt_top_iff a T.toDistr χ).mp
    (hsum.trans_lt (ENNReal.add_lt_top.mpr ⟨heST, heS⟩)))

/-- The finite-energy carrier is closed in the extended local negative Sobolev topology. -/
theorem isClosed_memLocalNegSobolev (a : ℝ) :
    IsClosed {T : LocNegSobolevTop a | MemLocalNegSobolev a T.toDistr} := by
  have he : {T : LocNegSobolevTop a | MemLocalNegSobolev a T.toDistr} =
      ⋂ χ : TestFn, {T : LocNegSobolevTop a | localNegSobolevSq a T.toDistr χ < ⊤} := by
    ext T
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, MemLocalNegSobolev]
  rw [he]
  exact isClosed_iInter (fun χ => isClosed_localNegSobolevSq_lt_top a χ)

end Critical2DKPZ

end
