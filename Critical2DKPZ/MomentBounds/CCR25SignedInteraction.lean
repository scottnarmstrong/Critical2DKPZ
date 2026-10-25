/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25Operators
import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # Signed CCR25 interacting replica kernel -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

attribute [local instance] Classical.propDecidable



/-- Every free replica transition kernel is nonnegative. -/
theorem freeReplicaKernel_nonneg {h : ℕ} (n : ℕ) (I J : ReplicaPartition h)
    (z x : LatticeConfiguration h) : 0 ≤ freeReplicaKernel n I J z x := by
  unfold freeReplicaKernel
  split_ifs
  · exact Finset.prod_nonneg fun _ _ => Critical2DKPZ.srwKernel_nonneg _ _
  · exact le_of_eq rfl


end

end Critical2DKPZ.MomentBounds
