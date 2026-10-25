/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
import Mathlib.Tactic

/-! # Finite compositions of collision gaps -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- Reverse ordered positive gap compositions of a duration. The first entry
is the final free interval, matching the recursion for the interacting kernel. -/
noncomputable def ccr25PositiveGapCompositionsRev : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | m + 1 => (Finset.range (m + 1)).biUnion fun n =>
      (ccr25PositiveGapCompositionsRev (m - n)).image (fun ds => (n + 1) :: ds)
termination_by m => m

decreasing_by
  simp_wf

/-- Every reversed gap composition has positive entries summing to its
specified duration. -/
theorem ccr25PositiveGapCompositionsRev_spec (m : ℕ) :
    ∀ gaps ∈ ccr25PositiveGapCompositionsRev m,
      (∀ d ∈ gaps, 1 ≤ d) ∧ gaps.sum = m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro gaps hg
      cases m with
      | zero =>
          have hg' : gaps = [] := by
            simpa [ccr25PositiveGapCompositionsRev] using hg
          subst gaps
          simp
      | succ m =>
          unfold ccr25PositiveGapCompositionsRev at hg
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hg
          obtain ⟨n, hn, ds, hds, rfl⟩ := hg
          have hlt : m - n < m + 1 := by omega
          obtain ⟨hpos, hsum⟩ := ih (m - n) hlt ds hds
          constructor
          · intro d hd
            simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · omega
            · exact hpos d hd
          · simp only [List.sum_cons]
            omega

/-- Summing the timed interaction contribution over every positive gap
composition of a fixed duration gives exactly CCR25's recursive interacting
kernel. -/
theorem ccr25TimedInteractionRunAbs_sum_gapCompositions {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) :
    ∀ m : ℕ, ∀ z x : LatticeConfiguration h,
      (∑ gaps ∈ ccr25PositiveGapCompositionsRev m,
        ccr25TimedInteractionRunAbs β I gaps z x) =
          interactingReplicaKernelAbs β I m z x := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro z x
      cases m with
      | zero =>
          simp [ccr25PositiveGapCompositionsRev,
            ccr25TimedInteractionRunAbs, interactingReplicaKernelAbs]
      | succ m =>
          classical
          let T : ℕ → Finset (List ℕ) := fun n =>
            (ccr25PositiveGapCompositionsRev (m - n)).image (fun ds => (n + 1) :: ds)
          have hdis : Set.PairwiseDisjoint (↑(Finset.range (m + 1))) T := by
            intro n hn n' hn' hne
            apply Finset.disjoint_left.mpr
            intro gaps hg hg'
            obtain ⟨ds, hds, heq⟩ := Finset.mem_image.mp (by simpa [T] using hg)
            obtain ⟨ds', hds', heq'⟩ := Finset.mem_image.mp (by simpa [T] using hg')
            have hhead := congrArg List.head? (heq.trans heq'.symm)
            simp only [List.head?_cons] at hhead
            exact hne (Nat.add_right_cancel (Option.some.inj hhead))
          rw [ccr25PositiveGapCompositionsRev, Finset.sum_biUnion hdis]
          have hinner (n : ℕ) (hn : n ∈ Finset.range (m + 1)) :
              (∑ gaps ∈ T n,
                ccr25TimedInteractionRunAbs β I gaps z x) =
                |replicaPartitionDisorderMoment β I| *
                  ∑' y : LatticeConfiguration h,
                    interactingReplicaKernelAbs β I (m - n) z y *
                      freeReplicaKernel (n + 1) I I y x := by
            dsimp [T]
            rw [Finset.sum_image]
            · calc
                _ = ∑ gaps ∈ ccr25PositiveGapCompositionsRev (m - n),
                    |replicaPartitionDisorderMoment β I| *
                      ∑' y : LatticeConfiguration h,
                        ccr25TimedInteractionRunAbs β I gaps z y *
                          freeReplicaKernel (n + 1) I I y x := by
                    apply Finset.sum_congr rfl
                    intro gaps hg
                    simp only [ccr25TimedInteractionRunAbs]
                _ = |replicaPartitionDisorderMoment β I| *
                    ∑ gaps ∈ ccr25PositiveGapCompositionsRev (m - n),
                      ∑' y : LatticeConfiguration h,
                        ccr25TimedInteractionRunAbs β I gaps z y *
                          freeReplicaKernel (n + 1) I I y x := by
                    rw [Finset.mul_sum]
                _ = |replicaPartitionDisorderMoment β I| *
                    ∑' y : LatticeConfiguration h,
                      (∑ gaps ∈ ccr25PositiveGapCompositionsRev (m - n),
                        ccr25TimedInteractionRunAbs β I gaps z y) *
                          freeReplicaKernel (n + 1) I I y x := by
                    congr 1
                    symm
                    calc
                      (∑' y : LatticeConfiguration h,
                          (∑ gaps ∈ ccr25PositiveGapCompositionsRev (m - n),
                            ccr25TimedInteractionRunAbs β I gaps z y) *
                              freeReplicaKernel (n + 1) I I y x) =
                          ∑' y : LatticeConfiguration h,
                            ∑ gaps ∈ ccr25PositiveGapCompositionsRev (m - n),
                              ccr25TimedInteractionRunAbs β I gaps z y *
                                freeReplicaKernel (n + 1) I I y x := by
                        congr 1
                        funext y
                        rw [Finset.sum_mul]
                      _ = ∑ gaps ∈ ccr25PositiveGapCompositionsRev (m - n),
                          ∑' y : LatticeConfiguration h,
                            ccr25TimedInteractionRunAbs β I gaps z y *
                              freeReplicaKernel (n + 1) I I y x :=
                        Summable.tsum_finsetSum (fun gaps hg =>
                          summable_mul_freeReplicaKernel_right
                            (ccr25TimedInteractionRunAbs β I gaps z)
                            (n + 1) I x)
                _ = |replicaPartitionDisorderMoment β I| *
                    ∑' y : LatticeConfiguration h,
                      interactingReplicaKernelAbs β I (m - n) z y *
                        freeReplicaKernel (n + 1) I I y x := by
                    apply congrArg
                    apply tsum_congr
                    intro y
                    rw [ih (m - n) (by omega) z y]
            · intro ds hds ds' hds' heq
              exact (List.cons.inj heq).2
          have hsum := Finset.sum_congr rfl hinner
          calc
            (∑ n ∈ Finset.range (m + 1), ∑ gaps ∈ T n,
                ccr25TimedInteractionRunAbs β I gaps z x) =
              ∑ n ∈ Finset.range (m + 1),
                |replicaPartitionDisorderMoment β I| *
                  ∑' y : LatticeConfiguration h,
                    interactingReplicaKernelAbs β I (m - n) z y *
                      freeReplicaKernel (n + 1) I I y x := hsum
            _ = interactingReplicaKernelAbs β I (m + 1) z x := by
              simp only [interactingReplicaKernelAbs]
              rw [← Finset.mul_sum]

/-- Summing all positive gap compositions, then damping by their total time,
recovers the finite Laplace-summed interacting kernel, including its zero-time
collision identity term. -/
theorem ccr25TimedInteractionRunAbs_damped_gapCompositionSum_eq_hatted
    {h : ℕ} (L : ℕ) (lam β : ℝ) (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) :
    (∑ d ∈ Finset.range (L + 1),
      Real.exp (-lam * (d : ℝ)) *
        ∑ gaps ∈ ccr25PositiveGapCompositionsRev d,
          ccr25TimedInteractionRunAbs β I gaps z x) =
      hattedInteractingReplicaKernelAbs L lam β I z x := by
  have hterm (d : ℕ) :
      Real.exp (-lam * (d : ℝ)) *
        ∑ gaps ∈ ccr25PositiveGapCompositionsRev d,
          ccr25TimedInteractionRunAbs β I gaps z x =
      Real.exp (-lam * (d : ℝ)) * interactingReplicaKernelAbs β I d z x := by
    rw [ccr25TimedInteractionRunAbs_sum_gapCompositions]
  calc
    (∑ d ∈ Finset.range (L + 1),
        Real.exp (-lam * (d : ℝ)) *
          ∑ gaps ∈ ccr25PositiveGapCompositionsRev d,
            ccr25TimedInteractionRunAbs β I gaps z x) =
        ∑ d ∈ Finset.range (L + 1),
          Real.exp (-lam * (d : ℝ)) * interactingReplicaKernelAbs β I d z x := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hterm d
    _ = hattedInteractingReplicaKernelAbs L lam β I z x := by
      rw [Finset.sum_range_succ']
      simp [hattedInteractingReplicaKernelAbs, interactingReplicaKernelAbs]
      ring

end Critical2DKPZ.MomentBounds

end
