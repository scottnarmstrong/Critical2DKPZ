/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Critical2DKPZ.RandomWalk.Port.Walk.Decomp

/-! # Coordinate decomposition of the simple random walk

The kernel is the uniform average over coordinate schedules of products of
one-dimensional simple walk kernels at the corresponding coordinate counts. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The one-dimensional kernel -/

/-- The one-dimensional simple random walk kernel. -/
noncomputable def S1 (n : ℕ) (k : ℤ) : ℝ := srwHeat 1 n ![k]

/-- A one-entry site vanishes exactly when its entry does, the identification
that turns the origin indicator on `Site 1` into an indicator on `ℤ`. -/
lemma vecCons_eq_zero_iff (k : ℤ) : (![k] : Site 1) = 0 ↔ k = 0 := by
  constructor
  · intro h
    simpa using congrFun h 0
  · rintro rfl
    funext i
    simp

/-- At time zero the one-dimensional kernel is the indicator of the origin. -/
lemma S1_zero (k : ℤ) : S1 0 k = if k = 0 then 1 else 0 := by
  rw [S1, srwHeat_zero]
  by_cases hk : k = 0
  · rw [ite_eq_left hk, ite_eq_left ((vecCons_eq_zero_iff k).mpr hk)]
  · rw [ite_eq_right hk, ite_eq_right (fun h => hk ((vecCons_eq_zero_iff k).mp h))]

/-- The one-dimensional kernel satisfies the nearest-neighbour recursion. -/
lemma S1_succ (n : ℕ) (k : ℤ) : S1 (n + 1) k = (S1 n (k - 1) + S1 n (k + 1)) / 2 :=
  srwHeat_one_succ n k

/-- The one-dimensional kernel is nonnegative, being a transition probability. -/
lemma S1_nonneg (n : ℕ) (k : ℤ) : 0 ≤ S1 n k := srwHeat_nonneg n ![k]

/-! ### The product kernel -/

/-- The product of one-dimensional simple walk kernels, coordinate `i` run for
`n i` steps. -/
noncomputable def KS (n : Fin d → ℕ) (x : Site d) : ℝ := ∏ i, S1 (n i) (x i)


/-- Running no coordinate at all leaves the indicator of the origin: a product
of indicators is the indicator of the conjunction. -/
lemma KS_zero_fun (x : Site d) : KS (fun _ => 0) x = if x = 0 then 1 else 0 := by
  unfold KS
  by_cases hx : x = 0
  · subst hx
    rw [ite_eq_left rfl]
    exact Finset.prod_eq_one fun i _ => by rw [S1_zero]; simp
  · rw [ite_eq_right hx]
    obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [S1_zero, ite_eq_right hi])

/-- Splits the product kernel into its `i`-th factor and the product over the
remaining coordinates. -/
lemma KS_eq_mul_erase (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    KS n x = S1 (n i) (x i) * ∏ j ∈ Finset.univ.erase i, S1 (n j) (x j) :=
  (Finset.mul_prod_erase Finset.univ (fun j => S1 (n j) (x j)) (Finset.mem_univ i)).symm

/-- Shifting the site by a positive unit step along coordinate `i` changes only
the `i`-th factor of the product kernel. -/
lemma KS_shift_pos (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    KS n (x + dirVec ((i, true) : Dir d))
      = S1 (n i) (x i + 1) * ∏ j ∈ Finset.univ.erase i, S1 (n j) (x j) := by
  rw [KS_eq_mul_erase n (x + dirVec ((i, true) : Dir d)) i, add_dirVec_true_apply, ite_eq_left rfl]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [add_dirVec_true_apply, ite_eq_right (Finset.ne_of_mem_erase hj)]

/-- Shifting the site by a negative unit step along coordinate `i` changes only
the `i`-th factor of the product kernel. -/
lemma KS_shift_neg (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    KS n (x + dirVec ((i, false) : Dir d))
      = S1 (n i) (x i - 1) * ∏ j ∈ Finset.univ.erase i, S1 (n j) (x j) := by
  rw [KS_eq_mul_erase n (x + dirVec ((i, false) : Dir d)) i, add_dirVec_false_apply, ite_eq_left rfl]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [add_dirVec_false_apply, ite_eq_right (Finset.ne_of_mem_erase hj)]

/-- One simple step in coordinate `i` advances the `i`-th factor of the product
kernel by one.  Unlike the lazy walk there is no holding term: the two
neighbours carry weight `1/2` each.  This is the operator identity behind
`LatticeProb.srwHeat_eq_sched`. -/
lemma KS_bump (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    KS (Function.update n i (n i + 1)) x
      = (KS n (x + dirVec (i, true)) + KS n (x + dirVec (i, false))) / 2 := by
  rw [KS_eq_mul_erase _ x i, KS_shift_pos, KS_shift_neg]
  simp only [Function.update_self]
  have herase : ∀ j ∈ Finset.univ.erase i,
      S1 (Function.update n i (n i + 1) j) (x j) = S1 (n j) (x j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl herase, S1_succ]
  ring

/-! ### The decomposition of the `r`-step kernel -/

/-- **The coordinate-schedule decomposition of the simple random walk.**  The
`r`-step kernel started at the origin is the average over all `d^r` coordinate
schedules of the product kernel attached to the step counts of the schedule. -/
theorem srwHeat_eq_sched {d : ℕ} (hd : 0 < d) (r : ℕ) (x : Site d) :
    srwHeat d r x = (∑ c : Fin r → Fin d, KS (cnt c) x) / (d : ℝ) ^ r := by
  induction r generalizing x with
  | zero =>
    have hu : (Finset.univ : Finset (Fin 0 → Fin d)) = {fun i => i.elim0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_univ _, fun c _ => ?_⟩
      funext t; exact t.elim0
    rw [hu, Finset.sum_singleton, pow_zero, div_one, cnt_zero, srwHeat_zero, KS_zero_fun]
  | succ r ih =>
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    rw [srwHeat_succ_eq_sum_dir]
    have hsum : ∀ a : Dir d, srwHeat d r (x + dirVec a)
        = (∑ c : Fin r → Fin d, KS (cnt c) (x + dirVec a)) / (d : ℝ) ^ r :=
      fun a => ih _
    rw [Finset.sum_congr rfl fun a _ => hsum a]
    have hdir : ∀ f : Dir d → ℝ, (∑ a : Dir d, f a)
        = ∑ i : Fin d, (f (i, true) + f (i, false)) := by
      intro f
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => by rw [Fintype.sum_bool]
    rw [hdir]
    have hL : ∑ i : Fin d, ((∑ c : Fin r → Fin d, KS (cnt c) (x + dirVec ((i, true) : Dir d)))
          / (d : ℝ) ^ r
          + (∑ c : Fin r → Fin d, KS (cnt c) (x + dirVec ((i, false) : Dir d))) / (d : ℝ) ^ r)
        = (∑ i : Fin d, ∑ c : Fin r → Fin d,
            (KS (cnt c) (x + dirVec ((i, true) : Dir d))
              + KS (cnt c) (x + dirVec ((i, false) : Dir d)))) / (d : ℝ) ^ r := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_add_distrib, ← add_div]
    rw [hL]
    have hre : ∑ c' : Fin (r + 1) → Fin d, KS (cnt c') x
        = ∑ i : Fin d, ∑ c : Fin r → Fin d,
            KS (Function.update (cnt c) i (cnt c i + 1)) x := by
      rw [← (snocEquiv r d).sum_comp (fun c' => KS (cnt c') x), Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
      show KS (cnt (Fin.snoc c i : Fin (r + 1) → Fin d)) x = _
      rw [cnt_snoc]
    have hR : ∑ i : Fin d, ∑ c : Fin r → Fin d,
          KS (Function.update (cnt c) i (cnt c i + 1)) x
        = (∑ i : Fin d, ∑ c : Fin r → Fin d,
            (KS (cnt c) (x + dirVec ((i, true) : Dir d))
              + KS (cnt c) (x + dirVec ((i, false) : Dir d)))) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => KS_bump _ _ _
    rw [hre, hR]
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hpne : ((d : ℝ)) ^ r ≠ 0 := pow_ne_zero _ hdne
    field_simp
    ring

end LatticeProb

end
