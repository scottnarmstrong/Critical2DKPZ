/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.Port.Walk.SRWOneDim
public import Critical2DKPZ.RandomWalk.KernelBridge
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Polymer.ProbabilityProfiles
public import Critical2DKPZ.MomentBounds.EvenKernelMaximum
import Mathlib.Tactic

/-! # Total variation under bounded changes of the planar smoothing width -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

private theorem summable_abs_P1_timeDiff (m : ℕ) :
    Summable (fun k : ℤ => |LatticeProb.P1 (m + 1) k - LatticeProb.P1 m k|) := by
  have hmajor : Summable (fun k : ℤ => LatticeProb.P1 (m + 1) k + LatticeProb.P1 m k) :=
    (LatticeProb.P1_summable (m + 1)).add (LatticeProb.P1_summable m)
  apply hmajor.of_nonneg_of_le
  · intro k
    exact abs_nonneg _
  · intro k
    rw [abs_le]
    constructor <;> nlinarith [LatticeProb.P1_nonneg (m + 1) k, LatticeProb.P1_nonneg m k]

private theorem tsum_abs_P1_timeDiff_le (m : ℕ) :
    (∑' k : ℤ, |LatticeProb.P1 (m + 1) k - LatticeProb.P1 m k|) ≤
      LatticeProb.P1 m 0 := by
  have hright : Summable (fun k : ℤ =>
      |LatticeProb.P1 m (k + 1) - LatticeProb.P1 m k|) :=
    LatticeProb.summable_abs_diff_P1 m
  have hleft : Summable (fun k : ℤ =>
      |LatticeProb.P1 m (k - 1) - LatticeProb.P1 m k|) := by
    have hcomp := hright.comp_injective (add_left_injective (-1 : ℤ))
    exact hcomp.congr fun k => by
      have hk : k + (-1) + 1 = k := by omega
      have hs : k + (-1) = k - 1 := by omega
      change |LatticeProb.P1 m (k + (-1) + 1) - LatticeProb.P1 m (k + (-1))| = _
      rw [hk, hs]
      exact abs_sub_comm _ _
  have hshift : (∑' k : ℤ,
      |LatticeProb.P1 m (k - 1) - LatticeProb.P1 m k|) =
      (∑' k : ℤ, |LatticeProb.P1 m (k + 1) - LatticeProb.P1 m k|) := by
    calc
      _ = ∑' k : ℤ,
          |LatticeProb.P1 m ((k + (-1)) + 1) - LatticeProb.P1 m (k + (-1))| := by
            apply tsum_congr
            intro k
            have hs : k - 1 = k + (-1) := by omega
            have hk : k + (-1) + 1 = k := by omega
            rw [hs, hk]
            exact abs_sub_comm _ _
      _ = _ := Equiv.tsum_eq (Equiv.addRight (-1))
        (fun k : ℤ => |LatticeProb.P1 m (k + 1) - LatticeProb.P1 m k|)
  have hmajor : Summable (fun k : ℤ =>
      (|LatticeProb.P1 m (k - 1) - LatticeProb.P1 m k| +
        |LatticeProb.P1 m (k + 1) - LatticeProb.P1 m k|) / 4) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hleft.add hright).mul_left (1 / 4 : ℝ)
  calc
    _ ≤ ∑' k : ℤ,
        (|LatticeProb.P1 m (k - 1) - LatticeProb.P1 m k| +
          |LatticeProb.P1 m (k + 1) - LatticeProb.P1 m k|) / 4 := by
      apply (summable_abs_P1_timeDiff m).tsum_le_tsum (fun k => ?_) hmajor
      rw [LatticeProb.P1_succ]
      have heq : LatticeProb.P1 m k / 2 + LatticeProb.P1 m (k - 1) / 4 +
          LatticeProb.P1 m (k + 1) / 4 - LatticeProb.P1 m k =
          ((LatticeProb.P1 m (k - 1) - LatticeProb.P1 m k) +
            (LatticeProb.P1 m (k + 1) - LatticeProb.P1 m k)) / 4 := by ring
      rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 4)
    _ = ((∑' k : ℤ,
          |LatticeProb.P1 m (k - 1) - LatticeProb.P1 m k|) +
        (∑' k : ℤ, |LatticeProb.P1 m (k + 1) - LatticeProb.P1 m k|)) / 4 := by
      rw [tsum_div_const, hleft.tsum_add hright]
    _ = (2 * LatticeProb.P1 m 0 + 2 * LatticeProb.P1 m 0) / 4 := by
      rw [hshift, LatticeProb.tsum_abs_diff_P1 m]
    _ = LatticeProb.P1 m 0 := by ring

/-- The `ℓ¹` change of a product of two lazy one-dimensional kernels under one
time increment is bounded by twice the central mass at the earlier time. This
is the one-dimensional product estimate used to control bounded changes of the
planar smoothing width. -/
theorem p1ProductKernel_timeVariation_le (m : ℕ) :
    (∑' z : ℤ × ℤ,
      |LatticeProb.P1 (m + 1) z.1 * LatticeProb.P1 (m + 1) z.2 -
        LatticeProb.P1 m z.1 * LatticeProb.P1 m z.2|) ≤
      2 * LatticeProb.P1 m 0 := by
  let d : ℤ → ℝ := fun k => |LatticeProb.P1 (m + 1) k - LatticeProb.P1 m k|
  let p : ℤ → ℝ := LatticeProb.P1 m
  let q : ℤ → ℝ := LatticeProb.P1 (m + 1)
  have hd : Summable d := by simpa [d] using summable_abs_P1_timeDiff m
  have hp : Summable p := LatticeProb.P1_summable m
  have hq : Summable q := LatticeProb.P1_summable (m + 1)
  have hdNorm : Summable (fun k => ‖d k‖) := by
    simpa [d, Real.norm_eq_abs, abs_abs] using hd
  have hpNorm : Summable (fun k => ‖p k‖) := by
    exact hp.congr fun k => (Real.norm_of_nonneg (LatticeProb.P1_nonneg m k)).symm
  have hqNorm : Summable (fun k => ‖q k‖) := by
    exact hq.congr fun k => (Real.norm_of_nonneg (LatticeProb.P1_nonneg (m + 1) k)).symm
  have hdq : Summable (fun z : ℤ × ℤ => d z.1 * q z.2) :=
    summable_mul_of_summable_norm hdNorm hqNorm
  have hpd : Summable (fun z : ℤ × ℤ => p z.1 * d z.2) :=
    summable_mul_of_summable_norm hpNorm hdNorm
  have hprodmajor : Summable (fun z : ℤ × ℤ => d z.1 * q z.2 + p z.1 * d z.2) :=
    hdq.add hpd
  have hpoint (z : ℤ × ℤ) :
      |q z.1 * q z.2 - p z.1 * p z.2| ≤ d z.1 * q z.2 + p z.1 * d z.2 := by
    have hq0 : 0 ≤ q z.2 := LatticeProb.P1_nonneg _ _
    have hp0 : 0 ≤ p z.1 := LatticeProb.P1_nonneg _ _
    have heq : q z.1 * q z.2 - p z.1 * p z.2 =
        (q z.1 - p z.1) * q z.2 + p z.1 * (q z.2 - p z.2) := by ring
    rw [heq]
    calc
      _ ≤ |(q z.1 - p z.1) * q z.2| + |p z.1 * (q z.2 - p z.2)| := abs_add_le _ _
      _ = |q z.1 - p z.1| * q z.2 + p z.1 * |q z.2 - p z.2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hp0]
      _ = _ := by rfl
  calc
    _ ≤ ∑' z : ℤ × ℤ, (d z.1 * q z.2 + p z.1 * d z.2) :=
      (hprodmajor.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint).tsum_le_tsum hpoint hprodmajor
    _ = (∑' k : ℤ, d k) * (∑' k : ℤ, q k) +
        (∑' k : ℤ, p k) * (∑' k : ℤ, d k) := by
      rw [Summable.tsum_add hdq hpd,
        tsum_mul_tsum_of_summable_norm hdNorm hqNorm,
        tsum_mul_tsum_of_summable_norm hpNorm hdNorm]
    _ = 2 * (∑' k : ℤ, d k) := by
      rw [LatticeProb.tsum_P1, LatticeProb.tsum_P1]
      ring
    _ ≤ 2 * LatticeProb.P1 m 0 := by
      exact mul_le_mul_of_nonneg_left (tsum_abs_P1_timeDiff_le m) (by norm_num)

private def rotatedFirst (z : LatticeProb.Site 2) : ℤ := z 0 + z 1

private def rotatedSecond (z : LatticeProb.Site 2) : ℤ := z 0 - z 1

private theorem srwHeat_two_rotated_product (n : ℕ) (z : LatticeProb.Site 2) :
    LatticeProb.srwHeat 2 n z =
      LatticeProb.srwHeat 1 n ![rotatedFirst z] *
        LatticeProb.srwHeat 1 n ![rotatedSecond z] := by
  induction n generalizing z with
  | zero =>
    simp only [LatticeProb.srwHeat_zero]
    by_cases hz : z = 0
    · subst z
      simp [rotatedFirst, rotatedSecond]
    · have hrot : rotatedFirst z ≠ 0 ∨ rotatedSecond z ≠ 0 := by
        by_contra h
        have hu : rotatedFirst z = 0 := by
          by_contra hu
          exact h (Or.inl hu)
        have hv : rotatedSecond z = 0 := by
          by_contra hv
          exact h (Or.inr hv)
        apply hz
        ext i
        fin_cases i
        · change z 0 = 0
          dsimp [rotatedFirst, rotatedSecond] at hu hv
          omega
        · change z 1 = 0
          dsimp [rotatedFirst, rotatedSecond] at hu hv
          omega
      rcases hrot with hu | hv
      · have hvec : ![rotatedFirst z] ≠ (0 : LatticeProb.Site 1) := by
          intro h
          have h0 := congrFun h 0
          simp at h0
          exact hu h0
        simp [hz, hvec]
      · have hvec : ![rotatedSecond z] ≠ (0 : LatticeProb.Site 1) := by
          intro h
          have h0 := congrFun h 0
          simp at h0
          exact hv h0
        simp [hz, hvec]
  | succ n ih =>
    rw [LatticeProb.srwHeat_succ_eq_sum_dir]
    have hU00 : rotatedFirst (z + LatticeProb.dirVec ((0, false) : LatticeProb.Dir 2)) =
        rotatedFirst z - 1 := by
      simp [rotatedFirst, LatticeProb.dirVec]
      ring
    have hV00 : rotatedSecond (z + LatticeProb.dirVec ((0, false) : LatticeProb.Dir 2)) =
        rotatedSecond z - 1 := by
      simp [rotatedSecond, LatticeProb.dirVec]
      ring
    have hU01 : rotatedFirst (z + LatticeProb.dirVec ((0, true) : LatticeProb.Dir 2)) =
        rotatedFirst z + 1 := by
      simp [rotatedFirst, LatticeProb.dirVec]
      ring
    have hV01 : rotatedSecond (z + LatticeProb.dirVec ((0, true) : LatticeProb.Dir 2)) =
        rotatedSecond z + 1 := by
      simp [rotatedSecond, LatticeProb.dirVec]
      ring
    have hU10 : rotatedFirst (z + LatticeProb.dirVec ((1, false) : LatticeProb.Dir 2)) =
        rotatedFirst z - 1 := by
      simp [rotatedFirst, LatticeProb.dirVec]
      ring
    have hV10 : rotatedSecond (z + LatticeProb.dirVec ((1, false) : LatticeProb.Dir 2)) =
        rotatedSecond z + 1 := by
      simp [rotatedSecond, LatticeProb.dirVec]
      ring
    have hU11 : rotatedFirst (z + LatticeProb.dirVec ((1, true) : LatticeProb.Dir 2)) =
        rotatedFirst z + 1 := by
      simp [rotatedFirst, LatticeProb.dirVec]
      ring
    have hV11 : rotatedSecond (z + LatticeProb.dirVec ((1, true) : LatticeProb.Dir 2)) =
        rotatedSecond z - 1 := by
      simp [rotatedSecond, LatticeProb.dirVec]
      ring
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, Fintype.sum_bool]
    simp_rw [ih, hU00, hV00, hU01, hV01, hU10, hV10, hU11, hV11]
    rw [LatticeProb.srwHeat_one_succ n (rotatedFirst z),
      LatticeProb.srwHeat_one_succ n (rotatedSecond z)]
    ring

private theorem srwKernel_even_rotated_eq_P1 (m : ℕ) (z : Site)
    (hz : ∃ i : ℤ, rotatedFirst z = 2 * i) :
    srwKernel (2 * m) z =
      LatticeProb.P1 m (rotatedFirst z / 2) * LatticeProb.P1 m (rotatedSecond z / 2) := by
  have hu : 2 * (rotatedFirst z / 2) = rotatedFirst z := by
    rcases hz with ⟨i, hi⟩
    omega
  have hvEven : ∃ i : ℤ, rotatedSecond z = 2 * i := by
    rcases hz with ⟨i, hi⟩
    refine ⟨i - z 1, ?_⟩
    dsimp [rotatedFirst, rotatedSecond] at hi ⊢
    omega
  have hv : 2 * (rotatedSecond z / 2) = rotatedSecond z := by
    rcases hvEven with ⟨i, hi⟩
    omega
  have huKernel : LatticeProb.srwHeat 1 (2 * m) ![rotatedFirst z] =
      LatticeProb.P1 m (rotatedFirst z / 2) := by
    have hvec := congrArg (fun x : ℤ => ![x]) (show rotatedFirst z = 2 * (rotatedFirst z / 2) by omega)
    rw [hvec]
    exact LatticeProb.srwHeat_one_two_mul m (rotatedFirst z / 2)
  have hvKernel : LatticeProb.srwHeat 1 (2 * m) ![rotatedSecond z] =
      LatticeProb.P1 m (rotatedSecond z / 2) := by
    have hvec := congrArg (fun x : ℤ => ![x])
      (show rotatedSecond z = 2 * (rotatedSecond z / 2) by omega)
    rw [hvec]
    exact LatticeProb.srwHeat_one_two_mul m (rotatedSecond z / 2)
  rw [Critical2DKPZ.srwKernel_eq_srwHeat, srwHeat_two_rotated_product,
    huKernel, hvKernel]

private theorem srwKernel_even_zero_of_not_rotated_even (m : ℕ) {z : Site}
    (hz : ¬ ∃ i : ℤ, rotatedFirst z = 2 * i) :
    srwKernel (2 * m) z = 0 := by
  have hzero : LatticeProb.srwHeat 1 (2 * m) ![rotatedFirst z] = 0 := by
    rcases Int.even_or_odd (rotatedFirst z) with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact False.elim (hz ⟨i, by omega⟩)
    · refine LatticeProb.srwHeat_eq_zero_of_parity ?_
      rw [LatticeProb.graphNorm_one]
      have hpar : (((rotatedFirst z).natAbs : ℕ) : ZMod 2) = 1 := by
        rw [LatticeProb.natAbs_cast_zmod, hi]
        push_cast
        ring_nf
        rw [show ((2 : ZMod 2)) = 0 by decide]
        ring
      have htime : ((2 * m : ℕ) : ZMod 2) = 0 := by
        push_cast
        rw [show ((2 : ZMod 2)) = 0 by decide]
        ring
      rw [hpar, htime]
      decide
  rw [Critical2DKPZ.srwKernel_eq_srwHeat, srwHeat_two_rotated_product, hzero]
  simp

/-- The even-time planar kernel is bounded by the reciprocal of its half-time scale. -/
theorem srwKernel_even_le_inv_succ (m : ℕ) (z : Site) :
    srwKernel (2 * m) z ≤ 1 / ((m : ℝ) + 1) := by
  calc
    srwKernel (2 * m) z ≤ srwKernel (2 * m) 0 :=
      Critical2DKPZ.MomentBounds.srwKernel_two_mul_le_zero m z
    _ = LatticeProb.P1 m 0 * LatticeProb.P1 m 0 := by
      rw [srwKernel_even_rotated_eq_P1 m 0 ⟨0, by simp [rotatedFirst]⟩]
      simp [rotatedFirst, rotatedSecond]
    _ ≤ (1 / Real.sqrt ((m : ℝ) + 1)) ^ 2 := by
      have hpeaknonneg := LatticeProb.P1_nonneg m 0
      have hpeak := LatticeProb.P1_zero_le_inv_sqrt m
      calc
        _ ≤ (1 / Real.sqrt ((m : ℝ) + 1)) *
            (1 / Real.sqrt ((m : ℝ) + 1)) :=
          mul_le_mul hpeak hpeak hpeaknonneg (by positivity)
        _ = _ := by rw [← pow_two]
    _ = 1 / ((m : ℝ) + 1) := by
      rw [one_div, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ) + 1)]
      simp [one_div]

private abbrev EvenRotatedSite :=
  {z : Site // z ∈ {z | ∃ i : ℤ, rotatedFirst z = 2 * i}}

private def evenRotatedSiteToPair (z : EvenRotatedSite) : ℤ × ℤ :=
  (rotatedFirst z.1 / 2, rotatedSecond z.1 / 2)

private def evenRotatedPairToSite (p : ℤ × ℤ) : EvenRotatedSite :=
  ⟨![p.1 + p.2, p.1 - p.2], ⟨p.1, by simp [rotatedFirst]; ring⟩⟩

private def rotatedSiteEquiv : EvenRotatedSite ≃ ℤ × ℤ where
  toFun := evenRotatedSiteToPair
  invFun := evenRotatedPairToSite
  left_inv := by
    rintro ⟨z, hz⟩
    rcases hz with ⟨i, hi⟩
    have hdiv : rotatedFirst z / 2 = i := by omega
    have hv : ∃ j : ℤ, rotatedSecond z = 2 * j := by
      refine ⟨i - z 1, ?_⟩
      dsimp [rotatedFirst, rotatedSecond] at hi ⊢
      omega
    rcases hv with ⟨j, hj⟩
    have hvdiv : rotatedSecond z / 2 = j := by omega
    apply Subtype.ext
    change ![rotatedFirst z / 2 + rotatedSecond z / 2,
      rotatedFirst z / 2 - rotatedSecond z / 2] = z
    rw [hdiv, hvdiv]
    funext k
    fin_cases k
    · dsimp [rotatedFirst] at hi
      dsimp [rotatedSecond] at hj
      simp
      omega
    · dsimp [rotatedFirst] at hi
      dsimp [rotatedSecond] at hj
      simp
      omega
  right_inv := by
    rintro ⟨i, j⟩
    apply Prod.ext
    · change (evenRotatedSiteToPair (evenRotatedPairToSite (i, j))).1 = i
      simp [evenRotatedSiteToPair, evenRotatedPairToSite, rotatedFirst]
      omega
    · change (evenRotatedSiteToPair (evenRotatedPairToSite (i, j))).2 = j
      simp [evenRotatedSiteToPair, evenRotatedPairToSite, rotatedFirst, rotatedSecond]
      omega

/-- The absolute difference of planar walk kernels at any two nonnegative integer times is summable. -/
private theorem summable_abs_srwKernel_sub (j k : ℕ) :
    Summable (fun z : Site => |srwKernel j z - srwKernel k z|) := by
  have hkernelSummable (n : ℕ) : Summable (fun z : Site => srwKernel n z) := by
    have hmass : (∑' z : Site, srwKernel n z) = 1 := by
      simpa only [sub_zero] using Polymer.tsum_srwKernel n 0
    have h := Polymer.summable_probability_profile (fun z : Site => srwKernel n z)
      (fun z => Polymer.kernel_nonneg n z) hmass
    exact h.congr fun z => abs_of_nonneg (Polymer.kernel_nonneg n z)
  have hmajor : Summable (fun z : Site => srwKernel j z + srwKernel k z) :=
    (hkernelSummable j).add (hkernelSummable k)
  apply hmajor.of_nonneg_of_le
  · intro z
    exact abs_nonneg _
  · intro z
    rw [abs_le]
    constructor <;> nlinarith [Polymer.kernel_nonneg j z, Polymer.kernel_nonneg k z]

/-- The ℓ¹ distance between consecutive even-time planar walk kernels is at most twice the one-dimensional return probability at the earlier time. -/
theorem srwKernel_even_timeVariation_le (m : ℕ) :
    (∑' z : Site, |srwKernel (2 * (m + 1)) z - srwKernel (2 * m) z|) ≤
      2 * LatticeProb.P1 m 0 := by
  let F : Site → ℝ := fun z => |srwKernel (2 * (m + 1)) z - srwKernel (2 * m) z|
  let S : Set Site := {z | ∃ i : ℤ, rotatedFirst z = 2 * i}
  have hF : Summable F := by
    simpa only [F] using summable_abs_srwKernel_sub (2 * (m + 1)) (2 * m)
  have hzero (z : Site) (hz : z ∉ S) : F z = 0 := by
    have hn : ¬ ∃ i : ℤ, rotatedFirst z = 2 * i := by simpa [S] using hz
    simp [F, srwKernel_even_zero_of_not_rotated_even (m + 1) hn,
      srwKernel_even_zero_of_not_rotated_even m hn]
  have hcomp : (∑' z : {z : Site // z ∈ Sᶜ}, F z.1) = 0 := by
    calc
      _ = ∑' _z : {z : Site // z ∈ Sᶜ}, (0 : ℝ) := by
        apply tsum_congr
        intro z
        have hz' : z.1 ∉ S := by
          intro hs
          exact z.2 hs
        exact hzero z.1 hz'
      _ = 0 := by simp
  have hsubtype : (∑' z : EvenRotatedSite, F z.1) = ∑' z : Site, F z := by
    rw [← hF.tsum_subtype_add_tsum_subtype_compl S, hcomp, add_zero]
  have hreindex : (∑' z : EvenRotatedSite, F z.1) =
      ∑' p : ℤ × ℤ,
        |LatticeProb.P1 (m + 1) p.1 * LatticeProb.P1 (m + 1) p.2 -
          LatticeProb.P1 m p.1 * LatticeProb.P1 m p.2| := by
    calc
      _ = ∑' p : ℤ × ℤ, F (rotatedSiteEquiv.symm p).1 := by
        simpa only [Equiv.symm_apply_apply] using
          (Equiv.tsum_eq rotatedSiteEquiv (fun p => F (rotatedSiteEquiv.symm p).1))
      _ = _ := by
        apply tsum_congr
        intro p
        have hz := (rotatedSiteEquiv.symm p).2
        have hnew := srwKernel_even_rotated_eq_P1 (m + 1)
          (rotatedSiteEquiv.symm p).1 hz
        have hold := srwKernel_even_rotated_eq_P1 m
          (rotatedSiteEquiv.symm p).1 hz
        have hcoords := rotatedSiteEquiv.apply_symm_apply p
        dsimp [F]
        rw [hnew, hold]
        rw [show rotatedFirst (rotatedSiteEquiv.symm p).1 / 2 = p.1 from congrArg Prod.fst hcoords,
          show rotatedSecond (rotatedSiteEquiv.symm p).1 / 2 = p.2 from congrArg Prod.snd hcoords]
  calc
    _ = ∑' z : EvenRotatedSite, F z.1 := hsubtype.symm
    _ = _ := hreindex
    _ ≤ 2 * LatticeProb.P1 m 0 := p1ProductKernel_timeVariation_le m

/-- The `ℓ¹` distance between two even-time planar walk kernels is at most the
number of two-step increments times the diffusive one-step bound. -/
theorem srwKernel_even_timeVariation_le_of_le {m n : ℕ} (hmn : m ≤ n) :
    (∑' z : Site, |srwKernel (2 * n) z - srwKernel (2 * m) z|) ≤
      2 * ((n - m : ℕ) : ℝ) / Real.sqrt ((m : ℝ) + 1) := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    simp
  | succ n ih =>
    by_cases hmn' : m ≤ n
    · have hprev := ih hmn'
      have hstepSummable : Summable (fun z : Site =>
          |srwKernel (2 * (n + 1)) z - srwKernel (2 * n) z|) :=
        summable_abs_srwKernel_sub (2 * (n + 1)) (2 * n)
      have hprevSummable : Summable (fun z : Site =>
          |srwKernel (2 * n) z - srwKernel (2 * m) z|) :=
        summable_abs_srwKernel_sub (2 * n) (2 * m)
      have hpoint (z : Site) :
          |srwKernel (2 * (n + 1)) z - srwKernel (2 * m) z| ≤
            |srwKernel (2 * (n + 1)) z - srwKernel (2 * n) z| +
              |srwKernel (2 * n) z - srwKernel (2 * m) z| := by
        exact abs_sub_le _ _ _
      have hsum : Summable (fun z : Site =>
          |srwKernel (2 * (n + 1)) z - srwKernel (2 * n) z| +
            |srwKernel (2 * n) z - srwKernel (2 * m) z|) :=
        hstepSummable.add hprevSummable
      have hnCast : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn' 1
      have hroot : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_le_sqrt hnCast
      have hstepBound : 2 * LatticeProb.P1 n 0 ≤ 2 / Real.sqrt ((m : ℝ) + 1) := by
        calc
          2 * LatticeProb.P1 n 0 ≤ 2 * (1 / Real.sqrt ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (LatticeProb.P1_zero_le_inv_sqrt n) (by norm_num)
          _ ≤ 2 * (1 / Real.sqrt ((m : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            simpa only [one_div] using
              one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hroot
          _ = _ := by ring
      have hstepL1 :
          (∑' z : Site, |srwKernel (2 * (n + 1)) z - srwKernel (2 * n) z|) ≤
            2 / Real.sqrt ((m : ℝ) + 1) :=
        (srwKernel_even_timeVariation_le n).trans hstepBound
      calc
        _ ≤ ∑' z : Site,
            (|srwKernel (2 * (n + 1)) z - srwKernel (2 * n) z| +
              |srwKernel (2 * n) z - srwKernel (2 * m) z|) :=
          (summable_abs_srwKernel_sub (2 * (n + 1)) (2 * m)).tsum_le_tsum hpoint hsum
        _ = (∑' z : Site, |srwKernel (2 * (n + 1)) z - srwKernel (2 * n) z|) +
            (∑' z : Site, |srwKernel (2 * n) z - srwKernel (2 * m) z|) :=
          Summable.tsum_add hstepSummable hprevSummable
        _ ≤ 2 / Real.sqrt ((m : ℝ) + 1) +
            2 * ((n - m : ℕ) : ℝ) / Real.sqrt ((m : ℝ) + 1) := by
          exact add_le_add hstepL1 hprev
        _ = 2 * (((n + 1) - m : ℕ) : ℝ) / Real.sqrt ((m : ℝ) + 1) := by
          have hsub : (n + 1) - m = (n - m) + 1 := by omega
          rw [hsub, Nat.cast_add, Nat.cast_one]
          ring
    · have hm : m = n + 1 := by omega
      subst m
      simp

end Critical2DKPZ.Smoothing

end
