/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.MomentBounds.BlockVarianceReduction
public import Critical2DKPZ.Blocks.Core
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Critical2DKPZ.OnePoint.CriticalGap
import Critical2DKPZ.OnePoint.MomentProductInverseProduct
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Product comparison for block second moments -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem inv_sq_sum_Icc_le (m M : ℕ) (hm : 2 ≤ m) (hmM : m ≤ M) :
    ∑ j ∈ Finset.Icc m M, 1 / (j : ℝ) ^ 2 ≤ 2 / (m : ℝ) := by
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℝ)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmone : 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hanti : AntitoneOn f (Set.Ici (m : ℝ)) := by
    intro x hx y hy hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hmpos hx) hxy (by norm_num)
  have hInt : IntegrableOn f (Set.Ioi (m : ℝ)) := by
    simpa [f] using integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-2 : ℝ) < -1) hmpos
  have hnonneg : ∀ x ∈ Set.Ioi (m : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (le_of_lt (lt_trans hmpos hx)) _
  have hrest :
      ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) ≤ ∫ x in Set.Ioi (m : ℝ), f x :=
    (hanti.mono Set.Icc_subset_Ici_self).sum_Ico_le_integral hInt hnonneg
  have hshift :
      ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) = ∑ j ∈ Finset.Ioc m M, f j := by
    apply Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
    · intro j hj
      rcases Finset.mem_Ico.mp hj with ⟨hmj, hjM⟩
      exact Finset.mem_Ioc.mpr ⟨Nat.lt_succ_of_le hmj, Nat.succ_le_of_lt hjM⟩
    · intro a ha b hb hab
      exact Nat.succ.inj hab
    · intro b hb
      rcases Finset.mem_Ioc.mp hb with ⟨hmB, bM⟩
      have hbpos : 1 ≤ b := by omega
      refine ⟨b - 1, Finset.mem_Ico.mpr ?_, ?_⟩
      · exact ⟨Nat.le_sub_one_of_lt hmB, by omega⟩
      · exact Nat.sub_add_cancel hbpos
    · intro j hj
      rfl
  have hsplit :
      ∑ j ∈ Finset.Icc m M, f j = f m + ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) := by
    rw [Finset.Icc_eq_cons_Ioc hmM, Finset.sum_cons, hshift]
  have hfirst : f (m : ℝ) ≤ 1 / (m : ℝ) := by
    have hp : (m : ℝ) ^ (-2 : ℝ) ≤ (m : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
    calc
      f (m : ℝ) = (m : ℝ) ^ (-2 : ℝ) := rfl
      _ ≤ (m : ℝ) ^ (-1 : ℝ) := hp
      _ = 1 / (m : ℝ) := by
        rw [Real.rpow_neg hmpos.le 1, Real.rpow_one]
        simp only [one_div]
  have hintegral : ∫ x in Set.Ioi (m : ℝ), f x = 1 / (m : ℝ) := by
    rw [show f = fun x : ℝ => x ^ (-2 : ℝ) by rfl]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hmpos]
    norm_num
    rw [Real.rpow_neg hmpos.le 1, Real.rpow_one]
  calc
    ∑ j ∈ Finset.Icc m M, 1 / (j : ℝ) ^ 2 =
        ∑ j ∈ Finset.Icc m M, f j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjpos : 0 < (j : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le (by omega : 0 < m) (Finset.mem_Icc.mp hj).1)
          dsimp [f]
          rw [div_eq_mul_inv, one_mul]
          rw [← Real.rpow_natCast]
          exact (Real.rpow_neg hjpos.le (2 : ℝ)).symm
    _ = f (m : ℝ) + ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) := hsplit
    _ ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := by
      have hrest' := hrest
      rw [hintegral] at hrest'
      exact add_le_add hfirst hrest'
    _ = 2 / (m : ℝ) := by ring

private theorem block_inv_sq_sum_le (u b K : ℕ) (hub : u < b)
    (hK : b + 2 ≤ K) :
    ∑ i ∈ Finset.Icc (u + 1) b, 1 / ((K : ℝ) - i) ^ 2 ≤
      2 / ((K - b : ℕ) : ℝ) := by
  have hm : 2 ≤ K - b := by omega
  let m := K - b
  let M := K - (u + 1)
  have hindex :
      ∑ i ∈ Finset.Icc (u + 1) b, 1 / ((K : ℝ) - i) ^ 2 =
        ∑ j ∈ Finset.Icc m M, 1 / (j : ℝ) ^ 2 := by
    refine Finset.sum_bij (fun i _ => K - i) ?_ ?_ ?_ ?_
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      simp only [Finset.mem_Icc]
      constructor
      · exact Nat.sub_le_sub_left hi'.2 K
      · exact Nat.sub_le_sub_left hi'.1 K
    · intro a ha b' hb' hab
      have haK : a ≤ K := by have h := Finset.mem_Icc.mp ha; omega
      have hbK : b' ≤ K := by have h := Finset.mem_Icc.mp hb'; omega
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hjK : j ≤ K := by dsimp [M] at hj'; omega
      refine ⟨K - j, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        constructor <;> omega
      · omega
    · intro i hi
      congr 1
      have hiK : i ≤ K := le_trans (Finset.mem_Icc.mp hi).2 (by omega)
      rw [Nat.cast_sub hiK]
  have hsum := inv_sq_sum_Icc_le m M (by dsimp [m]; exact hm)
    (by dsimp [m, M]; omega)
  rw [hindex]
  simpa [m] using hsum

private theorem prod_adjacent_ratios (g : ℕ → ℝ) :
    ∀ u b : ℕ, u ≤ b → (∀ i ≤ b, 0 < g i) →
      ∏ i ∈ Finset.Icc (u + 1) b, g (i - 1) / g i = g u / g b := by
  intro u b hub hg
  induction b generalizing u with
  | zero =>
      have hu : u = 0 := by omega
      subst u
      have hIcc : Finset.Icc (1 : ℕ) 0 = ∅ := by
        ext i
        simp
      simp only [hIcc, Finset.prod_empty]
      exact (div_self (ne_of_gt (hg 0 le_rfl))).symm
  | succ b ih =>
      by_cases hu : u = b + 1
      · subst u
        have hIcc : Finset.Icc (b + 2) (b + 1) = ∅ := by
          ext i
          simp
        simp only [hIcc, Finset.prod_empty]
        exact (div_self (ne_of_gt (hg (b + 1) le_rfl))).symm
      · have hub' : u ≤ b := by omega
        have hgb' : 0 < g b := hg b (by omega)
        have hg' : ∀ i ≤ b, 0 < g i := fun i hi => hg i (by omega)
        rw [Finset.prod_Icc_succ_top (by omega : u + 1 ≤ b + 1)]
        rw [ih u hub' hg']
        dsimp
        field_simp [ne_of_gt (hg u (by omega)), ne_of_gt hgb',
          ne_of_gt (hg (b + 1) le_rfl)]

private theorem inv_sq_le_half {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hroot : Real.sqrt (2 * a) ≤ d) : a / d ^ 2 ≤ 1 / 2 := by
  have hsqrt : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  have hd2 : 2 * a ≤ d ^ 2 := by
    calc
      2 * a = Real.sqrt (2 * a) ^ 2 := hsqrt.symm
      _ ≤ d ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hd.le).2 hroot
  rw [div_le_iff₀ (sq_pos_of_pos hd)]
  calc
    a = (2 * a) / 2 := by ring
    _ ≤ d ^ 2 / 2 := div_le_div_of_nonneg_right hd2 (by norm_num)
    _ = (1 / 2) * d ^ 2 := by ring

private theorem one_le_factor_of_half_bounds {x s : ℝ}
    (hsx : s ≤ x / 2) (hxs : x * s ≤ x / 2) :
    1 ≤ (1 + x) * (1 - s) := by
  have hsum : s + x * s ≤ x / 2 + x / 2 := add_le_add hsx hxs
  have hsum' : s + x * s ≤ x := by calc
    _ ≤ x / 2 + x / 2 := hsum
    _ = x := by ring
  calc
    1 ≤ 1 + x - (s + x * s) := by linarith only [hsum']
    _ = (1 + x) * (1 - s) := by ring

/-- The long smoothed second moment is bounded by the product of the geometric block second
moments, up to the terminal inverse-distance correction. The left integral is integrable by
`integrable_smoothedP2Plane_sq`, and the block-factor integrals are integrable by
`integrable_blockMass_inv_and_sq`. -/
theorem secondMoment_le_prod_blockSecondMoment (A ρ₀ ρ₁ : ℝ) (hρ₀ : 1 < ρ₀) :
    ∃ (C : ℝ) (J₀ : ℕ), 1 ≤ J₀ ∧ ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ u b : ℕ,
        u ≤ b → b + J₀ ≤ Critical2DKPZ.blockCount N ρ →
          ∫ ω, smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N)
              (Critical2DKPZ.blockTime N ρ u) (Critical2DKPZ.blockTime N ρ b) 0 ω ^ 2
              ∂disorderLaw ≤
            (1 + C / ((Critical2DKPZ.blockCount N ρ : ℝ) - b)) *
              ∏ i ∈ Finset.Icc (u + 1) b,
                ∫ ω, blockMass (Critical2DKPZ.criticalBeta ϑ N)
                  (Critical2DKPZ.blockTime N ρ) i ω ^ 2 ∂disorderLaw := by
  obtain ⟨Cgap, hgap⟩ := renewalGap_criticalBeta_sub_log_bounded A
  obtain ⟨Cvn, hVN⟩ := smoothedP2Plane_secondMoment_renewalGap
  obtain ⟨Cperiod, hperiod⟩ := replicaOverlap_sub_log_bounded
  have hlogρ₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
  let c := Real.log ρ₀ / 6
  let Rbound := (Real.log (max ρ₁ ρ₀ + 2) + |Cperiod|) / Real.pi
  let E := |Cvn| * (1 + Rbound)
  let a := E / c ^ 2
  let H := 3 + (Real.log 2 + |Cgap|) / c + Real.sqrt (2 * a) + 4 * a
  let J₀ : ℕ := ⌈H⌉₊
  let C := 4 * a
  have hc : 0 < c := by dsimp [c]; positivity
  have hRbound : 0 ≤ Rbound := by
    dsimp [Rbound]
    have hρmax : 1 < max ρ₁ ρ₀ := lt_of_lt_of_le hρ₀ (le_max_right _ _)
    apply div_nonneg
    · exact add_nonneg (Real.log_nonneg (by linarith)) (abs_nonneg _)
    · exact Real.pi_pos.le
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hH3 : 3 ≤ H := by
    dsimp [H]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hsqrt : 0 ≤ Real.sqrt (2 * a) := Real.sqrt_nonneg _
    have hquot : 0 ≤ (Real.log 2 + |Cgap|) / c := by positivity
    have h4a : 0 ≤ 4 * a := by positivity
    linarith
  have hJceil : H ≤ (J₀ : ℝ) := by
    dsimp [J₀]
    exact Nat.le_ceil H
  have hJthree : 3 ≤ (J₀ : ℝ) := le_trans hH3 hJceil
  have hJgap : (Real.log 2 + |Cgap|) / c ≤ (J₀ : ℝ) := by
    have h := hJceil
    dsimp [H] at h
    have hrest : 0 ≤ 3 + Real.sqrt (2 * a) + 4 * a := by positivity
    linarith
  have hJsqrt : Real.sqrt (2 * a) ≤ (J₀ : ℝ) := by
    have h := hJceil
    dsimp [H] at h
    have hrest : 0 ≤ 3 + (Real.log 2 + |Cgap|) / c + 4 * a := by
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    linarith
  have hJa : 4 * a ≤ (J₀ : ℝ) := by
    have h := hJceil
    dsimp [H] at h
    have hrest : 0 ≤ 3 + (Real.log 2 + |Cgap|) / c + Real.sqrt (2 * a) := by
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlogN : ∀ᶠ N : ℕ in atTop, |A| < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |A|
  refine ⟨C, J₀, ?_, ?_⟩
  · exact_mod_cast (show (1 : ℝ) ≤ (J₀ : ℝ) by linarith)
  · intro ρ hρρ
    have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρρ.1
    have hρNclock := Filter.eventually_ge_atTop (⌈2 * ρ₀ / (ρ₀ - 1)⌉₊)
    have hρNfirst := Filter.eventually_ge_atTop (⌈ρ₁⌉₊)
    have hNtwo := Filter.eventually_ge_atTop 2
    filter_upwards [hgap, hlogN, hρNclock, hρNfirst, hNtwo] with N hgapN hlogNN hNclock hNfirst hNtwo
    intro ϑ hϑ u b hub hKmargin
    let K := Critical2DKPZ.blockCount N ρ
    let t := Critical2DKPZ.blockTime N ρ
    let β := Critical2DKPZ.criticalBeta ϑ N
    let g := fun i : ℕ => renewalGap β (t i)
    have hN1 : 1 ≤ N := by omega
    have hρ₁N : ρ₁ ≤ (N : ℝ) := by
      exact (Nat.le_ceil ρ₁).trans (by exact_mod_cast hNfirst)
    have hρN : ρ ≤ (N : ℝ) := hρρ.2.trans hρ₁N
    have hclock : Monotone t := by
      dsimp [t]
      exact Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon
        hρ₀ hρρ.1 hNclock
    have hKfinal : t K = N := by
      have hJnat : 1 ≤ J₀ := by
        exact_mod_cast (show (1 : ℝ) ≤ (J₀ : ℝ) by linarith)
      have hKle : b + J₀ ≤ K := by simpa [K] using hKmargin
      have hKpos : 0 < K := lt_of_lt_of_le (by omega) hKle
      have hcount : Critical2DKPZ.blockCount N ρ ≠ 0 := by
        simpa [K] using Nat.ne_of_gt hKpos
      dsimp [t, K]
      simp [Critical2DKPZ.blockTime, hcount]
    have htimeLe (i : ℕ) (hi : i ≤ K) : t i ≤ N := by
      calc
        t i ≤ t K := hclock hi
        _ = N := hKfinal
    have hgapNθ := hgapN ϑ hϑ
    have hgapApprox (i : ℕ) (hi : i ≤ K) :
        |g i - Real.log ((N : ℝ) / ((max (t i) 1 : ℕ) : ℝ))| ≤ |Cgap| := by
      have h := hgapNθ (t i) (htimeLe i hi)
      exact le_trans (by simpa [g, t, β] using h) (le_abs_self Cgap)
    have hRmono (s n : ℕ) (hsn : s ≤ n) : replicaOverlap s ≤ replicaOverlap n := by
      have hsum := replicaOverlap_sub_eq_sum s n hsn
      have hnonneg : 0 ≤ ∑ r ∈ Finset.Icc (s + 1) n, Renewal.returnWeight r :=
        Finset.sum_nonneg fun r hr => Critical2DKPZ.srwKernel_nonneg (2 * r) 0
      have hsub : 0 ≤ replicaOverlap n - replicaOverlap s := by
        rw [hsum]
        exact hnonneg
      exact sub_nonneg.mp hsub
    have hgapMono (i j : ℕ) (hij : i ≤ j) : g j ≤ g i := by
      have htime := hclock hij
      have hR := hRmono (t i) (t j) htime
      have hdiff : 0 ≤ replicaOverlap (t j) - replicaOverlap (t i) := sub_nonneg.mpr hR
      have hmul := mul_nonneg Real.pi_pos.le hdiff
      dsimp [g, renewalGap]
      linarith only [hmul]
    have hKbound : b + 3 ≤ K := by
      have hJnat : 3 ≤ J₀ := by exact_mod_cast hJthree
      omega
    have hbK : b < K := by omega
    have hbN : b ≤ K := Nat.le_of_lt hbK
    have hGapLower (i : ℕ) (hi : 1 ≤ i) (hib : i ≤ b) :
        c * ((K - i : ℕ) : ℝ) ≤ g i := by
      have hiK : i < K := by omega
      have htimePos : 0 < (t i : ℝ) := by
        have hscale := Critical2DKPZ.MomentBounds.blockTime_lower_geometric_scale
          hρ hi hiK
        have hiReal : 1 ≤ (i : ℝ) := by exact_mod_cast hi
        have hpow : 1 ≤ ρ ^ ((i : ℝ) - 1) :=
          Real.one_le_rpow hρ.le (by linarith)
        have h := hpow.trans hscale
        exact lt_of_lt_of_le (by norm_num) h
      have htimePosNat : 0 < t i := by exact_mod_cast htimePos
      have htimeRealPos : 0 < (t i : ℝ) := htimePos
      have hNtime : 1 ≤ (N : ℝ) / t i := by
        apply (le_div_iff₀ htimeRealPos).2
        have htimeLeR : (t i : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast (htimeLe i (Nat.le_of_lt hiK))
        simpa using htimeLeR
      have hlogCompare : Real.log (1 + (N : ℝ) / t i) ≤
          Real.log 2 + Real.log ((N : ℝ) / t i) := by
        have hxpos : 0 < (N : ℝ) / t i := by positivity
        have htwo : 1 + (N : ℝ) / t i ≤ 2 * ((N : ℝ) / t i) := by linarith
        calc
          Real.log (1 + (N : ℝ) / t i) ≤ Real.log (2 * ((N : ℝ) / t i)) :=
            Real.log_le_log (by positivity) htwo
          _ = Real.log 2 + Real.log ((N : ℝ) / t i) := by
            rw [Real.log_mul (by norm_num) hxpos.ne']
      have hclockLog := Critical2DKPZ.MomentBounds.blockTime_log_horizon_lower
        hρ₀ hρρ.1 hi hiK
      have htimeOne : 1 ≤ t i := by omega
      have hmax : max (t i) 1 = t i := max_eq_left (by exact_mod_cast htimeOne)
      have happrox := hgapApprox i (Nat.le_of_lt hiK)
      have hgapLog : Real.log ((N : ℝ) / t i) - |Cgap| ≤ g i := by
        have habs := abs_le.mp (by simpa [hmax, g] using happrox)
        linarith
      have hKminus : (J₀ : ℝ) ≤ (K - i : ℕ) := by
        have : J₀ ≤ K - i := by omega
        exact_mod_cast this
      have hscale : (Real.log 2 + |Cgap|) ≤ c * ((K - i : ℕ) : ℝ) := by
        have hJ : Real.log 2 + |Cgap| ≤ c * (J₀ : ℝ) :=
          (by
            have hJ' := (div_le_iff₀ hc).mp hJgap
            calc
              Real.log 2 + |Cgap| ≤ (J₀ : ℝ) * c := hJ'
              _ = c * (J₀ : ℝ) := by ring)
        have hlarge := mul_le_mul_of_nonneg_left hKminus hc.le
        exact hJ.trans hlarge
      have hclockLog' : 2 * (c * ((K - i : ℕ) : ℝ)) ≤
          Real.log (1 + (N : ℝ) / t i) := by
        calc
          2 * (c * ((K - i : ℕ) : ℝ)) =
              ((K - i : ℕ) : ℝ) * Real.log ρ₀ / 3 := by dsimp [c]; ring
          _ ≤ Real.log (1 + (N : ℝ) / t i) := hclockLog
      calc
        c * ((K - i : ℕ) : ℝ) ≤
            2 * (c * ((K - i : ℕ) : ℝ)) - (Real.log 2 + |Cgap|) := by linarith
        _ ≤ Real.log ((N : ℝ) / t i) - |Cgap| := by linarith
        _ ≤ g i := hgapLog
    have hβpos : 0 < β := by
      have hA0 : 0 ≤ A := by linarith [hϑ.1, hϑ.2]
      have hθabs : |ϑ| ≤ A := abs_le.mpr ⟨hϑ.1, hϑ.2⟩
      have hAlog : A < Real.log (N : ℝ) := by simpa [abs_of_nonneg hA0] using hlogNN
      have hθlog : |ϑ| < Real.log (N : ℝ) := lt_of_le_of_lt hθabs hAlog
      have hσ := criticalSigmaSq_pos_of_abs_lt_log hN1 hθlog
      dsimp [β, Critical2DKPZ.criticalBeta]
      apply Real.sqrt_pos.2
      exact Real.log_pos (by linarith)
    have hGpos (i : ℕ) (hib : i ≤ b) : 0 < g i := by
      by_cases hi0 : i = 0
      · subst i
        have hσpos : 0 < Polymer.sigmaSq β := by
          dsimp [Polymer.sigmaSq]
          apply sub_pos.mpr
          rw [Real.one_lt_exp_iff]
          exact sq_pos_of_pos hβpos
        have ht0 : t 0 = 0 := by simp [t, Critical2DKPZ.blockTime]
        have hrep0 : replicaOverlap 0 = 0 := by simp [replicaOverlap]
        change 0 < renewalGap β (t 0)
        rw [ht0, renewalGap, hrep0]
        simpa using div_pos Real.pi_pos hσpos
      · have hi : 1 ≤ i := by omega
        have h := hGapLower i hi hib
        have hcpos := hc
        have hdpos : 0 < ((K - i : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < K - i by omega)
        exact lt_of_lt_of_le (mul_pos hcpos hdpos) h
    by_cases hubEq : u = b
    · subst u
      have hprodEmpty : ∏ i ∈ Finset.Icc (b + 1) b,
          ∫ ω, blockMass β t i ω ^ 2 ∂disorderLaw = 1 := by simp
      rw [hprodEmpty]
      have hgap := hVN β hβpos (t b) (t b) le_rfl (hGpos b le_rfl)
      have hratio : g b / g b = 1 := div_self (ne_of_gt (hGpos b le_rfl))
      have hmoment : ∫ ω, smoothedP2Plane β (t b) (t b) 0 ω ^ 2 ∂disorderLaw ≤ 1 := by
        linarith [hgap.1]
      have hcoef : 1 ≤ 1 + C / ((K : ℝ) - b) := by
        have hden : 0 < (K : ℝ) - b := by exact_mod_cast (show 0 < K - b by omega)
        change 1 ≤ 1 + 4 * a / ((K : ℝ) - b)
        have hnum : 0 ≤ (4 * a : ℝ) := by positivity
        have hfrac : 0 ≤ 4 * a / ((K : ℝ) - b) := div_nonneg hnum hden.le
        linarith
      simpa using hmoment.trans hcoef
    · have hublt : u < b := lt_of_le_of_ne hub hubEq
      let m := fun i : ℕ => ∫ ω, blockMass β t i ω ^ 2 ∂disorderLaw
      let q := fun i : ℕ => g (i - 1) / g i
      let η := fun i : ℕ => a / ((K - i : ℕ) : ℝ) ^ 2
      have hblock (i : ℕ) (hi : i ∈ Finset.Icc (u + 1) b) :
          q i * (1 - η i) ≤ m i := by
        have hi' := Finset.mem_Icc.mp hi
        have hi1 : 1 ≤ i := by omega
        have hiB : i ≤ b := hi'.2
        have hiK : i < K := by omega
        let d : ℝ := ((K - i : ℕ) : ℝ)
        have hdpos : 0 < d := by
          dsimp [d]
          exact_mod_cast (show 0 < K - i by omega)
        have hgapPos := hGapLower i hi1 hiB
        have hgapRealPos : 0 < g i := by
          exact lt_of_lt_of_le (mul_pos hc hdpos) hgapPos
        have hprevle : i - 1 ≤ i := by omega
        have hclockBlock : t (i - 1) ≤ t i := hclock hprevle
        have hRdiff : 0 ≤ replicaOverlap (t i) - replicaOverlap (t (i - 1)) := by
          exact sub_nonneg.mpr (hRmono _ _ hclockBlock)
        have hratioBound :
            (((max (t i) 1 : ℕ) : ℝ) / ((max (t (i - 1)) 1 : ℕ) : ℝ)) ≤ ρ + 2 := by
          by_cases hiEq : i = 1
          · subst i
            simpa [t] using Critical2DKPZ.MomentBounds.blockTime_first_endpoint_ratio_le hρ hρN
          · have hi2 : 2 ≤ i := by omega
            simpa [t] using Critical2DKPZ.MomentBounds.blockTime_endpoint_ratio_le hρ hi2 hiK
        have hRupper := Critical2DKPZ.MomentBounds.replicaOverlap_sub_le_of_ratio_bound
          Cperiod hperiod hclockBlock hratioBound
        have hRupper' : replicaOverlap (t i) - replicaOverlap (t (i - 1)) ≤ Rbound := by
          dsimp [Rbound]
          have hρmax : ρ ≤ max ρ₁ ρ₀ := le_trans hρρ.2 (le_max_left _ _)
          have hlog : Real.log (ρ + 2) ≤ Real.log (max ρ₁ ρ₀ + 2) := by
            apply Real.log_le_log
            · linarith
            · linarith
          have hnum : Real.log (ρ + 2) + Cperiod ≤
              Real.log (max ρ₁ ρ₀ + 2) + |Cperiod| := by
            linarith [le_abs_self Cperiod, hlog]
          calc
            replicaOverlap (t i) - replicaOverlap (t (i - 1)) ≤
                (Real.log (ρ + 2) + Cperiod) / Real.pi := hRupper
            _ ≤ Rbound := div_le_div_of_nonneg_right hnum Real.pi_pos.le
        have hgapKerr := hVN β hβpos (t (i - 1)) (t i) hclockBlock hgapRealPos
        have hq : q i = g (i - 1) / g i := rfl
        have hmassEq : m i =
            ∫ ω, smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ 2 ∂disorderLaw := by
          rfl
        have hKerr : q i - m i ≤
            Cvn * (1 + replicaOverlap (t i) - replicaOverlap (t (i - 1))) / g i ^ 2 := by
          calc
            q i - m i = g (i - 1) / g i -
                ∫ ω, smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ 2 ∂disorderLaw := by
                  rw [hq, hmassEq]
            _ ≤ _ := by simpa only [g] using hgapKerr.2.1
        have hRfactor : 0 ≤ 1 + replicaOverlap (t i) - replicaOverlap (t (i - 1)) := by
          linarith
        have herrorAbs : q i - m i ≤
            |Cvn| * (1 + replicaOverlap (t i) - replicaOverlap (t (i - 1))) / g i ^ 2 := by
          apply le_trans hKerr
          apply div_le_div_of_nonneg_right _ (sq_nonneg (g i))
          exact mul_le_mul_of_nonneg_right (le_abs_self Cvn) hRfactor
        have herrorE : q i - m i ≤ E / g i ^ 2 := by
          apply le_trans herrorAbs
          apply div_le_div_of_nonneg_right _ (sq_nonneg (g i))
          dsimp [E]
          have hRfactor' : 1 + replicaOverlap (t i) - replicaOverlap (t (i - 1)) ≤
              1 + Rbound := by
            calc
              1 + replicaOverlap (t i) - replicaOverlap (t (i - 1)) =
                  1 + (replicaOverlap (t i) - replicaOverlap (t (i - 1))) := by ring
              _ ≤ 1 + Rbound := add_le_add_right hRupper' 1
          exact mul_le_mul_of_nonneg_left hRfactor' (abs_nonneg Cvn)
        have hetaBound : E / g i ^ 2 ≤ η i := by
          have hden : (c * d) ^ 2 ≤ g i ^ 2 := by
            have hleft0 : 0 ≤ c * d := mul_nonneg hc.le hdpos.le
            exact (sq_le_sq₀ hleft0 hgapRealPos.le).2 (by simpa [d] using hgapPos)
          have hcmp := div_le_div_of_nonneg_left hE
            (sq_pos_of_pos (mul_pos hc hdpos)) hden
          have hrewrite : E / (c * d) ^ 2 = η i := by
            change E / (c * d) ^ 2 = a / d ^ 2
            dsimp [a]
            field_simp [ne_of_gt hc, ne_of_gt hdpos]
          calc
            E / g i ^ 2 ≤ E / (c * d) ^ 2 := hcmp
            _ = η i := hrewrite
        have hηi : η i = a / d ^ 2 := by rfl
        have hηnonneg : 0 ≤ η i := by rw [hηi]; positivity
        have hroot : Real.sqrt (2 * a) ≤ ((K - i : ℕ) : ℝ) := by
          have hji : (J₀ : ℝ) ≤ ((K - i : ℕ) : ℝ) := by
            have hnat : J₀ ≤ K - i := by omega
            exact_mod_cast hnat
          exact le_trans hJsqrt hji
        have hηhalf : η i ≤ 1 / 2 := by
          have hsqrt : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
          have hd2 : 2 * a ≤ d ^ 2 := by
            calc
              2 * a = Real.sqrt (2 * a) ^ 2 := hsqrt.symm
              _ ≤ d ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hdpos.le).2 (by simpa [d] using hroot)
          rw [hηi, div_le_iff₀ (sq_pos_of_pos hdpos)]
          calc
            a = (2 * a) / 2 := by ring
            _ ≤ d ^ 2 / 2 := div_le_div_of_nonneg_right hd2 (by norm_num)
            _ = (1 / 2) * d ^ 2 := by ring
        have hgapMon' : g i ≤ g (i - 1) := hgapMono (i - 1) i hprevle
        have hqge : 1 ≤ q i := by
          dsimp [q]
          exact (le_div_iff₀ hgapRealPos).2 (by simpa using hgapMon')
        have hqeta : η i ≤ q i * η i := by
          calc
            η i = 1 * η i := by ring
            _ ≤ q i * η i := mul_le_mul_of_nonneg_right hqge hηnonneg
        have hqMinus : q i - η i ≤ m i := by
          have herr := le_trans herrorE hetaBound
          linarith
        calc
          q i * (1 - η i) = q i - q i * η i := by ring
          _ ≤ q i - η i := sub_le_sub_left hqeta (q i)
          _ ≤ m i := hqMinus
      have hsumSq := block_inv_sq_sum_le u b K hublt (by omega)
      have hηsum : ∑ i ∈ Finset.Icc (u + 1) b, η i ≤
          2 * a / ((K - b : ℕ) : ℝ) := by
        dsimp [η]
        calc
          _ = a * (∑ i ∈ Finset.Icc (u + 1) b,
                1 / ((K : ℝ) - i) ^ 2) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hiK : i ≤ K := le_trans (Finset.mem_Icc.mp hi).2 hbN
                  have hcast : ((K - i : ℕ) : ℝ) = (K : ℝ) - i := by
                    rw [Nat.cast_sub hiK]
                  rw [← hcast]
                  ring
          _ ≤ a * (2 / ((K - b : ℕ) : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hsumSq ha
          _ = 2 * a / ((K - b : ℕ) : ℝ) := by ring
      have hJreal : (J₀ : ℝ) ≤ ((K - b : ℕ) : ℝ) := by
        have hnat : J₀ ≤ K - b := by omega
        exact_mod_cast hnat
      have hsumHalf : ∑ i ∈ Finset.Icc (u + 1) b, η i ≤ 1 / 2 := by
        have := hηsum
        have hja : 4 * a ≤ ((K - b : ℕ) : ℝ) := le_trans hJa hJreal
        have hJone : 1 ≤ (J₀ : ℝ) := by linarith
        have hden : 0 < ((K - b : ℕ) : ℝ) :=
          lt_of_lt_of_le (by norm_num) (le_trans hJone hJreal)
        have hbound : 2 * a / ((K - b : ℕ) : ℝ) ≤ 1 / 2 := by
          rw [div_le_iff₀ hden]
          calc
            2 * a = (4 * a) / 2 := by ring
            _ ≤ ((K - b : ℕ) : ℝ) / 2 := div_le_div_of_nonneg_right hja (by norm_num)
            _ = (1 / 2) * ((K - b : ℕ) : ℝ) := by ring
        exact this.trans hbound
      have hη0 : ∀ i ∈ Finset.Icc (u + 1) b, 0 ≤ η i := by
        intro i hi
        change 0 ≤ a / ((K - i : ℕ) : ℝ) ^ 2
        exact div_nonneg ha (sq_nonneg _)
      have hη1 : ∀ i ∈ Finset.Icc (u + 1) b, η i ≤ 1 := by
        intro i hi
        have hi' := Finset.mem_Icc.mp hi
        let d : ℝ := ((K - i : ℕ) : ℝ)
        have hdpos : 0 < d := by
          dsimp [d]
          exact_mod_cast (show 0 < K - i by omega)
        have hroot : Real.sqrt (2 * a) ≤ ((K - i : ℕ) : ℝ) := by
          have hnat : J₀ ≤ K - i := by omega
          exact le_trans hJsqrt (by exact_mod_cast hnat)
        have hηi : η i = a / d ^ 2 := by rfl
        have hηhalf : η i ≤ 1 / 2 := by
          rw [hηi]
          exact inv_sq_le_half ha hdpos (by simpa [d] using hroot)
        linarith
      have hbern := prod_one_sub_ge_one_sub_sum
        (Finset.Icc (u + 1) b) η hη0 hη1
      let S := Finset.Icc (u + 1) b
      have hprodEach (i : ℕ) (hi : i ∈ S) :
          0 ≤ q i * (1 - η i) ∧ q i * (1 - η i) ≤ m i := by
        have hη : η i ≤ 1 := hη1 i hi
        have hi' := Finset.mem_Icc.mp hi
        have hprevPos := hGpos (i - 1) (le_trans (Nat.sub_le _ _) hi'.2)
        have hiPos := hGpos i hi'.2
        have hqnonneg : 0 ≤ q i := by
          change 0 ≤ g (i - 1) / g i
          exact div_nonneg hprevPos.le hiPos.le
        exact ⟨mul_nonneg hqnonneg (sub_nonneg.mpr hη), hblock i hi⟩
      have hprodTerm :
          (∏ i ∈ Finset.Icc (u + 1) b, q i) *
            ∏ i ∈ Finset.Icc (u + 1) b, (1 - η i) ≤
          ∏ i ∈ Finset.Icc (u + 1) b, m i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_le_prod₀ (s := S)
          (f := fun i => q i * (1 - η i)) (g := m)
          (fun i hi => (hprodEach i hi).1) (fun i hi => (hprodEach i hi).2)
      have hqpos : 0 < ∏ i ∈ Finset.Icc (u + 1) b, q i := by
        exact Finset.prod_pos (fun i hi => by
          have hi' := Finset.mem_Icc.mp hi
          have hprevPos := hGpos (i - 1) (le_trans (Nat.sub_le _ _) hi'.2)
          have hiPos := hGpos i hi'.2
          change 0 < g (i - 1) / g i
          exact div_pos hprevPos hiPos)
      have hGposUpToB : ∀ i ≤ b, 0 < g i := hGpos
      have hqTel := prod_adjacent_ratios g u b hub hGposUpToB
      have hfactorLower : 1 / 2 ≤ ∏ i ∈ Finset.Icc (u + 1) b, (1 - η i) := by
        have hsum := hbern
        have hsum' : 1 / 2 ≤ 1 - ∑ i ∈ Finset.Icc (u + 1) b, η i := by linarith
        exact hsum'.trans hbern
      have hprodLower :
          (g u / g b) * (1 - ∑ i ∈ Finset.Icc (u + 1) b, η i) ≤
            ∏ i ∈ Finset.Icc (u + 1) b, m i := by
        rw [← hqTel]
        calc
          _ ≤ (∏ i ∈ Finset.Icc (u + 1) b, q i) *
                ∏ i ∈ Finset.Icc (u + 1) b, (1 - η i) :=
              mul_le_mul_of_nonneg_left hbern (le_of_lt hqpos)
          _ ≤ _ := hprodTerm
      have hfactorNonneg : 0 ≤ 1 - ∑ i ∈ Finset.Icc (u + 1) b, η i := by linarith [hsumHalf]
      have hratioPos : 0 < g u / g b := div_pos (hGpos u (le_of_lt hublt)) (hGpos b (le_rfl))
      have hwhole := hVN β hβpos (t u) (t b) (hclock hub) (hGpos b le_rfl)
      have hwholeUpper :
          ∫ ω, smoothedP2Plane β (t u) (t b) 0 ω ^ 2 ∂disorderLaw ≤ g u / g b := by
        linarith [hwhole.1]
      have hcoefFactor : 1 ≤ (1 + C / ((K : ℝ) - b)) *
          (1 - ∑ i ∈ Finset.Icc (u + 1) b, η i) := by
        let j := ((K - b : ℕ) : ℝ)
        have hjpos : 0 < j := by
          dsimp [j]
          exact_mod_cast (show 0 < K - b by omega)
        have hdenEq : j = (K : ℝ) - b := by
          dsimp [j]
          rw [Nat.cast_sub (by omega)]
        have hx : 0 ≤ 4 * a / j := by positivity
        have hs : ∑ i ∈ Finset.Icc (u + 1) b, η i ≤ 2 * a / j := by
          simpa [j] using hηsum
        have hsx : ∑ i ∈ Finset.Icc (u + 1) b, η i ≤ (4 * a / j) / 2 := by
          calc
            _ ≤ 2 * a / j := hs
            _ = (4 * a / j) / 2 := by ring
        have hxs : (4 * a / j) *
            (∑ i ∈ Finset.Icc (u + 1) b, η i) ≤ (4 * a / j) / 2 :=
          mul_le_mul_of_nonneg_left (by simpa [one_div] using hsumHalf) hx
        have hfactor : 1 ≤ (1 + 4 * a / j) *
            (1 - ∑ i ∈ Finset.Icc (u + 1) b, η i) := by
          exact one_le_factor_of_half_bounds hsx hxs
        have hcoeff : C / ((K : ℝ) - b) = 4 * a / j := by
          dsimp [C]
          rw [← hdenEq]
        rw [hcoeff]
        exact hfactor
      have hratioBound : g u / g b ≤
          (1 + C / ((K : ℝ) - b)) * ∏ i ∈ Finset.Icc (u + 1) b, m i := by
        have hden : 0 < (K : ℝ) - b := by
          exact_mod_cast (show 0 < K - b by omega)
        have hfactorNonneg : 0 ≤ 1 + C / ((K : ℝ) - b) :=
          add_nonneg (by norm_num) (div_nonneg hC hden.le)
        calc
          g u / g b = (g u / g b) * 1 := by ring
          _ ≤ (g u / g b) *
              ((1 + C / ((K : ℝ) - b)) *
                (1 - ∑ i ∈ Finset.Icc (u + 1) b, η i)) :=
              mul_le_mul_of_nonneg_left hcoefFactor (le_of_lt hratioPos)
          _ = (1 + C / ((K : ℝ) - b)) *
                ((g u / g b) *
                  (1 - ∑ i ∈ Finset.Icc (u + 1) b, η i)) := by ring
          _ ≤ (1 + C / ((K : ℝ) - b)) *
                ∏ i ∈ Finset.Icc (u + 1) b, m i :=
              mul_le_mul_of_nonneg_left hprodLower hfactorNonneg
      calc
        _ ≤ g u / g b := hwholeUpper
        _ ≤ (1 + C / ((K : ℝ) - b)) *
              ∏ i ∈ Finset.Icc (u + 1) b, m i := hratioBound
        _ = _ := by simp [m, β, t, K]

end Critical2DKPZ.OnePoint

end
