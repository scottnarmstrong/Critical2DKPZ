/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.MarkedUniformLimit
public import Critical2DKPZ.Renewal.PositiveArray
import Critical2DKPZ.RandomWalk.ReplicaOverlap
import Mathlib.Tactic.Linarith

/-!
# The local critical renewal limit

The differentiated renewal identity expresses a local renewal mass as a return-kernel
first moment tested against the marked renewal mass. The marked cumulative limit and the
period-two local central limit theorem then give the local density, uniformly on compact
positive-time and critical-parameter windows.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The first moment of the period-two return kernel converges to its continuum value. -/
theorem tendsto_returnWeight_moment :
    Tendsto (fun r : ℕ => (r : ℝ) * returnWeight r) atTop (nhds (1 / Real.pi)) := by
  obtain ⟨C, hC, hlocal⟩ := srwKernel_two_mul_zero_localCLT
  have herror : Tendsto (fun r : ℕ =>
      |(r : ℝ) * returnWeight r - 1 / Real.pi|) atTop (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall : Tendsto (fun r : ℕ => C / (r : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    obtain ⟨R, hR⟩ := eventually_atTop.mp
      (hsmall.eventually (Metric.ball_mem_nhds 0 hε))
    filter_upwards [eventually_ge_atTop (max R 1)] with r hr
    have hr1 : 1 ≤ r := le_trans (le_max_right R 1) hr
    have hrR : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr1)
    have hloc := hlocal r (by omega)
    change |returnWeight r - (1 / Real.pi) * (r : ℝ)⁻¹| ≤ C / (r : ℝ) ^ 2 at hloc
    have hmul : |(r : ℝ) * returnWeight r - 1 / Real.pi| ≤ C / (r : ℝ) := by
      have hrewrite : (r : ℝ) * returnWeight r - 1 / Real.pi =
          (r : ℝ) * (returnWeight r - (1 / Real.pi) * (r : ℝ)⁻¹) := by
        field_simp
      rw [hrewrite, abs_mul, abs_of_pos hrR]
      calc
        (r : ℝ) * |returnWeight r - (1 / Real.pi) * (r : ℝ)⁻¹|
          ≤ (r : ℝ) * (C / (r : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hloc hrR.le
        _ = C / (r : ℝ) := by field_simp
    have hball := hR r (le_trans (le_max_left R 1) hr)
    have hball' : C / (r : ℝ) < ε := by
      have hpos : 0 < C / (r : ℝ) := div_pos hC hrR
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hpos] using hball
    have hgoal : |(r : ℝ) * returnWeight r - 1 / Real.pi| < ε := hmul.trans_lt hball'
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)] using hgoal
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herror.eventually (Metric.ball_mem_nhds 0 hε)] with r hr
  have hdist : |(r : ℝ) * returnWeight r - 1 / Real.pi| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg (abs_nonneg _)] using hr
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)] using hdist

/-- The renewal index tends to infinity whenever its normalized time has a positive limit. -/
theorem tendsto_moving_index_atTop {ι : Type*} {L : Filter ι} {N m : ι → ℕ} {t : ℝ}
    (hN : Tendsto N L atTop)
    (hm : Tendsto (fun i => (m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds t))
    (ht : 0 < t) : Tendsto m L atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  have hratio : ∀ᶠ i in L,
      t / 2 < (m i : ℝ) / ((N i + 1 : ℕ) : ℝ) :=
    hm.eventually (eventually_gt_nhds (by linarith))
  have hN1 : Tendsto (fun i => N i + 1) L atTop :=
    (tendsto_add_atTop_nat 1).comp hN
  have hden : Tendsto (fun i => ((N i + 1 : ℕ) : ℝ)) L atTop :=
    tendsto_natCast_atTop_atTop.comp hN1
  have hlarge : ∀ᶠ i in L,
      2 * ((b : ℝ) + 1) / t < ((N i + 1 : ℕ) : ℝ) :=
    hden.eventually_gt_atTop (2 * ((b : ℝ) + 1) / t)
  filter_upwards [hratio, hlarge] with i hi hlarge
  have hdenpos : 0 < ((N i + 1 : ℕ) : ℝ) := by positivity
  have hprod : ((m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) *
      ((N i + 1 : ℕ) : ℝ) = (m i : ℝ) := by field_simp
  have h1 := mul_lt_mul_of_pos_right hi hdenpos
  have h2 := mul_lt_mul_of_pos_left hlarge (half_pos ht)
  have htarget : (t / 2) * (2 * ((b : ℝ) + 1) / t) = (b : ℝ) + 1 := by
    field_simp
  have hb : (b : ℝ) + 1 < (m i : ℝ) := by
    calc
      (b : ℝ) + 1 = (t / 2) * (2 * ((b : ℝ) + 1) / t) := htarget.symm
      _ < (t / 2) * ((N i + 1 : ℕ) : ℝ) := h2
      _ < (m i : ℝ) := by simpa only [hprod] using h1
  have hb' : b + 1 < m i := by exact_mod_cast hb
  have hb0 : b < m i := by omega
  exact Nat.le_of_lt hb0

/-- A macroscopic renewal index remains macroscopic after subtracting a fixed gap. -/
theorem tendsto_sub_index_scale {ι : Type*} {L : Filter ι} {N m : ι → ℕ} {t : ℝ}
    (hN : Tendsto N L atTop)
    (hm : Tendsto (fun i => (m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds t))
    (ht : 0 < t) (d : ℕ) :
    Tendsto (fun i => ((m i - d : ℕ) : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds t) := by
  have hN1 : Tendsto (fun i => N i + 1) L atTop :=
    (tendsto_add_atTop_nat 1).comp hN
  have hden : Tendsto (fun i => ((N i + 1 : ℕ) : ℝ)) L atTop :=
    tendsto_natCast_atTop_atTop.comp hN1
  have hsmall : Tendsto (fun i => (d : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds 0) := by
    simpa only [Nat.cast_ofNat] using (tendsto_const_nhds.div_atTop hden)
  have hmTop : Tendsto m L atTop := tendsto_moving_index_atTop hN hm ht
  have h := hm.sub hsmall
  have heq : (fun i => ((m i - d : ℕ) : ℝ) / ((N i + 1 : ℕ) : ℝ)) =ᶠ[L]
      fun i => (m i : ℝ) / ((N i + 1 : ℕ) : ℝ) -
        (d : ℝ) / ((N i + 1 : ℕ) : ℝ) := by
    filter_upwards [hmTop.eventually_ge_atTop d] with i hi
    rw [Nat.cast_sub hi]
    ring
  simpa only [sub_zero] using h.congr' heq.symm

/-- The marked cumulative limit applies to any moving sequence of macroscopic indices. -/
theorem tendsto_markedProfile_moving {ι : Type*} {L : Filter ι} {N m : ι → ℕ}
    {θ : ι → ℝ} {θ₀ t : ℝ} (hN : Tendsto N L atTop)
    (hθ : Tendsto θ L (nhds θ₀))
    (hm : Tendsto (fun i => (m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds t))
    (ht : 0 < t) :
    Tendsto (fun i => markedRenewalFunction
      (fun r => criticalSigmaSq (θ i) (N i) * returnWeight r) (m i) /
        (Real.log (N i)) ^ 2) L
      (nhds (t * DeltaBose.scalarDensity (θ₀ - Real.eulerMascheroniConstant) t)) := by
  have hparam : Tendsto (fun i => (θ i,
      (m i : ℝ) / ((N i + 1 : ℕ) : ℝ))) L (nhds (θ₀, t)) := hθ.prodMk_nhds hm
  have hjoint := (tendsto_joint_criticalMarkedProfile ht).comp (hN.prodMk hparam)
  apply hjoint.congr'
  filter_upwards with i
  change markedRenewalFunction
      (fun r => criticalSigmaSq (θ i) (N i) * returnWeight r)
      ⌊((N i : ℝ) + 1) * ((m i : ℝ) / ((N i + 1 : ℕ) : ℝ))⌋₊ /
        (Real.log (N i)) ^ 2 = _
  have hden : ((N i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hprod : ((N i + 1 : ℕ) : ℝ) *
      ((m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) = (m i : ℝ) := by
    field_simp
  have hprod' : ((N i : ℝ) + 1) *
      ((m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) = (m i : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hprod
  rw [hprod', Nat.floor_natCast]

/-- A marked local mass is the difference of two marked cumulative masses. -/
theorem markedRenewalMass_succ_eq_sub (w : ℕ → ℝ) (n : ℕ) :
    markedRenewalMass w (n + 1) =
      markedRenewalFunction w (n + 1) - markedRenewalFunction w n := by
  have hsum : markedRenewalFunction w (n + 1) =
      markedRenewalFunction w n + markedRenewalMass w (n + 1) := by
    rw [← sum_markedRenewalMass_range w (n + 1),
      ← sum_markedRenewalMass_range w n]
    conv_lhs => rw [Finset.sum_range_succ]
  linarith

/-- The critical variance times `log N` converges jointly with the parameter. -/
theorem tendsto_criticalSigmaSq_mul_log_moving {ι : Type*} {L : Filter ι}
    {N : ι → ℕ} {θ : ι → ℝ} {θ₀ : ℝ}
    (hN : Tendsto N L atTop) (hθ : Tendsto θ L (nhds θ₀)) :
    Tendsto (fun i => criticalSigmaSq (θ i) (N i) * Real.log (N i)) L (nhds Real.pi) := by
  have hlog : Tendsto (fun i => Real.log (N i)) L atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hnum : Tendsto (fun i => 1 + θ i / Real.log (N i)) L (nhds 1) := by
    simpa only [zero_add, div_zero, add_zero] using
      tendsto_const_nhds.add (hθ.div_atTop hlog)
  have hden : Tendsto (fun i => replicaOverlap (N i) / Real.log (N i)) L
      (nhds (1 / Real.pi)) := tendsto_overlap_div_log.comp hN
  have hratio : Tendsto (fun i => (1 + θ i / Real.log (N i)) /
      (replicaOverlap (N i) / Real.log (N i))) L (nhds Real.pi) := by
    have h := hnum.div hden (one_div_pos.mpr Real.pi_pos).ne'
    simpa only [one_div_one_div] using! h
  have heq : (fun i => criticalSigmaSq (θ i) (N i) * Real.log (N i)) =ᶠ[L]
      fun i => (1 + θ i / Real.log (N i)) /
        (replicaOverlap (N i) / Real.log (N i)) := by
    filter_upwards [hN.eventually_ge_atTop 2] with i hi
    have hlogne : Real.log (N i) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N i by omega))).ne'
    unfold criticalSigmaSq
    field_simp
  exact hratio.congr' heq.symm

/-- Uniform local renewal convergence along every moving positive-time sequence. -/
theorem tendsto_criticalRenewalMass_moving {ι : Type*} {L : Filter ι}
    {N m : ι → ℕ} {θ : ι → ℝ} {θ₀ t : ℝ}
    (hN : Tendsto N L atTop) (hθ : Tendsto θ L (nhds θ₀))
    (hm : Tendsto (fun i => (m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds t))
    (ht : 0 < t) :
    Tendsto (fun i => ((m i + 1 : ℕ) : ℝ) / Real.log (N i) *
      criticalRenewalMass (θ i) (N i) (m i + 1))
      L (nhds (t * DeltaBose.scalarDensity (θ₀ - Real.eulerMascheroniConstant) t)) := by
  let w : ι → ℕ → ℝ := fun i r => criticalSigmaSq (θ i) (N i) * returnWeight r
  let a : ι → ℕ → ℝ := fun i r => markedRenewalMass (w i) (m i - r) /
      (Real.log (N i)) ^ 2
  let e : ℕ → ℝ := fun r => ((r + 1 : ℕ) : ℝ) * returnWeight (r + 1)
  let s : ι → Finset ℕ := fun i => Finset.range (m i + 1)
  let H : ℝ := t * DeltaBose.scalarDensity (θ₀ - Real.eulerMascheroniConstant) t
  have hmTop : Tendsto m L atTop := tendsto_moving_index_atTop hN hm ht
  have hNlarge : ∀ᶠ i in L, 2 ≤ N i := hN.eventually_ge_atTop 2
  have hθlower : ∀ᶠ i in L, θ₀ - 1 < θ i :=
    hθ.eventually (eventually_gt_nhds (by linarith))
  have hσbase : ∀ᶠ i in L, 0 < criticalSigmaSq (θ₀ - 1) (N i) :=
    hN.eventually (criticalSigmaSq_eventually_pos (θ₀ - 1))
  have hσpos : ∀ᶠ i in L, 0 < criticalSigmaSq (θ i) (N i) := by
    filter_upwards [hNlarge, hθlower, hσbase] with i hi hθi hbase
    exact lt_of_lt_of_le hbase (criticalSigmaSq_mono_parameter hi hθi.le)
  have ha : ∀ᶠ i in L, ∀ r, 0 ≤ a i r := by
    filter_upwards [hNlarge, hσpos] with i hi hσ
    intro r
    apply div_nonneg
    · exact markedRenewalMass_nonneg (fun j => mul_nonneg hσ.le (srwKernel_nonneg _ _)) _
    · exact sq_nonneg _
  have hprofile := tendsto_markedProfile_moving hN hθ hm ht
  have htotal : Tendsto (fun i => ∑ r ∈ s i, a i r) L (nhds H) := by
    apply hprofile.congr'
    filter_upwards with i
    have hreflect : (∑ r ∈ Finset.range (m i + 1), markedRenewalMass (w i) (m i - r)) =
        markedRenewalFunction (w i) (m i) := by
      calc
        _ = ∑ r ∈ Finset.range (m i + 1), markedRenewalMass (w i) r := by
          simpa only [Nat.add_sub_cancel] using
            (Finset.sum_range_reflect (markedRenewalMass (w i)) (m i + 1))
        _ = _ := sum_markedRenewalMass_range (w i) (m i)
    change markedRenewalFunction (w i) (m i) / (Real.log (N i)) ^ 2 =
      ∑ r ∈ Finset.range (m i + 1),
        markedRenewalMass (w i) (m i - r) / (Real.log (N i)) ^ 2
    rw [← Finset.sum_div, hreflect]
  have hcol : ∀ r, Tendsto (fun i => a i r) L (nhds 0) := by
    intro r
    have hscale₁ := tendsto_sub_index_scale hN hm ht r
    have hscale₀ := tendsto_sub_index_scale hN hm ht (r + 1)
    have hprof₁ := tendsto_markedProfile_moving hN hθ hscale₁ ht
    have hprof₀ := tendsto_markedProfile_moving hN hθ hscale₀ ht
    have hdiff : Tendsto (fun i =>
        markedRenewalFunction (w i) (m i - r) / (Real.log (N i)) ^ 2 -
          markedRenewalFunction (w i) (m i - (r + 1)) / (Real.log (N i)) ^ 2)
        L (nhds 0) := by
      have h := hprof₁.sub hprof₀
      simpa only [sub_self] using h
    have heq : (fun i => a i r) =ᶠ[L] (fun i =>
        markedRenewalFunction (w i) (m i - r) / (Real.log (N i)) ^ 2 -
          markedRenewalFunction (w i) (m i - (r + 1)) / (Real.log (N i)) ^ 2) := by
      filter_upwards [hmTop.eventually_ge_atTop (r + 1), hNlarge] with i hir hi
      have hnat : m i - (r + 1) = (m i - r) - 1 := by omega
      have hmass : markedRenewalMass (w i) (m i - r) =
          markedRenewalFunction (w i) (m i - r) -
            markedRenewalFunction (w i) (m i - (r + 1)) := by
        rw [show m i - r = (m i - r - 1) + 1 by omega,
          markedRenewalMass_succ_eq_sub]
        congr 1
      change markedRenewalMass (w i) (m i - r) / (Real.log (N i)) ^ 2 = _
      rw [hmass]
      have hlogne : Real.log (N i) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (show 1 < N i by omega))).ne'
      field_simp [hlogne]
    exact hdiff.congr' heq.symm
  have he : Tendsto e atTop (nhds (1 / Real.pi)) := by
    have h := tendsto_returnWeight_moment.comp (tendsto_add_atTop_nat 1)
    simpa only [e, Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have hweighted := tendsto_sum_kernel_of_positive_array ha hcol htotal he
  have hσlog := tendsto_criticalSigmaSq_mul_log_moving hN hθ
  have hprod : Tendsto (fun i => criticalSigmaSq (θ i) (N i) * Real.log (N i) *
      (∑ r ∈ s i, e r * a i r)) L (nhds H) := by
    have hp := hσlog.mul hweighted
    have hcancel : Real.pi * ((1 / Real.pi) * H) = H := by field_simp
    simpa only [hcancel] using hp
  have hconv : ∀ i, ((m i + 1 : ℕ) : ℝ) *
      criticalRenewalMass (θ i) (N i) (m i + 1) =
        criticalSigmaSq (θ i) (N i) *
          ∑ r ∈ Finset.range (m i + 1), e r * markedRenewalMass (w i) (m i - r) := by
    intro i
    simp only [criticalRenewalMass, Nat.cast_add, Nat.cast_one]
    rw [mul_renewalMass_eq]
    simp_rw [renewalSquare_eq_markedRenewalMass]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [w, e]
    push_cast
    ring
  have hlogpos : ∀ᶠ i in L, 0 < Real.log (N i) := by
    filter_upwards [hNlarge] with i hi
    exact Real.log_pos (by exact_mod_cast (show 1 < N i by omega))
  have hlocal : Tendsto (fun i => ((m i + 1 : ℕ) : ℝ) / Real.log (N i) *
      criticalRenewalMass (θ i) (N i) (m i + 1)) L (nhds H) := by
    apply hprod.congr'
    filter_upwards [hNlarge, hlogpos] with i hi hlog
    have hsum : ∑ r ∈ Finset.range (m i + 1), e r * a i r =
        (∑ r ∈ Finset.range (m i + 1), e r * markedRenewalMass (w i) (m i - r)) /
          (Real.log (N i)) ^ 2 := by
      simp only [a]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hsum]
    have hiden := hconv i
    field_simp [hlog.ne']
    rw [← hiden]
  exact hlocal

/-- The natural cutoff and its successor have asymptotically the same scale. -/
theorem tendsto_nat_div_succ {ι : Type*} {L : Filter ι} {N : ι → ℕ}
    (hN : Tendsto N L atTop) :
    Tendsto (fun i => (N i : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds 1) := by
  have hden : Tendsto (fun i => ((N i + 1 : ℕ) : ℝ)) L atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hN)
  have hinv : Tendsto (fun i => (((N i + 1 : ℕ) : ℝ)⁻¹)) L (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have h0 := (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) L (nhds 1)).sub hinv
  have h : Tendsto (fun i : ι => (1 : ℝ) - (((N i + 1 : ℕ) : ℝ)⁻¹)) L (nhds 1) := by
    simpa only [sub_zero] using h0
  have heq : (fun i => (N i : ℝ) / ((N i + 1 : ℕ) : ℝ)) =ᶠ[L]
      fun i => 1 - (((N i + 1 : ℕ) : ℝ)⁻¹) := by
    filter_upwards with i
    push_cast
    field_simp
    ring
  simpa only [sub_zero] using h.congr' heq.symm

/-- Floors of a moving positive macroscopic time have the expected normalized scale. -/
theorem tendsto_floor_div_succ {ι : Type*} {L : Filter ι} {N : ι → ℕ}
    {τ : ι → ℝ} {t : ℝ} (hN : Tendsto N L atTop)
    (hτ : Tendsto τ L (nhds t)) (ht : 0 < t) :
    Tendsto (fun i => ((⌊(N i : ℝ) * τ i⌋₊ : ℕ) : ℝ) /
      ((N i + 1 : ℕ) : ℝ)) L (nhds t) := by
  have hden : Tendsto (fun i => ((N i + 1 : ℕ) : ℝ)) L atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hN)
  have hinv : Tendsto (fun i => (((N i + 1 : ℕ) : ℝ)⁻¹)) L (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hfrac := tendsto_nat_div_succ hN
  have hupper : Tendsto (fun i =>
      ((N i : ℝ) / ((N i + 1 : ℕ) : ℝ)) * τ i) L (nhds t) := by
    have h := hfrac.mul hτ
    simpa only [one_mul] using h
  have hτpos : ∀ᶠ i in L, 0 < τ i := by
    filter_upwards [hτ.eventually (eventually_gt_nhds (show t / 2 < t by linarith))]
      with i hi
    linarith
  have hlower : Tendsto (fun i =>
      ((N i : ℝ) / ((N i + 1 : ℕ) : ℝ)) * τ i -
        (((N i + 1 : ℕ) : ℝ)⁻¹)) L (nhds t) := by
    have h := hupper.sub hinv
    simpa only [sub_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards with i
    have hdenpos : 0 < ((N i + 1 : ℕ) : ℝ) := by positivity
    have hfloor : (N i : ℝ) * τ i <
        (⌊(N i : ℝ) * τ i⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
    have hdiv := div_lt_div_of_pos_right hfloor hdenpos
    have hrew : ((N i : ℝ) * τ i) / ((N i + 1 : ℕ) : ℝ) =
        ((N i : ℝ) / ((N i + 1 : ℕ) : ℝ)) * τ i := by ring
    have hsucc : (((⌊(N i : ℝ) * τ i⌋₊ : ℕ) : ℝ) + 1) /
        ((N i + 1 : ℕ) : ℝ) =
          ((⌊(N i : ℝ) * τ i⌋₊ : ℕ) : ℝ) /
            ((N i + 1 : ℕ) : ℝ) + (((N i + 1 : ℕ) : ℝ)⁻¹) := by
      field_simp
    rw [hrew, hsucc] at hdiv
    linarith
  · filter_upwards [hτpos] with i hτi
    have hdenpos : 0 < ((N i + 1 : ℕ) : ℝ) := by positivity
    have hxnonneg : 0 ≤ (N i : ℝ) * τ i := mul_nonneg (Nat.cast_nonneg _) hτi.le
    have hfloor : (⌊(N i : ℝ) * τ i⌋₊ : ℕ) ≤ (N i : ℝ) * τ i := Nat.floor_le hxnonneg
    have hdiv := div_le_div_of_nonneg_right hfloor (le_of_lt hdenpos)
    have hrew : ((N i : ℝ) * τ i) / ((N i + 1 : ℕ) : ℝ) =
        ((N i : ℝ) / ((N i + 1 : ℕ) : ℝ)) * τ i := by ring
    calc
      ((⌊(N i : ℝ) * τ i⌋₊ : ℕ) : ℝ) / ((N i + 1 : ℕ) : ℝ)
        ≤ ((N i : ℝ) * τ i) / ((N i + 1 : ℕ) : ℝ) := hdiv
      _ = ((N i : ℝ) / ((N i + 1 : ℕ) : ℝ)) * τ i := hrew

/-- The local renewal mass converges after converting its index scale to time scale. -/
theorem tendsto_criticalRenewalMass_N_moving {ι : Type*} {L : Filter ι}
    {N m : ι → ℕ} {θ : ι → ℝ} {θ₀ t : ℝ}
    (hN : Tendsto N L atTop) (hθ : Tendsto θ L (nhds θ₀))
    (hm : Tendsto (fun i => (m i : ℝ) / ((N i + 1 : ℕ) : ℝ)) L (nhds t))
    (ht : 0 < t) :
    Tendsto (fun i => (N i : ℝ) / Real.log (N i) *
      criticalRenewalMass (θ i) (N i) (m i + 1))
      L (nhds (DeltaBose.scalarDensity (θ₀ - Real.eulerMascheroniConstant) t)) := by
  have hlocal := tendsto_criticalRenewalMass_moving hN hθ hm ht
  have hden : Tendsto (fun i => ((N i + 1 : ℕ) : ℝ)) L atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hN)
  have hinv : Tendsto (fun i => (((N i + 1 : ℕ) : ℝ)⁻¹)) L (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hplus : Tendsto (fun i => ((m i + 1 : ℕ) : ℝ) /
      ((N i + 1 : ℕ) : ℝ)) L (nhds t) := by
    have h := hm.add hinv
    have heq : (fun i => (m i : ℝ) / ((N i + 1 : ℕ) : ℝ) +
        (((N i + 1 : ℕ) : ℝ)⁻¹)) =ᶠ[L]
        fun i => ((m i + 1 : ℕ) : ℝ) / ((N i + 1 : ℕ) : ℝ) := by
      filter_upwards with i
      push_cast
      ring
    simpa only [add_zero] using h.congr' heq
  have hfrac := tendsto_nat_div_succ hN
  have hratio : Tendsto (fun i => (N i : ℝ) / ((m i + 1 : ℕ) : ℝ)) L
      (nhds (1 / t)) := by
    have h := hfrac.div hplus ht.ne'
    have heq : (fun i => (N i : ℝ) / ((N i + 1 : ℕ) : ℝ) /
        (((m i + 1 : ℕ) : ℝ) / ((N i + 1 : ℕ) : ℝ))) =ᶠ[L]
        fun i => (N i : ℝ) / ((m i + 1 : ℕ) : ℝ) := by
      filter_upwards with i
      have hd : ((N i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hmpos : ((m i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    exact h.congr' heq
  have hresult := hratio.mul hlocal
  have hcancel : (1 / t) *
      (t * DeltaBose.scalarDensity (θ₀ - Real.eulerMascheroniConstant) t) =
        DeltaBose.scalarDensity (θ₀ - Real.eulerMascheroniConstant) t := by
    field_simp [ht.ne']
  have hresult' : Tendsto (fun i => (N i : ℝ) / ((m i + 1 : ℕ) : ℝ) *
      (((m i + 1 : ℕ) : ℝ) / Real.log (N i) *
        criticalRenewalMass (θ i) (N i) (m i + 1))) L
      (nhds (DeltaBose.scalarDensity (θ₀ - Real.eulerMascheroniConstant) t)) := by
    simpa only [hcancel] using hresult
  apply hresult'.congr'
  filter_upwards [hN.eventually_ge_atTop 2] with i hi
  have hmpos : ((m i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hlogne : Real.log (N i) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N i by omega))).ne'
  field_simp [hmpos, hlogne]

/-- The scalar local renewal profile on parameter and positive-time space. -/
def criticalRenewalMassProfile (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  (N : ℝ) / Real.log N * criticalRenewalMass p.1 N ⌊(N : ℝ) * p.2⌋₊

/-- Joint parameter/time convergence of the critical local renewal mass. -/
theorem tendsto_joint_criticalRenewalMassProfile {p : ℝ × ℝ} (hp : 0 < p.2) :
    Tendsto (fun z : ℕ × (ℝ × ℝ) => criticalRenewalMassProfile z.1 z.2)
      (atTop ×ˢ nhds p)
      (nhds (DeltaBose.scalarDensity (p.1 - Real.eulerMascheroniConstant) p.2)) := by
  let N : ℕ × (ℝ × ℝ) → ℕ := fun z => z.1
  let θ : ℕ × (ℝ × ℝ) → ℝ := fun z => z.2.1
  let τ : ℕ × (ℝ × ℝ) → ℝ := fun z => z.2.2
  let n : ℕ × (ℝ × ℝ) → ℕ := fun z => ⌊(z.1 : ℝ) * z.2.2⌋₊
  let m : ℕ × (ℝ × ℝ) → ℕ := fun z => n z - 1
  have hN : Tendsto N (atTop ×ˢ nhds p) atTop := by
    change Tendsto Prod.fst (atTop ×ˢ nhds p) atTop
    exact tendsto_fst
  have hparam : Tendsto (fun z : ℕ × (ℝ × ℝ) => z.2)
      (atTop ×ˢ nhds p) (nhds p) := tendsto_snd
  have hθ : Tendsto θ (atTop ×ˢ nhds p) (nhds p.1) := by
    change Tendsto (Prod.fst ∘ Prod.snd) (atTop ×ˢ nhds p) (nhds p.1)
    exact (continuous_fst.tendsto p).comp hparam
  have hτ : Tendsto τ (atTop ×ˢ nhds p) (nhds p.2) := by
    change Tendsto (Prod.snd ∘ Prod.snd) (atTop ×ˢ nhds p) (nhds p.2)
    exact (continuous_snd.tendsto p).comp hparam
  have hnscale : Tendsto (fun z => (n z : ℝ) / ((N z + 1 : ℕ) : ℝ))
      (atTop ×ˢ nhds p) (nhds p.2) := by
    change Tendsto (fun z => ((⌊(N z : ℝ) * τ z⌋₊ : ℕ) : ℝ) /
      ((N z + 1 : ℕ) : ℝ)) (atTop ×ˢ nhds p) (nhds p.2)
    exact tendsto_floor_div_succ hN hτ hp
  have hmscale := tendsto_sub_index_scale hN hnscale hp 1
  have hlocal := tendsto_criticalRenewalMass_N_moving hN hθ hmscale hp
  have hmTop := tendsto_moving_index_atTop hN hnscale hp
  have heq : (fun z : ℕ × (ℝ × ℝ) => (N z : ℝ) / Real.log (N z) *
      criticalRenewalMass (θ z) (N z) (m z + 1)) =ᶠ[atTop ×ˢ nhds p]
      fun z => criticalRenewalMassProfile (N z) (θ z, τ z) := by
    filter_upwards [hmTop.eventually_ge_atTop 1] with z hz
    simp only [m, n, Nat.sub_add_cancel hz, criticalRenewalMassProfile, N, θ, τ]
  simpa only [N, θ, τ] using hlocal.congr' heq

/-- Joint continuity of the limiting scalar renewal density. -/
theorem continuousAt_shiftedScalarDensity {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ =>
      DeltaBose.scalarDensity (q.1 - Real.eulerMascheroniConstant) q.2) p := by
  have hc : ContinuousAt (fun q : ℝ × ℝ => DeltaBose.scalarDensity q.1 q.2)
      (p.1 - Real.eulerMascheroniConstant, p.2) :=
    DeltaBose.continuousOn_scalarDensity.continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds
        (show (0 : ℝ) < (p.1 - Real.eulerMascheroniConstant, p.2).2 from hp))
  exact hc.comp₂ (continuous_fst.sub continuous_const).continuousAt continuous_snd.continuousAt

/-- The scalar local renewal limit holds locally uniformly on positive-time space. -/
theorem tendstoLocallyUniformlyOn_criticalRenewalMassProfile :
    TendstoLocallyUniformlyOn criticalRenewalMassProfile
      (fun p : ℝ × ℝ => DeltaBose.scalarDensity
        (p.1 - Real.eulerMascheroniConstant) p.2)
      atTop {p | 0 < p.2} := by
  apply (isOpen_lt continuous_const continuous_snd).tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro p hp
  have htarget := (continuousAt_shiftedScalarDensity hp).tendsto.comp
    (tendsto_snd : Tendsto (Prod.snd : ℕ × (ℝ × ℝ) → ℝ × ℝ)
      (atTop ×ˢ nhds p) (nhds p))
  exact (htarget.prodMk_nhds (tendsto_joint_criticalRenewalMassProfile hp)).mono_right
    (nhds_le_uniformity _)

/-- Uniform scalar local renewal convergence on compact positive-time sets. -/
theorem tendstoUniformlyOn_criticalRenewalMassProfile {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < p.2) :
    TendstoUniformlyOn criticalRenewalMassProfile
      (fun p : ℝ × ℝ => DeltaBose.scalarDensity
        (p.1 - Real.eulerMascheroniConstant) p.2) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (tendstoLocallyUniformlyOn_criticalRenewalMassProfile.mono hpos)

/-- The local renewal profiles converge uniformly on compact parameter intervals and times in `[δ,1]`. -/
theorem tendstoUniformlyOn_criticalRenewalMassProfile_box {a b δ : ℝ}
    (hδ : 0 < δ) :
    TendstoUniformlyOn criticalRenewalMassProfile
      (fun p : ℝ × ℝ => DeltaBose.scalarDensity
        (p.1 - Real.eulerMascheroniConstant) p.2) atTop
      (Set.Icc a b ×ˢ Set.Icc δ 1) := by
  apply tendstoUniformlyOn_criticalRenewalMassProfile
  · exact isCompact_Icc.prod isCompact_Icc
  · intro p hp
    exact hδ.trans_le hp.2.1

end Critical2DKPZ.Renewal

end
