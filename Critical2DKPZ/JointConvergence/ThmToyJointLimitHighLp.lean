/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.ThmToyJointLimitEstimates
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! # Lp limits identified by convergence in measure -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped ENNReal Topology

namespace Critical2DKPZ.JointConvergence

set_option linter.style.haveILetI false in
private theorem lp_representatives_cauchy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (f : ℕ → Ω → ℝ)
    (hmem : ∀ n, MemLp (f n) q P)
    (hsummable : Summable (fun n => ENNReal.toReal
      (eLpNorm (fun ω => f n ω - f n.succ ω) q P))) :
    CauchySeq (fun n : ℕ => (hmem n).toLp (f n)) := by
  let fLp : ℕ → Lp ℝ q P := fun n => (hmem n).toLp (f n)
  have hdist (n : ℕ) : dist (fLp n) (fLp n.succ) ≤
      ENNReal.toReal (eLpNorm (fun ω => f n ω - f n.succ ω) q P) := by
    rw [Lp.dist_def]
    have hEq : eLpNorm (⇑(fLp n) - ⇑(fLp n.succ)) q P =
        eLpNorm (fun ω => f n ω - f n.succ ω) q P := by
      apply eLpNorm_congr_ae
      filter_upwards [(hmem n).coeFn_toLp, (hmem n.succ).coeFn_toLp] with ω hω hω'
      change ((fLp n : Ω → ℝ) ω - (fLp n.succ : Ω → ℝ) ω) = f n ω - f n.succ ω
      rw [hω, hω']
    exact le_of_eq (congrArg ENNReal.toReal hEq)
  exact cauchySeq_of_dist_le_of_summable _ hdist hsummable

private theorem lp_representatives_have_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (f : ℕ → Ω → ℝ)
    (hmem : ∀ n, MemLp (f n) q P)
    (hsummable : Summable (fun n => ENNReal.toReal
      (eLpNorm (fun ω => f n ω - f n.succ ω) q P))) :
    ∃ g : Lp ℝ q P, Tendsto
      (fun n : ℕ => (hmem n).toLp (f n)) atTop (𝓝 g) := by
  exact cauchySeq_tendsto_of_complete (lp_representatives_cauchy P f hmem hsummable)

private theorem lp_tendstoInMeasure_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : ℕ → Lp ℝ q P} {g : Lp ℝ q P}
    (h : Tendsto f atTop (𝓝 g)) :
    TendstoInMeasure P (fun n => f n) atTop g :=
  tendstoInMeasure_of_tendsto_Lp h

private theorem ae_eq_of_measure_limits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f : ℕ → Ω → ℝ} {X g₀ : Ω → ℝ}
    (hf : TendstoInMeasure P f atTop X)
    (hg : TendstoInMeasure P f atTop g₀) :
    X =ᵐ[P] g₀ := by
  exact tendstoInMeasure_ae_unique hf hg

private theorem memLp_of_ae_eq_lp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {q : ℝ≥0∞} {X : Ω → ℝ} {g : Lp ℝ q P}
    (hEq : X =ᵐ[P] g) : MemLp X q P := by
  rw [memLp_iff, eLpNorm_congr_ae hEq]
  exact Lp.memLp g

set_option linter.style.haveILetI false in
/-- A summable sequence of successive `Lp` differences gives an `Lp` limit. If the same
representatives converge in measure to `X`, uniqueness in measure identifies `X` as an `Lp`
function. -/
theorem memLp_limit_of_summable_eLpNorm_differences
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hmem : ∀ n, MemLp (f n) q P)
    (hsummable : Summable (fun n => ENNReal.toReal
      (eLpNorm (fun ω => f n ω - f n.succ ω) q P)))
    (hconv : TendstoInMeasure P f atTop X) :
    MemLp X q P := by
  letI : Fact (1 ≤ q) := ⟨hq⟩
  let fLp : ℕ → Lp ℝ q P := fun n => (hmem n).toLp (f n)
  obtain ⟨g, hg⟩ := lp_representatives_have_limit P f hmem hsummable
  have hgMeasure := lp_tendstoInMeasure_of_tendsto P hg
  have hfMeasure : TendstoInMeasure P (fun n => fLp n) atTop X :=
    TendstoInMeasure.congr_left (fun n => (hmem n).coeFn_toLp.symm) hconv
  exact memLp_of_ae_eq_lp P (ae_eq_of_measure_limits P hfMeasure hgMeasure)

private theorem eLpNorm_interpolate_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q A B : ℝ} (hq : 2 < q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Ω → ℝ)
    (h2 : eLpNorm f 2 P ≤ ENNReal.ofReal A)
    (h2q : eLpNorm f (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal B) :
    eLpNorm f (ENNReal.ofReal q) P ≤ ENNReal.ofReal
      ((A ^ (1 / (q - 1))) * (B ^ ((q - 2) / (q - 1)))) := by
  let α : ℝ := 1 / (q - 1)
  let β : ℝ := (q - 2) / (q - 1)
  have hα : 0 < α := by dsimp [α]; exact div_pos zero_lt_one (by linarith)
  have hβ : 0 < β := by dsimp [β]; exact div_pos (by linarith) (by linarith)
  have hαle : α ≤ 1 := by dsimp [α]; rw [div_le_one (by linarith)]; linarith
  have hβle : β ≤ 1 := by dsimp [β]; rw [div_le_one (by linarith)]; linarith
  have hinterp := eLpNorm_interpolate_two_to_two_mul P hq f
  calc
    eLpNorm f (ENNReal.ofReal q) P ≤
        eLpNorm f 2 P ^ α * eLpNorm f (ENNReal.ofReal (2 * q)) P ^ β := by
          simpa [α, β, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using hinterp
    _ ≤ ENNReal.ofReal A ^ α * ENNReal.ofReal B ^ β :=
          mul_le_mul (ENNReal.rpow_le_rpow h2 hα.le)
            (ENNReal.rpow_le_rpow h2q hβ.le) (by positivity) (by positivity)
    _ = ENNReal.ofReal (A ^ α * B ^ β) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hA hα.le,
            ENNReal.ofReal_rpow_of_nonneg hB hβ.le,
            ← ENNReal.ofReal_mul (by positivity)]

set_option linter.style.haveILetI false in
/-- Logarithmic moment growth, together with a logarithmic L² rate, gives a logarithmic bound in
the higher `Lᵖ` norm. The bound holds uniformly for sufficiently small regularization widths. -/
theorem highLp_difference_log_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (X : Ω → ℝ) (c d C q : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hq : 2 < q)
    (hRate : ∀ δ ∈ Set.Ioo 0 d,
      eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤
        ENNReal.ofReal (C * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)))
    (hMoment : ∃ M : ℝ, 0 ≤ M ∧ ∀ δ ∈ Set.Ioo 0 d,
      AEStronglyMeasurable (Y δ) P ∧
      Integrable (fun ω => |Y δ ω| ^ (2 * q)) P ∧
      ∫ ω, |Y δ ω| ^ (2 * q) ∂P ≤
        M * (1 + Real.log (1 + |Real.log δ|)) ^ (2 * q))
    (hconvSeq : TendstoInMeasure P
      (fun n : ℕ => Y (c * Real.exp (-Real.exp (n : ℝ)))) atTop X) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ δ ∈ Set.Ioo 0 d,
      eLpNorm (fun ω => Y δ ω - X ω) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (Cp * (1 + Real.log (1 + |Real.log δ|))) := by
  classical
  let δseq : ℕ → ℝ := fun n => c * Real.exp (-Real.exp (n : ℝ))
  have hδseq : Tendsto δseq atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hexp := Real.tendsto_exp_atTop.comp hn
    have hsmall := Real.tendsto_exp_neg_atTop_nhds_zero.comp hexp
    simpa [δseq] using hsmall.const_mul c
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hδseq.eventually (Iio_mem_nhds hd))
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n N) tendsto_id
  let f : ℕ → Ω → ℝ :=
    (fun k : ℕ => Y (c * Real.exp (-Real.exp (k : ℝ)))) ∘ (fun n : ℕ => n + N)
  have hfconv : TendstoInMeasure P f atTop X := by
    exact hconvSeq.comp hshift
  obtain ⟨M, hM, hMoment⟩ := hMoment
  let B : ℝ → ℝ := fun δ => 1 + Real.log (1 + |Real.log δ|)
  let D0 : ℝ := 1 + (N : ℝ) + Real.log (2 + |Real.log c|)
  have hD0 : 1 ≤ D0 := by
    dsimp [D0]
    have hlog : 0 ≤ Real.log (2 + |Real.log c|) :=
      Real.log_nonneg (by have := abs_nonneg (Real.log c); linarith)
    have hN' : 0 ≤ (N : ℝ) := by positivity
    linarith
  have hwidth (n : ℕ) : B (δseq (n + N)) ≤ D0 * ((n : ℝ) + 1) := by
    let m : ℝ := ((n + N : ℕ) : ℝ)
    have hm : 0 ≤ m := by dsimp [m]; positivity
    have hE : 1 ≤ Real.exp m := by nlinarith [Real.add_one_le_exp m]
    have hlogδ : Real.log (δseq (n + N)) = Real.log c - Real.exp m := by
      dsimp [δseq, m]
      rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    have hlogAbs : |Real.log (δseq (n + N))| ≤ |Real.log c| + Real.exp m := by
      rw [hlogδ]
      simpa using abs_sub (Real.log c) (Real.exp m)
    have harg : 1 + |Real.log (δseq (n + N))| ≤
        (2 + |Real.log c|) * Real.exp m := by
      have hlogc : 0 ≤ |Real.log c| := abs_nonneg _
      nlinarith [hlogAbs, hE]
    have hlogWidth : Real.log (1 + |Real.log (δseq (n + N))|) ≤
        Real.log (2 + |Real.log c|) + m := by
      calc
        Real.log (1 + |Real.log (δseq (n + N))|) ≤
            Real.log ((2 + |Real.log c|) * Real.exp m) :=
          Real.log_le_log (by positivity) harg
        _ = Real.log (2 + |Real.log c|) + m := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have hcast : m = (n : ℝ) + (N : ℝ) := by
      dsimp [m]
      exact_mod_cast Nat.cast_add n N
    have hbase : B (δseq (n + N)) ≤ D0 + (n : ℝ) := by
      dsimp [B]
      calc
        1 + Real.log (1 + |Real.log (δseq (n + N))|) ≤
            1 + (Real.log (2 + |Real.log c|) + m) := by
              exact add_le_add le_rfl hlogWidth
        _ = D0 + (n : ℝ) := by rw [hcast]; dsimp [D0]; ring
    have hn : 0 ≤ (n : ℝ) := by positivity
    calc
      B (δseq (n + N)) ≤ D0 + (n : ℝ) := hbase
      _ ≤ D0 * ((n : ℝ) + 1) := by
        have hmul := mul_le_mul_of_nonneg_right hD0 hn
        calc
          D0 + (n : ℝ) = D0 + 1 * (n : ℝ) := by ring
          _ ≤ D0 + D0 * (n : ℝ) := add_le_add le_rfl (by simpa only [one_mul] using hmul)
          _ = D0 * ((n : ℝ) + 1) := by ring
  have hBpos (δ : ℝ) : 0 ≤ B δ := by
    dsimp [B]
    have hlog : 0 ≤ Real.log (1 + |Real.log δ|) :=
      Real.log_nonneg (by have := abs_nonneg (Real.log δ); linarith)
    linarith
  let M0 : ℝ := max M 1
  let K : ℝ := M0 ^ (1 / (2 * q))
  have hM0 : 0 < M0 := by dsimp [M0]; positivity
  have hK : 0 < K := by dsimp [K]; exact Real.rpow_pos_of_pos hM0 _
  have hqENN : 1 ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ q)
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨hqENN⟩
  have hraw (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 d) :
      eLpNorm (Y δ) (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal (K * B δ) := by
    obtain ⟨hsm, hint, hbound⟩ := hMoment δ hδ
    have hB : 0 ≤ B δ := by
      dsimp [B]
      have hlog : 0 ≤ Real.log (1 + |Real.log δ|) :=
        Real.log_nonneg (by have := abs_nonneg (Real.log δ); linarith)
      linarith
    have hbound' : ∫ ω, |Y δ ω| ^ (2 * q) ∂P ≤ M0 * B δ ^ (2 * q) := by
      calc
        ∫ ω, |Y δ ω| ^ (2 * q) ∂P ≤ M * B δ ^ (2 * q) := by simpa [B] using hbound
        _ ≤ M0 * B δ ^ (2 * q) :=
          mul_le_mul_of_nonneg_right (le_max_left M 1) (Real.rpow_nonneg hB _)
    have hnorm := eLpNorm_le_of_integral_abs_rpow_bound
      (by linarith : 0 < 2 * q) hM0.le hB hsm hint hbound'
    have hroot : (M0 * B δ ^ (2 * q)) ^ (1 / (2 * q)) ≤ K * B δ := by
      have hBpow : 0 ≤ B δ ^ (2 * q) := Real.rpow_nonneg hB _
      have hBr : (B δ ^ (2 * q)) ^ (1 / (2 * q)) = B δ := by
        rw [show (1 : ℝ) / (2 * q) = (2 * q)⁻¹ by field_simp]
        exact Real.rpow_rpow_inv hB (by positivity : (2 * q : ℝ) ≠ 0)
      have hsplit : (M0 * B δ ^ (2 * q)) ^ (1 / (2 * q)) = K * B δ := by
        rw [Real.mul_rpow hM0.le hBpow, hBr]
      exact hsplit.le
    exact hnorm.trans (ENNReal.ofReal_le_ofReal hroot)
  have hmem (n : ℕ) : MemLp (f n) (ENNReal.ofReal q) P := by
    have hnδ : δseq (n + N) ∈ Set.Ioo 0 d := by
      constructor
      · dsimp [δseq]
        exact mul_pos hc (Real.exp_pos _)
      · exact hN (n + N) (Nat.le_add_left N n)
    have hraw' : eLpNorm (f n) (ENNReal.ofReal (2 * q)) P ≤
        ENNReal.ofReal (K * B (δseq (n + N))) := by
      simpa [f, Function.comp_def, δseq] using hraw (δseq (n + N)) hnδ
    rw [memLp_iff]
    have hqle : ENNReal.ofReal q ≤ ENNReal.ofReal (2 * q) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    exact lt_of_le_of_lt
      ((eLpNorm_le_eLpNorm_of_exponent_le hqle).trans hraw')
      ENNReal.ofReal_lt_top
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := by dsimp [C0]; exact le_max_right _ _
  have hC0C : C ≤ C0 := by dsimp [C0]; exact le_max_left _ _
  let α : ℝ := 1 / (q - 1)
  let β : ℝ := (q - 2) / (q - 1)
  have hα : 0 < α := by dsimp [α]; exact div_pos zero_lt_one (by linarith)
  have hβ : 0 < β := by dsimp [β]; exact div_pos (by linarith) (by linarith)
  have hβle : β ≤ 1 := by
    dsimp [β]
    rw [div_le_one (by linarith)]
    linarith
  have hL2 (n : ℕ) : eLpNorm (fun ω => f n ω - X ω) 2 P ≤
      ENNReal.ofReal (2 * C0 * Real.exp (-(n : ℝ) / 40)) := by
    have hnδ : δseq (n + N) ∈ Set.Ioo 0 d := by
      constructor
      · dsimp [δseq]
        exact mul_pos hc (Real.exp_pos _)
      · exact hN (n + N) (Nat.le_add_left N n)
    have hlog (m : ℕ) : Real.log (δseq m / c) = -Real.exp (m : ℝ) := by
      have hcancel : δseq m / c = Real.exp (-Real.exp (m : ℝ)) := by
        dsimp [δseq]
        field_simp [hc.ne']
      rw [hcancel, Real.log_exp]
    have habs (m : ℕ) : |Real.log (δseq m / c)| = Real.exp (m : ℝ) := by
      rw [hlog]
      rw [abs_of_neg (neg_lt_zero.mpr (Real.exp_pos (m : ℝ))), neg_neg]
    have hpow (m : ℕ) : |Real.log (δseq m / c)| ^ (-(1 : ℝ) / 40) =
        Real.exp (-(m : ℝ) / 40) := by
      rw [habs]
      rw [Real.rpow_def_of_pos (Real.exp_pos (m : ℝ)), Real.log_exp]
      congr 1
      ring
    have hrate := hRate (δseq (n + N)) hnδ
    have hcoef : C * |Real.log (δseq (n + N) / c)| ^ (-(1 : ℝ) / 40) ≤
        C0 * |Real.log (δseq (n + N) / c)| ^ (-(1 : ℝ) / 40) :=
      mul_le_mul_of_nonneg_right hC0C (Real.rpow_nonneg (abs_nonneg _) _)
    have hcast : ((n + N : ℕ) : ℝ) = (n : ℝ) + N := by
      exact_mod_cast Nat.cast_add n N
    have hexp : Real.exp (-((n + N : ℕ) : ℝ) / 40) ≤
        Real.exp (-(n : ℝ) / 40) := by
      apply Real.exp_le_exp.mpr
      rw [hcast]
      have hNnonneg : 0 ≤ (N : ℝ) := by positivity
      linarith
    have hfinal : C * |Real.log (δseq (n + N) / c)| ^ (-(1 : ℝ) / 40) ≤
        2 * C0 * Real.exp (-(n : ℝ) / 40) := by
      calc
        _ ≤ C0 * Real.exp (-((n + N : ℕ) : ℝ) / 40) := by
          simpa [hpow] using hcoef
        _ ≤ C0 * Real.exp (-(n : ℝ) / 40) :=
          mul_le_mul_of_nonneg_left hexp hC0
        _ ≤ 2 * C0 * Real.exp (-(n : ℝ) / 40) := by
          nlinarith [mul_nonneg hC0 (Real.exp_pos (-(n : ℝ) / 40)).le]
    exact hrate.trans (ENNReal.ofReal_le_ofReal hfinal)
  have hstep2 (n : ℕ) : eLpNorm (fun ω => f n ω - f n.succ ω) 2 P ≤
      ENNReal.ofReal (2 * C0 * Real.exp (-(n : ℝ) / 40) +
        2 * C0 * Real.exp (-((n.succ : ℕ) : ℝ) / 40)) := by
    calc
      eLpNorm (fun ω => f n ω - f n.succ ω) 2 P =
          eLpNorm (fun ω => (f n ω - X ω) - (f n.succ ω - X ω)) 2 P := by
            congr 1
            funext ω
            ring
      _ ≤ eLpNorm (fun ω => f n ω - X ω) 2 P +
          eLpNorm (fun ω => f n.succ ω - X ω) 2 P := eLpNorm_sub_le (by norm_num)
      _ ≤ ENNReal.ofReal (2 * C0 * Real.exp (-(n : ℝ) / 40)) +
          ENNReal.ofReal (2 * C0 * Real.exp (-((n.succ : ℕ) : ℝ) / 40)) :=
        add_le_add (hL2 n) (hL2 n.succ)
      _ = _ := by
        exact (ENNReal.ofReal_add
          (p := 2 * C0 * Real.exp (-(n : ℝ) / 40))
          (q := 2 * C0 * Real.exp (-((n.succ : ℕ) : ℝ) / 40))
          (by positivity) (by positivity)).symm
  have hstep2' (n : ℕ) : eLpNorm (fun ω => f n ω - f n.succ ω) 2 P ≤
      ENNReal.ofReal (4 * C0 * Real.exp (-(n : ℝ) / 40)) := by
    have hmon : Real.exp (-((n.succ : ℕ) : ℝ) / 40) ≤ Real.exp (-(n : ℝ) / 40) := by
      apply Real.exp_le_exp.mpr
      have hcast : ((n.succ : ℕ) : ℝ) = (n : ℝ) + 1 := by
        exact_mod_cast Nat.cast_succ n
      rw [hcast]
      nlinarith
    have hreal : 2 * C0 * Real.exp (-(n : ℝ) / 40) +
        2 * C0 * Real.exp (-((n.succ : ℕ) : ℝ) / 40) ≤
        4 * C0 * Real.exp (-(n : ℝ) / 40) := by
      have hmul := mul_le_mul_of_nonneg_left hmon (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0)
      nlinarith
    exact (hstep2 n).trans (ENNReal.ofReal_le_ofReal hreal)
  have hstepHigh (n : ℕ) : eLpNorm (fun ω => f n ω - f n.succ ω)
      (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal (3 * K * D0 * ((n : ℝ) + 1)) := by
    have hnδ : δseq (n + N) ∈ Set.Ioo 0 d := by
      constructor
      · dsimp [δseq]
        exact mul_pos hc (Real.exp_pos _)
      · exact hN (n + N) (Nat.le_add_left N n)
    have hsδ : δseq (n.succ + N) ∈ Set.Ioo 0 d := by
      constructor
      · dsimp [δseq]
        exact mul_pos hc (Real.exp_pos _)
      · exact hN (n.succ + N) (by omega)
    have htriangle : eLpNorm (fun ω => f n ω - f n.succ ω) (ENNReal.ofReal (2 * q)) P ≤
        eLpNorm (f n) (ENNReal.ofReal (2 * q)) P +
        eLpNorm (f n.succ) (ENNReal.ofReal (2 * q)) P := by
      have h2q : 1 ≤ ENNReal.ofReal (2 * q) :=
        by simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 2 * q)
      exact eLpNorm_sub_le h2q
    have hrawn : eLpNorm (f n) (ENNReal.ofReal (2 * q)) P ≤
        ENNReal.ofReal (K * B (δseq (n + N))) := by
      simpa [f, Function.comp_def, δseq] using hraw (δseq (n + N)) hnδ
    have hraws : eLpNorm (f n.succ) (ENNReal.ofReal (2 * q)) P ≤
        ENNReal.ofReal (K * B (δseq (n.succ + N))) := by
      change eLpNorm (Y (δseq (n.succ + N))) (ENNReal.ofReal (2 * q)) P ≤ _
      exact hraw (δseq (n.succ + N)) hsδ
    have hnwidth : B (δseq (n + N)) ≤ D0 * ((n : ℝ) + 1) := hwidth n
    have hswidth : B (δseq (n.succ + N)) ≤ D0 * ((n : ℝ) + 2) := by
      calc
        _ ≤ D0 * (((n.succ : ℕ) : ℝ) + 1) := hwidth n.succ
        _ = D0 * ((n : ℝ) + 2) := by push_cast; ring
    have hswidth' : B (δseq (n.succ + N)) ≤ D0 * (2 * ((n : ℝ) + 1)) := by
      calc
        _ ≤ D0 * ((n : ℝ) + 2) := hswidth
        _ ≤ D0 * (2 * ((n : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ D0)
          nlinarith
    have hsum : K * B (δseq (n + N)) + K * B (δseq (n.succ + N)) ≤
        3 * K * D0 * ((n : ℝ) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hnwidth hK.le,
        mul_le_mul_of_nonneg_left hswidth' hK.le]
    calc
      _ ≤ eLpNorm (f n) (ENNReal.ofReal (2 * q)) P +
          eLpNorm (f n.succ) (ENNReal.ofReal (2 * q)) P := htriangle
      _ ≤ _ := add_le_add hrawn hraws
      _ ≤ ENNReal.ofReal (K * B (δseq (n + N)) + K * B (δseq (n.succ + N))) := by
        rw [← ENNReal.ofReal_add
          (mul_nonneg hK.le (hBpos _))
          (mul_nonneg hK.le (hBpos _))]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
  let r : ℝ := Real.exp (-α / 40)
  let D : ℝ := (4 * C0) ^ α * (3 * K * D0) ^ β
  have hr0 : 0 < r := by dsimp [r]; exact Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith [hα]) (by norm_num)
  have hgeom : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
    have hpoly : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (by
        rw [Real.norm_of_nonneg hr0.le]
        exact hr1)
    have hbase : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0.le hr1
    convert hpoly.add hbase using 1
    · ext n
      simp [add_mul]
  have hInterpStep (n : ℕ) : eLpNorm (fun ω => f n ω - f n.succ ω)
      (ENNReal.ofReal q) P ≤ ENNReal.ofReal (D * ((n : ℝ) + 1) * r ^ n) := by
    let A : ℝ := 4 * C0 * Real.exp (-(n : ℝ) / 40)
    let Bn : ℝ := 3 * K * D0 * ((n : ℝ) + 1)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hBn : 0 ≤ Bn := by dsimp [Bn]; positivity
    have hInterp := eLpNorm_interpolate_bound P hq hA hBn
      (fun ω => f n ω - f n.succ ω) (hstep2' n) (hstepHigh n)
    have hExpR : (Real.exp (-(n : ℝ) / 40)) ^ α = r ^ n := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hAα : A ^ α = (4 * C0) ^ α * r ^ n := by
      dsimp [A]
      rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, hExpR]
    have hBnβ : Bn ^ β ≤ (3 * K * D0) ^ β * ((n : ℝ) + 1) := by
      dsimp [Bn]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc
        (3 * K * D0) ^ β * ((n : ℝ) + 1) ^ β ≤
            (3 * K * D0) ^ β * ((n : ℝ) + 1) ^ (1 : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
              apply Real.rpow_le_rpow_of_exponent_le
                (by nlinarith : (1 : ℝ) ≤ (n : ℝ) + 1) hβle
        _ = (3 * K * D0) ^ β * ((n : ℝ) + 1) := by rw [Real.rpow_one]
    calc
      _ ≤ ENNReal.ofReal (A ^ α * Bn ^ β) := hInterp
      _ ≤ ENNReal.ofReal ((4 * C0) ^ α * r ^ n *
          ((3 * K * D0) ^ β * ((n : ℝ) + 1))) := by
          apply ENNReal.ofReal_le_ofReal
          calc
            A ^ α * Bn ^ β ≤ A ^ α * ((3 * K * D0) ^ β * ((n : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hBnβ (Real.rpow_nonneg hA _)
            _ = (4 * C0) ^ α * r ^ n * ((3 * K * D0) ^ β * ((n : ℝ) + 1)) := by
              rw [hAα]
      _ = ENNReal.ofReal (D * ((n : ℝ) + 1) * r ^ n) := by
          congr 1
          dsimp [D]
          ring
  have hsummable : Summable (fun n : ℕ => ENNReal.toReal
      (eLpNorm (fun ω => f n ω - f n.succ ω) (ENNReal.ofReal q) P)) := by
    have hle (n : ℕ) : ENNReal.toReal
        (eLpNorm (fun ω => f n ω - f n.succ ω) (ENNReal.ofReal q) P) ≤
        D * ((n : ℝ) + 1) * r ^ n := by
      have hfinite : ENNReal.ofReal (D * ((n : ℝ) + 1) * r ^ n) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      have hto := ENNReal.toReal_mono hfinite (hInterpStep n)
      calc
        _ ≤ ENNReal.toReal (ENNReal.ofReal (D * ((n : ℝ) + 1) * r ^ n)) := hto
        _ = D * ((n : ℝ) + 1) * r ^ n :=
          ENNReal.toReal_ofReal (by positivity)
    have hnonneg (n : ℕ) : 0 ≤ ENNReal.toReal
        (eLpNorm (fun ω => f n ω - f n.succ ω) (ENNReal.ofReal q) P) := by positivity
    have hmajor : Summable (fun n : ℕ => D * ((n : ℝ) + 1) * r ^ n) := by
      simpa [mul_assoc] using hgeom.mul_left D
    exact hmajor.of_nonneg_of_le hnonneg hle
  have hXq : MemLp X (ENNReal.ofReal q) P :=
    memLp_limit_of_summable_eLpNorm_differences P hqENN f X hmem hsummable hfconv
  have hXfinite : eLpNorm X (ENNReal.ofReal q) P < ⊤ := hXq.eLpNorm_lt_top
  let DX : ℝ := ENNReal.toReal (eLpNorm X (ENNReal.ofReal q) P)
  have hDX : 0 ≤ DX := by dsimp [DX]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDXeq : ENNReal.ofReal DX = eLpNorm X (ENNReal.ofReal q) P := by
    dsimp [DX]
    exact ENNReal.ofReal_toReal (ne_of_lt hXfinite)
  have hBge (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 d) : 1 ≤ B δ := by
    dsimp [B]
    have hlog : 0 ≤ Real.log (1 + |Real.log δ|) :=
      Real.log_nonneg (by have := abs_nonneg (Real.log δ); linarith)
    linarith
  have hqY (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 d) :
      eLpNorm (Y δ) (ENNReal.ofReal q) P ≤ ENNReal.ofReal (K * B δ) := by
    have hqle : ENNReal.ofReal q ≤ ENNReal.ofReal (2 * q) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    exact (eLpNorm_le_eLpNorm_of_exponent_le hqle).trans (hraw δ hδ)
  refine ⟨K + DX, by positivity, ?_⟩
  intro δ hδ
  calc
    eLpNorm (fun ω => Y δ ω - X ω) (ENNReal.ofReal q) P ≤
        eLpNorm (Y δ) (ENNReal.ofReal q) P + eLpNorm X (ENNReal.ofReal q) P :=
      eLpNorm_sub_le hqENN
    _ ≤ ENNReal.ofReal (K * B δ) + ENNReal.ofReal DX :=
      add_le_add (hqY δ hδ) (le_of_eq hDXeq.symm)
    _ = ENNReal.ofReal (K * B δ + DX) := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg hK.le (le_trans (by norm_num) (hBge δ hδ))) hDX]
    _ ≤ ENNReal.ofReal ((K + DX) * B δ) := by
      apply ENNReal.ofReal_le_ofReal
      have := hBge δ hδ
      nlinarith [mul_nonneg hDX (sub_nonneg.mpr this)]

end Critical2DKPZ.JointConvergence

end
