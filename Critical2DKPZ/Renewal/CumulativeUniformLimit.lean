/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CumulativeLimit
public import Critical2DKPZ.Renewal.MonotoneUniform
public import Critical2DKPZ.Renewal.LocalLimit
public import Critical2DKPZ.Definitions.EvenCeil
import Critical2DKPZ.SHF.Moments.TimeRounding

/-! # Locally uniform cumulative renewal convergence

Monotonicity in time gives joint convergence as the lattice scale grows and the positive
macroscopic time varies, including horizons rounded up to an even integer. -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The cumulative critical renewal function at a macroscopic time. -/
def criticalRenewalFunctionProfile (ϑ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  criticalRenewalFunction ϑ N ⌊((N : ℝ) + 1) * t⌋₊ / Real.log N

/-- Joint cutoff/time convergence of the cumulative critical renewal function. -/
theorem tendsto_joint_criticalRenewalFunctionProfile (ϑ : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun z : ℕ × ℝ => criticalRenewalFunctionProfile ϑ z.1 z.2)
      (atTop ×ˢ nhds t)
      (nhds (scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant) t)) := by
  let F : ℕ → ℝ × ℝ → ℝ := fun N p => criticalRenewalFunctionProfile ϑ N p.2
  let f : ℝ × ℝ → ℝ := fun p => scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant) p.2
  let K : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc (t / 2) (t + 1)
  have hK : K ∈ nhds (0, t) := by
    rw [nhds_prod_eq]
    exact Filter.mem_prod_iff.mpr ⟨_, Icc_mem_nhds (by norm_num) (by norm_num),
      _, Icc_mem_nhds (by linarith) (by linarith), fun _ h => h⟩
  have hmono : ∀ᶠ N : ℕ in atTop, MonotoneOn (F N) K := by
    filter_upwards [criticalSigmaSq_eventually_pos ϑ, eventually_ge_atTop 2] with N hσ hN
    intro x hx y hy hxy
    have hw : ∀ r, 0 ≤ criticalSigmaSq ϑ N * returnWeight r := fun r =>
      mul_nonneg hσ.le (srwKernel_nonneg _ _)
    have hfloor : ⌊((N : ℝ) + 1) * x.2⌋₊ ≤ ⌊((N : ℝ) + 1) * y.2⌋₊ :=
      Nat.floor_mono (mul_le_mul_of_nonneg_left hxy.2 (by positivity))
    have htime : criticalRenewalFunction ϑ N ⌊((N : ℝ) + 1) * x.2⌋₊ ≤
        criticalRenewalFunction ϑ N ⌊((N : ℝ) + 1) * y.2⌋₊ := by
      change renewalFunction (fun r => criticalSigmaSq ϑ N * returnWeight r)
          ⌊((N : ℝ) + 1) * x.2⌋₊ ≤
        renewalFunction (fun r => criticalSigmaSq ϑ N * returnWeight r)
          ⌊((N : ℝ) + 1) * y.2⌋₊
      exact renewalFunction_mono_time hw hfloor
    have hlog : 0 < Real.log N :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact div_le_div_of_nonneg_right htime hlog.le
  have hlim : ∀ q ∈ K, Tendsto (fun N => F N q) atTop (nhds (f q)) := by
    intro q hq
    exact tendsto_criticalRenewalFunction ϑ ((half_pos ht).trans_le hq.2.1)
  have hf0 : ContinuousAt (scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant)) t :=
    continuousAt_scalarRenewalPrimitive _ ht
  have hf : ContinuousAt f (0, t) := by
    change ContinuousAt (fun p : ℝ × ℝ =>
      scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant) p.2) (0, t)
    exact hf0.comp_of_eq continuous_snd.continuousAt (by rfl)
  have hjoint := tendsto_joint_of_eventually_monotone hK hmono hlim hf
  have hparam : Tendsto (fun s : ℝ => ((0 : ℝ), s)) (nhds t) (nhds ((0 : ℝ), t)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhds t) (nhds 0)).prodMk_nhds
      tendsto_id
  have hmap : Tendsto (fun z : ℕ × ℝ => (z.1, (0, z.2)))
      (atTop ×ˢ nhds t) (atTop ×ˢ nhds ((0 : ℝ), t)) := by
    have hfirst : Tendsto (fun z : ℕ × ℝ => z.1) (atTop ×ˢ nhds t) atTop := by
      exact tendsto_fst
    have hsecond : Tendsto (fun z : ℕ × ℝ => ((0 : ℝ), z.2))
        (atTop ×ˢ nhds t) (nhds ((0 : ℝ), t)) := by
      exact hparam.comp tendsto_snd
    have h := hfirst.prodMk hsecond
    simpa only [Function.comp_def] using h
  have h := hjoint.comp hmap
  apply h.congr'
  filter_upwards with z
  rfl

/-- The cumulative renewal limit holds at horizons rounded up to the next even integer. -/
theorem tendsto_criticalRenewalFunction_evenCeil (ϑ : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => criticalRenewalFunction ϑ N (evenCeil ((N : ℝ) * t)) /
      Real.log N) atTop
      (nhds (scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant) t)) := by
  let s : ℕ → ℝ := fun N => ((evenCeil ((N : ℝ) * t) : ℝ) / ((N + 1 : ℕ) : ℝ))
  have hceil := SHF.Moments.tendsto_evenCeil_div t ht.le
  have hfrac := tendsto_nat_div_succ (tendsto_id : Tendsto (fun N : ℕ => N) atTop atTop)
  have hprod : Tendsto (fun N : ℕ =>
      ((evenCeil ((N : ℝ) * t) : ℝ) / N) * ((N : ℝ) / ((N + 1 : ℕ) : ℝ)))
      atTop (nhds t) := by
    simpa only [id_eq, mul_one] using hceil.mul hfrac
  have heq : (fun N : ℕ => s N) =ᶠ[atTop] (fun N =>
      ((evenCeil ((N : ℝ) * t) : ℝ) / N) * ((N : ℝ) / ((N + 1 : ℕ) : ℝ))) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    unfold s
    field_simp
  have hs : Tendsto s atTop (nhds t) := hprod.congr' heq.symm
  have hjoint := (tendsto_joint_criticalRenewalFunctionProfile ϑ ht).comp
    ((tendsto_id : Tendsto (fun N : ℕ => N) atTop atTop).prodMk hs)
  apply hjoint.congr'
  filter_upwards with N
  change criticalRenewalFunction ϑ N ⌊((N : ℝ) + 1) * s N⌋₊ / Real.log N = _
  unfold s
  have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hprod : ((N : ℝ) + 1) *
      ((evenCeil ((N : ℝ) * t) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        (evenCeil ((N : ℝ) * t) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (by field_simp [hden] :
      ((N + 1 : ℕ) : ℝ) *
        ((evenCeil ((N : ℝ) * t) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
          (evenCeil ((N : ℝ) * t) : ℝ))
  rw [hprod, Nat.floor_natCast]

end Critical2DKPZ.Renewal

end
