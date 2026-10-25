/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.Renewal.CumulativeUniformLimit
import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # A uniform lower bound on critical one-point second moments -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.FutureProfiles

/-- The rescaled partition-function second moment is bounded below uniformly for times between `N / 4` and `N` and parameters in a compact interval, for sufficiently large `N`. -/
theorem sigmaSq_secondMoment_ge (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ k : ℕ,
      N ≤ 4 * k → k ≤ N →
        c ≤ criticalSigmaSq ϑ N *
          ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw := by
  let θ₀ : ℝ := -A
  let τ : ℝ := 1 / 8
  let L : ℝ := Renewal.scalarRenewalPrimitive
    (θ₀ - Real.eulerMascheroniConstant) τ
  have hτ : 0 < τ := by norm_num [τ]
  have hLpos : 0 < L := by
    dsimp [L]
    exact Renewal.scalarRenewalPrimitive_pos _ hτ
  have hσlog := Renewal.tendsto_sigma_mul_log θ₀
  have hrenew := Renewal.tendsto_criticalRenewalFunction_evenCeil θ₀ hτ
  have hprod : Tendsto
      (fun N : ℕ =>
        (criticalSigmaSq θ₀ N * Real.log (N : ℝ)) *
          (Renewal.criticalRenewalFunction θ₀ N
            (evenCeil ((N : ℝ) * τ)) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.pi * L)) := by
    simpa only [θ₀, τ, L] using hσlog.mul hrenew
  have hprodEq :
      (fun N : ℕ =>
        (criticalSigmaSq θ₀ N * Real.log (N : ℝ)) *
          (Renewal.criticalRenewalFunction θ₀ N
            (evenCeil ((N : ℝ) * τ)) / Real.log (N : ℝ))) =ᶠ[atTop]
      fun N : ℕ => criticalSigmaSq θ₀ N *
        Renewal.criticalRenewalFunction θ₀ N (evenCeil ((N : ℝ) * τ)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    field_simp
  have hlimit : Tendsto
      (fun N : ℕ => criticalSigmaSq θ₀ N *
        Renewal.criticalRenewalFunction θ₀ N (evenCeil ((N : ℝ) * τ)))
      atTop (𝓝 (Real.pi * L)) := hprod.congr' hprodEq
  let c : ℝ := Real.pi * L / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hbelow : c < Real.pi * L := by
    dsimp [c]
    nlinarith [mul_pos Real.pi_pos hLpos]
  have heventBase : ∀ᶠ N : ℕ in atTop, c ≤ criticalSigmaSq θ₀ N *
      Renewal.criticalRenewalFunction θ₀ N (evenCeil ((N : ℝ) * τ)) := by
    filter_upwards [hlimit.eventually (Ioi_mem_nhds hbelow)] with N hN
    exact hN.le
  have heventLog : ∀ᶠ N : ℕ in atTop, A < Real.log (N : ℝ) := by
    have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |A|
    filter_upwards [hlog] with N hN
    exact lt_of_le_of_lt (le_abs_self A) hN
  refine ⟨c, hc, ?_⟩
  have hfreeEqEvent := Renewal.eventually_freeSecondMoment_eq_criticalRenewalFunction θ₀
  have hσEvent := Renewal.criticalSigmaSq_eventually_pos θ₀
  filter_upwards [eventually_ge_atTop 16, heventBase, heventLog, hfreeEqEvent, hσEvent]
    with N hN hbase hlog hfreeEq hσ₀pos
  intro ϑ hϑ k hNk hkN
  have hA0 : 0 ≤ A := by linarith [hϑ.1, hϑ.2]
  have hθabs : |ϑ| ≤ A := abs_le.mpr ⟨hϑ.1, hϑ.2⟩
  have hθlog : |ϑ| < Real.log (N : ℝ) := lt_of_le_of_lt hθabs hlog
  have hθ₀log : |θ₀| < Real.log (N : ℝ) := by
    simpa [θ₀, abs_of_nonneg hA0] using hlog
  have hN1 : 1 ≤ N := by omega
  have hspecθ := OnePoint.criticalBeta_spec_of_abs_lt_log hN1 hθlog
  have hspec₀ := OnePoint.criticalBeta_spec_of_abs_lt_log hN1 hθ₀log
  have hσθ : Polymer.sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N := by
    simpa only [Polymer.sigmaSq] using hspecθ
  have hσ₀ : Polymer.sigmaSq (criticalBeta θ₀ N) = criticalSigmaSq θ₀ N := by
    simpa only [Polymer.sigmaSq] using hspec₀
  have hσθmono : criticalSigmaSq θ₀ N ≤ criticalSigmaSq ϑ N :=
    Renewal.criticalSigmaSq_mono_parameter (by omega) (by dsimp [θ₀]; linarith [hϑ.1])
  have hσβmono : Polymer.sigmaSq (criticalBeta θ₀ N) ≤
      Polymer.sigmaSq (criticalBeta ϑ N) := by rw [hσ₀, hσθ]; exact hσθmono
  have hσβ₀nonneg : 0 ≤ Polymer.sigmaSq (criticalBeta θ₀ N) := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have htime0 : (evenCeil ((N : ℝ) * τ)) ≤ k := by
    have hround := Critical2DKPZ.evenCeil_error (show 0 ≤ (N : ℝ) * τ by positivity)
    have hNreal : 16 ≤ (N : ℝ) := by exact_mod_cast hN
    have hNkreal : (N : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hNk
    have hcast : (evenCeil ((N : ℝ) * τ) : ℝ) ≤ (k : ℝ) := by
      dsimp [τ] at hround ⊢
      nlinarith [hround.2]
    exact_mod_cast hcast
  have hfreeTime : Renewal.freeSecondMoment (criticalBeta θ₀ N)
      (evenCeil ((N : ℝ) * τ)) ≤ Renewal.freeSecondMoment (criticalBeta θ₀ N) k := by
    rw [Renewal.freeSecondMoment_eq_renewalFunction]
    apply Renewal.renewalFunction_mono_time
    intro r
    exact mul_nonneg hσβ₀nonneg (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
    exact htime0
  have hfreeMono : Renewal.freeSecondMoment (criticalBeta θ₀ N) k ≤
      Renewal.freeSecondMoment (criticalBeta ϑ N) k :=
    OnePoint.freeSecondMoment_mono_sigmaSq hσβmono k
  have hfreeNonneg : 0 ≤ Renewal.freeSecondMoment (criticalBeta θ₀ N) k := by
    unfold Renewal.freeSecondMoment
    exact integral_nonneg fun ω => sq_nonneg _
  have hσβθnonneg : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ N) := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have hbaseline : c ≤ Polymer.sigmaSq (criticalBeta θ₀ N) *
      Renewal.freeSecondMoment (criticalBeta θ₀ N) (evenCeil ((N : ℝ) * τ)) := by
    rw [hσ₀]
    simpa only [hfreeEq (evenCeil ((N : ℝ) * τ))] using hbase
  calc
    c ≤ Polymer.sigmaSq (criticalBeta θ₀ N) *
        Renewal.freeSecondMoment (criticalBeta θ₀ N) (evenCeil ((N : ℝ) * τ)) := hbaseline
    _ ≤ Polymer.sigmaSq (criticalBeta θ₀ N) *
        Renewal.freeSecondMoment (criticalBeta θ₀ N) k :=
      mul_le_mul_of_nonneg_left hfreeTime hσβ₀nonneg
    _ ≤ Polymer.sigmaSq (criticalBeta ϑ N) *
        Renewal.freeSecondMoment (criticalBeta ϑ N) k :=
      mul_le_mul hσβmono hfreeMono hfreeNonneg hσβθnonneg
    _ = criticalSigmaSq ϑ N *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw := by
      rw [hσθ]
      rfl

end Critical2DKPZ.FutureProfiles

end
