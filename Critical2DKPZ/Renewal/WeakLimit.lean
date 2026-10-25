/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.RenewalLaw
public import Critical2DKPZ.Renewal.CompactMoments

/-!
# Weak convergence of tilted critical renewal laws

The Laplace limit determines every compactified moment. Polynomial approximation
then identifies the limit with the Euler-shifted scalar renewal density.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The critical parameters eventually lie in the domain of the tilted renewal law. -/
theorem eventually_critical_law_domain (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) :
    ∀ᶠ N : ℕ in atTop, 0 < criticalSigmaSq ϑ N ∧ 0 < criticalGap ϑ a N := by
  filter_upwards [criticalSigmaSq_eventually_pos ϑ,
    eventually_critical_damped_subcritical ϑ a ha] with N hσ hsub
  exact ⟨hσ, sub_pos.mpr hsub⟩

/-- A cutoff beyond which the tilted critical renewal laws are well defined. -/
def renewalStart (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) : ℕ :=
  (eventually_atTop.mp (eventually_critical_law_domain ϑ a ha)).choose

/-- The chosen starting scale satisfies the critical-law domain conditions. -/
theorem renewalStart_spec (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) (N : ℕ) :
    0 < criticalSigmaSq ϑ (N + renewalStart ϑ a ha) ∧
      0 < criticalGap ϑ a (N + renewalStart ϑ a ha) :=
  (eventually_atTop.mp (eventually_critical_law_domain ϑ a ha)).choose_spec _ (Nat.le_add_left _ _)

/-- The tail of the rescaled renewal laws, indexed without exceptional small cutoffs. -/
def compactCriticalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) (N : ℕ) :
    ProbabilityMeasure (Set.Icc (0 : ℝ) 1) :=
  compactRenewalLaw ϑ a (N + renewalStart ϑ a ha)
    (renewalStart_spec ϑ a ha N).1.le (renewalStart_spec ϑ a ha N).2


/-- Every compactified moment converges to the scalar-density moment. -/
theorem tendsto_moments_compactCriticalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) (k : ℕ) :
    Tendsto (fun N => ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k
      ∂(compactCriticalLaw ϑ a ha N : Measure _)) atTop
      (nhds (∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ k
        ∂(compactScalarRenewalLaw (ϑ - Real.eulerMascheroniConstant) a (by linarith) : Measure _))) := by
  let b : {b : ℝ // 0 < b} := ⟨a + k, add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg _)⟩
  have hb : ϑ < Real.log b + Real.eulerMascheroniConstant := by
    have hlog : Real.log a ≤ Real.log b :=
      Real.log_le_log a.2 (le_add_of_nonneg_right (Nat.cast_nonneg k))
    linarith only [ha, hlog]
  have h := ((tendsto_log_mul_critical_gap ϑ a).mul
    (tendsto_damped_criticalRenewalMass ϑ b hb)).comp (tendsto_add_atTop_nat (renewalStart ϑ a ha))
  rw [integral_pow_compactScalarRenewalLaw]
  have hc : (Real.log a + Real.eulerMascheroniConstant - ϑ) *
      (1 / (Real.log b + Real.eulerMascheroniConstant - ϑ)) =
      (Real.log a - (ϑ - Real.eulerMascheroniConstant)) /
        (Real.log (a + k) - (ϑ - Real.eulerMascheroniConstant)) := by
    dsimp only [b]
    rw [mul_one_div]
    congr 1 <;> ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [compactCriticalLaw, integral_pow_compactRenewalLaw]
  have hlog : Real.log ((N + renewalStart ϑ a ha : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N + renewalStart ϑ a ha by omega))).ne'
  change (Real.log ((N + renewalStart ϑ a ha : ℕ) : ℝ) * criticalGap ϑ a _) *
    ((∑' n, criticalRenewalMass ϑ _ n * Real.exp (-((a : ℝ) + k) * n /
      ((N + renewalStart ϑ a ha : ℕ) + 1))) / Real.log ((N + renewalStart ϑ a ha : ℕ) : ℝ)) = _
  field_simp

/-- The tilted critical renewal laws converge to the Euler-shifted scalar density law. -/
theorem tendsto_compactCriticalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) :
    Tendsto (compactCriticalLaw ϑ a ha) atTop
      (nhds (compactScalarRenewalLaw (ϑ - Real.eulerMascheroniConstant) a (by linarith))) :=
  tendsto_probabilityMeasure_of_moments _ _ (tendsto_moments_compactCriticalLaw ϑ a ha)

end Critical2DKPZ.Renewal

end
