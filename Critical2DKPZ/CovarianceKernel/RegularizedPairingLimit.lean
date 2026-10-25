/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
public import Critical2DKPZ.CovarianceKernel.CovarianceConvergence

/-! # Weak-limit target for regularized covariance kernels -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.CovarianceKernel

/-- Along an explicit vanishing sequence of regularization scales, the difference-kernel
pairings converge to the covariance of the limiting KPZ field.

Integrability of each finite-scale kernel pairing comes from the third conjunct of
`covariance_test_integral_eq_of`, applied in `regCovKernel_spec_of`; its almost-everywhere
difference-kernel identification transfers integrability to the displayed pairing. -/
theorem regularized_covKernel_pairing_tendsto_of
    {Ω : Type u} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hC12 : LocalSobolev.ToyJointAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (f g : TestFn) :
    Tendsto
      (fun n : ℕ => ∫ p : Plane × Plane,
        f p.1 * g p.2 * regCovKernel P Z t (t / ((n : ℝ) + 3)) (p.1 - p.2))
      atTop (𝓝 (cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P])) := by
  let δn : ℕ → ℝ := fun n => t / ((n : ℝ) + 3)
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 2)
    convert h using 1
    ext n
    simp [Nat.cast_add]
    ring
  have hδn : Tendsto δn atTop (𝓝 0) := by
    simpa [δn, div_eq_mul_inv, mul_comm] using hInv.const_mul t
  have hδpos (n : ℕ) : 0 < δn n := by
    dsimp [δn]
    positivity
  have hδlt (n : ℕ) : δn n < t := by
    dsimp [δn]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn : (1 : ℝ) < (n : ℝ) + 3 := by linarith
    have hden : 0 < (n : ℝ) + 3 := lt_trans zero_lt_one hn
    apply (div_lt_iff₀ hden).2
    have hmul := mul_lt_mul_of_pos_left hn ht
    nlinarith
  have hδnWithin : Tendsto δn atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hδn, Filter.Eventually.of_forall (fun n => hδpos n)⟩
  have hcov := (kpz_cov_tendsto_of ϑ P Z hZ hsym hrevL hC12 H hH ht f g).2
  have hseq := hcov.comp hδnWithin
  apply hseq.congr'
  filter_upwards [] with n
  have hspec := regCovKernel_spec_of ϑ P Z hZ hsym hrevL
    (hδpos n) (hδlt n)
  simpa [δn] using hspec.2 f g

end Critical2DKPZ.CovarianceKernel

end
