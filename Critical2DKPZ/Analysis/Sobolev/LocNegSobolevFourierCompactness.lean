/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevCompactness

/-! # Uniform bounds on compact families of test functions -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology Distributions

namespace Critical2DKPZ.Analysis.Sobolev

/-- A uniform local energy bound controls pairings uniformly on every compact continuous
family of tests with one common compact support. -/
theorem exists_uniform_pairing_bound_of_localizer_energy
    {P : Type*} [TopologicalSpace P] (a : ℝ) (T : ℕ → Distr)
    (K : Compacts Plane) (A : Set P) (hA : IsCompact A)
    (φ : P → ContDiffMapSupportedIn Plane ℝ ⊤ K) (hφ : Continuous φ)
    (hT : ∀ m, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      ∀ n, localNegSobolevSq a (T n) (localizer m) ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n p, p ∈ A →
      |T n (TestFunction.ofSupportedIn (Set.subset_univ _) (φ p))| ≤ B := by
  obtain ⟨r, _, hKr⟩ := K.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
  obtain ⟨m, hm⟩ := exists_nat_gt r
  have hKD : (K : Set Plane) ⊆ Rellich.compactnessDomain m := by
    intro x hx
    change dist x 0 < (m : ℝ) + 1
    exact (Metric.mem_ball.mp (hKr hx)).trans (by linarith)
  obtain ⟨B, hB, hTB⟩ := hT m
  let M : ℝ := (B ^ (1 / 2 : ℝ)).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hnorm (n : ℕ) : Rellich.negSobolevNorm 2 a (Rellich.compactnessDomain m)
      (Rellich.distributionFunctional (T n)) ≤ ENNReal.ofReal M := by
    calc
      _ ≤ (localNegSobolevSq a (T n) (localizer m)) ^ (1 / 2 : ℝ) :=
        Rellich.distributionFunctional_negSobolevNorm_le_localEnergy (T n) (localizer m) a
          (fun x hx => localizer_eq_one_of_mem_closedBall m
            (Metric.ball_subset_closedBall hx))
      _ ≤ B ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (hTB n) (by norm_num)
      _ = ENNReal.ofReal M :=
        (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB)).symm
  obtain ⟨j, C, hC, hSob⟩ := Rellich.exists_compact_sobolev_control_by_jet K a
  obtain ⟨D, hD⟩ := hA.bddAbove_image
    (((compactTestJet K j).continuous.comp hφ).norm.continuousOn)
  let D' : ℝ := max D 0
  refine ⟨M * (Real.sqrt C + 1) * D', by positivity, ?_⟩
  intro n p hp
  have hsmul : ∀ c χ, Rellich.IsTestFn (Rellich.compactnessDomain m) χ →
      Rellich.distributionFunctional (T n) (fun x => c * χ x) =
        c * Rellich.distributionFunctional (T n) χ := by
    intro c χ hχ
    exact Rellich.distributionFunctional_smul (T n)
      ⟨hχ.1, hχ.2.1, Set.subset_univ _⟩ c
  have hpair := Rellich.pairing_bound_by_compact_jet_of_sobolev_control a M hM
    (Rellich.distributionFunctional (T n)) (Rellich.compactnessDomain m)
    (hnorm n) hsmul K hKD j C hC hSob (φ p)
  have hrepr : Rellich.distributionFunctional (T n) (fun x => φ p x) =
      T n (TestFunction.ofSupportedIn (Set.subset_univ _) (φ p)) := by
    rw [Rellich.distributionFunctional_apply (T n)
      ⟨(φ p).contDiff, (φ p).hasCompactSupport, Set.subset_univ _⟩]
    congr 1
  rw [hrepr] at hpair
  exact hpair.trans (mul_le_mul_of_nonneg_left
    ((hD ⟨p, hp, rfl⟩).trans (le_max_left D 0)) (by positivity))

/-- Uniform energy bounds give a uniform bound on the localized Fourier transform on each
compact set of frequencies. -/
theorem exists_uniform_localizedFourier_bound
    (a : ℝ) (T : ℕ → Distr) (χ : TestFn) (A : Set Plane) (hA : IsCompact A)
    (hT : ∀ m, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      ∀ n, localNegSobolevSq a (T n) (localizer m) ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n ξ, ξ ∈ A → ‖localizedFourier (T n) χ ξ‖ ≤ B := by
  let K : Compacts Plane := ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩
  let fc : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K := fun ξ => {
    toFun := χ.mulCos ξ
    contDiff' := (χ.mulCos ξ).contDiff
    zero_on_compl' := fun x hx => by
      change χ x * Real.cos (inner ℝ ξ x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul] }
  let fs : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K := fun ξ => {
    toFun := χ.mulSin ξ
    contDiff' := (χ.mulSin ξ).contDiff
    zero_on_compl' := fun x hx => by
      change χ x * Real.sin (inner ℝ ξ x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul] }
  have hfc : Continuous fc := by
    apply continuous_supported_test_family K fc
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => χ p.2 * Real.cos (inner ℝ p.1 p.2))
    exact (χ.contDiff.comp contDiff_snd).mul
      (Real.contDiff_cos.comp (contDiff_fst.inner ℝ contDiff_snd))
  have hfs : Continuous fs := by
    apply continuous_supported_test_family K fs
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => χ p.2 * Real.sin (inner ℝ p.1 p.2))
    exact (χ.contDiff.comp contDiff_snd).mul
      (Real.contDiff_sin.comp (contDiff_fst.inner ℝ contDiff_snd))
  obtain ⟨Bc, hBc, hc⟩ :=
    exists_uniform_pairing_bound_of_localizer_energy a T K A hA fc hfc hT
  obtain ⟨Bs, hBs, hs⟩ :=
    exists_uniform_pairing_bound_of_localizer_energy a T K A hA fs hfs hT
  refine ⟨Bc + Bs, add_nonneg hBc hBs, fun n ξ hξ => ?_⟩
  have hc' : |T n (χ.mulCos ξ)| ≤ Bc := by
    convert hc n ξ hξ using 1
    congr 2
  have hs' : |T n (χ.mulSin ξ)| ≤ Bs := by
    convert hs n ξ hξ using 1
    congr 2
  calc
    _ ≤ ‖(T n (χ.mulCos ξ) : ℂ)‖ + ‖Complex.I * (T n (χ.mulSin ξ) : ℂ)‖ :=
      norm_sub_le _ _
    _ = |T n (χ.mulCos ξ)| + |T n (χ.mulSin ξ)| := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Bc + Bs := add_le_add hc' hs'

end Critical2DKPZ.Analysis.Sobolev

end
