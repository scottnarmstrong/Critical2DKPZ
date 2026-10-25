/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.DistributionValuedLimits
public import Critical2DKPZ.LocalSobolev.TestedFieldLpConvergence
public import Critical2DKPZ.LocalSobolev.LatticeTestConvergence
public import Critical2DKPZ.LocalSobolev.RegularizedFieldCauchy
public import Critical2DKPZ.LocalSobolev.LatticeReversalClose
import Critical2DKPZ.LocalSobolev.LatticeEnergyAllN

/-! # Construction and convergence of the critical KPZ process -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.LocalSobolev

/-- The moment, symmetry and reversal assumptions give a measurable critical KPZ process, regularized convergence and joint lattice convergence in local negative Sobolev spaces. -/
private theorem criticalKPZ_main_of_internal (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (hC12 : ToyJointAt ϑ P Z) (hrevN : LatticeReverseLawClose ϑ) :
    ∃ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr,
      IsCriticalKPZ P Z H ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn),
        Measurable[shfSigma Z] (fun ω => H t h₀ ω φ)) ∧
      (∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P, ∀ a, 0 < a →
        MemLocalNegSobolev a (H t h₀ ω)) ∧
      (∀ t δ, 0 < δ → δ < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P,
        LocallyIntegrable (fun x => kpzRegularized P Z t δ h₀ x ω)) ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (a : ℝ), 0 < a →
        ∀ (χ : TestFn) (ε : ℝ≥0∞), 0 < ε →
        Tendsto (fun δ => P {ω | ε < localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤ -
            H t h₀ ω) χ})
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞),
        1 ≤ p → p ≠ ⊤ →
        Tendsto (fun δ => eLpNorm
          (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ) p P)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)),
        (∀ i, 0 < t i) → ∀ a, 0 < a →
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) => toLocNegSobolevTuple a fun i =>
            Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤)
          atTop (fun ω => toLocNegSobolevTuple a fun i => H (t i) (h₀ i) ω)
          (fun _ => disorderLaw) P) := by
  have hLatticeEnergy : ∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ))
      (ht : ∀ i, 0 < t i) {a : ℝ} (ha : 0 < a),
      ∀ i (χ : TestFn), ∃ C : ℝ, ∀ N : ℕ,
        ∫⁻ ω, localNegSobolevSq (a / 2)
          (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤)
          χ ∂disorderLaw ≤ ENNReal.ofReal C := by
    intro k t h₀ ht a ha i χ
    exact kpzLattice_negSobolev_moment_le_allN_of hVD ϑ (ht i) (h₀ i)
      (a := a / 2) (by positivity) χ
  have hCauchy : ∀ {t : ℝ}, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ), ∀ {a : ℝ}, 0 < a →
      ∀ χ : TestFn, Tendsto (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
        (kpzRegularizedDistribution P Z t p.1 h₀ ω -
          kpzRegularizedDistribution P Z t p.2 h₀ ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    intro t ht h₀ a ha χ
    simpa only [kpzRegularizedDistribution] using
      kpzRegularized_negSobolev_cauchy_of hVD ϑ P Z hZ hHeatStartLogInput hsym hC12 ht h₀ ha χ
  obtain ⟨H, hH, hHmeas, hHloc, hHprob, hHenergy⟩ :=
    exists_kpzRegularized_criticalProcess_of P ϑ Z hZ hsym hCauchy
  have hHmem : ∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P, ∀ a, 0 < a →
      MemLocalNegSobolev a (H t h₀ ω) := by
    intro t ht h₀
    have hMemAll : ∀ᵐ ω ∂P, ∀ n : ℕ,
        MemLocalNegSobolev (1 / ((n : ℝ) + 1)) (H t h₀ ω) := by
      apply ae_all_iff.mpr
      intro n
      apply kpzRegularized_limit_memLocalNegSobolev_of P ϑ Z hZ ht h₀
        (H t h₀) (hHmeas t ht h₀)
      · positivity
      · exact (hHenergy t ht h₀ (1 / ((n : ℝ) + 1)) (by positivity))
      · intro χ
        simpa only [kpzRegularizedDistribution] using
          kpzRegularized_negSobolev_moment_le_of hVD ϑ P Z hZ hHeatStartLogInput hsym ht h₀
            (a := 1 / ((n : ℝ) + 1)) (by positivity) χ
    filter_upwards [hMemAll] with ω hω
    intro a ha
    obtain ⟨n, hn⟩ := exists_nat_gt a⁻¹
    have hn' : (1 : ℝ) / ((n : ℝ) + 1) ≤ a := by
      have hInv : 1 / a < (n : ℝ) + 1 := by
        have hncast : 1 / a < (n : ℝ) := by simpa [one_div] using hn
        exact hncast.trans (by exact_mod_cast Nat.lt_succ_self n)
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      have hmul := (div_lt_iff₀ ha).1 hInv
      nlinarith
    exact (hω n).mono hn'
  have hTupleLimit {k : ℕ} (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ))
      (ht : ∀ i, 0 < t i) {a : ℝ} (ha : 0 < a) :=
    kpzLattice_localSobolevTuple_tendsto_internal ϑ P Z hZ hsym hC12 hrevN
      H hH hHmeas hHmem t h₀ ht ha (hLatticeEnergy k t h₀ ht ha)
      (fun hH' hsym' hC12' hrevN' k' t' h₀' φ' ht' =>
        kpzLattice_testFn_tendsto_of ϑ P Z hZ hsym' hC12' hrevN'
          H hH' k' t' h₀' φ' ht')
  refine ⟨H, hH, hHmeas, hHmem, hHloc, hHprob, ?_, ?_⟩
  · intro t ht h₀ φ p hp hpTop
    exact kpzRegularized_pairing_tendsto_eLpNorm_of_process ϑ P Z hZ hC12
      H hH hHmeas ht h₀ φ p hp hpTop
  · intro k t h₀ ht a ha
    exact hTupleLimit t h₀ ht ha

/-- The stated moment, symmetry and reversal hypotheses yield a critical KPZ process with local negative Sobolev convergence. -/
theorem criticalKPZ_main_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (hC12 : ToyJointAt ϑ P Z) (hrevN : LatticeReverseLawClose ϑ) :
    ∃ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr,
      IsCriticalKPZ P Z H ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn),
        Measurable[shfSigma Z] (fun ω => H t h₀ ω φ)) ∧
      (∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P, ∀ a, 0 < a →
        MemLocalNegSobolev a (H t h₀ ω)) ∧
      (∀ t δ, 0 < δ → δ < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P,
        LocallyIntegrable (fun x => kpzRegularized P Z t δ h₀ x ω)) ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (a : ℝ), 0 < a →
        ∀ (χ : TestFn) (ε : ℝ≥0∞), 0 < ε →
        Tendsto (fun δ => P {ω | ε < localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤ -
            H t h₀ ω) χ})
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞),
        1 ≤ p → p ≠ ⊤ →
        Tendsto (fun δ => eLpNorm
          (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ) p P)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)),
        (∀ i, 0 < t i) → ∀ a, 0 < a →
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) => toLocNegSobolevTuple a fun i =>
            Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤)
          atTop (fun ω => toLocNegSobolevTuple a fun i => H (t i) (h₀ i) ω)
          (fun _ => disorderLaw) P) := by
  exact criticalKPZ_main_of_internal hVD ϑ P Z hZ hHeatStartLogInput hsym hC12 hrevN

end Critical2DKPZ.LocalSobolev

end
