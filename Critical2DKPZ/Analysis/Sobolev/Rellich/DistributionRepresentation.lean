/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.NegativeNormCompactness
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichNet
public import Critical2DKPZ.Analysis.Sobolev.CompactJets

/-! On compact supports, positive Sobolev norms are bounded by finitely many derivative seminorms, so locally negative-Sobolev-bounded linear functionals define distributions. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- On each fixed compact support, derivatives up to some finite order bound the positive Sobolev energy uniformly over smooth test functions. -/
theorem exists_compact_sobolev_control_by_jet (K : Compacts Plane) (s : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        sobolevNormSq 2 s (fun x => (φ x : ℝ)) ≤
          ENNReal.ofReal (C * ‖compactTestJet K m φ‖ ^ 2) := by
  obtain ⟨m, C, hC, hres⟩ := rkResidual_diff_bound (K := (K : Set Plane)) K.isCompact s
  refine ⟨m, C, hC, ?_⟩
  intro φ
  let q : ℝ := ‖compactTestJet K m φ‖
  by_cases hq : q = 0
  · have hjet : compactTestJet K m φ = 0 := norm_eq_zero.mp hq
    have hφ : φ = 0 := by
      apply compactTestJet_injective K m
      simpa using hjet
    simp [hφ, sobolevNormSq, Real.fourier_eq]
  · have hqpos : 0 < q := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
    have hbound := hres (fun x => (φ x : ℝ)) φ.contDiff φ.tsupport_subset q hqpos
    apply hbound
    intro k hk x
    let i : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    have hfield : ‖compactTestJet K m φ i x‖ ≤ q := by
      calc
        ‖compactTestJet K m φ i x‖ ≤ ‖compactTestJet K m φ i‖ :=
          (compactTestJet K m φ i).norm_coe_le_norm x
        _ ≤ ‖compactTestJet K m φ‖ := by
          exact norm_le_pi_norm (compactTestJet K m φ) i
    change ‖iteratedFDeriv ℝ k (fun x => (φ x : ℝ)) x‖ ≤ q
    simpa [q, i, compactTestJet, ContDiffMapSupportedIn.structureMapCLM_top_apply] using hfield

/-- Every compactly supported smooth test has finite positive Sobolev square, with an explicit
positive real upper bound. The bound may depend on the test. -/
theorem exists_test_sobolev_norm_bound (s : ℝ) (φ : TestFn) :
    ∃ B : ℝ, 0 < B ∧
      sobolevNormSq 2 s (fun x => (φ x : ℝ)) ≤ ENNReal.ofReal (B ^ 2) := by
  let K : Compacts Plane := ⟨tsupport φ, φ.hasCompactSupport.isCompact⟩
  let φK : ContDiffMapSupportedIn Plane ℝ ⊤ K := {
    toFun := φ
    contDiff' := φ.contDiff
    zero_on_compl' := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport hx }
  obtain ⟨m, C, hC, hSob⟩ := exists_compact_sobolev_control_by_jet K s
  let q : ℝ := ‖compactTestJet K m φK‖
  let B : ℝ := (Real.sqrt C + 1) * q + 1
  have hq : 0 ≤ q := norm_nonneg _
  have hroot : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have hcoeff : C ≤ (Real.sqrt C + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hC, hroot]
  have ht : 0 ≤ (Real.sqrt C + 1) * q := mul_nonneg (by positivity) hq
  have hsq : C * q ^ 2 ≤ B ^ 2 := by
    calc
      C * q ^ 2 ≤ (Real.sqrt C + 1) ^ 2 * q ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg q)
      _ = ((Real.sqrt C + 1) * q) ^ 2 := by ring
      _ ≤ B ^ 2 := by dsimp [B]; nlinarith
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  have hfun : (fun x : Plane => (φK x : ℝ)) = fun x => (φ x : ℝ) := by
    funext x
    rfl
  have hSob' : sobolevNormSq 2 s (fun x => (φ x : ℝ)) ≤
      ENNReal.ofReal (C * q ^ 2) := by
    rw [← hfun]
    simpa [q] using hSob φK
  exact hSob'.trans (ENNReal.ofReal_le_ofReal hsq)

/-- A compact Sobolev-to-jet estimate and a negative Sobolev bound give a uniform finite-jet bound on distribution pairings. -/
theorem pairing_bound_by_compact_jet_of_sobolev_control (s M : ℝ)
    (hM : 0 ≤ M) (G : (Space 2 → ℝ) → ℝ)
    (D : Set Plane)
    (hGbound : negSobolevNorm 2 s D G ≤ ENNReal.ofReal M)
    (hGsmul : ∀ (c : ℝ) φ, IsTestFn D φ →
      G (fun x => c * φ x) = c * G φ)
    (K : Compacts Plane) (hKsub : (K : Set Plane) ⊆ D)
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hSob : ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
      sobolevNormSq 2 s (fun x => (φ x : ℝ)) ≤
        ENNReal.ofReal (C * ‖compactTestJet K m φ‖ ^ 2)) :
    ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
      |G (fun x => (φ x : ℝ))| ≤ M * (Real.sqrt C + 1) * ‖compactTestJet K m φ‖ := by
  intro φ
  let q : ℝ := ‖compactTestJet K m φ‖
  have hφtest : IsTestFn D (fun x => (φ x : ℝ)) := by
    refine ⟨φ.contDiff, φ.hasCompactSupport, ?_⟩
    exact φ.tsupport_subset.trans hKsub
  by_cases hq : q = 0
  · have hjet : compactTestJet K m φ = 0 := norm_eq_zero.mp hq
    have hφ : φ = 0 := by
      apply compactTestJet_injective K m
      simpa using hjet
    have hzero : IsTestFn D (fun _ : Plane => (0 : ℝ)) := by
      exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
    have hGzero : G (fun _ : Plane => (0 : ℝ)) = 0 := by
      simpa using hGsmul 0 (fun _ : Plane => (0 : ℝ)) hzero
    simp [hφ, hGzero]
  · have hqpos : 0 < q := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
    let η : ℝ := q * (Real.sqrt C + 1)
    have hη : 0 < η := by
      dsimp [η]
      positivity
    have hsqrt : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
    have hcoeff : C ≤ (Real.sqrt C + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg C]
    have hpow : C * q ^ 2 ≤ η ^ 2 := by
      calc
        C * q ^ 2 ≤ (Real.sqrt C + 1) ^ 2 * q ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg q)
        _ = η ^ 2 := by dsimp [η]; ring
    have hnorm : sobolevNormSq 2 s (fun x => (φ x : ℝ)) ≤ ENNReal.ofReal (η ^ 2) :=
      (hSob φ).trans (ENNReal.ofReal_le_ofReal hpow)
    have happly := abs_apply_le_negSobolevNorm (D := D) s η hη G hGsmul hφtest hnorm
    have hreal : ENNReal.ofReal |G (fun x => (φ x : ℝ))| ≤ ENNReal.ofReal (η * M) := by
      calc
        _ ≤ ENNReal.ofReal η * negSobolevNorm 2 s D G := happly
        _ ≤ ENNReal.ofReal η * ENNReal.ofReal M := mul_le_mul_right hGbound _
        _ = ENNReal.ofReal (η * M) := (ENNReal.ofReal_mul (le_of_lt hη)).symm
    have habs := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_of_lt hη) hM)).mp hreal
    calc
      |G (fun x => (φ x : ℝ))| ≤ η * M := habs
      _ = M * (Real.sqrt C + 1) * ‖compactTestJet K m φ‖ := by
        dsimp [η, q]
        ring

/-- A negative Sobolev bound controls distribution pairings uniformly over tests on each fixed compact support by finitely many derivatives. -/
theorem exists_pairing_bound_by_compact_jet (s M : ℝ)
    (hM : 0 ≤ M) (G : (Space 2 → ℝ) → ℝ)
    (D : Set Plane)
    (hGbound : negSobolevNorm 2 s D G ≤ ENNReal.ofReal M)
    (hGsmul : ∀ (c : ℝ) φ, IsTestFn D φ →
      G (fun x => c * φ x) = c * G φ)
    (K : Compacts Plane) (hKsub : (K : Set Plane) ⊆ D) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        |G (fun x => (φ x : ℝ))| ≤ M * (Real.sqrt C + 1) * ‖compactTestJet K m φ‖ := by
  obtain ⟨m, C, hC, hSob⟩ := exists_compact_sobolev_control_by_jet K s
  refine ⟨m, C, hC, ?_⟩
  exact pairing_bound_by_compact_jet_of_sobolev_control s M hM G D hGbound
    hGsmul K hKsub m C hC hSob

/-- The finite-jet estimate can be expressed in the defining compact-support seminorms of the
test-function topology. -/
theorem compactTestJet_norm_le_supSeminorm (K : Compacts Plane) (m : ℕ)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K) :
    ‖compactTestJet K m φ‖ ≤
      ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by
  apply norm_compactTestJet_le K m φ (by positivity)
  intro k hk x
  let i : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  calc
    ‖iteratedFDeriv ℝ k (fun y => (φ y : ℝ)) x‖ ≤
        ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k φ x‖ := by
          rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    _ ≤ ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k φ‖ :=
      (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k φ).norm_coe_le_norm x
    _ = ContDiffMapSupportedIn.seminorm ℝ Plane ℝ ⊤ K k φ := by
      rw [ContDiffMapSupportedIn.seminorm_apply]
    _ ≤ ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by
      have hs : ContDiffMapSupportedIn.seminorm ℝ Plane ℝ ⊤ K k ≤
          ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m :=
        Finset.le_sup (Finset.mem_Iic.mpr hk)
      exact hs φ

/-- A linear functional with a finite-jet bound on each compact is continuous on each compact
test-function space. -/
theorem continuous_compact_restriction_of_pairing_seminorm_bound
    (G : (Space 2 → ℝ) → ℝ)
    (hGadd : ∀ φ ψ, IsTestFn Set.univ φ → IsTestFn Set.univ ψ →
      G (φ + ψ) = G φ + G ψ)
    (hGsmul : ∀ (c : ℝ) φ, IsTestFn Set.univ φ →
      G (fun x => c * φ x) = c * G φ)
    (K : Compacts Plane)
    (hbound : ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        |G (fun x => (φ x : ℝ))| ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ) :
    Continuous (fun φ : ContDiffMapSupportedIn Plane ℝ ⊤ K => G (fun x => (φ x : ℝ))) := by
  let F : ContDiffMapSupportedIn Plane ℝ ⊤ K →ₗ[ℝ] ℝ :=
    { toFun := fun φ => G (fun x => (φ x : ℝ))
      map_add' := by
        intro φ ψ
        have hφ : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
          ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
        have hψ : IsTestFn Set.univ (fun x => (ψ x : ℝ)) :=
          ⟨ψ.contDiff, ψ.hasCompactSupport, Set.subset_univ _⟩
        change G ((fun x => (φ x : ℝ)) + (fun x => (ψ x : ℝ))) = _
        exact hGadd _ _ hφ hψ
      map_smul' := by
        intro c φ
        have hφ : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
          ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
        change G (fun x => c * (φ x : ℝ)) = _
        exact hGsmul c _ hφ }
  obtain ⟨m, C, hC, hpair⟩ := hbound
  let p : ℕ → Seminorm ℝ (ContDiffMapSupportedIn Plane ℝ ⊤ K) :=
    fun i => ContDiffMapSupportedIn.seminorm ℝ Plane ℝ ⊤ K i
  have hbounded : ∃ (S : Finset ℕ) (c : NNReal),
      ∀ φ, F φ ≤ (c • S.sup p) φ := by
    refine ⟨Finset.Iic m, ⟨C, hC⟩, ?_⟩
    intro φ
    have heq : (Finset.Iic m).sup p =
        ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m := rfl
    rw [heq]
    change G (fun x => (φ x : ℝ)) ≤
      C * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ
    exact (le_abs_self _).trans (hpair φ)
  exact WithSeminorms.continuous_real_rng
    (ContDiffMapSupportedIn.withSeminorms ℝ Plane ℝ ⊤ K) F hbounded

/-- A linear functional on smooth compactly supported functions with a finite-jet bound on every compact set defines a distribution. -/
theorem exists_frozen_distribution_of_compact_pairing_bounds
    (G : (Space 2 → ℝ) → ℝ)
    (hGadd : ∀ φ ψ, IsTestFn Set.univ φ → IsTestFn Set.univ ψ →
      G (φ + ψ) = G φ + G ψ)
    (hGsmul : ∀ (c : ℝ) φ, IsTestFn Set.univ φ →
      G (fun x => c * φ x) = c * G φ)
    (hbound : ∀ K : Compacts Plane, ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        |G (fun x => (φ x : ℝ))| ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ) :
    ∃ T : Distr, ∀ φ : TestFn, T φ = G (fun x => (φ x : ℝ)) := by
  let toFun : TestFn → ℝ := fun φ => G (fun x => (φ x : ℝ))
  have htoAdd : ∀ φ ψ, toFun (φ + ψ) = toFun φ + toFun ψ := by
    intro φ ψ
    have hφ : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
      ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
    have hψ : IsTestFn Set.univ (fun x => (ψ x : ℝ)) :=
      ⟨ψ.contDiff, ψ.hasCompactSupport, Set.subset_univ _⟩
    change G ((fun x => (φ x : ℝ)) + (fun x => (ψ x : ℝ))) = _
    exact hGadd _ _ hφ hψ
  have htoSmul : ∀ c : ℝ, ∀ φ, toFun (c • φ) = c • toFun φ := by
    intro c φ
    have hφ : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
      ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
    change G (fun x => c * (φ x : ℝ)) = _
    exact hGsmul c _ hφ
  have htoCont : ∀ (K : Compacts Plane) (hK : (K : Set Plane) ⊆ (Set.univ : Set Plane)),
      Continuous (toFun ∘ TestFunction.ofSupportedIn hK) := by
    intro K hK
    have hcont := continuous_compact_restriction_of_pairing_seminorm_bound
      G hGadd hGsmul K (hbound K)
    have heq : (toFun ∘ TestFunction.ofSupportedIn hK) =
        fun φ : ContDiffMapSupportedIn Plane ℝ ⊤ K => G (fun x => (φ x : ℝ)) := by
      funext φ
      rfl
    rw [heq]
    exact hcont
  refine ⟨TestFunction.mkCLM ℝ toFun htoAdd htoSmul htoCont, ?_⟩
  intro φ
  rfl

/-- A linear functional bounded in a negative Sobolev norm on every compact support is represented by a distribution. -/
theorem exists_frozen_distribution_of_local_negative_norm_bounds
    (s : ℝ) (G : (Space 2 → ℝ) → ℝ)
    (hGadd : ∀ φ ψ, IsTestFn Set.univ φ → IsTestFn Set.univ ψ →
      G (φ + ψ) = G φ + G ψ)
    (hGsmul : ∀ (c : ℝ) φ, IsTestFn Set.univ φ →
      G (fun x => c * φ x) = c * G φ)
    (hLocal : ∀ K : Compacts Plane, ∃ (D : Set Plane) (M : ℝ),
      (K : Set Plane) ⊆ D ∧ 0 ≤ M ∧
        negSobolevNorm 2 s D G ≤ ENNReal.ofReal M) :
    ∃ T : Distr, ∀ φ : TestFn, T φ = G (fun x => (φ x : ℝ)) := by
  have hcompact : ∀ K : Compacts Plane, ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        |G (fun x => (φ x : ℝ))| ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by
    intro K
    obtain ⟨D, M, hKD, hM, hGbound⟩ := hLocal K
    have hGsmulD : ∀ (c : ℝ) φ, IsTestFn D φ →
        G (fun x => c * φ x) = c * G φ := by
      intro c φ hφ
      have hφU : IsTestFn Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
      exact hGsmul c φ hφU
    obtain ⟨m, C, hC, hpair⟩ :=
      exists_pairing_bound_by_compact_jet s M hM G D hGbound hGsmulD K hKD
    let A : ℝ := M * (Real.sqrt C + 1)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    refine ⟨m, A, hA, ?_⟩
    intro φ
    have hjet := compactTestJet_norm_le_supSeminorm K m φ
    calc
      |G (fun x => (φ x : ℝ))| ≤ A * ‖compactTestJet K m φ‖ := by
        simpa [A] using hpair φ
      _ ≤ A * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ :=
        mul_le_mul_of_nonneg_left hjet hA
  exact exists_frozen_distribution_of_compact_pairing_bounds G hGadd hGsmul hcompact

/-- A sequence of distributions with locally uniform negative Sobolev bounds and Cauchy test pairings has a distributional limit against every test function. -/
theorem exists_frozen_distribution_limit_of_locally_bounded_cauchy_pairings
    (s : ℝ) (T : ℕ → Distr)
    (hpair : ∀ φ : TestFn, CauchySeq (fun n => T n φ))
    (hLocal : ∀ K : Compacts Plane, ∃ (D : Set Plane) (M : ℝ),
      (K : Set Plane) ⊆ D ∧ 0 ≤ M ∧
        ∀ n, negSobolevNorm 2 s D (distributionFunctional (T n)) ≤ ENNReal.ofReal M) :
    ∃ Tlim : Distr, ∀ φ : TestFn,
      Tendsto (fun n => T n φ) atTop (𝓝 (Tlim φ)) := by
  classical
  let F : ℕ → (Space 2 → ℝ) → ℝ := fun n φ => distributionFunctional (T n) φ
  have hCauchy (φ : Space 2 → ℝ) (hφ : IsTestFn Set.univ φ) :
      CauchySeq (fun n => F n φ) := by
    let ψ : TestFn := testFnOfRellich hφ.1 hφ.2.1
    have hEq (n : ℕ) : F n φ = T n ψ := by
      change distributionFunctional (T n) φ = T n ψ
      rw [distributionFunctional_apply (T n) hφ]
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hpair ψ) ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [hEq m, hEq n]
    exact hN m hm n hn
  let G : (Space 2 → ℝ) → ℝ := fun φ =>
    if hφ : IsTestFn Set.univ φ then limUnder atTop (fun n => F n φ) else 0
  have hlim (φ : Space 2 → ℝ) (hφ : IsTestFn Set.univ φ) :
      Tendsto (fun n => F n φ) atTop (𝓝 (G φ)) := by
    change Tendsto (fun n => F n φ) atTop
      (𝓝 (if h : IsTestFn Set.univ φ then limUnder atTop (fun n => F n φ) else 0))
    rw [dite_eq_left hφ]
    exact (hCauchy φ hφ).tendsto_limUnder
  have hGadd : ∀ φ ψ, IsTestFn Set.univ φ → IsTestFn Set.univ ψ →
      G (φ + ψ) = G φ + G ψ := by
    intro φ ψ hφ hψ
    apply tendsto_nhds_unique (hlim (φ + ψ) (hφ.add hψ))
    have hsum : Tendsto (fun n => F n φ + F n ψ) atTop (𝓝 (G φ + G ψ)) :=
      (hlim φ hφ).add (hlim ψ hψ)
    have heq : (fun n => F n φ + F n ψ) = fun n => F n (φ + ψ) := by
      funext n
      exact (distributionFunctional_add (T n) hφ hψ).symm
    simpa only [heq] using hsum
  have hGsmul : ∀ (c : ℝ) φ, IsTestFn Set.univ φ →
      G (fun x => c * φ x) = c * G φ := by
    intro c φ hφ
    apply tendsto_nhds_unique (hlim (fun x => c * φ x) (hφ.const_mul c))
    have hmul : Tendsto (fun n => c * F n φ) atTop (𝓝 (c * G φ)) :=
      tendsto_const_nhds.mul (hlim φ hφ)
    have heq : (fun n => c * F n φ) = fun n => F n (fun x => c * φ x) := by
      funext n
      exact (distributionFunctional_smul (T n) hφ c).symm
    simpa only [heq] using hmul
  have hLocalG : ∀ K : Compacts Plane, ∃ (D : Set Plane) (M : ℝ),
      (K : Set Plane) ⊆ D ∧ 0 ≤ M ∧
        negSobolevNorm 2 s D G ≤ ENNReal.ofReal M := by
    intro K
    obtain ⟨D, M, hKD, hM, hbound⟩ := hLocal K
    have hGbound : negSobolevNorm 2 s D G ≤ ENNReal.ofReal M := by
      unfold negSobolevNorm
      apply sSup_le
      rintro v ⟨φ, hφ, hn, rfl⟩
      have hφU : IsTestFn Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
      have hFnBound (n : ℕ) : |F n φ| ≤ M := by
        have hval : ENNReal.ofReal |F n φ| ≤ negSobolevNorm 2 s D (F n) := by
          unfold negSobolevNorm
          apply le_sSup
          exact ⟨φ, hφ, hn, rfl⟩
        exact (ENNReal.ofReal_le_ofReal_iff hM).mp (hval.trans (hbound n))
      have hIcc : ∀ᶠ n in atTop, F n φ ∈ Set.Icc (-M) M :=
        Filter.Eventually.of_forall fun n => abs_le.mp (hFnBound n)
      have hGmem : G φ ∈ Set.Icc (-M) M :=
        isClosed_Icc.mem_of_tendsto (hlim φ hφU) hIcc
      exact ENNReal.ofReal_le_ofReal
        (abs_le.mpr ⟨hGmem.1, hGmem.2⟩)
    exact ⟨D, M, hKD, hM, hGbound⟩
  obtain ⟨Tlim, hTlim⟩ := exists_frozen_distribution_of_local_negative_norm_bounds
    s G hGadd hGsmul hLocalG
  refine ⟨Tlim, ?_⟩
  intro φ
  have hφ : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
    ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
  have hrep : testFnOfRellich hφ.1 hφ.2.1 = φ := by
    apply TestFunction.ext
    intro x
    rfl
  have hEq (n : ℕ) : F n (fun x => (φ x : ℝ)) = T n φ := by
    change distributionFunctional (T n) (fun x => (φ x : ℝ)) = T n φ
    rw [distributionFunctional_apply (T n) hφ, hrep]
  rw [hTlim φ]
  rw [← funext hEq]
  exact hlim (fun x => (φ x : ℝ)) hφ

/-- A functional bounded in one global negative Sobolev norm is continuous on each fixed compact-support test-function space. -/
theorem continuous_compact_restriction_of_negSobolevNorm_bound
    (s M : ℝ) (hM : 0 ≤ M) (G : (Space 2 → ℝ) → ℝ)
    (hGadd : ∀ φ ψ, IsTestFn Set.univ φ → IsTestFn Set.univ ψ →
      G (φ + ψ) = G φ + G ψ)
    (hGsmul : ∀ (c : ℝ) φ, IsTestFn Set.univ φ →
      G (fun x => c * φ x) = c * G φ)
    (hGbound : negSobolevNorm 2 s Set.univ G ≤ ENNReal.ofReal M)
    (K : Compacts Plane) :
    Continuous (fun φ : ContDiffMapSupportedIn Plane ℝ ⊤ K => G (fun x => (φ x : ℝ))) := by
  let F : ContDiffMapSupportedIn Plane ℝ ⊤ K →ₗ[ℝ] ℝ :=
    { toFun := fun φ => G (fun x => (φ x : ℝ))
      map_add' := by
        intro φ ψ
        have hφ : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
          ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
        have hψ : IsTestFn Set.univ (fun x => (ψ x : ℝ)) :=
          ⟨ψ.contDiff, ψ.hasCompactSupport, Set.subset_univ _⟩
        change G ((fun x => (φ x : ℝ)) + (fun x => (ψ x : ℝ))) = _
        exact hGadd _ _ hφ hψ
      map_smul' := by
        intro c φ
        have hφ : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
          ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
        change G (fun x => c * (φ x : ℝ)) = _
        exact hGsmul c _ hφ }
  obtain ⟨m, C, hC, hpair⟩ :=
    exists_pairing_bound_by_compact_jet s M hM G Set.univ hGbound hGsmul K
      (Set.subset_univ _)
  let A : ℝ := M * (Real.sqrt C + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let p : ℕ → Seminorm ℝ (ContDiffMapSupportedIn Plane ℝ ⊤ K) :=
    fun i => ContDiffMapSupportedIn.seminorm ℝ Plane ℝ ⊤ K i
  have hbound : ∃ (S : Finset ℕ) (c : NNReal),
      ∀ φ, F φ ≤ (c • S.sup p) φ := by
    refine ⟨Finset.Iic m, ⟨A, hA⟩, ?_⟩
    intro φ
    have hφ := hpair φ
    have hjet := compactTestJet_norm_le_supSeminorm K m φ
    have habs : |G (fun x => (φ x : ℝ))| ≤
        A * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by
      dsimp [A] at hφ ⊢
      exact hφ.trans (mul_le_mul_of_nonneg_left hjet (by positivity))
    have heq : (Finset.Iic m).sup p =
        ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m := rfl
    rw [heq]
    change G (fun x => (φ x : ℝ)) ≤ A *
      ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ
    exact (le_abs_self _).trans habs
  exact WithSeminorms.continuous_real_rng
    (ContDiffMapSupportedIn.withSeminorms ℝ Plane ℝ ⊤ K) F hbound

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
