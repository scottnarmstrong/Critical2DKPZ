/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.ProfileEstimateCorrections
public import Critical2DKPZ.FutureProfiles.EnergySeminorm
public import Critical2DKPZ.FutureProfiles.HelperExpansions
public import Critical2DKPZ.FutureProfiles.HelperIdentities
public import Critical2DKPZ.FutureProfiles.OpenCorrectorEnergy
public import Critical2DKPZ.FutureProfiles.SplitBoundInputs
public import Critical2DKPZ.FutureProfiles.WalkBounds
public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawGoodSet
public import Critical2DKPZ.FutureProfiles.AdaptiveLeftTail
import Mathlib.Tactic

/-! # The block profile estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal
open ProbabilityTheory

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer

/-- The profile-good event complement bound follows from the probability half of the block-ratio estimates. -/
theorem measure_profileGoodSet_compl_le_of (hBlockRatioInput : RatioBoundP) (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
          (disorderLaw (profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
            C / ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨ρ₀, hρ₀, hBlockRatioInputA⟩ := hBlockRatioInput A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨C₁, hBlockRatioInputρ₁⟩ := hBlockRatioInputA ρ₁
  refine ⟨5 * |C₁|, ?_⟩
  intro ρ hρρ
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρρ.1
  filter_upwards [hBlockRatioInputρ₁ ρ hρρ, blockTime_monotone hρ] with N hBlockRatioInputN ht
  intro ϑ hϑ r s hr hrs hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let K := blockCount N ρ
  have hsK' : s + 1 ≤ K := by dsimp [K]; omega
  have hratioBound := hBlockRatioInputN ϑ hϑ r s hr hrs hsK'
  have hD : 0 < (K : ℝ) - s := by
    have hNat : 0 < K - s := by omega
    rw [← Nat.cast_sub (show s ≤ K by omega)]
    exact_mod_cast hNat
  have hblock : (disorderLaw (blockGoodSet β t r s)ᶜ).toReal ≤ |C₁| / ((K : ℝ) - s) := by
    calc
      (disorderLaw (blockGoodSet β t r s)ᶜ).toReal ≤ C₁ / ((K : ℝ) - s) := by
        simpa [β, t, K] using hratioBound.1
      _ ≤ |C₁| / ((K : ℝ) - s) :=
        div_le_div_of_nonneg_right (le_abs_self C₁) hD.le
  have hRatio : ∫ ω in blockGoodSet β t r s,
      (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw ≤ |C₁| / ((K : ℝ) - s) := by
    calc
      ∫ ω in blockGoodSet β t r s,
          (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw ≤ C₁ / ((K : ℝ) - s) := by
        simpa [β, t, K] using hratioBound.2
      _ ≤ |C₁| / ((K : ℝ) - s) :=
        div_le_div_of_nonneg_right (le_abs_self C₁) hD.le
  have hprofile := profileGoodSet_compl_measure_le β t r s ht hr hrs
    (|C₁| / ((K : ℝ) - s)) (|C₁| / ((K : ℝ) - s)) hblock hRatio
  calc
    (disorderLaw (profileGoodSet β t r s)ᶜ).toReal ≤
        |C₁| / ((K : ℝ) - s) + 4 * (|C₁| / ((K : ℝ) - s)) := hprofile
    _ = (5 * |C₁|) / ((K : ℝ) - s) := by ring
    _ = (5 * |C₁|) / ((blockCount N ρ : ℝ) - s) := by rfl

private theorem integral_smoothedEndpointDist_futureEnergy_le_of
    (β : ℝ) (t : ℕ → ℕ) (N r s K : ℕ) (ht : Monotone t)
    (hr : 1 ≤ r) (hrs : r ≤ s) (hsK : s + 2 ≤ K) (hts : t s ≤ N)
    (Cweighted Cwalk : ℝ)
    (hweightedInt : IntegrableOn
      (fun ω => futureEnergy β (t s) N (weightedCorrection β t r s ω))
      (blockGoodSet β t r s) disorderLaw)
    (hweighted : ∫ ω in blockGoodSet β t r s,
      futureEnergy β (t s) N (weightedCorrection β t r s ω) ∂disorderLaw ≤
        Cweighted / ((K : ℝ) - s))
    (hwalk : futureEnergy β (t s) N (fun y => srwKernel (t s) y) ≤
      Cwalk * ((K : ℝ) + 1 - s)) :
    IntegrableOn
      (fun ω => futureEnergy β (t s) N
        (smoothedEndpointDist β (t (r - 1)) (t s) 0 ω))
      (profileGoodSet β t r s) disorderLaw ∧
    ∫ ω in profileGoodSet β t r s,
      futureEnergy β (t s) N
        (smoothedEndpointDist β (t (r - 1)) (t s) 0 ω) ∂disorderLaw ≤
      (4 * |Cwalk| + 8 * |Cweighted|) * ((K : ℝ) - s) := by
  classical
  let G := blockGoodSet β t r s
  let PG := profileGoodSet β t r s
  let I := Finset.Icc r s
  let S := I.biUnion (fun u => openCorrectorNumeratorSupport t u s)
  let W : Disorder → Site → ℝ := weightedCorrection β t r s
  let EW : Disorder → ℝ := fun ω => futureEnergy β (t s) N (W ω)
  let EU : ℝ := futureEnergy β (t s) N (fun y => srwKernel (t s) y)
  let L : ℝ := (K : ℝ) - s
  have hL : 1 ≤ L := by
    dsimp [L]
    have hn : 1 ≤ K - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ K)]
    exact_mod_cast hn
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hblockGlobal := Gaussian.disorderBlock_le (t (r - 1)) (t s)
  have hRatioMeasBlock :
      Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)] (blockRatio β t r s) :=
    measurable_blockRatio_on_block β t ht r s (by omega)
  have hGglobal : MeasurableSet G := hblockGlobal G
    (measurable_blockGoodSet_on_block β t ht r s)
  have hRmeas : Measurable (blockRatio β t r s) :=
    hRatioMeasBlock.mono hblockGlobal le_rfl
  have hGblock :
      MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)] G :=
    measurable_blockGoodSet_on_block β t ht r s
  have hPGmeas : MeasurableSet PG := by
    change MeasurableSet (G ∩ {ω | |blockRatio β t r s ω - 1| ≤ 1 / 2})
    exact hGglobal.inter (measurableSet_le
      (hRmeas.sub measurable_const).abs measurable_const)
  have hPGsubset : PG ⊆ G := fun _ hω => hω.1
  have hWsupport (ω : Disorder) (y : Site) (hy : y ∉ S) : W ω y = 0 := by
    dsimp [W, weightedCorrection]
    apply Finset.sum_eq_zero
    intro u hu
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro hmem
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, hmem⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div,
      mul_zero]
  have hprofile (ω : Disorder) :
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω =
        (fun y => srwKernel (t s) y) + (blockRatio β t r s ω)⁻¹ • W ω := by
    funext y
    rw [smoothedEndpointDist_block_expansion β t ht r s hr hrs ω y]
    simp [W, weightedCorrection, smul_eq_mul]
  have henergyBound (ω : Disorder) (hω : ω ∈ PG) :
      futureEnergy β (t s) N (smoothedEndpointDist β (t (r - 1)) (t s) 0 ω) ≤
        2 * EU + 8 * EW ω := by
    let V : Site → ℝ := fun y => srwKernel (t s) y
    let c : ℝ := (blockRatio β t r s ω)⁻¹
    have hVsupport (y : Site) (hy : y ∉ S ∪ Polymer.endpoints 0 (t s)) : V y = 0 := by
      simpa [V] using Polymer.srwKernel_eq_zero_of_not_mem (t s) 0 y (by
        intro hmem
        exact hy (Finset.mem_union_right _ hmem))
    have hWsupport' (y : Site) (hy : y ∉ S ∪ Polymer.endpoints 0 (t s)) : W ω y = 0 :=
      hWsupport ω y (by intro hmem; exact hy (Finset.mem_union_left _ hmem))
    have hWscaledSupport (y : Site) (hy : y ∉ S ∪ Polymer.endpoints 0 (t s)) :
        (c • W ω) y = 0 := by
      simp [Pi.smul_apply, smul_eq_mul, hWsupport' y hy]
    have htriangle := sqrt_futureEnergy_add_le β (t s) N V (c • W ω)
      (S ∪ Polymer.endpoints 0 (t s)) hVsupport hWscaledSupport
    have hscale := futureEnergy_smul β (t s) N c (W ω) S (hWsupport ω)
    have hRgood : |blockRatio β t r s ω - 1| ≤ 1 / 2 := by
      simpa [PG, profileGoodSet] using hω.2
    have hRpos : 0 < blockRatio β t r s ω := by
      unfold blockRatio
      exact div_pos (Polymer.smoothedP2Plane_pos β (t (r - 1)) (t s) 0 ω)
        (Finset.prod_pos fun i _ => blockMass_pos β t i ω)
    have hRlower : 1 / 2 ≤ blockRatio β t r s ω := by
      have h := abs_le.mp hRgood
      linarith
    have hcabs : |c| ≤ 2 := by
      dsimp [c]
      rw [abs_inv, abs_of_pos hRpos, inv_eq_one_div]
      apply (div_le_iff₀ hRpos).2
      linarith
    have hcSq : c ^ 2 ≤ 4 := by
      have hsq : |c| ^ 2 ≤ (2 : ℝ) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg c) (by norm_num : (0 : ℝ) ≤ 2)).2 hcabs
      rw [sq_abs] at hsq
      norm_num at hsq
      exact hsq
    have hVnonneg : 0 ≤ futureEnergy β (t s) N V :=
      futureEnergy_nonneg β (t s) N V
    have hWnonneg : 0 ≤ EW ω := futureEnergy_nonneg β (t s) N (W ω)
    have hrootSq := (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 htriangle
    have htriangleEnergy :
        futureEnergy β (t s) N (V + c • W ω) ≤ 2 * EU + 2 * futureEnergy β (t s) N (c • W ω) := by
      calc
        _ = Real.sqrt (futureEnergy β (t s) N (V + c • W ω)) ^ 2 := by
          rw [Real.sq_sqrt (futureEnergy_nonneg β (t s) N (V + c • W ω))]
        _ ≤ (Real.sqrt (futureEnergy β (t s) N V) +
              Real.sqrt (futureEnergy β (t s) N (c • W ω))) ^ 2 := hrootSq
        _ ≤ 2 * EU + 2 * futureEnergy β (t s) N (c • W ω) := by
          have hVrootSq : Real.sqrt (futureEnergy β (t s) N V) ^ 2 = EU := by
            simpa [EU] using Real.sq_sqrt hVnonneg
          have hWrootSq :
              Real.sqrt (futureEnergy β (t s) N (c • W ω)) ^ 2 =
                futureEnergy β (t s) N (c • W ω) :=
            Real.sq_sqrt (futureEnergy_nonneg β (t s) N (c • W ω))
          nlinarith [sq_nonneg (Real.sqrt (futureEnergy β (t s) N V) -
            Real.sqrt (futureEnergy β (t s) N (c • W ω))), hVrootSq, hWrootSq]
    calc
      _ = futureEnergy β (t s) N (V + c • W ω) := by rw [hprofile ω]
      _ ≤ 2 * EU + 2 * futureEnergy β (t s) N (c • W ω) := htriangleEnergy
      _ = 2 * EU + 2 * (c ^ 2 * EW ω) := by rw [hscale]
      _ ≤ 2 * EU + 8 * EW ω := by
        have hscaled : c ^ 2 * EW ω ≤ 4 * EW ω :=
          mul_le_mul_of_nonneg_right hcSq hWnonneg
        nlinarith
  have hsmoothedInt : IntegrableOn
      (fun ω => futureEnergy β (t s) N
        (smoothedEndpointDist β (t (r - 1)) (t s) 0 ω)) PG disorderLaw := by
    have hm : t (r - 1) ≤ t s := ht (by omega)
    exact (integrable_futureEnergy_smoothedEndpointDist β (t (r - 1)) (t s) N hm hts 0).integrableOn
  have hwalkInt : IntegrableOn (fun _ : Disorder => 2 * EU) PG disorderLaw :=
    (integrable_const (μ := disorderLaw) (2 * EU)).integrableOn
  have hweightedPG : IntegrableOn EW PG disorderLaw :=
    hweightedInt.mono_set hPGsubset
  have hRhsInt : IntegrableOn (fun ω => 2 * EU + 8 * EW ω) PG disorderLaw :=
    hwalkInt.add (hweightedPG.const_mul 8)
  have henergyIntegral :
      ∫ ω in PG, futureEnergy β (t s) N
          (smoothedEndpointDist β (t (r - 1)) (t s) 0 ω) ∂disorderLaw ≤
        2 * EU + 8 * (∫ ω in G, EW ω ∂disorderLaw) := by
    calc
      _ ≤ ∫ ω in PG, 2 * EU + 8 * EW ω ∂disorderLaw :=
        integral_mono_ae hsmoothedInt hRhsInt (by
          filter_upwards [ae_restrict_mem hPGmeas] with ω hω
          exact henergyBound ω hω)
      _ = (∫ ω in PG, (2 * EU : ℝ) ∂disorderLaw) +
          8 * (∫ ω in PG, EW ω ∂disorderLaw) := by
        calc
          _ = (∫ ω in PG, (2 * EU : ℝ) ∂disorderLaw) +
              ∫ ω in PG, 8 * EW ω ∂disorderLaw := by
            rw [integral_add hwalkInt (hweightedPG.const_mul 8)]
          _ = _ := by
            congr 1
            exact integral_const_mul 8 EW
      _ ≤ 2 * EU + 8 * (∫ ω in G, EW ω ∂disorderLaw) := by
        have hEUnonneg : 0 ≤ EU := by
          exact futureEnergy_nonneg β (t s) N (fun y => srwKernel (t s) y)
        have hwalkSet : ∫ ω in PG, (2 * EU : ℝ) ∂disorderLaw ≤ 2 * EU := by
          calc
            _ ≤ ∫ ω, (2 * EU : ℝ) ∂disorderLaw :=
              setIntegral_le_integral (integrable_const (2 * EU))
                (Filter.Eventually.of_forall fun _ => mul_nonneg (by norm_num) hEUnonneg)
            _ = 2 * EU := by simp
        have hweightedSet : ∫ ω in PG, EW ω ∂disorderLaw ≤
            ∫ ω in G, EW ω ∂disorderLaw :=
          setIntegral_mono_set hweightedInt
            (Filter.Eventually.of_forall fun ω => futureEnergy_nonneg β (t s) N (W ω))
            (Filter.Eventually.of_forall fun ω hω => hPGsubset hω)
        exact add_le_add hwalkSet (mul_le_mul_of_nonneg_left hweightedSet (by norm_num))
  have hCwalk : 0 ≤ 2 * |Cwalk| := by positivity
  have hCweighted : 0 ≤ 8 * |Cweighted| := by positivity
  have hweightedAbs : ∫ ω in G, EW ω ∂disorderLaw ≤ |Cweighted| / L :=
    hweighted.trans (div_le_div_of_nonneg_right (le_abs_self Cweighted) hLpos.le)
  refine ⟨hsmoothedInt, ?_⟩
  calc
    _ ≤ 2 * EU + 8 * (|Cweighted| / L) := by
      exact henergyIntegral.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hweightedAbs (by norm_num : (0 : ℝ) ≤ 8)))
    _ ≤ 2 * (|Cwalk| * (L + 1)) + 8 * (|Cweighted| / L) := by
      apply add_le_add
      · have hwalk' : EU ≤ Cwalk * (L + 1) := by
          calc
            EU ≤ Cwalk * ((K : ℝ) + 1 - s) := by simpa [EU] using hwalk
            _ = Cwalk * (L + 1) := by dsimp [L]; ring
        exact mul_le_mul_of_nonneg_left
          (hwalk'.trans (mul_le_mul_of_nonneg_right (le_abs_self Cwalk) (by positivity)))
          (by norm_num)
      · rfl
    _ ≤ (4 * |Cwalk| + 8 * |Cweighted|) * L := by
      have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
      have hwalkLe : 2 * (|Cwalk| * (L + 1)) ≤ 4 * |Cwalk| * L := by
        nlinarith [mul_nonneg (abs_nonneg Cwalk) (sub_nonneg.mpr hL)]
      have hweightedLe : 8 * (|Cweighted| / L) ≤ 8 * |Cweighted| * L := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hLpos).2
        nlinarith [mul_nonneg (abs_nonneg Cweighted) (sub_nonneg.mpr hLsq)]
      nlinarith [hwalkLe, hweightedLe]
    _ = _ := by ring

/-- The open-discrepancy and block-ratio bounds imply five probability and future-energy estimates for endpoint profiles. The integrands are integrable on their good sets: the second and
third by the `IntegrableOn` conjuncts of `commonCorrection_integral_energy_le_of_openCorrector` and
`weightedCorrection_integral_energy_le_of`, the fourth by that of
`profileResidual_integral_sqrt_le_of`, and the fifth by
`integrable_futureEnergy_smoothedEndpointDist`. -/
theorem profile_estimates_of (hDiscrepancyStringInput : OpenStringBound) (hBlockRatioInput : RatioBoundP) (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ (C : ℝ) (ℓ : ℕ),
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + ℓ ≤ blockCount N ρ →
          (disorderLaw (profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
              C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
                (commonCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω) ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
                (weightedCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω) ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              Real.sqrt (futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N (fun y =>
                smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1))
                    (blockTime N ρ s) 0 ω y -
                  srwKernel (blockTime N ρ s) y -
                  commonCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω y)) ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
                (smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1))
                  (blockTime N ρ s) 0 ω) ∂disorderLaw ≤
            C * ((blockCount N ρ : ℝ) - s) := by
  classical
  obtain ⟨ρOpen, θ, hρOpen, hθ0, hθ1, hOpenA⟩ :=
    setIntegral_futureEnergy_openCorrector_le_of hDiscrepancyStringInput A
  obtain ⟨ρRatio, hρRatio, hRatioA⟩ := hBlockRatioInput A
  obtain ⟨ρProb, hρProb, hProbA⟩ := measure_profileGoodSet_compl_le_of hBlockRatioInput A
  obtain ⟨ρWeighted, hρWeighted, hWeightedA⟩ :=
    weightedCorrection_integral_energy_le_of hDiscrepancyStringInput hBlockRatioInput A
  let ρ₀ := max ρOpen (max ρRatio (max ρProb ρWeighted))
  have hρ₀ : 1 < ρ₀ := lt_of_lt_of_le hρOpen (le_max_left _ _)
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨C₀, hOpenρ₁⟩ := hOpenA ρ₁
  obtain ⟨C₁, hRatioρ₁⟩ := hRatioA ρ₁
  obtain ⟨Cprob, hProbρ₁⟩ := hProbA ρ₁
  obtain ⟨Cweighted, hWeightedρ₁⟩ := hWeightedA ρ₁
  obtain ⟨Cwalk, hWalkρ₁⟩ := futureEnergy_srwKernel_blockTime_le A ρ₀ ρ₁ hρ₀
  let Ccommon := |C₀| / (1 - θ) ^ 2
  let Cresid := 2 * (Real.sqrt (|C₁| * |C₀|) / (1 - θ) +
    Real.sqrt (|C₁| * |Ccommon|))
  let Csmoothed := 4 * |Cwalk| + 8 * |Cweighted|
  let C := |Cprob| + |Ccommon| + |Cweighted| + |Cresid| + Csmoothed
  have hCprob : Cprob ≤ C := by
    dsimp [C]
    have hnn : 0 ≤ |Ccommon| + |Cweighted| + |Cresid| + Csmoothed := by
      positivity
    linarith [le_abs_self Cprob]
  have hCcommon : Ccommon ≤ C := by
    dsimp [C]
    have hnn : 0 ≤ |Cprob| + |Cweighted| + |Cresid| + Csmoothed := by
      positivity
    linarith [le_abs_self Ccommon]
  have hCweighted : Cweighted ≤ C := by
    dsimp [C]
    have hnn : 0 ≤ |Cprob| + |Ccommon| + |Cresid| + Csmoothed := by
      positivity
    linarith [le_abs_self Cweighted]
  have hCresid : Cresid ≤ C := by
    dsimp [C]
    have hnn : 0 ≤ |Cprob| + |Ccommon| + |Cweighted| + Csmoothed := by
      positivity
    linarith [le_abs_self Cresid]
  have hCsmoothed : Csmoothed ≤ C := by
    dsimp [C]
    have hnn : 0 ≤ |Cprob| + |Ccommon| + |Cweighted| + |Cresid| := by
      positivity
    dsimp [Csmoothed]
    linarith
  refine ⟨C, 2, ?_⟩
  intro ρ hρ
  have hρOpen' : ρOpen ≤ ρ := (le_max_left _ _).trans hρ.1
  have hρrest : max ρRatio (max ρProb ρWeighted) ≤ ρ :=
    (le_max_right _ _).trans hρ.1
  have hρRatio' : ρRatio ≤ ρ := (le_max_left _ _).trans hρrest
  have hρProbRest : max ρProb ρWeighted ≤ ρ := (le_max_right _ _).trans hρrest
  have hρProb' : ρProb ≤ ρ := (le_max_left _ _).trans hρProbRest
  have hρWeighted' : ρWeighted ≤ ρ := (le_max_right _ _).trans hρProbRest
  have hρstrict : 1 < ρ := lt_of_lt_of_le hρ₀ hρ.1
  filter_upwards
    [hOpenρ₁ ρ ⟨hρOpen', hρ.2⟩,
      hRatioρ₁ ρ ⟨hρRatio', hρ.2⟩,
      hProbρ₁ ρ ⟨hρProb', hρ.2⟩,
      hWeightedρ₁ ρ ⟨hρWeighted', hρ.2⟩,
      hWalkρ₁ ρ hρ, blockTime_monotone hρstrict]
    with N hOpenN hRatioN hProbN hWeightedN hWalkN hmono
  intro ϑ hϑ r s hr hrs hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let K := blockCount N ρ
  have htS : t s ≤ N := by
    have hsK' : s ≤ blockCount N ρ := by omega
    have htimeS := hmono hsK'
    have hKpos : 0 < blockCount N ρ := by unfold blockCount; omega
    have hterminal : blockTime N ρ (blockCount N ρ) = N := by
      simp [blockTime, Nat.ne_of_gt hKpos]
    rw [hterminal] at htimeS
    exact htimeS
  have hsK2 : s + 2 ≤ K := by simpa [K] using hsK
  have hOpen : ∀ u : ℕ, r ≤ u → u ≤ s →
      ∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
    intro u hu hus
    exact hOpenN ϑ hϑ u s (by omega) hus (by omega)
  have hRatio : ∀ u : ℕ, r < u → u ≤ s →
      ∫ ω in blockGoodSet β t r (u - 1),
        (blockRatio β t r (u - 1) ω - 1) ^ 2 ∂disorderLaw ≤
          C₁ / ((K : ℝ) - (u - 1)) := by
    intro u hru hus
    have huone : 1 ≤ u := by omega
    have huK : (u - 1) + 1 ≤ K := by
      rw [Nat.sub_add_cancel huone]
      omega
    have h := hRatioN ϑ hϑ r (u - 1) hr (by omega) huK
    simpa [β, t, K, Nat.cast_sub huone, Nat.cast_one] using h.2
  have hTotalRatio : ∫ ω in blockGoodSet β t r s,
      (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw ≤ C₁ / ((K : ℝ) - s) := by
    have h := hRatioN ϑ hϑ r s hr hrs (by omega)
    simpa [β, t, K] using h.2
  have hCommon := commonCorrection_integral_energy_le_of_openCorrector β t N r s K
    hmono hr (by simpa [K] using hsK2) htS θ C₀ hθ0 hθ1 hOpen
  have hWeighted := hWeightedN ϑ hϑ r s hr hrs (by omega)
  have hResidual := profileResidual_integral_sqrt_le_of β t N r s K hmono hr hrs
    hsK2 htS θ C₀ C₁ Ccommon hθ0 hθ1 hRatio hOpen hTotalRatio hCommon.1 hCommon.2
  have hWalk := hWalkN ϑ hϑ s (by omega) (by omega)
  have hSmoothed := integral_smoothedEndpointDist_futureEnergy_le_of β t N r s K
    hmono hr hrs hsK2 htS Cweighted Cwalk hWeighted.1 hWeighted.2 hWalk
  have hProb := hProbN ϑ hϑ r s hr hrs (by omega)
  have hDen : 0 < (K : ℝ) - s := by
    have hn : 0 < K - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ K)]
    exact_mod_cast hn
  have hDenL : (K : ℝ) - s = (blockCount N ρ : ℝ) - s := by rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hbound := hProb.trans (div_le_div_of_nonneg_right hCprob hDen.le)
    simpa [β, t, K, hDenL] using hbound
  · have hbound := hCommon.2.trans (div_le_div_of_nonneg_right hCcommon hDen.le)
    simpa [β, t, K, Ccommon, hDenL] using hbound
  · have hbound := hWeighted.2.trans (div_le_div_of_nonneg_right hCweighted hDen.le)
    simpa [β, t, K, hDenL] using hbound
  · have hbound := hResidual.2.trans (div_le_div_of_nonneg_right hCresid hDen.le)
    simpa [β, t, K, Cresid, Ccommon, hDenL] using hbound
  · have hbound := hSmoothed.2.trans (mul_le_mul_of_nonneg_right hCsmoothed hDen.le)
    simpa [β, t, K, Csmoothed, hDenL] using hbound

end Critical2DKPZ.FutureProfiles

end
