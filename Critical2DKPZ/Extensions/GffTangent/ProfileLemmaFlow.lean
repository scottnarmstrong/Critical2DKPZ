/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.ProfileIdentities
public import Critical2DKPZ.Extensions.GffTangent.Grid
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Critical2DKPZ.JointConvergence.HeatStartProfileApprox
public import Critical2DKPZ.Extensions.GffTangent.ProfileLemmaLattice
import Critical2DKPZ.Blocks.GridAlignment
import Critical2DKPZ.NonGaussian.HeatStartWalkLaw
import Critical2DKPZ.JointConvergence.HeatStartLogConvergence
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Critical2DKPZ.SHF.Positivity.LawFatou

/-!
# Passing endpoint-profile comparisons to the flow

Continuous cutoffs keep the two denominator coordinates away from zero.
Their removal uses positivity only in the limiting law.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

open JointConvergence SHF.Limit

/-- A continuous cutoff supported strictly above the denominator threshold. -/
def profileDenominatorCutoff (ε d : ℝ) : ℝ := min 1 (max 0 (d / ε - 1))

theorem profileDenominatorCutoff_nonneg (ε d : ℝ) : 0 ≤ profileDenominatorCutoff ε d :=
  le_min zero_le_one (le_max_left _ _)

theorem profileDenominatorCutoff_le_one (ε d : ℝ) : profileDenominatorCutoff ε d ≤ 1 :=
  min_le_left _ _

theorem profileDenominatorCutoff_eq_zero {ε d : ℝ} (hε : 0 < ε) (hd : d ≤ ε) :
    profileDenominatorCutoff ε d = 0 := by
  have hdiv : d / ε ≤ 1 := (div_le_one hε).mpr hd
  simp only [profileDenominatorCutoff, max_eq_left (by linarith : d / ε - 1 ≤ 0),
    min_eq_right zero_le_one]

theorem profileDenominatorCutoff_eq_one {ε d : ℝ} (hε : 0 < ε) (hd : 2 * ε ≤ d) :
    profileDenominatorCutoff ε d = 1 := by
  have hdiv : 2 ≤ d / ε := (le_div_iff₀ hε).mpr hd
  unfold profileDenominatorCutoff
  exact min_eq_left ((by linarith : 1 ≤ d / ε - 1).trans (le_max_right _ _))

/-- The bounded absolute difference of two ratios, in numerator/denominator order. -/
def profileRatioCap (M : ℝ) (z : Fin 4 → ℝ) : ℝ := min |z 0 / z 1 - z 2 / z 3| M

/-- A continuous minorant of the ratio cap, with both denominator cutoffs. -/
def profileRatioCutoff (M ε : ℝ) (z : Fin 4 → ℝ) : ℝ :=
  min |z 0 / max (z 1) ε - z 2 / max (z 3) ε| M *
    profileDenominatorCutoff ε (z 1) * profileDenominatorCutoff ε (z 3)

theorem continuous_profileRatioCutoff (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (profileRatioCutoff M ε) := by
  have hden (i : Fin 4) (z : Fin 4 → ℝ) : max (z i) ε ≠ 0 :=
    ne_of_gt (hε.trans_le (le_max_right _ _))
  have hdiv (i j : Fin 4) : Continuous (fun z : Fin 4 → ℝ => z i / max (z j) ε) :=
    (continuous_apply i).div₀ ((continuous_apply j).max continuous_const) (hden j)
  have hcut (i : Fin 4) : Continuous (fun z : Fin 4 → ℝ => profileDenominatorCutoff ε (z i)) := by
    unfold profileDenominatorCutoff
    fun_prop
  exact ((((hdiv 0 1).sub (hdiv 2 3)).abs.min continuous_const).mul (hcut 1)).mul (hcut 3)

theorem profileRatioCutoff_nonneg {M : ℝ} (hM : 0 ≤ M) (ε : ℝ) (z : Fin 4 → ℝ) :
    0 ≤ profileRatioCutoff M ε z := by
  unfold profileRatioCutoff
  exact mul_nonneg (mul_nonneg (le_min (abs_nonneg _) hM)
    (profileDenominatorCutoff_nonneg _ _)) (profileDenominatorCutoff_nonneg _ _)

theorem profileRatioCutoff_le {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (z : Fin 4 → ℝ) :
    profileRatioCutoff M ε z ≤ profileRatioCap M z := by
  by_cases h1 : z 1 ≤ ε
  · simp only [profileRatioCutoff, profileDenominatorCutoff_eq_zero hε h1, mul_zero, zero_mul]
    exact le_min (abs_nonneg _) hM
  by_cases h3 : z 3 ≤ ε
  · simp only [profileRatioCutoff, profileDenominatorCutoff_eq_zero hε h3, mul_zero]
    exact le_min (abs_nonneg _) hM
  have hcap : 0 ≤ profileRatioCap M z := le_min (abs_nonneg _) hM
  unfold profileRatioCutoff
  rw [max_eq_left (not_le.mp h1).le, max_eq_left (not_le.mp h3).le]
  change profileRatioCap M z * _ * _ ≤ profileRatioCap M z
  calc
    _ ≤ profileRatioCap M z * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (profileDenominatorCutoff_le_one _ _) hcap)
        (profileDenominatorCutoff_le_one _ _) (profileDenominatorCutoff_nonneg _ _) (by positivity)
    _ = _ := by ring

theorem profileRatioCutoff_le_cap {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (z : Fin 4 → ℝ) :
    profileRatioCutoff M ε z ≤ M := (profileRatioCutoff_le hM hε z).trans (min_le_right _ _)

/-- Once the positive denominators exceed twice the cutoff, the continuous
test is exactly the ratio cap. -/
theorem profileRatioCutoff_eq {M ε : ℝ} (hε : 0 < ε) (z : Fin 4 → ℝ)
    (h1 : 2 * ε ≤ z 1) (h3 : 2 * ε ≤ z 3) :
    profileRatioCutoff M ε z = profileRatioCap M z := by
  have hε2 : ε ≤ 2 * ε := by linarith
  simp only [profileRatioCutoff, profileDenominatorCutoff_eq_one hε h1,
    profileDenominatorCutoff_eq_one hε h3, mul_one,
    max_eq_left (hε2.trans h1), max_eq_left (hε2.trans h3), profileRatioCap]

/-- The denominator-cutoff ratio test as a bounded continuous function. -/
def profileRatioCutoffTest {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    (Fin 4 → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨profileRatioCutoff M ε, continuous_profileRatioCutoff M hε⟩
    (2 * M) (by
      intro z w
      change |profileRatioCutoff M ε z - profileRatioCutoff M ε w| ≤ 2 * M
      have hz := profileRatioCutoff_le_cap hM hε z
      have hw := profileRatioCutoff_le_cap hM hε w
      calc
        _ ≤ |profileRatioCutoff M ε z| + |profileRatioCutoff M ε w| := abs_sub _ _
        _ ≤ M + M := by
          rw [abs_of_nonneg (profileRatioCutoff_nonneg hM _ _),
            abs_of_nonneg (profileRatioCutoff_nonneg hM _ _)]
          exact add_le_add hz hw
        _ = _ := by ring)

/-- A truncated ratio expectation passes through joint convergence in law
when the two limiting denominators are positive almost surely. -/
theorem profile_ratio_cap_integral_le_of_tendstoInDistribution
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → Fin 4 → ℝ} {Y : Ω → Fin 4 → ℝ}
    (hd : TendstoInDistribution X atTop Y μ P)
    (hpos : ∀ᵐ ω ∂P, 0 < Y ω 1 ∧ 0 < Y ω 3)
    {M C : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ N in atTop, (∫ ω, profileRatioCap M (X N ω) ∂(μ N)) ≤ C) :
    (∫ ω, profileRatioCap M (Y ω) ∂P) ≤ C := by
  have hmcap : Measurable (profileRatioCap M) := by unfold profileRatioCap; fun_prop
  have hcapnorm (z : Fin 4 → ℝ) : ‖profileRatioCap M z‖ ≤ M := by
    unfold profileRatioCap
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) hM)]
    exact min_le_right _ _
  have htest {ε : ℝ} (hε : 0 < ε) : (∫ ω, profileRatioCutoff M ε (Y ω) ∂P) ≤ C := by
    let f := profileRatioCutoffTest hM hε
    have ht := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hd.forall_aemeasurable hd.aemeasurable_limit).mp hd f
    apply le_of_tendsto ht
    filter_upwards [hbound] with N hN
    apply le_trans _ hN
    have hiX : Integrable (fun ω => profileRatioCap M (X N ω)) (μ N) :=
      Integrable.of_bound ((hmcap.comp_aemeasurable (hd.forall_aemeasurable N)).aestronglyMeasurable)
        M (Eventually.of_forall fun ω => hcapnorm _)
    have hif : Integrable (fun ω => f (X N ω)) (μ N) := by
      apply Integrable.of_bound ((f.continuous.measurable.comp_aemeasurable
        (hd.forall_aemeasurable N)).aestronglyMeasurable) M
      filter_upwards [] with ω
      change ‖profileRatioCutoff M ε (X N ω)‖ ≤ M
      rw [Real.norm_eq_abs, abs_of_nonneg (profileRatioCutoff_nonneg hM _ _)]
      exact profileRatioCutoff_le_cap hM hε _
    apply integral_mono hif hiX
    intro ω
    exact profileRatioCutoff_le hM hε _
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => profileRatioCutoff M (ε k) (Y ω))
      atTop (𝓝 (profileRatioCap M (Y ω))) := by
    filter_upwards [hpos] with ω hω
    have hsmall1 := (hεlim.const_mul 2).eventually (eventually_lt_nhds (by simpa using hω.1))
    have hsmall3 := (hεlim.const_mul 2).eventually (eventually_lt_nhds (by simpa using hω.2))
    apply tendsto_const_nhds.congr'
    filter_upwards [hsmall1, hsmall3] with k hk1 hk3
    exact (profileRatioCutoff_eq (hε k) _ hk1.le hk3.le).symm
  have hdom (k : ℕ) : ∀ᵐ ω ∂P, ‖profileRatioCutoff M (ε k) (Y ω)‖ ≤ M := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (profileRatioCutoff_nonneg hM _ _)]
    exact profileRatioCutoff_le_cap hM (hε k) _
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Ω => M)
    (fun k => (((continuous_profileRatioCutoff M (hε k)).measurable.comp_aemeasurable
      hd.aemeasurable_limit).aestronglyMeasurable)) (integrable_const M) hdom hlim
  exact le_of_tendsto hconv (Eventually.of_forall fun k => htest (hε k))

/-- Boundedness of cell averages of a bounded exponential terminal function. -/
theorem profile_cellAverage_exp_bounds (N : ℕ) (hN : 1 ≤ N) (h₀ : Plane →ᵇ ℝ)
    (z : Site) :
    0 ≤ cellAverage N (fun y => Real.exp (h₀ y)) z ∧
      cellAverage N (fun y => Real.exp (h₀ y)) z ≤ Real.exp ‖h₀‖ := by
  by_cases hz : z ∈ evenLattice
  · change Even (z 0 + z 1) at hz
    have hb := Smoothing.cellAverage_exp_bounds_of_even N hN h₀ hz
    have hloghi := (abs_le.mp hb.2).2
    have hupp : cellAverage N (fun y => Real.exp (h₀ y)) z ≤ Real.exp ‖h₀‖ := by
      have := Real.exp_le_exp.mpr hloghi
      simpa only [Real.exp_log hb.1] using this
    exact ⟨hb.1.le, hupp⟩
  · have hEmpty : cell N z = ∅ := cell_eq_empty_of_not_even hz
    simp [cellAverage, hEmpty]
    positivity

/-- Replacing the heat-cell start weights by the walk kernel changes the polymer pairing by at
most the terminal bound times the `ℓ¹` kernel error. -/
theorem profile_heatStart_pairing_error (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s T δ : ℝ) (hδ : 0 < δ) (x : Plane) (h₀ : Plane →ᵇ ℝ) (η : ℝ)
    (hη : ∑' w : Site,
      |srwKernel (evenCeil ((N : ℝ) * δ)) (w - latticePoint N x) -
        ∫ y in cell N w, heatKernel δ (y - x)| ≤ η) :
    MemLp (fun ω =>
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω -
        ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(SHF.Limit.polymerMeasure ϑ N s T ω)) 1 disorderLaw ∧
    ∫⁻ ω, ENNReal.ofReal
      |profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω -
        ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(SHF.Limit.polymerMeasure ϑ N s T ω)| ∂disorderLaw ≤
      ENNReal.ofReal (Real.exp ‖h₀‖ * η) := by
  classical
  let a : ℕ := evenCeil (N * s)
  let b : ℕ := evenCeil (N * T)
  let m : ℕ := evenCeil (N * δ)
  let x₀ : Site := latticePoint N x
  let ν : Site → ℝ := fun w => srwKernel m (w - x₀)
  let μ : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x)
  let f : Site → ℝ := fun z => cellAverage N (fun y => Real.exp (h₀ y)) z
  let C : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b μ f ω
  let A : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν f ω
  let M : ℝ := Real.exp ‖h₀‖
  have hM : 0 ≤ M := by positivity
  have hν0 : ∀ w, 0 ≤ ν w := by
    intro w
    exact Polymer.kernel_nonneg m (w - x₀)
  have hνsum : (∑' w : Site, ν w) = 1 := by
    simpa [ν, m, x₀] using Polymer.tsum_srwKernel m (latticePoint N x)
  have hνabs : Summable (fun w : Site => |ν w|) :=
    Polymer.summable_probability_profile ν hν0 hνsum
  obtain ⟨hμ0, hμsum, hμabs⟩ := heatKernel_cellMass_probability hδ x
  have hdiffabs : Summable (fun w : Site => |ν w - μ w|) := by
    have hmajor : Summable (fun w : Site => |ν w| + |μ w|) := hνabs.add hμabs
    apply hmajor.of_nonneg_of_le (fun _ => by positivity)
    intro w
    calc
      |ν w - μ w| = |ν w + -μ w| := by rw [sub_eq_add_neg]
      _ ≤ |ν w| + |-μ w| := abs_add_le _ _
      _ = |ν w| + |μ w| := by rw [abs_neg]
  have hf : ∀ z, 0 ≤ f z ∧ f z ≤ M := by
    intro z
    simpa only [f, M] using profile_cellAverage_exp_bounds N hN h₀ z
  have hprofileDiff := memLp_lintegral_abs_profileP2Fun_sub_le
    (criticalBeta ϑ N) a b ν μ f hνabs hμabs hdiffabs M hM hf
  have hsumRepr :
      (∑' w : Site, ENNReal.ofReal |ν w - μ w|) =
        ENNReal.ofReal (∑' w : Site, |ν w - μ w|) := by
    exact (ENNReal.ofReal_tsum_of_nonneg (fun w => abs_nonneg _) hdiffabs).symm
  have hprofileDiff' :
      ∫⁻ ω, ENNReal.ofReal |A ω - C ω| ∂disorderLaw ≤ ENNReal.ofReal (M * η) := by
    calc
      _ ≤ ENNReal.ofReal M * ∑' w, ENNReal.ofReal |ν w - μ w| := hprofileDiff.2
      _ = ENNReal.ofReal M * ENNReal.ofReal (∑' w, |ν w - μ w|) := by rw [hsumRepr]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal η :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hη) (by positivity)
      _ = ENNReal.ofReal (M * η) := (ENNReal.ofReal_mul hM).symm
  have hkerAE := SHF.Positivity.ae_integrable_polymer_heat_start ϑ
    (by exact_mod_cast hN) s T δ hδ x
  have hPairInt : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
        (SHF.Limit.polymerMeasure ϑ N s T ω) := by
    filter_upwards [hkerAE] with ω hker
    have hmeas : AEStronglyMeasurable
        (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
        (SHF.Limit.polymerMeasure ϑ N s T ω) := by
      have hm : Measurable (fun p : Plane × Plane =>
          heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)) := by
        exact ((((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
          (Real.continuous_exp.comp (h₀.continuous.comp continuous_snd))).measurable)
      exact hm.aestronglyMeasurable
    have hmajor : Integrable
        (fun p : Plane × Plane => M * ‖heatKernel δ (p.1 - x)‖)
        (SHF.Limit.polymerMeasure ϑ N s T ω) := by
      simpa [M, mul_comm] using hker.norm.const_mul (Real.exp ‖h₀‖)
    apply hmajor.mono' hmeas
    filter_upwards [] with p
    have hg : ‖Real.exp (h₀ p.2)‖ ≤ M := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        h₀ p.2 ≤ |h₀ p.2| := le_abs_self _
        _ = ‖h₀ p.2‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖h₀‖ := h₀.norm_coe_le_norm p.2
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |heatKernel δ (p.1 - x)| * |Real.exp (h₀ p.2)| ≤
          |heatKernel δ (p.1 - x)| * M :=
        mul_le_mul_of_nonneg_left hg (abs_nonneg _)
      _ = M * ‖heatKernel δ (p.1 - x)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hδ.le _)]
        ring
  have hbridge : ∀ᵐ ω ∂disorderLaw, C ω =
      ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
      ∂(SHF.Limit.polymerMeasure ϑ N s T ω) := by
    filter_upwards [hPairInt] with ω hω
    exact profile_cellHeat_eq_polymerMeasure_pairing ϑ N s T δ x h₀ ω
      (by exact_mod_cast hN) hω
  have hbridgeLin :
      ∫⁻ ω, ENNReal.ofReal |A ω -
          ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
            ∂(SHF.Limit.polymerMeasure ϑ N s T ω)| ∂disorderLaw =
        ∫⁻ ω, ENNReal.ofReal |A ω - C ω| ∂disorderLaw := by
    apply lintegral_congr_ae
    filter_upwards [hbridge] with ω hω
    rw [hω]
  rw [← hbridgeLin] at hprofileDiff'
  have hmem : MemLp (fun ω =>
      A ω - ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(SHF.Limit.polymerMeasure ϑ N s T ω)) 1 disorderLaw := by
    apply (memLp_congr_ae ?_).2 hprofileDiff.1
    filter_upwards [hbridge] with ω hω
    rw [← hω]
  refine ⟨?_, ?_⟩
  · simpa only [A, a, b, m, x₀, ν, μ, f, M] using hmem
  · simpa only [A, a, b, m, x₀, ν, μ, f, M] using hprofileDiff'


/-- The norm of a finite coordinate vector is bounded by its coordinate absolute sum. -/
theorem profile_pi_norm_le_sum_abs {k : ℕ} (v : Fin k → ℝ) :
    ‖v‖ ≤ ∑ i, |v i| := by
  rw [Pi.norm_def]
  have hsum : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsup : Finset.univ.sup (fun i => ‖v i‖₊) ≤ Real.toNNReal (∑ i, |v i|) := by
    apply Finset.sup_le
    intro i hi
    have hsingle : |v i| ≤ ∑ j, |v j| :=
      Finset.single_le_sum (f := fun j : Fin k => |v j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hreal : (↑(‖v i‖₊) : ℝ) ≤ ↑(Real.toNNReal (∑ j, |v j|)) := by
      rw [coe_nnnorm, Real.coe_toNNReal (∑ j, |v j|) hsum]
      simpa only [Real.norm_eq_abs] using hsingle
    exact NNReal.coe_le_coe.mpr hreal
  calc
    ↑(Finset.univ.sup (fun i => ‖v i‖₊)) ≤ ↑(Real.toNNReal (∑ i, |v i|)) :=
      NNReal.coe_le_coe.mpr hsup
    _ = ∑ i, |v i| := Real.coe_toNNReal (∑ i, |v i|) hsum


/-- Coordinate mean-error bounds control the mean norm of a finite vector. -/
theorem profile_lintegral_norm_pi_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (D : Ω → Fin k → ℝ) (hD : AEMeasurable D P)
    (hDint : ∀ i, Integrable (fun ω => ‖D ω i‖) P)
    (B : Fin k → ℝ) (hB : ∀ i, ∫ ω, ‖D ω i‖ ∂P ≤ B i) :
    ∫⁻ ω, ENNReal.ofReal ‖D ω‖ ∂P ≤ ENNReal.ofReal (∑ i, B i) := by
  have hsumInt : Integrable (fun ω => ∑ i : Fin k, ‖D ω i‖) P :=
    integrable_finsetSum Finset.univ (fun i hi => hDint i)
  have hnormInt : Integrable (fun ω => ‖D ω‖) P := by
    apply hsumInt.mono' hD.aestronglyMeasurable.norm
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      profile_pi_norm_le_sum_abs (D ω)
  have hsumBound : ∫ ω, ‖D ω‖ ∂P ≤ ∑ i, B i := by
    calc
      _ ≤ ∫ ω, ∑ i : Fin k, ‖D ω i‖ ∂P := by
        apply integral_mono hnormInt hsumInt
        intro ω
        exact profile_pi_norm_le_sum_abs (D ω)
      _ = ∑ i, ∫ ω, ‖D ω i‖ ∂P := by
        rw [integral_finsetSum Finset.univ (fun i hi => hDint i)]
      _ ≤ ∑ i, B i := Finset.sum_le_sum fun i hi => hB i
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ ‖D ω‖ := Filter.Eventually.of_forall fun ω => norm_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hnormInt hnonneg]
  exact ENNReal.ofReal_le_ofReal hsumBound


/-- Joint convergence of walk-kernel heat-started masses, allowing different
future horizons in every coordinate. -/
theorem profile_heatStart_joint_tendsto (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane) (h₀ : Plane →ᵇ ℝ)
    (hparams : ∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) => profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s i)) (evenCeil (N * t i))
        (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N (x i)))
        (cellAverage N fun y => Real.exp (h₀ y)) ω)
      atTop
      (fun ω i => shfPairing Z (s i) (t i) (fun y => heatKernel (δ i) (y - x i))
        (fun y => Real.exp (h₀ y)) ω) (fun _ => disorderLaw) P := by
  let X := fun (N : ℕ) (ω : Disorder) (i : Fin k) => profileP2Fun (criticalBeta ϑ N)
    (evenCeil (N * s i)) (evenCeil (N * t i))
    (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N (x i)))
    (cellAverage N fun y => Real.exp (h₀ y)) ω
  let Y := fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
    ∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
      ∂(polymerMeasure ϑ N (s i) (t i) ω)
  let L := fun ω i => shfPairing Z (s i) (t i) (fun y => heatKernel (δ i) (y - x i))
    (fun y => Real.exp (h₀ y)) ω
  let g : Plane →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.exp (h₀ y), by fun_prop⟩ (2 * Real.exp ‖h₀‖) (by
      intro y z
      change |Real.exp (h₀ y) - Real.exp (h₀ z)| ≤ 2 * Real.exp ‖h₀‖
      have hy := Real.exp_le_exp.mpr (abs_le.mp (h₀.norm_coe_le_norm y)).2
      have hz := Real.exp_le_exp.mpr (abs_le.mp (h₀.norm_coe_le_norm z)).2
      rw [abs_le]
      constructor <;> linarith [Real.exp_pos (h₀ y), Real.exp_pos (h₀ z)])
  have hY : TendstoInDistribution Y atTop L (fun _ => disorderLaw) P := by
    exact SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
      k s t δ x (fun _ => g) hparams
  have hXm (N : ℕ) : AEMeasurable (X N) disorderLaw := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact (Polymer.measurable_profileP2Fun _ _ _ _ _).aemeasurable
  apply tendstoInDistribution_of_approx X (fun _ => Y) (fun _ => L) L
    (fun _ => hY) _ _ hXm hY.aemeasurable_limit
  · intro e he
    exact Eventually.of_forall fun _ => by simp
  · intro e he
    let η : ℝ := e / (((k : ℝ) + 1) * Real.exp ‖h₀‖)
    have hη : 0 < η := by dsimp only [η]; positivity
    have hkernels : ∀ᶠ N : ℕ in atTop, ∀ i : Fin k,
        ∑' w : Site, |srwKernel (evenCeil ((N : ℝ) * δ i)) (w - latticePoint N (x i)) -
          ∫ y in cell N w, heatKernel (δ i) (y - x i)| ≤ η :=
      Filter.eventually_all.mpr fun i =>
        (srwKernel_sub_cellHeat_l1_le (δ i) (hparams i).2.2 η hη).mono fun N hN => hN (x i)
    apply Eventually.of_forall
    intro j
    filter_upwards [hkernels, eventually_ge_atTop 1] with N hK hN
    let D := fun ω => X N ω - Y N ω
    have herror (i : Fin k) := profile_heatStart_pairing_error ϑ hN
      (s i) (t i) (δ i) (hparams i).2.2 (x i) h₀ η (hK i)
    have hDint (i : Fin k) : Integrable (fun ω => ‖D ω i‖) disorderLaw :=
      (herror i).1.integrable (by norm_num) |>.norm
    have hB (i : Fin k) : (∫ ω, ‖D ω i‖ ∂disorderLaw) ≤ Real.exp ‖h₀‖ * η := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ Real.exp ‖h₀‖ * η)).mp
      rw [ofReal_integral_eq_lintegral_ofReal (hDint i) (Eventually.of_forall fun _ => norm_nonneg _)]
      exact (herror i).2
    have hvec := profile_lintegral_norm_pi_le disorderLaw D
      ((hXm N).sub (hY.forall_aemeasurable N)) hDint (fun _ => Real.exp ‖h₀‖ * η) hB
    apply hvec.trans
    apply ENNReal.ofReal_le_ofReal
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [η]
    have hkp : 0 < (k : ℝ) + 1 := by positivity
    calc
      _ = (k : ℝ) * e / ((k : ℝ) + 1) := by
        field_simp [Real.exp_ne_zero _]
      _ ≤ e := (div_le_iff₀ hkp).mpr (by nlinarith only [he])

/-- Even lattice horizons are fixed by even rounding. -/
theorem profile_evenCeil_natCast {N : ℕ} (hN : Even N) : evenCeil (N : ℝ) = N := by
  obtain ⟨d, hd⟩ := hN
  have hhalf : (N : ℝ) / 2 = d := by rw [hd, Nat.cast_add]; ring
  rw [evenCeil, hhalf, Nat.ceil_natCast]
  omega

/-- Counting backwards from the horizon identifies the block grid with
fixed macroscopic geometric times, including the terminal horizon itself. -/
theorem profile_blockTime_from_horizon {N k : ℕ} {ρ : ℝ}
    (hN : Even N) (hk : k < blockCount N ρ) :
    blockTime N ρ (blockCount N ρ - k) = evenCeil ((N : ℝ) * ρ ^ (-(k : ℝ))) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.sub_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
    rw [profile_evenCeil_natCast hN]
    simp only [blockTime, ite_eq_right (Nat.ne_of_gt hk), lt_self_iff_false, ite_false]
  · have hidx : blockCount N ρ - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hk)
    have hidxK : blockCount N ρ - k < blockCount N ρ := by omega
    simp only [blockTime, ite_eq_right hidx, ite_eq_left hidxK]
    rw [Nat.cast_sub hk.le]
    congr 2
    ring_nf

/-- Flat-terminal walk heat-start approximants are the smoothed lattice
masses, with the parity-correct cell averages removed. -/
theorem profile_heatStart_approximant_eq_mass (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {s t : ℝ} (hst : s ≤ t) (x : Plane) (ω : Disorder) :
    profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
      (fun w => srwKernel (evenCeil (N * s)) (w - latticePoint N x))
      (cellAverage N fun _ : Plane => 1) ω =
        smoothedP2Plane (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
          (latticePoint N x) ω := by
  have hclock : evenCeil (N * s) ≤ evenCeil (N * t) :=
    evenCeil_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N))
  rw [NonGaussian.heatStartWalkProfile_cellAverage_one_eq _ hN hclock
    (evenCeil_even _) (Smoothing.evenCeil_sub_even (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N)))]
  exact profileHeatMass_lattice _ _ _ _ _

/-- The truncated profile comparison on a geometric grid at a unit horizon.
Its constants are uniform in both entrance indices and in the chosen
shorter future horizon. -/
theorem profile_comparison_flow_grid (A : ℝ) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ Cr Co Cb : ℝ, 0 ≤ Cr ∧ 0 ≤ Co ∧ 0 ≤ Cb ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ), ϑ ∈ Set.Icc (-A) A →
      IsCriticalSHF ϑ P Z → ∀ ka km kn kT : ℕ,
        km ≤ ka → kn < km → 2 ≤ kn → kT ≤ kn → ∀ x : Plane, ∀ M : ℝ, 0 ≤ M →
          (∫ ω, min |profileMass Z (ρ ^ (-(ka : ℝ))) (ρ ^ (-(kn : ℝ))) (ρ ^ (-(kT : ℝ))) x ω -
            profileMass Z (ρ ^ (-(km : ℝ))) (ρ ^ (-(kn : ℝ))) (ρ ^ (-(kT : ℝ))) x ω| M ∂P) ≤
            Cr / ((kn : ℝ) * Real.sqrt kn) + Co * q ^ (km - kn) / Real.sqrt kn + Cb * M / kn := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hq1, hLattice⟩ := profile_comparison_lattice_truncated A
  refine ⟨ρ₀, q, hρ₀, hq0, hq1, ?_⟩
  intro ρ hρ
  have hρ1 := hρ₀.trans_le hρ
  obtain ⟨Cr, Co, Cb, hCr, hCo, hCb, hRate⟩ := hLattice ρ hρ
  refine ⟨Cr, Co, Cb, hCr, hCo, hCb, ?_⟩
  intro Ω _ P _ Z ϑ hϑ hZ ka km kn kT hma hnm hn2 hTn x M hM
  let τ := fun k : ℕ => ρ ^ (-(k : ℝ))
  have hτpos (k : ℕ) : 0 < τ k := Real.rpow_pos_of_pos (by linarith : 0 < ρ) _
  have hτanti : Antitone τ := fun i j hij =>
    Real.rpow_le_rpow_of_exponent_le hρ1.le
      (neg_le_neg (show (i : ℝ) ≤ j by exact_mod_cast hij))
  have hmn : τ km < τ kn := Real.rpow_lt_rpow_of_exponent_lt hρ1
    (neg_lt_neg (show (kn : ℝ) < km by exact_mod_cast hnm))
  have han : τ ka < τ kn := (hτanti hma).trans_lt hmn
  have hnT : τ kn ≤ τ kT := hτanti hTn
  let s : Fin 4 → ℝ := ![τ ka, τ ka, τ km, τ km]
  let t : Fin 4 → ℝ := ![τ kT, τ kn, τ kT, τ kn]
  have hparams : ∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < s i := by
    intro i
    fin_cases i
    · exact ⟨(hτpos ka).le, han.trans_le hnT, hτpos ka⟩
    · exact ⟨(hτpos ka).le, han, hτpos ka⟩
    · exact ⟨(hτpos km).le, hmn.trans_le hnT, hτpos km⟩
    · exact ⟨(hτpos km).le, hmn, hτpos km⟩
  let X := fun (N : ℕ) (ω : Disorder) (i : Fin 4) => profileP2Fun (criticalBeta ϑ N)
    (evenCeil (N * s i)) (evenCeil (N * t i))
    (fun w => srwKernel (evenCeil (N * s i)) (w - latticePoint N x))
    (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω
  let Y := fun (ω : Ω) (i : Fin 4) => shfPairing Z (s i) (t i)
    (fun y => heatKernel (s i) (y - x)) (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω
  have hd : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P :=
    profile_heatStart_joint_tendsto ϑ P Z hZ 4 s t s (fun _ => x) 0 hparams
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n) tendsto_id
  have hdEven : TendstoInDistribution (fun n => X (2 * n)) atTop Y (fun _ => disorderLaw) P :=
    ⟨fun n => hd.forall_aemeasurable (2 * n), hd.aemeasurable_limit, hd.tendsto.comp heven⟩
  have hpos : ∀ᵐ ω ∂P, 0 < Y ω 1 ∧ 0 < Y ω 3 := by
    have ha := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
      (τ ka) (τ kn) (τ ka) x 0 (hτpos ka).le han (hτpos ka)
    have hm := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
      (τ km) (τ kn) (τ km) x 0 (hτpos km).le hmn (hτpos km)
    filter_upwards [ha.1, hm.1] with ω haω hmω
    exact ⟨haω, hmω⟩
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∫ ω, profileRatioCap M (X (2 * n) ω) ∂disorderLaw) ≤
        Cr / ((kn : ℝ) * Real.sqrt kn) + Co * q ^ (km - kn) / Real.sqrt kn + Cb * M / kn := by
    have hK := (Blocks.blockCount_tendsto_atTop hρ1).eventually (eventually_gt_atTop ka)
    have hlarge := heven.eventually (hRate.and ((Blocks.blockTime_monotone hρ1).and hK))
    filter_upwards [hlarge, eventually_ge_atTop 1] with n hlarge hn
    let N := 2 * n
    let K := blockCount N ρ
    let r := K - ka + 1
    let m := K - km + 1
    let j := K - kn
    have hNEven : Even N := ⟨n, by dsimp only [N]; omega⟩
    have hN : 0 < N := by dsimp only [N]; omega
    obtain ⟨hR, ht, hK⟩ := hlarge
    have hka : ka < K := hK
    have hclock (k : ℕ) (hk : k ≤ ka) : blockTime N ρ (K - k) = evenCeil (N * τ k) :=
      profile_blockTime_from_horizon hNEven (lt_of_le_of_lt hk hka)
    have hterminal : blockTime N ρ K = N := by
      simp [K, blockTime, Nat.ne_of_gt (by omega : 0 < blockCount N ρ)]
    have hobs : blockTime N ρ j ≤ evenCeil (N * τ kT) := by
      rw [← hclock kT (by omega)]
      exact ht (by dsimp only [j]; omega)
    have hfuture : evenCeil (N * τ kT) ≤ N := by
      rw [← hclock kT (by omega)]
      exact (ht (Nat.sub_le K kT)).trans_eq hterminal
    have h := hR ϑ hϑ r m j (evenCeil (N * τ kT)) (by dsimp only [r]; omega)
      (by dsimp only [r, m]; omega) (by dsimp only [m, j]; omega)
      (by change j + 2 ≤ K; dsimp only [j]; omega) hobs hfuture (latticePoint N x) M hM
    have hD : (K : ℝ) - j = (kn : ℝ) := by
      dsimp only [j]
      rw [Nat.cast_sub (by omega : kn ≤ K)]
      ring
    have hpad : j - m + 1 = km - kn := by dsimp only [j, m]; omega
    have hrclock : blockTime N ρ (r - 1) = evenCeil (N * τ ka) := by
      rw [show r - 1 = K - ka by dsimp only [r]; omega]
      exact hclock ka le_rfl
    have hmclock : blockTime N ρ (m - 1) = evenCeil (N * τ km) := by
      rw [show m - 1 = K - km by dsimp only [m]; omega]
      exact hclock km hma
    have hjclock : blockTime N ρ j = evenCeil (N * τ kn) := hclock kn (by omega)
    change (∫ ω, profileRatioCap M (X N ω) ∂disorderLaw) ≤ _
    convert h using 1
    · apply integral_congr_ae
      filter_upwards [] with ω
      change min |profileP2Fun _ _ _ _ _ ω / profileP2Fun _ _ _ _ _ ω -
        profileP2Fun _ _ _ _ _ ω / profileP2Fun _ _ _ _ _ ω| M = _
      dsimp [s, t]
      simp only [Real.exp_zero]
      rw [profile_heatStart_approximant_eq_mass ϑ hN (han.trans_le hnT).le,
        profile_heatStart_approximant_eq_mass ϑ hN han.le,
        profile_heatStart_approximant_eq_mass ϑ hN (hmn.trans_le hnT).le,
        profile_heatStart_approximant_eq_mass ϑ hN hmn.le,
        hrclock, hmclock, hjclock]
    · change _ = Cr / (((K : ℝ) - j) * Real.sqrt ((K : ℝ) - j)) +
        Co * q ^ (j - m + 1) / Real.sqrt ((K : ℝ) - j) + Cb * M / ((K : ℝ) - j)
      rw [hD, hpad]
  have hcap := profile_ratio_cap_integral_le_of_tendstoInDistribution hdEven hpos hM hbound
  simpa [profileRatioCap, Y, s, t, profileMass, τ] using hcap

/-- The profile comparison at exponential horizon `c exp l`, obtained by
pathwise scaling from the fixed-parameter unit-horizon estimate. -/
theorem profile_comparison_flow {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ Cr Co Cb : ℝ, 0 ≤ Cr ∧ 0 ≤ Co ∧ 0 ≤ Cb ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (l : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ ka km kn kT : ℕ, km ≤ ka → kn < km → 2 ≤ kn → kT ≤ kn →
      ∀ x : Plane, ∀ M : ℝ, 0 ≤ M →
        (∫ ω, min
          |profileMass Z (c * Real.exp l * ρ ^ (-(ka : ℝ)))
              (c * Real.exp l * ρ ^ (-(kn : ℝ))) (c * Real.exp l * ρ ^ (-(kT : ℝ))) x ω -
            profileMass Z (c * Real.exp l * ρ ^ (-(km : ℝ)))
              (c * Real.exp l * ρ ^ (-(kn : ℝ))) (c * Real.exp l * ρ ^ (-(kT : ℝ))) x ω| M ∂P) ≤
          Cr / ((kn : ℝ) * Real.sqrt kn) + Co * q ^ (km - kn) / Real.sqrt kn + Cb * M / kn := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hq1, hBound⟩ := profile_comparison_flow_grid |Real.log c|
  refine ⟨ρ₀, q, hρ₀, hq0, hq1, ?_⟩
  intro ρ hρ
  obtain ⟨Cr, Co, Cb, hCr, hCo, hCb, hB⟩ := hBound ρ hρ
  refine ⟨Cr, Co, Cb, hCr, hCo, hCb, ?_⟩
  intro Ω _ P _ l Z hZ ka km kn kT hma hnm hn2 hTn x M hM
  let H := c * Real.exp l
  have hH : 0 < H := mul_pos hc (Real.exp_pos l)
  let Z' := fun s t ω => ENNReal.ofReal H⁻¹ • (Z (H * s) (H * t) ω).map
    (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2))
  have hZ' : IsCriticalSHF (Real.log c) P Z' := isCriticalSHF_profile_horizon_scaled P hc Z hZ
  have h := hB P Z' (Real.log c) ⟨neg_abs_le _, le_abs_self _⟩ hZ'
    ka km kn kT hma hnm hn2 hTn ((Real.sqrt H)⁻¹ • x) M hM
  have hdiv (b : ℝ) : H * b / H = b := by field_simp
  have hscale (k : ℕ) (ω : Ω) :
      profileMass Z' (ρ ^ (-(k : ℝ))) (ρ ^ (-(kn : ℝ))) (ρ ^ (-(kT : ℝ)))
        ((Real.sqrt H)⁻¹ • x) ω =
      profileMass Z (H * ρ ^ (-(k : ℝ))) (H * ρ ^ (-(kn : ℝ))) (H * ρ ^ (-(kT : ℝ))) x ω := by
    simpa only [hdiv] using profileMass_scaled_eq Z hH
      (H * ρ ^ (-(k : ℝ))) (H * ρ ^ (-(kn : ℝ))) (H * ρ ^ (-(kT : ℝ))) x ω
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [hscale ka ω, hscale km ω]

/-- The remaining real block count agrees exactly with the integer index
on the exponential geometric grid. -/
theorem profile_grid_remaining_blocks {H ρ : ℝ} (hH : 0 < H) (hρ : 1 < ρ) (k : ℕ) :
    Real.logb ρ (H / (H * ρ ^ (-(k : ℝ)))) = k := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  rw [Real.rpow_neg hρ0.le]
  have hratio : H / (H * (ρ ^ (k : ℝ))⁻¹) = ρ ^ (k : ℝ) := by
    field_simp [ne_of_gt hH, ne_of_gt (Real.rpow_pos_of_pos hρ0 (k : ℝ))]
  rw [hratio, Real.logb_rpow hρ0 (ne_of_gt hρ)]

/-- The capped profile comparison at the polynomial observation horizon,
uniformly over all earlier entrances and at either future horizon. -/
theorem profile_comparison_polynomial_horizon {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ Cr Co Cb : ℝ, 0 ≤ Cr ∧ 0 ≤ Co ∧ 0 ≤ Cb ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ j : ℕ, ∀ T : ℝ, T = S c ρ q l ∨ T = c * Real.exp l →
      ∀ x : Plane, ∀ M : ℝ, 0 ≤ M →
        let D := Real.logb ρ (c * Real.exp l / S c ρ q l)
        (∫ ω, min |profileMass Z (gridEntrance c ρ l j) (S c ρ q l) T x ω -
          profileMass Z (gridPoint c ρ l) (S c ρ q l) T x ω| M ∂P) ≤
          Cr / (D * Real.sqrt D) + Co * q ^ gridJ q l / Real.sqrt D + Cb * M / D := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hBound⟩ := profile_comparison_flow hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle
  obtain ⟨Cr, Co, Cb, hCr, hCo, hCb, hB⟩ := hBound ρ hρle
  have hρ : 1 < ρ := hρ₀.trans_le hρle
  have hρ0 := zero_lt_one.trans hρ
  refine ⟨Cr, Co, Cb, hCr, hCo, hCb, ?_⟩
  filter_upwards [eventually_gridJ_le_gridIndex hc hρ hq0 hqHalf,
    eventually_grid_remaining_ge_two hc hρ hq0 hqHalf,
    eventually_gt_atTop (1 : ℝ)] with l hJ hkn hl
  intro Ω _ P _ Z hZ j T hT x M hM
  let km := gridIndex c ρ l
  let kn := gridIndex c ρ l - gridJ q l
  have hJpos := gridJ_pos hq0 (by linarith : q < 1) hl
  have hnm : kn < km := by dsimp [kn, km]; omega
  have hS : S c ρ q l = c * Real.exp l * ρ ^ (-(kn : ℝ)) :=
    gridHorizon_eq_geometric hρ0 hJ
  have hE : gridEntrance c ρ l j = c * Real.exp l * ρ ^ (-((km + j : ℕ) : ℝ)) :=
    gridEntrance_eq_geometric hρ0 j
  have hp : gridPoint c ρ l = c * Real.exp l * ρ ^ (-(km : ℝ)) := by
    simpa only [gridEntrance, pow_zero, div_one, Nat.add_zero] using
      (gridEntrance_eq_geometric (c := c) (l := l) hρ0 0)
  have hpad : km - kn = gridJ q l := by dsimp [km, kn]; omega
  have hD : Real.logb ρ (c * Real.exp l / S c ρ q l) = (kn : ℝ) := by
    rw [hS]
    exact profile_grid_remaining_blocks (mul_pos hc (Real.exp_pos l)) hρ kn
  have hgeneric (kT : ℕ) (hTn : kT ≤ kn) :=
    hB P l Z hZ (km + j) km kn kT (by omega) hnm hkn hTn x M hM
  dsimp only
  rw [hD]
  rcases hT with rfl | rfl
  · simpa only [← hS, ← hE, ← hp, hpad] using hgeneric kn le_rfl
  · simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, ← hS, ← hE, ← hp, hpad]
      using hgeneric 0 (Nat.zero_le kn)

/-- A linear remaining-block lower bound converts the grid estimate to
the scale used in localisation. -/
theorem profile_comparison_rate_arithmetic {Cr Co Cb b l D v M : ℝ}
    (hCr : 0 ≤ Cr) (hCo : 0 ≤ Co) (hCb : 0 ≤ Cb) (hb : 0 < b)
    (hl : 0 < l) (hD : b * l ≤ D) (hv : v ≤ l⁻¹) (hM : 0 ≤ M) :
    Cr / (D * Real.sqrt D) + Co * v / Real.sqrt D + Cb * M / D ≤
      (Cr / (b * Real.sqrt b) + Co / Real.sqrt b + Cb / b) / (l * Real.sqrt l) +
      (Cr / (b * Real.sqrt b) + Co / Real.sqrt b + Cb / b) * M / l := by
  have hD0 : 0 < D := (mul_pos hb hl).trans_le hD
  have hroot : Real.sqrt b * Real.sqrt l ≤ Real.sqrt D := by
    rw [← Real.sqrt_mul hb.le]
    exact Real.sqrt_le_sqrt hD
  have hprod : (b * Real.sqrt b) * (l * Real.sqrt l) ≤ D * Real.sqrt D := by
    have h := mul_le_mul hD hroot (by positivity) hD0.le
    nlinarith only [h]
  have h1 : Cr / (D * Real.sqrt D) ≤ (Cr / (b * Real.sqrt b)) / (l * Real.sqrt l) := by
    convert div_le_div_of_nonneg_left hCr (by positivity : 0 < (b * Real.sqrt b) * (l * Real.sqrt l)) hprod using 1; ring
  have h2 : Co * v / Real.sqrt D ≤ (Co / Real.sqrt b) / (l * Real.sqrt l) := by
    calc
      _ ≤ Co * l⁻¹ / Real.sqrt D := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv hCo) (Real.sqrt_nonneg D)
      _ ≤ Co * l⁻¹ / (Real.sqrt b * Real.sqrt l) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hroot
      _ = _ := by ring
  have h3 : Cb * M / D ≤ (Cb / b) * M / l := by
    convert div_le_div_of_nonneg_left (mul_nonneg hCb hM) (mul_pos hb hl) hD using 1; ring
  have h4 : 0 ≤ (Cb / b) / (l * Real.sqrt l) := by positivity
  have h5 : 0 ≤ (Cr / (b * Real.sqrt b) + Co / Real.sqrt b) * M / l := by positivity
  calc
    _ ≤ (Cr / (b * Real.sqrt b)) / (l * Real.sqrt l) +
        (Co / Real.sqrt b) / (l * Real.sqrt l) + (Cb / b) * M / l :=
      add_le_add (add_le_add h1 h2) h3
    _ ≤ ((Cr / (b * Real.sqrt b)) / (l * Real.sqrt l) +
        (Co / Real.sqrt b) / (l * Real.sqrt l) + (Cb / b) * M / l) +
        (Cb / b) / (l * Real.sqrt l) +
        (Cr / (b * Real.sqrt b) + Co / Real.sqrt b) * M / l := by linarith only [h4, h5]
    _ = _ := by ring

/-- The capped profile comparison has rate `l^(-3/2) + M/l` uniformly
in the entrance and at either future horizon. -/
theorem profile_comparison_localisation_rate {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ j : ℕ, ∀ T : ℝ, T = S c ρ q l ∨ T = c * Real.exp l →
      ∀ x : Plane, ∀ M : ℝ, 0 ≤ M →
        (∫ ω, min |profileMass Z (gridEntrance c ρ l j) (S c ρ q l) T x ω -
          profileMass Z (gridPoint c ρ l) (S c ρ q l) T x ω| M ∂P) ≤
            C / (l * Real.sqrt l) + C * M / l := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hBound⟩ := profile_comparison_polynomial_horizon hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle
  have hρ := hρ₀.trans_le hρle
  obtain ⟨Cr, Co, Cb, hCr, hCo, hCb, hBound⟩ := hBound ρ hρle
  obtain ⟨b, hb, hLower⟩ := grid_blockCount_lower hc hρ hq0 hqHalf
  refine ⟨Cr / (b * Real.sqrt b) + Co / Real.sqrt b + Cb / b, by positivity, ?_⟩
  filter_upwards [hBound, hLower, eventually_ge_atTop (1 : ℝ)] with l hBound hLower hl1
  intro Ω _ P _ Z hZ j T hT x M hM
  have hl : 0 < l := by linarith
  have hS := gridHorizon_pos hc (zero_lt_one.trans hρ) q l
  have hD := hLower (S c ρ q l) hS le_rfl
  have hv : q ^ gridJ q l ≤ l⁻¹ := by
    have h := pow_gridJ_le_inv_sq hq0 (by linarith : q < 1) hl
    have hinv : l⁻¹ ≤ 1 := (inv_le_one₀ hl).mpr hl1
    nlinarith only [h, hinv, inv_nonneg.mpr hl.le]
  exact (hBound P Z hZ j T hT x M hM).trans
    (profile_comparison_rate_arithmetic hCr hCo hCb hb hl hD hv hM)


end Critical2DKPZ.Extensions.GffTangent

end
