/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartProfileApprox
public import Critical2DKPZ.JointConvergence.HeatKernelCellApprox
public import Critical2DKPZ.JointConvergence.HeatStartLogTails
import Critical2DKPZ.SHF.Positivity.HeatStartMean
import Critical2DKPZ.Smoothing.ParityHelpers
import Critical2DKPZ.Polymer.ProbabilityProfiles
import Mathlib.Tactic

/-! # Walk-kernel to heat-cell approximation of lattice masses

The mass-error argument is reproduced from the private helper in
`JointConvergence.HeatStartLogConvergence`. Unlike its logarithmic consumer,
this estimate needs no inverse moments or logarithmic tail control.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.JointConvergence
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

private theorem cellAverage_exp_nonneg_le (N : ℕ) (hN : 1 ≤ N) (h₀ : Plane →ᵇ ℝ)
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
theorem heatStart_profile_mass_error (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
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
    simpa only [f, M] using cellAverage_exp_nonneg_le N hN h₀ z
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


end Critical2DKPZ.Extensions.ScaleLimit
