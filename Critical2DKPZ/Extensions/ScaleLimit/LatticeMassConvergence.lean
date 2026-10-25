/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LatticeMassApprox
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.ShfPairing
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Mathlib.Tactic

/-! # Joint convergence of walk-smoothed lattice masses

At each fixed finite set of time intervals, the total mean kernel error vanishes.
Slutsky then transports joint convergence of heat-cell pairings to the walk starts.
The endpoints may vary across the finite family.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.JointConvergence
open scoped ENNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A walk-smoothed lattice mass, with the cell average of terminal weight one. -/
def latticeHeatMass (ϑ : ℝ) (N : ℕ) (s t δ : ℝ) (x : Plane) (ω : Disorder) : ℝ :=
  profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
    (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
    (cellAverage N (fun _ => 1)) ω

/-- Mean absolute errors on finitely many coordinates control the mean norm. -/
theorem lintegral_norm_pi_le_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {k : ℕ} (D : Ω → Fin k → ℝ) (hm : AEMeasurable D P) :
    (∫⁻ ω, ENNReal.ofReal ‖D ω‖ ∂P) ≤
      ∑ i, ∫⁻ ω, ENNReal.ofReal |D ω i| ∂P := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (∑ i, |D ω i|) ∂P := by
      apply lintegral_mono
      intro ω
      apply ENNReal.ofReal_le_ofReal
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr
      intro i
      simpa only [Real.norm_eq_abs] using
        (Finset.single_le_sum (f := fun i : Fin k => |D ω i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ i))
    _ = ∫⁻ ω, ∑ i, ENNReal.ofReal |D ω i| ∂P := by
      congr 1
      funext ω
      exact ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ = _ := lintegral_finsetSum' _ (fun i _ =>
      ((aemeasurable_pi_iff.mp hm) i).abs.ennreal_ofReal)

/-- The walk starts and heat-cell starts have vanishing joint `L¹` error. -/
theorem latticeHeatMass_error_tendsto {k : ℕ} (ϑ : ℝ)
    (s t δ : Fin k → ℝ) (x : Fin k → Plane) (hδ : ∀ i, 0 < δ i) :
    Tendsto (fun N => eLpNorm (fun ω i => latticeHeatMass ϑ N (s i) (t i) (δ i) (x i) ω -
      ∫ p, heatKernel (δ i) (p.1 - x i) ∂(polymerMeasure ϑ N (s i) (t i) ω)) 1 disorderLaw)
      atTop (𝓝 0) := by
  let X : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    latticeHeatMass ϑ N (s i) (t i) (δ i) (x i) ω
  let W : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ p, heatKernel (δ i) (p.1 - x i) ∂(polymerMeasure ϑ N (s i) (t i) ω)
  have hXm (N : ℕ) : AEMeasurable (X N) disorderLaw := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact (Polymer.measurable_profileP2Fun _ _ _ _ _).aemeasurable
  have hWm (N : ℕ) (hN : 1 ≤ N) : AEMeasurable (W N) disorderLaw := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact (SHF.Positivity.integral_polymer_heat_start_pairing_eq_one ϑ
      hN (s i) (t i) (δ i) (hδ i) (x i)).1.aemeasurable
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  let η : ℝ := (r : ℝ) / ((k : ℝ) + 1)
  have hη : 0 < η := div_pos hrR (by positivity)
  have hkernel : ∀ᶠ N : ℕ in atTop, ∀ i : Fin k,
      ∑' w : Site, |srwKernel (evenCeil ((N : ℝ) * δ i)) (w - latticePoint N (x i)) -
        ∫ y in cell N w, heatKernel (δ i) (y - x i)| ≤ η := by
    apply Filter.eventually_all.mpr
    intro i
    exact (srwKernel_sub_cellHeat_l1_le (δ i) (hδ i) η hη).mono fun N hN => hN (x i)
  filter_upwards [eventually_ge_atTop 1, hkernel] with N hN hK
  have heach (i : Fin k) : (∫⁻ ω, ENNReal.ofReal |X N ω i - W N ω i| ∂disorderLaw) ≤
      ENNReal.ofReal η := by
    have h := (heatStart_profile_mass_error ϑ hN (s i) (t i) (δ i) (hδ i) (x i) 0 η (hK i)).2
    simpa only [X, W, latticeHeatMass, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      Real.exp_zero, norm_zero, mul_one, one_mul] using h
  have hD : AEMeasurable (fun ω => X N ω - W N ω) disorderLaw :=
    (hXm N).sub (hWm N hN)
  change eLpNorm (fun ω => X N ω - W N ω) 1 disorderLaw ≤ ε
  rw [eLpNorm_one_eq_lintegral_enorm hD.aestronglyMeasurable]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal ‖X N ω - W N ω‖ ∂disorderLaw := by
      simp only [ofReal_norm]
    _ ≤ ∑ i, ∫⁻ ω, ENNReal.ofReal |X N ω i - W N ω i| ∂disorderLaw :=
      lintegral_norm_pi_le_sum disorderLaw _ hD
    _ ≤ ∑ _i : Fin k, ENNReal.ofReal η := Finset.sum_le_sum fun i _ => heach i
    _ = ENNReal.ofReal ((k : ℝ) * η) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hη.le)]
      simp
    _ ≤ (r : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      dsimp [η]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
      nlinarith
    _ ≤ ε := hrε.le

/-- A finite family of walk-smoothed masses converges jointly to the corresponding
heat-start flow masses. No logarithmic moment assumption is needed. -/
theorem latticeHeatMass_joint_tendsto (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
    (h : ∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) :
    TendstoInDistribution
      (fun N ω i => latticeHeatMass ϑ N (s i) (t i) (δ i) (x i) ω) atTop
      (fun ω i => shfPairing Z (s i) (t i) (fun y => heatKernel (δ i) (y - x i))
        (fun _ => 1) ω) (fun _ => disorderLaw) P := by
  have hraw := SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
    k s t δ x (fun _ => 1) h
  have hone : ((1 : Plane →ᵇ ℝ) : Plane → ℝ) = fun _ => 1 := by
    funext y
    simp
  have hraw' : TendstoInDistribution
      (fun N ω i => ∫ p, heatKernel (δ i) (p.1 - x i) ∂(polymerMeasure ϑ N (s i) (t i) ω))
      atTop (fun ω i => shfPairing Z (s i) (t i) (fun y => heatKernel (δ i) (y - x i))
        (fun _ => 1) ω) (fun _ => disorderLaw) P := by
    simpa only [hone, mul_one] using hraw
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hraw'
  · apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
    convert! (latticeHeatMass_error_tendsto ϑ s t δ x (fun i => (h i).2.2)) using 1
    funext N
    congr 1
    funext ω i
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
  · intro N
    apply aemeasurable_pi_iff.mpr
    intro i
    exact (Polymer.measurable_profileP2Fun _ _ _ _ _).aemeasurable

end Critical2DKPZ.Extensions.ScaleLimit
