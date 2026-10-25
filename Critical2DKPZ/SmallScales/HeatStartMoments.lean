/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.Basic
public import Critical2DKPZ.SmallScales.Inputs
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.OnePoint.SecondMoment
import Critical2DKPZ.JointConvergence.MomentConvergence
import Critical2DKPZ.MomentBounds.AiiKSmoothedShift
import Critical2DKPZ.Smoothing.TimeShiftEnvironment
import Critical2DKPZ.FutureProfiles.EndpointTranslation
import Critical2DKPZ.Analysis.Lattice.Basic
import Critical2DKPZ.LogNormality.LatticeInputs
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Critical2DKPZ.SHF.Positivity.PolymerHeatSecondMoment
import Critical2DKPZ.SHF.Positivity.HeatStartMean
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Critical2DKPZ.SmallScales.GaussianJensen
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic

/-! # Moments of heat-start pairings -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Positivity Critical2DKPZ.SHF.Limit
open Critical2DKPZ.JointConvergence
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.SmallScales

/-- The heat-start pairing has integrable mass and annealed mean one. -/
theorem heatStart_integral_eq_one (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {s T δ : ℝ} (hs : 0 ≤ s) (hsT : s < T)
    (hδ : 0 < δ) (x : Plane) :
    Integrable
        (fun ω => shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω) P ∧
      ∫ ω, shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω ∂P = 1 := by
  let X : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s T ω)
  let Y : Ω → ℝ := fun ω =>
    shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
  have hg : ((1 : Plane →ᵇ ℝ) : Plane → ℝ) = fun _ => (1 : ℝ) := by
    funext y
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply]
  have hpair := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hsT hδ x
    (1 : Plane →ᵇ ℝ)
  have hdist : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P := by
    simpa only [X, Y, hg, mul_one] using hpair.2.2.2
  obtain ⟨C, hC⟩ := polymer_heat_pairing_sq_integral_bounded ϑ hs hsT hδ x
  have hXnonneg (N : ℕ) (ω : Disorder) : 0 ≤ X N ω :=
    integral_nonneg fun p => heatKernel_nonneg hδ.le (p.1 - x)
  have hpow (N : ℕ) (ω : Disorder) :
      |X N ω| ^ ((2 : ℕ) : ℝ) = X N ω ^ 2 := by
    rw [Real.rpow_natCast, abs_of_nonneg (hXnonneg N ω)]
  have hmoment : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |X N ω| ^ ((2 : ℕ) : ℝ) ∂disorderLaw ≤ C := by
    filter_upwards [hC] with N hN
    calc
      ∫ ω, |X N ω| ^ ((2 : ℕ) : ℝ) ∂disorderLaw =
          ∫ ω, X N ω ^ 2 ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact hpow N ω
      _ ≤ C := by simpa only [X] using hN.2
  have hint : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω| ^ ((2 : ℕ) : ℝ)) disorderLaw := by
    filter_upwards [hC] with N hN
    have heq : (fun ω => |X N ω| ^ ((2 : ℕ) : ℝ)) = fun ω =>
        (∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s T ω)) ^ 2 := by
      funext ω
      simpa only [X] using hpow N ω
    rw [heq]
    exact hN.1
  have hmeanTend : Tendsto (fun N => ∫ ω, X N ω ∂disorderLaw) atTop
      (𝓝 (∫ ω, Y ω ∂P)) :=
    tendsto_integral_of_tendstoInDistribution hdist (by norm_num : 1 < ((2 : ℕ) : ℝ)) hmoment hint
  have hmeanEq (N : ℕ) (hN : 1 ≤ N) : ∫ ω, X N ω ∂disorderLaw = 1 := by
    have h := integral_polymer_heat_start_pairing_eq_one ϑ hN s T δ hδ x
    simpa only [X] using h.2
  have hmeanOne : Tendsto (fun N => ∫ ω, X N ω ∂disorderLaw) atTop (𝓝 (1 : ℝ)) := by
    have heq : (fun N => ∫ ω, X N ω ∂disorderLaw) =ᶠ[atTop] fun _ => 1 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact hmeanEq N hN
    exact tendsto_const_nhds.congr' heq.symm
  have hYmean : ∫ ω, Y ω ∂P = 1 := tendsto_nhds_unique hmeanTend hmeanOne
  exact ⟨by simpa only [Y, hg] using hpair.2.1,
    by simpa only [Y] using hYmean⟩

private theorem profile_cellAverage_one_eq (β : ℝ) {N : ℕ} (hN : 0 < N)
    (a b m : ℕ) (hm : Even (m : ℤ)) (hd : Even ((b - a : ℕ) : ℤ))
    (x : Plane) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x))
        (cellAverage N fun _ : Plane => 1) ω =
      profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x)) (fun _ => 1) ω := by
  let x₀ : Site := latticePoint N x
  let A : Finset Site := Polymer.endpoints x₀ m
  have hxEven : Even (x₀ 0 + x₀ 1) := Critical2DKPZ.latticePoint_mem_evenLattice N x
  have hkernel (w : Site) (hw : w ∉ A) : srwKernel m (w - x₀) = 0 := by
    exact Polymer.srwKernel_eq_zero_of_not_mem m x₀ w hw
  have hterminal (w : Site) (hw : w ∈ A) :
      (∑' y : Site, pointToPoint β a (b - a) w y ω * cellAverage N (fun _ : Plane => 1) y) =
        pointToPlane β a (b - a) w ω := by
    obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff x₀ w m).mp hw
    have hwEven : Even (w 0 + w 1) := by
      have hpath : Int.ModEq 2 (w 0 + w 1) (x₀ 0 + x₀ 1 + (m : ℤ)) := by
        simpa only [hp] using Polymer.walkPosition_parity x₀ p
      have hbase : Even (x₀ 0 + x₀ 1 + (m : ℤ)) := Even.add hxEven hm
      have hmod : Int.ModEq 2 (w 0 + w 1) 0 :=
        hpath.trans (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp hbase))
      exact even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod)
    rw [Polymer.tsum_pointToPoint_mul_eq_sum]
    calc
      _ = ∑ y ∈ Polymer.endpoints w (b - a), pointToPoint β a (b - a) w y ω := by
        apply Finset.sum_congr rfl
        intro y hy
        obtain ⟨q, hq⟩ := (Polymer.mem_endpoints_iff w y (b - a)).mp hy
        have hpath : Int.ModEq 2 (y 0 + y 1)
            (w 0 + w 1 + ((b - a : ℕ) : ℤ)) := by
          simpa only [hq] using Polymer.walkPosition_parity w q
        have hbase : Even (w 0 + w 1 + ((b - a : ℕ) : ℤ)) := Even.add hwEven hd
        have hmod : Int.ModEq 2 (y 0 + y 1) 0 :=
          hpath.trans (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp hbase))
        have hyEven : Even (y 0 + y 1) :=
          even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod)
        rw [Critical2DKPZ.cellAverage_const hN hyEven 1]
        simp only [mul_one]
      _ = pointToPlane β a (b - a) w ω := by
        calc
          _ = ∑' y : Site, pointToPoint β a (b - a) w y ω := by
            simpa only [mul_one] using
              (Polymer.tsum_pointToPoint_mul_eq_sum β a (b - a) w (fun _ => 1) ω).symm
          _ = pointToPlane β a (b - a) w ω := by
            simpa only [mul_one] using Polymer.tsum_pointToPoint β a (b - a) w ω
  rw [Polymer.profileP2Fun_eq_sum β a b _ _ A hkernel ω,
      Polymer.profileP2Fun_eq_sum β a b _ _ A hkernel ω]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hterminal w hw]
  simp only [mul_one, Polymer.tsum_pointToPoint]

private theorem lintegral_square_le_liminf_of_tendstoInDistribution
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω} [∀ N, IsProbabilityMeasure (μ N)]
    [IsProbabilityMeasure P] {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y μ P) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P ≤
      atTop.liminf (fun N => ∫⁻ ω, ENNReal.ofReal (X N ω ^ 2) ∂(μ N)) := by
  let νN : ℕ → ProbabilityMeasure ℝ := fun N => ⟨(μ N).map (X N), inferInstance⟩
  let ν : ProbabilityMeasure ℝ := ⟨P.map Y, inferInstance⟩
  have hweak : Tendsto νN atTop (𝓝 ν) := by
    simpa only [νN, ν] using hX.tendsto
  have hopen : ∀ G, IsOpen G → (ν : Measure ℝ) G ≤
      atTop.liminf (fun N => (νN N : Measure ℝ) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hG
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (ν : Measure ℝ)) (μs := fun N => (νN N : Measure ℝ))
    (f := fun x : ℝ => x ^ 2) (continuous_id.pow 2) (fun _ => sq_nonneg _) hopen
  have hmapY : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂P.map Y =
      ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P :=
    lintegral_map' (by fun_prop) hX.aemeasurable_limit
  have hmapN (N : ℕ) : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(μ N).map (X N) =
      ∫⁻ ω, ENNReal.ofReal (X N ω ^ 2) ∂(μ N) :=
    lintegral_map' (by fun_prop) (hX.forall_aemeasurable N)
  have hport' : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂P.map Y ≤
      atTop.liminf (fun N => ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(μ N).map (X N)) := by
    simpa only [ν, νN, ProbabilityMeasure.coe_mk] using hport
  rw [hmapY] at hport'
  simpa only [hmapN] using hport'

/-- Assuming convergence of lattice heat-start logarithms, the heat-start stochastic heat flow mass has a second moment bounded by one plus a constant times the logarithm of inverse smoothing time. -/
theorem heatStart_sq_integral_le_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ s T δ : ℝ, 0 ≤ s → τ₀ ≤ T - s → T - s ≤ τ₁ →
      0 < δ → δ ≤ δ₀ → ∀ x : Plane,
        MemLp (fun ω => shfPairing Z s T (fun y => heatKernel δ (y - x))
          (fun _ => 1) ω) 2 P ∧
        ∫ ω, shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω ^ 2 ∂P ≤
          1 + C * Real.log δ⁻¹ := by
  let Tlo : ℝ := τ₀ / 2
  let Thi : ℝ := max τ₁ 0 + 5
  have hTlo : 0 < Tlo := by dsimp [Tlo]; linarith
  have hThi : 1 ≤ Thi := by dsimp [Thi]; have := le_max_right τ₁ 0; linarith
  have hThiPos : 0 < Thi := lt_of_lt_of_le zero_lt_one hThi
  have hlogThi : 0 ≤ Real.log Thi := Real.log_nonneg hThi
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_log
    |ϑ| Tlo Thi hTlo
  let C : ℝ := |C₂| * (2 + Real.log Thi)
  let δ₀ : ℝ := Real.exp (-1)
  have hδ₀ : 0 < δ₀ := Real.exp_pos _
  refine ⟨C, δ₀, hδ₀, ?_⟩
  intro s T δ hs hτlo hτhi hδ hδle x
  have hdurpos : 0 < T - s := lt_of_lt_of_le hτ₀ hτlo
  have hTpos : 0 < T := by linarith
  have hδone : δ ≤ 1 := by
    have he : Real.exp (-1) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact le_trans hδle he.le
  have hlogδ : 1 ≤ Real.log δ⁻¹ := by
    have hlogle : Real.log δ ≤ -1 := by
      calc
        Real.log δ ≤ Real.log (Real.exp (-1)) := Real.log_le_log hδ hδle
        _ = -1 := Real.log_exp _
    rw [Real.log_inv]
    linarith
  let Kδ : ℕ := Nat.ceil (1 / δ)
  let Kt : ℕ := Nat.ceil (4 / τ₀)
  let K : ℕ := max (max Kδ Kt) 2
  let Xseq : ℕ → Disorder → ℝ := fun N ω =>
    profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω
  have hKδceil : 1 / δ ≤ (Kδ : ℝ) := Nat.le_ceil _
  have hKtceil : 4 / τ₀ ≤ (Kt : ℝ) := Nat.le_ceil _
  have hKevent : ∀ᶠ N : ℕ in atTop, K ≤ N := Filter.eventually_ge_atTop K
  have hseqBound : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => Xseq N ω ^ 2) disorderLaw ∧
        (∫ ω, Xseq N ω ^ 2 ∂disorderLaw ≤ 1 + C * Real.log δ⁻¹) ∧
        ∀ ω, 0 < Xseq N ω := by
    filter_upwards [hC₂, hKevent] with N hC₂N hKN
    have hN1 : 1 ≤ N := by dsimp [K] at hKN; omega
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN1
    have hNpos : 0 < (N : ℝ) := by linarith
    have hKδN : Kδ ≤ N := by dsimp [K] at hKN; omega
    have hKtN : Kt ≤ N := by dsimp [K] at hKN; omega
    have hKδNreal : (Kδ : ℝ) ≤ N := by exact_mod_cast hKδN
    have hKtNreal : (Kt : ℝ) ≤ N := by exact_mod_cast hKtN
    have hNδ : 1 ≤ (N : ℝ) * δ := by
      have hceil := (div_le_iff₀ hδ).mp hKδceil
      have hmul := mul_le_mul_of_nonneg_right hKδNreal hδ.le
      nlinarith
    have hNτ : 4 ≤ (N : ℝ) * τ₀ := by
      have hceil := (div_le_iff₀ hτ₀).mp hKtceil
      have hmul := mul_le_mul_of_nonneg_right hKtNreal hτ₀.le
      nlinarith
    let a : ℕ := evenCeil (N * s)
    let b : ℕ := evenCeil (N * T)
    let m : ℕ := evenCeil (N * δ)
    let n : ℕ := m + (b - a)
    let x₀ : Site := latticePoint N x
    let ν : Site → ℝ := fun w => srwKernel m (w - x₀)
    let ν₀ : Site → ℝ := fun w => srwKernel m w
    let F : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) 0 (b - a)
      ν₀ (fun _ => 1) ω
    let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x₀)
    let Xone : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν
      (fun _ => 1) ω
    have ha0 : 0 ≤ (N : ℝ) * s := mul_nonneg hNpos.le hs
    have hb0 : 0 ≤ (N : ℝ) * T := mul_nonneg hNpos.le hTpos.le
    have hm0 : 0 ≤ (N : ℝ) * δ := mul_nonneg hNpos.le hδ.le
    have hab : a ≤ b := by
      dsimp [a, b]
      have hst : s ≤ T := by linarith
      apply evenCeil_mono
      exact mul_le_mul_of_nonneg_left hst hNpos.le
    have hmEven : Even (m : ℤ) := by
      dsimp [m]
      exact_mod_cast evenCeil_even (N * δ)
    have hdEven : Even ((b - a : ℕ) : ℤ) := by
      have hbe : Even (b : ℤ) := by dsimp [b]; exact_mod_cast evenCeil_even (N * T)
      have hae : Even (a : ℤ) := by dsimp [a]; exact_mod_cast evenCeil_even (N * s)
      have hcast : ((b - a : ℕ) : ℤ) = (b : ℤ) - a := by
        rw [Nat.cast_sub hab]
      rw [hcast]
      exact hbe.sub hae
    have hmge : 1 ≤ (m : ℝ) := by
      have hceil := evenCeil_lt_add_two hm0
      have hmcast : (N : ℝ) * δ ≤ (m : ℝ) := by dsimp [m]; exact le_evenCeil _
      exact le_trans (by linarith [hNδ]) hmcast
    have hncast : (n : ℝ) = (m : ℝ) + ((b : ℝ) - a) := by
      dsimp [n]
      rw [Nat.cast_add, Nat.cast_sub hab]
    have hduration := evenCeil_duration_error ha0 hb0
    rw [abs_lt] at hduration
    have hnlo : Tlo * N ≤ (n : ℝ) := by
      rw [hncast]
      have hlow : τ₀ * (N : ℝ) - 2 < (b : ℝ) - a := by
        nlinarith [hduration.1, mul_le_mul_of_nonneg_left hτlo hNpos.le]
      dsimp [Tlo]
      nlinarith [hNτ, hlow, hmge]
    have hnhi : (n : ℝ) ≤ Thi * N := by
      have hmhi : (m : ℝ) < (N : ℝ) * δ + 2 := by
        dsimp [m]
        exact evenCeil_lt_add_two hm0
      have hdhi : (b : ℝ) - a < (N : ℝ) * (T - s) + 2 := by
        nlinarith [hduration.2]
      rw [hncast]
      dsimp [Thi]
      have hNdelta : (N : ℝ) * δ ≤ N := by
        calc
          (N : ℝ) * δ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hδone hNpos.le
          _ = N := by ring
      have hNduration : (N : ℝ) * (T - s) ≤ (N : ℝ) * τ₁ :=
        mul_le_mul_of_nonneg_left hτhi hNpos.le
      have hNduration' : (N : ℝ) * τ₁ ≤ (N : ℝ) * max τ₁ 0 :=
        mul_le_mul_of_nonneg_left (le_max_left τ₁ 0) hNpos.le
      have h4N : 4 ≤ 4 * (N : ℝ) := by nlinarith [hNreal]
      apply le_trans (le_of_lt (add_lt_add hmhi hdhi))
      calc
        ((N : ℝ) * δ + 2) + ((N : ℝ) * (T - s) + 2) =
            (N : ℝ) * δ + (N : ℝ) * (T - s) + 4 := by ring
        _ ≤ (N : ℝ) + (N : ℝ) * max τ₁ 0 + 4 := by
          exact add_le_add (add_le_add hNdelta (le_trans hNduration hNduration')) le_rfl
        _ ≤ (N : ℝ) + (N : ℝ) * max τ₁ 0 + 4 * (N : ℝ) :=
          calc
            _ = 4 + ((N : ℝ) + (N : ℝ) * max τ₁ 0) := by ring
            _ ≤ 4 * (N : ℝ) + ((N : ℝ) + (N : ℝ) * max τ₁ 0) :=
              add_le_add_left h4N _
            _ = _ := by ring
        _ = (max τ₁ 0 + 5) * N := by ring
    have hmn : m ≤ n := by dsimp [n]; omega
    have hnge : 1 ≤ n := by
      have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (mul_pos hTlo (by exact_mod_cast hN1)) hnlo
      exact_mod_cast hnpos
    have hratio : (n : ℝ) / (m : ℝ) ≤ Thi / δ := by
      have hmpos : 0 < (m : ℝ) := by linarith
      have hNm : (N : ℝ) * δ ≤ (m : ℝ) := by dsimp [m]; exact le_evenCeil _
      apply (div_le_div_iff₀ hmpos hδ).2
      calc
        (n : ℝ) * δ ≤ Thi * N * δ := by
          exact mul_le_mul_of_nonneg_right hnhi hδ.le
        _ = Thi * ((N : ℝ) * δ) := by ring
        _ ≤ Thi * (m : ℝ) := mul_le_mul_of_nonneg_left hNm (le_of_lt hThiPos)
    have hlogratio : Real.log ((n : ℝ) / (m : ℝ)) ≤ Real.log (Thi / δ) :=
      Real.log_le_log (by positivity) hratio
    have hlogdiv : Real.log (Thi / δ) = Real.log Thi + Real.log δ⁻¹ := by
      rw [Real.log_div hThiPos.ne' hδ.ne', Real.log_inv]
      ring
    have hlogqnonneg : 0 ≤ 1 + Real.log ((n : ℝ) / (m : ℝ)) := by
      have hratioone : 1 ≤ (n : ℝ) / (m : ℝ) := by
        apply (one_le_div (by linarith : 0 < (m : ℝ))).2
        exact_mod_cast hmn
      exact add_nonneg zero_le_one (Real.log_nonneg hratioone)
    have hqbound : 1 + Real.log ((n : ℝ) / (m : ℝ)) ≤
        (2 + Real.log Thi) * Real.log δ⁻¹ := by
      rw [hlogdiv] at hlogratio
      have hlogThiMul : Real.log Thi ≤ Real.log Thi * Real.log δ⁻¹ := by
        calc
          Real.log Thi = Real.log Thi * 1 := by ring
          _ ≤ Real.log Thi * Real.log δ⁻¹ :=
            mul_le_mul_of_nonneg_left hlogδ hlogThi
      have hlogδDouble : 1 + Real.log δ⁻¹ ≤ 2 * Real.log δ⁻¹ := by linarith
      calc
        1 + Real.log ((n : ℝ) / (m : ℝ)) ≤
            1 + (Real.log Thi + Real.log δ⁻¹) := add_le_add_right hlogratio 1
        _ = (1 + Real.log δ⁻¹) + Real.log Thi := by ring
        _ ≤ 2 * Real.log δ⁻¹ + Real.log Thi * Real.log δ⁻¹ :=
          add_le_add hlogδDouble hlogThiMul
        _ = (2 + Real.log Thi) * Real.log δ⁻¹ := by ring
    have hϑ : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| := ⟨neg_abs_le ϑ, le_abs_self ϑ⟩
    have hsm := hC₂N ϑ hϑ m n hmn hnlo hnhi
    have hsm' : ∫ ω, smoothedP2Plane (criticalBeta ϑ N) m n 0 ω ^ 2 ∂disorderLaw ≤
        |C₂| * ((2 + Real.log Thi) * Real.log δ⁻¹) := by
      have hcoeff : C₂ * (1 + Real.log ((n : ℝ) / (m : ℝ))) ≤
          |C₂| * (1 + Real.log ((n : ℝ) / (m : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₂) hlogqnonneg
      have hmax : max m 1 = m := max_eq_left (by exact_mod_cast hmge)
      rw [hmax] at hsm
      calc
        _ ≤ C₂ * (1 + Real.log ((n : ℝ) / (m : ℝ))) := hsm
        _ ≤ |C₂| * (1 + Real.log ((n : ℝ) / (m : ℝ))) := hcoeff
        _ ≤ |C₂| * ((2 + Real.log Thi) * Real.log δ⁻¹) := by
          exact mul_le_mul_of_nonneg_left hqbound (abs_nonneg C₂)
    have hkernelA : ∀ w ∉ Polymer.endpoints x₀ m, ν w = 0 := by
      intro w hw
      exact Polymer.srwKernel_eq_zero_of_not_mem m x₀ w hw
    have hkernel0 : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg m (w - x₀)
    have hkernel1 : ∑ w ∈ Polymer.endpoints x₀ m, ν w = 1 := by
      simpa only [ν] using Polymer.sum_srwKernel_endpoints m x₀
    have hXpos : ∀ ω, 0 < Xone ω := by
      intro ω
      exact OnePoint.profileP2Fun_pos_of_normalized _ _ _ _ (Polymer.endpoints x₀ m)
        hkernelA hkernel0 hkernel1 ω
    have hFmeas : Measurable (fun ω => F ω ^ 2) := by
      dsimp [F]
      exact (Polymer.measurable_profileP2Fun _ _ _ _ _).pow_const 2
    have hτmeas : Measurable τ := by
      dsimp [τ]
      apply measurable_pi_iff.mpr
      intro p
      exact Gaussian.measurable_disorder_eval (p.1, p.2 + x₀)
    have hτMP : MeasurePreserving τ disorderLaw disorderLaw := by
      dsimp [τ]
      exact FutureProfiles.measurePreserving_disorderShift x₀
    have hτint : (∫ ω, F (τ ω) ^ 2 ∂disorderLaw) = ∫ ω, F ω ^ 2 ∂disorderLaw := by
      have h := integral_map (μ := disorderLaw) hτmeas.aemeasurable
        hFmeas.aestronglyMeasurable
      rw [hτMP.map_eq] at h
      exact h.symm
    have hspatial (ω : Disorder) :
        profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω =
          F (τ (Smoothing.shiftEnvironment a ω)) := by
      rw [Smoothing.profileP2Fun_timeShift_sub (criticalBeta ϑ N) le_rfl hab ν
        (fun _ => 1) ω]
      simp only [Nat.sub_self]
      rw [FutureProfiles.profileP2Fun_translate (criticalBeta ϑ N) 0 (b - a) x₀ ν₀
        (fun _ => 1) (Smoothing.shiftEnvironment a ω)]
    have hprofileInt : (∫ ω, Xone ω ^ 2 ∂disorderLaw) = ∫ ω, F ω ^ 2 ∂disorderLaw := by
      calc
        _ = ∫ ω, F (τ (Smoothing.shiftEnvironment a ω)) ^ 2 ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [← hspatial]
        _ = ∫ ω, F (τ ω) ^ 2 ∂disorderLaw := by
          simpa only [Function.comp_apply] using
            (Smoothing.integral_shiftEnvironment a (hFmeas.comp hτmeas))
        _ = ∫ ω, F ω ^ 2 ∂disorderLaw := hτint
    have hpoint (ω : Disorder) :
        smoothedP2Plane (criticalBeta ϑ N) m n 0 ω = F (Smoothing.shiftEnvironment m ω) := by
      simpa only [F, n, Nat.add_sub_cancel_left] using
        MomentBounds.smoothedP2Plane_eq_profileP2Fun_shift (criticalBeta ϑ N) hmn ω
    have hsmoothedInt :
        (∫ ω, smoothedP2Plane (criticalBeta ϑ N) m n 0 ω ^ 2 ∂disorderLaw) =
          ∫ ω, F ω ^ 2 ∂disorderLaw := by
      calc
        _ = ∫ ω, F (Smoothing.shiftEnvironment m ω) ^ 2 ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [hpoint]
        _ = ∫ ω, F ω ^ 2 ∂disorderLaw :=
          Smoothing.integral_shiftEnvironment m hFmeas
    have hprofileBound : ∫ ω, Xone ω ^ 2 ∂disorderLaw ≤
        1 + C * Real.log δ⁻¹ := by
      rw [hprofileInt, ← hsmoothedInt]
      dsimp [C]
      have hnonneg : 0 ≤ |C₂| * ((2 + Real.log Thi) * Real.log δ⁻¹) := by positivity
      calc
        _ ≤ |C₂| * ((2 + Real.log Thi) * Real.log δ⁻¹) := hsm'
        _ = C * Real.log δ⁻¹ := by dsimp [C]; ring
        _ ≤ 1 + C * Real.log δ⁻¹ := le_add_of_nonneg_left (by norm_num)
    have hXint : Integrable (fun ω => Xone ω ^ 2) disorderLaw := by
      have h := OnePoint.integrable_rpow_profileP2Fun (criticalBeta ϑ N) a b ν
        (Polymer.endpoints x₀ m) hkernelA hkernel0 hkernel1 2
      have hpow : (fun ω => profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω ^
          (2 : ℝ)) = fun ω => Xone ω ^ 2 := by
        funext ω
        change profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω ^ (2 : ℝ) =
          profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω ^ (2 : ℕ)
        exact Real.rpow_natCast _ _
      rw [← hpow]
      exact h
    have hcellfun : (fun _ : Plane => Real.exp (0 : ℝ)) = fun _ => (1 : ℝ) := by
      funext y
      simp only [Real.exp_zero]
    have hXseqEq (ω : Disorder) : Xseq N ω = Xone ω := by
      dsimp [Xseq, Xone]
      rw [hcellfun]
      exact profile_cellAverage_one_eq (criticalBeta ϑ N) (by exact_mod_cast hN1)
        a b m hmEven hdEven x ω
    have hXseqInt : Integrable (fun ω => Xseq N ω ^ 2) disorderLaw := by
      have hEq : (fun ω => Xseq N ω ^ 2) = fun ω => Xone ω ^ 2 := by
        funext ω
        rw [hXseqEq]
      rw [hEq]
      exact hXint
    have hXseqBound : ∫ ω, Xseq N ω ^ 2 ∂disorderLaw ≤ 1 + C * Real.log δ⁻¹ := by
      have hEq : (∫ ω, Xseq N ω ^ 2 ∂disorderLaw) = ∫ ω, Xone ω ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hXseqEq]
      rw [hEq]
      exact hprofileBound
    have hXseqPos : ∀ ω, 0 < Xseq N ω := by
      intro ω
      rw [hXseqEq]
      exact hXpos ω
    exact ⟨hXseqInt, hXseqBound, hXseqPos⟩
  let h₀ : Plane →ᵇ ℝ := 0
  let svec : Fin 1 → ℝ := fun _ => s
  let δvec : Fin 1 → ℝ := fun _ => δ
  let xvec : Fin 1 → Plane := fun _ => x
  have hsT : s < T := by linarith
  have hparams : ∀ i : Fin 1, 0 ≤ svec i ∧ svec i < T ∧ 0 < δvec i := by
    intro i
    simp only [svec, δvec]
    exact ⟨hs, hsT, hδ⟩
  have hK := hHeatStartLogInput T h₀ 1 svec δvec xvec hparams
  let Y : Ω → ℝ := fun ω =>
    shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
  let Lseq : ℕ → Disorder → ℝ := fun N ω => Real.log (Xseq N ω)
  have hdistLog : TendstoInDistribution Lseq atTop (fun ω => Real.log (Y ω))
      (fun _ => disorderLaw) P := by
    have h := hK.2.1.continuous_comp (continuous_apply (0 : Fin 1))
    simpa only [Lseq, Xseq, Y, svec, δvec, xvec, Function.comp_def,
      Function.comp_apply, h₀, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      Real.exp_zero] using h
  have hposExp := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    ϑ P Z hZ s T δ x h₀ hs hsT hδ
  have hposY : ∀ᵐ ω ∂P, 0 < Y ω := by
    simpa only [Y, h₀, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      Real.exp_zero] using hposExp.1
  have hExpTarget : (fun ω => Real.exp (Real.log (Y ω))) =ᵐ[P] Y := by
    filter_upwards [hposY] with ω hω
    exact Real.exp_log hω
  have hdistExp : TendstoInDistribution (fun N ω => Real.exp (Lseq N ω)) atTop
      (fun ω => Real.exp (Real.log (Y ω))) (fun _ => disorderLaw) P :=
    hdistLog.continuous_comp (g := Real.exp) Real.continuous_exp
  have hseqExp : ∀ᶠ N : ℕ in atTop,
      (fun ω => Real.exp (Lseq N ω)) =ᵐ[disorderLaw] Xseq N := by
    filter_upwards [hseqBound] with N hN
    filter_upwards [] with ω
    dsimp [Lseq]
    exact Real.exp_log (hN.2.2 ω)
  have hXmeas (N : ℕ) : Measurable (Xseq N) := by
    dsimp [Xseq]
    exact Polymer.measurable_profileP2Fun _ _ _ _ _
  have hdistX : TendstoInDistribution Xseq atTop Y (fun _ => disorderLaw) P := by
    refine ⟨fun N => (hXmeas N).aemeasurable,
      hdistExp.aemeasurable_limit.congr hExpTarget, ?_⟩
    have hmapEq : ∀ᶠ N : ℕ in atTop,
        (⟨disorderLaw.map (fun ω => Real.exp (Lseq N ω)), inferInstance⟩ :
          ProbabilityMeasure ℝ) =
        ⟨disorderLaw.map (Xseq N), inferInstance⟩ := by
      filter_upwards [hseqExp] with N hN
      apply Subtype.ext
      exact Measure.map_congr hN
    have hlimEq :
        (⟨P.map (fun ω => Real.exp (Real.log (Y ω))), inferInstance⟩ :
          ProbabilityMeasure ℝ) = ⟨P.map Y, inferInstance⟩ := by
      apply Subtype.ext
      exact Measure.map_congr hExpTarget
    have hweak := hdistExp.tendsto.congr' hmapEq
    rw [hlimEq] at hweak
    exact hweak
  have hfatou := lintegral_square_le_liminf_of_tendstoInDistribution hdistX
  have hlinBound : ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal (Xseq N ω ^ 2) ∂disorderLaw ≤
        ENNReal.ofReal (1 + C * Real.log δ⁻¹) := by
    filter_upwards [hseqBound] with N hN
    rw [← ofReal_integral_eq_lintegral_ofReal hN.1
      (Filter.Eventually.of_forall fun ω => sq_nonneg (Xseq N ω))]
    exact ENNReal.ofReal_le_ofReal hN.2.1
  have hlinlim : atTop.liminf
      (fun N => ∫⁻ ω, ENNReal.ofReal (Xseq N ω ^ 2) ∂disorderLaw) ≤
        ENNReal.ofReal (1 + C * Real.log δ⁻¹) := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨N, hNb⟩ := (hb.and hlinBound).exists
    exact hNb.1.trans hNb.2
  have hYlin : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P ≤
      ENNReal.ofReal (1 + C * Real.log δ⁻¹) := hfatou.trans hlinlim
  have hYstrong : AEStronglyMeasurable Y P :=
    hdistX.aemeasurable_limit.aestronglyMeasurable
  have hYsqStrong : AEStronglyMeasurable (fun ω => Y ω ^ 2) P :=
    (continuous_id.pow 2).comp_aestronglyMeasurable hYstrong
  have hYsqInt : Integrable (fun ω => Y ω ^ 2) P := by
    refine ⟨hYsqStrong, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => sq_nonneg (Y ω))]
    exact lt_of_le_of_lt hYlin ENNReal.ofReal_lt_top
  have hBnonneg : 0 ≤ 1 + C * Real.log δ⁻¹ := by positivity
  have hYintegral : ∫ ω, Y ω ^ 2 ∂P ≤ 1 + C * Real.log δ⁻¹ := by
    have hlin := hYlin
    rw [← ofReal_integral_eq_lintegral_ofReal hYsqInt
      (Filter.Eventually.of_forall fun ω => sq_nonneg (Y ω))] at hlin
    exact (ENNReal.ofReal_le_ofReal_iff hBnonneg).mp hlin
  have hYmem : MemLp Y 2 P := (memLp_two_iff_integrable_sq hYstrong).2 hYsqInt
  exact ⟨by simpa only [Y] using hYmem, by simpa only [Y] using hYintegral⟩

/-- The logarithmic heat-start pairing has a uniform second-moment estimate. -/
theorem heatStartLog_moments_le_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ s T δ : ℝ, 0 ≤ s → τ₀ ≤ T - s → T - s ≤ τ₁ →
      0 < δ → δ ≤ δ₀ → ∀ x : Plane,
        MemLp (heatStartLog Z s T δ x) 2 P ∧
        0 ≤ -∫ ω, heatStartLog Z s T δ x ω ∂P ∧
        Var[heatStartLog Z s T δ x; P] ≤ -2 * ∫ ω, heatStartLog Z s T δ x ω ∂P ∧
        -2 * ∫ ω, heatStartLog Z s T δ x ω ∂P ≤ Real.log (Real.log δ⁻¹) + C := by
  obtain ⟨C₂, δ₂, hδ₂, hsecond⟩ := heatStart_sq_integral_le_of ϑ P Z hZ hHeatStartLogInput hτ₀
  let C : ℝ := |C₂| + 1
  let δ₀ : ℝ := min δ₂ (Real.exp (-1))
  have hδ₀ : 0 < δ₀ := lt_min hδ₂ (Real.exp_pos _)
  refine ⟨C, δ₀, hδ₀, ?_⟩
  intro s T δ hs hτlo hτhi hδ hδle x
  have hsT : s < T := by linarith
  have hδ₂le : δ ≤ δ₂ := le_trans hδle (min_le_left _ _)
  have hδexp : δ ≤ Real.exp (-1) := le_trans hδle (min_le_right _ _)
  have hlogδ : 1 ≤ Real.log δ⁻¹ := by
    have hlog : Real.log δ ≤ -1 := by
      calc
        Real.log δ ≤ Real.log (Real.exp (-1)) := Real.log_le_log hδ hδexp
        _ = -1 := Real.log_exp _
    rw [Real.log_inv]
    linarith
  obtain ⟨hYint, hYmean⟩ := heatStart_integral_eq_one ϑ P Z hZ hs hsT hδ x
  obtain ⟨hYmem, hYsqBound⟩ := hsecond s T δ hs hτlo hτhi hδ hδ₂le x
  let Y : Ω → ℝ := fun ω =>
    shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
  let L : Ω → ℝ := heatStartLog Z s T δ x
  have hlogPackage := hsym.2.2.2.2.2.2 s T δ x (0 : Plane →ᵇ ℝ) hs hsT hδ
  have hterminal : (fun _ : Plane => Real.exp (0 : ℝ)) = fun _ => (1 : ℝ) := by
    funext y
    exact Real.exp_zero
  have hpairTerminal (ω : Ω) :
      shfPairing Z s T (fun y => heatKernel δ (y - x))
          (fun _ => Real.exp (0 : ℝ)) ω = Y ω := by
    rw [hterminal]
  have hlogAtZero : (fun ω => Real.log (shfPairing Z s T
      (fun y => heatKernel δ (y - x))
      (fun _ => Real.exp (0 : ℝ)) ω)) =ᵐ[P] L := by
    filter_upwards [] with ω
    dsimp [L, heatStartLog]
    rw [hterminal]
  have hYpos : ∀ᵐ ω ∂P, 0 < Y ω := by
    filter_upwards [hlogPackage.1] with ω hω
    rw [← hpairTerminal]
    exact hω
  have hLmeas : AEMeasurable L P := by
    exact hlogPackage.2.1.congr hlogAtZero
  have hEhrhard : IsEhrhardType (P.map L) := by
    rw [← Measure.map_congr hlogAtZero]
    exact hlogPackage.2.2
  have hExpL : (fun ω => Real.exp (L ω)) =ᵐ[P] Y := by
    filter_upwards [hYpos] with ω hω
    dsimp [L, Y, heatStartLog]
    exact Real.exp_log hω
  have hExpLInt : Integrable (fun ω => Real.exp (L ω)) P := hYint.congr hExpL.symm
  have hExpLawInt : Integrable (fun r : ℝ => Real.exp r) (P.map L) :=
    (integrable_map_measure (by fun_prop) hLmeas).2 hExpLInt
  have hExpLawMean : ∫ r, Real.exp r ∂P.map L = 1 := by
    calc
      ∫ r, Real.exp r ∂P.map L = ∫ ω, Real.exp (L ω) ∂P :=
        integral_map hLmeas (by fun_prop)
      _ = ∫ ω, Y ω ∂P := integral_congr_ae hExpL
      _ = 1 := hYmean
  have hMom := Critical2DKPZ.Provider.ehrhardType_momentBounds
    (P.map L) hEhrhard hExpLawInt hExpLawMean
  have hLawIdMeas : AEStronglyMeasurable (id : ℝ → ℝ) (P.map L) := by fun_prop
  have hLawIdMem : MemLp (id : ℝ → ℝ) 2 (P.map L) :=
    (memLp_two_iff_integrable_sq hLawIdMeas).2 hMom.1
  have hLawIdInt : Integrable (id : ℝ → ℝ) (P.map L) := hLawIdMem.integrable (by norm_num)
  have hLawMeanLe : (∫ r, r ∂P.map L) ≤ 0 := by
    have hj := integral_le_log_integral_exp (P.map L) id hLawIdInt hExpLawInt
    simp only [id_eq] at hj
    rw [hExpLawMean] at hj
    simpa only [Real.log_one] using hj
  have hMeanMap : (∫ r, r ∂P.map L) = ∫ ω, L ω ∂P := by
    rw [integral_map hLmeas (by fun_prop)]
  have hMeanLe : (∫ ω, L ω ∂P) ≤ 0 := hMeanMap ▸ hLawMeanLe
  have hLsqInt : Integrable (fun ω => L ω ^ 2) P :=
    (integrable_map_measure (by fun_prop) hLmeas).mp hMom.1
  have hLmem : MemLp L 2 P :=
    (memLp_two_iff_integrable_sq hLmeas.aestronglyMeasurable).2 hLsqInt
  have hVariance : Var[L; P] ≤ -2 * ∫ ω, L ω ∂P := by
    rw [← variance_id_map hLmeas, ← hMeanMap]
    exact hMom.2.1
  have hYsqInt : Integrable (fun ω => Y ω ^ 2) P := hYmem.integrable_sq
  have hExp2L : (fun ω => Real.exp (2 * L ω)) =ᵐ[P] fun ω => Y ω ^ 2 := by
    filter_upwards [hYpos] with ω hω
    calc
      Real.exp (2 * L ω) = Real.exp (L ω + L ω) := by congr 1; ring
      _ = Real.exp (L ω) * Real.exp (L ω) := Real.exp_add _ _
      _ = Y ω ^ 2 := by
        change Real.exp (Real.log (Y ω)) * Real.exp (Real.log (Y ω)) = _
        rw [Real.exp_log hω]
        ring
  have hExp2Int : Integrable (fun ω => Real.exp (2 * L ω)) P := hYsqInt.congr hExp2L.symm
  have hExp2LawInt : Integrable (fun r : ℝ => Real.exp (2 * r)) (P.map L) :=
    (integrable_map_measure (by fun_prop) hLmeas).2 hExp2Int
  have hExp2LawMean : ∫ r, Real.exp (2 * r) ∂P.map L = ∫ ω, Y ω ^ 2 ∂P := by
    calc
      ∫ r, Real.exp (2 * r) ∂P.map L = ∫ ω, Real.exp (2 * L ω) ∂P :=
        integral_map hLmeas (by fun_prop)
      _ = ∫ ω, Y ω ^ 2 ∂P := integral_congr_ae hExp2L
  have hConditional := (hMom.2.2.2 hExp2LawInt).1
  have hMeanLogI : -2 * ∫ ω, L ω ∂P ≤ Real.log (∫ ω, Y ω ^ 2 ∂P) := by
    have hmul := mul_le_mul_of_nonneg_left hConditional (by norm_num : 0 ≤ (2 : ℝ))
    rw [hMeanMap, hExp2LawMean] at hmul
    nlinarith [hConditional]
  have hYsqNonneg : 0 ≤ᵐ[P] fun ω => Y ω ^ 2 := Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hYsqSupport : ∀ᵐ ω ∂P, ω ∈ Function.support (fun ω => Y ω ^ 2) := by
    filter_upwards [hYpos] with ω hω
    simp only [Function.mem_support, ne_eq]
    exact pow_ne_zero 2 (ne_of_gt hω)
  have hYsqSupportMass : P (Function.support (fun ω => Y ω ^ 2)) = 1 := by
    have hcomp : P ((Function.support (fun ω => Y ω ^ 2))ᶜ) = 0 := by
      have hnot : P {ω | ω ∉ Function.support (fun ω => Y ω ^ 2)} = 0 := ae_iff.mp hYsqSupport
      have hset : {ω | ω ∉ Function.support (fun ω => Y ω ^ 2)} =
          (Function.support (fun ω => Y ω ^ 2))ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
      rw [← hset]
      exact hnot
    rw [measure_of_measure_compl_eq_zero hcomp, measure_univ]
  have hYsqIntegralPos : 0 < ∫ ω, Y ω ^ 2 ∂P := by
    apply (integral_pos_iff_support_of_nonneg_ae hYsqNonneg hYsqInt).2
    rw [hYsqSupportMass]
    exact zero_lt_one
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hC2le : C₂ ≤ C := by
    dsimp [C]
    exact le_trans (le_abs_self C₂) (le_add_of_nonneg_right (by norm_num))
  have hsecondBound : (∫ ω, Y ω ^ 2 ∂P) ≤ 1 + C * Real.log δ⁻¹ := by
    calc
      ∫ ω, Y ω ^ 2 ∂P ≤ 1 + C₂ * Real.log δ⁻¹ := hYsqBound
      _ ≤ 1 + C * Real.log δ⁻¹ := by
        have hmul := mul_le_mul_of_nonneg_right hC2le (le_trans zero_le_one hlogδ)
        simpa only [add_comm] using add_le_add_left hmul 1
  have hsecondLeProduct : 1 + C * Real.log δ⁻¹ ≤
      Real.log δ⁻¹ * (1 + C) := by
    calc
      1 + C * Real.log δ⁻¹ ≤ Real.log δ⁻¹ + C * Real.log δ⁻¹ := by
        have h := add_le_add_left hlogδ (C * Real.log δ⁻¹)
        linarith
      _ = Real.log δ⁻¹ * (1 + C) := by ring
  have hproductPos : 0 < Real.log δ⁻¹ * (1 + C) :=
    mul_pos (lt_of_lt_of_le zero_lt_one hlogδ) (add_pos_of_pos_of_nonneg zero_lt_one hCnonneg)
  have hlogBound : Real.log (∫ ω, Y ω ^ 2 ∂P) ≤ Real.log (Real.log δ⁻¹) + C := by
    calc
      Real.log (∫ ω, Y ω ^ 2 ∂P) ≤ Real.log (Real.log δ⁻¹ * (1 + C)) :=
        Real.log_le_log hYsqIntegralPos (hsecondBound.trans hsecondLeProduct)
      _ = Real.log (Real.log δ⁻¹) + Real.log (1 + C) := by
        rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hlogδ))
          (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hCnonneg))]
      _ ≤ Real.log (Real.log δ⁻¹) + C := by
        have h := Real.log_le_sub_one_of_pos (show 0 < 1 + C by linarith)
        linarith
  refine ⟨hLmem, ?_, hVariance, ?_⟩
  · linarith
  · exact hMeanLogI.trans hlogBound

end Critical2DKPZ.SmallScales

end
