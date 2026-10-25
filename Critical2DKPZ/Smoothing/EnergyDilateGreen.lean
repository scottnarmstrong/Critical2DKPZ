/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.EnergyDilateUniform
import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.MeasureTheory.Integral.Prod

/-! # Uniform Green convergence for compact dilation families -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Critical2DKPZ.Smoothing

/-- A mixed Green-energy integral is controlled by the exact row mass when its second profile is bounded.
The integrability conjunct makes this an actual integral estimate. -/
theorem integral_truncatedGreen_latticePoint_mixed_le (N L : ℕ) (hN : 0 < N)
    (f g : Plane → ℝ) (hfi : Integrable f) (hgi : Integrable g)
    (B : ℝ) (hgB : ∀ y, |g y| ≤ B) :
    Integrable (fun p : Plane × Plane => |f p.1| * |g p.2| *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1))
      (volume.prod volume) ∧
    (∫ p : Plane × Plane, |f p.1| * |g p.2| *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) ≤
      (4 * (L : ℝ) / N) * B * (∫ x : Plane, |f x|) := by
  classical
  let F : Plane × Plane → ℝ := fun p => |f p.1| * |g p.2|
  let K : Plane × Plane → ℝ := fun p =>
    MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)
  have hfnorm : Integrable (fun x : Plane => |f x|) := by
    simpa only [Real.norm_eq_abs] using hfi.norm
  have hgnorm : Integrable (fun x : Plane => |g x|) := by
    simpa only [Real.norm_eq_abs] using hgi.norm
  have hFInt : Integrable F (volume.prod volume) := by
    simpa [F] using hfnorm.mul_prod hgnorm
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKmeas : Measurable K := by
    apply (measurable_of_countable fun z : Site => MomentBounds.truncatedGreen L z).comp
    exact (measurable_latticePoint N).comp measurable_snd |>.sub
      ((measurable_latticePoint N).comp measurable_fst)
  have hKnonneg (p : Plane × Plane) : 0 ≤ K p :=
    MomentBounds.truncatedGreen_nonneg L _
  have hKF' : Integrable (fun p : Plane × Plane => K p * F p) (volume.prod volume) := by
    apply hFInt.bdd_mul (c := L) hKmeas.aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hKnonneg p)]
    exact MomentBounds.truncatedGreen_le L _
  have hKF : Integrable (fun p : Plane × Plane => F p * K p) (volume.prod volume) := by
    simpa only [mul_comm] using hKF'
  have houterInt : Integrable (fun x : Plane => ∫ y : Plane, F (x, y) * K (x, y)) :=
    hKF.integral_prod_left
  have houterMajor : Integrable (fun x : Plane => |f x| * (B * (4 * (L : ℝ) / N))) :=
    hfnorm.mul_const _
  have hrow (x : Plane) :
      ∫ y : Plane, F (x, y) * K (x, y) ≤ |f x| * (B * (4 * (L : ℝ) / N)) := by
    let Kx : Plane → ℝ := fun y => MomentBounds.truncatedGreen L
      (latticePoint N y - latticePoint N x)
    have hxEven : Even (latticePoint N x 0 + latticePoint N x 1) := by
      have hxmem := latticePoint_mem_evenLattice N x
      change Even (latticePoint N x 0 + latticePoint N x 1) at hxmem
      exact hxmem
    have hrowMass := integral_truncatedGreen_latticePoint_eq N L hN
      (latticePoint N x) hxEven
    have hKxInt : Integrable Kx := by simpa only [Kx] using hrowMass.1
    have hKxMass : (∫ y : Plane, Kx y) = 4 * (L : ℝ) / N := by
      simpa only [Kx] using hrowMass.2
    have hKxnonneg (y : Plane) : 0 ≤ Kx y := MomentBounds.truncatedGreen_nonneg L _
    have hgKInt : Integrable (fun y : Plane => |g y| * Kx y) := by
      apply hKxInt.bdd_mul (c := B) hgnorm.aestronglyMeasurable
      filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (g y))]
      exact hgB y
    have hinnerInt : Integrable (fun y : Plane => |f x| * |g y| * Kx y) := by
      simpa [mul_assoc] using hgKInt.const_mul (|f x|)
    have hinnerMajor : Integrable (fun y : Plane => (|f x| * B) * Kx y) :=
      hKxInt.const_mul (|f x| * B)
    have hpoint (y : Plane) : |f x| * |g y| * Kx y ≤ (|f x| * B) * Kx y := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgB y) (abs_nonneg _)) (hKxnonneg y)
    have hmono := integral_mono hinnerInt hinnerMajor hpoint
    change (∫ y : Plane, |f x| * |g y| * Kx y) ≤ _ at hmono
    calc
      ∫ y : Plane, F (x, y) * K (x, y) ≤ ∫ y : Plane, (|f x| * B) * Kx y := by
        simpa [F, K, Kx, mul_assoc] using hmono
      _ = (|f x| * B) * (∫ y : Plane, Kx y) := integral_const_mul _ _
      _ = |f x| * (B * (4 * (L : ℝ) / N)) := by rw [hKxMass]; ring
  have hpairEq : (∫ p : Plane × Plane, F p * K p) =
      ∫ x : Plane, ∫ y : Plane, F (x, y) * K (x, y) := by
    rw [Measure.volume_eq_prod Plane Plane]
    exact integral_prod _ hKF
  refine ⟨?_, ?_⟩
  · simpa [F, K] using hKF
  · rw [show (∫ p : Plane × Plane, |f p.1| * |g p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) =
      ∫ p : Plane × Plane, F p * K p by rfl, hpairEq]
    calc
      (∫ x : Plane, ∫ y : Plane, F (x, y) * K (x, y)) ≤
          ∫ x : Plane, |f x| * (B * (4 * (L : ℝ) / N)) :=
        integral_mono houterInt houterMajor hrow
      _ = (∫ x : Plane, |f x|) * (B * (4 * (L : ℝ) / N)) := integral_mul_const _ _
      _ = (4 * (L : ℝ) / N) * B * (∫ x : Plane, |f x|) := by ring

/-- The heat profile of a positive dilation is the correspondingly rescaled heat profile. -/
theorem continuumHeatProfile_dilate (φ : Plane → ℝ) {c r : ℝ} (hc : 0 < c) :
    continuumHeatProfile (fun x => c * φ (Real.sqrt c • x)) r =
      c * continuumHeatProfile φ (c * r) := by
  let F : Plane × Plane → ℝ := fun p =>
    |φ p.1| * |φ p.2| * heatKernel (2 * (c * r)) (p.2 - p.1)
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hdim : Module.finrank ℝ (Plane × Plane) = 4 := by
    simp [Plane, Module.finrank_prod, finrank_euclideanSpace]
  unfold continuumHeatProfile
  calc
    (∫ p : Plane × Plane,
        |(fun x => c * φ (Real.sqrt c • x)) p.1| *
          |(fun x => c * φ (Real.sqrt c • x)) p.2| *
          heatKernel (2 * r) (p.2 - p.1)) =
        ∫ p : Plane × Plane, c ^ 3 * F (Real.sqrt c • p) := by
          apply integral_congr_ae
          filter_upwards [] with p
          dsimp [F]
          rw [abs_mul, abs_of_pos hc, abs_mul, abs_of_pos hc]
          have hscale := Critical2DKPZ.heatKernel_scaling
            (a := Real.sqrt c) (u := 2 * r) hsqrt (p.2 - p.1)
          have hmul : Real.sqrt c ^ 2 * (2 * r) = 2 * (c * r) := by
            rw [Real.sq_sqrt hc.le]
            ring
          rw [hmul] at hscale
          rw [← smul_sub]
          have hscale' : heatKernel (2 * (c * r))
              (Real.sqrt c • (p.2 - p.1)) = c⁻¹ * heatKernel (2 * r) (p.2 - p.1) := by
            simpa [Real.sq_sqrt hc.le] using hscale
          have hkernel : heatKernel (2 * r) (p.2 - p.1) =
              c * heatKernel (2 * (c * r)) (Real.sqrt c • (p.2 - p.1)) := by
            calc
              heatKernel (2 * r) (p.2 - p.1) =
                  c * (c⁻¹ * heatKernel (2 * r) (p.2 - p.1)) := by
                    field_simp [ne_of_gt hc]
              _ = c * heatKernel (2 * (c * r))
                  (Real.sqrt c • (p.2 - p.1)) := by rw [← hscale']
          rw [hkernel]
          ring
    _ = c ^ 3 * ∫ p : Plane × Plane, F (Real.sqrt c • p) := integral_const_mul _ _
    _ = c ^ 3 * ((Real.sqrt c ^ 4)⁻¹ * ∫ p : Plane × Plane, F p) := by
          have hcomp : (∫ p : Plane × Plane, F (Real.sqrt c • p)) =
              (Real.sqrt c ^ Module.finrank ℝ (Plane × Plane))⁻¹ *
                (∫ p : Plane × Plane, F p) := by
            rw [Measure.volume_eq_prod Plane Plane]
            simpa only [smul_eq_mul] using
              (Measure.integral_comp_smul_of_nonneg (volume.prod volume) F (Real.sqrt c)
                (hR := hsqrt.le))
          rw [hcomp, hdim]
    _ = c * ∫ p : Plane × Plane, F p := by
          have hfour : Real.sqrt c ^ 4 = c ^ 2 := by
            calc
              Real.sqrt c ^ 4 = (Real.sqrt c ^ 2) ^ 2 := by ring
              _ = c ^ 2 := by rw [Real.sq_sqrt hc.le]
          rw [hfour]
          field_simp [ne_of_gt hc]
    _ = c * continuumHeatProfile φ (c * r) := by rfl

/-- Dilation changes the heat-energy horizon by its scale. -/
theorem heatEnergy_dilate_eq (φ : Plane → ℝ) (hφ : Measurable φ) (hint : Integrable φ)
    (B : ℝ) (hB : ∀ x, |φ x| ≤ B) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    heatEnergy s (fun x => c * φ (Real.sqrt c • x)) = heatEnergy (c * s) φ := by
  have hB0 : 0 ≤ B := by
    have h := hB (0 : Plane)
    exact le_trans (abs_nonneg _) h
  let ψ : Plane → ℝ := fun x => c * φ (Real.sqrt c • x)
  have hψmeas : Measurable ψ := measurable_dilate φ hφ c
  have hψint : Integrable ψ := integrable_dilate φ hint hc
  have hψB : ∀ x, |ψ x| ≤ c * B := by
    intro x
    change |c * φ (Real.sqrt c • x)| ≤ c * B
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hB _) hc.le
  have hleft := heatEnergy_eq_profile_timeIntegral ψ hψmeas hψint (c * B) hψB hs
  have hright := heatEnergy_eq_profile_timeIntegral φ hφ hint B hB (mul_pos hc hs)
  have htime : (∫ r in (0 : ℝ)..s, continuumHeatProfile ψ r) =
      ∫ u in (0 : ℝ)..(c * s), continuumHeatProfile φ u := by
    calc
      (∫ r in (0 : ℝ)..s, continuumHeatProfile ψ r) =
          ∫ r in (0 : ℝ)..s, c * continuumHeatProfile φ (c * r) := by
            apply intervalIntegral.integral_congr
            intro r hr
            exact continuumHeatProfile_dilate φ hc
      _ = c * ∫ r in (0 : ℝ)..s, continuumHeatProfile φ (c * r) := by
            rw [intervalIntegral.integral_const_mul]
      _ = c * (c⁻¹ * ∫ u in (0 : ℝ)..(c * s), continuumHeatProfile φ u) := by
            rw [intervalIntegral.integral_comp_mul_left (f := continuumHeatProfile φ)
              (a := 0) (b := s) (c := c) (ne_of_gt hc)]
            simp only [smul_eq_mul, mul_zero]
      _ = ∫ u in (0 : ℝ)..(c * s), continuumHeatProfile φ u := by
            field_simp [ne_of_gt hc]
  calc
    heatEnergy s ψ = 4 * ∫ r in (0 : ℝ)..s, continuumHeatProfile ψ r := hleft.2
    _ = 4 * ∫ u in (0 : ℝ)..(c * s), continuumHeatProfile φ u := by rw [htime]
    _ = heatEnergy (c * s) φ := hright.2.symm

/-- The continuum heat energy varies continuously with the scale of a positive dilation. -/
theorem tendsto_heatEnergy_dilate (φ : Plane → ℝ) (hφ : Measurable φ)
    (hint : Integrable φ) (B : ℝ) (hB : ∀ x, |φ x| ≤ B)
    {c₀ s : ℝ} (hc₀ : 0 < c₀) (hs : 0 < s) :
    Tendsto (fun c => heatEnergy s (fun x => c * φ (Real.sqrt c • x)))
      (nhds c₀) (𝓝 (heatEnergy (c₀ * s) φ)) := by
  let S : ℝ := 2 * (c₀ * s)
  have hS : 0 < S := by dsimp [S]; positivity
  have hprof := heatEnergy_eq_profile_timeIntegral φ hφ hint B hB hS
  let P : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, continuumHeatProfile φ u
  have hprofOn : IntegrableOn (fun u : ℝ => continuumHeatProfile φ u)
      (Set.uIcc (0 : ℝ) S) volume := by
    rw [uIcc_of_le hS.le]
    exact hprof.1
  have hprimCont : ContinuousOn P (Set.Ioo (0 : ℝ) S) := by
    have hcont := intervalIntegral.continuousOn_primitive_interval hprofOn
    exact hcont.mono (by
      intro t ht
      rw [uIcc_of_le hS.le]
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hcSleft : 0 < c₀ * s := mul_pos hc₀ hs
  have hcSright : c₀ * s < S := by dsimp [S]; nlinarith [hcSleft]
  have hIoo : Set.Ioo (0 : ℝ) S ∈ 𝓝 (c₀ * s) := Ioo_mem_nhds hcSleft hcSright
  have hPcontAt := hprimCont.continuousAt hIoo
  have htimes : Tendsto (fun c => c * s) (nhds c₀) (nhds (c₀ * s)) := by
    exact (continuous_id.mul continuous_const).continuousAt.tendsto
  have hprimitiveTendsto : Tendsto (fun c => P (c * s)) (nhds c₀)
      (𝓝 (P (c₀ * s))) := hPcontAt.tendsto.comp htimes
  have hcenter := heatEnergy_eq_profile_timeIntegral φ hφ hint B hB hcSleft
  have henergyTendsto : Tendsto (fun c => 4 * P (c * s)) (nhds c₀)
      (𝓝 (heatEnergy (c₀ * s) φ)) := by
    have heq : 4 * P (c₀ * s) = heatEnergy (c₀ * s) φ := by
      simpa only [P] using hcenter.2.symm
    rw [← heq]
    exact (tendsto_const_nhds (x := (4 : ℝ))).mul hprimitiveTendsto
  have hEq : (fun c => heatEnergy (c * s) φ) =ᶠ[nhds c₀]
      fun c => 4 * P (c * s) := by
    filter_upwards [Ioi_mem_nhds hc₀] with c hc
    simpa [P] using (heatEnergy_eq_profile_timeIntegral φ hφ hint B hB
      (mul_pos hc hs)).2
  have hscaled : Tendsto (fun c => heatEnergy (c * s) φ) (nhds c₀)
      (𝓝 (heatEnergy (c₀ * s) φ)) := henergyTendsto.congr' hEq.symm
  have hEqD : (fun c => heatEnergy s (fun x => c * φ (Real.sqrt c • x))) =ᶠ[nhds c₀]
      fun c => heatEnergy (c * s) φ := by
    filter_upwards [Ioi_mem_nhds hc₀] with c hc
    exact heatEnergy_dilate_eq φ hφ hint B hB hc hs
  exact hscaled.congr' hEqD.symm

private theorem truncatedGreen_neg (L : ℕ) (z : Site) :
    MomentBounds.truncatedGreen L (-z) = MomentBounds.truncatedGreen L z := by
  simp [MomentBounds.truncatedGreen, Critical2DKPZ.Polymer.srwKernel_neg]

/-- Swapping the two spatial variables leaves the sampled Green kernel unchanged. -/
theorem integral_truncatedGreen_latticePoint_mixed_swap (N L : ℕ)
    (f g : Plane → ℝ) :
    (∫ p : Plane × Plane, |g p.1| * |f p.2| *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) =
    (∫ p : Plane × Plane, |f p.1| * |g p.2| *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) := by
  let F : Plane × Plane → ℝ := fun p => |f p.1| * |g p.2| *
    MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)
  have hkernel (p : Plane × Plane) :
      MomentBounds.truncatedGreen L (latticePoint N p.1 - latticePoint N p.2) =
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1) := by
    rw [show latticePoint N p.1 - latticePoint N p.2 =
      -(latticePoint N p.2 - latticePoint N p.1) by abel, truncatedGreen_neg]
  have hswap : (∫ p : Plane × Plane, F p.swap) = (∫ p : Plane × Plane, F p) := by
    rw [Measure.volume_eq_prod Plane Plane]
    exact MeasureTheory.integral_prod_swap F
  calc
    (∫ p : Plane × Plane, |g p.1| * |f p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) =
      ∫ p : Plane × Plane, F p.swap := by
        apply integral_congr_ae
        filter_upwards [] with p
        dsimp [F]
        rw [hkernel p]
        ring
    _ = ∫ p : Plane × Plane, F p := hswap
    _ = ∫ p : Plane × Plane, |f p.1| * |g p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1) := by rfl

/-- The sampled Green quadratic form is Lipschitz in `L¹` on profiles with bounded sup norm. -/
theorem integral_truncatedGreen_latticePoint_dilate_difference_le
    (N L : ℕ) (hN : 0 < N) (f g : Plane → ℝ)
    (hfi : Integrable f) (hgi : Integrable g)
    (Bf Bg : ℝ) (hfB : ∀ x, |f x| ≤ Bf) (hgB : ∀ x, |g x| ≤ Bg) :
    |(∫ p : Plane × Plane, |f p.1| * |f p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) -
      (∫ p : Plane × Plane, |g p.1| * |g p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1))| ≤
      (4 * (L : ℝ) / N) * (Bf + Bg) * (∫ x : Plane, |f x - g x|) := by
  let d : Plane → ℝ := fun x => f x - g x
  let K : Plane × Plane → ℝ := fun p =>
    MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)
  let Qf : Plane × Plane → ℝ := fun p => |f p.1| * |f p.2| * K p
  let Qg : Plane × Plane → ℝ := fun p => |g p.1| * |g p.2| * K p
  have hdi : Integrable d := hfi.sub hgi
  have hdBound (x : Plane) : |d x| ≤ Bf + Bg := by
    dsimp [d]
    calc
      |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
      _ ≤ Bf + Bg := add_le_add (hfB x) (hgB x)
  have hQf : Integrable Qf (volume.prod volume) := by
    simpa [Qf, K] using
      (integral_truncatedGreen_latticePoint_mixed_le N L hN f f hfi hfi Bf hfB).1
  have hQg : Integrable Qg (volume.prod volume) := by
    simpa [Qg, K] using
      (integral_truncatedGreen_latticePoint_mixed_le N L hN g g hgi hgi Bg hgB).1
  have hdiffInt : Integrable (fun p : Plane × Plane => Qf p - Qg p)
      (volume.prod volume) := hQf.sub hQg
  have hfirst := integral_truncatedGreen_latticePoint_mixed_le N L hN d f hdi hfi Bf hfB
  have hcrossSwap := integral_truncatedGreen_latticePoint_mixed_swap N L d g
  have hcrossInt1 : Integrable (fun p : Plane × Plane => |d p.1| * |f p.2| * K p)
      (volume.prod volume) := by simpa [K] using hfirst.1
  have hcrossInt2 : Integrable (fun p : Plane × Plane => |g p.1| * |d p.2| * K p)
      (volume.prod volume) := by
    simpa [K] using (integral_truncatedGreen_latticePoint_mixed_le N L hN g d hgi hdi
      (Bf + Bg) hdBound).1
  have hmajorInt : Integrable (fun p : Plane × Plane =>
      |d p.1| * |f p.2| * K p + |g p.1| * |d p.2| * K p)
      (volume.prod volume) := hcrossInt1.add hcrossInt2
  have hpoint (p : Plane × Plane) :
      |Qf p - Qg p| ≤
        |d p.1| * |f p.2| * K p + |g p.1| * |d p.2| * K p := by
    have hprod : abs (abs (f p.1) * abs (f p.2) - abs (g p.1) * abs (g p.2)) ≤
        |d p.1| * |f p.2| + |g p.1| * |d p.2| := by
      calc
        _ = abs ((abs (f p.1) - abs (g p.1)) * abs (f p.2) +
            abs (g p.1) * (abs (f p.2) - abs (g p.2))) := by congr 1; ring
        _ ≤ abs ((abs (f p.1) - abs (g p.1)) * abs (f p.2)) +
            abs (abs (g p.1) * (abs (f p.2) - abs (g p.2))) := abs_add_le _ _
        _ = abs (abs (f p.1) - abs (g p.1)) * abs (f p.2) +
            abs (g p.1) * abs (abs (f p.2) - abs (g p.2)) := by simp [abs_mul]
        _ ≤ |d p.1| * |f p.2| + |g p.1| * |d p.2| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (by simpa [d] using abs_abs_sub_abs_le_abs_sub (f p.1) (g p.1))
              (abs_nonneg _))
            (mul_le_mul_of_nonneg_left
              (by simpa [d] using abs_abs_sub_abs_le_abs_sub (f p.2) (g p.2))
              (abs_nonneg _))
    have hKnonneg : 0 ≤ K p := MomentBounds.truncatedGreen_nonneg L _
    dsimp [Qf, Qg]
    have hfact : |f p.1| * |f p.2| * K p - |g p.1| * |g p.2| * K p =
        (|f p.1| * |f p.2| - |g p.1| * |g p.2|) * K p := by ring
    rw [hfact, abs_mul, abs_of_nonneg hKnonneg]
    calc
      _ ≤ (|d p.1| * |f p.2| + |g p.1| * |d p.2|) * K p :=
        mul_le_mul_of_nonneg_right hprod hKnonneg
      _ = |d p.1| * |f p.2| * K p + |g p.1| * |d p.2| * K p := by rw [add_mul]
  have hnormDiff : Integrable (fun p : Plane × Plane => |Qf p - Qg p|)
      (volume.prod volume) := by
    simpa only [Real.norm_eq_abs] using hdiffInt.norm
  have hintAbs :
      |(∫ p : Plane × Plane, Qf p) - ∫ p : Plane × Plane, Qg p| ≤
        ∫ p : Plane × Plane, |Qf p - Qg p| := by
    have hsub : (∫ p : Plane × Plane, Qf p - Qg p) =
        (∫ p : Plane × Plane, Qf p) - ∫ p : Plane × Plane, Qg p :=
      integral_sub hQf hQg
    calc
      _ = |∫ p : Plane × Plane, Qf p - Qg p| := congrArg abs hsub.symm
      _ ≤ ∫ p : Plane × Plane, |Qf p - Qg p| := abs_integral_le_integral_abs
  have hmono := integral_mono hnormDiff hmajorInt hpoint
  have hsumBound :
      (∫ p : Plane × Plane, |d p.1| * |f p.2| * K p +
        |g p.1| * |d p.2| * K p) ≤
      (4 * (L : ℝ) / N) * Bf * (∫ x : Plane, |d x|) +
        (4 * (L : ℝ) / N) * Bg * (∫ x : Plane, |d x|) := by
    have hswap' : (∫ p : Plane × Plane, |g p.1| * |d p.2| * K p) =
        ∫ p : Plane × Plane, |d p.1| * |g p.2| * K p := by
      simpa [K] using hcrossSwap
    have hsecondBound :=
      (integral_truncatedGreen_latticePoint_mixed_le N L hN d g hdi hgi Bg hgB).2
    have hsumInt :
        (∫ p : Plane × Plane, |d p.1| * |f p.2| * K p +
          |g p.1| * |d p.2| * K p) =
        (∫ p : Plane × Plane, |d p.1| * |f p.2| * K p) +
          ∫ p : Plane × Plane, |g p.1| * |d p.2| * K p := by
      simpa only [Measure.volume_eq_prod Plane Plane] using
        (integral_add (μ := volume.prod volume) hcrossInt1 hcrossInt2)
    calc
      _ = (∫ p : Plane × Plane, |d p.1| * |f p.2| * K p) +
          ∫ p : Plane × Plane, |d p.1| * |g p.2| * K p := by
            rw [hsumInt, hswap']
      _ ≤ _ := add_le_add hfirst.2 hsecondBound
  calc
    |(∫ p : Plane × Plane, Qf p) - ∫ p : Plane × Plane, Qg p| ≤
        ∫ p : Plane × Plane, |Qf p - Qg p| := hintAbs
    _ ≤ ∫ p : Plane × Plane,
        (|d p.1| * |f p.2| * K p + |g p.1| * |d p.2| * K p) := hmono
    _ ≤ (4 * (L : ℝ) / N) * Bf * (∫ x : Plane, |d x|) +
        (4 * (L : ℝ) / N) * Bg * (∫ x : Plane, |d x|) := hsumBound
    _ = (4 * (L : ℝ) / N) * (Bf + Bg) * (∫ x : Plane, |d x|) := by ring
    _ = _ := by rfl

/-- The lattice Green energy converges uniformly over a compact interval of positive dilations. -/
theorem integral_truncatedGreen_latticePoint_le_dilate (δ : ℝ) (hδ : 0 < δ)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hint : Integrable φ)
    (hb : ∃ M : ℝ, ∀ x, |φ x| ≤ M) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ c ∈ Set.Icc c₀ c₁,
      ∫ p : Plane × Plane, |c * φ (Real.sqrt c • p.1)| * |c * φ (Real.sqrt c • p.2)| *
          MomentBounds.truncatedGreen (evenCeil (Real.sqrt δ * N))
            (latticePoint N p.2 - latticePoint N p.1) ≤
        heatEnergy (Real.sqrt δ) (fun y => c * φ (Real.sqrt c • y)) + ε := by
  classical
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := by
    have h := hB (0 : Plane)
    exact le_trans (abs_nonneg _) h
  let s : ℝ := Real.sqrt δ
  have hs : 0 < s := Real.sqrt_pos.2 hδ
  by_cases hc₀₁ : c₀ ≤ c₁
  · have hc₁ : 0 < c₁ := lt_of_lt_of_le hc₀ hc₀₁
    have hcommonB : 0 ≤ c₁ * B := mul_nonneg hc₁.le hB0
    let G : ℕ → ℝ → ℝ := fun N c =>
      ∫ p : Plane × Plane, |c * φ (Real.sqrt c • p.1)| *
        |c * φ (Real.sqrt c • p.2)| *
        MomentBounds.truncatedGreen (evenCeil (s * N))
          (latticePoint N p.2 - latticePoint N p.1)
    let E : ℝ → ℝ := fun c =>
      heatEnergy s (fun x => c * φ (Real.sqrt c • x))
    intro ε hε
    let D : ℝ := 4 * (s + 2) * (2 * (c₁ * B))
    let η : ℝ := ε / (3 * (D + 1))
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hη : 0 < η := by dsimp [η]; positivity
    have hηD : (D + 1) * η = ε / 3 := by
      dsimp [η]
      have hden : 3 * (D + 1) ≠ 0 := by positivity
      field_simp [hden]
    let Kset : Set ℝ := Set.Icc c₀ c₁
    let Cset := {a : ℝ // a ∈ Kset}
    have hlocal : ∀ a : Cset, ∃ r : ℝ, 0 < r ∧ ∀ c : ℝ,
        dist c a.1 < r →
          (∫ x : Plane, |c * φ (Real.sqrt c • x) - a.1 * φ (Real.sqrt a.1 • x)|) < η ∧
          |E c - E a.1| < η := by
      intro a
      have ha : 0 < a.1 := lt_of_lt_of_le hc₀ a.2.1
      have hL1 := tendsto_integral_abs_dilate φ hint ha
      have hL1event := hL1.eventually (Iio_mem_nhds hη)
      have hEcenter : E a.1 = heatEnergy (a.1 * s) φ := by
        simpa only [E] using heatEnergy_dilate_eq φ hφ hint B hB ha hs
      have hE0 := tendsto_heatEnergy_dilate φ hφ hint B hB ha hs
      rw [← hEcenter] at hE0
      have hEevent0 := hE0.eventually (Metric.ball_mem_nhds (E a.1) hη)
      have hEevent : ∀ᶠ c in nhds a.1, |E c - E a.1| < η := by
        filter_upwards [hEevent0] with c hc
        simpa only [Metric.mem_ball, Real.dist_eq] using hc
      have hboth : ∀ᶠ c in nhds a.1,
          (∫ x : Plane, |c * φ (Real.sqrt c • x) - a.1 * φ (Real.sqrt a.1 • x)|) < η ∧
            |E c - E a.1| < η := hL1event.and hEevent
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hboth
      exact ⟨r, hr, fun c hc => hball hc⟩
    choose radius hradius hsmall using hlocal
    let U : Cset → Set ℝ := fun a => Metric.ball a.1 (radius a)
    have hUopen (a : Cset) : IsOpen (U a) := Metric.isOpen_ball
    have hcover : Kset ⊆ ⋃ a : Cset, U a := by
      intro c hc
      let a : Cset := ⟨c, hc⟩
      exact Set.mem_iUnion.mpr ⟨a, Metric.mem_ball_self (hradius a)⟩
    obtain ⟨t, htcover⟩ := isCompact_Icc.elim_finite_subcover U hUopen
      (by simpa [Kset] using hcover)
    have hfixed (a : Cset) : ∀ᶠ N : ℕ in atTop, G N a.1 ≤ E a.1 + ε / 3 := by
      have ha : 0 < a.1 := lt_of_lt_of_le hc₀ a.2.1
      have haMeas : Measurable (fun x : Plane => a.1 * φ (Real.sqrt a.1 • x)) :=
        measurable_dilate φ hφ a.1
      have haInt : Integrable (fun x : Plane => a.1 * φ (Real.sqrt a.1 • x)) :=
        integrable_dilate φ hint ha
      have haBound : ∀ x, |a.1 * φ (Real.sqrt a.1 • x)| ≤ c₁ * B := by
        intro x
        rw [abs_mul, abs_of_pos ha]
        exact mul_le_mul a.2.2 (hB _) (abs_nonneg _) hc₁.le
      have hfixed' := integral_truncatedGreen_latticePoint_le δ hδ
        (fun x : Plane => a.1 * φ (Real.sqrt a.1 • x)) haMeas haInt
        ⟨c₁ * B, haBound⟩ (ε / 3) (by linarith)
      simpa [G, E, s] using hfixed'
    have hfixedAll : ∀ᶠ N : ℕ in atTop, ∀ a ∈ t, G N a.1 ≤ E a.1 + ε / 3 :=
      (Filter.eventually_all_finset t).2 (fun a _ => hfixed a)
    have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
    filter_upwards [hfixedAll, hNpos] with N hfixedN hN
    intro c hc
    obtain ⟨a, haT, hca⟩ := Set.mem_iUnion₂.mp (htcover hc)
    have hdist : dist c a.1 < radius a := by
      simpa [U, dist_comm] using hca
    have hnear := hsmall a c hdist
    have hcaPos : 0 < c := lt_of_lt_of_le hc₀ hc.1
    have hcInt : Integrable (fun x : Plane => c * φ (Real.sqrt c • x)) :=
      integrable_dilate φ hint hcaPos
    have haInt : Integrable (fun x : Plane => a.1 * φ (Real.sqrt a.1 • x)) :=
      integrable_dilate φ hint (lt_of_lt_of_le hc₀ a.2.1)
    have hcBound : ∀ x, |c * φ (Real.sqrt c • x)| ≤ c₁ * B := by
      intro x
      rw [abs_mul, abs_of_pos hcaPos]
      exact mul_le_mul hc.2 (hB _) (abs_nonneg _) hc₁.le
    have haBound : ∀ x, |a.1 * φ (Real.sqrt a.1 • x)| ≤ c₁ * B := by
      intro x
      rw [abs_mul, abs_of_pos (lt_of_lt_of_le hc₀ a.2.1)]
      exact mul_le_mul a.2.2 (hB _) (abs_nonneg _) hc₁.le
    let L : ℕ := evenCeil (s * N)
    have hceil : (L : ℝ) < s * N + 2 := by
      dsimp [L]
      exact evenCeil_lt_add_two (mul_nonneg hs.le (Nat.cast_nonneg N))
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hNge : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hratio : (L : ℝ) / N < s + 2 := by
      have hceilDiv : (L : ℝ) / N < (s * N + 2) / N :=
        (div_lt_div_of_pos_right hceil hNr)
      have hdiv : (s * N + 2) / N ≤ s + 2 := by
        apply (div_le_iff₀ hNr).2
        nlinarith [hs.le, hNge]
      exact hceilDiv.trans_le hdiv
    have hgreenDiff := integral_truncatedGreen_latticePoint_dilate_difference_le
      N L hN (fun x : Plane => c * φ (Real.sqrt c • x))
      (fun x : Plane => a.1 * φ (Real.sqrt a.1 • x)) hcInt haInt
      (c₁ * B) (c₁ * B) hcBound haBound
    have hgreenErr : |G N c - G N a.1| ≤ D * η := by
      have hcoeff : 0 ≤ 4 * (L : ℝ) / N := by positivity
      have hboundCoeff : (4 * (L : ℝ) / N) * (2 * (c₁ * B)) ≤ D := by
        dsimp [D]
        have hL : (L : ℝ) ≤ (s + 2) * N := by
          have hL' := (div_lt_iff₀ hNr).mp hratio
          exact hL'.le
        have hfour : 4 * (L : ℝ) / N ≤ 4 * (s + 2) := by
          apply (div_le_iff₀ hNr).2
          nlinarith [hL]
        exact mul_le_mul_of_nonneg_right hfour (by positivity)
      calc
        |G N c - G N a.1| ≤
            (4 * (L : ℝ) / N) * (2 * (c₁ * B)) *
              (∫ x : Plane, |c * φ (Real.sqrt c • x) - a.1 * φ (Real.sqrt a.1 • x)|) := by
                simpa [G, L, s, two_mul] using hgreenDiff
        _ ≤ (4 * (L : ℝ) / N) * (2 * (c₁ * B)) * η :=
              mul_le_mul_of_nonneg_left (le_of_lt hnear.1) (by positivity)
        _ ≤ D * η := mul_le_mul_of_nonneg_right hboundCoeff hη.le
    have henergyErr : E a.1 ≤ E c + η := by
      have habs : |E c - E a.1| < η := hnear.2
      have hrev : |E a.1 - E c| < η := by simpa [abs_sub_comm] using habs
      have hle : E a.1 - E c ≤ |E a.1 - E c| := le_abs_self _
      linarith
    have hcenterN := hfixedN a haT
    have hgreenUpper : G N c ≤ G N a.1 + D * η := by
      have hsub : G N c - G N a.1 ≤ D * η :=
        (le_abs_self (G N c - G N a.1)).trans hgreenErr
      linarith
    have hstrict : G N c < E c + ε := by
      calc
        G N c ≤ G N a.1 + D * η := hgreenUpper
        _ ≤ E a.1 + ε / 3 + D * η := by linarith
        _ ≤ E c + η + ε / 3 + D * η := by linarith
        _ < E c + ε := by linarith [hηD, hε]
    exact hstrict.le
  · intro ε hε
    filter_upwards [] with N
    intro c hc
    exact (hc₀₁ (le_trans hc.1 hc.2)).elim

end Critical2DKPZ.Smoothing

end
