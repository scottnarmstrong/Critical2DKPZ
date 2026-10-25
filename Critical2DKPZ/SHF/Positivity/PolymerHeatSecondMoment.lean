/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.PolymerHeatProfile
public import Critical2DKPZ.SHF.Positivity.HeatCellProfileBounds
public import Critical2DKPZ.SHF.Positivity.HeatClockBounds
public import Critical2DKPZ.MomentBounds.CSZ25Variance
public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
import Mathlib.Tactic

/-! # Uniform second moment of the polymer heat-start pairing -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open ProbabilityTheory
open Critical2DKPZ.SHF.Limit
open scoped Topology

namespace Critical2DKPZ.SHF.Positivity

/-- At fixed positive time and heat scales, the polymer heat-start pairing has integrable squares with an eventual uniform second-moment bound. -/
theorem polymer_heat_pairing_sq_integral_bounded (ϑ : ℝ) {s t δ : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (∫ p, heatKernel δ (p.1 - x)
        ∂(polymerMeasure ϑ N s t ω)) ^ 2) disorderLaw ∧
      ∫ ω, (∫ p, heatKernel δ (p.1 - x)
        ∂(polymerMeasure ϑ N s t ω)) ^ 2 ∂disorderLaw ≤ C := by
  let T : ℝ := t - s + 2
  let κ : ℝ := (2 * Real.pi * δ)⁻¹
  obtain ⟨C₀, hC₀⟩ := OnePoint.sigmaSq_secondMoment_le_uniform |ϑ| T
  have hclock := eventually_evenClock_duration_bounds hs hst
  have hT : 0 < T := by dsimp [T]; linarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hden : 0 < Real.log (1 + 1 / T) := by
    apply Real.log_pos
    have : 0 < 1 / T := one_div_pos.mpr hT
    linarith
  let C : ℝ := 1 + T * 4 * κ * (max C₀ 0 / Real.log (1 + 1 / T))
  refine ⟨C, ?_⟩
  filter_upwards [hclock, hC₀] with N hN hmoment
  have hN1 : 1 ≤ N := hN.1
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  let L := b - a
  have hab : a ≤ b := by
    dsimp [a, b]
    exact evenCeil_mono (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  have hLcast : (L : ℝ) = (b : ℝ) - a := by
    dsimp [L]
    exact Nat.cast_sub hab
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    rw [hLcast]
    exact hN.2.1
  have hLupper : (L : ℝ) ≤ T * N := by
    rw [hLcast]
    simpa only [a, b, T] using hN.2.2
  let ν : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x)
  have hν := heatCellProfile_bounds hN1 hδ x
  have hν0 : ∀ w, 0 ≤ ν w := by simpa only [ν] using hν.1
  have hνsum : Summable ν := by simpa only [ν] using hν.2.1
  have hν1 : (∑' w, ν w) = 1 := by simpa only [ν] using hν.2.2.1
  have hgreen := greenEnergy_heatCell_le L hN1 hδ x
  have hscaleMoment := hmoment ϑ ⟨neg_abs_le ϑ, le_abs_self ϑ⟩
    L (by exact_mod_cast hL1) (by simpa only [T] using hLupper)
  have hlogCompare : Real.log (1 + 1 / T) ≤ Real.log (1 + (N : ℝ) / L) := by
    apply Real.log_le_log
    · positivity
    · have hLpos : 0 < (L : ℝ) := lt_of_lt_of_le zero_lt_one hL1
      have hratio : 1 / T ≤ (N : ℝ) / L := by
        apply (div_le_div_iff₀ hT hLpos).2
        dsimp [T] at hLupper ⊢
        nlinarith
      linarith
  have hlogL : 0 < Real.log (1 + (N : ℝ) / L) :=
    lt_of_lt_of_le hden hlogCompare
  have hqnonneg : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ N) *
      Renewal.freeSecondMoment (criticalBeta ϑ N) L := by
    apply mul_nonneg
    · unfold Polymer.sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
    · rw [Renewal.freeSecondMoment]
      exact integral_nonneg fun ω => sq_nonneg _
  have hscaleMoment' : Polymer.sigmaSq (criticalBeta ϑ N) *
      Renewal.freeSecondMoment (criticalBeta ϑ N) L ≤
      C₀ / Real.log (1 + (N : ℝ) / L) := by
    simpa only [Renewal.freeSecondMoment] using hscaleMoment
  have hqBound : Polymer.sigmaSq (criticalBeta ϑ N) *
      Renewal.freeSecondMoment (criticalBeta ϑ N) L ≤
        max C₀ 0 / Real.log (1 + 1 / T) := by
    by_cases hC₀nonneg : 0 ≤ C₀
    · calc
        _ ≤ C₀ / Real.log (1 + (N : ℝ) / L) := hscaleMoment'
        _ ≤ C₀ / Real.log (1 + 1 / T) :=
          div_le_div_of_nonneg_left hC₀nonneg hden hlogCompare
        _ ≤ max C₀ 0 / Real.log (1 + 1 / T) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hden.le
    · have hC₀nonpos : C₀ ≤ 0 := le_of_not_ge hC₀nonneg
      have hCquot : C₀ / Real.log (1 + (N : ℝ) / L) ≤ 0 :=
        (div_le_iff₀ hlogL).2 (by simpa using hC₀nonpos)
      have hqle : Polymer.sigmaSq (criticalBeta ϑ N) *
          Renewal.freeSecondMoment (criticalBeta ϑ N) L ≤ 0 := hscaleMoment'.trans hCquot
      have hqeq : Polymer.sigmaSq (criticalBeta ϑ N) *
          Renewal.freeSecondMoment (criticalBeta ϑ N) L = 0 := le_antisymm hqle hqnonneg
      rw [hqeq]
      positivity
  have hcellScale : (L : ℝ) * ((4 / (N : ℝ)) * κ) ≤ T * 4 * κ := by
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hdiv : (L : ℝ) / N ≤ T := (div_le_iff₀ hNposR).2
      (by simpa only [mul_comm] using hLupper)
    calc
      (L : ℝ) * ((4 / (N : ℝ)) * κ) = 4 * ((L : ℝ) / N) * κ := by
        field_simp [ne_of_gt hNposR]
      _ ≤ 4 * T * κ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiv (by norm_num)) hκ.le
      _ = T * 4 * κ := by ring
  have hσFnonneg : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ N) *
      Renewal.freeSecondMoment (criticalBeta ϑ N) L := hqnonneg
  have hvarBound : MomentBounds.greenEnergy L ν * Polymer.sigmaSq (criticalBeta ϑ N) *
      Renewal.freeSecondMoment (criticalBeta ϑ N) L ≤
        T * 4 * κ * (max C₀ 0 / Real.log (1 + 1 / T)) := by
    have hgreen0 : 0 ≤ MomentBounds.greenEnergy L ν :=
      MomentBounds.greenEnergy_nonneg L ν hν0
    have hgreen' : MomentBounds.greenEnergy L ν ≤ (L : ℝ) * ((4 / (N : ℝ)) * κ) := by
      simpa only [ν, mul_assoc, mul_left_comm, mul_comm, κ] using hgreen
    have hmasscaled : MomentBounds.greenEnergy L ν *
        (Polymer.sigmaSq (criticalBeta ϑ N) * Renewal.freeSecondMoment (criticalBeta ϑ N) L) ≤
        (T * 4 * κ) * (max C₀ 0 / Real.log (1 + 1 / T)) := by
      calc
        _ ≤ ((L : ℝ) * ((4 / (N : ℝ)) * κ)) *
            (Polymer.sigmaSq (criticalBeta ϑ N) * Renewal.freeSecondMoment (criticalBeta ϑ N) L) :=
          mul_le_mul_of_nonneg_right hgreen' hσFnonneg
        _ ≤ (T * 4 * κ) *
            (Polymer.sigmaSq (criticalBeta ϑ N) * Renewal.freeSecondMoment (criticalBeta ϑ N) L) :=
          mul_le_mul_of_nonneg_right hcellScale hσFnonneg
        _ ≤ (T * 4 * κ) * (max C₀ 0 / Real.log (1 + 1 / T)) :=
          mul_le_mul_of_nonneg_left hqBound (by positivity)
    simpa only [mul_assoc] using hmasscaled
  let F : Disorder → ℝ := profileP2Fun (criticalBeta ϑ N) 0 L ν (fun _ => 1)
  let G : Disorder → ℝ := profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1)
  have hFmeas : Measurable F := by
    dsimp [F]
    exact Polymer.measurable_profileP2Fun (criticalBeta ϑ N) 0 L ν (fun _ => 1)
  have hFmem : MemLp F 2 disorderLaw := by
    dsimp [F]
    exact Polymer.memLp_profile_probability (criticalBeta ϑ N) 0 L ν (fun _ => 1)
      hν0 hν1 1 zero_le_one (fun _ => by norm_num) 2 (by norm_num)
  have hF0 : ∀ ω, 0 ≤ F ω := by
    intro ω
    dsimp [F]
    unfold profileP2Fun
    apply tsum_nonneg
    intro w
    apply mul_nonneg (hν0 w)
    apply tsum_nonneg
    intro z
    exact mul_nonneg (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (by norm_num)
  have hmean : (∫ ω, F ω ∂disorderLaw) = 1 := by
    dsimp [F]
    exact Polymer.integral_profile_flat_probability (criticalBeta ϑ N) 0 L ν hν0 hν1
  have hsecondEq : (∫ ω, F ω ^ 2 ∂disorderLaw) = Var[F; disorderLaw] + 1 := by
    have hpow : (fun ω => F ω ^ 2) = F ^ 2 := rfl
    rw [hpow, variance_eq_sub hFmem, hmean]
    ring
  have hshift : G = fun ω => F (Smoothing.shiftEnvironment a ω) := by
    funext ω
    dsimp [F, G]
    have htime := Smoothing.profileP2Fun_timeShift_sub (criticalBeta ϑ N)
      (d := a) (a := a) (b := b) (ν := ν) (f := fun _ => (1 : ℝ)) (ω := ω)
      (by omega) hab
    simpa only [Nat.sub_self] using htime
  have hG0 : ∀ ω, 0 ≤ G ω := by
    intro ω
    rw [hshift]
    exact hF0 _
  have hGpow : Integrable (fun ω => G ω ^ 2) disorderLaw := by
    have h : Integrable (fun ω => |G ω| ^ 2) disorderLaw := by
      dsimp [G]
      exact Polymer.integrable_abs_pow_profile_probability
        (criticalBeta ϑ N) a b ν (fun _ => 1) hν0 hν1 1 zero_le_one
        (fun _ => by norm_num) 2
    have heq : (fun ω => |G ω| ^ 2) = fun ω => G ω ^ 2 := by
      funext ω
      rw [abs_of_nonneg (hG0 ω)]
    exact heq ▸ h
  have hvarEq : Var[F; disorderLaw] = Var[G; disorderLaw] := by
    rw [hshift]
    exact ((Smoothing.measurePreserving_shiftEnvironment a).variance_fun_comp
      hFmeas.aemeasurable).symm
  have hvariance := MomentBounds.variance_profileP2Fun_bounds
    (criticalBeta ϑ N) L ν hν0 hνsum
  have hvarBound' : Var[G; disorderLaw] ≤
      T * 4 * κ * (max C₀ 0 / Real.log (1 + 1 / T)) := by
    rw [← hvarEq]
    calc
      Var[F; disorderLaw] ≤
          MomentBounds.greenEnergy L ν * Polymer.sigmaSq (criticalBeta ϑ N) *
            Renewal.freeSecondMoment (criticalBeta ϑ N) L := hvariance.2
      _ ≤ _ := hvarBound
  let A : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x) ∂polymerMeasure ϑ N s t ω
  have hAeq : ∀ᵐ ω ∂disorderLaw, A ω = G ω := by
    filter_upwards [ae_integral_heatKernel_polymerMeasure_eq ϑ hN1 hs hst hδ x] with ω hω
    simpa only [A, G, ν, a, b, L] using hω
  have hAint : Integrable (fun ω => A ω ^ 2) disorderLaw := by
    apply hGpow.congr
    filter_upwards [hAeq] with ω hω
    rw [hω]
  have hAintEq : (∫ ω, A ω ^ 2 ∂disorderLaw) = ∫ ω, G ω ^ 2 ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [hAeq] with ω hω
    rw [hω]
  have hGsecond : (∫ ω, G ω ^ 2 ∂disorderLaw) = Var[G; disorderLaw] + 1 := by
    have hmeanG : (∫ ω, G ω ∂disorderLaw) = 1 := by
      dsimp [G]
      exact Polymer.integral_profile_flat_probability (criticalBeta ϑ N) a b ν hν0 hν1
    have hGmem : MemLp G 2 disorderLaw := by
      dsimp [G]
      exact Polymer.memLp_profile_probability (criticalBeta ϑ N) a b ν (fun _ => 1)
        hν0 hν1 1 zero_le_one (fun _ => by norm_num) 2 (by norm_num)
    have hpow : (fun ω => G ω ^ 2) = G ^ 2 := rfl
    rw [hpow, variance_eq_sub hGmem, hmeanG]
    ring
  have hfinal : (∫ ω, A ω ^ 2 ∂disorderLaw) ≤ C := by
    rw [hAintEq, hGsecond]
    dsimp [C]
    linarith only [hvarBound']
  exact ⟨hAint, hfinal⟩

end Critical2DKPZ.SHF.Positivity

end
