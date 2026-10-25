/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.UnitHorizonPerturbed
public import Critical2DKPZ.Smoothing.EnergyDilateDiagonal
public import Critical2DKPZ.Smoothing.EnergyDilateUniform
import Mathlib.Tactic

/-! # Unit-horizon perturbation bounds for compact dilation families -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BoundedContinuousFunction Topology

namespace Critical2DKPZ.Smoothing

/-- The width-perturbation and one-point moment bounds imply a unit-horizon heat-energy estimate uniform over compact intervals of positive test dilations. -/
theorem latticeSmoothingError_unit_le_energy_dilate_of_perturb
    (hP : LatticeSmoothingPerturbBound) (hVD : PropVDBound)
    (hO : FutureProfiles.PropPFOriginBound) (hL : FutureProfiles.LogTailsOriginBound) :
    LatticeSmoothingErrorEnergyDilate := by
  intro A H
  obtain ⟨CD, δD, hδD, hD⟩ :=
    latticeSmoothingError_diagonal_unit_le_energy_dilate_of hVD hO hL A H
  let C : ℝ := |CD| + 1
  let δ₁ : ℝ := min δD (Real.exp (-1))
  have hC : 0 < C := by dsimp [C]; positivity
  have hCD : CD ≤ C := by dsimp [C]; linarith [le_abs_self CD]
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  refine ⟨C, δ₁, hδ₁, ?_⟩
  intro δ hδ hδ₁' φ hφ hφc hφint hφB c₀ c₁ hc₀ ε hε
  obtain ⟨B, hB⟩ := hφB
  have hδD' : δ < δD := lt_of_lt_of_le hδ₁' (min_le_left _ _)
  have hδexp : δ < Real.exp (-1) := lt_of_lt_of_le hδ₁' (min_le_right _ _)
  have hδone : δ < 1 := lt_trans hδexp (by norm_num [Real.exp_lt_one_iff])
  have hlog : 0 < |Real.log δ| := by
    apply abs_pos.mpr
    have hlog' : Real.log δ < -1 := by
      calc
        Real.log δ < Real.log (Real.exp (-1)) := Real.log_lt_log hδ hδexp
        _ = -1 := Real.log_exp _
    linarith
  have hεhalf : 0 < ε / 2 := by linarith
  let M₁ : ℝ := ∫ x, |φ x|
  let M₂ : ℝ := c₁ * B
  have hM₁ : 0 ≤ M₁ := by
    dsimp [M₁]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => abs_nonneg (φ x))
  have hPevent := hP A H M₁ M₂ δ hδ hδone (ε / 2) hεhalf
  have hDevent := hD δ hδ hδD' φ hφ hφc hφint ⟨B, hB⟩
    c₀ c₁ hc₀ (ε / 2) hεhalf
  filter_upwards [hPevent, hDevent] with M hPbound hDbound
  intro hMeven c hc ϑ hϑ j k hj hk hjlo hjhi hklo hkhi h₀ hh₀
  have hcpos : 0 < c := lt_of_lt_of_le hc₀ hc.1
  have hc₁pos : 0 < c₁ := lt_of_lt_of_le hc₀ (le_trans hc.1 hc.2)
  let ψ : Plane → ℝ := fun x => c * φ (Real.sqrt c • x)
  have hψmeas : Measurable ψ := measurable_dilate φ hφ c
  have hψc : HasCompactSupport ψ := hasCompactSupport_dilate φ hφc hcpos
  have hψint : Integrable ψ := integrable_dilate φ hφint hcpos
  have hmass : (∫ x, |ψ x|) = ∫ x, |φ x| := integral_abs_dilate_eq φ hφint hcpos
  have hmassM₁ : M₁ = ∫ x, |ψ x| := by simpa [M₁] using hmass.symm
  have hBψ : ∀ x, |ψ x| ≤ c₁ * B := by
    intro x
    change |c * φ (Real.sqrt c • x)| ≤ c₁ * B
    rw [abs_mul, abs_of_pos hcpos]
    exact mul_le_mul hc.2 (hB _) (abs_nonneg _) hc₁pos.le
  have hDboundc := hDbound hMeven c hc ϑ hϑ h₀ hh₀
  let p : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ ψ ω -
      latticeSmoothingError (criticalBeta ϑ M) M M (evenCeil (δ * M))
        (evenCeil (δ * M)) h₀ ψ ω
  let d : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M
      (evenCeil (δ * M)) (evenCeil (δ * M)) h₀ ψ ω
  let e : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ ψ ω
  have hpbound : eLpNorm p 2 disorderLaw ≤ ENNReal.ofReal (ε / 2) := by
    simpa only [p, M₁, M₂] using hPbound hMeven ϑ hϑ j k hj hk hjlo hjhi hklo hkhi
      h₀ hh₀ ψ hψmeas hψc (by simpa [M₁] using hmass.le) (by dsimp [M₂]; exact hBψ)
  have henergy : 0 ≤ heatEnergy (Real.sqrt δ) ψ :=
    (heatEnergy_le_of_bounded ψ hψmeas hψint (c₁ * B) hBψ
      (Real.sqrt_pos.2 hδ)).1
  have hpow : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hlogDen : 0 ≤ |Real.log δ| := hlog.le
  have hroot : Real.sqrt (CD * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) ≤
      Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hlogDen
    exact mul_le_mul_of_nonneg_right hCD henergy
  have hL1pow : 0 ≤ M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) :=
    mul_nonneg hM₁ hpow
  have hlogTerm : CD * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) ≤
      C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
    calc
      CD * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) =
          CD * (M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40)) := by ring
      _ ≤ C * (M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40)) :=
        mul_le_mul_of_nonneg_right hCD hL1pow
      _ = C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) := by ring
  have hDbound' : eLpNorm d 2 disorderLaw ≤ ENNReal.ofReal
      (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
        C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) := by
    have hraw : eLpNorm d 2 disorderLaw ≤ ENNReal.ofReal
        (Real.sqrt (CD * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
          CD * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) := by
      simpa [d, ψ, abs_mul, abs_of_pos hcpos, hmassM₁] using hDboundc
    have hreal : Real.sqrt (CD * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
        CD * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 ≤
        Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
          C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 := by
      linarith [hroot, hlogTerm]
    exact hraw.trans (ENNReal.ofReal_le_ofReal hreal)
  have hdecomp : e = p + d := by
    funext ω
    dsimp [e, p, d]
    ring
  have htriangle : eLpNorm (p + d) 2 disorderLaw ≤
      eLpNorm p 2 disorderLaw + eLpNorm d 2 disorderLaw :=
    eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have htargetNonneg : 0 ≤
      Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
        C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 := by
    positivity
  have hfinal : eLpNorm e 2 disorderLaw ≤ ENNReal.ofReal
      (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
        C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
    calc
      eLpNorm e 2 disorderLaw = eLpNorm (p + d) 2 disorderLaw := by rw [hdecomp]
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal
          (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
            C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) :=
        htriangle.trans (add_le_add hpbound hDbound')
      _ = ENNReal.ofReal
          (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
            C * M₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
        rw [← ENNReal.ofReal_add (by positivity) htargetNonneg]
        congr 1
        ring
  simpa [ψ, abs_mul, abs_of_pos hcpos, hmassM₁] using hfinal
end Critical2DKPZ.Smoothing

end
