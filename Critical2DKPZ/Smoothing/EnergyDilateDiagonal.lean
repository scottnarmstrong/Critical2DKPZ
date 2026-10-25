/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.UnitHorizonBounds
public import Critical2DKPZ.Smoothing.EnergyDilateLocalLog
public import Critical2DKPZ.Smoothing.EnergyDilateUniform
import Mathlib.Tactic

/-! # Diagonal smoothing energy bounds for compact dilation families -/

@[expose] public section

open MeasureTheory Filter Set
open scoped BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.Smoothing

/-- At equal smoothing clocks, the unit-horizon logarithmic error satisfies a heat-energy bound uniform over compact intervals of positive test dilations. -/
theorem latticeSmoothingError_diagonal_unit_le_energy_dilate_of (hVD : PropVDBound)
    (hO : FutureProfiles.PropPFOriginBound) (hL : FutureProfiles.LogTailsOriginBound) (A H : ℝ) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ → Integrable φ →
        (∃ B : ℝ, ∀ x, |φ x| ≤ B) → ∀ c₀ c₁ : ℝ, 0 < c₀ → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ M : ℕ in atTop, Even M → ∀ c ∈ Set.Icc c₀ c₁, ∀ ϑ ∈ Set.Icc (-A) A,
            ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
              eLpNorm (latticeSmoothingError (criticalBeta ϑ M) M M
                (evenCeil (δ * M)) (evenCeil (δ * M)) h₀ (fun y => c * φ (Real.sqrt c • y)))
                2 disorderLaw ≤ ENNReal.ofReal
                  (Real.sqrt (C * heatEnergy (Real.sqrt δ) (fun y => c * φ (Real.sqrt c • y)) /
                      |Real.log δ|) +
                    C * (∫ x, |c * φ (Real.sqrt c • x)|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  obtain ⟨CLraw, δL, hδL, hLocal⟩ :=
    localLogError_L2_le_energy_dilate_of hVD A 2 (by norm_num)
  obtain ⟨CGraw, δG, hδG, hGlobal⟩ := globalLogError_L2_le_of hO hL A H
  let CL := |CLraw| + 1
  let CG := |CGraw| + 1
  let δ₁ := min δL (min δG (Real.exp (-1)))
  let C := CL + 2 * CG
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hCL : 0 < CL := by dsimp [CL]; positivity
  have hCG : 0 < CG := by dsimp [CG]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, δ₁, hδ₁, ?_⟩
  intro δ hδ hδlt φ hφ hφc hφint hφB c₀ c₁ hc₀ ε hε
  obtain ⟨B, hB⟩ := hφB
  have hδL' : δ ≤ δL := (le_of_lt hδlt).trans (min_le_left _ _)
  have hδG' : δ ≤ δG :=
    (le_of_lt hδlt).trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδexp : δ < Real.exp (-1) :=
    lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hLpos : 0 < |Real.log δ| := by
    apply abs_pos.mpr
    have hlog : Real.log δ < -1 := by
      calc
        Real.log δ < Real.log (Real.exp (-1)) := Real.log_lt_log hδ hδexp
        _ = -1 := Real.log_exp _
    linarith
  have hLone : 1 ≤ |Real.log δ| := by
    have hlog : Real.log δ < -1 := by
      calc
        Real.log δ < Real.log (Real.exp (-1)) := Real.log_lt_log hδ hδexp
        _ = -1 := Real.log_exp _
    rw [abs_of_neg (by linarith)]
    linarith
  have hpow : |Real.log δ| ^ (-(1 : ℝ) / 8) ≤
      |Real.log δ| ^ (-(1 : ℝ) / 40) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  let εG := ε / (4 * ((∫ x, |φ x|) + 1))
  have hεG : 0 < εG := by dsimp [εG]; positivity
  have hLocalEv := hLocal δ hδ hδL' φ hφ hφint ⟨B, hB⟩
    c₀ c₁ hc₀ (ε / 2) (by linarith)
  have hGlobalEv := hGlobal δ hδ hδG' εG hεG
  have hScaleEv : ∀ᶠ M : ℕ in atTop, 2 ≤ δ * (M : ℝ) := by
    have hev := (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / δ))
    filter_upwards [hev] with M hM
    have hM' := (div_le_iff₀ hδ).mp hM
    simpa [mul_comm] using hM'
  filter_upwards [hLocalEv, hGlobalEv, hScaleEv] with M hLocal hGlobal hScale
  intro hMeven c hc ϑ hϑ h₀ h₀bound
  have hcpos : 0 < c := lt_of_lt_of_le hc₀ hc.1
  have hc₁pos : 0 < c₁ := lt_of_lt_of_le hc₀ (le_trans hc.1 hc.2)
  let ψ : Plane → ℝ := fun x => c * φ (Real.sqrt c • x)
  have hψmeas : Measurable ψ := measurable_dilate φ hφ c
  have hψint : Integrable ψ := integrable_dilate φ hφint hcpos
  have hψc : HasCompactSupport ψ := hasCompactSupport_dilate φ hφc hcpos
  have hBψ : ∀ x, |ψ x| ≤ c₁ * B := by
    intro x
    change |c * φ (Real.sqrt c • x)| ≤ c₁ * B
    rw [abs_mul, abs_of_pos hcpos]
    exact mul_le_mul hc.2 (hB _) (abs_nonneg _) hc₁pos.le
  have hmass : (∫ x, |ψ x|) = ∫ x, |φ x| := integral_abs_dilate_eq φ hφint hcpos
  have hNcast : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hδM : 0 ≤ δ * (M : ℝ) := mul_nonneg hδ.le hNcast
  let m := evenCeil (δ * (M : ℝ))
  let n := evenCeil (Real.sqrt δ * (M : ℝ))
  have hmEven : Even m := evenCeil_even _
  have hnEven : Even n := evenCeil_even _
  have hδone : δ < 1 := lt_trans hδexp (by norm_num [Real.exp_lt_one_iff])
  have hroot : δ ≤ Real.sqrt δ := Real.le_sqrt_self_iff.mpr hδone.le
  have hmle : m ≤ n := evenCeil_mono
    (mul_le_mul_of_nonneg_right hroot hNcast)
  have hceilM : evenCeil (M : ℝ) = M := by
    obtain ⟨q, hq⟩ := hMeven
    rw [hq]
    simp [evenCeil, two_mul]
  have hnle : n ≤ M := by
    have hrootone : Real.sqrt δ < 1 := by
      simpa using Real.sqrt_lt_sqrt hδ.le hδone
    have hceil := evenCeil_mono (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hrootone.le hNcast)
    simpa [n, hceilM] using hceil
  have hmnReal : δ * (M : ℝ) ≤ (m : ℝ) := le_evenCeil _
  have hmUpper : (m : ℝ) ≤ 2 * δ * (M : ℝ) := by
    have hround := evenCeil_lt_add_two hδM
    dsimp [m]
    nlinarith [hround, hScale]
  have hLocalBound := hLocal c hc ϑ hϑ m hmEven hmnReal hmUpper
  have hH : 0 ≤ H := le_trans (norm_nonneg _) h₀bound
  have hcell (z : Site) :
      0 < evenExtension (cellAverage M (fun y => Real.exp (h₀ y))) z ∧
        |Real.log (evenExtension (cellAverage M (fun y => Real.exp (h₀ y))) z)| ≤ H := by
    by_cases hz : Even (z 0 + z 1)
    · have hMone : 1 ≤ M := by
        have hδMleM : δ * (M : ℝ) ≤ (M : ℝ) :=
          by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδone.le hNcast
        have hMreal : 1 ≤ (M : ℝ) := by nlinarith [hScale, hδMleM]
        exact_mod_cast hMreal
      have hc := cellAverage_exp_bounds_of_even M hMone h₀ hz
      constructor
      · simpa [evenExtension, hz] using hc.1
      · have hlog :
            |Real.log (evenExtension (cellAverage M fun y => Real.exp (h₀ y)) z)| ≤ ‖h₀‖ := by
          simpa [evenExtension, hz] using hc.2
        exact hlog.trans h₀bound
    · constructor
      · simp [evenExtension, hz]
      · simpa [evenExtension, hz] using hH
  have hGf : ∀ z, eLpNorm (globalLogError (criticalBeta ϑ M) m n M
      (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) z) 2 disorderLaw ≤
      ENNReal.ofReal (CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + εG) := by
    intro z
    exact (hGlobal ϑ hϑ _ hcell z).trans (ENNReal.ofReal_le_ofReal (by
      have hp : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLpos.le _
      have hcoeff := mul_le_mul_of_nonneg_right (le_abs_self CGraw) hp
      dsimp [CG]
      linarith))
  have hG1 : ∀ z, eLpNorm (globalLogError (criticalBeta ϑ M) m n M
      (fun _ => 1) z) 2 disorderLaw ≤
      ENNReal.ofReal (CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + εG) := by
    intro z
    exact (hGlobal ϑ hϑ (fun _ : Site => 1) (by
      intro y
      exact ⟨by norm_num, by simpa [Real.log_one] using hH⟩) z).trans
        (ENNReal.ofReal_le_ofReal (by
          have hp : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLpos.le _
          have hcoeff := mul_le_mul_of_nonneg_right (le_abs_self CGraw) hp
          dsimp [CG]
          linarith))
  let R := CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + εG
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let globalTerm : Disorder → ℝ := fun ω => ∫ x, ψ x *
    (globalLogError (criticalBeta ϑ M) m n M
      (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) (latticePoint M x) ω -
      ∫ ω', globalLogError (criticalBeta ϑ M) m n M (fun _ => 1)
        (latticePoint M x) ω' ∂disorderLaw)
  have hGlobalSpatial := eLpNorm_integral_centeredGlobal_le (criticalBeta ϑ M) m n M
    (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) ψ hψmeas hψint R hR hGf hG1
  have henergy : 0 ≤ heatEnergy (Real.sqrt δ) ψ :=
    (heatEnergy_le_of_bounded ψ hψmeas hψint (c₁ * B) hBψ (Real.sqrt_pos.2 hδ)).1
  have hlocal : eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n ψ ω)
      2 disorderLaw ≤ ENNReal.ofReal
        (Real.sqrt (CL * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
          CL * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) := by
    apply hLocalBound.trans
    apply ENNReal.ofReal_le_ofReal
    have hpow0 : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLpos.le _
    have hcoeff : CLraw ≤ CL := by dsimp [CL]; linarith [le_abs_self CLraw]
    have hroot : Real.sqrt (CLraw * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) ≤
        Real.sqrt (CL * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) := by
      apply Real.sqrt_le_sqrt
      have hden : 0 < |Real.log δ| := hLpos
      apply (div_le_div_iff_of_pos_right hden).2
      exact mul_le_mul_of_nonneg_right hcoeff henergy
    have hfirst : CLraw * heatEnergy (Real.sqrt δ) ψ / |Real.log δ| ≤
        CL * heatEnergy (Real.sqrt δ) ψ / |Real.log δ| := by
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff henergy) hLpos.le)
    have hlocalraw := hLocalBound
    have hpow8 : |Real.log δ| ^ (-(1 : ℝ) / 8) ≤
        |Real.log δ| ^ (-(1 : ℝ) / 40) :=
      Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
    have hL1 : 0 ≤ ∫ x, |ψ x| := integral_nonneg fun x => abs_nonneg _
    have htail : CLraw * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 8) ≤
        CL * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
      calc
        _ ≤ |CLraw| * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 8) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self CLraw) hL1) (by positivity)
        _ ≤ |CLraw| * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
          gcongr
        _ ≤ CL * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
          have habs : |CLraw| ≤ CL := by dsimp [CL]; linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right habs hL1) hpow0
    have hrawcmp :
        Real.sqrt (CLraw * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
          CLraw * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 8) + ε / 2 ≤
        Real.sqrt (CL * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
          CL * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 := by
      exact add_le_add (add_le_add hroot htail) le_rfl
    exact hrawcmp
  have hglobalBound : eLpNorm globalTerm 2 disorderLaw ≤
      ENNReal.ofReal (2 * R * ∫ x, |ψ x|) := hGlobalSpatial.2
  have hsum := eLpNorm_add_le (μ := disorderLaw) (p := (2 : ENNReal))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (f := fun ω => localLogError (criticalBeta ϑ M) M m n ψ ω)
    (g := globalTerm)
  have hdecomp (ω : Disorder) := latticeSmoothingError_eq_local_add_global
    (criticalBeta ϑ M) hmEven hnEven hMeven hmle hnle h₀ ψ hψmeas hψc ⟨c₁ * B, hBψ⟩ ω
  have hresult := calc
    eLpNorm (latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ ψ) 2 disorderLaw =
        eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n ψ ω + globalTerm ω)
          2 disorderLaw := by
            apply eLpNorm_congr_ae
            exact Filter.Eventually.of_forall fun ω => by
              simpa [globalTerm] using hdecomp ω
    _ ≤ eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n ψ ω) 2 disorderLaw +
        eLpNorm globalTerm 2 disorderLaw := hsum
  have hsumBound :
      eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n ψ ω) 2 disorderLaw +
        eLpNorm globalTerm 2 disorderLaw ≤ ENNReal.ofReal
          (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
            C * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
    calc
      _ ≤ ENNReal.ofReal
          (Real.sqrt (CL * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
            CL * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) +
          ENNReal.ofReal (2 * R * ∫ x, |ψ x|) := add_le_add hlocal hglobalBound
      _ = ENNReal.ofReal
          (Real.sqrt (CL * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
            CL * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 +
            2 * R * ∫ x, |ψ x|) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal
          (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
            C * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
              apply ENNReal.ofReal_le_ofReal
              have hL1 : 0 ≤ ∫ x, |ψ x| := integral_nonneg fun x => abs_nonneg _
              have hεsmall : 2 * εG * (∫ x, |ψ x|) ≤ ε / 2 := by
                rw [hmass]
                dsimp [εG]
                have hden : 0 < 4 * ((∫ x, |φ x|) + 1) := by positivity
                have hcoef : 2 * (∫ x, |φ x|) ≤
                    2 * ((∫ x, |φ x|) + 1) := by nlinarith
                calc
                  _ = (2 * (∫ x, |φ x|)) *
                      (ε / (4 * ((∫ x, |φ x|) + 1))) := by ring
                  _ ≤ 2 * ((∫ x, |φ x|) + 1) *
                      (ε / (4 * ((∫ x, |φ x|) + 1))) :=
                    mul_le_mul_of_nonneg_right hcoef (by positivity)
                  _ = ε / 2 := by field_simp [ne_of_gt hden]; ring
              have hroot : Real.sqrt (CL * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) ≤
                  Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) := by
                apply Real.sqrt_le_sqrt
                apply (div_le_div_iff_of_pos_right hLpos).2
                apply mul_le_mul_of_nonneg_right _ henergy
                dsimp [C]
                linarith
              have hcoeff : CL * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) ≤
                  C * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
                gcongr
                dsimp [C]
                linarith
              dsimp [R]
              linarith
  simpa [m, ψ, abs_mul, abs_of_pos hcpos] using hresult.trans hsumBound
end Critical2DKPZ.Smoothing

end
