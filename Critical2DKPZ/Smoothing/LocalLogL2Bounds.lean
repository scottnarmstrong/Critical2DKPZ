/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.LocalErrorBounds
public import Critical2DKPZ.Smoothing.GreenCoarseBound
public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # L² bounds for the local logarithmic error -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Critical2DKPZ.Smoothing

private theorem sqrt_le_log_rpow_neg_quarter (δ : ℝ) (hδ : 0 < δ)
    (hδexp : δ ≤ Real.exp (-8)) :
    8 ≤ |Real.log δ| ∧ Real.sqrt δ ≤ |Real.log δ| ^ (-(1 : ℝ) / 4) := by
  have hlogδ : Real.log δ ≤ -8 := by
    calc
      Real.log δ ≤ Real.log (Real.exp (-8)) := Real.log_le_log hδ hδexp
      _ = -8 := Real.log_exp _
  have hlogδneg : Real.log δ < 0 := lt_of_le_of_lt hlogδ (by norm_num)
  have hL : 8 ≤ |Real.log δ| := by
    rw [abs_of_neg hlogδneg]
    linarith
  have hLpos : 0 < |Real.log δ| := lt_of_lt_of_le (by norm_num) hL
  have hlogL : Real.log |Real.log δ| ≤ 2 * |Real.log δ| := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  have habslog : |Real.log δ| = -Real.log δ := abs_of_neg hlogδneg
  rw [habslog] at hlogL
  have hcompare : Real.log δ / 2 ≤ -Real.log |Real.log δ| / 4 := by
    rw [habslog]
    nlinarith [hlogL]
  have hsqrtExp : Real.sqrt δ = Real.exp (Real.log δ / 2) := by
    calc
      Real.sqrt δ = δ ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow δ
      _ = Real.exp (Real.log δ * ((1 : ℝ) / 2)) := Real.rpow_def_of_pos hδ _
      _ = Real.exp (Real.log δ / 2) := by congr 1; ring
  have hpow : |Real.log δ| ^ (-(1 : ℝ) / 4) =
      Real.exp (Real.log |Real.log δ| * (-(1 : ℝ) / 4)) :=
    Real.rpow_def_of_pos hLpos _
  refine ⟨hL, ?_⟩
  calc
    Real.sqrt δ = Real.exp (Real.log δ / 2) := hsqrtExp
    _ ≤ Real.exp (-Real.log |Real.log δ| / 4) := Real.exp_le_exp.mpr hcompare
    _ = |Real.log δ| ^ (-(1 : ℝ) / 4) := by rw [hpow]; congr 1; ring

private theorem integral_abs_plane_mul_integral_abs (φ : Plane → ℝ)
    :
    (∫ p : Plane × Plane, |φ p.1| * |φ p.2|) = (∫ x : Plane, |φ x|) ^ 2 := by
  rw [Measure.volume_eq_prod Plane Plane]
  simpa only [pow_two] using
    (integral_prod_mul (fun x : Plane => |φ x|) (fun x : Plane => |φ x|))

/-- The local logarithmic error satisfies a test-dependent `L²` heat-energy bound. The sampled Green kernel is integrable by `integrable_truncatedGreen_latticePoint`. -/
theorem localLogError_L2_le_energy_of (hVD : PropVDBound) (A κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ φ : Plane → ℝ, Measurable φ → Integrable φ →
        (∃ M : ℝ, ∀ x, |φ x| ≤ M) → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
            ∀ m : ℕ, Even m → δ * N ≤ m → (m : ℝ) ≤ κ * δ * N →
              eLpNorm (localLogError (criticalBeta ϑ N) N m
                (evenCeil (Real.sqrt δ * N)) φ) 2 disorderLaw ≤
                ENNReal.ofReal (Real.sqrt
                    (C * heatEnergy (Real.sqrt δ) φ / |Real.log δ|) +
                  C * (∫ x, |φ x|) * |Real.log δ| ^ (-(1 : ℝ) / 8) + ε) := by
  obtain ⟨δVD, CVD, hδVDpos, hδVDlt, hVDsmall⟩ :=
    gaussianityDefect_small_time_of hVD A
  obtain ⟨Csecond, hsecond⟩ := OnePoint.sigmaSq_secondMoment_le_uniform A 1
  let C₂ : ℝ := |Csecond| + 1
  let Cdef : ℝ := |CVD| + 1
  let C : ℝ := max (16 * C₂) (max (2 * Real.sqrt (2 * Cdef)) 1)
  let δ₀ : ℝ := min δVD (min (1 / 16) (min (Real.exp (-8)) (κ⁻¹ ^ 2)))
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  have hCdef : 0 < Cdef := by dsimp [Cdef]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCfirst : 16 * C₂ ≤ C := le_max_left _ _
  have hCsecond : 2 * Real.sqrt (2 * Cdef) ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCsquare : 8 * Cdef ≤ C ^ 2 := by
    have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 2 * Cdef)
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt (2 * Cdef)) hCpos.le).2 hCsecond
    nlinarith [h, hsquare]
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    positivity
  have hδ₀core : δ₀ ≤ min (1 / 16) (min (Real.exp (-8)) (κ⁻¹ ^ 2)) :=
    min_le_right δVD _
  have hδ₀lt : δ₀ < 1 := by
    apply lt_of_le_of_lt (le_trans hδ₀core (min_le_left _ _))
    norm_num
  refine ⟨C, δ₀, hδ₀pos, ?_⟩
  intro δ hδ hδle φ hφ hφint hφbound ε hε
  obtain ⟨Mφ, hφM⟩ := hφbound
  have hδVD : δ ≤ δVD := le_trans hδle (min_le_left _ _)
  have hδ16 : δ ≤ 1 / 16 :=
    le_trans hδle (le_trans hδ₀core (min_le_left _ _))
  have hδexp : δ ≤ Real.exp (-8) :=
    le_trans hδle (le_trans hδ₀core
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδκ : δ ≤ κ⁻¹ ^ 2 :=
    le_trans hδle (le_trans hδ₀core
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hLdata := sqrt_le_log_rpow_neg_quarter δ hδ hδexp
  let L : ℝ := |Real.log δ|
  let Q : ℝ := L ^ (-(1 : ℝ) / 4)
  have hLge : 8 ≤ L := by simpa [L] using hLdata.1
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLge
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hroot : Real.sqrt δ ≤ Q := by simpa [L, Q] using hLdata.2
  have hrootQ : Q ^ 2 = L ^ (-(1 : ℝ) / 2) := by
    dsimp [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hQpow : (L ^ (-(1 : ℝ) / 8)) ^ 2 = Q := by
    dsimp [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hLpowPos : 0 < L ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hLpos _
  have hQinv : (L ^ ((1 : ℝ) / 4))⁻¹ = Q := by
    dsimp [Q]
    calc
      (L ^ ((1 : ℝ) / 4))⁻¹ = L ^ (-(1 / 4 : ℝ)) :=
        (Real.rpow_neg hLpos.le ((1 : ℝ) / 4)).symm
      _ = L ^ (-1 / 4 : ℝ) := by congr 1; norm_num
  have hD : 0 < L / 4 := by positivity
  have hsmall := hVDsmall δ hδ hδVD
  obtain ⟨o, ho, hdefect⟩ := hsmall
  have hsmallO : ∀ᶠ N : ℕ in atTop, o N ≤ Q := by
    have h := ho.eventually (eventually_lt_nhds hQpos)
    filter_upwards [h] with N hN
    exact le_of_lt hN
  let εg : ℝ := ε ^ 2 / (64 * (C₂ + 1))
  have hgreenεpos : 0 < εg := by dsimp [εg]; positivity
  have hGreenEventually := integral_truncatedGreen_latticePoint_le δ hδ φ hφ hφint
    ⟨Mφ, hφM⟩ εg hgreenεpos
  have hNscale : ∀ᶠ N : ℕ in atTop, 2 / Real.sqrt δ ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 / Real.sqrt δ)
  have hlogEventually := eventually_small_time_log_bounds δ hδ hδ16 hδexp
  filter_upwards [hsmallO, hdefect, hsecond, hlogEventually, hGreenEventually,
    hNscale] with N hsmallON hdefectN hsecondN hlogN hGreenN hNscale
  intro ϑ hϑ m hm hδm hmUpper
  let n : ℕ := evenCeil (Real.sqrt δ * N)
  have hnleN : (n : ℝ) ≤ N := by simpa [n] using hlogN.1
  have hNpos : 0 < (N : ℝ) := by
    have hpos : 0 < 2 / Real.sqrt δ := by positivity
    exact lt_of_lt_of_le hpos hNscale
  have hqN : 2 ≤ Real.sqrt δ * N := by
    have h := (div_le_iff₀ (Real.sqrt_pos.2 hδ)).1 hNscale
    nlinarith
  have hnle : m ≤ n := by
    have hsqrtκ : Real.sqrt δ ≤ κ⁻¹ := by
      calc
        Real.sqrt δ ≤ Real.sqrt (κ⁻¹ ^ 2) := Real.sqrt_le_sqrt hδκ
        _ = κ⁻¹ := by rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hκpos)]
    have htime : κ * δ ≤ Real.sqrt δ := by
      calc
        κ * δ = (κ * Real.sqrt δ) * Real.sqrt δ := by
          calc
            κ * δ = κ * (Real.sqrt δ) ^ 2 := by rw [Real.sq_sqrt hδ.le]
            _ = (κ * Real.sqrt δ) * Real.sqrt δ := by ring
        _ ≤ 1 * Real.sqrt δ := by
          exact mul_le_mul_of_nonneg_right
            (by
              rw [mul_comm]
              have hsqrtκ' : Real.sqrt δ ≤ 1 / κ := by simpa [one_div] using hsqrtκ
              exact (le_div_iff₀ hκpos).1 hsqrtκ') (Real.sqrt_nonneg _)
        _ = Real.sqrt δ := by ring
    have hmReal : (m : ℝ) ≤ (n : ℝ) := by
      calc
        (m : ℝ) ≤ κ * δ * N := hmUpper
        _ ≤ Real.sqrt δ * N := by
          exact mul_le_mul_of_nonneg_right htime (Nat.cast_nonneg N)
        _ ≤ n := by
          dsimp [n]
          exact_mod_cast le_evenCeil (Real.sqrt δ * N)
    exact_mod_cast hmReal
  have hβ : 0 ≤ criticalBeta ϑ N := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hdef0 : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) 0 n x ω)) ≤ Cdef * Q := by
    intro x
    have h := (hdefectN ϑ hϑ x 0 (⟨0, rfl⟩) (Nat.zero_le _)).2
    have hcoef : CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| * Q := by
      calc
        CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| / L ^ ((1 : ℝ) / 4) :=
          div_le_div_of_nonneg_right (le_abs_self CVD) hLpowPos.le
        _ = |CVD| * Q := by rw [div_eq_mul_inv, hQinv]
    calc
      _ ≤ CVD / L ^ ((1 : ℝ) / 4) + o N := h
      _ ≤ |CVD| * Q + Q := add_le_add hcoef hsmallON
      _ = Cdef * Q := by dsimp [Cdef]; ring
  have hdefm : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) m n x ω)) ≤ Cdef * Q := by
    intro x
    have h := (hdefectN ϑ hϑ x m hm (by simpa [n] using hnle)).2
    have hcoef : CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| * Q := by
      calc
        CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| / L ^ ((1 : ℝ) / 4) :=
          div_le_div_of_nonneg_right (le_abs_self CVD) hLpowPos.le
        _ = |CVD| * Q := by rw [div_eq_mul_inv, hQinv]
    calc
      _ ≤ CVD / L ^ ((1 : ℝ) / 4) + o N := h
      _ ≤ |CVD| * Q + Q := add_le_add hcoef hsmallON
      _ = Cdef * Q := by dsimp [Cdef]; ring
  have hlogK (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      L / 4 ≤ Real.log (1 + (N : ℝ) / k) := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using hlogN.2.1 k hk hkn
  have hlogZero : L / 4 ≤ Real.log (1 + (N : ℝ)) := hlogN.2.2
  have hsecondK (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
          C₂ / Real.log (1 + (N : ℝ) / k) := by
    have hkN : (k : ℝ) ≤ (1 : ℝ) * (N : ℝ) := by
      have hkR : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hkn
      simpa only [one_mul] using le_trans hkR hnleN
    have hbase := hsecondN ϑ hϑ k hk hkN
    have hden : 0 < Real.log (1 + (N : ℝ) / k) :=
      lt_of_lt_of_le (by positivity : 0 < L / 4) (hlogK k hk hkn)
    calc
      _ ≤ Csecond / Real.log (1 + (N : ℝ) / k) := hbase
      _ ≤ C₂ / Real.log (1 + (N : ℝ) / k) :=
        div_le_div_of_nonneg_right (by dsimp [C₂]; linarith [le_abs_self Csecond]) hden.le
  have hcoeff := sigmaSq_collision_secondMoment_le (criticalBeta ϑ N) N n L C₂ hLpos
    hC₂.le hsecondK hlogK hlogZero
  have hcoeff' : ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C₂ / (L / 4) := by
    intro r hr
    calc
      _ ≤ 4 * C₂ / L := hcoeff r hr
      _ = C₂ / (L / 4) := by field_simp
  have hGreenIntegrable := integrable_truncatedGreen_latticePoint δ (N := N) φ hφ hφint
  have hφnorm : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hφint.norm
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  let G : Plane × Plane → ℝ := fun p =>
    MomentBounds.truncatedGreen n (latticePoint N p.2 - latticePoint N p.1)
  let K : Plane × Plane → ℝ := fun p => F p *
    (C₂ / (L / 4) * G p + Cdef * Q + Cdef * Q)
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hφnorm.mul_prod hφnorm
  have hGreenInt : Integrable (fun p : Plane × Plane => F p * G p)
      (volume.prod volume) := by simpa [F, G, n] using hGreenIntegrable
  have hKint : Integrable K (volume.prod volume) := by
    have htermGreen : Integrable (fun p : Plane × Plane =>
        F p * (C₂ / (L / 4) * G p)) (volume.prod volume) := by
      have h := hGreenInt.const_mul (C₂ / (L / 4))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    have htermDefect : Integrable (fun p : Plane × Plane =>
        F p * (Cdef * Q + Cdef * Q)) (volume.prod volume) :=
      hFint.mul_const _
    have hsum := htermGreen.add htermDefect
    have heq : (fun p : Plane × Plane =>
        F p * (C₂ / (L / 4) * G p + Cdef * Q + Cdef * Q)) =
        fun p => F p * (C₂ / (L / 4) * G p) + F p * (Cdef * Q + Cdef * Q) := by
      funext p
      ring
    simpa only [K] using heq ▸ hsum
  have hFintEq : (∫ p : Plane × Plane, F p ∂volume.prod volume) =
      (∫ x : Plane, |φ x|) ^ 2 := by
    rw [← Measure.volume_eq_prod Plane Plane]
    simpa [F] using integral_abs_plane_mul_integral_abs φ
  have hL1nonneg : 0 ≤ ∫ x : Plane, |φ x| := integral_nonneg fun x => abs_nonneg _
  have hGreenNonneg : 0 ≤ ∫ p : Plane × Plane, F p * G p ∂volume.prod volume :=
    integral_nonneg fun p => by
      dsimp [F, G]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (MomentBounds.truncatedGreen_nonneg n _)
  have hcoeffNonneg : 0 ≤ C₂ / (L / 4) := div_nonneg hC₂.le hD.le
  have htermGreenEq : (∫ p : Plane × Plane, F p *
      (C₂ / (L / 4) * G p) ∂volume.prod volume) =
      C₂ / (L / 4) * (∫ p : Plane × Plane, F p * G p ∂volume.prod volume) := by
    calc
      _ = ∫ p : Plane × Plane, C₂ / (L / 4) * (F p * G p) ∂volume.prod volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by ring
      _ = _ := integral_const_mul _ _
  have htermDefectEq : (∫ p : Plane × Plane, F p *
      (Cdef * Q + Cdef * Q) ∂volume.prod volume) =
      (Cdef * Q + Cdef * Q) * (∫ p : Plane × Plane, F p ∂volume.prod volume) := by
    calc
      _ = (∫ p : Plane × Plane, F p ∂volume.prod volume) * (Cdef * Q + Cdef * Q) :=
        integral_mul_const _ _
      _ = _ := by ring
  have hKsplit : (∫ p : Plane × Plane, K p ∂volume.prod volume) =
      C₂ / (L / 4) * (∫ p : Plane × Plane, F p * G p ∂volume.prod volume) +
        (Cdef * Q + Cdef * Q) * (∫ p : Plane × Plane, F p ∂volume.prod volume) := by
    change (∫ p : Plane × Plane, F p *
      (C₂ / (L / 4) * G p + Cdef * Q + Cdef * Q) ∂volume.prod volume) = _
    rw [show (fun p : Plane × Plane => F p *
      (C₂ / (L / 4) * G p + Cdef * Q + Cdef * Q)) =
      fun p => F p * (C₂ / (L / 4) * G p) + F p * (Cdef * Q + Cdef * Q) by
        funext p
        ring, integral_add (by
          simpa only [mul_assoc, mul_comm, mul_left_comm] using
            hGreenInt.const_mul (C₂ / (L / 4))) (hFint.mul_const _),
      htermGreenEq, htermDefectEq]
  have hGreenN' :
      ∫ p : Plane × Plane, F p * G p ∂volume.prod volume ≤
        heatEnergy (Real.sqrt δ) φ + εg := by
    rw [← Measure.volume_eq_prod Plane Plane]
    simpa [F, G, n] using hGreenN
  have hKbound : ∫ p : Plane × Plane, K p ∂volume.prod volume ≤
      C₂ / (L / 4) * (heatEnergy (Real.sqrt δ) φ + εg) +
        (Cdef * Q + Cdef * Q) * (∫ x : Plane, |φ x|) ^ 2 := by
    rw [hKsplit, hFintEq]
    exact add_le_add (mul_le_mul_of_nonneg_left hGreenN' hcoeffNonneg) le_rfl
  have hKradNonneg : 0 ≤ ∫ p : Plane × Plane, K p ∂volume.prod volume := by
    exact integral_nonneg fun p => by
      dsimp [K]
      apply mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hgreen : 0 ≤ G p := MomentBounds.truncatedGreen_nonneg n _
      positivity
  have hLone : 1 ≤ L := by linarith [hLge]
  have hCoeffEq : C₂ / (L / 4) = 4 * C₂ / L := by field_simp
  let X : ℝ := 4 * C₂ * heatEnergy (Real.sqrt δ) φ / L
  let Y : ℝ := 2 * Cdef * Q * (∫ x : Plane, |φ x|) ^ 2
  let Z : ℝ := C₂ / (L / 4) * εg
  have hheatpos : 0 ≤ heatEnergy (Real.sqrt δ) φ :=
    (heatEnergy_le_of_bounded φ hφ hφint Mφ hφM (Real.sqrt_pos.2 hδ)).1
  have hXnonneg : 0 ≤ X := by dsimp [X]; positivity
  have hYnonneg : 0 ≤ Y := by dsimp [Y]; positivity
  have hZnonneg : 0 ≤ Z := by dsimp [Z]; positivity
  have hRadBound : (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤ X + Y + Z := by
    rw [hCoeffEq] at hKbound
    dsimp [X, Y, Z]
    calc
      _ ≤ (4 * C₂ / L) * (heatEnergy (Real.sqrt δ) φ + εg) +
          (Cdef * Q + Cdef * Q) * (∫ x : Plane, |φ x|) ^ 2 := hKbound
      _ = _ := by ring
  have hrootSum : Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤
      Real.sqrt X + Real.sqrt Y + Real.sqrt Z := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      ∫ p : Plane × Plane, K p ∂volume.prod volume ≤ X + Y + Z := hRadBound
      _ ≤ (Real.sqrt X + Real.sqrt Y + Real.sqrt Z) ^ 2 := by
        have hsX := Real.sq_sqrt hXnonneg
        have hsY := Real.sq_sqrt hYnonneg
        have hsZ := Real.sq_sqrt hZnonneg
        nlinarith only [hsX, hsY, hsZ,
          mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Y),
          mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Z),
          mul_nonneg (Real.sqrt_nonneg Y) (Real.sqrt_nonneg Z)]
  have hrootX : 2 * Real.sqrt X ≤ Real.sqrt
      (C * heatEnergy (Real.sqrt δ) φ / L) := by
    have htarget : 0 ≤ C * heatEnergy (Real.sqrt δ) φ / L := by positivity
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    have hleft : (2 * Real.sqrt X) ^ 2 = 16 * C₂ *
        (heatEnergy (Real.sqrt δ) φ / L) := by
      calc
        _ = 4 * X := by rw [mul_pow, Real.sq_sqrt hXnonneg]; norm_num
        _ = _ := by dsimp [X]; ring
    have hright : (Real.sqrt (C * heatEnergy (Real.sqrt δ) φ / L)) ^ 2 =
        C * (heatEnergy (Real.sqrt δ) φ / L) := by
      rw [Real.sq_sqrt htarget]
      ring
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_right hCfirst (div_nonneg hheatpos hLpos.le)
  have hrootY : 2 * Real.sqrt Y ≤
      C * (∫ x : Plane, |φ x|) * L ^ (-(1 : ℝ) / 8) := by
    have htarget : 0 ≤ C * (∫ x : Plane, |φ x|) * L ^ (-(1 : ℝ) / 8) := by positivity
    apply (sq_le_sq₀ (by positivity) htarget).mp
    have hfactor : 0 ≤ Q * (∫ x : Plane, |φ x|) ^ 2 :=
      mul_nonneg hQpos.le (sq_nonneg _)
    have hcoef := mul_le_mul_of_nonneg_right hCsquare hfactor
    have hleft : (2 * Real.sqrt Y) ^ 2 =
        (8 * Cdef) * (Q * (∫ x : Plane, |φ x|) ^ 2) := by
      calc
        _ = 4 * Y := by rw [mul_pow, Real.sq_sqrt hYnonneg]; norm_num
        _ = _ := by dsimp [Y]; ring
    have hright : (C * (∫ x : Plane, |φ x|) * L ^ (-(1 : ℝ) / 8)) ^ 2 =
        C ^ 2 * (Q * (∫ x : Plane, |φ x|) ^ 2) := by
      calc
        _ = C ^ 2 * (∫ x : Plane, |φ x|) ^ 2 *
            (L ^ (-(1 : ℝ) / 8)) ^ 2 := by ring
        _ = _ := by rw [hQpow]; ring
    rw [hleft, hright]
    exact hcoef
  have hZsmall : Z ≤ ε ^ 2 / 16 := by
    have hratio : C₂ / (L * (C₂ + 1)) ≤ 1 := by
      apply (div_le_one (mul_pos hLpos (by positivity))).2
      exact le_trans (by linarith [hC₂])
        (mul_le_mul_of_nonneg_right hLone (by positivity))
    calc
      Z = (ε ^ 2 / 16) * (C₂ / (L * (C₂ + 1))) := by
        dsimp [Z, εg]
        rw [hCoeffEq]
        field_simp [ne_of_gt hLpos, ne_of_gt (by positivity : 0 < C₂ + 1)]
        ring
      _ ≤ ε ^ 2 / 16 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
          (div_nonneg (sq_nonneg ε) (by norm_num : (0 : ℝ) ≤ 16))
  have hrootZ : 2 * Real.sqrt Z ≤ ε := by
    apply (sq_le_sq₀ (by positivity) hε.le).mp
    calc
      (2 * Real.sqrt Z) ^ 2 = 4 * Z := by
        rw [mul_pow, Real.sq_sqrt hZnonneg]
        norm_num
      _ ≤ 4 * (ε ^ 2 / 16) := mul_le_mul_of_nonneg_left hZsmall (by norm_num)
      _ = ε ^ 2 / 4 := by ring
      _ ≤ ε ^ 2 := div_le_self (sq_nonneg ε) (by norm_num)
  have hrootReal : 2 * Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤
      Real.sqrt (C * heatEnergy (Real.sqrt δ) φ / L) +
        C * (∫ x : Plane, |φ x|) * L ^ (-(1 : ℝ) / 8) + ε := by
    calc
      _ ≤ 2 * (Real.sqrt X + Real.sqrt Y + Real.sqrt Z) :=
        mul_le_mul_of_nonneg_left hrootSum (by norm_num)
      _ = 2 * Real.sqrt X + 2 * Real.sqrt Y + 2 * Real.sqrt Z := by ring
      _ ≤ Real.sqrt (C * heatEnergy (Real.sqrt δ) φ / L) +
          C * (∫ x : Plane, |φ x|) * L ^ (-(1 : ℝ) / 8) + ε := by
        linarith [hrootX, hrootY, hrootZ]
  have hnorm := localLogError_eLpNorm_le_covariance_integral
    (criticalBeta ϑ N) hβ N m n (by exact hnle) φ hφ hφint C₂ (L / 4) (Cdef * Q)
    hC₂.le hD (mul_nonneg hCdef.le hQpos.le) hcoeff' hdef0 hdefm hKint
  have hNormReal :
      2 * Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤
        Real.sqrt (C * heatEnergy (Real.sqrt δ) φ / L) +
          C * (∫ x : Plane, |φ x|) * L ^ (-(1 : ℝ) / 8) + ε := hrootReal
  calc
    _ ≤ 2 * ENNReal.ofReal
        (Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume)) := hnorm
    _ = ENNReal.ofReal
        (2 * Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume)) := by
      have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      simpa only [h2] using
        (ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))).symm
    _ ≤ ENNReal.ofReal
        (Real.sqrt (C * heatEnergy (Real.sqrt δ) φ / L) +
          C * (∫ x : Plane, |φ x|) * L ^ (-(1 : ℝ) / 8) + ε) :=
      ENNReal.ofReal_le_ofReal hNormReal

/-- Covariance control with a direct uniform bound on the sampled Green integral. -/
private theorem localLogError_L2_le_green_bound
    (β : ℝ) (hβ : 0 ≤ β) (N m n : ℕ) (hmn : m ≤ n)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hφint : Integrable φ)
    (C₂ D E M₁ Bgreen : ℝ) (hC₂ : 0 ≤ C₂) (hD : 0 < D) (hE : 0 ≤ E)
    (hcoeff : ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C₂ / D)
    (hdef0 : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β 0 n x ω)) ≤ E)
    (hdefm : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β m n x ω)) ≤ E)
    (hL1 : (∫ x : Plane, |φ x|) ≤ M₁) (hM₁ : 0 ≤ M₁)
    (hGreenInt : Integrable (fun p : Plane × Plane =>
      |φ p.1| * |φ p.2| * MomentBounds.truncatedGreen n
        (latticePoint N p.2 - latticePoint N p.1)) (volume.prod volume))
    (hGreenBound : (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
      MomentBounds.truncatedGreen n (latticePoint N p.2 - latticePoint N p.1)
      ∂volume.prod volume) ≤ Bgreen) :
    eLpNorm (localLogError β N m n φ) 2 disorderLaw ≤
      ENNReal.ofReal (2 * Real.sqrt ((C₂ / D) * Bgreen + 2 * E * M₁ ^ 2)) := by
  have hφnorm : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hφint.norm
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  let G : Plane × Plane → ℝ := fun p =>
    MomentBounds.truncatedGreen n (latticePoint N p.2 - latticePoint N p.1)
  let K : Plane × Plane → ℝ := fun p => F p * ((C₂ / D) * G p + E + E)
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hφnorm.mul_prod hφnorm
  have hFGint : Integrable (fun p : Plane × Plane => F p * G p)
      (volume.prod volume) := by simpa only [F, G] using hGreenInt
  have htermG : Integrable (fun p : Plane × Plane =>
      F p * ((C₂ / D) * G p)) (volume.prod volume) := by
    have h := hFGint.const_mul (C₂ / D)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have htermE : Integrable (fun p : Plane × Plane => F p * (E + E))
      (volume.prod volume) := hFint.mul_const _
  have hKint : Integrable K (volume.prod volume) := by
    have hsum := htermG.add htermE
    have heq : (fun p : Plane × Plane => F p *
        ((C₂ / D) * G p + E + E)) =
      fun p => F p * ((C₂ / D) * G p) + F p * (E + E) := by
      funext p
      ring
    simpa only [K] using heq ▸ hsum
  have hFintEq : (∫ p : Plane × Plane, F p ∂volume.prod volume) =
      (∫ x : Plane, |φ x|) ^ 2 := by
    rw [← Measure.volume_eq_prod Plane Plane]
    simpa [F] using integral_abs_plane_mul_integral_abs φ
  have htermGEq : (∫ p : Plane × Plane, F p * ((C₂ / D) * G p)
      ∂volume.prod volume) =
      (C₂ / D) * (∫ p : Plane × Plane, F p * G p ∂volume.prod volume) := by
    calc
      _ = ∫ p : Plane × Plane, (C₂ / D) * (F p * G p) ∂volume.prod volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by ring
      _ = _ := integral_const_mul _ _
  have htermEEq : (∫ p : Plane × Plane, F p * (E + E) ∂volume.prod volume) =
      (E + E) * (∫ p : Plane × Plane, F p ∂volume.prod volume) := by
    calc
      _ = (∫ p : Plane × Plane, F p ∂volume.prod volume) * (E + E) :=
        integral_mul_const _ _
      _ = _ := by ring
  have hKsplit : (∫ p : Plane × Plane, K p ∂volume.prod volume) =
      (C₂ / D) * (∫ p : Plane × Plane, F p * G p ∂volume.prod volume) +
        (E + E) * (∫ p : Plane × Plane, F p ∂volume.prod volume) := by
    calc
      _ = ∫ p : Plane × Plane,
          F p * ((C₂ / D) * G p) + F p * (E + E) ∂volume.prod volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun p => by
              dsimp [K]
              ring
      _ = (∫ p : Plane × Plane, F p * ((C₂ / D) * G p) ∂volume.prod volume) +
          (∫ p : Plane × Plane, F p * (E + E) ∂volume.prod volume) :=
            integral_add htermG htermE
      _ = _ := by rw [htermGEq, htermEEq]
  have hL1nonneg : 0 ≤ ∫ x : Plane, |φ x| :=
    integral_nonneg fun x => abs_nonneg (φ x)
  have hcoefNonneg : 0 ≤ C₂ / D := div_nonneg hC₂ hD.le
  have hgreenNonneg : 0 ≤ ∫ p : Plane × Plane, F p * G p ∂volume.prod volume :=
    integral_nonneg fun p => by
      dsimp [F, G]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (MomentBounds.truncatedGreen_nonneg n _)
  have hKbound : (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤
      (C₂ / D) * Bgreen + 2 * E * M₁ ^ 2 := by
    rw [hKsplit, hFintEq]
    have hL1sq : (∫ x : Plane, |φ x|) ^ 2 ≤ M₁ ^ 2 := by
      nlinarith [hL1, hL1nonneg, hM₁]
    calc
      _ ≤ (C₂ / D) * Bgreen + (E + E) * (∫ x : Plane, |φ x|) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hGreenBound hcoefNonneg) le_rfl
      _ ≤ (C₂ / D) * Bgreen + (E + E) * M₁ ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hL1sq (by positivity))
      _ = (C₂ / D) * Bgreen + 2 * E * M₁ ^ 2 := by ring
  have hKupperNonneg : 0 ≤ (C₂ / D) * Bgreen + 2 * E * M₁ ^ 2 := by
    have hBgreen : 0 ≤ Bgreen := le_trans hgreenNonneg hGreenBound
    positivity
  have hnorm := localLogError_eLpNorm_le_covariance_integral β hβ N m n hmn
    φ hφ hφint C₂ D E hC₂ hD hE hcoeff hdef0 hdefm hKint
  calc
    _ ≤ 2 * ENNReal.ofReal (Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume)) := hnorm
    _ = ENNReal.ofReal (2 * Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume)) := by
      have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      simpa only [h2] using
        (ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))).symm
    _ ≤ ENNReal.ofReal (2 * Real.sqrt ((C₂ / D) * Bgreen + 2 * E * M₁ ^ 2)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hKbound) (by norm_num))

private theorem two_sqrt_le_mul_of_square_bound (R B C Q X : ℝ)
    (hR : 0 ≤ R) (hRB : R ≤ B * Q) (hB : 4 * B ≤ C ^ 2)
    (hQ : 0 ≤ Q) (hQpow : X ^ 2 = Q) (hCX : 0 ≤ C * X) :
    2 * Real.sqrt R ≤ C * X := by
  have hleftNonneg : 0 ≤ 2 * Real.sqrt R :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ hleftNonneg hCX).mp
  calc
    (2 * Real.sqrt R) ^ 2 = 4 * R := by
      rw [mul_pow, Real.sq_sqrt hR]
      norm_num
    _ ≤ 4 * (B * Q) := mul_le_mul_of_nonneg_left hRB (by norm_num)
    _ = (4 * B) * Q := by rw [mul_assoc]
    _ ≤ C ^ 2 * Q := mul_le_mul_of_nonneg_right hB hQ
    _ = C ^ 2 * X ^ 2 := congrArg (fun y : ℝ => C ^ 2 * y) hQpow.symm
    _ = (C * X) ^ 2 := (mul_pow C X 2).symm

private theorem collision_bounds_integrable (β : ℝ) (N n : ℕ) (L C₂ : ℝ)
    (hL : 0 < L) (hC₂ : 0 ≤ C₂)
    (hsecond : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 k 0 ω ^ 2 ∂disorderLaw ≤
          C₂ / Real.log (1 + (N : ℝ) / k))
    (hlog : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      L / 4 ≤ Real.log (1 + (N : ℝ) / k))
    (hlogN : L / 4 ≤ Real.log (1 + (N : ℝ))) :
    ∀ r ∈ Finset.Icc 1 n,
      Integrable (fun ω => pointToPlane β 0 (n - r) 0 ω ^ 2) disorderLaw ∧
        Polymer.sigmaSq β *
          ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C₂ / (L / 4) := by
  have hcoeff := sigmaSq_collision_secondMoment_le β N n L C₂ hL hC₂
    hsecond hlog hlogN
  intro r hr
  constructor
  · exact Polymer.integrable_pow_pointToPlane β 0 (n - r) 0 2
  · calc
      _ ≤ 4 * C₂ / L := hcoeff r hr
      _ = C₂ / (L / 4) := by field_simp

private theorem localLogError_L2_le_at_N
    (A M₁ M₂ κ δ CVD Csecond C₂ Cdef Cbase C : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hδκ : δ ≤ κ⁻¹ ^ 2) (hκpos : 0 < κ)
    (hC₂ : 0 < C₂) (hC₂Def : C₂ = |Csecond| + 1)
    (hCdef : 0 < Cdef) (hCdefDef : Cdef = |CVD| + 1) (hCbase : 0 ≤ Cbase)
    (hCbaseDef : Cbase = 40 * C₂ * |M₁| * |M₂| + 2 * Cdef * |M₁| ^ 2)
    (hCeq : C = 4 * Cbase + 2) (oN : ℝ)
    (hLgeIn : 8 ≤ |Real.log δ|)
    (hQposIn : 0 < |Real.log δ| ^ (-(1 : ℝ) / 4))
    (hrootIn : Real.sqrt δ ≤ |Real.log δ| ^ (-(1 : ℝ) / 4))
    (hQpowIn : (|Real.log δ| ^ (-(1 : ℝ) / 8)) ^ 2 =
      |Real.log δ| ^ (-(1 : ℝ) / 4))
    (hsmallONIn : oN ≤ |Real.log δ| ^ (-(1 : ℝ) / 4))
    (hdefectN : ∀ ϑ ∈ Set.Icc (-A) A, ∀ (x : Site) (s : ℕ),
      Even s → s ≤ evenCeil (Real.sqrt δ * N) →
        0 ≤ gaussianityDefect disorderLaw
          (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s
            (evenCeil (Real.sqrt δ * N)) x ω)) ∧
        gaussianityDefect disorderLaw
          (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s
            (evenCeil (Real.sqrt δ * N)) x ω)) ≤
          CVD / |Real.log δ| ^ ((1 : ℝ) / 4) + oN)
    (hsecondN : ∀ ϑ ∈ Set.Icc (-A) A, ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ 1 * (N : ℝ) →
        Polymer.sigmaSq (criticalBeta ϑ N) *
          ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
            Csecond / Real.log (1 + (N : ℝ) / k))
    (hlogN : ((evenCeil (Real.sqrt δ * N) : ℝ) ≤ N) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ evenCeil (Real.sqrt δ * N) →
        |Real.log δ| / 4 ≤ Real.log (1 + (N : ℝ) / k)) ∧
      |Real.log δ| / 4 ≤ Real.log (1 + (N : ℝ)))
    (hNscale : 2 / Real.sqrt δ ≤ (N : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ ϑ ∈ Set.Icc (-A) A, ∀ m : ℕ, Even m → δ * N ≤ m →
      (m : ℝ) ≤ κ * δ * N → ∀ φ : Plane → ℝ, Measurable φ → Integrable φ →
        (∫ x, |φ x| ≤ M₁) → (∀ x, |φ x| ≤ M₂) →
          eLpNorm (localLogError (criticalBeta ϑ N) N m
            (evenCeil (Real.sqrt δ * N)) φ) 2 disorderLaw ≤
          ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 8) + ε) := by
  let L : ℝ := |Real.log δ|
  let Q : ℝ := L ^ (-(1 : ℝ) / 4)
  have hLge' : 8 ≤ L := by simpa [L] using hLgeIn
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLge'
  have hQpos : 0 < Q := by simpa [Q, L] using hQposIn
  have hroot : Real.sqrt δ ≤ Q := by simpa [Q, L] using hrootIn
  have hsmallON : oN ≤ Q := by simpa [Q, L] using hsmallONIn
  have hQpow : (L ^ (-(1 : ℝ) / 8)) ^ 2 = Q := by
    simpa [Q, L] using hQpowIn
  have hLpowPos : 0 < L ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hLpos _
  have hQinv : (L ^ ((1 : ℝ) / 4))⁻¹ = Q := by
    dsimp [Q]
    calc
      (L ^ ((1 : ℝ) / 4))⁻¹ = L ^ (-(1 / 4 : ℝ)) :=
        (Real.rpow_neg hLpos.le ((1 : ℝ) / 4)).symm
      _ = L ^ (-1 / 4 : ℝ) := by congr 1; norm_num
      _ = L ^ (-(1 : ℝ) / 4) := by congr 1
  have hD : 0 < L / 4 := by positivity
  have hCge2 : 2 ≤ C := by rw [hCeq]; linarith [hCbase]
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hCge2
  intro ϑ hϑ m hm hδm hmUpper φ hφ hφint hL1 hφM
  have hL1nonneg : 0 ≤ ∫ x : Plane, |φ x| := integral_nonneg fun x => abs_nonneg _
  have hM₁ : 0 ≤ M₁ := le_trans hL1nonneg hL1
  have hM₂ : 0 ≤ M₂ := le_trans (abs_nonneg (φ 0)) (hφM 0)
  have hCbaseEq : Cbase = 40 * C₂ * M₁ * M₂ + 2 * Cdef * M₁ ^ 2 := by
    rw [hCbaseDef, abs_of_nonneg hM₁, abs_of_nonneg hM₂]
  have hnleN : (evenCeil (Real.sqrt δ * N) : ℝ) ≤ N := by
    simpa using hlogN.1
  have hNpos : 0 < (N : ℝ) := by
    have hpos : 0 < 2 / Real.sqrt δ := by positivity
    exact lt_of_lt_of_le hpos hNscale
  have hNnat : 0 < N := Nat.cast_pos.mp hNpos
  have hqN : 2 ≤ Real.sqrt δ * N := by
    have h := (div_le_iff₀ (Real.sqrt_pos.2 hδ)).1 hNscale
    nlinarith
  have hnle : m ≤ evenCeil (Real.sqrt δ * N) := by
    have hsqrtκ : Real.sqrt δ ≤ κ⁻¹ := by
      calc
        Real.sqrt δ ≤ Real.sqrt (κ⁻¹ ^ 2) := Real.sqrt_le_sqrt hδκ
        _ = κ⁻¹ := by rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hκpos)]
    have htime : κ * δ ≤ Real.sqrt δ := by
      calc
        κ * δ = (κ * Real.sqrt δ) * Real.sqrt δ := by
          calc
            κ * δ = κ * (Real.sqrt δ) ^ 2 := by rw [Real.sq_sqrt hδ.le]
            _ = (κ * Real.sqrt δ) * Real.sqrt δ := by ring
        _ ≤ 1 * Real.sqrt δ := by
          exact mul_le_mul_of_nonneg_right
            (by
              rw [mul_comm]
              have hsqrtκ' : Real.sqrt δ ≤ 1 / κ := by simpa [one_div] using hsqrtκ
              exact (le_div_iff₀ hκpos).1 hsqrtκ') (Real.sqrt_nonneg _)
        _ = Real.sqrt δ := by ring
    have hmReal : (m : ℝ) ≤ evenCeil (Real.sqrt δ * N) := by
      calc
        (m : ℝ) ≤ κ * δ * N := hmUpper
        _ ≤ Real.sqrt δ * N :=
          mul_le_mul_of_nonneg_right htime (Nat.cast_nonneg N)
        _ ≤ evenCeil (Real.sqrt δ * N) := by exact_mod_cast le_evenCeil _
    exact_mod_cast hmReal
  have hβ : 0 ≤ criticalBeta ϑ N := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hdef0 : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) 0
          (evenCeil (Real.sqrt δ * N)) x ω)) ≤ Cdef * Q := by
    intro x
    have h := (hdefectN ϑ hϑ x 0 (⟨0, rfl⟩) (Nat.zero_le _)).2
    have hcoef : CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| * Q := by
      calc
        CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| / L ^ ((1 : ℝ) / 4) :=
          div_le_div_of_nonneg_right (le_abs_self CVD) hLpowPos.le
        _ = |CVD| * Q := by rw [div_eq_mul_inv, hQinv]
    calc
      _ ≤ CVD / L ^ ((1 : ℝ) / 4) + oN := h
      _ ≤ |CVD| * Q + Q := add_le_add hcoef hsmallON
      _ = Cdef * Q := by rw [hCdefDef]; ring
  have hdefm : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) m
          (evenCeil (Real.sqrt δ * N)) x ω)) ≤ Cdef * Q := by
    intro x
    have h := (hdefectN ϑ hϑ x m hm (by simpa using hnle)).2
    have hcoef : CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| * Q := by
      calc
        CVD / L ^ ((1 : ℝ) / 4) ≤ |CVD| / L ^ ((1 : ℝ) / 4) :=
          div_le_div_of_nonneg_right (le_abs_self CVD) hLpowPos.le
        _ = |CVD| * Q := by rw [div_eq_mul_inv, hQinv]
    calc
      _ ≤ CVD / L ^ ((1 : ℝ) / 4) + oN := h
      _ ≤ |CVD| * Q + Q := add_le_add hcoef hsmallON
      _ = Cdef * Q := by rw [hCdefDef]; ring
  have hlogK (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ evenCeil (Real.sqrt δ * N)) :
      L / 4 ≤ Real.log (1 + (N : ℝ) / k) := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using hlogN.2.1 k hk hkn
  have hlogZero : L / 4 ≤ Real.log (1 + (N : ℝ)) := hlogN.2.2
  have hsecondK (k : ℕ) (hk : 1 ≤ k)
      (hkn : k ≤ evenCeil (Real.sqrt δ * N)) :
      Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
          C₂ / Real.log (1 + (N : ℝ) / k) := by
    have hkN : (k : ℝ) ≤ (1 : ℝ) * (N : ℝ) := by
      have hkR : (k : ℝ) ≤ evenCeil (Real.sqrt δ * N) := Nat.cast_le.mpr hkn
      simpa only [one_mul] using le_trans hkR hnleN
    have hbase := hsecondN ϑ hϑ k hk hkN
    have hden : 0 < Real.log (1 + (N : ℝ) / k) :=
      lt_of_lt_of_le (by positivity : 0 < L / 4) (hlogK k hk hkn)
    calc
      _ ≤ Csecond / Real.log (1 + (N : ℝ) / k) := hbase
      _ ≤ C₂ / Real.log (1 + (N : ℝ) / k) :=
        div_le_div_of_nonneg_right
          (by rw [hC₂Def]; linarith [le_abs_self Csecond]) hden.le
  have hcoeffInt := collision_bounds_integrable (criticalBeta ϑ N) N
    (evenCeil (Real.sqrt δ * N)) L C₂ hLpos hC₂.le hsecondK hlogK hlogZero
  have hcoeff' : ∀ r ∈ Finset.Icc 1 (evenCeil (Real.sqrt δ * N)),
      Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0
          (evenCeil (Real.sqrt δ * N) - r) 0 ω ^ 2 ∂disorderLaw ≤ C₂ / (L / 4) := by
    intro r hr
    exact (hcoeffInt r hr).2
  have hNbound := integral_truncatedGreen_latticePoint_coarse_le N
    (evenCeil (Real.sqrt δ * N)) hNnat φ hφ hφint M₁ M₂ hL1 hφM
  have hwidth0 : ((evenCeil (Real.sqrt δ * N) : ℝ) + 1) ≤
      Real.sqrt δ * N + 3 := by
    have hceil : (evenCeil (Real.sqrt δ * (N : ℝ)) : ℝ) <
        Real.sqrt δ * (N : ℝ) + 2 :=
      evenCeil_lt_add_two (mul_nonneg (Real.sqrt_nonneg δ) (Nat.cast_nonneg N))
    linarith
  have hwidth : ((evenCeil (Real.sqrt δ * N) : ℝ) + 1) / N ≤
      (5 / 2) * Real.sqrt δ := by
    have hdiv : ((evenCeil (Real.sqrt δ * N) : ℝ) + 1) / N ≤
        Real.sqrt δ + 3 / N := by
      calc
        _ ≤ (Real.sqrt δ * N + 3) / N :=
          div_le_div_of_nonneg_right hwidth0 (Nat.cast_nonneg N)
        _ = _ := by field_simp [ne_of_gt hNpos]
    have hinv' : (1 : ℝ) / N ≤ Real.sqrt δ / 2 := by
      apply (div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [hqN]
    have hinv : (N : ℝ)⁻¹ ≤ Real.sqrt δ / 2 := by
      simpa [one_div] using hinv'
    calc
      _ ≤ Real.sqrt δ + 3 / N := hdiv
      _ ≤ Real.sqrt δ + 3 * (Real.sqrt δ / 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv (by norm_num))
      _ = (5 / 2) * Real.sqrt δ := by ring
  have hgreenBound :
      (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        MomentBounds.truncatedGreen (evenCeil (Real.sqrt δ * N))
          (latticePoint N p.2 - latticePoint N p.1) ∂volume.prod volume) ≤
      10 * Real.sqrt δ * M₂ * M₁ := by
    calc
      _ ≤ 4 * (((evenCeil (Real.sqrt δ * N) : ℝ) + 1) / N) * M₂ * M₁ := hNbound.2
      _ ≤ 4 * ((5 / 2) * Real.sqrt δ) * M₂ * M₁ := by
        calc
          _ = (4 * (((evenCeil (Real.sqrt δ * N) : ℝ) + 1) / N)) * (M₂ * M₁) := by ring
          _ ≤ (4 * ((5 / 2) * Real.sqrt δ)) * (M₂ * M₁) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hwidth (by norm_num)) (mul_nonneg hM₂ hM₁)
          _ = 4 * ((5 / 2) * Real.sqrt δ) * M₂ * M₁ := by ring
      _ = 10 * Real.sqrt δ * M₂ * M₁ := by ring
  have hgreenInt : Integrable (fun p : Plane × Plane =>
      |φ p.1| * |φ p.2| * MomentBounds.truncatedGreen
        (evenCeil (Real.sqrt δ * N))
        (latticePoint N p.2 - latticePoint N p.1)) (volume.prod volume) := hNbound.1
  have hLinv : 0 < 1 / L := by positivity
  have hLinvle : 1 / L ≤ 1 := (div_le_one hLpos).2 (by linarith)
  have hrootInv : Real.sqrt δ * (1 / L) ≤ Q := by
    calc
      _ ≤ Q * (1 / L) := mul_le_mul_of_nonneg_right hroot hLinv.le
      _ ≤ Q * 1 := mul_le_mul_of_nonneg_left hLinvle hQpos.le
      _ = Q := by ring
  have hcoefEq : C₂ / (L / 4) = 4 * C₂ / L := by field_simp
  have hfirstBound : (C₂ / (L / 4)) *
      (10 * Real.sqrt δ * M₂ * M₁) ≤ (40 * C₂ * M₁ * M₂) * Q := by
    rw [hcoefEq]
    calc
      _ = (40 * C₂ * M₂ * M₁) * (Real.sqrt δ * (1 / L)) := by ring
      _ ≤ (40 * C₂ * M₂ * M₁) * Q :=
        mul_le_mul_of_nonneg_left hrootInv (by positivity)
      _ = (40 * C₂ * M₁ * M₂) * Q := by ring
  let Rad : ℝ := (C₂ / (L / 4)) * (10 * Real.sqrt δ * M₂ * M₁) +
    2 * (Cdef * Q) * M₁ ^ 2
  have hRadBound : Rad ≤ Cbase * Q := by
    dsimp [Rad]
    calc
      _ ≤ (40 * C₂ * M₁ * M₂) * Q + 2 * (Cdef * Q) * M₁ ^ 2 := by
        exact add_le_add hfirstBound le_rfl
      _ = Cbase * Q := by rw [hCbaseEq]; ring
  have hRadNonneg : 0 ≤ Rad := by dsimp [Rad]; positivity
  have hCbaseSq : 4 * Cbase ≤ C ^ 2 := by
    calc
      4 * Cbase ≤ 2 * C := by rw [hCeq]; linarith [hCbase]
      _ ≤ C ^ 2 := by
        have hCnonneg : 0 ≤ C := le_trans (by norm_num) hCge2
        have := mul_le_mul_of_nonneg_left hCge2 hCnonneg
        simpa [mul_comm, pow_two] using this
  have htargetNonneg : 0 ≤ C * L ^ (-(1 : ℝ) / 8) := by positivity
  have hmain : 2 * Real.sqrt Rad ≤ C * L ^ (-(1 : ℝ) / 8) :=
    two_sqrt_le_mul_of_square_bound Rad Cbase C Q (L ^ (-(1 : ℝ) / 8))
      hRadNonneg hRadBound hCbaseSq hQpos.le hQpow htargetNonneg
  have hcore := localLogError_L2_le_green_bound (criticalBeta ϑ N) hβ N m
    (evenCeil (Real.sqrt δ * N)) hnle φ hφ hφint C₂ (L / 4) (Cdef * Q)
    M₁ (10 * Real.sqrt δ * M₂ * M₁) hC₂.le hD
    (mul_nonneg hCdef.le hQpos.le) hcoeff' hdef0 hdefm hL1 hM₁ hgreenInt hgreenBound
  have hreal : 2 * Real.sqrt Rad ≤ C * L ^ (-(1 : ℝ) / 8) := hmain
  calc
    _ ≤ ENNReal.ofReal (2 * Real.sqrt Rad) := hcore
    _ ≤ ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 8)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 8) + ε) :=
      ENNReal.ofReal_le_ofReal (by linarith [le_of_lt hε])
    _ = ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 8) + ε) := by
      simp [L]

/-- The local error bound (lattice smoothing estimates), from the one-point moment comparison: for small `δ`, eventually in `N`, uniformly in `ϑ ∈
[-A, A]`, even `m ∈ [δ N, κ δ N]` and tests `φ` with `‖φ‖₁ ≤ M₁`, `‖φ‖∞ ≤ M₂`, the `L²` norm of the
local log error is at most `C |log δ| ^ (-1/8) + ε`. -/
theorem localLogError_L2_le_of (hVD : PropVDBound) (A M₁ M₂ κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ m : ℕ, Even m → δ * N ≤ m →
          (m : ℝ) ≤ κ * δ * N → ∀ φ : Plane → ℝ, Measurable φ → Integrable φ →
            (∫ x, |φ x| ≤ M₁) → (∀ x, |φ x| ≤ M₂) →
              eLpNorm (localLogError (criticalBeta ϑ N) N m
                (evenCeil (Real.sqrt δ * N)) φ) 2 disorderLaw ≤
                ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 8) + ε) := by
  obtain ⟨δVD, CVD, hδVDpos, hδVDlt, hVDsmall⟩ :=
    gaussianityDefect_small_time_of hVD A
  obtain ⟨Csecond, hsecond⟩ := OnePoint.sigmaSq_secondMoment_le_uniform A 1
  let C₂ : ℝ := |Csecond| + 1
  let Cdef : ℝ := |CVD| + 1
  let Cbase : ℝ := 40 * C₂ * |M₁| * |M₂| + 2 * Cdef * |M₁| ^ 2
  let C : ℝ := 4 * Cbase + 2
  let δ₀ : ℝ := min δVD (min (1 / 16) (min (Real.exp (-8)) (κ⁻¹ ^ 2)))
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  have hCdef : 0 < Cdef := by dsimp [Cdef]; positivity
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    positivity
  have hδ₀core : δ₀ ≤ min (1 / 16) (min (Real.exp (-8)) (κ⁻¹ ^ 2)) :=
    min_le_right δVD _
  refine ⟨C, δ₀, hδ₀pos, ?_⟩
  intro δ hδ hδle ε hε
  have hδVD : δ ≤ δVD := le_trans hδle (min_le_left _ _)
  have hδ16 : δ ≤ 1 / 16 :=
    le_trans hδle (le_trans hδ₀core (min_le_left _ _))
  have hδexp : δ ≤ Real.exp (-8) :=
    le_trans hδle (le_trans hδ₀core
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδκ : δ ≤ κ⁻¹ ^ 2 :=
    le_trans hδle (le_trans hδ₀core
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hLdata := sqrt_le_log_rpow_neg_quarter δ hδ hδexp
  let L : ℝ := |Real.log δ|
  let Q : ℝ := L ^ (-(1 : ℝ) / 4)
  have hLge : 8 ≤ L := by simpa [L] using hLdata.1
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLge
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hroot : Real.sqrt δ ≤ Q := by simpa [L, Q] using hLdata.2
  have hQpow : (L ^ (-(1 : ℝ) / 8)) ^ 2 = Q := by
    dsimp [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hLpowPos : 0 < L ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hLpos _
  have hQinv : (L ^ ((1 : ℝ) / 4))⁻¹ = Q := by
    dsimp [Q]
    calc
      (L ^ ((1 : ℝ) / 4))⁻¹ = L ^ (-(1 / 4 : ℝ)) :=
        (Real.rpow_neg hLpos.le ((1 : ℝ) / 4)).symm
      _ = L ^ (-1 / 4 : ℝ) := by congr 1; norm_num
  have hD : 0 < L / 4 := by positivity
  have hsmall := hVDsmall δ hδ hδVD
  obtain ⟨o, ho, hdefect⟩ := hsmall
  have hsmallO : ∀ᶠ N : ℕ in atTop, o N ≤ Q := by
    have h := ho.eventually (eventually_lt_nhds hQpos)
    filter_upwards [h] with N hN
    exact le_of_lt hN
  have hNscale : ∀ᶠ N : ℕ in atTop, 2 / Real.sqrt δ ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 / Real.sqrt δ)
  have hlogEventually := eventually_small_time_log_bounds δ hδ hδ16 hδexp
  filter_upwards [hsmallO, hdefect, hsecond, hlogEventually, hNscale]
    with N hsmallON hdefectN hsecondN hlogN hNscale
  intro ϑ hϑ m hm hδm hmUpper φ hφ hφint hL1 hφM
  exact localLogError_L2_le_at_N A M₁ M₂ κ δ CVD Csecond C₂ Cdef Cbase C N
    hδ hδκ hκpos hC₂ (by rfl) hCdef (by rfl) hCbase (by rfl) (by rfl) (o N)
    (by simpa [L] using hLge)
    (by simpa [L, Q] using hQpos)
    (by simpa [L, Q] using hroot)
    (by simpa [L, Q] using hQpow)
    (by simpa [L, Q] using hsmallON)
    hdefectN hsecondN hlogN hNscale ε hε ϑ hϑ m hm hδm hmUpper
    φ hφ hφint hL1 hφM

end Critical2DKPZ.Smoothing

end
