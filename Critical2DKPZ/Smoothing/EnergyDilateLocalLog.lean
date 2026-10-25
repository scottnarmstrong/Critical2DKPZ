/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.LocalLogL2Bounds
public import Critical2DKPZ.Smoothing.EnergyDilateGreen
import Mathlib.Tactic

/-! # Local logarithmic error bounds for compact dilation families -/

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

private theorem two_sqrt_energy_bound (C C₂ H L : ℝ)
    (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hCfirst : 16 * C₂ ≤ C)
    (hH : 0 ≤ H) (hL : 0 < L) :
    2 * Real.sqrt (4 * C₂ * H / L) ≤ Real.sqrt (C * H / L) := by
  have hX : 0 ≤ 4 * C₂ * H / L := by positivity
  have hY : 0 ≤ C * H / L := by positivity
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  calc
    (2 * Real.sqrt (4 * C₂ * H / L)) ^ 2 = 16 * C₂ * (H / L) := by
      rw [mul_pow, Real.sq_sqrt hX]
      ring
    _ ≤ C * (H / L) := mul_le_mul_of_nonneg_right hCfirst (div_nonneg hH hL.le)
    _ = (Real.sqrt (C * H / L)) ^ 2 := by
      rw [Real.sq_sqrt hY]
      ring

private theorem two_sqrt_defect_bound (C Cdef Q M L : ℝ)
    (hC : 0 ≤ C) (hCdef : 0 ≤ Cdef) (hL : 0 < L)
    (hCsquare : 8 * Cdef ≤ C ^ 2) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hQpow : (L ^ (-(1 : ℝ) / 8)) ^ 2 = Q) :
    2 * Real.sqrt (2 * Cdef * Q * M ^ 2) ≤ C * M * L ^ (-(1 : ℝ) / 8) := by
  have hX : 0 ≤ 2 * Cdef * Q * M ^ 2 := by positivity
  have hY : 0 ≤ C * M * L ^ (-(1 : ℝ) / 8) := by positivity
  apply (sq_le_sq₀ (by positivity) hY).mp
  calc
    (2 * Real.sqrt (2 * Cdef * Q * M ^ 2)) ^ 2 =
        (8 * Cdef) * (Q * M ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hX]
          ring
    _ ≤ C ^ 2 * (Q * M ^ 2) :=
      mul_le_mul_of_nonneg_right hCsquare (mul_nonneg hQ (sq_nonneg M))
    _ = C ^ 2 * (L ^ (-(1 : ℝ) / 8)) ^ 2 * M ^ 2 := by rw [hQpow]; ring
    _ = (C * M * L ^ (-(1 : ℝ) / 8)) ^ 2 := by ring

private theorem z_error_factorization (C₂ L ε : ℝ) (hL : 0 < L)
    (hC₂ : 0 < C₂) :
    C₂ / (L / 4) * (ε ^ 2 / (64 * (C₂ + 1))) =
      (ε ^ 2 / 16) * (C₂ / (L * (C₂ + 1))) := by
  field_simp [ne_of_gt hL, ne_of_gt (by positivity : 0 < C₂ + 1)]
  ring

private theorem two_sqrt_small_le (R ε : ℝ) (hR : 0 ≤ R)
    (hRε : R ≤ ε ^ 2 / 16) (hε : 0 ≤ ε) : 2 * Real.sqrt R ≤ ε := by
  apply (sq_le_sq₀ (by positivity) hε).mp
  calc
    (2 * Real.sqrt R) ^ 2 = 4 * R := by rw [mul_pow, Real.sq_sqrt hR]; norm_num
    _ ≤ 4 * (ε ^ 2 / 16) := mul_le_mul_of_nonneg_left hRε (by norm_num)
    _ = ε ^ 2 / 4 := by ring
    _ ≤ ε ^ 2 := div_le_self (sq_nonneg ε) (by norm_num)

private theorem two_mul_add_three (x y z : ℝ) :
    2 * (x + y + z) = 2 * x + 2 * y + 2 * z := by ring

private theorem add_three_bound (x y z A B ε : ℝ)
    (hx : 2 * x ≤ A) (hy : 2 * y ≤ B) (hz : 2 * z ≤ ε) :
    2 * x + 2 * y + 2 * z ≤ A + B + ε := by linarith

/-- The local logarithmic error satisfies an L² heat-energy bound uniform over the stated dilations. -/
private theorem localLogError_L2_energy_at_N
    (A κ δ C C₂ Cdef CVD Csecond oN εg ε : ℝ) (N : ℕ) (ψ : Plane → ℝ)
    (hC₂_def : C₂ = |Csecond| + 1) (hCdef_def : Cdef = |CVD| + 1)
    (hεg_def : εg = ε ^ 2 / (64 * (C₂ + 1)))
    (hδ : 0 < δ) (hδκ : δ ≤ κ⁻¹ ^ 2) (hκpos : 0 < κ)
    (hC₂ : 0 < C₂) (hCdef : 0 < Cdef) (hCfirst : 16 * C₂ ≤ C)
    (hCsquare : 8 * Cdef ≤ C ^ 2)
    (hLdata : 8 ≤ |Real.log δ| ∧
      Real.sqrt δ ≤ |Real.log δ| ^ (-(1 : ℝ) / 4))
    (hsmallON : oN ≤ |Real.log δ| ^ (-(1 : ℝ) / 4))
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
    (hNscale : 2 / Real.sqrt δ ≤ (N : ℝ))
    (hψ : Measurable ψ) (hψint : Integrable ψ)
    (hψbound : ∃ M : ℝ, ∀ x, |ψ x| ≤ M)
    (hGreenN : ∫ p : Plane × Plane, |ψ p.1| * |ψ p.2| *
      MomentBounds.truncatedGreen (evenCeil (Real.sqrt δ * N))
        (latticePoint N p.2 - latticePoint N p.1) ≤
        heatEnergy (Real.sqrt δ) ψ + εg)
    (hεg : 0 < εg) (hε : 0 < ε) :
    ∀ ϑ ∈ Set.Icc (-A) A, ∀ m : ℕ, Even m → δ * N ≤ m →
      (m : ℝ) ≤ κ * δ * N →
        eLpNorm (localLogError (criticalBeta ϑ N) N m
          (evenCeil (Real.sqrt δ * N)) ψ) 2 disorderLaw ≤
          ENNReal.ofReal (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / |Real.log δ|) +
            C * (∫ x, |ψ x|) * |Real.log δ| ^ (-(1 : ℝ) / 8) + ε) := by
  obtain ⟨Mψ, hψM⟩ := hψbound
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
      _ = L ^ (-(1 : ℝ) / 4) := by congr 1
  have hD : 0 < L / 4 := by positivity
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hCfirst
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
      _ ≤ CVD / L ^ ((1 : ℝ) / 4) + oN := h
      _ ≤ |CVD| * Q + Q := add_le_add hcoef hsmallON
      _ = Cdef * Q := by rw [hCdef_def]; ring
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
      _ ≤ CVD / L ^ ((1 : ℝ) / 4) + oN := h
      _ ≤ |CVD| * Q + Q := add_le_add hcoef hsmallON
      _ = Cdef * Q := by rw [hCdef_def]; ring
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
      _ ≤ C₂ / Real.log (1 + (N : ℝ) / k) := by
        apply div_le_div_of_nonneg_right _ hden.le
        rw [hC₂_def]
        linarith [le_abs_self Csecond]
  have hcoeff := sigmaSq_collision_secondMoment_le (criticalBeta ϑ N) N n L C₂ hLpos
    hC₂.le hsecondK hlogK hlogZero
  have hcoeff' : ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C₂ / (L / 4) := by
    intro r hr
    calc
      _ ≤ 4 * C₂ / L := hcoeff r hr
      _ = C₂ / (L / 4) := by field_simp
  have hGreenIntegrable := integrable_truncatedGreen_latticePoint δ (N := N)
    ψ hψ hψint
  have hψnorm : Integrable (fun x : Plane => |ψ x|) := by
    simpa only [Real.norm_eq_abs] using hψint.norm
  let F : Plane × Plane → ℝ := fun p => |ψ p.1| * |ψ p.2|
  let G : Plane × Plane → ℝ := fun p =>
    MomentBounds.truncatedGreen n (latticePoint N p.2 - latticePoint N p.1)
  let K : Plane × Plane → ℝ := fun p => F p *
    (C₂ / (L / 4) * G p + Cdef * Q + Cdef * Q)
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hψnorm.mul_prod hψnorm
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
      (∫ x : Plane, |ψ x|) ^ 2 := by
    rw [← Measure.volume_eq_prod Plane Plane]
    simpa [F] using integral_abs_plane_mul_integral_abs ψ
  have hL1nonneg : 0 ≤ ∫ x : Plane, |ψ x| := integral_nonneg fun x => abs_nonneg _
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
        heatEnergy (Real.sqrt δ) ψ + εg := by
    rw [← Measure.volume_eq_prod Plane Plane]
    have hfun : (fun p : Plane × Plane => F p * G p) = fun p =>
        |ψ p.1| * |ψ p.2| *
          MomentBounds.truncatedGreen (evenCeil (Real.sqrt δ * N))
            (latticePoint N p.2 - latticePoint N p.1) := by
      funext p
      simp only [F, G, n]
    rw [hfun]
    exact hGreenN
  have hKbound : ∫ p : Plane × Plane, K p ∂volume.prod volume ≤
      C₂ / (L / 4) * (heatEnergy (Real.sqrt δ) ψ + εg) +
        (Cdef * Q + Cdef * Q) * (∫ x : Plane, |ψ x|) ^ 2 := by
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
  let X : ℝ := 4 * C₂ * heatEnergy (Real.sqrt δ) ψ / L
  let Y : ℝ := 2 * Cdef * Q * (∫ x : Plane, |ψ x|) ^ 2
  let Z : ℝ := C₂ / (L / 4) * εg
  have hheatpos : 0 ≤ heatEnergy (Real.sqrt δ) ψ :=
    (heatEnergy_le_of_bounded ψ hψ hψint Mψ hψM (Real.sqrt_pos.2 hδ)).1
  have hXnonneg : 0 ≤ X := by dsimp [X]; positivity
  have hYnonneg : 0 ≤ Y := by dsimp [Y]; positivity
  have hZnonneg : 0 ≤ Z := by dsimp [Z]; positivity
  have hRadBound : (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤ X + Y + Z := by
    rw [hCoeffEq] at hKbound
    dsimp [X, Y, Z]
    calc
      _ ≤ (4 * C₂ / L) * (heatEnergy (Real.sqrt δ) ψ + εg) +
          (Cdef * Q + Cdef * Q) * (∫ x : Plane, |ψ x|) ^ 2 := hKbound
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
      (C * heatEnergy (Real.sqrt δ) ψ / L) := by
    dsimp [X]
    exact two_sqrt_energy_bound C C₂ (heatEnergy (Real.sqrt δ) ψ) L
      hCpos.le hC₂.le hCfirst hheatpos hLpos
  have hrootY : 2 * Real.sqrt Y ≤
      C * (∫ x : Plane, |ψ x|) * L ^ (-(1 : ℝ) / 8) := by
    simpa [Y] using two_sqrt_defect_bound C Cdef Q (∫ x : Plane, |ψ x|) L
      hCpos.le hCdef.le hLpos hCsquare hQpos.le hL1nonneg hQpow
  have hZsmall : Z ≤ ε ^ 2 / 16 := by
    have hratio : C₂ / (L * (C₂ + 1)) ≤ 1 := by
      apply (div_le_one (mul_pos hLpos (by positivity))).2
      exact le_trans (by linarith [hC₂])
        (mul_le_mul_of_nonneg_right hLone (by positivity))
    calc
      Z = (ε ^ 2 / 16) * (C₂ / (L * (C₂ + 1))) := by
        dsimp [Z]
        rw [hεg_def]
        exact z_error_factorization C₂ L ε hLpos hC₂
      _ ≤ ε ^ 2 / 16 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
          (div_nonneg (sq_nonneg ε) (by norm_num : (0 : ℝ) ≤ 16))
  have hrootZ : 2 * Real.sqrt Z ≤ ε :=
    two_sqrt_small_le Z ε hZnonneg hZsmall hε.le
  have hrootReal : 2 * Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤
      Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / L) +
        C * (∫ x : Plane, |ψ x|) * L ^ (-(1 : ℝ) / 8) + ε := by
    calc
      _ ≤ 2 * (Real.sqrt X + Real.sqrt Y + Real.sqrt Z) :=
        mul_le_mul_of_nonneg_left hrootSum (by norm_num)
      _ = 2 * Real.sqrt X + 2 * Real.sqrt Y + 2 * Real.sqrt Z :=
        two_mul_add_three _ _ _
      _ ≤ Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / L) +
          C * (∫ x : Plane, |ψ x|) * L ^ (-(1 : ℝ) / 8) + ε :=
        add_three_bound _ _ _ _ _ _ hrootX hrootY hrootZ
  have hnorm := localLogError_eLpNorm_le_covariance_integral
    (criticalBeta ϑ N) hβ N m n (by exact hnle) ψ hψ hψint C₂ (L / 4) (Cdef * Q)
    hC₂.le hD (mul_nonneg hCdef.le hQpos.le) hcoeff' hdef0 hdefm hKint
  have hNormReal :
      2 * Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume) ≤
        Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / L) +
          C * (∫ x : Plane, |ψ x|) * L ^ (-(1 : ℝ) / 8) + ε := hrootReal
  change eLpNorm (localLogError (criticalBeta ϑ N) N m n ψ) 2 disorderLaw ≤ _
  calc
    _ ≤ 2 * ENNReal.ofReal
        (Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume)) := hnorm
    _ = ENNReal.ofReal
        (2 * Real.sqrt (∫ p : Plane × Plane, K p ∂volume.prod volume)) := by
      have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      simpa only [h2] using
        (ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))).symm
    _ ≤ ENNReal.ofReal
        (Real.sqrt (C * heatEnergy (Real.sqrt δ) ψ / L) +
          C * (∫ x : Plane, |ψ x|) * L ^ (-(1 : ℝ) / 8) + ε) :=
      ENNReal.ofReal_le_ofReal hNormReal

/-- The variance bound controls the local logarithmic error for dilated tests uniformly over compact positive dilation intervals. -/
theorem localLogError_L2_le_energy_dilate_of (hVD : PropVDBound) (A κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ φ : Plane → ℝ, Measurable φ → Integrable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
        ∀ c₀ c₁ : ℝ, 0 < c₀ → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ N : ℕ in atTop, ∀ c ∈ Set.Icc c₀ c₁, ∀ ϑ ∈ Set.Icc (-A) A,
            ∀ m : ℕ, Even m → δ * N ≤ m → (m : ℝ) ≤ κ * δ * N →
              eLpNorm (localLogError (criticalBeta ϑ N) N m
                (evenCeil (Real.sqrt δ * N)) (fun y => c * φ (Real.sqrt c • y))) 2 disorderLaw ≤
                ENNReal.ofReal (Real.sqrt
                    (C * heatEnergy (Real.sqrt δ) (fun y => c * φ (Real.sqrt c • y)) / |Real.log δ|) +
                  C * (∫ x, |c * φ (Real.sqrt c • x)|) * |Real.log δ| ^ (-(1 : ℝ) / 8) + ε) := by
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
  intro δ hδ hδle φ hφ hφint hφbound c₀ c₁ hc₀ ε hε
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
  have hGreenEventually := integral_truncatedGreen_latticePoint_le_dilate δ hδ φ hφ hφint
    ⟨Mφ, hφM⟩ (c₀ := c₀) (c₁ := c₁) hc₀ εg hgreenεpos
  have hNscale : ∀ᶠ N : ℕ in atTop, 2 / Real.sqrt δ ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 / Real.sqrt δ)
  have hlogEventually := eventually_small_time_log_bounds δ hδ hδ16 hδexp
  filter_upwards [hsmallO, hdefect, hsecond, hlogEventually, hGreenEventually,
    hNscale] with N hsmallON hdefectN hsecondN hlogN hGreenN hNscale
  intro c hc ϑ hϑ m hm hδm hmUpper
  have hcpos : 0 < c := lt_of_lt_of_le hc₀ hc.1
  have hc₁pos : 0 < c₁ := lt_of_lt_of_le hc₀ (le_trans hc.1 hc.2)
  let ψ : Plane → ℝ := fun x => c * φ (Real.sqrt c • x)
  have hψmeas : Measurable ψ := measurable_dilate φ hφ c
  have hψint : Integrable ψ := integrable_dilate φ hφint hcpos
  have hψbound : ∃ M : ℝ, ∀ x, |ψ x| ≤ M := by
    refine ⟨c₁ * Mφ, ?_⟩
    intro x
    change |c * φ (Real.sqrt c • x)| ≤ c₁ * Mφ
    rw [abs_mul, abs_of_pos hcpos]
    exact mul_le_mul hc.2 (hφM _) (abs_nonneg _) hc₁pos.le
  have hGreenNc := hGreenN c hc
  exact localLogError_L2_energy_at_N A κ δ C C₂ Cdef CVD Csecond (o N) εg ε N ψ
    rfl rfl rfl hδ hδκ hκpos hC₂ hCdef hCfirst hCsquare hLdata
    (by simpa [L, Q] using hsmallON)
    hdefectN hsecondN hlogN hNscale hψmeas hψint hψbound hGreenNc hgreenεpos hε
    ϑ hϑ m hm hδm hmUpper

end Critical2DKPZ.Smoothing

end
