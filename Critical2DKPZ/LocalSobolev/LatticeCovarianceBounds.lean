/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeCovarianceBase
public import Critical2DKPZ.LocalSobolev.CovarianceBounds
public import Critical2DKPZ.Renewal.PolymerBridge
public import Critical2DKPZ.Polymer.Locality
public import Critical2DKPZ.Smoothing.PolymerLogMomentBounds
import Mathlib.Tactic

/-! # Forward lattice covariance bounds -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace Critical2DKPZ.LocalSobolev

private theorem covariance_kpzLattice_flat_le_of_data (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (x y : Plane) (m : ℕ) (hm : m = evenCeil ((N : ℝ) * t))
    (hm1 : 1 ≤ m) (M S C E v : ℝ) (hβ : 0 ≤ criticalBeta ϑ N)
    (hβsq : criticalBeta ϑ N ^ 2 ≤ v)
    (hMpos : 0 < M) (hprod : v * M ≤ S)
    (hM : ∀ z : Site,
      ∫ ω, pointToPlane (criticalBeta ϑ N) 0 (m - 1) z ω ^ 2 ∂disorderLaw ≤ M)
    (hcoeff : ∀ r ∈ Finset.Icc 1 (m - 1),
      Polymer.sigmaSq (criticalBeta ϑ N) *
        (∫ ω, pointToPlane (criticalBeta ϑ N) 0 (m - 1 - r) 0 ω ^ 2 ∂disorderLaw) ≤ C)
    (hDx : gaussianityDefect disorderLaw
      (fun ω => Real.log (pointToPlane (criticalBeta ϑ N) 0 (m - 1)
        (latticePoint N x) ω)) ≤ E)
    (hDy : gaussianityDefect disorderLaw
      (fun ω => Real.log (pointToPlane (criticalBeta ϑ N) 0 (m - 1)
        (latticePoint N y) ω)) ≤ E) :
    covariance (kpzLattice ϑ N t 0 x) (kpzLattice ϑ N t 0 y) disorderLaw ≤
      Real.log (1 + C * MomentBounds.truncatedGreen (m - 1)
        (latticePoint N y - latticePoint N x)) + 2 * E + 2 * Real.sqrt S + v := by
  let β := criticalBeta ϑ N
  let n := m - 1
  let sx := latticePoint N x
  let sy := latticePoint N y
  let rev := PolymerCalculus.reversedDisorder m
  let Fx : Disorder → ℝ := fun ω => Real.log (pointToPlane β 0 n sx ω)
  let Fy : Disorder → ℝ := fun ω => Real.log (pointToPlane β 0 n sy ω)
  let Ux : Disorder → ℝ := fun ω => Fx (rev ω)
  let Uy : Disorder → ℝ := fun ω => Fy (rev ω)
  let Dx : Disorder → ℝ := fun ω => β * ω (m, sx)
  let Dy : Disorder → ℝ := fun ω => β * ω (m, sy)
  let cx := β ^ 2 / 2 + kpzLatticeCentring ϑ N t
  let cy := β ^ 2 / 2 + kpzLatticeCentring ϑ N t
  have hn : n + 1 = m := by dsimp [n]; omega
  have hFx : MemLp Fx 2 disorderLaw := by
    dsimp [Fx, β, n, sx]
    exact memLp_log_pointToPlane _ _ _ _
  have hFy : MemLp Fy 2 disorderLaw := by
    dsimp [Fy, β, n, sy]
    exact memLp_log_pointToPlane _ _ _ _
  have hrevMP := PolymerCalculus.measurePreserving_reversedDisorder m
  have hUx : MemLp Ux 2 disorderLaw := by
    dsimp [Ux]
    exact hFx.comp_measurePreserving hrevMP
  have hUy : MemLp Uy 2 disorderLaw := by
    dsimp [Uy]
    exact hFy.comp_measurePreserving hrevMP
  have hcoordX := Gaussian.hasLaw_disorder_eval (m, sx)
  have hcoordY := Gaussian.hasLaw_disorder_eval (m, sy)
  have hcoordXmem : MemLp (fun ω : Disorder => ω (m, sx)) 2 disorderLaw :=
    hcoordX.memLp (memLp_id_gaussianReal 2)
  have hcoordYmem : MemLp (fun ω : Disorder => ω (m, sy)) 2 disorderLaw :=
    hcoordY.memLp (memLp_id_gaussianReal 2)
  have hDxMem : MemLp Dx 2 disorderLaw := by
    dsimp [Dx]
    simpa only [mul_comm] using hcoordXmem.const_mul β
  have hDyMem : MemLp Dy 2 disorderLaw := by
    dsimp [Dy]
    simpa only [mul_comm] using hcoordYmem.const_mul β
  have hcoordXvar : Var[fun ω : Disorder => ω (m, sx); disorderLaw] = 1 := by
    calc
      _ = Var[id; gaussianReal 0 1] := hcoordX.variance_eq
      _ = 1 := variance_id_gaussianReal
  have hcoordYvar : Var[fun ω : Disorder => ω (m, sy); disorderLaw] = 1 := by
    calc
      _ = Var[id; gaussianReal 0 1] := hcoordY.variance_eq
      _ = 1 := variance_id_gaussianReal
  have hDxVar : Var[Dx; disorderLaw] = β ^ 2 := by
    dsimp [Dx]
    rw [variance_const_mul, hcoordXvar]
    ring
  have hDyVar : Var[Dy; disorderLaw] = β ^ 2 := by
    dsimp [Dy]
    rw [variance_const_mul, hcoordYvar]
    ring
  have hFxMeas : AEMeasurable Fx disorderLaw := by
    dsimp [Fx, β, n, sx]
    exact (Real.measurable_log.comp (Polymer.measurable_pointToPlane _ _ _ _)).aemeasurable
  have hFyMeas : AEMeasurable Fy disorderLaw := by
    dsimp [Fy, β, n, sy]
    exact (Real.measurable_log.comp (Polymer.measurable_pointToPlane _ _ _ _)).aemeasurable
  have hrevLaw : HasLaw rev disorderLaw disorderLaw := by
    constructor
    · exact (PolymerCalculus.measurePreserving_reversedDisorder m).measurable.aemeasurable
    · simpa [rev] using (PolymerCalculus.measurePreserving_reversedDisorder m).map_eq
  have hcovRev : covariance Ux Uy disorderLaw = covariance Fx Fy disorderLaw := by
    dsimp [Ux, Uy]
    exact hrevLaw.covariance_fun_comp hFxMeas hFyMeas
  have hvarUx : Var[Ux; disorderLaw] = Var[Fx; disorderLaw] := by
    dsimp [Ux]
    exact hrevMP.variance_fun_comp hFxMeas
  have hvarUy : Var[Uy; disorderLaw] = Var[Fy; disorderLaw] := by
    dsimp [Uy]
    exact hrevMP.variance_fun_comp hFyMeas
  have hvarFx : Var[Fx; disorderLaw] ≤ M := by
    dsimp [Fx, β, n, sx]
    have h := variance_log_pointToPlane_le_log_secondMoment β 0 (m - 1) (latticePoint N x)
    have hp := integral_sq_pointToPlane_pos (criticalBeta ϑ N) 0 (m - 1) (latticePoint N x)
    have hmom := hM (latticePoint N x)
    have hlog := Real.log_le_sub_one_of_pos hp
    linarith
  have hvarFy : Var[Fy; disorderLaw] ≤ M := by
    dsimp [Fy, β, n, sy]
    have h := variance_log_pointToPlane_le_log_secondMoment β 0 (m - 1) (latticePoint N y)
    have hp := integral_sq_pointToPlane_pos (criticalBeta ϑ N) 0 (m - 1) (latticePoint N y)
    have hmom := hM (latticePoint N y)
    have hlog := Real.log_le_sub_one_of_pos hp
    linarith
  have hC1 := smoothedP2Plane_covariance_le_log_truncatedGreen_of β hβ n sx sy C E
    (by simpa [β, n] using hcoeff) (by
      simpa [Fx, β, n, smoothedP2Plane_zero_eq_pointToPlane] using hDx)
    (by simpa [Fy, β, n, smoothedP2Plane_zero_eq_pointToPlane] using hDy)
  have hFxFy : covariance Fx Fy disorderLaw ≤
      Real.log (1 + C * MomentBounds.truncatedGreen n (sy - sx)) + 2 * E := by
    simpa only [Fx, Fy, smoothedP2Plane_zero_eq_pointToPlane] using hC1
  have hreprx (ω : Disorder) :
      kpzLattice ϑ N t 0 x ω = Ux ω + Dx ω - cx := by
    rw [kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t x ω (by omega)]
    simp only [Ux, Fx, Dx, cx, β, n, sx, rev]
    rw [hm]
    ring
  have hrepry (ω : Disorder) :
      kpzLattice ϑ N t 0 y ω = Uy ω + Dy ω - cy := by
    rw [kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t y ω (by omega)]
    simp only [Uy, Fy, Dy, cy, β, n, sy, rev]
    rw [hm]
    ring
  have hcovrepr : covariance (kpzLattice ϑ N t 0 x) (kpzLattice ϑ N t 0 y) disorderLaw =
      covariance (Ux + Dx) (Uy + Dy) disorderLaw := by
    have hx : (fun ω => kpzLattice ϑ N t 0 x ω) = fun ω => Ux ω + Dx ω - cx :=
      funext hreprx
    have hy : (fun ω => kpzLattice ϑ N t 0 y ω) = fun ω => Uy ω + Dy ω - cy :=
      funext hrepry
    change covariance (fun ω => kpzLattice ϑ N t 0 x ω)
      (fun ω => kpzLattice ϑ N t 0 y ω) disorderLaw = _
    rw [hx, hy]
    change covariance (fun ω => (Ux + Dx) ω - cx)
      (fun ω => (Uy + Dy) ω - cy) disorderLaw = _
    rw [covariance_sub_const_left
      ((hUx.add hDxMem).integrable (by norm_num)) cx,
      covariance_sub_const_right ((hUy.add hDyMem).integrable (by norm_num)) cy]
  have hcovadd := covariance_add_add_le_of hUx hUy hDxMem hDyMem
  have hvarDprod : Var[Dx; disorderLaw] * Var[Uy; disorderLaw] ≤ S := by
    rw [hDxVar, hvarUy]
    have h0 : 0 ≤ Var[Fy; disorderLaw] := variance_nonneg _ _
    have h1 : Var[Fy; disorderLaw] ≤ M := hvarFy
    have h2 : β ^ 2 * M ≤ S := (mul_le_mul_of_nonneg_right hβsq hMpos.le).trans hprod
    exact (mul_le_mul_of_nonneg_left h1 (sq_nonneg β)).trans h2
  have hvarUprod : Var[Ux; disorderLaw] * Var[Dy; disorderLaw] ≤ S := by
    rw [hvarUx, hDyVar]
    have h0 : 0 ≤ Var[Fx; disorderLaw] := variance_nonneg _ _
    have h1 : Var[Fx; disorderLaw] ≤ M := hvarFx
    have h2 : β ^ 2 * M ≤ S := (mul_le_mul_of_nonneg_right hβsq hMpos.le).trans hprod
    calc
      _ = β ^ 2 * Var[Fx; disorderLaw] := by ring
      _ ≤ β ^ 2 * M := mul_le_mul_of_nonneg_left h1 (sq_nonneg β)
      _ ≤ S := h2
  have hroot1 : Real.sqrt (Var[Dx; disorderLaw] * Var[Uy; disorderLaw]) ≤ Real.sqrt S :=
    Real.sqrt_le_sqrt hvarDprod
  have hroot2 : Real.sqrt (Var[Ux; disorderLaw] * Var[Dy; disorderLaw]) ≤ Real.sqrt S :=
    Real.sqrt_le_sqrt hvarUprod
  have hroot3 : Real.sqrt (Var[Dx; disorderLaw] * Var[Dy; disorderLaw]) ≤ v := by
    rw [hDxVar, hDyVar]
    have hβ20 : 0 ≤ β ^ 2 := sq_nonneg β
    calc
      Real.sqrt (β ^ 2 * β ^ 2) = β ^ 2 := by
        rw [show β ^ 2 * β ^ 2 = (β ^ 2) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg hβ20]
      _ ≤ v := hβsq
  calc
    _ = covariance (Ux + Dx) (Uy + Dy) disorderLaw := hcovrepr
    _ ≤ covariance Ux Uy disorderLaw +
        Real.sqrt (Var[Dx; disorderLaw] * Var[Uy; disorderLaw]) +
        Real.sqrt (Var[Ux; disorderLaw] * Var[Dy; disorderLaw]) +
        Real.sqrt (Var[Dx; disorderLaw] * Var[Dy; disorderLaw]) := hcovadd
    _ ≤ Real.log (1 + C * MomentBounds.truncatedGreen n (sy - sx)) +
        2 * E + 2 * Real.sqrt S + v := by
      rw [hcovRev]
      linarith [hFxFy, hroot1, hroot2, hroot3]

private theorem one_add_mul_absorb (A c u : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hu : 0 ≤ u) :
    1 + A * (c + 2 * u) ≤ (1 + A * c + 2 * A) * (1 + u) := by
  have hcoef : 0 ≤ 1 + A * c := by nlinarith [mul_nonneg hA hc]
  nlinarith [mul_nonneg hcoef hu, mul_nonneg hA hu]

/-- Constant used to absorb the lattice Green logarithm into the continuum distance scale. -/
def greenAbsorbConstant (S B K : ℝ) : ℝ :=
  1 + S * B * (1 + Real.log (1 + 16 * K) + 2 * Real.log 2) + 2 * S * B

/-- Converts the lattice truncated Green estimate to the continuum logarithmic distance bound. -/
theorem log_green_to_plane_bound (S B K : ℝ) (hS : 0 ≤ S) (hB : 0 < B)
    (hK : 0 < K) {N n : ℕ} (hN : 0 < N) (hn : (n : ℝ) ≤ K * N)
    {x y : Plane} (hxy : x ≠ y)
    (hgreen : MomentBounds.truncatedGreen n
        (latticePoint N y - latticePoint N x) ≤
      B * (1 + Real.log (1 + (n : ℝ) /
        (1 + ‖siteToPlane (latticePoint N y - latticePoint N x)‖ ^ 2)))) :
    1 ≤ greenAbsorbConstant S B K ∧
      Real.log (1 + S * MomentBounds.truncatedGreen n
        (latticePoint N y - latticePoint N x)) ≤
        Real.log (greenAbsorbConstant S B K) +
          Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
  let d := ‖x - y‖
  let u := max 0 (Real.log d⁻¹)
  let R := ‖siteToPlane (latticePoint N y - latticePoint N x)‖
  let K₀ := 16 * K
  let c₀ := 1 + Real.log (1 + K₀) + 2 * Real.log 2
  let A := S * B
  let D := greenAbsorbConstant S B K
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hR : 0 ≤ R := norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg hS hB.le
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hc₀ : 0 ≤ c₀ := by
    dsimp [c₀]
    have hlogK : 0 ≤ Real.log (1 + K₀) := Real.log_nonneg (by linarith)
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hDform : D = 1 + A * c₀ + 2 * A := by
    dsimp [D, greenAbsorbConstant, A, c₀]
    ring
  have hD : 1 ≤ D := by
    rw [hDform]
    nlinarith [mul_nonneg hA hc₀]
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hdistSq : 0 < d ^ 2 := pow_pos hd _
  have hscale : 0 < Real.sqrt ((N : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  let a := Real.sqrt ((N : ℝ) / 2)
  have happroxX : dist x (a⁻¹ • siteToPlane (latticePoint N x)) ≤ a⁻¹ := by
    dsimp [a]
    simpa only [dist_eq_norm] using norm_sub_latticePoint_le hN x
  have happroxY : dist y (a⁻¹ • siteToPlane (latticePoint N y)) ≤ a⁻¹ := by
    dsimp [a]
    simpa only [dist_eq_norm] using norm_sub_latticePoint_le hN y
  have hmid : dist (a⁻¹ • siteToPlane (latticePoint N x))
      (a⁻¹ • siteToPlane (latticePoint N y)) = a⁻¹ * R := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hscale)]
    congr 1
    have hplane : siteToPlane (latticePoint N y - latticePoint N x) =
        siteToPlane (latticePoint N y) - siteToPlane (latticePoint N x) := by
      ext i
      simp [siteToPlane]
    have hneg : siteToPlane (latticePoint N x) - siteToPlane (latticePoint N y) =
        -siteToPlane (latticePoint N y - latticePoint N x) := by
      rw [hplane]
      abel
    rw [hneg, norm_neg]
  have happroxY' : dist (a⁻¹ • siteToPlane (latticePoint N y)) y ≤ a⁻¹ := by
    rw [dist_comm]
    exact happroxY
  have htri : dist x y ≤ a⁻¹ * (R + 2) := by
    calc
      dist x y ≤ dist x (a⁻¹ • siteToPlane (latticePoint N x)) +
          dist (a⁻¹ • siteToPlane (latticePoint N x)) y := dist_triangle _ _ _
      _ ≤ a⁻¹ + (dist (a⁻¹ • siteToPlane (latticePoint N x))
          (a⁻¹ • siteToPlane (latticePoint N y)) +
          dist (a⁻¹ • siteToPlane (latticePoint N y)) y) := by
        apply add_le_add
        · exact happroxX
        · exact dist_triangle _ _ _
      _ ≤ a⁻¹ + (a⁻¹ * R + a⁻¹) := by
        apply add_le_add
        · rfl
        · exact add_le_add hmid.le happroxY'
      _ = a⁻¹ * (R + 2) := by ring
  have hscaled : a * d ≤ R + 2 := by
    have htri' : d ≤ a⁻¹ * (R + 2) := by
      simpa [d, dist_eq_norm] using htri
    calc
      _ ≤ Real.sqrt ((N : ℝ) / 2) *
          ((Real.sqrt ((N : ℝ) / 2))⁻¹ * (R + 2)) :=
            mul_le_mul_of_nonneg_left htri' (le_of_lt hscale)
      _ = R + 2 := by field_simp [ne_of_gt hscale]
  have hscaledSq : (a * d) ^ 2 ≤ (R + 2) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hscale.le (norm_nonneg _)) (by positivity)).2 hscaled
  have hRbound : (R + 2) ^ 2 ≤ 8 * (1 + R ^ 2) := by
    nlinarith [sq_nonneg (R - 2)]
  have hgeom : (N : ℝ) * d ^ 2 ≤ 16 * (1 + R ^ 2) := by
    have ha2 : a ^ 2 = (N : ℝ) / 2 := by
      simpa [a] using Real.sq_sqrt (show 0 ≤ (N : ℝ) / 2 by positivity)
    have hscaledSq' : ((N : ℝ) / 2) * d ^ 2 ≤ (R + 2) ^ 2 := by
      calc
        _ = (a * d) ^ 2 := by rw [mul_pow, ha2]
        _ ≤ _ := hscaledSq
    nlinarith [hscaledSq', hRbound]
  have hfrac : (n : ℝ) / (1 + R ^ 2) ≤ K₀ / d ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hdistSq]
    dsimp [K₀]
    nlinarith [mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ d ^ 2), hgeom]
  have hlogfrac : Real.log (1 + (n : ℝ) / (1 + R ^ 2)) ≤
      Real.log (1 + K₀ / d ^ 2) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hdInv : 0 < d⁻¹ := inv_pos.mpr hd
  have hlogInv : Real.log (1 + d⁻¹) ≤ Real.log 2 + u := by
    by_cases ha : d⁻¹ ≤ 1
    · have harg : 1 + d⁻¹ ≤ 2 := by linarith
      have hl := Real.log_le_log (by positivity) harg
      have hu : 0 ≤ u := le_max_left _ _
      have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      dsimp [u]
      linarith
    · have ha' : 1 < d⁻¹ := lt_of_not_ge ha
      have harg : 1 + d⁻¹ ≤ 2 * d⁻¹ := by linarith
      have hl := Real.log_le_log (by positivity) harg
      rw [Real.log_mul (by norm_num) hdInv.ne'] at hl
      have hu : Real.log d⁻¹ ≤ u := le_max_right _ _
      dsimp [u]
      linarith
  have hpoly : 1 + K₀ / d ^ 2 ≤ (1 + K₀) * (1 + d⁻¹) ^ 2 := by
    have hclear : d ^ 2 + K₀ ≤ (1 + K₀) * (d + 1) ^ 2 := by
      nlinarith [sq_nonneg d, mul_nonneg hK₀.le (sq_nonneg d)]
    have hright : d ^ 2 * ((1 + K₀) * (1 + d⁻¹) ^ 2) =
        (1 + K₀) * (d + 1) ^ 2 := by
      field_simp [ne_of_gt hd]
    have hleft : d ^ 2 * (1 + K₀ / d ^ 2) = d ^ 2 + K₀ := by
      field_simp [ne_of_gt hd]
    rw [← hleft, ← hright] at hclear
    exact (mul_le_mul_iff_of_pos_left hdistSq).mp hclear
  have hlogpoly : Real.log (1 + K₀ / d ^ 2) ≤
      Real.log (1 + K₀) + 2 * Real.log (1 + d⁻¹) := by
    calc
      _ ≤ Real.log ((1 + K₀) * (1 + d⁻¹) ^ 2) :=
        Real.log_le_log (by positivity) hpoly
      _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        norm_num
  have hW : 1 + Real.log (1 + (n : ℝ) / (1 + R ^ 2)) ≤ c₀ + 2 * u := by
    dsimp [c₀]
    linarith [hlogfrac, hlogpoly, hlogInv]
  have hgreen0 : 0 ≤ MomentBounds.truncatedGreen n
      (latticePoint N y - latticePoint N x) := by
    rw [MomentBounds.truncatedGreen]
    exact Finset.sum_nonneg fun r hr => Polymer.kernel_nonneg (2 * r) _
  have hgreenArg : 1 + S * MomentBounds.truncatedGreen n
      (latticePoint N y - latticePoint N x) ≤ D * (1 + u) := by
    calc
      _ ≤ 1 + A * (c₀ + 2 * u) := by
        have hW' := hW
        dsimp [R] at hW'
        calc
          _ ≤ 1 + S * (B * (1 + Real.log (1 + (n : ℝ) /
              (1 + ‖siteToPlane (latticePoint N y - latticePoint N x)‖ ^ 2)))) := by
            simpa [add_comm] using
              (add_le_add_left (mul_le_mul_of_nonneg_left hgreen hS) 1)
          _ = 1 + A * (1 + Real.log (1 + (n : ℝ) /
              (1 + ‖siteToPlane (latticePoint N y - latticePoint N x)‖ ^ 2))) := by
            dsimp [A]
            ring
          _ ≤ 1 + A * (c₀ + 2 * u) := by
            simpa [add_comm] using
              (add_le_add_left (mul_le_mul_of_nonneg_left hW' hA) 1)
      _ ≤ D * (1 + u) := by
        rw [hDform]
        have hu : 0 ≤ u := le_max_left _ _
        exact one_add_mul_absorb A c₀ u hA hc₀ hu
  have hlogFinal : Real.log (1 + S * MomentBounds.truncatedGreen n
      (latticePoint N y - latticePoint N x)) ≤ Real.log D + Real.log (1 + u) := by
    calc
      _ ≤ Real.log (D * (1 + u)) := Real.log_le_log (by positivity) hgreenArg
      _ = _ := Real.log_mul hDpos.ne' (by positivity)
  constructor
  · exact hD
  · exact hlogFinal

/-- The flat lattice fields have nonnegative covariance, since their spatial masses are finite
positive path sums with nonnegative coefficients. -/
theorem covariance_kpzLattice_flat_nonneg (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (x y : Plane) (htime : Even (evenCeil ((N : ℝ) * t))) :
    0 ≤ covariance (kpzLattice ϑ N t 0 x) (kpzLattice ϑ N t 0 y) disorderLaw := by
  let n : ℕ := evenCeil ((N : ℝ) * t)
  let β : ℝ := criticalBeta ϑ N
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; exact Real.sqrt_nonneg _
  let cx : (Fin n → Fin 4) × (Fin n → Fin 4) → ℝ := flatMassPathCoeff
  let wx : (Fin n → Fin 4) → Site := flatMassPathStart (latticePoint N x)
  let wy : (Fin n → Fin 4) → Site := flatMassPathStart (latticePoint N y)
  have hcx (p : (Fin n → Fin 4) × (Fin n → Fin 4)) : 0 ≤ cx p := by
    dsimp [cx, flatMassPathCoeff]
    split_ifs <;> positivity
  have hp (w : (Fin n → Fin 4) → Site) :
      ∃ p : (Fin n → Fin 4) × (Fin n → Fin 4), 0 < cx p := by
    refine ⟨(fun _ : Fin n => 0, fun _ : Fin n => 0), ?_⟩
    dsimp [cx, flatMassPathCoeff]
    simp only [ite_true]
    positivity
  have hxmass (ω : Disorder) :
      (∫ z : Plane, rescaledP2P ϑ N 0 t (z, x) ω) =
        PolymerCalculus.finitePathMass β 0 n wx cx ω := by
    simpa only [n, β, wx, cx] using
      integral_rescaledP2P_flat_eq_finitePathMass ϑ hN t x ω (by simpa [n] using htime)
  have hymass (ω : Disorder) :
      (∫ z : Plane, rescaledP2P ϑ N 0 t (z, y) ω) =
        PolymerCalculus.finitePathMass β 0 n wy cx ω := by
    simpa only [n, β, wy, cx] using
      integral_rescaledP2P_flat_eq_finitePathMass ϑ hN t y ω (by simpa [n] using htime)
  have hXpos (ω : Disorder) : 0 < PolymerCalculus.finitePathMass β 0 n wx cx ω :=
    PolymerCalculus.finitePathMass_pos β 0 n wx hcx (hp wx) ω
  have hYpos (ω : Disorder) : 0 < PolymerCalculus.finitePathMass β 0 n wy cx ω :=
    PolymerCalculus.finitePathMass_pos β 0 n wy hcx (hp wy) ω
  have hXmem : MemLp
      (fun ω => Real.log (PolymerCalculus.finitePathMass β 0 n wx cx ω)) 2 disorderLaw :=
    PolymerCalculus.memLp_log_finitePathMass β 0 n wx hcx (hp wx) 2
  have hYmem : MemLp
      (fun ω => Real.log (PolymerCalculus.finitePathMass β 0 n wy cx ω)) 2 disorderLaw :=
    PolymerCalculus.memLp_log_finitePathMass β 0 n wy hcx (hp wy) 2
  have hX : (fun ω => kpzLattice ϑ N t 0 x ω) =
      fun ω => Real.log (PolymerCalculus.finitePathMass β 0 n wx cx ω) -
        kpzLatticeCentring ϑ N t := by
    funext ω
    unfold kpzLattice
    have hzero (z : Plane) : Real.exp ((0 : BoundedContinuousFunction Plane ℝ) z) = 1 := by simp
    simp_rw [hzero, one_mul]
    rw [hxmass ω]
  have hY : (fun ω => kpzLattice ϑ N t 0 y ω) =
      fun ω => Real.log (PolymerCalculus.finitePathMass β 0 n wy cx ω) -
        kpzLatticeCentring ϑ N t := by
    funext ω
    unfold kpzLattice
    have hzero (z : Plane) : Real.exp ((0 : BoundedContinuousFunction Plane ℝ) z) = 1 := by simp
    simp_rw [hzero, one_mul]
    rw [hymass ω]
  change 0 ≤ covariance (fun ω => kpzLattice ϑ N t 0 x ω)
    (fun ω => kpzLattice ϑ N t 0 y ω) disorderLaw
  rw [hX, hY]
  rw [covariance_sub_const_left
        (hXmem.integrable (by norm_num)) (kpzLatticeCentring ϑ N t),
      covariance_sub_const_right
        (hYmem.integrable (by norm_num)) (kpzLatticeCentring ϑ N t)]
  exact PolymerCalculus.covariance_log_finitePathMass_nonneg hβ hβ
    0 n 0 n wx wy hcx (hp wx) hcx (hp wy)

/-- The forward flat lattice field has a logarithmic covariance bound at every positive
macroscopic time, from the even-horizon defect estimate. The fields are in `L²` by
`memLp_log_pointToPlane` with `kpzLattice_flat_log_eq_timeReversedPlane`. -/
theorem kpzLattice_flat_covariance_le_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc t₀ t₁, ∀ x y : Plane, x ≠ y →
      0 ≤ covariance (kpzLattice ϑ N t 0 x) (kpzLattice ϑ N t 0 y) disorderLaw ∧
      covariance (kpzLattice ϑ N t 0 x) (kpzLattice ϑ N t 0 y) disorderLaw ≤
        C * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) := by
  let Aθ := |ϑ| + 1
  let T₀ := t₀ / 2
  let T₁ := max (t₀ / 2 + 1) (t₁ + 1)
  let d₀ := Real.log (1 + 1 / (T₁ + 1))
  have hθrange : ϑ ∈ Set.Icc (-Aθ) Aθ := by
    constructor <;> dsimp [Aθ] <;> linarith [neg_abs_le ϑ, le_abs_self ϑ]
  have hT₀pos : 0 < T₀ := by dsimp [T₀]; linarith
  have hT₁pos : 0 < T₁ := by
    dsimp [T₁]
    have : 0 < t₀ / 2 + 1 := by linarith
    exact lt_of_lt_of_le this (le_max_left _ _)
  have hT₀T₁ : T₀ < T₁ := by
    dsimp [T₀, T₁]
    linarith [le_max_left (t₀ / 2 + 1) (t₁ + 1)]
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    apply Real.log_pos
    have : 0 < 1 / (T₁ + 1) := by positivity
    linarith
  obtain ⟨hVDfirst, _⟩ := hVD Aθ
  obtain ⟨CVD, hVDlarge⟩ := hVDfirst T₀ T₁ hT₀pos hT₀T₁
  obtain ⟨Csm, hCsmpos, hsmLarge⟩ := Renewal.secondMoment_log_bound_horizon ϑ T₁
  obtain ⟨B, hBpos, hgreenBound⟩ := truncatedGreen_le_log_bound
  let S := Csm / d₀
  have hSpos : 0 < S := by dsimp [S]; exact div_pos hCsmpos hd₀
  let E₀ := CVD + 1 + (15 / 8) + Real.sqrt ((5 / 2) * S)
  let D₀ := greenAbsorbConstant S B T₁
  let Cfinal := Real.log D₀ + 2 * |E₀| + 2 * Real.sqrt S + 2
  have hD₀ : 1 ≤ D₀ := by
    have hlog1 : 0 ≤ Real.log (1 + 16 * T₁) :=
      Real.log_nonneg (by nlinarith [hT₁pos])
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hSB : 0 ≤ S * B := mul_nonneg hSpos.le hBpos.le
    dsimp [D₀, greenAbsorbConstant]
    nlinarith [mul_nonneg hSB (show 0 ≤ 1 + Real.log (1 + 16 * T₁) +
      2 * Real.log 2 by linarith)]
  have hCfinalge1 : 1 ≤ Cfinal := by
    have hlogD : 0 ≤ Real.log D₀ := Real.log_nonneg hD₀
    have hsqrt : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    dsimp [Cfinal]
    nlinarith [abs_nonneg E₀]
  have hCbase (σ : ℝ) (hσ : σ ≤ 1) :
      Real.log D₀ + 2 * E₀ + 2 * Real.sqrt S + σ ≤ Cfinal := by
    dsimp [Cfinal]
    have hE : E₀ ≤ |E₀| := le_abs_self _
    linarith
  refine ⟨Cfinal, ?_⟩
  have hSigmaMoment (N L : ℕ) (hN : 0 < N)
      (hL : (L : ℝ) ≤ T₁ * N) (hsmN :
        ∀ L : ℕ, (L : ℝ) ≤ T₁ * N →
          criticalSigmaSq ϑ N *
            ∫ ω, pointToPlane (criticalBeta ϑ N) 0 L 0 ω ^ 2 ∂disorderLaw ≤
              Csm / Real.log (1 + (N : ℝ) / (L + 1))) :
      criticalSigmaSq ϑ N *
          ∫ ω, pointToPlane (criticalBeta ϑ N) 0 L 0 ω ^ 2 ∂disorderLaw ≤ S := by
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hdenom : (L : ℝ) + 1 ≤ (T₁ + 1) * N := by nlinarith [hL, hNreal]
    have hratio : 1 / (T₁ + 1) ≤ (N : ℝ) / (L + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hdenom]
    have hlogdenom : d₀ ≤ Real.log (1 + (N : ℝ) / (L + 1)) := by
      dsimp [d₀]
      apply Real.log_le_log (by positivity)
      linarith
    calc
      _ ≤ Csm / Real.log (1 + (N : ℝ) / (L + 1)) := hsmN L hL
      _ ≤ Csm / d₀ := div_le_div_of_nonneg_left hCsmpos.le hd₀ hlogdenom
      _ = S := by rfl
  have hsigmaSmall : ∀ᶠ N : ℕ in atTop, criticalSigmaSq ϑ N < 1 :=
    (Renewal.tendsto_sigma_zero ϑ).eventually (Iio_mem_nhds (by norm_num))
  have hsigmaPos : ∀ᶠ N : ℕ in atTop, 0 < criticalSigmaSq ϑ N :=
    Renewal.criticalSigmaSq_eventually_pos ϑ
  filter_upwards [eventually_ge_atTop 2, hVDlarge, hsmLarge,
      criticalBeta_spec ϑ, hsigmaSmall, hsigmaPos] with N hN2 hVDN hsmN hspec hsigmaSmallN hsigmaPosN
  have hNpos : 0 < N := by omega
  have hNrealTwo : 2 ≤ (N : ℝ) := by exact_mod_cast hN2
  have hσeq : 1 + criticalSigmaSq ϑ N = Real.exp (criticalBeta ϑ N ^ 2) := by
    linarith [hspec]
  have hσnonneg : 0 ≤ criticalSigmaSq ϑ N := hsigmaPosN.le
  have hσle1 : criticalSigmaSq ϑ N ≤ 1 := hsigmaSmallN.le
  have hβsq : criticalBeta ϑ N ^ 2 ≤ criticalSigmaSq ϑ N := by
    have hlog := Real.log_le_sub_one_of_pos
      (show 0 < 1 + criticalSigmaSq ϑ N by linarith [hsigmaPosN])
    have hlogeq : Real.log (1 + criticalSigmaSq ϑ N) = criticalBeta ϑ N ^ 2 := by
      rw [hσeq, Real.log_exp]
    linarith
  have hβpos : 0 ≤ criticalBeta ϑ N := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hβ4 : criticalBeta ϑ N ^ 4 ≤ criticalSigmaSq ϑ N := by
    have hβ20 : 0 ≤ criticalBeta ϑ N ^ 2 := sq_nonneg _
    have hβ2le1 : criticalBeta ϑ N ^ 2 ≤ 1 := hβsq.trans hσle1
    have hmul := mul_nonneg hβ20 (sub_nonneg.mpr hβ2le1)
    nlinarith [hmul]
  have hqbound : criticalBeta ϑ N ^ 2 + criticalBeta ϑ N ^ 4 / 4 ≤
      (5 / 4) * criticalSigmaSq ϑ N := by nlinarith [hβsq, hβ4]
  have hT₁ge : t₁ + 1 ≤ T₁ := le_max_right _ _
  intro t ht x y hxy
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht.1
  let m := evenCeil ((N : ℝ) * t)
  let n := m - 1
  have hmEven : Even m := by
    refine ⟨⌈((N : ℝ) * t) / 2⌉₊, ?_⟩
    simp [m, evenCeil, two_mul]
  have hmrealLower : (N : ℝ) * t ≤ (m : ℝ) := by
    dsimp [m]
    exact le_evenCeil _
  have hmrealUpper : (m : ℝ) ≤ T₁ * N := by
    have hceil := Critical2DKPZ.evenCeil_lt_add_two
      (mul_nonneg (Nat.cast_nonneg N) htpos.le)
    have hNt : (N : ℝ) * t ≤ (N : ℝ) * t₁ :=
      mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg N)
    have hrough : (m : ℝ) < (N : ℝ) * t + 2 := by simpa [m] using hceil
    have hNatUpper : (N : ℝ) * t₁ + 2 ≤ (t₁ + 1) * N := by nlinarith [hT₁ge, hNrealTwo]
    have hTUpper : (t₁ + 1) * N ≤ T₁ * N :=
      mul_le_mul_of_nonneg_right hT₁ge (Nat.cast_nonneg N)
    nlinarith
  have hm1 : 1 ≤ m := by
    have hmpos : 0 < (m : ℝ) := by
      have hlow := hmrealLower
      have ht0N : 0 < (N : ℝ) * t := mul_pos (by exact_mod_cast hNpos) htpos
      linarith
    have hmposNat : 0 < m := by exact_mod_cast hmpos
    omega
  have hn : n + 1 = m := by dsimp [n]; omega
  have hnle : (n : ℝ) ≤ T₁ * N := by
    have hnNat : n ≤ m := by dsimp [n]; omega
    exact (Nat.cast_le.mpr hnNat).trans hmrealUpper
  have hT₀m : T₀ * N ≤ (m : ℝ) := by
    have hlow := hmrealLower
    have htime := mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg N)
    dsimp [T₀]
    linarith
  have hσMomentBound (L : ℕ) (hL : (L : ℝ) ≤ T₁ * N) :
      criticalSigmaSq ϑ N *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 L 0 ω ^ 2 ∂disorderLaw ≤ S := by
    exact hSigmaMoment N L hNpos hL hsmN
  have hM : ∀ z : Site,
      ∫ ω, pointToPlane (criticalBeta ϑ N) 0 n z ω ^ 2 ∂disorderLaw ≤
        S / criticalSigmaSq ϑ N := by
    intro z
    rw [integral_sq_pointToPlane_eq_zero]
    apply (le_div_iff₀ hsigmaPosN).2
    simpa [mul_comm] using hσMomentBound n hnle
  have hMpos : 0 < S / criticalSigmaSq ϑ N :=
    div_pos hSpos hsigmaPosN
  have hprod : criticalSigmaSq ϑ N * (S / criticalSigmaSq ϑ N) ≤ S := by
    rw [mul_div_cancel₀ S hsigmaPosN.ne']
  have hEvenDef (z : Site) :
      gaussianityDefect disorderLaw
        (fun ω => Real.log (pointToPlane (criticalBeta ϑ N) 0 m z ω)) ≤ CVD := by
    have hvd := hVDN ϑ hθrange z 0 m (by norm_num) hmEven (by omega) hT₀m hmrealUpper
    have hvd' := hvd.2.1.trans hvd.2.2
    simpa only [smoothedP2Plane_zero_eq_pointToPlane] using hvd'
  have hOddDef (z : Site) :
      gaussianityDefect disorderLaw
        (fun ω => Real.log (pointToPlane (criticalBeta ϑ N) 0 n z ω)) ≤
          E₀ := by
    have hMsite := integral_sq_pointToPlane_pos (criticalBeta ϑ N) 0 n z
    have hEvenDef' : gaussianityDefect disorderLaw
        (fun ω => Real.log (pointToPlane (criticalBeta ϑ N) 0 (n + 1) z ω)) ≤ CVD := by
      rw [hn]
      exact hEvenDef z
    have htransfer := gaussianityDefect_pointToPlane_le_of_succ
      (criticalBeta ϑ N) n z CVD hMsite hEvenDef'
    have hI : ∫ ω, pointToPlane (criticalBeta ϑ N) 0 n z ω ^ 2 ∂disorderLaw ≤
        S / criticalSigmaSq ϑ N := hM z
    have hq0 : 0 ≤ criticalBeta ϑ N ^ 2 + criticalBeta ϑ N ^ 4 / 4 := by positivity
    have hIq : 2 * (∫ ω, pointToPlane (criticalBeta ϑ N) 0 n z ω ^ 2 ∂disorderLaw) *
        (criticalBeta ϑ N ^ 2 + criticalBeta ϑ N ^ 4 / 4) ≤ (5 / 2) * S := by
      have hI0 : 0 ≤ ∫ ω, pointToPlane (criticalBeta ϑ N) 0 n z ω ^ 2 ∂disorderLaw :=
        integral_nonneg fun ω => sq_nonneg _
      calc
        _ ≤ 2 * (S / criticalSigmaSq ϑ N) * ((5 / 4) * criticalSigmaSq ϑ N) := by
          gcongr
        _ = (5 / 2) * S := by
          field_simp [hsigmaPosN.ne']
          ring
    have hroot : Real.sqrt (2 *
        (∫ ω, pointToPlane (criticalBeta ϑ N) 0 n z ω ^ 2 ∂disorderLaw) *
        (criticalBeta ϑ N ^ 2 + criticalBeta ϑ N ^ 4 / 4)) ≤ Real.sqrt ((5 / 2) * S) :=
      Real.sqrt_le_sqrt hIq
    have hthree : (3 / 2) *
        (criticalBeta ϑ N ^ 2 + criticalBeta ϑ N ^ 4 / 4) ≤ 15 / 8 := by
      have := mul_le_mul_of_nonneg_left hqbound (by norm_num : (0 : ℝ) ≤ 3 / 2)
      nlinarith [hσle1]
    dsimp [E₀]
    linarith [htransfer, hroot, hthree]
  have hcoeff : ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq (criticalBeta ϑ N) *
        (∫ ω, pointToPlane (criticalBeta ϑ N) 0 (n - r) 0 ω ^ 2 ∂disorderLaw) ≤ S := by
    intro r hr
    have hL : ((n - r : ℕ) : ℝ) ≤ T₁ * N := by
      have hNat : n - r ≤ n := Nat.sub_le _ _
      exact (Nat.cast_le.mpr hNat).trans hnle
    have hmoment := hσMomentBound (n - r) hL
    simpa [Polymer.sigmaSq, hspec] using hmoment
  have hDx := hOddDef (latticePoint N x)
  have hDy := hOddDef (latticePoint N y)
  have hcore := covariance_kpzLattice_flat_le_of_data ϑ hNpos t x y m rfl hm1
    (S / criticalSigmaSq ϑ N) S S
    E₀ (criticalSigmaSq ϑ N) hβpos hβsq hMpos hprod hM hcoeff hDx hDy
  have hGreenPlane := hgreenBound n (latticePoint N y - latticePoint N x)
  obtain ⟨_, hlogGreen⟩ := log_green_to_plane_bound S B T₁ hSpos.le hBpos
    hT₁pos hNpos hnle hxy hGreenPlane
  have hLnonneg : 0 ≤ Real.log
      (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
    apply Real.log_nonneg
    linarith [le_max_left (0 : ℝ) (Real.log ‖x - y‖⁻¹)]
  have hcovNonneg := covariance_kpzLattice_flat_nonneg ϑ hNpos t x y hmEven
  have hcovUpper : covariance (kpzLattice ϑ N t 0 x)
      (kpzLattice ϑ N t 0 y) disorderLaw ≤
        Cfinal * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) := by
    have hgreenShift :
        Real.log (1 + S * MomentBounds.truncatedGreen n
            (latticePoint N y - latticePoint N x)) +
          (2 * E₀ + 2 * Real.sqrt S + criticalSigmaSq ϑ N) ≤
          (Real.log (greenAbsorbConstant S B T₁) +
            Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) +
          (2 * E₀ + 2 * Real.sqrt S + criticalSigmaSq ϑ N) :=
      add_le_add hlogGreen le_rfl
    have hupper : covariance (kpzLattice ϑ N t 0 x)
        (kpzLattice ϑ N t 0 y) disorderLaw ≤
          (Real.log (greenAbsorbConstant S B T₁) +
            Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) +
              (2 * E₀ + 2 * Real.sqrt S + criticalSigmaSq ϑ N) := by
      calc
        _ ≤ Real.log (1 + S * MomentBounds.truncatedGreen n
              (latticePoint N y - latticePoint N x)) +
                (2 * E₀ + 2 * Real.sqrt S + criticalSigmaSq ϑ N) := by
          simpa only [add_assoc] using hcore
        _ ≤ _ := hgreenShift
    have hbound : covariance (kpzLattice ϑ N t 0 x)
        (kpzLattice ϑ N t 0 y) disorderLaw ≤
        Cfinal + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
      have hbase := hCbase (criticalSigmaSq ϑ N) hσle1
      linarith [hupper, hbase]
    calc
      _ ≤ Cfinal + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := hbound
      _ ≤ Cfinal + Cfinal * Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
        apply add_le_add le_rfl
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hCfinalge1 hLnonneg)
      _ = _ := by ring
  exact ⟨hcovNonneg, hcovUpper⟩

end Critical2DKPZ.LocalSobolev

end
