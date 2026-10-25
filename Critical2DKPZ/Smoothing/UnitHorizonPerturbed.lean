/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.PolymerLogMomentBounds
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.Smoothing.DiagonalClockPerturbation
public import Critical2DKPZ.Smoothing.WidthClockPerturbation
public import Critical2DKPZ.Smoothing.ClockScaleMoments
public import Critical2DKPZ.Smoothing.WidthCollisionControl
import Critical2DKPZ.Smoothing.UnitHorizonBounds
import Mathlib.Tactic

/-! # Unit-horizon bounds with perturbed widths -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BoundedContinuousFunction Topology

namespace Critical2DKPZ.Smoothing

/-- `latticeSmoothingError_perturb_le`, as a proposition. For every `A, H, M₁, M₂`, `δ ∈ (0, 1)`
and `ε > 0`, for all large even `M`, uniformly in `ϑ ∈ [-A, A]`, in even `j, k` within `6` of
`evenCeil (δ M)`, in `h₀` with `‖h₀‖ ≤ H` and in test functions `φ` with `L¹` norm `≤ M₁` and sup
norm `≤ M₂`, the lattice smoothing error at `(k, j)` is within `ε` in `L²` of that at the
diagonal `(evenCeil (δ M), evenCeil (δ M))`. -/
def LatticeSmoothingPerturbBound : Prop := ∀ (A H M₁ M₂ : ℝ) (δ : ℝ), 0 < δ → δ < 1 →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, Even M → ∀ ϑ ∈ Set.Icc (-A) A, ∀ j k : ℕ, Even j → Even k →
      (j : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ j + 6 →
      (k : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ k + 6 →
      ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H → ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ → (∫ x, |φ x| ≤ M₁) →
        (∀ x, |φ x| ≤ M₂) →
        eLpNorm (fun ω => latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ φ ω -
            latticeSmoothingError (criticalBeta ϑ M) M M (evenCeil (δ * M)) (evenCeil (δ * M)) h₀ φ ω)
          2 disorderLaw ≤ ENNReal.ofReal ε

private noncomputable def diagonalLogShiftBound (H F Q Qflat D : ℝ) : ℝ :=
  logHolderConstant * (Real.sqrt Q) ^ ((1 : ℝ) / 3) *
      ((1 + Q) ^ ((1 : ℝ) / 3) + 1) +
    logHolderConstant * (Real.sqrt (F ^ 2 * D)) ^ ((1 : ℝ) / 3) *
      ((Real.exp H * (2 * Qflat + 2 * D)) ^ ((1 : ℝ) / 3) +
        (Real.exp H * Qflat) ^ ((1 : ℝ) / 3))

private theorem diagonalLogShiftBound_nonneg (H F Q Qflat D : ℝ)
    (hQ : 0 ≤ Q) (hQflat : 0 ≤ Qflat)
    (hD : 0 ≤ D) : 0 ≤ diagonalLogShiftBound H F Q Qflat D := by
  dsimp [diagonalLogShiftBound]
  have hp1 : 0 ≤ (Real.sqrt Q) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hp2 : 0 ≤ (1 + Q) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 + Q) _
  have hp3 : 0 ≤ (Real.sqrt (F ^ 2 * D)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hp4 : 0 ≤ (Real.exp H * (2 * Qflat + 2 * D)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (by positivity) _
  have hp5 : 0 ≤ (Real.exp H * Qflat) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (by positivity) _
  have hC : 0 ≤ logHolderConstant := logHolderConstant_pos.le
  positivity

private theorem diagonalLogShiftBound_continuousAt_zero (H F Qflat : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ =>
      diagonalLogShiftBound H F p.1 Qflat p.2) (0, 0) := by
  dsimp [diagonalLogShiftBound]
  fun_prop (disch := norm_num)

private theorem diagonalLogShiftBound_tendsto_zero (H F Qflat Cq Cd : ℝ) :
    Tendsto (fun M : ℕ => diagonalLogShiftBound H F
      (Cq * (M : ℝ)⁻¹ * (Real.log (M : ℝ))⁻¹) Qflat
      (Cd * (Real.log (M : ℝ))⁻¹)) atTop (𝓝 0) := by
  let q : ℕ → ℝ := fun M => Cq * (M : ℝ)⁻¹ * (Real.log (M : ℝ))⁻¹
  let d : ℕ → ℝ := fun M => Cd * (Real.log (M : ℝ))⁻¹
  have hM : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun M : ℕ => (Real.log (M : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hq : Tendsto q atTop (𝓝 0) := by
    dsimp [q]
    have hc : Tendsto (fun _ : ℕ => Cq) atTop (𝓝 Cq) := tendsto_const_nhds
    simpa [mul_assoc] using hc.mul (hM.mul hlog)
  have hd : Tendsto d atTop (𝓝 0) := by
    dsimp [d]
    simpa using tendsto_const_nhds.mul hlog
  have hpair : Tendsto (fun M : ℕ => (q M, d M)) atTop (𝓝 (0, 0)) :=
    hq.prodMk_nhds hd
  have hcont := (diagonalLogShiftBound_continuousAt_zero H F Qflat).tendsto.comp hpair
  have hzero : diagonalLogShiftBound H F 0 Qflat 0 = 0 := by
    norm_num [diagonalLogShiftBound]
  change Tendsto (fun M : ℕ => diagonalLogShiftBound H F
    (q M) Qflat (d M)) atTop
      (𝓝 (diagonalLogShiftBound H F 0 Qflat 0)) at hcont
  rw [hzero] at hcont
  simpa [q, d] using hcont

private theorem one_add_pow_six_sub_one_le (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ 6 - 1 ≤ 6 * x * (1 + x) ^ 5 := by
  have hbase : 1 ≤ 1 + x := by linarith
  have hpow0 : (1 + x) ^ 0 ≤ (1 + x) ^ 5 := by
    exact pow_le_pow_right₀ hbase (by omega)
  have hpow1 : (1 + x) ^ 1 ≤ (1 + x) ^ 5 := by
    exact pow_le_pow_right₀ hbase (by omega)
  have hpow2 : (1 + x) ^ 2 ≤ (1 + x) ^ 5 := by
    exact pow_le_pow_right₀ hbase (by omega)
  have hpow3 : (1 + x) ^ 3 ≤ (1 + x) ^ 5 := by
    exact pow_le_pow_right₀ hbase (by omega)
  have hpow4 : (1 + x) ^ 4 ≤ (1 + x) ^ 5 := by
    exact pow_le_pow_right₀ hbase (by omega)
  have hgeom : (1 + x) ^ 6 - 1 = x *
      ((1 + x) ^ 5 + (1 + x) ^ 4 + (1 + x) ^ 3 +
        (1 + x) ^ 2 + (1 + x) + 1) := by ring
  have hsum :
      (1 + x) ^ 5 + (1 + x) ^ 4 + (1 + x) ^ 3 +
          (1 + x) ^ 2 + (1 + x) + 1 ≤
        (1 + x) ^ 5 + (1 + x) ^ 5 + (1 + x) ^ 5 +
          (1 + x) ^ 5 + (1 + x) ^ 5 + (1 + x) ^ 5 :=
    add_le_add
      (add_le_add
        (add_le_add (add_le_add (add_le_add le_rfl hpow4) hpow3) hpow2)
        ((pow_one (1 + x)).symm.le.trans hpow1))
      ((pow_zero (1 + x)).symm.le.trans hpow0)
  calc
    _ = x * ((1 + x) ^ 5 + (1 + x) ^ 4 + (1 + x) ^ 3 +
        (1 + x) ^ 2 + (1 + x) + 1) := hgeom
    _ ≤ x * ((1 + x) ^ 5 + (1 + x) ^ 5 + (1 + x) ^ 5 +
        (1 + x) ^ 5 + (1 + x) ^ 5 + (1 + x) ^ 5) :=
      mul_le_mul_of_nonneg_left hsum hx
    _ = _ := by ring

private theorem exp_short_clock_increment_le (β Cσ Cexp : ℝ) (M s : ℕ)
    (hβspec : Real.exp (β ^ 2) - 1 = Polymer.sigmaSq β)
    (hσnonneg : 0 ≤ Polymer.sigmaSq β) (hs : s ≤ 6)
    (hσrate : Polymer.sigmaSq β ≤ Cσ / Real.log (M : ℝ))
    (hCσ : 0 ≤ Cσ) (hCexp : Cexp = 6 * Cσ * (1 + Cσ / Real.log 2) ^ 5)
    (_hlogM : 0 < Real.log (M : ℝ)) (hMge2 : (2 : ℝ) ≤ (M : ℝ)) :
    Real.exp ((s : ℝ) * β ^ 2) - 1 ≤ Cexp / Real.log (M : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by norm_num) hMge2
  have hσbound : Polymer.sigmaSq β ≤ Cσ / Real.log 2 :=
    hσrate.trans (div_le_div_of_nonneg_left hCσ hlog2 hlog2le)
  have hfactor : (1 + Polymer.sigmaSq β) ^ 5 ≤
      (1 + Cσ / Real.log 2) ^ 5 := by
    apply pow_le_pow_left₀ (by linarith [hσnonneg])
    linarith
  have hexpNat : Real.exp ((s : ℝ) * β ^ 2) = (Real.exp (β ^ 2)) ^ s := by
    rw [← Real.exp_nat_mul]
  have hβexp : Real.exp (β ^ 2) = 1 + Polymer.sigmaSq β := by
    linarith [hβspec]
  have hpow : (1 + Polymer.sigmaSq β) ^ s ≤ (1 + Polymer.sigmaSq β) ^ 6 :=
    pow_le_pow_right₀ (by linarith [hσnonneg]) hs
  have hgeom := one_add_pow_six_sub_one_le (Polymer.sigmaSq β) hσnonneg
  have hbase : 0 ≤ 6 * Polymer.sigmaSq β := by positivity
  calc
    _ = (1 + Polymer.sigmaSq β) ^ s - 1 := by rw [hexpNat, hβexp]
    _ ≤ (1 + Polymer.sigmaSq β) ^ 6 - 1 := sub_le_sub_right hpow 1
    _ ≤ 6 * Polymer.sigmaSq β * (1 + Polymer.sigmaSq β) ^ 5 := hgeom
    _ ≤ 6 * Polymer.sigmaSq β * (1 + Cσ / Real.log 2) ^ 5 :=
      mul_le_mul_of_nonneg_left hfactor hbase
    _ ≤ Cexp / Real.log (M : ℝ) := by
      have hcoef := mul_le_mul_of_nonneg_left hσrate
        (show 0 ≤ 6 * (1 + Cσ / Real.log 2) ^ 5 by positivity)
      calc
        _ = (6 * (1 + Cσ / Real.log 2) ^ 5) * Polymer.sigmaSq β := by ring
        _ ≤ (6 * (1 + Cσ / Real.log 2) ^ 5) *
            (Cσ / Real.log (M : ℝ)) := hcoef
        _ = Cexp / Real.log (M : ℝ) := by rw [hCexp]; ring

private theorem natCast_div_two_of_even {n : ℕ} (hn : Even n) :
    ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by
  rcases hn with ⟨r, hr⟩
  have hn' : 2 * (n / 2) = n := by omega
  have hc : 2 * ((n / 2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hn'
  linarith only [hc]

private theorem diagonalLogShiftENN_eq_of_nonneg (H F Q Qflat D : ℝ)
    (hQ : 0 ≤ Q) (hQflat : 0 ≤ Qflat)
    (hD : 0 ≤ D) :
    ENNReal.ofReal logHolderConstant * ENNReal.ofReal (Real.sqrt Q) ^ ((1 : ℝ) / 3) *
        ((ENNReal.ofReal (1 + Q)) ^ ((1 : ℝ) / 3) + 1) +
      ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 * D)) ^ ((1 : ℝ) / 3) *
        ((ENNReal.ofReal (Real.exp H * (2 * Qflat + 2 * D))) ^ ((1 : ℝ) / 3) +
          (ENNReal.ofReal (Real.exp H * Qflat)) ^ ((1 : ℝ) / 3)) =
      ENNReal.ofReal (diagonalLogShiftBound H F Q Qflat D) := by
  have hC : 0 ≤ logHolderConstant := logHolderConstant_pos.le
  have hsqrtQ : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hF2D : 0 ≤ F ^ 2 * D := mul_nonneg (sq_nonneg F) hD
  have hsqrtF2D : 0 ≤ Real.sqrt (F ^ 2 * D) := Real.sqrt_nonneg _
  have h1Q : 0 ≤ 1 + Q := by linarith
  have hA : 0 ≤ Real.exp H * (2 * Qflat + 2 * D) := by positivity
  have hB : 0 ≤ Real.exp H * Qflat := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hsqrtQ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg h1Q (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hsqrtF2D (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hB (by norm_num),
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by positivity) (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1

private theorem eLpNorm_centered_log_diagonal_profile_shift_le
    (β H F : ℝ) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hF : 0 ≤ F) (hFone : 1 ≤ F)
    {d u M : ℕ} (hdu : d ≤ u) (huM : u ≤ M) (x : Site) (f : Site → ℝ)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H)
    (hfb : ∀ z, |f z| ≤ F) (Qvar : ℝ) (hQvar : 0 ≤ Qvar)
    (hvarInt : Integrable
      (fun ω => (smoothedP2Plane β d u x ω - 1) ^ 2) disorderLaw)
    (hvar : (∫ ω, (smoothedP2Plane β d u x ω - 1) ^ 2 ∂disorderLaw) ≤ Qvar)
    (R : ℝ) (hR : 0 ≤ R) (hkernel : ∀ z, srwKernel u (z - x) ≤ R)
    (K : ℝ) (hK : 0 ≤ K)
    (hcollision : (∑ r ∈ Finset.Icc 1 (M - u),
      Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (M - u - r) 0 ω ^ 2 ∂disorderLaw)) ≤ K)
    (Qflat : ℝ) (hQflat : 0 ≤ Qflat)
    (hflatInt : Integrable
      (fun ω => profileP2Fun β u M (fun w => srwKernel u (w - x))
        (fun _ => 1) ω ^ 2) disorderLaw)
    (hflat : (∫ ω, profileP2Fun β u M (fun w => srwKernel u (w - x))
      (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Qflat)
    (D : ℝ) (hD : 0 ≤ D)
    (hDflat : (∫ ω, shortClockEndpointTV β d u x ω ^ 2 ∂disorderLaw) +
      (∫ ω, ∑ w ∈ Polymer.endpoints x u,
        (smoothedEndpointDist β d u x ω w - srwKernel u (w - x)) ^ 2
          ∂disorderLaw) * K ≤ D) :
    eLpNorm (fun ω =>
      (Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) f ω) -
        Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) f ω)) -
      ∫ ω', (Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x))
            (fun _ => 1) ω') -
          Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x))
            (fun _ => 1) ω')) ∂disorderLaw)
      2 disorderLaw ≤ ENNReal.ofReal (2 * diagonalLogShiftBound H F Qvar Qflat D) := by
  let T : ℝ := ∫ ω, shortClockEndpointTV β d u x ω ^ 2 ∂disorderLaw
  let Ccoord : ℝ := ∫ ω, ∑ w ∈ Polymer.endpoints x u,
    (smoothedEndpointDist β d u x ω w - srwKernel u (w - x)) ^ 2 ∂disorderLaw
  let D₀ : ℝ := T + Ccoord * K
  have hT : 0 ≤ T := by
    dsimp [T]
    exact integral_nonneg fun ω => sq_nonneg _
  have hCcoord : 0 ≤ Ccoord := by
    dsimp [Ccoord]
    apply integral_nonneg_of_ae
    filter_upwards [] with ω
    exact Finset.sum_nonneg fun w hw => sq_nonneg _
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD₀le : D₀ ≤ D := by simpa [D₀, T, Ccoord] using hDflat
  have hflatTerminal : ∀ z : Site, 0 < (1 : ℝ) ∧ |Real.log (1 : ℝ)| ≤ H := by
    intro z
    constructor
    · norm_num
    · simpa using hH
  have hflatBound : ∀ z : Site, |(1 : ℝ)| ≤ F := by
    intro z
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1)]
    exact hFone
  have hrawF := eLpNorm_log_diagonal_profile_shift_le β H F hβ hH hF
    hdu huM x f hf hfb Qvar hvarInt hvar R hR hkernel K hK hcollision Qflat hQflat
    hflatInt hflat
  have hrawOne := eLpNorm_log_diagonal_profile_shift_le β H F hβ hH hF
    hdu huM x (fun _ => 1) hflatTerminal hflatBound Qvar hvarInt hvar R hR hkernel
    K hK hcollision Qflat hQflat hflatInt hflat
  have hmono : diagonalLogShiftBound H F Qvar Qflat D₀ ≤
      diagonalLogShiftBound H F Qvar Qflat D := by
    dsimp [diagonalLogShiftBound]
    have hmul : F ^ 2 * D₀ ≤ F ^ 2 * D :=
      mul_le_mul_of_nonneg_left hD₀le (sq_nonneg F)
    have hroot : Real.sqrt (F ^ 2 * D₀) ≤ Real.sqrt (F ^ 2 * D) :=
      Real.sqrt_le_sqrt hmul
    have hroot0 : 0 ≤ Real.sqrt (F ^ 2 * D₀) := Real.sqrt_nonneg _
    have hpow : (Real.sqrt (F ^ 2 * D₀)) ^ ((1 : ℝ) / 3) ≤
        (Real.sqrt (F ^ 2 * D)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hroot0 hroot (by norm_num)
    have hsum : Real.exp H * (2 * Qflat + 2 * D₀) ≤
        Real.exp H * (2 * Qflat + 2 * D) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      linarith
    have hsum0 : 0 ≤ Real.exp H * (2 * Qflat + 2 * D₀) := by positivity
    have hsumPow : (Real.exp H * (2 * Qflat + 2 * D₀)) ^ ((1 : ℝ) / 3) ≤
        (Real.exp H * (2 * Qflat + 2 * D)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hsum0 hsum (by norm_num)
    have hC : 0 ≤ logHolderConstant := logHolderConstant_pos.le
    have hExpQ : 0 ≤ (Real.exp H * Qflat) ^ ((1 : ℝ) / 3) := by positivity
    have hExpQ' : 0 ≤ (Real.exp H * (2 * Qflat + 2 * D₀)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by positivity) _
    exact add_le_add le_rfl
      (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC)
        (add_le_add hsumPow le_rfl)
        (add_nonneg hExpQ' hExpQ)
        (mul_nonneg hC
          (Real.rpow_nonneg (Real.sqrt_nonneg (F ^ 2 * D)) ((1 : ℝ) / 3))))
  have hrawBoundF :
      eLpNorm (fun ω => Real.log (profileP2Fun β d M
          (fun w => srwKernel d (w - x)) f ω) -
        Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) f ω))
        2 disorderLaw ≤ ENNReal.ofReal (diagonalLogShiftBound H F Qvar Qflat D) := by
    have hactual := diagonalLogShiftENN_eq_of_nonneg H F Qvar Qflat D₀
      hQvar hQflat hD₀
    calc
      _ ≤ _ := hrawF
      _ = ENNReal.ofReal (diagonalLogShiftBound H F Qvar Qflat D₀) := by
        simpa [D₀, T, Ccoord, diagonalLogShiftBound] using hactual
      _ ≤ _ := ENNReal.ofReal_le_ofReal hmono
  have hrawBoundOne :
      eLpNorm (fun ω => Real.log (profileP2Fun β d M
          (fun w => srwKernel d (w - x)) (fun _ => 1) ω) -
        Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) (fun _ => 1) ω))
        2 disorderLaw ≤ ENNReal.ofReal (diagonalLogShiftBound H F Qvar Qflat D) := by
    have hactual := diagonalLogShiftENN_eq_of_nonneg H F Qvar Qflat D₀
      hQvar hQflat hD₀
    calc
      _ ≤ _ := hrawOne
      _ = ENNReal.ofReal (diagonalLogShiftBound H F Qvar Qflat D₀) := by
        simpa [D₀, T, Ccoord, diagonalLogShiftBound] using hactual
      _ ≤ _ := ENNReal.ofReal_le_ofReal hmono
  have hrawOneMem : MemLp (fun ω =>
      (Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) (fun _ => 1) ω) -
        Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) (fun _ => 1) ω)))
      2 disorderLaw := by
    apply (memLp_iff).2
    exact (hrawBoundOne.trans_lt ENNReal.ofReal_lt_top)
  have hcenter := eLpNorm_sub_integral_le disorderLaw
    (fun ω => Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) f ω) -
      Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) f ω))
    (fun ω => Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) (fun _ => 1) ω) -
      Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) (fun _ => 1) ω))
    hrawOneMem
  have hBnonneg := diagonalLogShiftBound_nonneg H F Qvar Qflat D
    hQvar hQflat hD
  calc
    _ ≤ eLpNorm (fun ω =>
          Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) f ω) -
            Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) f ω))
          2 disorderLaw +
        eLpNorm (fun ω => Real.log (profileP2Fun β d M
          (fun w => srwKernel d (w - x)) (fun _ => 1) ω) -
          Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) (fun _ => 1) ω))
          2 disorderLaw := by
      simpa using hcenter
    _ ≤ ENNReal.ofReal (diagonalLogShiftBound H F Qvar Qflat D) +
        ENNReal.ofReal (diagonalLogShiftBound H F Qvar Qflat D) :=
      add_le_add hrawBoundF hrawBoundOne
    _ = ENNReal.ofReal (2 * diagonalLogShiftBound H F Qvar Qflat D) := by
      rw [← ENNReal.ofReal_add hBnonneg hBnonneg]
      congr 1
      ring

private theorem integrable_log_freeKernelProfile (β : ℝ) (t M : ℕ) (z : Site) :
    Integrable (fun ω => Real.log (profileP2Fun β t M
      (fun w => srwKernel t (w - z)) (fun _ => 1) ω)) disorderLaw := by
  let ν : Site → ℝ := fun w => srwKernel t (w - z)
  let A : Finset Site := Polymer.endpoints z t
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem t z w (by simpa [A] using hw)
  have hν0 : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg t (w - z)
  have hν1 : ∑ w ∈ A, ν w = 1 := by
    simpa [A, ν] using Polymer.sum_srwKernel_endpoints t z
  have hνpos : ∃ w ∈ A, 0 < ν w := by
    have hsum : 0 < ∑ w ∈ A, ν w := by rw [hν1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hν0 w)).mp hsum
  have hmem := memLp_log_profileP2Fun_of_bounded_terminal β t M ν A
    hνA hν0 hν1 (fun _ => 1) 0 (by norm_num) (by intro w; norm_num)
  exact hmem.integrable (by norm_num)

private theorem latticeSmoothingError_diagonal_change_le_of_site
    (β : ℝ) (M d u : ℕ) (hM : 0 < M) (hdu : d ≤ u) (huM : u ≤ M)
    (hMeven : Even M) (hdEven : Even d) (huEven : Even u)
    (h₀ : Plane →ᵇ ℝ) (φ : Plane → ℝ) (hφ : Measurable φ)
    (hφc : HasCompactSupport φ) (hφb : ∃ B : ℝ, ∀ x, |φ x| ≤ B)
    (B : ℝ) (hB : 0 ≤ B)
    (hsite : ∀ z : Site, eLpNorm (fun ω =>
      (Real.log (profileP2Fun β d M (fun w => srwKernel d (w - z))
          (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) ω) -
        Real.log (profileP2Fun β u M (fun w => srwKernel u (w - z))
          (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) ω)) -
        ∫ ω', (Real.log (profileP2Fun β d M (fun w => srwKernel d (w - z))
              (fun _ => 1) ω') -
            Real.log (profileP2Fun β u M (fun w => srwKernel u (w - z))
              (fun _ => 1) ω')) ∂disorderLaw)
        2 disorderLaw ≤ ENNReal.ofReal B) :
    Integrable (fun ω => latticeSmoothingError β M M d d h₀ φ ω -
      latticeSmoothingError β M M u u h₀ φ ω) disorderLaw ∧
    eLpNorm (fun ω => latticeSmoothingError β M M d d h₀ φ ω -
      latticeSmoothingError β M M u u h₀ φ ω) 2 disorderLaw ≤
        ENNReal.ofReal (B * ∫ x, |φ x|) := by
  let f : Site → ℝ := evenExtension (cellAverage M fun y => Real.exp (h₀ y))
  let raw : Disorder → Site → ℝ := fun ω z =>
    Real.log (profileP2Fun β d M (fun w => srwKernel d (w - z)) f ω) -
      Real.log (profileP2Fun β u M (fun w => srwKernel u (w - z)) f ω)
  let rawFlat : Disorder → Site → ℝ := fun ω z =>
    Real.log (profileP2Fun β d M (fun w => srwKernel d (w - z)) (fun _ => 1) ω) -
      Real.log (profileP2Fun β u M (fun w => srwKernel u (w - z)) (fun _ => 1) ω)
  let center : Site → ℝ := fun z => ∫ ω, rawFlat ω z ∂disorderLaw
  let Z : Disorder → Plane → ℝ := fun ω x => raw ω (latticePoint M x) - center (latticePoint M x)
  let pointStart : Disorder → Site → ℝ := fun ω z =>
    Real.log (profileP2Fun β 0 M (fun w => if w = z then 1 else 0)
        (cellAverage M fun y => Real.exp (h₀ y)) ω) -
      ∫ ω', Real.log (profileP2Fun β 0 M (fun w => if w = z then 1 else 0)
        (fun _ => 1) ω') ∂disorderLaw
  let profileAt : ℕ → Disorder → Site → ℝ := fun a ω z =>
    Real.log (profileP2Fun β a M (fun w => srwKernel a (w - z)) f ω) -
      ∫ ω', Real.log (profileP2Fun β a M
        (fun w => srwKernel a (w - z)) (fun _ => 1) ω') ∂disorderLaw
  have hfInt : Integrable φ :=
    integrable_of_measurable_compactSupport_bounded hφ hφc hφb
  have hνd : ∀ w : Site, Measurable (fun p : Disorder × Site => srwKernel d (w - p.2)) := by
    intro w
    exact (measurable_of_countable fun z : Site => srwKernel d (w - z)).comp measurable_snd
  have hνu : ∀ w : Site, Measurable (fun p : Disorder × Site => srwKernel u (w - p.2)) := by
    intro w
    exact (measurable_of_countable fun z : Site => srwKernel u (w - z)).comp measurable_snd
  have hrawJoint : Measurable (fun p : Disorder × Site => raw p.1 p.2) := by
    dsimp [raw, f]
    exact (measurable_profileP2Fun_param β d M
      (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) hνd measurable_fst).log.sub
      (measurable_profileP2Fun_param β u M
        (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) hνu measurable_fst).log
  have hcenterMeas : Measurable center := measurable_of_countable _
  have hZ : Measurable (fun p : Disorder × Plane => Z p.1 p.2) := by
    dsimp [Z, raw]
    have hp : Measurable (fun p : Disorder × Plane => (p.1, latticePoint M p.2)) :=
      measurable_fst.prodMk ((measurable_latticePoint M).comp measurable_snd)
    exact (hrawJoint.comp hp).sub (hcenterMeas.comp
      ((measurable_latticePoint M).comp measurable_snd))
  have hZbound (x : Plane) : eLpNorm (fun ω => Z ω x) 2 disorderLaw ≤
      ENNReal.ofReal B := by
    simpa [Z, center, raw, rawFlat] using hsite (latticePoint M x)
  have hZmem (x : Plane) : MemLp (fun ω => Z ω x) 2 disorderLaw := by
    apply (memLp_iff).2
    exact (hZbound x).trans_lt ENNReal.ofReal_lt_top
  have hZsq (x : Plane) : Integrable (fun ω => Z ω x ^ 2) disorderLaw ∧
      (∫ ω, Z ω x ^ 2 ∂disorderLaw) ≤ B ^ 2 :=
    integral_sq_le_of_eLpNorm_le disorderLaw (hZmem x) B hB (hZbound x)
  let hspatial := eLpNorm_integral_mul_le_of_uniform_secondMoment disorderLaw φ hφ hfInt
    hZ hZmem (B ^ 2) (sq_nonneg B) hZsq
  have hlogD (z : Site) := integrable_log_freeKernelProfile β d M z
  have hlogU (z : Site) := integrable_log_freeKernelProfile β u M z
  have hprofileCell (a : ℕ) (haM : a ≤ M) (haEven : Even a)
      (ω : Disorder) (z : Site) (hzEven : Even (z 0 + z 1)) :
      profileP2Fun β a M (fun w => srwKernel a (w - z))
          (cellAverage M fun y => Real.exp (h₀ y)) ω =
        profileP2Fun β a M (fun w => srwKernel a (w - z)) f ω := by
    have hν : ∀ w, srwKernel a (w - z) ≠ 0 → Even (w 0 + w 1) := by
      intro w hw
      have hwmem : w ∈ Polymer.endpoints z a := by
        by_contra hnot
        exact hw (Polymer.srwKernel_eq_zero_of_not_mem a z w hnot)
      exact even_endpoint_of_mem hzEven haEven hwmem
    have hfg : ∀ w, Even (w 0 + w 1) →
        (cellAverage M fun y => Real.exp (h₀ y)) w = f w := by
      intro w hw
      simp [f, evenExtension, hw]
    exact profileP2Fun_congr_of_even β haM
      ((Nat.even_sub haM).2 ⟨fun _ => haEven, fun _ => hMeven⟩)
      (fun w => srwKernel a (w - z))
      (cellAverage M fun y => Real.exp (h₀ y)) f hν hfg ω
  have hφBound : ∃ C : ℝ, ∀ x, |φ x| ≤ C := hφb
  have houterInt (a : ℕ) (ω : Disorder) :
      Integrable (fun x => φ x *
        (pointStart ω (latticePoint M x) - profileAt a ω (latticePoint M x))) := by
    let g : Site → ℝ := fun z => pointStart ω z - profileAt a ω z
    have hg := integrable_mul_siteFunction_latticePoint M hM hφ hφc hφBound g
    have heq : (fun x => φ x *
        (pointStart ω (latticePoint M x) - profileAt a ω (latticePoint M x))) =
      fun x => φ x * g (latticePoint M x) := by
        funext x
        rfl
    rw [heq]
    exact hg
  have herrorEq (a : ℕ) (haM : a ≤ M) (haEven : Even a) (ω : Disorder) :
      latticeSmoothingError β M M a a h₀ φ ω =
        ∫ x, φ x *
          (pointStart ω (latticePoint M x) - profileAt a ω (latticePoint M x)) := by
    unfold latticeSmoothingError
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [pointStart, profileAt]
    have hzEven : Even ((latticePoint M x) 0 + (latticePoint M x) 1) := by
      have hzmem := Critical2DKPZ.latticePoint_mem_evenLattice M x
      simpa only [Critical2DKPZ.evenLattice, Set.mem_ofPred_eq] using hzmem
    rw [hprofileCell a haM haEven ω (latticePoint M x) hzEven]
  have hmeanSub (z : Site) :
      center z =
        (∫ ω, Real.log (profileP2Fun β d M (fun w => srwKernel d (w - z))
            (fun _ => 1) ω) ∂disorderLaw) -
        ∫ ω, Real.log (profileP2Fun β u M (fun w => srwKernel u (w - z))
            (fun _ => 1) ω) ∂disorderLaw := by
    dsimp [center, rawFlat]
    rw [integral_sub (hlogD z) (hlogU z)]
  have hdiagEq (ω : Disorder) :
      latticeSmoothingError β M M d d h₀ φ ω -
          latticeSmoothingError β M M u u h₀ φ ω =
        -∫ x, φ x * Z ω x := by
    rw [herrorEq d (by omega) hdEven ω, herrorEq u huM huEven ω]
    calc
      _ = ∫ x, (φ x * (pointStart ω (latticePoint M x) -
            profileAt d ω (latticePoint M x)) -
          φ x * (pointStart ω (latticePoint M x) -
            profileAt u ω (latticePoint M x))) := by
              rw [← integral_sub (houterInt d ω) (houterInt u ω)]
      _ = -∫ x, φ x * Z ω x := by
            rw [← integral_neg]
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [Z, raw, rawFlat, profileAt]
            rw [hmeanSub (latticePoint M x)]
            ring
  have hdiagInt : Integrable (fun ω =>
      latticeSmoothingError β M M d d h₀ φ ω -
        latticeSmoothingError β M M u u h₀ φ ω) disorderLaw := by
    have heq : (fun ω => latticeSmoothingError β M M d d h₀ φ ω -
        latticeSmoothingError β M M u u h₀ φ ω) = fun ω => -∫ x, φ x * Z ω x := by
      funext ω
      exact hdiagEq ω
    rw [heq]
    exact hspatial.1.neg
  refine ⟨hdiagInt, ?_⟩
  have hnormEq : eLpNorm (fun ω =>
      latticeSmoothingError β M M d d h₀ φ ω -
        latticeSmoothingError β M M u u h₀ φ ω) 2 disorderLaw =
      eLpNorm (fun ω => ∫ x, φ x * Z ω x) 2 disorderLaw := by
    have heq : (fun ω => latticeSmoothingError β M M d d h₀ φ ω -
        latticeSmoothingError β M M u u h₀ φ ω) =
        fun ω => -∫ x, φ x * Z ω x := by
      funext ω
      exact hdiagEq ω
    rw [heq]
    change eLpNorm (-(fun ω => ∫ x, φ x * Z ω x)) 2 disorderLaw = _
    exact eLpNorm_neg _ _ _
  rw [hnormEq]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (B ^ 2) * ∫ x, |φ x|) := hspatial.2
    _ = ENNReal.ofReal (B * ∫ x, |φ x|) := by
      congr 1
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB]

/-- The diagonal short-clock change tends to zero uniformly over bounded terminal profiles. -/
private theorem latticeSmoothingError_diagonal_change_small
    (A H M₁ M₂ δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, Even M →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ k : ℕ, Even k →
        (k : ℤ) ≤ evenCeil (δ * M) + 6 →
        (evenCeil (δ * M) : ℤ) ≤ k + 6 →
        ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
          ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ →
            (∫ x, |φ x| ≤ M₁) → (∀ x, |φ x| ≤ M₂) →
              eLpNorm (fun ω =>
                latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω -
                  latticeSmoothingError (criticalBeta ϑ M) M M
                    (evenCeil (δ * M)) (evenCeil (δ * M)) h₀ φ ω)
                2 disorderLaw ≤ ENNReal.ofReal ε := by
  intro ε hε
  let H₀ : ℝ := max H 0
  let F : ℝ := Real.exp H₀
  let η : ℝ := ε / (6 * (|M₁| + 1))
  have hH₀ : 0 ≤ H₀ := by dsimp [H₀]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hFone : 1 ≤ F := by
    dsimp [F]
    exact Real.one_le_exp hH₀
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨Cvar, hCvar, hvarEvent⟩ :=
    integrable_smoothedP2Plane_shortClock_centered_sq_le A
  obtain ⟨Qflat, hQflat, hflatEvent⟩ :=
    integrable_smoothedP2Plane_sq_and_le_of_scale A δ hδ hδ1
  obtain ⟨Ccoll, hCcoll, hcollEvent⟩ := shortClockCollision_sum_le_linear A
  obtain ⟨Craw, hsecondEvent⟩ := OnePoint.sigmaSq_secondMoment_le_uniform A 1
  let Cσ : ℝ := |Craw| + 1
  let Cq : ℝ := 2 * Cvar / δ
  let Cexp : ℝ := 6 * Cσ * (1 + Cσ / Real.log 2) ^ 5
  let CRK : ℝ := 4 * Ccoll / δ
  let Cd : ℝ := (16 + 8 * CRK) * (Cexp + Cq) + 8 * Ccoll * Cq
  have hCσ : 0 < Cσ := by dsimp [Cσ]; positivity
  have hCq : 0 < Cq := by dsimp [Cq]; positivity
  have hCexp : 0 < Cexp := by
    dsimp [Cexp]
    positivity
  have hCRK : 0 < CRK := by dsimp [CRK]; positivity
  have hCd : 0 < Cd := by
    dsimp [Cd]
    positivity
  have hlogAtTop : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogA : ∀ᶠ M : ℕ in atTop, |A| < Real.log (M : ℝ) :=
    hlogAtTop.eventually_gt_atTop |A|
  have hthreshold : ∀ᶠ M : ℕ in atTop,
      12 ≤ δ * (M : ℝ) ∧ 8 ≤ (1 - δ) * (M : ℝ) ∧ 1 ≤ M := by
    have hM := tendsto_natCast_atTop_atTop.eventually_gt_atTop
      (max (12 / δ) (8 / (1 - δ)))
    filter_upwards [hM, eventually_ge_atTop 1] with M hM hM1
    have hMcast : max (12 / δ) (8 / (1 - δ)) < (M : ℝ) := hM
    have hδM : 12 ≤ δ * (M : ℝ) := by
      have h := lt_of_le_of_lt (le_max_left _ _) hMcast
      have h' := (div_lt_iff₀ hδ).mp h
      exact h'.le.trans_eq (mul_comm _ _)
    have hmargin : 8 ≤ (1 - δ) * (M : ℝ) := by
      have hδ' : 0 < 1 - δ := by linarith
      have h := lt_of_le_of_lt (le_max_right _ _) hMcast
      have h' := (div_lt_iff₀ hδ').mp h
      exact h'.le.trans_eq (mul_comm _ _)
    exact ⟨hδM, hmargin, hM1⟩
  have hdiagConv := diagonalLogShiftBound_tendsto_zero H₀ F Qflat Cq Cd
  have hdiagSmall : ∀ᶠ M : ℕ in atTop,
      diagonalLogShiftBound H₀ F
        (Cq * (M : ℝ)⁻¹ * (Real.log (M : ℝ))⁻¹) Qflat
        (Cd * (Real.log (M : ℝ))⁻¹) < η := by
    filter_upwards [hdiagConv.eventually (Metric.ball_mem_nhds 0 hη)] with M hM
    have habs : |diagonalLogShiftBound H₀ F
        (Cq * (M : ℝ)⁻¹ * (Real.log (M : ℝ))⁻¹) Qflat
        (Cd * (Real.log (M : ℝ))⁻¹)| < η := by
      simpa [Real.dist_eq] using hM
    exact (abs_lt.mp habs).2
  filter_upwards [hvarEvent, hflatEvent, hcollEvent, hsecondEvent, hlogA,
    hthreshold, hdiagSmall] with M hvarM hflatM hcollM hCσM
      hlogAM hthresholdM hdiagSmallM
  intro hMeven ϑ hϑ k hk hklo hkhi h₀ hh₀ φ hφ hφc hφL1 hφM
  have hA0 : 0 ≤ A := by
    rcases hϑ with ⟨hlo, hhi⟩
    linarith
  have hθlog : |ϑ| < Real.log (M : ℝ) := by
    have hθabs : |ϑ| ≤ A := abs_le.mpr hϑ
    have hAabs : A = |A| := (abs_of_nonneg hA0).symm
    rw [hAabs] at hθabs
    exact lt_of_le_of_lt hθabs hlogAM
  have hMone : 1 ≤ M := hthresholdM.2.2
  have hβspec := OnePoint.criticalBeta_spec_of_abs_lt_log hMone hθlog
  have hβ : 0 ≤ criticalBeta ϑ M := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hσnonneg : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ M) := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have hσone : 1 ≤
      ∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ^ 2 ∂disorderLaw :=
    pointToPlane_oneStep_secondMoment_ge_one (criticalBeta ϑ M)
  have hσraw := hCσM ϑ hϑ 1 (by norm_num) (by
    norm_num
    exact_mod_cast hMone)
  have hlogMpos : 0 < Real.log (M : ℝ) := by
    apply Real.log_pos
    have : (1 : ℝ) < (M : ℝ) := by
      have hprod : δ * (M : ℝ) ≤ (M : ℝ) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hδ1.le (Nat.cast_nonneg M)
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 12)
        (hthresholdM.1.trans hprod)
    exact this
  have hMrealpos : 0 < (M : ℝ) := by linarith
  have hlogM1 : 0 < Real.log (1 + (M : ℝ)) := by
    apply Real.log_pos
    linarith
  have hCrawLe : Craw ≤ Cσ := by dsimp [Cσ]; linarith [le_abs_self Craw]
  have hσrate : Polymer.sigmaSq (criticalBeta ϑ M) ≤ Cσ / Real.log (M : ℝ) := by
    have hσstep : Polymer.sigmaSq (criticalBeta ϑ M) ≤
        Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ^ 2 ∂disorderLaw) := by
      calc
        _ = Polymer.sigmaSq (criticalBeta ϑ M) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hσone hσnonneg
    have hraw : Polymer.sigmaSq (criticalBeta ϑ M) ≤
        Craw / Real.log (1 + (M : ℝ)) := by
      calc
        _ ≤ _ := hσstep
        _ ≤ Craw / Real.log (1 + (M : ℝ) / 1) := by simpa using hσraw
        _ = _ := by norm_num
    have hraw' : Polymer.sigmaSq (criticalBeta ϑ M) ≤
        Cσ / Real.log (1 + (M : ℝ)) :=
      hraw.trans (div_le_div_of_nonneg_right hCrawLe hlogM1.le)
    have hlogle : Real.log (M : ℝ) ≤ Real.log (1 + (M : ℝ)) :=
      Real.log_le_log hMrealpos (by linarith)
    exact hraw'.trans (div_le_div_of_nonneg_left hCσ.le hlogMpos hlogle)
  let m : ℕ := evenCeil (δ * (M : ℝ))
  have hmEven : Even m := evenCeil_even _
  have hmCastLower : δ * (M : ℝ) ≤ (m : ℝ) := by
    dsimp [m]
    exact Critical2DKPZ.le_evenCeil _
  have hmCastUpper : (m : ℝ) < δ * (M : ℝ) + 2 := by
    dsimp [m]
    exact evenCeil_lt_add_two (by positivity)
  have hm6Mcast : (m : ℝ) + 6 ≤ (M : ℝ) := by
    have := hthresholdM.2.1
    linarith
  have hm6M : m + 6 ≤ M := by exact_mod_cast hm6Mcast
  have hkmInt : (k : ℤ) ≤ (m : ℤ) + 6 := by simpa [m] using hklo
  have hmkInt : (m : ℤ) ≤ (k : ℤ) + 6 := by simpa [m] using hkhi
  have hkm : k ≤ m + 6 := by omega
  have hmk : m ≤ k + 6 := by omega
  have hkM : k ≤ M := by omega
  have hkLower : δ * (M : ℝ) / 2 ≤ (k : ℝ) := by
    have hkreal : (m : ℝ) ≤ (k : ℝ) + 6 := by exact_mod_cast hmk
    linarith [hthresholdM.1, hmCastLower]
  have hmLower : δ * (M : ℝ) / 2 ≤ (m : ℝ) := by linarith [hmCastLower]
  have hkEven : Even k := hk
  let d : ℕ := min k m
  let u : ℕ := max k m
  have hdu : d ≤ u := min_le_max
  have hmM : m ≤ M := by omega
  have huM : u ≤ M := max_le hkM hmM
  have hdEven : Even d := by
    dsimp [d]
    rcases le_total k m with h | h
    · rw [min_eq_left h]
      exact hkEven
    · rw [min_eq_right h]
      exact hmEven
  have huEven : Even u := by
    dsimp [u]
    rcases le_total k m with h | h
    · rw [max_eq_right h]
      exact hmEven
    · rw [max_eq_left h]
      exact hkEven
  have hgap : u - d ≤ 6 := by
    rcases le_total k m with h | h
    · dsimp [u, d]
      rw [max_eq_right h, min_eq_left h]
      omega
    · dsimp [u, d]
      rw [max_eq_left h, min_eq_right h]
      omega
  have hdLower : δ * (M : ℝ) / 2 ≤ (d : ℝ) := by
    dsimp [d]
    rw [Nat.cast_min]
    exact le_min hkLower hmLower
  have hdpos : 1 ≤ d := by
    have hdreal : 0 < (d : ℝ) := by linarith [hdLower, hthresholdM.1]
    exact_mod_cast (show (1 : ℝ) ≤ (d : ℝ) by linarith)
  have huScale : δ * (M : ℝ) / 2 ≤ (u : ℝ) := by
    have hdleu : (d : ℝ) ≤ (u : ℝ) := by exact_mod_cast hdu
    linarith [hdLower, hdleu]
  have hlogM : 0 < Real.log (M : ℝ) := hlogMpos
  let Qvar : ℝ := Cq * (M : ℝ)⁻¹ * (Real.log (M : ℝ))⁻¹
  let Dvar : ℝ := Cd * (Real.log (M : ℝ))⁻¹
  have hQvar : 0 ≤ Qvar := by
    dsimp [Qvar]
    positivity
  have hDvar : 0 ≤ Dvar := by dsimp [Dvar]; positivity
  have hvarInt (x : Site) : Integrable
      (fun ω => (smoothedP2Plane (criticalBeta ϑ M) d u x ω - 1) ^ 2) disorderLaw := by
    simpa only [Nat.add_sub_of_le hdu] using (hvarM ϑ hϑ d (u - d)
      hdpos (by omega) (by omega) x).1
  have hvar (x : Site) :
      (∫ ω, (smoothedP2Plane (criticalBeta ϑ M) d u x ω - 1) ^ 2 ∂disorderLaw) ≤ Qvar := by
    have hraw := (hvarM ϑ hϑ d (u - d) hdpos (by omega) (by omega) x).2
    have hraw' :
        (∫ ω, (smoothedP2Plane (criticalBeta ϑ M) d u x ω - 1) ^ 2 ∂disorderLaw) ≤
          Cvar / ((d : ℝ) * Real.log (M : ℝ)) := by
      simpa only [Nat.add_sub_of_le hdu] using hraw
    have hdscale : δ * (M : ℝ) / 2 ≤ (d : ℝ) := hdLower
    have hden : (δ * (M : ℝ) / 2) * Real.log (M : ℝ) ≤
        (d : ℝ) * Real.log (M : ℝ) :=
      mul_le_mul_of_nonneg_right hdscale hlogM.le
    have hdenpos : 0 < (δ * (M : ℝ) / 2) * Real.log (M : ℝ) := by positivity
    have hrough : Cvar / ((d : ℝ) * Real.log (M : ℝ)) ≤
        Cvar / ((δ * (M : ℝ) / 2) * Real.log (M : ℝ)) :=
      div_le_div_of_nonneg_left hCvar.le hdenpos hden
    have heq : Cvar / ((δ * (M : ℝ) / 2) * Real.log (M : ℝ)) = Qvar := by
      dsimp [Qvar, Cq]
      field_simp
    exact hraw'.trans (hrough.trans_eq heq)
  have hsmoothedInt : Integrable
      (fun ω => smoothedP2Plane (criticalBeta ϑ M) u M 0 ω ^ 2) disorderLaw :=
    OnePoint.integrable_smoothedP2Plane_sq (criticalBeta ϑ M) u M
  have hflatMass := hflatM ϑ hϑ u (by omega) (by exact_mod_cast huScale) huM
  have hflatIdent (z : Site) : IdentDistrib
      (fun ω => smoothedP2Plane (criticalBeta ϑ M) u M z ω ^ 2)
      (fun ω => smoothedP2Plane (criticalBeta ϑ M) u M 0 ω ^ 2)
      disorderLaw disorderLaw := by
    have hident := Critical2DKPZ.LogNormality.identDistrib_smoothedP2Plane_translate
      (criticalBeta ϑ M) u M z
    simpa only [Function.comp_def, Function.comp_apply] using
      hident.comp (by fun_prop : Measurable (fun r : ℝ => r ^ 2))
  have hsmoothedIntAt (z : Site) : Integrable
      (fun ω => smoothedP2Plane (criticalBeta ϑ M) u M z ω ^ 2) disorderLaw :=
    (hflatIdent z).integrable_iff.2 hsmoothedInt
  have hflatEq (z : Site) (ω : Disorder) :
      profileP2Fun (criticalBeta ϑ M) u M (fun w => srwKernel u (w - z))
          (fun _ => 1) ω = smoothedP2Plane (criticalBeta ϑ M) u M z ω :=
    Polymer.profileP2Fun_srw_flat (criticalBeta ϑ M) u M z ω
  have hflatInt (z : Site) : Integrable
      (fun ω => profileP2Fun (criticalBeta ϑ M) u M
        (fun w => srwKernel u (w - z)) (fun _ => 1) ω ^ 2) disorderLaw := by
    have heq : (fun ω => profileP2Fun (criticalBeta ϑ M) u M
        (fun w => srwKernel u (w - z)) (fun _ => 1) ω ^ 2) =
        fun ω => smoothedP2Plane (criticalBeta ϑ M) u M z ω ^ 2 := by
      funext ω
      rw [hflatEq]
    rw [heq]
    exact hsmoothedIntAt z
  have hflat (z : Site) :
      (∫ ω, profileP2Fun (criticalBeta ϑ M) u M
        (fun w => srwKernel u (w - z)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Qflat := by
    calc
      _ = ∫ ω, smoothedP2Plane (criticalBeta ϑ M) u M z ω ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hflatEq]
      _ = ∫ ω, smoothedP2Plane (criticalBeta ϑ M) u M 0 ω ^ 2 ∂disorderLaw :=
        (hflatIdent z).integral_eq
      _ ≤ Qflat := hflatMass.2
  have hcollisionData := hcollM ϑ hϑ (M - u) (Nat.sub_le M u)
  have hcollision :
      (∑ r ∈ Finset.Icc 1 (M - u),
        Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (M - u - r) 0 ω ^ 2 ∂disorderLaw)) ≤
        Ccoll * (M : ℝ) := hcollisionData.2
  have hMge2 : (2 : ℝ) ≤ (M : ℝ) := by
    have hδMleM : δ * (M : ℝ) ≤ (M : ℝ) :=
      calc
        δ * (M : ℝ) ≤ 1 * (M : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith : δ ≤ 1) (Nat.cast_nonneg M)
        _ = (M : ℝ) := by ring
    have hMge12 : 12 ≤ (M : ℝ) := hthresholdM.1.trans hδMleM
    linarith only [hMge12]
  have hCexpEq : Cexp = 6 * Cσ * (1 + Cσ / Real.log 2) ^ 5 := rfl
  have hβspecPolymer : Real.exp ((criticalBeta ϑ M) ^ 2) - 1 =
      Polymer.sigmaSq (criticalBeta ϑ M) := rfl
  have hinc := exp_short_clock_increment_le (criticalBeta ϑ M) Cσ Cexp M (u - d)
    hβspecPolymer hσnonneg hgap hσrate hCσ.le hCexpEq hlogMpos hMge2
  have hRpos : 0 ≤ 4 / (δ * (M : ℝ)) := by positivity
  let R : ℝ := 4 / (δ * (M : ℝ))
  let K : ℝ := Ccoll * (M : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hRK : R * K = CRK := by
    dsimp [R, K, CRK]
    field_simp
  have hkernel (x z : Site) : srwKernel u (z - x) ≤ R := by
    have hhalf : 2 * (u / 2) = u := by
      rcases huEven with ⟨r, hr⟩
      omega
    have hkernel0 := srwKernel_even_le_inv_succ (u / 2) (z - x)
    have hkernel' : srwKernel u (z - x) ≤
        1 / (((u / 2 : ℕ) : ℝ) + 1) := by simpa [hhalf] using hkernel0
    have hhalfCast : ((u / 2 : ℕ) : ℝ) = (u : ℝ) / 2 :=
      natCast_div_two_of_even huEven
    have hden : δ * (M : ℝ) / 4 ≤ ((u / 2 : ℕ) : ℝ) + 1 := by
      rw [hhalfCast]
      linarith [huScale]
    have hdenpos : 0 < δ * (M : ℝ) / 4 := by positivity
    calc
      _ ≤ 1 / (((u / 2 : ℕ) : ℝ) + 1) := hkernel'
      _ ≤ 1 / (δ * (M : ℝ) / 4) :=
        one_div_le_one_div_of_le hdenpos hden
      _ = R := by dsimp [R]; field_simp
  have hmassKQ : K * Qvar ≤ Ccoll * Cq / Real.log (M : ℝ) := by
    have hQeq : Qvar = Cq / ((M : ℝ) * Real.log (M : ℝ)) := by
      dsimp [Qvar]
      field_simp
    rw [hQeq]
    dsimp [K]
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    calc
      _ = Ccoll * Cq / Real.log (M : ℝ) := by
        field_simp
      _ ≤ _ := le_rfl
  have hDactual (x : Site) :
      (∫ ω, shortClockEndpointTV (criticalBeta ϑ M) d u x ω ^ 2 ∂disorderLaw) +
        (∫ ω, ∑ w ∈ Polymer.endpoints x u,
          (smoothedEndpointDist (criticalBeta ϑ M) d u x ω w -
            srwKernel u (w - x)) ^ 2 ∂disorderLaw) * K ≤ Dvar := by
    have hvarflat : Integrable
        (fun ω => (smoothedP2Plane (criticalBeta ϑ M) d u x ω - 1) ^ 2) disorderLaw :=
      hvarInt x
    have hTV := integral_shortClockEndpointTV_sq_le (criticalBeta ϑ M) hdu x Qvar
      hvarflat (hvar x)
    have hcoord := integral_shortClockEndpoint_coordinate_sq_le
      (criticalBeta ϑ M) hdu x Qvar R hRpos hvarflat (hvar x)
      (fun z => hkernel x z)
    have hcoordK := mul_le_mul_of_nonneg_right hcoord.2 hK
    have hE := hinc
    have hQ := hvar x
    have hRKC : 0 ≤ CRK := le_of_lt hCRK
    have hmajor :
        (∫ ω, shortClockEndpointTV (criticalBeta ϑ M) d u x ω ^ 2 ∂disorderLaw) +
          (∫ ω, ∑ w ∈ Polymer.endpoints x u,
            (smoothedEndpointDist (criticalBeta ϑ M) d u x ω w -
              srwKernel u (w - x)) ^ 2 ∂disorderLaw) * K ≤
        (16 + 8 * CRK) * (Cexp / Real.log (M : ℝ)) +
          (16 + 8 * CRK) * Qvar + 8 * K * Qvar := by
      calc
        _ ≤ (16 * (Real.exp (((u - d : ℕ) : ℝ) * (criticalBeta ϑ M) ^ 2) - 1) +
              16 * Qvar) +
            (8 * (R * (Real.exp (((u - d : ℕ) : ℝ) * (criticalBeta ϑ M) ^ 2) - 1)) +
              8 * R * Qvar + 8 * Qvar) * K :=
          add_le_add hTV.2 hcoordK
        _ = (16 + 8 * (R * K)) *
              (Real.exp (((u - d : ℕ) : ℝ) * (criticalBeta ϑ M) ^ 2) - 1) +
            (16 + 8 * (R * K)) * Qvar + 8 * K * Qvar := by ring
        _ ≤ _ := by rw [hRK]
        _ ≤ _ := by
          have hQnonneg' : 0 ≤ Qvar := hQvar
          have hC1 : 0 ≤ 16 + 8 * CRK := by positivity
          have hEbound := mul_le_mul_of_nonneg_left hE hC1
          have hQbound := mul_le_mul_of_nonneg_left hQ
            (by positivity : 0 ≤ 16 + 8 * CRK)
          linarith
    have hqExact : (16 + 8 * CRK) * Qvar + 8 * K * Qvar ≤
        ((16 + 8 * CRK) * Cq + 8 * Ccoll * Cq) / Real.log (M : ℝ) := by
      have hMge1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
      have hden : Real.log (M : ℝ) ≤ (M : ℝ) * Real.log (M : ℝ) :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMge1 hlogMpos.le
      have hQrate : Qvar ≤ Cq / Real.log (M : ℝ) := by
        have hQeq : Qvar = Cq / ((M : ℝ) * Real.log (M : ℝ)) := by
          dsimp [Qvar]
          field_simp
        rw [hQeq]
        exact div_le_div_of_nonneg_left hCq.le hlogMpos hden
      have hKrate := hmassKQ
      have hA : 0 ≤ 16 + 8 * CRK := by positivity
      calc
        _ ≤ (16 + 8 * CRK) * (Cq / Real.log (M : ℝ)) +
            8 * (Ccoll * Cq / Real.log (M : ℝ)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hQrate hA
          · calc
              8 * K * Qvar = 8 * (K * Qvar) := by ring
              _ ≤ 8 * (Ccoll * Cq / Real.log (M : ℝ)) :=
                mul_le_mul_of_nonneg_left hKrate (by norm_num)
        _ = _ := by ring

    have hDreal : Dvar = Cd / Real.log (M : ℝ) := by
      dsimp [Dvar]
      ring
    rw [hDreal]
    calc
      _ ≤ (16 + 8 * CRK) * (Cexp / Real.log (M : ℝ)) +
          (16 + 8 * CRK) * Qvar + 8 * K * Qvar := hmajor
      _ = (16 + 8 * CRK) * (Cexp / Real.log (M : ℝ)) +
          ((16 + 8 * CRK) * Qvar + 8 * K * Qvar) := by ring
      _ ≤ (16 + 8 * CRK) * (Cexp / Real.log (M : ℝ)) +
          ((16 + 8 * CRK) * Cq + 8 * Ccoll * Cq) / Real.log (M : ℝ) :=
        add_le_add_right hqExact _
      _ = Cd / Real.log (M : ℝ) := by dsimp [Cd]; field_simp; ring
  have hφbound : ∃ Bφ : ℝ, ∀ x, |φ x| ≤ Bφ := by
    refine ⟨max M₂ 0, ?_⟩
    intro x
    exact (hφM x).trans (le_max_left _ _)
  have hφint : Integrable φ := integrable_of_measurable_compactSupport_bounded hφ hφc hφbound
  have hnormBound : ‖h₀‖ ≤ H₀ := hh₀.trans (le_max_left _ _)
  let f : Site → ℝ := evenExtension (cellAverage M fun y => Real.exp (h₀ y))
  have hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H₀ := by
    intro z
    by_cases hz : Even (z 0 + z 1)
    · have hcell := cellAverage_exp_bounds_of_even M (by omega) h₀ hz
      constructor
      · simpa [f, evenExtension, hz] using hcell.1
      · have hcellLog : |Real.log (f z)| ≤ ‖h₀‖ := by
          simpa [f, evenExtension, hz] using hcell.2
        exact hcellLog.trans hnormBound
    · simp [f, evenExtension, hz, hH₀]
  have hfb : ∀ z, |f z| ≤ F := by
    intro z
    have hz := hf z
    have hlog : Real.log (f z) ≤ H₀ := (abs_le.mp hz.2).2
    calc
      |f z| = f z := abs_of_pos hz.1
      _ = Real.exp (Real.log (f z)) := (Real.exp_log hz.1).symm
      _ ≤ Real.exp H₀ := Real.exp_le_exp.mpr hlog
      _ = F := rfl
  let Bdiag : ℝ := 2 * diagonalLogShiftBound H₀ F Qvar Qflat Dvar
  have hBdiag : 0 ≤ Bdiag := by
    dsimp [Bdiag]
    exact mul_nonneg (by norm_num) (diagonalLogShiftBound_nonneg H₀ F Qvar Qflat Dvar
      hQvar (le_of_lt hQflat) hDvar)
  have hsite (z : Site) :
      eLpNorm (fun ω =>
        (Real.log (profileP2Fun (criticalBeta ϑ M) d M
              (fun w => srwKernel d (w - z)) f ω) -
            Real.log (profileP2Fun (criticalBeta ϑ M) u M
              (fun w => srwKernel u (w - z)) f ω)) -
          ∫ ω', (Real.log (profileP2Fun (criticalBeta ϑ M) d M
                (fun w => srwKernel d (w - z)) (fun _ => 1) ω') -
              Real.log (profileP2Fun (criticalBeta ϑ M) u M
                (fun w => srwKernel u (w - z)) (fun _ => 1) ω')) ∂disorderLaw)
        2 disorderLaw ≤ ENNReal.ofReal Bdiag := by
    have hraw := eLpNorm_centered_log_diagonal_profile_shift_le
      (criticalBeta ϑ M) H₀ F hβ hH₀ hF hFone hdu huM z f hf hfb Qvar hQvar
      (hvarInt z) (hvar z) R hRpos (fun w => hkernel z w) K hK hcollision
      Qflat (le_of_lt hQflat) (hflatInt z) (hflat z) Dvar hDvar (hDactual z)
    simpa [Bdiag] using hraw
  have hdiag := latticeSmoothingError_diagonal_change_le_of_site
    (criticalBeta ϑ M) M d u (by omega) hdu huM hMeven hdEven huEven h₀ φ hφ hφc
    hφbound Bdiag hBdiag hsite
  have hdiagSmallBound : Bdiag * (∫ x, |φ x|) ≤ ε / 3 := by
    have hmassNonneg : 0 ≤ ∫ x, |φ x| :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => abs_nonneg (φ x))
    have hmass : ∫ x, |φ x| ≤ M₁ := hφL1
    have hmassUpper : ∫ x, |φ x| ≤ |M₁| + 1 := by
      linarith [le_abs_self M₁]
    have hLsmall : diagonalLogShiftBound H₀ F Qvar Qflat Dvar < η := by
      simpa [Qvar, Dvar] using hdiagSmallM
    have hBsmall : Bdiag ≤ ε / (3 * (|M₁| + 1)) := by
      dsimp [Bdiag]
      calc
        _ ≤ 2 * η := mul_le_mul_of_nonneg_left hLsmall.le (by norm_num)
        _ = ε / (3 * (|M₁| + 1)) := by
          dsimp [η]
          have hden : |M₁| + 1 ≠ 0 := by positivity
          field_simp
          norm_num
    have hmul := mul_le_mul_of_nonneg_right hBsmall hmassNonneg
    have hmassineq := mul_le_mul_of_nonneg_left hmassUpper
      (show 0 ≤ ε / (3 * (|M₁| + 1)) by positivity)
    have hden : 0 < 3 * (|M₁| + 1) := by positivity
    have hfinal : (ε / (3 * (|M₁| + 1))) * (|M₁| + 1) = ε / 3 := by
      field_simp
    calc
      _ ≤ (ε / (3 * (|M₁| + 1))) * (∫ x, |φ x|) := hmul
      _ ≤ (ε / (3 * (|M₁| + 1))) * (|M₁| + 1) := hmassineq
      _ = ε / 3 := hfinal
  have hdiagReduced := hdiag.2.trans (ENNReal.ofReal_le_ofReal hdiagSmallBound)
  have hdiagFinal : eLpNorm (fun ω =>
      latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω -
        latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ ω)
      2 disorderLaw ≤ ENNReal.ofReal ε := by
    rcases le_total k m with h | h
    · have hdEq : d = k := by simp [d, h]
      have huEq : u = m := by simp [u, h]
      have hsmall := hdiagReduced.trans
        (ENNReal.ofReal_le_ofReal (by linarith : ε / 3 ≤ ε))
      simpa only [hdEq, huEq] using hsmall
    · have hdEq : d = m := by simp [d, h]
      have huEq : u = k := by simp [u, h]
      have hneg : (fun ω =>
          latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω -
            latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ ω) =
          -fun ω => latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ ω -
            latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω := by
        funext ω
        change latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω -
            latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ ω =
          -(latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ ω -
            latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω)
        ring
      rw [hneg, eLpNorm_neg]
      have hsmall := hdiagReduced.trans
        (ENNReal.ofReal_le_ofReal (by linarith : ε / 3 ≤ ε))
      simpa only [hdEq, huEq] using hsmall
  simpa only [m] using hdiagFinal

/-- The perturbation estimate follows from two same-start width changes and the diagonal time
change. -/
theorem latticeSmoothingError_perturb_le : LatticeSmoothingPerturbBound := by
  intro A H M₁ M₂ δ hδ hδ1 ε hε
  let H₀ : ℝ := max H 0
  have hH₀ : 0 ≤ H₀ := by dsimp [H₀]; positivity
  have hε3 : 0 < ε / 3 := by linarith
  have hwidthEvent := latticeSmoothingError_sameStart_width_small_of_close_even_widths
    A H₀ M₁ M₂ δ hH₀ hδ (ε / 3) hε3
  have hdiagEvent := latticeSmoothingError_diagonal_change_small
    A H M₁ M₂ δ hδ hδ1 (ε / 3) hε3
  have hthreshold : ∀ᶠ M : ℕ in atTop,
      12 ≤ δ * (M : ℝ) ∧ 8 ≤ (1 - δ) * (M : ℝ) := by
    have hM := tendsto_natCast_atTop_atTop.eventually_gt_atTop
      (max (12 / δ) (8 / (1 - δ)))
    filter_upwards [hM] with M hM
    have hMcast : max (12 / δ) (8 / (1 - δ)) < (M : ℝ) := hM
    have hδM : 12 ≤ δ * (M : ℝ) := by
      have h := lt_of_le_of_lt (le_max_left _ _) hMcast
      have h' := (div_lt_iff₀ hδ).mp h
      exact h'.le.trans_eq (mul_comm _ _)
    have hmargin : 8 ≤ (1 - δ) * (M : ℝ) := by
      have hδ' : 0 < 1 - δ := by linarith
      have h := lt_of_le_of_lt (le_max_right _ _) hMcast
      have h' := (div_lt_iff₀ hδ').mp h
      exact h'.le.trans_eq (mul_comm _ _)
    exact ⟨hδM, hmargin⟩
  filter_upwards [hwidthEvent, hdiagEvent, hthreshold] with M hwidthM hdiagM hthresholdM
  intro hMeven ϑ hϑ j k hj hk hjlo hjhi hklo hkhi h₀ hh₀ φ hφ hφc hφL1 hφM
  let m : ℕ := evenCeil (δ * (M : ℝ))
  have hmEven : Even m := evenCeil_even _
  have hmCastLower : δ * (M : ℝ) ≤ (m : ℝ) := by
    dsimp [m]
    exact Critical2DKPZ.le_evenCeil _
  have hmCastUpper : (m : ℝ) < δ * (M : ℝ) + 2 := by
    dsimp [m]
    exact evenCeil_lt_add_two (by positivity)
  have hm6Mcast : (m : ℝ) + 6 ≤ (M : ℝ) := by linarith [hmCastUpper, hthresholdM.2]
  have hm6M : m + 6 ≤ M := by exact_mod_cast hm6Mcast
  have hmM : m ≤ M := by omega
  have hjmInt : (j : ℤ) ≤ (m : ℤ) + 6 := by simpa [m] using hjlo
  have hmjInt : (m : ℤ) ≤ (j : ℤ) + 6 := by simpa [m] using hjhi
  have hkmInt : (k : ℤ) ≤ (m : ℤ) + 6 := by simpa [m] using hklo
  have hmkInt : (m : ℤ) ≤ (k : ℤ) + 6 := by simpa [m] using hkhi
  have hjm : j ≤ m + 6 := by omega
  have hmj : m ≤ j + 6 := by omega
  have hkm : k ≤ m + 6 := by omega
  have hmk : m ≤ k + 6 := by omega
  have hkM : k ≤ M := by omega
  have hjLower : δ * (M : ℝ) / 2 ≤ (j : ℝ) := by
    have hjreal : (m : ℝ) ≤ (j : ℝ) + 6 := by exact_mod_cast hmj
    linarith [hthresholdM.1, hmCastLower]
  have hkLower : δ * (M : ℝ) / 2 ≤ (k : ℝ) := by
    have hkreal : (m : ℝ) ≤ (k : ℝ) + 6 := by exact_mod_cast hmk
    linarith [hthresholdM.1, hmCastLower]
  have hjhalf := natCast_div_two_of_even hj
  have hmhalf := natCast_div_two_of_even hmEven
  have hkhalf := natCast_div_two_of_even hk
  have hminJM : δ * (M : ℝ) / 4 ≤ min ((j / 2 : ℕ) : ℝ) ((m / 2 : ℕ) : ℝ) := by
    rw [hjhalf, hmhalf]
    exact le_min (by linarith [hjLower]) (by linarith [hmCastLower])
  have hminMK : δ * (M : ℝ) / 4 ≤ min ((m / 2 : ℕ) : ℝ) ((k / 2 : ℕ) : ℝ) := by
    rw [hmhalf, hkhalf]
    exact le_min (by linarith [hmCastLower]) (by linarith [hkLower])
  have hminJM' : δ * (M : ℝ) / 4 ≤ min ((j : ℝ) / 2) ((m : ℝ) / 2) := by
    simpa only [hjhalf, hmhalf] using hminJM
  have hminMK' : δ * (M : ℝ) / 4 ≤ min ((m : ℝ) / 2) ((k : ℝ) / 2) := by
    simpa only [hmhalf, hkhalf] using hminMK
  have hh₀' : ‖h₀‖ ≤ H₀ := hh₀.trans (le_max_left _ _)
  have hwidth1 := hwidthM hMeven ϑ hϑ k j m hk hkM hj hmEven
    hjmInt hmjInt hminJM' h₀ hh₀' φ hφ hφc hφL1 hφM
  have hwidth2 := hwidthM hMeven ϑ hϑ k m k hk hkM hmEven hk
    hmkInt hkmInt hminMK' h₀ hh₀' φ hφ hφc hφL1 hφM
  have hdiag := hdiagM hMeven ϑ hϑ k hk hklo hkhi h₀ hh₀ φ hφ hφc hφL1 hφM
  let p₁ : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ φ ω -
      latticeSmoothingError (criticalBeta ϑ M) M M k m h₀ φ ω
  let p₂ : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M k m h₀ φ ω -
      latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω
  let p₃ : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M k k h₀ φ ω -
      latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ ω
  let e : Disorder → ℝ := fun ω => p₁ ω + p₂ ω + p₃ ω
  have heq : (fun ω =>
      latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ φ ω -
        latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ ω) = e := by
    funext ω
    dsimp [e, p₁, p₂, p₃]
    ring
  have hp₁ : eLpNorm p₁ 2 disorderLaw ≤ ENNReal.ofReal (ε / 3) := by
    simpa only [p₁] using hwidth1
  have hp₂ : eLpNorm p₂ 2 disorderLaw ≤ ENNReal.ofReal (ε / 3) := by
    simpa only [p₂] using hwidth2
  have hp₃ : eLpNorm p₃ 2 disorderLaw ≤ ENNReal.ofReal (ε / 3) := by
    simpa only [m, p₃] using hdiag
  have htriangle₁ : eLpNorm (p₁ + p₂) 2 disorderLaw ≤
      eLpNorm p₁ 2 disorderLaw + eLpNorm p₂ 2 disorderLaw :=
    eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
  have htriangle₂ : eLpNorm ((p₁ + p₂) + p₃) 2 disorderLaw ≤
      eLpNorm (p₁ + p₂) 2 disorderLaw + eLpNorm p₃ 2 disorderLaw :=
    eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
  have hsumenn : ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) +
      ENNReal.ofReal (ε / 3) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ = eLpNorm e 2 disorderLaw := by rw [heq]
    _ ≤ eLpNorm (p₁ + p₂) 2 disorderLaw + eLpNorm p₃ 2 disorderLaw := htriangle₂
    _ ≤ (eLpNorm p₁ 2 disorderLaw + eLpNorm p₂ 2 disorderLaw) +
        eLpNorm p₃ 2 disorderLaw := add_le_add htriangle₁ (le_refl _)
    _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) +
        ENNReal.ofReal (ε / 3) := by
      exact add_le_add (add_le_add hp₁ hp₂) hp₃
    _ = ENNReal.ofReal ε := hsumenn

/-- `latticeSmoothingError_unit_le_of`'s conclusion, as a proposition. For every `A, H, M₁, M₂`
there are `C` and `δ₁ > 0`, depending only on them, such that for all `δ < δ₁` and `ε > 0`, for
all large even `M`, uniformly in `ϑ, j, k, h₀, φ` as in `LatticeSmoothingPerturbBound`, the `L²`
norm of the lattice smoothing error is at most `C |log δ| ^ (-1/40) + ε`. -/
def LatticeSmoothingUnitBound : Prop := ∀ (A H M₁ M₂ : ℝ),
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, Even M →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ j k : ℕ, Even j → Even k →
        (j : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ j + 6 →
        (k : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ k + 6 →
        ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H → ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ → (∫ x, |φ x| ≤ M₁) →
          (∀ x, |φ x| ≤ M₂) →
          eLpNorm (latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ φ) 2 disorderLaw ≤
            ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε)

/-- The unit bound follows by adding the perturbation estimate to the diagonal bound. -/
theorem latticeSmoothingError_unit_le_of_perturb (hP : LatticeSmoothingPerturbBound)
    (hVD : PropVDBound) (hO : FutureProfiles.PropPFOriginBound)
    (hL : FutureProfiles.LogTailsOriginBound) : LatticeSmoothingUnitBound := by
  intro A H M₁ M₂
  obtain ⟨CD, δD, hδD, hD⟩ := latticeSmoothingError_diagonal_unit_le_of hVD hO hL A H M₁ M₂
  let C : ℝ := |CD| + 1
  let δ₁ : ℝ := min δD 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCD : CD ≤ C := by dsimp [C]; linarith [le_abs_self CD]
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  refine ⟨C, δ₁, hδ₁, ?_⟩
  intro δ hδ hδ₁' ε hε
  have hδD' : δ < δD := lt_of_lt_of_le hδ₁' (min_le_left _ _)
  have hδone : δ < 1 := lt_of_lt_of_le hδ₁' (min_le_right _ _)
  have hεhalf : 0 < ε / 2 := by linarith
  have hPevent := hP A H M₁ M₂ δ hδ hδone (ε / 2) hεhalf
  have hDevent := hD δ hδ hδD' (ε / 2) hεhalf
  filter_upwards [hPevent, hDevent] with M hPbound hDbound
  intro hMeven ϑ hϑ j k hj hk hjlo hjhi hklo hkhi h₀ hh₀ φ hφ hφc hφL1 hφM
  let p : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ φ ω -
      latticeSmoothingError (criticalBeta ϑ M) M M (evenCeil (δ * M))
        (evenCeil (δ * M)) h₀ φ ω
  let d : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M
      (evenCeil (δ * M)) (evenCeil (δ * M)) h₀ φ ω
  let e : Disorder → ℝ := fun ω =>
    latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ φ ω
  have hpbound : eLpNorm p 2 disorderLaw ≤ ENNReal.ofReal (ε / 2) := by
    simpa only [p] using
      hPbound hMeven ϑ hϑ j k hj hk hjlo hjhi hklo hkhi h₀ hh₀ φ hφ hφc hφL1 hφM
  have hpow : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hDbound' : eLpNorm d 2 disorderLaw ≤
      ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) := by
    have hraw := hDbound hMeven ϑ hϑ h₀ hh₀ φ hφ hφc hφL1 hφM
    apply hraw.trans
    apply ENNReal.ofReal_le_ofReal
    have hcoeff := mul_le_mul_of_nonneg_right hCD hpow
    dsimp [C]
    linarith
  have hdecomp : e = p + d := by
    funext ω
    dsimp [e, p, d]
    ring
  have htriangle : eLpNorm (p + d) 2 disorderLaw ≤
      eLpNorm p 2 disorderLaw + eLpNorm d 2 disorderLaw :=
    eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have htargetNonneg : 0 ≤ C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 := by
    positivity
  calc
    eLpNorm e 2 disorderLaw = eLpNorm (p + d) 2 disorderLaw := by rw [hdecomp]
    _ ≤ ENNReal.ofReal (ε / 2) +
        ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) :=
      htriangle.trans (add_le_add hpbound hDbound')
    _ = ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
      rw [← ENNReal.ofReal_add (by positivity) htargetNonneg]
      congr 1
      ring


/-- The diagonal estimate and bounded width-perturbation estimate imply the unit-horizon logarithmic smoothing bound. -/
theorem latticeSmoothingError_unit_le_of (hVD : PropVDBound)
    (hO : FutureProfiles.PropPFOriginBound) (hL : FutureProfiles.LogTailsOriginBound)
    (A H M₁ M₂ : ℝ) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ M : ℕ in atTop, Even M →
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ j k : ℕ, Even j → Even k →
          (j : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ j + 6 →
          (k : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ k + 6 →
          ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H → ∀ φ : Plane → ℝ, Measurable φ →
            HasCompactSupport φ → (∫ x, |φ x| ≤ M₁) → (∀ x, |φ x| ≤ M₂) →
              eLpNorm (latticeSmoothingError (criticalBeta ϑ M) M M k j h₀ φ)
                2 disorderLaw ≤
                ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  exact (latticeSmoothingError_unit_le_of_perturb latticeSmoothingError_perturb_le
    hVD hO hL) A H M₁ M₂


end Critical2DKPZ.Smoothing

end
