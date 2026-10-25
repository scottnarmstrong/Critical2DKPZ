/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.HeatEnergyLogBound
public import Critical2DKPZ.Smoothing.SmoothingClockBounds
public import Critical2DKPZ.Smoothing.ParameterRescaling
public import Critical2DKPZ.Smoothing.Rescaling
public import Critical2DKPZ.Smoothing.TimeShift
public import Critical2DKPZ.Smoothing.UnitHorizonPerturbed

/-! # Lattice bounds for shrinking regularized reversed fields -/

@[expose] public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.SmallScales

open Critical2DKPZ.Smoothing

private theorem eLpNorm_lattice_difference_eq_smoothingError (ϑ : ℝ) (N : ℕ)
    {T η : ℝ} (hη : 0 < η) (hηT : η < T) (φ : TestFn) :
    eLpNorm (fun ω => ∫ y, φ y *
      (kpzLatticeReversed ϑ N 0 T 0 y ω - kpzLatticeReversedReg ϑ N 0 T η 0 y ω))
      2 disorderLaw =
    eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T))
      (evenCeil (N * η)) (evenCeil (η * N)) 0 φ) 2 disorderLaw := by
  let f : Disorder → ℝ := fun ω => ∫ y, φ y *
    (kpzLatticeReversed ϑ N 0 T 0 y ω - kpzLatticeReversedReg ϑ N 0 T η 0 y ω)
  let g : Disorder → ℝ := latticeSmoothingError (criticalBeta ϑ N) N
    (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0 φ
  have hfg : f = g ∘ shiftEnvironment 0 := by
    funext ω
    have hdiff := kpzLattice_difference_timeShift ϑ N (t := (0 : ℝ)) (T := T) (δ := η)
      (by norm_num) hη (by simpa using hηT) 0 φ ω
    change (∫ y, φ y * (kpzLatticeReversed ϑ N 0 T 0 y ω -
      kpzLatticeReversedReg ϑ N 0 T η 0 y ω)) = _
    rw [hdiff]
    simp [g, evenCeil_zero]
  have hfm : Measurable f := by
    rw [hfg]
    exact (measurable_latticeSmoothingError (criticalBeta ϑ N) N
      (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0
      (φ := φ) φ.continuous.measurable).comp (measurable_shiftEnvironment 0)
  have hgm : Measurable g := measurable_latticeSmoothingError (criticalBeta ϑ N) N
    (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0
    (φ := φ) φ.continuous.measurable
  have hmap (F : Disorder → ℝ) (hF : Measurable F) :
      eLpNorm F 2 disorderLaw = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map F) := by
    symm
    simpa only [Function.comp_def] using
      (eLpNorm_map_measure (μ := disorderLaw) (p := (2 : ENNReal))
        (f := F) (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
        hF.aemeasurable)
  calc
    eLpNorm f 2 disorderLaw = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map f) := hmap f hfm
    _ = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map g) := by
      rw [kpzLattice_difference_timeShift_law ϑ N (t := (0 : ℝ)) (T := T) (δ := η)
        (by norm_num) hη (by simpa using hηT) 0 φ]
      simp [g, evenCeil_zero]
    _ = eLpNorm g 2 disorderLaw := (hmap g hgm).symm

/-- One lattice smoothing error for a test at scale `ε` has a uniform `L²` bound when
the regularization width is at most `ε²`. -/
theorem kpzLatticeReversed_error_le_uniform_of (hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (ϑ T : ℝ) (hT : 0 < T) (φ : TestFn) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x : Plane,
      ∀ η : ℝ, 0 < η → η ≤ ε ^ 2 →
        ∀ᶠ N : ℕ in atTop,
          eLpNorm (fun ω => ∫ y, φ.dilate ε x y *
            (kpzLatticeReversed ϑ N 0 T 0 y ω -
              kpzLatticeReversedReg ϑ N 0 T η 0 y ω)) 2 disorderLaw ≤ ENNReal.ofReal C := by
  obtain ⟨Braw, hBraw⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  let B : ℝ := |Braw| + 1
  have hB : ∀ y : Plane, |φ y| ≤ B := by
    intro y
    have hy := hBraw y
    rw [Real.norm_eq_abs] at hy
    dsimp [B]
    calc
      |φ y| ≤ Braw := hy
      _ ≤ |Braw| := le_abs_self _
      _ ≤ |Braw| + 1 := le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  let m : ℝ := ∫ y, |φ y|
  have hm : 0 ≤ m := by
    dsimp [m]
    exact integral_nonneg fun y => abs_nonneg _
  obtain ⟨A', hcritical⟩ := criticalBeta_rescale |ϑ| T (T + 1) hT
  obtain ⟨C₀, δ₀, hδ₀, hLatticeSmoothingEnergyInputBound⟩ := hLatticeSmoothingEnergyInput A' 0
  let D₀ : ℝ := (T + 1) / Real.sqrt T
  let L₀ : ℝ := |Real.log T| + |Real.log D₀| + 2
  let ε₀ : ℝ := min (Real.exp (-L₀)) (Real.sqrt (T * min δ₀ (Real.exp (-1))) / 2)
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  have hδsmall : 0 < min δ₀ (Real.exp (-1)) := by positivity
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  let Cbar : ℝ := |C₀| + 1
  let Ebar : ℝ := 4 * B * m + 2 * m ^ 2 / Real.pi
  let C : ℝ := Real.sqrt (Cbar * Ebar) + Cbar * m + 1
  have hCbar : 0 < Cbar := by dsimp [Cbar]; positivity
  have hEbar : 0 ≤ Ebar := by dsimp [Ebar]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro ε hε hε₀' x η hη hηε
  have hεexp : ε < Real.exp (-L₀) := by
    exact (lt_of_lt_of_le hε₀' (min_le_left _ _))
  have hL : L₀ < Real.log ε⁻¹ := by
    have hlog := Real.log_lt_log hε hεexp
    rw [Real.log_exp] at hlog
    calc
      L₀ < -Real.log ε := by linarith [hlog]
      _ = Real.log ε⁻¹ := (Real.log_inv ε).symm
  have hLpos : 0 < Real.log ε⁻¹ := by linarith [hL]
  have hL2 : |Real.log T| + |Real.log D₀| + 2 < Real.log ε⁻¹ := by
    simpa [L₀] using hL
  have hLone : 1 ≤ Real.log ε⁻¹ := by
    linarith [hL2, abs_nonneg (Real.log T), abs_nonneg (Real.log D₀)]
  have hLlogT : |Real.log T| ≤ Real.log ε⁻¹ := by
    linarith [hL2, abs_nonneg (Real.log D₀)]
  have hLlogD : |Real.log D₀| ≤ Real.log ε⁻¹ := by
    linarith [hL2, abs_nonneg (Real.log T)]
  have hεsqBound : ε ^ 2 / T < min δ₀ (Real.exp (-1)) := by
    have hεroot : ε < Real.sqrt (T * min δ₀ (Real.exp (-1))) / 2 :=
      lt_of_lt_of_le hε₀' (min_le_right _ _)
    have hrootSq : (Real.sqrt (T * min δ₀ (Real.exp (-1))) / 2) ^ 2 =
        T * min δ₀ (Real.exp (-1)) / 4 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt (mul_pos hT hδsmall))]
      ring
    have hprod : ε ^ 2 < T * min δ₀ (Real.exp (-1)) := by
      nlinarith [hrootSq, sq_nonneg (ε - Real.sqrt (T * min δ₀ (Real.exp (-1))) / 2)]
    exact (div_lt_iff₀ hT).2 (by simpa [mul_comm] using hprod)
  have hεT : ε ^ 2 < T := by
    have hmin : min δ₀ (Real.exp (-1)) ≤ Real.exp (-1) := min_le_right _ _
    have hdiv : ε ^ 2 / T < Real.exp (-1) := hεsqBound.trans_le hmin
    have hexp : Real.exp (-1) < 1 := by norm_num [Real.exp_lt_one_iff]
    exact (div_lt_one hT).1 (hdiv.trans hexp)
  have hηd : 0 < η / T := div_pos hη hT
  have hηdle : η / T ≤ ε ^ 2 / T := div_le_div_of_nonneg_right hηε (le_of_lt hT)
  have hηdSmall : η / T < min δ₀ (Real.exp (-1)) := hηdle.trans_lt hεsqBound
  have hηδ₀ : η / T < δ₀ := hηdSmall.trans_le (min_le_left _ _)
  have hηexp : η / T < Real.exp (-1) := hηdSmall.trans_le (min_le_right _ _)
  have hlogηneg : Real.log (η / T) < -1 := by
    calc
      Real.log (η / T) < Real.log (Real.exp (-1)) := Real.log_lt_log hηd hηexp
      _ = -1 := Real.log_exp _
  have hDenone : 1 ≤ |Real.log (η / T)| := by
    rw [abs_of_neg (lt_trans hlogηneg (by norm_num : (-1 : ℝ) < 0))]
    linarith
  have hηratio : η / T ≤ ε ^ 2 / T := hηdle
  have hlogratio : Real.log (ε ^ 2 / T) = -2 * Real.log ε⁻¹ - Real.log T := by
    rw [Real.log_div (pow_ne_zero 2 hε.ne') hT.ne', Real.log_pow ε 2, Real.log_inv]
    ring
  have hlogηupper : Real.log (η / T) ≤ -2 * Real.log ε⁻¹ - Real.log T := by
    calc
      Real.log (η / T) ≤ Real.log (ε ^ 2 / T) := Real.log_le_log hηd hηratio
      _ = -2 * Real.log ε⁻¹ - Real.log T := hlogratio
  have hDenL : Real.log ε⁻¹ ≤ |Real.log (η / T)| := by
    rw [abs_of_neg (lt_trans hlogηneg (by norm_num : (-1 : ℝ) < 0))]
    have hTlow : -Real.log ε⁻¹ ≤ Real.log T := by
      calc
        -Real.log ε⁻¹ ≤ -|Real.log T| := by linarith [hLlogT]
        _ ≤ Real.log T := neg_abs_le _
    linarith
  let Mfun : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * T)
  have hMlim : Tendsto Mfun atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    have hN : ∀ᶠ N : ℕ in atTop, (n : ℝ) ≤ (N : ℝ) * T := by
      filter_upwards [
        (tendsto_natCast_atTop_atTop.const_mul_atTop hT).eventually
          (eventually_ge_atTop (n : ℝ))] with N hN
      simpa [mul_comm] using hN
    filter_upwards [hN] with N hN
    have hround := le_evenCeil ((N : ℝ) * T)
    exact_mod_cast hN.trans hround
  have hcriticalN := hcritical
  have hNlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  let base : TestFn := φ.dilate ε x
  have hbaseMeas : Measurable (base : Plane → ℝ) := base.continuous.measurable
  have hbaseCompact : HasCompactSupport (base : Plane → ℝ) := base.hasCompactSupport
  have hbaseInt : Integrable (base : Plane → ℝ) :=
    base.continuous.integrable_of_hasCompactSupport base.hasCompactSupport
  obtain ⟨Brawε, hBrawε⟩ := base.continuous.bounded_above_of_compact_support base.hasCompactSupport
  let Bε : ℝ := |Brawε| + 1
  have hBε : ∀ y : Plane, |base y| ≤ Bε := by
    intro y
    have hy := hBrawε y
    rw [Real.norm_eq_abs] at hy
    dsimp [Bε]
    calc
      |base y| ≤ Brawε := hy
      _ ≤ |Brawε| := le_abs_self _
      _ ≤ |Brawε| + 1 := le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  have hψevent : ∀ᶠ M : ℕ in atTop,
      Even M → ∀ c ∈ Set.Icc T (T + 1), ∀ θ ∈ Set.Icc (-A') A',
        ∀ j k : ℕ, Even j → Even k →
          (j : ℤ) ≤ evenCeil ((η / T) * M) + 6 →
          (evenCeil ((η / T) * M) : ℤ) ≤ j + 6 →
          (k : ℤ) ≤ evenCeil ((η / T) * M) + 6 →
          (evenCeil ((η / T) * M) : ℤ) ≤ k + 6 →
          ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ 0 →
            eLpNorm (latticeSmoothingError (criticalBeta θ M) M M k j h₀
              (fun y => c * base (Real.sqrt c • y))) 2 disorderLaw ≤
              ENNReal.ofReal (Real.sqrt
                (C₀ * heatEnergy (Real.sqrt (η / T))
                    (fun y => c * base (Real.sqrt c • y)) / |Real.log (η / T)|) +
                C₀ * (∫ y, |c * base (Real.sqrt c • y)|) *
                    |Real.log (η / T)| ^ (-(1 : ℝ) / 40) + 1) := by
    filter_upwards [hLatticeSmoothingEnergyInputBound (η / T) hηd hηδ₀ base hbaseMeas hbaseCompact hbaseInt
      ⟨Bε, hBε⟩ T (T + 1) hT 1 (by norm_num)] with M hM
    exact hM
  have hψeventN := hMlim.eventually hψevent
  have hcriticalN' := hcriticalN
  have hbaseMass : (∫ y, |base y|) = m := by
    dsimp [base]
    exact integral_abs_testFn_dilate_eq φ hε x
  filter_upwards [hψeventN, hcriticalN', hNlarge] with N hψN hcritN hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let M : ℕ := Mfun N
  have hMreal : (0 : ℝ) < M := by
    apply lt_of_lt_of_le _ (le_evenCeil ((N : ℝ) * T))
    positivity
  have hMpos : 0 < M := by exact_mod_cast hMreal
  have hMeven : Even M := evenCeil_even _
  have hMlo : T * (N : ℝ) ≤ (M : ℝ) := by
    simpa [M, Mfun, mul_comm] using le_evenCeil ((N : ℝ) * T)
  have hMhi : (M : ℝ) ≤ (T + 1) * (N : ℝ) := by
    have herr := evenCeil_error (mul_nonneg hNreal.le hT.le)
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [herr.2]
  obtain ⟨θ, hθ, hβ⟩ := hcritN ϑ
    (abs_le.mp (le_rfl : |ϑ| ≤ |ϑ|)) M hMlo hMhi
  let c : ℝ := (M : ℝ) / N
  have hc : c ∈ Set.Icc T (T + 1) := by
    constructor
    · exact (le_div_iff₀ hNreal).2 hMlo
    · exact (div_le_iff₀ hNreal).2 hMhi
  let j : ℕ := evenCeil (η * (N : ℝ))
  let k : ℕ := evenCeil ((N : ℝ) * η)
  have hj : Even j := evenCeil_even _
  have hk : Even k := evenCeil_even _
  have hwidth := c11_widths_within_six (N := N) (t := (0 : ℝ)) (T := T)
    (δ := η) (a := T) (by norm_num) hT (by simp) hη
    (le_of_lt (lt_of_le_of_lt hηε hεT))
  have hJlo : (j : ℤ) ≤ evenCeil ((η / T) * M) + 6 := by
    simpa [j, M, Mfun] using hwidth.1
  have hJhi : (evenCeil ((η / T) * M) : ℤ) ≤ j + 6 := by
    simpa [j, M, Mfun] using hwidth.2.1
  have hKlo : (k : ℤ) ≤ evenCeil ((η / T) * M) + 6 := by
    simpa [k, j, M, Mfun, mul_comm] using hwidth.1
  have hKhi : (evenCeil ((η / T) * M) : ℤ) ≤ k + 6 := by
    simpa [k, j, M, Mfun, mul_comm] using hwidth.2.1
  have hunit := hψN hMeven c hc θ hθ j k hj hk hJlo hJhi hKlo hKhi 0 (by simp)
  have hηT : η < T := by
    have hηlt : η ≤ ε ^ 2 := hηε
    have hepsT : ε ^ 2 < T := by
      have hsquare := hεsqBound
      have hminle : min δ₀ (Real.exp (-1)) ≤ Real.exp (-1) := min_le_right _ _
      have he : ε ^ 2 / T < Real.exp (-1) := hsquare.trans_le hminle
      have hexp : Real.exp (-1) < 1 := by norm_num [Real.exp_lt_one_iff]
      have : ε ^ 2 / T < 1 := he.trans hexp
      exact (div_lt_one hT).1 this
    exact lt_of_le_of_lt hηlt hepsT
  have herrNorm := eLpNorm_lattice_difference_eq_smoothingError ϑ N hη hηT base
  have hscaleEq : ∀ ω : Disorder,
      latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T))
          (evenCeil (N * η)) (evenCeil (η * N)) 0 base ω =
        latticeSmoothingError (criticalBeta θ M) M M k j 0
          (fun y => c * base (Real.sqrt c • y)) ω := by
    intro ω
    have hscale := latticeSmoothingError_rescale (criticalBeta ϑ N)
      (by exact_mod_cast (show 0 < N by omega)) hMpos
      (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0 base ω
    have hβ' : criticalBeta ϑ N = criticalBeta θ M := hβ
    simpa [c, M, Mfun, j, k, hβ', mul_comm] using hscale
  have hscaledNorm :
      eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T))
        (evenCeil (N * η)) (evenCeil (η * N)) 0 base) 2 disorderLaw =
      eLpNorm (latticeSmoothingError (criticalBeta θ M) M M k j 0
        (fun y => c * base (Real.sqrt c • y))) 2 disorderLaw := by
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall hscaleEq
  have hbaseDilate : (fun y => c * base (Real.sqrt c • y)) =
      (φ.dilate (ε / Real.sqrt c) ((Real.sqrt c)⁻¹ • x) : Plane → ℝ) := by
    funext y
    change c * (ε⁻¹ ^ 2 * φ (ε⁻¹ • (Real.sqrt c • y - x))) =
      (ε / Real.sqrt c)⁻¹ ^ 2 *
        φ ((ε / Real.sqrt c)⁻¹ • (y - (Real.sqrt c)⁻¹ • x))
    have hr : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 (lt_of_lt_of_le hT hc.1)).ne'
    have hsqrt : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (le_of_lt (lt_of_lt_of_le hT hc.1))
    have harg : (ε / Real.sqrt c)⁻¹ • (y - (Real.sqrt c)⁻¹ • x) =
        ε⁻¹ • (Real.sqrt c • y - x) := by
      have hInvDiv : (ε / Real.sqrt c)⁻¹ = ε⁻¹ * Real.sqrt c := by field_simp
      have hcancel : (ε⁻¹ * Real.sqrt c) * (Real.sqrt c)⁻¹ = ε⁻¹ := by field_simp
      rw [hInvDiv]
      simp_rw [smul_sub, smul_smul]
      rw [hcancel]
    rw [harg]
    have hcoeff : c * ε⁻¹ ^ 2 = (ε / Real.sqrt c)⁻¹ ^ 2 := by
      rw [show (ε / Real.sqrt c)⁻¹ = ε⁻¹ * Real.sqrt c by field_simp, mul_pow]
      field_simp [hε.ne', hr]
      exact hsqrt.symm
    calc
      c * (ε⁻¹ ^ 2 * φ (ε⁻¹ • (Real.sqrt c • y - x))) =
          (c * ε⁻¹ ^ 2) * φ (ε⁻¹ • (Real.sqrt c • y - x)) := by ring
      _ = (ε / Real.sqrt c)⁻¹ ^ 2 * φ (ε⁻¹ • (Real.sqrt c • y - x)) := by rw [hcoeff]
  have hαpos : 0 < ε / Real.sqrt c := div_pos hε (Real.sqrt_pos.2 (lt_of_lt_of_le hT hc.1))
  have hbaseMass' : (∫ y, |c * base (Real.sqrt c • y)|) = m := by
    calc
      (∫ y, |c * base (Real.sqrt c • y)|) = ∫ y, |base y| :=
        integral_abs_dilate_eq base hbaseInt (lt_of_lt_of_le hT hc.1)
      _ = m := hbaseMass
  have henergyPos : 0 ≤ heatEnergy (Real.sqrt (η / T))
      (fun y => c * base (Real.sqrt c • y)) := by
    rw [hbaseDilate]
    have hbound : ∀ y, |(φ.dilate (ε / Real.sqrt c) ((Real.sqrt c)⁻¹ • x) : Plane → ℝ) y| ≤
        (ε / Real.sqrt c)⁻¹ ^ 2 * B := by
      intro y
      change |(ε / Real.sqrt c)⁻¹ ^ 2 * φ ((ε / Real.sqrt c)⁻¹ •
        (y - (Real.sqrt c)⁻¹ • x))| ≤ _
      rw [abs_mul, abs_of_pos (sq_pos_of_pos (inv_pos.mpr hαpos))]
      exact mul_le_mul_of_nonneg_left (hB _) (sq_nonneg _)
    exact (heatEnergy_le_of_bounded _ (φ.dilate _ _).continuous.measurable
      ((φ.dilate _ _).continuous.integrable_of_hasCompactSupport (φ.dilate _ _).hasCompactSupport)
      ((ε / Real.sqrt c)⁻¹ ^ 2 * B) hbound (Real.sqrt_pos.2 hηd)).1
  have hlogargBound :
      max 0 (Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2)) ≤
        2 * Real.log ε⁻¹ := by
    have hsqrtη : Real.sqrt (η / T) ≤ ε / Real.sqrt T := by
      calc
        Real.sqrt (η / T) ≤ Real.sqrt (ε ^ 2 / T) := Real.sqrt_le_sqrt hηdle
        _ = ε / Real.sqrt T := by
          calc
            Real.sqrt (ε ^ 2 / T) = Real.sqrt (ε ^ 2) / Real.sqrt T := by
              rw [Real.sqrt_div' _ hT.le]
            _ = ε / Real.sqrt T := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]
    have hratio : (Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2 ≤ D₀ / ε := by
      have hαsq : (ε / Real.sqrt c) ^ 2 = ε ^ 2 / c := by
        rw [div_pow, Real.sq_sqrt (le_of_lt (lt_of_lt_of_le hT hc.1))]
      rw [hαsq]
      have hnum : c * Real.sqrt (η / T) ≤ (T + 1) * (ε / Real.sqrt T) :=
        mul_le_mul hc.2 hsqrtη (Real.sqrt_nonneg _) (by positivity)
      have hratio' : Real.sqrt (η / T) / (ε ^ 2 / c) =
          (c * Real.sqrt (η / T)) / ε ^ 2 := by field_simp
      rw [hratio']
      have hbound := div_le_div_of_nonneg_right hnum (sq_nonneg ε)
      have hεpossq : 0 < ε ^ 2 := sq_pos_of_pos hε
      calc
        (c * Real.sqrt (η / T)) / ε ^ 2 ≤
            ((T + 1) * (ε / Real.sqrt T)) / ε ^ 2 := hbound
        _ = D₀ / ε := by
          dsimp [D₀]
          field_simp [ne_of_gt hε, ne_of_gt (Real.sqrt_pos.2 hT)]
    have hlog : Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2) ≤
        Real.log ε⁻¹ + |Real.log D₀| := by
      have hposarg : 0 < (Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2 := by positivity
      have hposD : 0 < D₀ / ε := div_pos hD₀ hε
      calc
        Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2) ≤ Real.log (D₀ / ε) :=
          Real.log_le_log hposarg (by exact hratio)
        _ = Real.log D₀ + Real.log ε⁻¹ := by
          rw [Real.log_div hD₀.ne' hε.ne', Real.log_inv ε]
          ring
        _ ≤ Real.log ε⁻¹ + |Real.log D₀| := by linarith [le_abs_self (Real.log D₀)]
    have hmax : max 0 (Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2)) ≤
        Real.log ε⁻¹ + |Real.log D₀| := by
      apply max_le
      · positivity
      · exact hlog
    dsimp [L₀] at hL
    linarith [hmax]
  have henergyBound := heatEnergy_testFn_dilate_le_log φ B hB
    ((Real.sqrt c)⁻¹ • x) (ε := ε / Real.sqrt c) (s := Real.sqrt (η / T)) hαpos
    (Real.sqrt_pos.2 hηd)
  have henergyBound' : heatEnergy (Real.sqrt (η / T))
      (fun y => c * base (Real.sqrt c • y)) ≤
        4 * B * m + m ^ 2 / Real.pi * max 0
          (Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2)) := by
    have hmass := henergyBound.2
    rw [hbaseDilate]
    simpa [m] using hmass
  have hERatio : heatEnergy (Real.sqrt (η / T))
      (fun y => c * base (Real.sqrt c • y)) / |Real.log (η / T)| ≤ Ebar := by
    have hD : 0 < |Real.log (η / T)| := by linarith
    apply (div_le_iff₀ hD).2
    have htermA : 4 * B * m ≤ |Real.log (η / T)| * (4 * B * m) := by
      calc
        4 * B * m = (4 * B * m) * 1 := by ring
        _ ≤ (4 * B * m) * |Real.log (η / T)| :=
          mul_le_mul_of_nonneg_left hDenone (by positivity)
        _ = |Real.log (η / T)| * (4 * B * m) := by ring
    have htermB : m ^ 2 / Real.pi * max 0
        (Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2)) ≤
        |Real.log (η / T)| * (2 * m ^ 2 / Real.pi) := by
      have hmaxD : max 0 (Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2)) ≤
          2 * |Real.log (η / T)| := by
        exact hlogargBound.trans
          (mul_le_mul_of_nonneg_left hDenL (by norm_num : (0 : ℝ) ≤ 2))
      have hm2pi : 0 ≤ m ^ 2 / Real.pi := by positivity
      calc
        _ ≤ (m ^ 2 / Real.pi) * (2 * |Real.log (η / T)|) :=
          mul_le_mul_of_nonneg_left hmaxD hm2pi
        _ = |Real.log (η / T)| * (2 * m ^ 2 / Real.pi) := by ring
    dsimp [Ebar]
    calc
      heatEnergy (Real.sqrt (η / T)) (fun y => c * base (Real.sqrt c • y)) ≤
          4 * B * m + m ^ 2 / Real.pi * max 0
            (Real.log ((Real.sqrt (η / T)) / (ε / Real.sqrt c) ^ 2)) := henergyBound'
      _ ≤ |Real.log (η / T)| * (4 * B * m) +
          |Real.log (η / T)| * (2 * m ^ 2 / Real.pi) := add_le_add htermA htermB
      _ = |Real.log (η / T)| * (4 * B * m + 2 * m ^ 2 / Real.pi) := by ring
      _ = (4 * B * m + 2 * m ^ 2 / Real.pi) * |Real.log (η / T)| := by ring
  have hC₀le : C₀ ≤ Cbar := by dsimp [Cbar]; linarith [le_abs_self C₀]
  have hroot : Real.sqrt (C₀ * heatEnergy (Real.sqrt (η / T))
      (fun y => c * base (Real.sqrt c • y)) / |Real.log (η / T)|) ≤
      Real.sqrt (Cbar * Ebar) := by
    apply Real.sqrt_le_sqrt
    calc
      (C₀ * heatEnergy (Real.sqrt (η / T))
          (fun y => c * base (Real.sqrt c • y))) / |Real.log (η / T)| =
          C₀ * (heatEnergy (Real.sqrt (η / T))
            (fun y => c * base (Real.sqrt c • y)) / |Real.log (η / T)|) := by ring
      _ ≤ Cbar * (heatEnergy (Real.sqrt (η / T))
          (fun y => c * base (Real.sqrt c • y)) / |Real.log (η / T)|) :=
        mul_le_mul_of_nonneg_right hC₀le (div_nonneg henergyPos (abs_nonneg _))
      _ ≤ Cbar * Ebar := mul_le_mul_of_nonneg_left hERatio hCbar.le
  have hpow : |Real.log (η / T)| ^ (-(1 : ℝ) / 40) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hDenone (by norm_num)
  have hpowNonneg : 0 ≤ |Real.log (η / T)| ^ (-(1 : ℝ) / 40) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have htail : C₀ * m * |Real.log (η / T)| ^ (-(1 : ℝ) / 40) ≤ Cbar * m := by
    calc
      C₀ * m * |Real.log (η / T)| ^ (-(1 : ℝ) / 40) ≤
          Cbar * m * |Real.log (η / T)| ^ (-(1 : ℝ) / 40) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀le hm) hpowNonneg
      _ ≤ Cbar * m := by
        have hCm : 0 ≤ Cbar * m := mul_nonneg hCbar.le hm
        calc
          Cbar * m * |Real.log (η / T)| ^ (-(1 : ℝ) / 40) ≤ Cbar * m * 1 :=
            mul_le_mul_of_nonneg_left hpow hCm
          _ = Cbar * m := by ring
  have hboundReal : Real.sqrt (C₀ * heatEnergy (Real.sqrt (η / T))
      (fun y => c * base (Real.sqrt c • y)) / |Real.log (η / T)|) +
      C₀ * (∫ y, |c * base (Real.sqrt c • y)|) *
        |Real.log (η / T)| ^ (-(1 : ℝ) / 40) + 1 ≤ C := by
    rw [hbaseMass']
    dsimp [C]
    linarith [hroot, htail]
  have hunit' : eLpNorm (latticeSmoothingError (criticalBeta θ M) M M k j 0
      (fun y => c * base (Real.sqrt c • y))) 2 disorderLaw ≤ ENNReal.ofReal C := by
    exact hunit.trans (ENNReal.ofReal_le_ofReal hboundReal)
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N from hNreal)
  have hηT' : η < T := by
    exact lt_of_le_of_lt hηε hεT
  have hnormEq := eLpNorm_lattice_difference_eq_smoothingError ϑ N hη hηT' base
  have hscaleEq : ∀ ω : Disorder,
      latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T))
          (evenCeil (N * η)) (evenCeil (η * N)) 0 base ω =
        latticeSmoothingError (criticalBeta θ M) M M k j 0
          (fun y => c * base (Real.sqrt c • y)) ω := by
    intro ω
    have hscale := latticeSmoothingError_rescale (criticalBeta ϑ N)
      hNpos hMpos (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0 base ω
    simpa [c, M, Mfun, j, k, hβ] using hscale
  have hscaledNorm :
      eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T))
        (evenCeil (N * η)) (evenCeil (η * N)) 0 base) 2 disorderLaw =
      eLpNorm (latticeSmoothingError (criticalBeta θ M) M M k j 0
        (fun y => c * base (Real.sqrt c • y))) 2 disorderLaw := by
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall hscaleEq
  rw [hnormEq]
  rw [hscaledNorm]
  exact hunit'

end Critical2DKPZ.SmallScales

end
