/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.UnitHorizonPerturbed
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.Definitions.TestFn
import Critical2DKPZ.Smoothing.SmoothingClockBounds
import Critical2DKPZ.Smoothing.Measurability
import Critical2DKPZ.Smoothing.ParameterRescaling
import Critical2DKPZ.Smoothing.Rescaling
import Critical2DKPZ.Smoothing.SpatialRescaling
import Critical2DKPZ.Smoothing.TimeShift
import Mathlib.Tactic

/-! Diffusive rescaling gives lattice smoothing estimates on arbitrary positive time intervals. -/

@[expose] public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.Smoothing

private theorem eLpNorm_kpzLattice_difference_eq_smoothingError (ϑ : ℝ) (N : ℕ)
    {t T δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (htT : t + δ < T)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    eLpNorm (fun ω => ∫ x, φ x *
      (kpzLatticeReversed ϑ N t T h₀ x ω - kpzLatticeReversedReg ϑ N t T δ h₀ x ω))
      2 disorderLaw =
    eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N
      (evenCeil (N * T) - evenCeil (N * t))
      (evenCeil (N * (t + δ)) - evenCeil (N * t)) (evenCeil (δ * N)) h₀ φ)
      2 disorderLaw := by
  let f : Disorder → ℝ := fun ω => ∫ x, φ x *
    (kpzLatticeReversed ϑ N t T h₀ x ω - kpzLatticeReversedReg ϑ N t T δ h₀ x ω)
  let g : Disorder → ℝ := latticeSmoothingError (criticalBeta ϑ N) N
    (evenCeil (N * T) - evenCeil (N * t))
    (evenCeil (N * (t + δ)) - evenCeil (N * t)) (evenCeil (δ * N)) h₀ φ
  have hfg : f = g ∘ shiftEnvironment (evenCeil (N * t)) := by
    funext ω
    simpa only [f, g, Function.comp_apply] using
      kpzLattice_difference_timeShift ϑ N ht hδ htT h₀ φ ω
  have hfm : Measurable f := by
    rw [hfg]
    exact (measurable_latticeSmoothingError (criticalBeta ϑ N) N
      (evenCeil (N * T) - evenCeil (N * t))
      (evenCeil (N * (t + δ)) - evenCeil (N * t)) (evenCeil (δ * N)) h₀
      φ.continuous.measurable).comp (measurable_shiftEnvironment _)
  have hgm : Measurable g := by
    exact measurable_latticeSmoothingError (criticalBeta ϑ N) N
      (evenCeil (N * T) - evenCeil (N * t))
      (evenCeil (N * (t + δ)) - evenCeil (N * t)) (evenCeil (δ * N)) h₀
      φ.continuous.measurable
  have hmap (F : Disorder → ℝ) (hF : Measurable F) :
      eLpNorm F 2 disorderLaw =
        eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map F) := by
    symm
    simpa only [Function.comp_def] using
      (eLpNorm_map_measure (μ := disorderLaw) (p := (2 : ENNReal))
        (f := F) (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
        hF.aemeasurable)
  calc
    eLpNorm f 2 disorderLaw = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map f) := hmap f hfm
    _ = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map g) := by
      rw [kpzLattice_difference_timeShift_law ϑ N ht hδ htT h₀ φ]
    _ = eLpNorm g 2 disorderLaw := (hmap g hgm).symm

private theorem c11_horizon_tendsto {t T a b : ℝ} (ht : 0 ≤ t) (ha : 0 < a)
    (hab : a ≤ b) (hgap : T - t ∈ Set.Icc a b) :
    Tendsto (fun N : ℕ => evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t)) atTop atTop := by
  have hclock := c11_horizon_rescale_bounds ht ha hab hgap
  apply Filter.tendsto_atTop.2
  intro m
  have hN : ∀ᶠ N : ℕ in atTop, (m : ℝ) ≤ a / 2 * (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < a / 2)).eventually
      (eventually_ge_atTop (m : ℝ))
  filter_upwards [hclock, hN] with N hclock hN
  dsimp only at hclock
  have hM : (m : ℝ) ≤
      ((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) :=
    hN.trans hclock.1
  exact_mod_cast hM

/-- The unit-horizon smoothing bound gives an L² lattice approximation uniform over compact ranges of time horizons and critical parameters. -/
theorem lem_extension_approximation_of_unit (hU : LatticeSmoothingUnitBound)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a b A : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ t T : ℝ, 0 ≤ t → T - t ∈ Set.Icc a b → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop,
          eLpNorm (fun ω => ∫ x, φ x *
            (kpzLatticeReversed ϑ N t T h₀ x ω - kpzLatticeReversedReg ϑ N t T δ h₀ x ω))
            2 disorderLaw ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  obtain ⟨Braw, hBraw⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  let B : ℝ := |Braw| + 1
  have hB : ∀ x : Plane, |φ x| ≤ B := by
    intro x
    have hx := hBraw x
    rw [Real.norm_eq_abs] at hx
    dsimp [B]
    exact hx.trans (calc
      Braw ≤ |Braw| := le_abs_self _
      _ ≤ |Braw| + 1 := le_add_of_nonneg_right (by norm_num))
  have hBpos : 0 < B := by dsimp [B]; positivity
  let M₁ : ℝ := ∫ x, |φ x|
  let M₂ : ℝ := 2 * b * B
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hM₂ : 0 ≤ M₂ := by dsimp [M₂]; positivity
  obtain ⟨A', hcritical⟩ := criticalBeta_rescale A (a / 2) (2 * b) (by positivity)
  obtain ⟨CU, δU, hδU, hUbound⟩ := hU A' ‖h₀‖ M₁ M₂
  let Kpow : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 40)
  let C : ℝ := |CU| * Kpow + 1
  let Klog : ℝ := max |Real.log a| |Real.log b|
  let δ₁ : ℝ := min (a / 2)
    (min (a * δU) (Real.exp (-(2 * Klog + 1))))
  have hKpow : 0 < Kpow := by dsimp [Kpow]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hKlog : 0 ≤ Klog := by dsimp [Klog]; positivity
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  refine ⟨C, δ₁, hδ₁, ?_⟩
  intro δ hδ hδ₁' ϑ hϑ t T ht hgap ε hε
  let gap : ℝ := T - t
  let δ' : ℝ := δ / gap
  let Mfun : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t)
  have hgapPos : 0 < gap := by dsimp [gap]; exact lt_of_lt_of_le ha hgap.1
  have hδsmall : δ < a / 2 := lt_of_lt_of_le hδ₁' (min_le_left _ _)
  have hδa : δ ≤ a := by linarith
  have hδbelowUnit : δ < a * δU := lt_of_lt_of_le hδ₁'
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδexp : δ < Real.exp (-(2 * Klog + 1)) := lt_of_lt_of_le hδ₁'
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hlogδ : Real.log δ < -(2 * Klog + 1) := by
    calc
      Real.log δ < Real.log (Real.exp (-(2 * Klog + 1))) := Real.log_lt_log hδ hδexp
      _ = -(2 * Klog + 1) := Real.log_exp _
  have hlogδlower : 2 * Klog + 1 ≤ |Real.log δ| := by
    rw [abs_of_neg (by linarith : Real.log δ < 0)]
    linarith
  have hδ'pos : 0 < δ' := by dsimp [δ']; exact div_pos hδ hgapPos
  have hδ'lt : δ' < 1 := by
    apply (div_lt_one hgapPos).2
    have hgapLower : a ≤ gap := by dsimp [gap]; exact hgap.1
    linarith
  have hδ'unit : δ' < δU := by
    apply (div_lt_iff₀ hgapPos).2
    have hgapLower : a ≤ gap := by dsimp [gap]; exact hgap.1
    calc
      δ < a * δU := hδbelowUnit
      _ ≤ gap * δU := mul_le_mul_of_nonneg_right hgapLower hδU.le
      _ = δU * gap := by ring
  have hεhalf : 0 < ε / 2 := by linarith
  have hUevent := hUbound δ' hδ'pos hδ'unit (ε / 2) hεhalf
  have hMlim : Tendsto Mfun atTop atTop := by
    simpa only [Mfun] using c11_horizon_tendsto ht ha hab (by simpa only [gap] using hgap)
  have hUeventN := hMlim.eventually hUevent
  have hcriticalN := hcritical
  have hclockN := c11_horizon_rescale_bounds ht ha hab hgap
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  filter_upwards [hclockN, hcriticalN, hUeventN, hNpos] with N hclock hcriticalN hUeventM hN
  dsimp only at hclock
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let M : ℕ := Mfun N
  have hMlow : a / 2 * (N : ℝ) ≤ (M : ℝ) := by simpa only [M, Mfun] using hclock.1
  have hMhigh : (M : ℝ) ≤ 2 * b * (N : ℝ) := by simpa only [M, Mfun] using hclock.2
  have hMreal : 0 < (M : ℝ) := lt_of_lt_of_le
    (mul_pos (by linarith : 0 < a / 2) hNreal) hMlow
  have hMpos : 0 < M := by exact_mod_cast hMreal
  have htime : (N : ℝ) * t ≤ (N : ℝ) * T :=
    mul_le_mul_of_nonneg_left (by linarith [hgap.1]) (Nat.cast_nonneg N)
  have hMeven : Even M := by
    dsimp [M, Mfun]
    exact evenCeil_sub_even htime
  obtain ⟨ϑ', hϑ', hβ⟩ := hcriticalN ϑ hϑ M hMlow hMhigh
  have hwidth := c11_widths_within_six N ht ha hgap.1 hδ (by linarith)
  let j : ℕ := evenCeil (δ * (N : ℝ))
  let k : ℕ := evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t)
  have hj : Even j := by dsimp [j]; exact evenCeil_even _
  have hk : Even k := by
    dsimp [k]
    apply evenCeil_sub_even
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ.le) (Nat.cast_nonneg N)
  have htimeDelta : (N : ℝ) * t ≤ (N : ℝ) * (t + δ) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ.le) (Nat.cast_nonneg N)
  have hceilDelta : evenCeil ((N : ℝ) * t) ≤ evenCeil ((N : ℝ) * (t + δ)) :=
    evenCeil_mono htimeDelta
  have hKcast : (k : ℤ) =
      (evenCeil ((N : ℝ) * (t + δ)) : ℤ) - evenCeil ((N : ℝ) * t) := by
    dsimp [k]
    rw [Nat.cast_sub hceilDelta]
  have hJlo : (j : ℤ) ≤ (evenCeil (δ' * M) : ℤ) + 6 := by
    simpa only [j, δ', M, Mfun] using hwidth.1
  have hJhi : (evenCeil (δ' * M) : ℤ) ≤ (j : ℤ) + 6 := by
    simpa only [j, δ', M, Mfun] using hwidth.2.1
  have hKlo : (k : ℤ) ≤ (evenCeil (δ' * M) : ℤ) + 6 := by
    rw [hKcast]
    simpa only [δ', M, Mfun] using hwidth.2.2.1
  have hKhi : (evenCeil (δ' * M) : ℤ) ≤ (k : ℤ) + 6 := by
    rw [hKcast]
    simpa only [δ', M, Mfun] using hwidth.2.2.2
  have hNpos' : (N : ℝ) ≠ 0 := ne_of_gt hNreal
  let c : ℝ := (M : ℝ) / (N : ℝ)
  have hcLower : a / 2 ≤ c := (le_div_iff₀ hNreal).2 hMlow
  have hcUpper : c ≤ 2 * b := (div_le_iff₀ hNreal).2 hMhigh
  have hcPos : 0 < c := lt_of_lt_of_le (by linarith : 0 < a / 2) hcLower
  let ψ : Plane → ℝ := fun y => c * φ (Real.sqrt c • y)
  let h₀' : Plane →ᵇ ℝ := h₀.compContinuous
    ⟨fun y => Real.sqrt c • y, by fun_prop⟩
  have hh₀' : ‖h₀'‖ ≤ ‖h₀‖ := by
    dsimp [h₀']
    exact BoundedContinuousFunction.norm_compContinuous_le h₀
      ⟨fun y => Real.sqrt c • y, by fun_prop⟩
  have hψmeas : Measurable ψ := by
    have hψcont : Continuous ψ := by
      dsimp [ψ]
      exact continuous_const.mul
        (φ.continuous.comp (continuous_id.const_smul (Real.sqrt c)))
    exact hψcont.measurable
  have hψcompact : HasCompactSupport ψ := by
    have hcomp : HasCompactSupport (fun y : Plane => φ (Real.sqrt c • y)) := by
      let e : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero (α := Plane)
        (Real.sqrt c) (ne_of_gt (Real.sqrt_pos.2 hcPos))
      have he : (fun y : Plane => φ (Real.sqrt c • y)) = φ ∘ e := by
        funext y
        rfl
      rw [he]
      exact φ.hasCompactSupport.comp_homeomorph e
    change HasCompactSupport
      ((fun _ : Plane => c) * fun y : Plane => φ (Real.sqrt c • y))
    exact hcomp.mul_left
  have hψL1eq : (∫ y, |ψ y|) = ∫ x, |φ x| := by
    have hscale := integral_plane_sqrt_scale hcPos (fun x : Plane => |φ x|)
    calc
      ∫ y, |ψ y| = ∫ y, c * |φ (Real.sqrt c • y)| := by
        congr 1
        funext y
        simp only [ψ, abs_mul, abs_of_pos hcPos]
      _ = c * ∫ y, |φ (Real.sqrt c • y)| := integral_const_mul c _
      _ = ∫ x, |φ x| := hscale.symm
  have hψL1 : (∫ y, |ψ y|) ≤ M₁ := by simpa only [hψL1eq, M₁] using le_rfl
  have hψbound : ∀ y : Plane, |ψ y| ≤ M₂ := by
    intro y
    have hfirst : c * |φ (Real.sqrt c • y)| ≤ c * B :=
      mul_le_mul_of_nonneg_left (hB _) hcPos.le
    have hsecond : c * B ≤ 2 * b * B :=
      mul_le_mul_of_nonneg_right hcUpper hBpos.le
    dsimp [ψ, M₂]
    rw [abs_mul, abs_of_pos hcPos]
    exact hfirst.trans hsecond
  have hUbound := hUeventM hMeven ϑ' hϑ' j k hj hk hJlo hJhi hKlo hKhi
    h₀' hh₀' ψ hψmeas hψcompact hψL1 hψbound
  have hscaledEq :
      (fun ω => latticeSmoothingError (criticalBeta ϑ N) N M k j h₀ φ ω) =
        fun ω => latticeSmoothingError (criticalBeta ϑ' M) M M k j h₀' ψ ω := by
    funext ω
    have hscale := latticeSmoothingError_rescale (criticalBeta ϑ N)
      (by exact_mod_cast hN) (by exact_mod_cast hMpos) M k j h₀ φ ω
    calc
      _ = latticeSmoothingError (criticalBeta ϑ N) M M k j h₀' ψ ω := by
        simpa only [h₀', ψ, c] using hscale
      _ = latticeSmoothingError (criticalBeta ϑ' M) M M k j h₀' ψ ω := by rw [hβ]
  have hscaledNorm :
      eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N M k j h₀ φ) 2 disorderLaw =
        eLpNorm (latticeSmoothingError (criticalBeta ϑ' M) M M k j h₀' ψ)
          2 disorderLaw := by
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun ω => congrFun hscaledEq ω
  have hUnitNorm : eLpNorm
      (latticeSmoothingError (criticalBeta ϑ' M) M M k j h₀' ψ) 2 disorderLaw ≤
        ENNReal.ofReal (CU * |Real.log δ'| ^ (-(1 : ℝ) / 40) + ε / 2) := hUbound
  have hKgap : |Real.log gap| ≤ Klog := by
    apply abs_le.mpr
    constructor
    · have hla : -Klog ≤ Real.log a := by
        exact (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
      exact hla.trans (Real.log_le_log ha hgap.1)
    · exact (Real.log_le_log hgapPos (hgap.2)).trans (le_abs_self _ |>.trans (le_max_right _ _))
  have hlogδdiv : Real.log δ' = Real.log δ - Real.log gap := by
    dsimp [δ', gap]
    rw [Real.log_div hδ.ne' hgapPos.ne']
  have hlogdifference : |Real.log δ| - Klog ≤ |Real.log δ'| := by
    rw [hlogδdiv]
    calc
      |Real.log δ| - Klog ≤ |Real.log δ| - |Real.log gap| :=
        sub_le_sub_left hKgap _
      _ ≤ |Real.log δ - Real.log gap| := by
        exact abs_sub_abs_le_abs_sub (Real.log δ) (Real.log gap)
  have hloghalf : |Real.log δ| / 2 ≤ |Real.log δ'| := by
    linarith [hlogdifference, hlogδlower]
  have hlogδpos : 0 < |Real.log δ| := by linarith [hlogδlower]
  have hpowδ : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) :=
    Real.rpow_nonneg hlogδpos.le _
  have hpowδ' : 0 ≤ |Real.log δ'| ^ (-(1 : ℝ) / 40) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hpowfactor : (|Real.log δ| / 2) ^ (-(1 : ℝ) / 40) =
      Kpow * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
    rw [Real.div_rpow hlogδpos.le (by norm_num)]
    have hden : (2 : ℝ) ^ (-(1 : ℝ) / 40) = Kpow⁻¹ := by
      dsimp [Kpow]
      rw [show -(1 : ℝ) / 40 = -((1 : ℝ) / 40) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hden]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hpowCompare : |Real.log δ'| ^ (-(1 : ℝ) / 40) ≤
      Kpow * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
    calc
      _ ≤ (|Real.log δ| / 2) ^ (-(1 : ℝ) / 40) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hloghalf (by norm_num)
      _ = _ := hpowfactor
  have hcoeff : CU * |Real.log δ'| ^ (-(1 : ℝ) / 40) ≤
      C * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
    calc
      _ ≤ |CU| * |Real.log δ'| ^ (-(1 : ℝ) / 40) :=
        mul_le_mul_of_nonneg_right (le_abs_self CU) hpowδ'
      _ ≤ |CU| * (Kpow * |Real.log δ| ^ (-(1 : ℝ) / 40)) :=
        mul_le_mul_of_nonneg_left hpowCompare (abs_nonneg CU)
      _ = (|CU| * Kpow) * |Real.log δ| ^ (-(1 : ℝ) / 40) := by ring
      _ ≤ C * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) hpowδ
  have hfinalReal : CU * |Real.log δ'| ^ (-(1 : ℝ) / 40) + ε / 2 ≤
      C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε := by linarith
  have hfinal : eLpNorm
      (latticeSmoothingError (criticalBeta ϑ N) N M k j h₀ φ) 2 disorderLaw ≤
        ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
    calc
      _ = eLpNorm (latticeSmoothingError (criticalBeta ϑ' M) M M k j h₀' ψ)
          2 disorderLaw := hscaledNorm
      _ ≤ ENNReal.ofReal
          (CU * |Real.log δ'| ^ (-(1 : ℝ) / 40) + ε / 2) := hUnitNorm
      _ ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) :=
        ENNReal.ofReal_le_ofReal hfinalReal
  have htimeShift : t + δ < T := by
    have hgapLower : a ≤ T - t := hgap.1
    linarith
  have htimeNorm := eLpNorm_kpzLattice_difference_eq_smoothingError ϑ N ht hδ htimeShift h₀ φ
  calc
    _ = eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N
        (evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t))
        (evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t))
        (evenCeil (δ * (N : ℝ))) h₀ φ) 2 disorderLaw := htimeNorm
    _ = eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N M k j h₀ φ)
        2 disorderLaw := by rfl
    _ ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := hfinal

/-- The perturbation bound and profile estimates give the L² lattice smoothing approximation. -/
theorem lem_extension_approximation_of_perturb (hP : LatticeSmoothingPerturbBound)
    (hVD : PropVDBound) (hO : FutureProfiles.PropPFOriginBound)
    (hL : FutureProfiles.LogTailsOriginBound) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (a b A : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ t T : ℝ, 0 ≤ t → T - t ∈ Set.Icc a b → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop,
          eLpNorm (fun ω => ∫ x, φ x *
            (kpzLatticeReversed ϑ N t T h₀ x ω - kpzLatticeReversedReg ϑ N t T δ h₀ x ω))
            2 disorderLaw ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) :=
  lem_extension_approximation_of_unit
    (latticeSmoothingError_unit_le_of_perturb hP hVD hO hL) h₀ φ a b A ha hab

/-- The logarithmic variance and profile estimates give the L² lattice smoothing approximation. -/
theorem lem_extension_approximation_of (hVD : PropVDBound)
    (hO : FutureProfiles.PropPFOriginBound) (hL : FutureProfiles.LogTailsOriginBound)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a b A : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ t T : ℝ, 0 ≤ t → T - t ∈ Set.Icc a b →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          eLpNorm (fun ω => ∫ x, φ x *
            (kpzLatticeReversed ϑ N t T h₀ x ω - kpzLatticeReversedReg ϑ N t T δ h₀ x ω))
            2 disorderLaw ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  exact lem_extension_approximation_of_perturb
    (fun A H M₁ M₂ δ hδ hδ1 =>
      latticeSmoothingError_perturb_le A H M₁ M₂ δ hδ hδ1)
    hVD hO hL h₀ φ a b A ha hab

end Critical2DKPZ.Smoothing

end
