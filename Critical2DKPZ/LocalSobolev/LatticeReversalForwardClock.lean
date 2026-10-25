/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.UnitHorizonPerturbed
public import Critical2DKPZ.LocalSobolev.LatticeMoment
public import Critical2DKPZ.LocalSobolev.LatticeReversalPointwise
import all Critical2DKPZ.LocalSobolev.LatticeReversalProfileIdentity
public import Critical2DKPZ.Definitions.TestFn
import all Critical2DKPZ.Provider.LemExtensionApproximation
import all Critical2DKPZ.Smoothing.LatticeSmoothingRescaling
import Critical2DKPZ.Provider.PropPFLogTails
import Critical2DKPZ.Provider.PropVD
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Forward lattice fields under bounded even-clock perturbations -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BoundedContinuousFunction Topology

namespace Critical2DKPZ.LocalSobolev

/-- All clocks in the perturbation remain positive, with a fixed positive
macroscopic lower bound, once the lattice scale is sufficiently large. -/
theorem eventually_evenClockPerturb_pos (t : ℝ) (ht : 0 < t)
    (r : ℕ → ℤ) (hr : ∀ N, r N = -2 ∨ r N = 0 ∨ r N = 2) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ t / 2 ≤ t + (r N : ℝ) / (N : ℝ) := by
  filter_upwards [eventually_ge_atTop ⌈4 / t⌉₊, eventually_gt_atTop 0] with N hN hN0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlarge : 4 / t ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
  have hNt : 4 ≤ t * N := by simpa only [mul_comm] using (div_le_iff₀ ht).mp hlarge
  have hrlo : (-2 : ℝ) ≤ (r N : ℝ) := by rcases hr N with h | h | h <;> rw [h] <;> norm_num
  refine ⟨hN0, ?_⟩
  have hh : t / 2 * N ≤ t * N + r N := by linarith only [hNt, hrlo]
  simpa only [add_div, mul_div_cancel_right₀ _ hNr.ne'] using
    (div_le_div_of_nonneg_right hh hNr.le)

/-- Bounded even perturbations change the even ceiling by exactly the
same signed number of lattice steps, once the time is positive. -/
theorem eventually_evenCeil_evenClockPerturb (t : ℝ) (ht : 0 < t)
    (r : ℕ → ℤ) (hr : ∀ N, r N = -2 ∨ r N = 0 ∨ r N = 2) :
    ∀ᶠ N : ℕ in atTop,
      (evenCeil ((N : ℝ) * (t + (r N : ℝ) / (N : ℝ))) : ℤ) =
        (evenCeil ((N : ℝ) * t) : ℤ) + r N := by
  filter_upwards [eventually_ge_atTop ⌈4 / t⌉₊, eventually_gt_atTop 0] with N hN hN0
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hlarge : 4 / t ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
  have hNt : 4 ≤ (N : ℝ) * t := by
    have hh := (div_le_iff₀ ht).mp hlarge
    simpa only [mul_comm] using hh
  have hexpand : (N : ℝ) * (t + (r N : ℝ) / N) = N * t + r N := by field_simp
  rw [hexpand]
  rcases hr N with h | h | h
  · rw [h]
    have hc := evenCeil_add_two_mul (t := (N : ℝ) * t - 2) (by linarith only [hNt]) 1
    have he : (N : ℝ) * t - 2 + 2 * (1 : ℕ) = N * t := by norm_num
    rw [he] at hc
    norm_num at hc ⊢
    simp only [sub_eq_add_neg] at hc
    omega
  · simp only [h, Int.cast_zero, add_zero]
  · rw [h]
    have hc := evenCeil_add_two_mul (t := (N : ℝ) * t) (by linarith only [hNt]) 1
    norm_num at hc ⊢
    omega

/-- The forward lattice field, including its deterministic centering, depends
on a time only through the even clock. -/
theorem kpzLattice_eq_of_evenCeil_eq (ϑ : ℝ) (N : ℕ) {s t : ℝ}
    (hst : evenCeil ((N : ℝ) * s) = evenCeil ((N : ℝ) * t))
    (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    kpzLattice ϑ N s h₀ x ω = kpzLattice ϑ N t h₀ x ω := by
  simp only [kpzLattice, kpzLatticeCentring, rescaledP2P, hst]


private theorem forwardClock_unit_bound : Smoothing.LatticeSmoothingUnitBound := by
  have hC6 : OnePoint.BlockMomentsBound := fun A ρ₀ ρ₁ hρ =>
    Provider.blockMoments A ρ₀ ρ₁ hρ
  have hDiscrepancyStringInput : FutureProfiles.OpenStringBound := fun A =>
    Blocks.openDiscrepancyMass_sq_integral_le A
  have hBlockRatioInput : FutureProfiles.RatioBoundP := fun A =>
    OnePoint.blockGoodSet_compl_and_ratio_bound_of hC6 A
  have hPE : FutureProfiles.ProfileEstimatesBound := fun A =>
    FutureProfiles.profile_estimates_of hDiscrepancyStringInput hBlockRatioInput A
  have hO : FutureProfiles.PropPFOriginBound := fun A =>
    FutureProfiles.prop_PF_origin_of hDiscrepancyStringInput hPE A
  have hTail : FutureProfiles.LogProfileTailBound := fun A =>
    FutureProfiles.log_profile_tail_le_of hPE A
  have hL : FutureProfiles.LogTailsOriginBound := fun A =>
    FutureProfiles.logTails_origin_of hTail A
  exact Smoothing.latticeSmoothingError_unit_le_of (fun A => Provider.prop_VD A) hO hL

/-- The unit-horizon smoothing estimate is uniform over every integer horizon
in a comparable window, rather than only along a fixed macroscopic time. -/
theorem eventually_latticeSmoothingError_comparable_horizon_le (ϑ a b : ℝ)
    (ha : 0 < a) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, Even M →
        a * N ≤ M → (M : ℝ) ≤ b * N → ∀ j k : ℕ, Even j → Even k →
        (j : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ j + 6 →
        (k : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ k + 6 →
          eLpNorm (Smoothing.latticeSmoothingError (criticalBeta ϑ N) N M k j h₀ φ)
            2 disorderLaw ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  obtain ⟨Braw, hBraw⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  let B : ℝ := |Braw| + 1
  have hB : ∀ x : Plane, |φ x| ≤ B := fun x => by
    have hh := hBraw x
    rw [Real.norm_eq_abs] at hh
    exact hh.trans ((le_abs_self Braw).trans (le_add_of_nonneg_right (by norm_num)))
  have hBpos : 0 < B := by dsimp [B]; positivity
  obtain ⟨A', hcritical⟩ := Smoothing.criticalBeta_rescale |ϑ| a b ha
  obtain ⟨C, δ₀, hδ₀, hunit⟩ := forwardClock_unit_bound A' ‖h₀‖
    (∫ x, |φ x|) (max b 0 * B)
  refine ⟨C, min δ₀ 1, lt_min hδ₀ zero_lt_one, min_le_right _ _, ?_⟩
  intro δ hδ hδ₁ ε hε
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp
    (hunit δ hδ (hδ₁.trans_le (min_le_left _ _)) ε hε)
  have hlarge : ∀ᶠ N : ℕ in atTop, (M₀ : ℝ) ≤ a * N :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha).eventually_ge_atTop _
  filter_upwards [hcritical, hlarge, eventually_gt_atTop 0] with N hcriticalN hlargeN hN
  intro M hMeven hlo hhi j k hj hk hjlo hjhi hklo hkhi
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := (mul_pos ha hNr).trans_le hlo
  have hM : 0 < M := by exact_mod_cast hMr
  have hM₀le : M₀ ≤ M := by exact_mod_cast hlargeN.trans hlo
  obtain ⟨ϑ', hϑ', hβ⟩ := hcriticalN ϑ ⟨neg_abs_le _, le_abs_self _⟩ M hlo hhi
  let c : ℝ := (M : ℝ) / N
  have hc : 0 < c := div_pos hMr hNr
  have hcb : c ≤ max b 0 := ((div_le_iff₀ hNr).mpr hhi).trans (le_max_left _ _)
  let ψ : Plane → ℝ := fun y => c * φ (Real.sqrt c • y)
  let h₀' : Plane →ᵇ ℝ := h₀.compContinuous ⟨fun y => Real.sqrt c • y, by fun_prop⟩
  have hh₀' : ‖h₀'‖ ≤ ‖h₀‖ := BoundedContinuousFunction.norm_compContinuous_le _ _
  have hψmeas : Measurable ψ := by
    have hh : Continuous ψ := by dsimp [ψ]; fun_prop
    exact hh.measurable
  have hψcompact : HasCompactSupport ψ := by
    let e : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero (α := Plane)
      (Real.sqrt c) (Real.sqrt_pos.mpr hc).ne'
    have hcomp : HasCompactSupport (fun y : Plane => φ (Real.sqrt c • y)) :=
      φ.hasCompactSupport.comp_homeomorph e
    exact hcomp.mul_left
  have hψL1 : (∫ y, |ψ y|) ≤ ∫ x, |φ x| := by
    have hscale := Smoothing.integral_plane_sqrt_scale hc (fun x : Plane => |φ x|)
    have he : (∫ y, |ψ y|) = c * ∫ y, |φ (Real.sqrt c • y)| := by
      simp only [ψ, abs_mul, abs_of_pos hc, integral_const_mul]
    exact le_of_eq (he.trans hscale.symm)
  have hψbound (y : Plane) : |ψ y| ≤ max b 0 * B := by
    rw [show ψ y = c * φ (Real.sqrt c • y) from rfl, abs_mul, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left (hB _) hc.le).trans
      (mul_le_mul_of_nonneg_right hcb hBpos.le)
  have hbound := hM₀ M hM₀le hMeven ϑ' hϑ' j k hj hk hjlo hjhi hklo hkhi
    h₀' hh₀' ψ hψmeas hψcompact hψL1 hψbound
  have heq : Smoothing.latticeSmoothingError (criticalBeta ϑ N) N M k j h₀ φ =
      Smoothing.latticeSmoothingError (criticalBeta ϑ' M) M M k j h₀' ψ := by
    funext ω
    rw [Smoothing.latticeSmoothingError_rescale (criticalBeta ϑ N) hN hM, hβ]
  rw [heq]
  exact hbound


private def forwardClockProfile (β : ℝ) (N a M : ℕ) (h₀ : Plane →ᵇ ℝ)
    (x : Plane) (ω : Disorder) : ℝ :=
  Real.log (profileP2Fun β a M (fun z => if z = latticePoint N x then 1 else 0)
      (cellAverage N fun y => Real.exp (h₀ y)) ω) -
    ∫ ζ, Real.log (profileP2Fun β a M (fun z => if z = latticePoint N x then 1 else 0)
      (fun _ => 1) ζ) ∂disorderLaw

private theorem forwardClock_profile_increment_eq_errors (β : ℝ) {N M : ℕ}
    (hN : 0 < N) (hM : 2 ≤ M) (j : ℕ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (ω : Disorder) :
    (∫ x, φ x * (forwardClockProfile β N 0 M h₀ x ω -
      forwardClockProfile β N 2 M h₀ x ω)) =
      Smoothing.latticeSmoothingError β N M (2 + j) j h₀ φ ω -
        Smoothing.latticeSmoothingError β N (M - 2) j j h₀ φ
          (Smoothing.shiftEnvironment 2 ω) := by
  have hB : ∃ B : ℝ, ∀ x, |φ x| ≤ B := by
    obtain ⟨B, hB⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    exact ⟨B, fun x => by simpa only [Real.norm_eq_abs] using hB x⟩
  let P (a : ℕ) (ν : Site → ℝ) :=
    Real.log (profileP2Fun β a M ν (cellAverage N fun y => Real.exp (h₀ y)) ω) -
      ∫ ζ, Real.log (profileP2Fun β a M ν (fun _ => 1) ζ) ∂disorderLaw
  let A : Plane → ℝ := fun x => P 0 (fun z => if z = latticePoint N x then 1 else 0)
  let B : Plane → ℝ := fun x => P 2 (fun z => if z = latticePoint N x then 1 else 0)
  let R : Plane → ℝ := fun x => P (2 + j) (fun z => srwKernel j (z - latticePoint N x))
  have hiA : Integrable (fun x => φ x * A x) :=
    Smoothing.integrable_mul_siteFunction_latticePoint N hN φ.continuous.measurable
      φ.hasCompactSupport hB (fun z => P 0 (fun w => if w = z then 1 else 0))
  have hiB : Integrable (fun x => φ x * B x) :=
    Smoothing.integrable_mul_siteFunction_latticePoint N hN φ.continuous.measurable
      φ.hasCompactSupport hB (fun z => P 2 (fun w => if w = z then 1 else 0))
  have hiR : Integrable (fun x => φ x * R x) :=
    Smoothing.integrable_mul_siteFunction_latticePoint N hN φ.continuous.measurable
      φ.hasCompactSupport hB (fun z => P (2 + j) (fun w => srwKernel j (w - z)))
  have hshift : Smoothing.latticeSmoothingError β N (M - 2) j j h₀ φ
      (Smoothing.shiftEnvironment 2 ω) = ∫ x, φ x * (B x - R x) := by
    unfold Smoothing.latticeSmoothingError
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [B, R, P]
    rw [Smoothing.centered_profile_timeShift_sub β (a := 2) le_rfl hM,
      Smoothing.centered_profile_timeShift_sub β (a := 2 + j) (by omega) hM]
    simp only [Nat.sub_self, Nat.add_sub_cancel_left]
  have hfirst : Smoothing.latticeSmoothingError β N M (2 + j) j h₀ φ ω =
      ∫ x, φ x * (A x - R x) := rfl
  rw [hshift, hfirst]
  change (∫ x, φ x * (A x - B x)) = _
  simp_rw [mul_sub]
  rw [integral_sub hiA hiB, integral_sub hiA hiR, integral_sub hiB hiR]
  ring

private theorem forwardClock_regularization_clocks {M : ℕ} (hM : 2 ≤ M)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    let j := evenCeil (δ * (M - 2 : ℕ))
    let q := evenCeil (δ * M)
    j ≤ q ∧ q ≤ j + 2 := by
  dsimp only
  have hcast : ((M - 2 : ℕ) : ℝ) = M - 2 := Nat.cast_sub hM
  constructor
  · apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le M 2)) hδ
  · have hh : δ * (M : ℝ) ≤ δ * (M - 2 : ℕ) + 2 := by
      rw [hcast]
      nlinarith only [hδ1]
    exact (evenCeil_mono hh).trans_eq (by
      simpa only [Nat.cast_one, mul_one] using
        evenCeil_add_two_mul (t := δ * (M - 2 : ℕ)) (by positivity) 1)


private theorem forwardClock_choose_regularization (C δ₁ ε : ℝ)
    (hδ₁ : 0 < δ₁) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧ δ < 1 ∧
      C * |Real.log δ| ^ (-(1 : ℝ) / 40) ≤ ε := by
  have hexp : Tendsto (fun L : ℝ => Real.exp (-L)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hpow : Tendsto (fun L : ℝ => |C| * L ^ (-(1 : ℝ) / 40)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)).const_mul |C|
  have hevent : ∀ᶠ L : ℝ in atTop, Real.exp (-L) < δ₁ ∧
      Real.exp (-L) < 1 ∧ |C| * L ^ (-(1 : ℝ) / 40) < ε ∧ 0 ≤ L := by
    filter_upwards [hexp.eventually (Iio_mem_nhds hδ₁),
      hexp.eventually (Iio_mem_nhds zero_lt_one), hpow.eventually (Iio_mem_nhds hε),
      eventually_ge_atTop 0] with L hLδ hL1 hLε hL0
    exact ⟨hLδ, hL1, hLε, hL0⟩
  obtain ⟨L, hLδ, hL1, hLε, hL0⟩ := hevent.exists
  refine ⟨Real.exp (-L), Real.exp_pos _, hLδ, hL1, ?_⟩
  rw [Real.log_exp, abs_neg, abs_of_nonneg hL0]
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hL0 _)).trans hLε.le

private theorem forwardClock_reversed_twoStep (ϑ a b : ℝ) (ha : 0 < a)
    (M : ℕ → ℕ) (hMeven : ∀ N, Even (M N))
    (hlo : ∀ᶠ N : ℕ in atTop, a * N + 2 ≤ M N)
    (hhi : ∀ᶠ N : ℕ in atTop, (M N : ℝ) ≤ b * N)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    Tendsto (fun N : ℕ => eLpNorm (fun ω : Disorder =>
      ∫ x, φ x * (forwardClockProfile (criticalBeta ϑ N) N 0 (M N) h₀ x ω -
        forwardClockProfile (criticalBeta ϑ N) N 2 (M N) h₀ x ω))
      2 disorderLaw) atTop (𝓝 0) := by
  obtain ⟨C, δ₁, hδ₁, _hδ₁one, hbound⟩ :=
    eventually_latticeSmoothingError_comparable_horizon_le ϑ a b ha h₀ φ
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases hεtop : ε = ∞
  · filter_upwards [] with N
    rw [hεtop]
    exact le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨δ, hδ, hδsmall, hδone, hδerror⟩ :=
    forwardClock_choose_regularization C δ₁ (ε.toReal / 8) hδ₁ (by positivity)
  have hη : 0 < ε.toReal / 8 := by positivity
  filter_upwards [hbound δ hδ hδsmall (ε.toReal / 8) hη,
    hlo, hhi, eventually_gt_atTop 0] with N hboundN hloN hhiN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (2 : ℝ) < M N := (lt_add_of_pos_left 2 (mul_pos ha hNr)).trans_le hloN
  have hM : 2 ≤ M N := by exact_mod_cast hMreal.le
  have hcast : ((M N - 2 : ℕ) : ℝ) = M N - 2 := by rw [Nat.cast_sub hM]; norm_num
  have hlo₂ : a * N ≤ (M N - 2 : ℕ) := by rw [hcast]; linarith only [hloN]
  have hhi₂ : ((M N - 2 : ℕ) : ℝ) ≤ b * N :=
    (Nat.cast_le.mpr (Nat.sub_le (M N) 2)).trans hhiN
  let j := evenCeil (δ * (M N - 2 : ℕ))
  let q := evenCeil (δ * M N)
  have hclock : j ≤ q ∧ q ≤ j + 2 := forwardClock_regularization_clocks hM hδ.le hδone.le
  have hj : Even j := evenCeil_even _
  have hk : Even (2 + j) := (by decide : Even (2 : ℕ)).add hj
  have hfirst := hboundN (M N) (hMeven N) (by linarith only [hloN]) hhiN
    j (2 + j) hj hk (by dsimp [q] at hclock; omega) (by dsimp [q] at hclock; omega)
    (by dsimp [q] at hclock; omega) (by dsimp [q] at hclock; omega)
  have hsecond := hboundN (M N - 2) ((hMeven N).tsub (by decide : Even (2 : ℕ)))
    hlo₂ hhi₂ j j hj hj (by omega) (by omega) (by omega) (by omega)
  let E₁ := Smoothing.latticeSmoothingError (criticalBeta ϑ N) N (M N) (2 + j) j h₀ φ
  let E₂ := Smoothing.latticeSmoothingError (criticalBeta ϑ N) N (M N - 2) j j h₀ φ
  have hsmall : C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε.toReal / 8 ≤ ε.toReal / 4 := by
    linarith only [hδerror]
  have hfirst' : eLpNorm E₁ 2 disorderLaw ≤ ENNReal.ofReal (ε.toReal / 4) :=
    hfirst.trans (ENNReal.ofReal_le_ofReal hsmall)
  have hsecond' : eLpNorm E₂ 2 disorderLaw ≤ ENNReal.ofReal (ε.toReal / 4) :=
    hsecond.trans (ENNReal.ofReal_le_ofReal hsmall)
  have hcompose : eLpNorm (E₂ ∘ Smoothing.shiftEnvironment 2) 2 disorderLaw =
      eLpNorm E₂ 2 disorderLaw :=
    eLpNorm_comp_measurePreserving
      (Smoothing.measurable_latticeSmoothingError _ _ _ _ _ _ φ.continuous.measurable).aestronglyMeasurable
      (Smoothing.measurePreserving_shiftEnvironment 2)
  have heq : (fun ω : Disorder => ∫ x, φ x *
      (forwardClockProfile (criticalBeta ϑ N) N 0 (M N) h₀ x ω -
        forwardClockProfile (criticalBeta ϑ N) N 2 (M N) h₀ x ω)) =
        E₁ - E₂ ∘ Smoothing.shiftEnvironment 2 := by
    funext ω
    exact forwardClock_profile_increment_eq_errors _ hN hM j h₀ φ ω
  rw [heq]
  calc
    _ ≤ eLpNorm E₁ 2 disorderLaw + eLpNorm (E₂ ∘ Smoothing.shiftEnvironment 2) 2 disorderLaw :=
      eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε.toReal / 4) + ENNReal.ofReal (ε.toReal / 4) := by
      rw [hcompose]
      exact add_le_add hfirst' hsecond'
    _ = ENNReal.ofReal (ε.toReal / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal (by linarith only [hεr])
    _ = ε := ENNReal.ofReal_toReal hεtop


/-- The two perturbed fields can use one common reversed horizon. Their
initial reversed clocks are exactly zero or two, with a uniform horizon window. -/
theorem eventually_evenClockPerturb_common_horizon (t : ℝ) (ht : 0 < t)
    (r : ℕ → ℤ) (hr : ∀ N, r N = -2 ∨ r N = 0 ∨ r N = 2) :
    ∀ᶠ N : ℕ in atTop,
      let m := evenCeil ((N : ℝ) * t)
      let m' := evenCeil ((N : ℝ) * (t + (r N : ℝ) / N))
      let L := max m m'
      Even L ∧ (t / 2) * N + 2 ≤ L ∧ (L : ℝ) ≤ (t + 4) * N ∧
        ((m = L ∧ m' + 2 = L) ∨ (m + 2 = L ∧ m' = L) ∨ (m = L ∧ m' = L)) := by
  filter_upwards [eventually_evenCeil_evenClockPerturb t ht r hr,
    eventually_ge_atTop ⌈4 / t⌉₊, eventually_ge_atTop 1] with N hclock hN hN1
  dsimp only
  let m := evenCeil ((N : ℝ) * t)
  let m' := evenCeil ((N : ℝ) * (t + (r N : ℝ) / N))
  have hL : Even (max m m') := by
    rcases le_total m m' with hh | hh
    · rw [max_eq_right hh]
      exact evenCeil_even _
    · rw [max_eq_left hh]
      exact evenCeil_even _
  have hlarge : 4 / t ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
  have hNt : 4 ≤ (N : ℝ) * t := (div_le_iff₀ ht).mp hlarge
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hmlo : (N : ℝ) * t ≤ m := le_evenCeil _
  have hmhi : (m : ℝ) < N * t + 2 := evenCeil_lt_add_two (by positivity)
  change (m' : ℤ) = (m : ℤ) + r N at hclock
  have hgap : m' ≤ m + 2 := by
    rcases hr N with hh | hh | hh <;> rw [hh] at hclock <;> norm_num at hclock <;> omega
  have hupper : max m m' ≤ m + 2 := max_le (by omega) hgap
  have hlower : (t / 2) * N + 2 ≤ (max m m' : ℕ) := by
    have hcast : (m : ℝ) ≤ ((max m m' : ℕ) : ℝ) := by exact_mod_cast le_max_left m m'
    nlinarith only [hNt, hmlo, hcast]
  have hupperReal : ((max m m' : ℕ) : ℝ) ≤ (t + 4) * N := by
    have hcast : ((max m m' : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast hupper
    rw [Nat.cast_add, Nat.cast_ofNat] at hcast
    nlinarith only [hcast, hmhi, hNr]
  refine ⟨hL, hlower, hupperReal, ?_⟩
  change ((m = max m m' ∧ m' + 2 = max m m') ∨
    (m + 2 = max m m' ∧ m' = max m m') ∨ (m = max m m' ∧ m' = max m m'))
  rcases hr N with hh | hh | hh
  · rw [hh] at hclock
    left
    omega
  · rw [hh] at hclock
    right; right
    norm_num at hclock
    omega
  · rw [hh] at hclock
    right; left
    omega


private theorem forwardClock_terminal_ratio_sq (β : ℝ) {n : ℕ} (hn : ¬ Even n)
    (x : Site) (hx : Even (x 0 + x 1)) (f : Site → ℝ)
    (hf : ∀ z, Even (z 0 + z 1) → 0 < f z) :
    Integrable (fun ω => (Real.log (profileP2Fun β n (n + 1)
        (endpointDist β n x ω) f ω) - Real.log (profileP2Fun 0 n (n + 1)
          (endpointDist β n x ω) f ω)) ^ 2) disorderLaw ∧
      (∫ ω, (Real.log (profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω)) ^ 2
        ∂disorderLaw) ≤ β ^ 2 + β ^ 4 / 4 := by
  let F := Smoothing.evenExtension f
  have hF (z : Site) : 0 < F z := by
    by_cases hz : Even (z 0 + z 1)
    · simpa [F, Smoothing.evenExtension, hz] using hf z hz
    · simp [F, Smoothing.evenExtension, hz]
  have hfg (z : Site) (hz : Even (z 0 + z 1)) : f z = F z := by
    simp [F, Smoothing.evenExtension, hz]
  have heq (ω : Disorder) (γ : ℝ) :
      profileP2Fun γ n (n + 1) (endpointDist β n x ω) f ω =
        profileP2Fun γ n (n + 1) (endpointDist β n x ω) F ω := by
    apply profileP2Fun_congr_of_oddStart_oneStep γ (by omega) _ f F _ hfg
    intro z hz
    have hzA : z ∈ Polymer.endpoints x n := by
      by_contra hnot
      exact hz (Polymer.endpointDist_eq_zero_of_not_mem β n x z ω hnot)
    exact odd_endpoint_of_oddDuration x z hx hn hzA
  have hfun : (fun ω => (Real.log (profileP2Fun β n (n + 1)
      (endpointDist β n x ω) f ω) - Real.log (profileP2Fun 0 n (n + 1)
        (endpointDist β n x ω) f ω)) ^ 2) =
      fun ω => (Real.log (profileP2Fun β n (n + 1) (endpointDist β n x ω) F ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) F ω)) ^ 2 := by
    funext ω
    rw [heq ω β, heq ω 0]
  rw [hfun]
  exact integral_sq_log_endpointDist_terminal_ratio_le β n x F hF

private def forwardClockBoundaryError (ϑ : ℝ) (N m L : ℕ) (h₀ : Plane →ᵇ ℝ)
    (ω : Disorder) (z : Site) : ℝ :=
  let β := criticalBeta ϑ N
  let ξ := Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)
  let f := cellAverage N fun y => Real.exp (h₀ y)
  β * ω (m, z) - β ^ 2 / 2 -
    (Real.log (profileP2Fun β (m - 1) m (endpointDist β (m - 1) z ξ) f ξ) -
      Real.log (profileP2Fun 0 (m - 1) m (endpointDist β (m - 1) z ξ) f ξ)) +
    ((∫ ζ, Real.log (pointToPlane β 0 m 0 ζ) ∂disorderLaw) -
      kpzLatticeCentring ϑ N ((m : ℝ) / N))

private theorem forwardClock_boundary_measurable (ϑ : ℝ) (N m L : ℕ) (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun p : Disorder × Site => forwardClockBoundaryError ϑ N m L h₀ p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro z
  let ξ : Disorder → Disorder := fun ω =>
    Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)
  have hξ : Measurable ξ := (Smoothing.measurable_shiftEnvironment _).comp
    (PolymerCalculus.measurePreserving_reversedDisorder L).measurable
  have hη (w : Site) : Measurable (fun ω => endpointDist (criticalBeta ϑ N) (m - 1) z (ξ ω) w) :=
    (Polymer.measurable_endpointDist _ _ _ _).comp hξ
  have hprofile (γ : ℝ) : Measurable (fun ω => profileP2Fun γ (m - 1) m
      (endpointDist (criticalBeta ϑ N) (m - 1) z (ξ ω))
      (cellAverage N fun y => Real.exp (h₀ y)) (ξ ω)) :=
    Smoothing.measurable_profileP2Fun_param γ _ _ _ hη hξ
  exact (((measurable_const.mul (Gaussian.measurable_disorder_eval (m, z))).sub_const _).sub
    ((hprofile _).log.sub (hprofile 0).log)).add_const _

private theorem forwardClock_gaussian_slice_sq (β : ℝ) (m : ℕ) (z : Site) :
    Integrable (fun ω : Disorder => (β * ω (m, z) - β ^ 2 / 2) ^ 2) disorderLaw ∧
      (∫ ω : Disorder, (β * ω (m, z) - β ^ 2 / 2) ^ 2 ∂disorderLaw) ≤
        2 * β ^ 2 + β ^ 4 / 2 := by
  let A : Disorder → ℝ := fun ω => β * ω (m, z) - β ^ 2 / 2
  have hXmem : MemLp (fun ω : Disorder => ω (m, z)) 2 disorderLaw :=
    (Gaussian.hasLaw_disorder_eval (m, z)).memLp (memLp_id_gaussianReal 2)
  have hAmem : MemLp A 2 disorderLaw := (hXmem.const_mul β).sub (memLp_const _)
  have hAsq : Integrable (fun ω => A ω ^ 2) disorderLaw := by
    simpa only [Real.norm_eq_abs, sq_abs] using hAmem.integrable_norm_pow'
  have hXsq : Integrable (fun ω : Disorder => ω (m, z) ^ 2) disorderLaw := by
    simpa only [Real.norm_eq_abs, sq_abs] using hXmem.integrable_norm_pow'
  have hXmoment : (∫ ω : Disorder, ω (m, z) ^ 2 ∂disorderLaw) = 1 := by
    have hv := variance_eq_integral (X := fun ω : Disorder => ω (m, z))
      (μ := disorderLaw) (Gaussian.measurable_disorder_eval _).aemeasurable
    have hmean : (∫ ω : Disorder, ω (m, z) ∂disorderLaw) = 0 := by
      have he := (Gaussian.hasLaw_disorder_eval (m, z)).integral_comp
        (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
      simpa only [Function.comp_def, integral_id_gaussianReal, zero_add, id_eq] using he
    have hvar : Var[fun ω : Disorder => ω (m, z); disorderLaw] = 1 := by
      rw [(Gaussian.hasLaw_disorder_eval (m, z)).variance_eq]; simp
    simpa only [hmean, sub_zero, hvar] using hv.symm
  have hAbound : (∫ ω, A ω ^ 2 ∂disorderLaw) ≤ 2 * β ^ 2 + β ^ 4 / 2 := by
    have hi := (hXsq.const_mul (2 * β ^ 2)).add (integrable_const (β ^ 4 / 2))
    have hh := integral_mono hAsq hi (fun ω => by
      change (β * ω (m, z) - β ^ 2 / 2) ^ 2 ≤
        2 * β ^ 2 * ω (m, z) ^ 2 + β ^ 4 / 2
      nlinarith only [sq_nonneg (β * ω (m, z) + β ^ 2 / 2)])
    change (∫ ω, A ω ^ 2 ∂disorderLaw) ≤
      ∫ ω, 2 * β ^ 2 * ω (m, z) ^ 2 + β ^ 4 / 2 ∂disorderLaw at hh
    rw [integral_add (hXsq.const_mul _) (integrable_const _), integral_const_mul,
      hXmoment, mul_one, integral_const] at hh
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] using hh
  exact ⟨hAsq, hAbound⟩

private theorem forwardClock_boundary_sq (ϑ : ℝ) {N m L : ℕ} (hN : 0 < N)
    (hm : 1 ≤ m) (hmEven : Even m) (h₀ : Plane →ᵇ ℝ) (z : Site)
    (hz : Even (z 0 + z 1)) :
    Integrable (fun ω => forwardClockBoundaryError ϑ N m L h₀ ω z ^ 2) disorderLaw ∧
      (∫ ω, forwardClockBoundaryError ϑ N m L h₀ ω z ^ 2 ∂disorderLaw) ≤
        9 * criticalBeta ϑ N ^ 2 + 3 * criticalBeta ϑ N ^ 4 := by
  let β := criticalBeta ϑ N
  let ξ := Smoothing.shiftEnvironment (L - m) ∘ PolymerCalculus.reversedDisorder L
  let f := cellAverage N fun y => Real.exp (h₀ y)
  let A : Disorder → ℝ := fun ω => β * ω (m, z) - β ^ 2 / 2
  let B : Disorder → ℝ := fun ω => Real.log (profileP2Fun β (m - 1) m
      (endpointDist β (m - 1) z (ξ ω)) f (ξ ω)) -
    Real.log (profileP2Fun 0 (m - 1) m (endpointDist β (m - 1) z (ξ ω)) f (ξ ω))
  let C : ℝ := (∫ ζ, Real.log (pointToPlane β 0 m 0 ζ) ∂disorderLaw) -
    kpzLatticeCentring ϑ N ((m : ℝ) / N)
  have hξ : MeasurePreserving ξ disorderLaw disorderLaw :=
    (Smoothing.measurePreserving_shiftEnvironment _).comp
      (PolymerCalculus.measurePreserving_reversedDisorder L)
  have hodd : ¬ Even (m - 1) := by
    intro hh
    have hh' := hh.add (by decide : Even (0 : ℕ))
    rcases hmEven with ⟨q, hq⟩
    rcases hh' with ⟨p, hp⟩
    omega
  have hf (w : Site) (hw : Even (w 0 + w 1)) : 0 < f w :=
    (Smoothing.cellAverage_exp_bounds_of_even N hN h₀ hw).1
  have hBbase := forwardClock_terminal_ratio_sq β hodd z hz f hf
  simp only [Nat.sub_add_cancel hm] at hBbase
  have hBsq : Integrable (fun ω => B ω ^ 2) disorderLaw := by
    simpa only [B, Function.comp_def] using
      hξ.integrable_comp_of_integrable hBbase.1
  have hBbound : (∫ ω, B ω ^ 2 ∂disorderLaw) ≤ β ^ 2 + β ^ 4 / 4 := by
    have he := integral_map hξ.measurable.aemeasurable
      (show AEStronglyMeasurable _ (disorderLaw.map ξ) from by
        rw [hξ.map_eq]; exact hBbase.1.aestronglyMeasurable)
    rw [hξ.map_eq] at he
    have hh := he.symm.trans_le hBbase.2
    simpa only [B, Function.comp_def] using hh
  obtain ⟨hAsq, hAbound⟩ := forwardClock_gaussian_slice_sq β m z
  have hmc : evenCeil ((N : ℝ) * ((m : ℝ) / N)) = m :=
    SHF.Symmetries.evenCeil_scaled_nat_div hN hmEven
  have hC : |C| ≤ β ^ 2 / 2 := by
    have hh := Assembly.kpzLatticeCentring_sub_logPointToPlane_le_of_pos ϑ ((m : ℝ) / N)
      (by positivity : 0 < (m : ℝ) / N) (show 1 ≤ N by omega)
    rw [hmc] at hh
    simpa only [C, β, abs_sub_comm] using hh
  have hCsq : C ^ 2 ≤ β ^ 4 / 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg C) (by positivity : 0 ≤ β ^ 2 / 2)).mpr hC
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hZmeas : Measurable (fun ω => forwardClockBoundaryError ϑ N m L h₀ ω z) :=
    (forwardClock_boundary_measurable _ _ _ _ _).comp (measurable_id.prodMk measurable_const)
  have hi := ((hAsq.add hBsq).add (integrable_const (C ^ 2))).const_mul 3
  have hpoly (ω : Disorder) : (A ω - B ω + C) ^ 2 ≤ 3 * (A ω ^ 2 + B ω ^ 2 + C ^ 2) := by
    nlinarith only [sq_nonneg (A ω + B ω), sq_nonneg (A ω - C), sq_nonneg (B ω + C)]
  have hZsq : Integrable (fun ω => forwardClockBoundaryError ϑ N m L h₀ ω z ^ 2) disorderLaw := by
    apply hi.mono' (hZmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoly ω
  refine ⟨hZsq, ?_⟩
  have hh := integral_mono hZsq hi (fun ω => by
    change (A ω - B ω + C) ^ 2 ≤ 3 * (A ω ^ 2 + B ω ^ 2 + C ^ 2)
    nlinarith only [sq_nonneg (A ω + B ω), sq_nonneg (A ω - C), sq_nonneg (B ω + C)])
  rw [integral_const_mul] at hh
  change (∫ ω, forwardClockBoundaryError ϑ N m L h₀ ω z ^ 2 ∂disorderLaw) ≤
    3 * (∫ ω, A ω ^ 2 + B ω ^ 2 + C ^ 2 ∂disorderLaw) at hh
  rw [integral_add (f := fun ω => A ω ^ 2 + B ω ^ 2) (g := fun _ => C ^ 2)
      (hAsq.add hBsq) (integrable_const _),
    integral_add (f := fun ω => A ω ^ 2) (g := fun ω => B ω ^ 2) hAsq hBsq,
    integral_const] at hh
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hh
  dsimp only [β] at hAbound hBbound hCsq
  nlinarith only [hh, hAbound, hBbound, hCsq]


private theorem forwardClock_boundary_identity (ϑ : ℝ) {N m L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmEven : Even m) (hLEven : Even L) (hmL : m ≤ L)
    (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      forwardClockProfile (criticalBeta ϑ N) N (L - m) L h₀ x
        (PolymerCalculus.reversedDisorder L ω) =
      forwardClockBoundaryError ϑ N m L h₀ ω (latticePoint N x) := by
  have hqEven : Even (L - m) := hLEven.tsub hmEven
  have hq := SHF.Symmetries.evenCeil_scaled_nat_div hN hqEven
  have hL := SHF.Symmetries.evenCeil_scaled_nat_div hN hLEven
  have hprofile (ζ : Disorder) :
      kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ x ζ =
        forwardClockProfile (criticalBeta ϑ N) N (L - m) L h₀ x ζ := by
    unfold kpzLatticeReversed forwardClockProfile
    rw [hq, hL]
  have hh := kpzLattice_sub_exactReverseField_eq ϑ hN hm hmEven hLEven hmL h₀ x ω
  dsimp only at hh
  rw [hprofile] at hh
  rw [hh]
  unfold forwardClockBoundaryError
  ring

private theorem forwardClock_tested_boundary_le (ϑ : ℝ) {N m L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmEven : Even m) (hLEven : Even L) (hmL : m ≤ L)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    eLpNorm (fun ω : Disorder => ∫ x, φ x *
      (kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
        forwardClockProfile (criticalBeta ϑ N) N (L - m) L h₀ x
          (PolymerCalculus.reversedDisorder L ω))) 2 disorderLaw ≤
      ENNReal.ofReal (Real.sqrt (9 * criticalBeta ϑ N ^ 2 + 3 * criticalBeta ϑ N ^ 4) *
        ∫ x, |φ x|) := by
  let Z : Disorder → Plane → ℝ := fun ω x =>
    forwardClockBoundaryError ϑ N m L h₀ ω (latticePoint N x)
  have hZ : Measurable (fun p : Disorder × Plane => Z p.1 p.2) :=
    (forwardClock_boundary_measurable _ _ _ _ _).comp
      (measurable_fst.prodMk ((measurable_latticePoint N).comp measurable_snd))
  have hZsq (x : Plane) : Integrable (fun ω => Z ω x ^ 2) disorderLaw ∧
      (∫ ω, Z ω x ^ 2 ∂disorderLaw) ≤ 9 * criticalBeta ϑ N ^ 2 + 3 * criticalBeta ϑ N ^ 4 :=
    forwardClock_boundary_sq ϑ hN hm hmEven h₀ (latticePoint N x)
      (latticePoint_mem_evenLattice N x)
  have hZmem (x : Plane) : MemLp (fun ω => Z ω x) 2 disorderLaw :=
    (memLp_two_iff_integrable_sq
      (hZ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr (hZsq x).1
  have hiφ : Integrable (fun x : Plane => φ x) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hbound := (Smoothing.eLpNorm_integral_mul_le_of_uniform_secondMoment disorderLaw
    φ φ.continuous.measurable hiφ hZ hZmem _ (by positivity) hZsq).2
  have heq : (fun ω : Disorder => ∫ x, φ x *
      (kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
        forwardClockProfile (criticalBeta ϑ N) N (L - m) L h₀ x
          (PolymerCalculus.reversedDisorder L ω))) = fun ω => ∫ x, φ x * Z ω x := by
    funext ω
    apply integral_congr_ae
    filter_upwards [] with x
    rw [forwardClock_boundary_identity ϑ hN hm hmEven hLEven hmL h₀ x ω]
  rw [heq]
  exact hbound

private theorem forwardClock_profile_measurable (β : ℝ) (N a M : ℕ) (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun p : Disorder × Plane => forwardClockProfile β N a M h₀ p.2 p.1) := by
  apply Smoothing.measurable_centered_profile_log_param β a M
    (cellAverage N fun y => Real.exp (h₀ y)) _ measurable_fst
  intro w
  exact measurable_const.ite
    (measurableSet_eq_fun measurable_const ((measurable_latticePoint N).comp measurable_snd))
    measurable_const

private theorem forwardClock_profile_pairing_measurable (β : ℝ) (N a b M : ℕ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    Measurable (fun ω : Disorder => ∫ x, φ x *
      (forwardClockProfile β N a M h₀ x ω - forwardClockProfile β N b M h₀ x ω)) := by
  have hm : Measurable (fun p : Disorder × Plane => φ p.2 *
      (forwardClockProfile β N a M h₀ p.2 p.1 - forwardClockProfile β N b M h₀ p.2 p.1)) :=
    (φ.continuous.measurable.comp measurable_snd).mul
      ((forwardClock_profile_measurable β N a M h₀).sub
        (forwardClock_profile_measurable β N b M h₀))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private theorem forwardClock_spatial_integrability (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (ω : Disorder) :
    Integrable (fun x : Plane => φ x * kpzLattice ϑ N t h₀ x ω) := by
  obtain ⟨B, hB⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hb : ∃ B : ℝ, ∀ x, |φ x| ≤ B :=
    ⟨B, fun x => by simpa only [Real.norm_eq_abs] using hB x⟩
  let G : Site → ℝ := fun z => Real.log (∫ y, Real.exp (h₀ y) *
      ((N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) 0 (evenCeil (N * t))
        (latticePoint N y) z ω)) - kpzLatticeCentring ϑ N t
  simpa only [G, kpzLattice, rescaledP2P, mul_zero, evenCeil_zero, Nat.sub_zero] using
    Smoothing.integrable_mul_siteFunction_latticePoint N hN φ.continuous.measurable
      φ.hasCompactSupport hb G

private theorem forwardClock_profile_spatial_integrability (β : ℝ) {N : ℕ} (hN : 0 < N)
    (a M : ℕ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (ω : Disorder) :
    Integrable (fun x => φ x * forwardClockProfile β N a M h₀ x ω) := by
  obtain ⟨B, hB⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  exact Smoothing.integrable_mul_siteFunction_latticePoint N hN φ.continuous.measurable
    φ.hasCompactSupport ⟨B, fun x => by simpa only [Real.norm_eq_abs] using hB x⟩
    (fun z => Real.log (profileP2Fun β a M (fun w => if w = z then 1 else 0)
      (cellAverage N fun y => Real.exp (h₀ y)) ω) -
        ∫ ζ, Real.log (profileP2Fun β a M (fun w => if w = z then 1 else 0)
          (fun _ => 1) ζ) ∂disorderLaw)


private theorem forwardClock_reversed_increment_le (ϑ : ℝ) (N m m' L : ℕ)
    (hc : (m = L ∧ m' + 2 = L) ∨ (m + 2 = L ∧ m' = L) ∨ (m = L ∧ m' = L))
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    eLpNorm (fun ω : Disorder => ∫ x, φ x *
      (forwardClockProfile (criticalBeta ϑ N) N (L - m) L h₀ x
          (PolymerCalculus.reversedDisorder L ω) -
        forwardClockProfile (criticalBeta ϑ N) N (L - m') L h₀ x
          (PolymerCalculus.reversedDisorder L ω))) 2 disorderLaw ≤
      eLpNorm (fun ω : Disorder => ∫ x, φ x *
        (forwardClockProfile (criticalBeta ϑ N) N 0 L h₀ x ω -
          forwardClockProfile (criticalBeta ϑ N) N 2 L h₀ x ω)) 2 disorderLaw := by
  let F : Disorder → ℝ := fun ω => ∫ x, φ x *
    (forwardClockProfile (criticalBeta ϑ N) N (L - m) L h₀ x ω -
      forwardClockProfile (criticalBeta ϑ N) N (L - m') L h₀ x ω)
  change eLpNorm (F ∘ PolymerCalculus.reversedDisorder L) 2 disorderLaw ≤ _
  rw [eLpNorm_comp_measurePreserving
    (forwardClock_profile_pairing_measurable _ _ _ _ _ _ _).aestronglyMeasurable
    (PolymerCalculus.measurePreserving_reversedDisorder L)]
  change eLpNorm (fun ω : Disorder => ∫ x, φ x *
    (forwardClockProfile (criticalBeta ϑ N) N (L - m) L h₀ x ω -
      forwardClockProfile (criticalBeta ϑ N) N (L - m') L h₀ x ω)) 2 disorderLaw ≤ _
  rcases hc with ⟨hm, hm'⟩ | ⟨hm, hm'⟩ | ⟨hm, hm'⟩
  · have hq : L - m = 0 := by omega
    have hq' : L - m' = 2 := by omega
    rw [hq, hq']
  · have hq : L - m = 2 := by omega
    have hq' : L - m' = 0 := by omega
    rw [hq, hq']
    have he : (fun ω : Disorder => ∫ x, φ x *
        (forwardClockProfile (criticalBeta ϑ N) N 2 L h₀ x ω -
          forwardClockProfile (criticalBeta ϑ N) N 0 L h₀ x ω)) =
        -(fun ω : Disorder => ∫ x, φ x *
          (forwardClockProfile (criticalBeta ϑ N) N 0 L h₀ x ω -
            forwardClockProfile (criticalBeta ϑ N) N 2 L h₀ x ω)) := by
      funext ω
      change (∫ x, φ x * (forwardClockProfile (criticalBeta ϑ N) N 2 L h₀ x ω -
        forwardClockProfile (criticalBeta ϑ N) N 0 L h₀ x ω)) =
        -(∫ x, φ x * (forwardClockProfile (criticalBeta ϑ N) N 0 L h₀ x ω -
          forwardClockProfile (criticalBeta ϑ N) N 2 L h₀ x ω))
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [he, eLpNorm_neg]
  · rw [hm, hm']
    simp only [sub_self, mul_zero, integral_zero]
    change eLpNorm (0 : Disorder → ℝ) 2 disorderLaw ≤ _
    rw [eLpNorm_zero]
    exact bot_le

private theorem forwardClock_tested_increment_le (ϑ : ℝ) {N m m' L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hmEven : Even m) (hm'Even : Even m') (hLEven : Even L)
    (hc : (m = L ∧ m' + 2 = L) ∨ (m + 2 = L ∧ m' = L) ∨ (m = L ∧ m' = L))
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    eLpNorm (fun ω : Disorder => ∫ x, φ x *
      (kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω - kpzLattice ϑ N ((m' : ℝ) / N) h₀ x ω))
      2 disorderLaw ≤
      (ENNReal.ofReal (Real.sqrt (9 * criticalBeta ϑ N ^ 2 + 3 * criticalBeta ϑ N ^ 4) *
        ∫ x, |φ x|) +
        ENNReal.ofReal (Real.sqrt (9 * criticalBeta ϑ N ^ 2 + 3 * criticalBeta ϑ N ^ 4) *
          ∫ x, |φ x|)) +
      eLpNorm (fun ω : Disorder => ∫ x, φ x *
        (forwardClockProfile (criticalBeta ϑ N) N 0 L h₀ x ω -
          forwardClockProfile (criticalBeta ϑ N) N 2 L h₀ x ω)) 2 disorderLaw := by
  have hmL : m ≤ L := by rcases hc with h | h | h <;> omega
  have hm'L : m' ≤ L := by rcases hc with h | h | h <;> omega
  let P (a : ℕ) (x : Plane) (ω : Disorder) := forwardClockProfile (criticalBeta ϑ N) N a L h₀ x
    (PolymerCalculus.reversedDisorder L ω)
  let E (n : ℕ) : Disorder → ℝ := fun ω => ∫ x, φ x *
    (kpzLattice ϑ N ((n : ℝ) / N) h₀ x ω - P (L - n) x ω)
  let R : Disorder → ℝ := fun ω => ∫ x, φ x * (P (L - m) x ω - P (L - m') x ω)
  have he : (fun ω : Disorder => ∫ x, φ x *
      (kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω - kpzLattice ϑ N ((m' : ℝ) / N) h₀ x ω)) =
      E m - E m' + R := by
    funext ω
    have hF := forwardClock_spatial_integrability ϑ hN ((m : ℝ) / N) h₀ φ ω
    have hG := forwardClock_spatial_integrability ϑ hN ((m' : ℝ) / N) h₀ φ ω
    have hP := forwardClock_profile_spatial_integrability (criticalBeta ϑ N) hN (L - m) L h₀ φ
      (PolymerCalculus.reversedDisorder L ω)
    have hQ := forwardClock_profile_spatial_integrability (criticalBeta ϑ N) hN (L - m') L h₀ φ
      (PolymerCalculus.reversedDisorder L ω)
    change (∫ x, φ x * (kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      kpzLattice ϑ N ((m' : ℝ) / N) h₀ x ω)) = E m ω - E m' ω + R ω
    dsimp only [E, R]
    simp_rw [mul_sub]
    rw [integral_sub hF hG, integral_sub hF hP, integral_sub hG hQ, integral_sub hP hQ]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm (E m - E m') 2 disorderLaw + eLpNorm R 2 disorderLaw :=
      eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (E m) 2 disorderLaw + eLpNorm (E m') 2 disorderLaw) + eLpNorm R 2 disorderLaw :=
      add_le_add (eLpNorm_sub_le (by norm_num)) le_rfl
    _ ≤ _ := add_le_add
      (add_le_add (forwardClock_tested_boundary_le ϑ hN hm hmEven hLEven hmL h₀ φ)
        (forwardClock_tested_boundary_le ϑ hN hm' hm'Even hLEven hm'L h₀ φ))
      (forwardClock_reversed_increment_le ϑ N m m' L hc h₀ φ)

/-- Two-step changes of the forward even clock vanish in tested L², including
both endpoint corrections and the deterministic centering increment. -/
theorem tendsto_eLpNorm_tested_kpzLattice_evenClockPerturb
    (ϑ t : ℝ) (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (r : ℕ → ℤ) (hr : ∀ N, r N = -2 ∨ r N = 0 ∨ r N = 2) :
    Tendsto (fun N : ℕ => eLpNorm (fun ω : Disorder =>
      ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
        kpzLattice ϑ N (t + (r N : ℝ) / (N : ℝ)) h₀ x ω))
      2 disorderLaw) atTop (𝓝 0) := by
  let m (N : ℕ) := evenCeil ((N : ℝ) * t)
  let m' (N : ℕ) := evenCeil ((N : ℝ) * (t + (r N : ℝ) / N))
  let L (N : ℕ) := max (m N) (m' N)
  have hLEven (N : ℕ) : Even (L N) := by
    rcases le_total (m N) (m' N) with hh | hh
    · rw [show L N = m' N from max_eq_right hh]
      exact evenCeil_even _
    · rw [show L N = m N from max_eq_left hh]
      exact evenCeil_even _
  have hcommon := eventually_evenClockPerturb_common_horizon t ht r hr
  have hlo : ∀ᶠ N : ℕ in atTop, (t / 2) * N + 2 ≤ L N := hcommon.mono fun N hN => hN.2.1
  have hhi : ∀ᶠ N : ℕ in atTop, (L N : ℝ) ≤ (t + 4) * N := hcommon.mono fun N hN => hN.2.2.1
  have hR := forwardClock_reversed_twoStep ϑ (t / 2) (t + 4) (half_pos ht) L hLEven hlo hhi h₀ φ
  let B (N : ℕ) := ENNReal.ofReal (Real.sqrt
    (9 * criticalBeta ϑ N ^ 2 + 3 * criticalBeta ϑ N ^ 4) * ∫ x, |φ x|)
  have hB : Tendsto B atTop (𝓝 0) := by
    have hc : Continuous (fun β : ℝ => Real.sqrt (9 * β ^ 2 + 3 * β ^ 4) * ∫ x, |φ x|) := by
      fun_prop
    have hh := hc.continuousAt.tendsto.comp (SHF.Moments.tendsto_criticalBeta_zero ϑ)
    have hr' : Tendsto (fun N => Real.sqrt
        (9 * criticalBeta ϑ N ^ 2 + 3 * criticalBeta ϑ N ^ 4) * ∫ x, |φ x|) atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
        mul_zero, zero_add, Real.sqrt_zero, zero_mul] using hh
    simpa only [B, Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr'
  have hsum := (hB.add hB).add hR
  simp only [zero_add] at hsum
  have hbound : ∀ᶠ N : ℕ in atTop,
      eLpNorm (fun ω : Disorder => ∫ x, φ x *
        (kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N (t + (r N : ℝ) / N) h₀ x ω))
        2 disorderLaw ≤ B N + B N + eLpNorm (fun ω : Disorder => ∫ x, φ x *
          (forwardClockProfile (criticalBeta ϑ N) N 0 (L N) h₀ x ω -
            forwardClockProfile (criticalBeta ϑ N) N 2 (L N) h₀ x ω)) 2 disorderLaw := by
    filter_upwards [hcommon, eventually_evenClockPerturb_pos t ht r hr] with N hcommonN hposN
    have hN := hposN.1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hm : 1 ≤ m N := by
      have hh : (0 : ℝ) < m N := (mul_pos hNr ht).trans_le (le_evenCeil _)
      exact_mod_cast hh
    have hm' : 1 ≤ m' N := by
      have hp : 0 < t + (r N : ℝ) / N := (half_pos ht).trans_le hposN.2
      have hh : (0 : ℝ) < m' N := (mul_pos hNr hp).trans_le (le_evenCeil _)
      exact_mod_cast hh
    have hc := hcommonN.2.2.2
    have heq (s : ℝ) (x : Plane) (ω : Disorder) :
        kpzLattice ϑ N s h₀ x ω = kpzLattice ϑ N ((evenCeil (N * s) : ℝ) / N) h₀ x ω := by
      apply kpzLattice_eq_of_evenCeil_eq
      exact (SHF.Symmetries.evenCeil_scaled_nat_div hN (evenCeil_even _)).symm
    have htest : (fun ω : Disorder => ∫ x, φ x *
        (kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N (t + (r N : ℝ) / N) h₀ x ω)) =
        fun ω : Disorder => ∫ x, φ x * (kpzLattice ϑ N ((m N : ℝ) / N) h₀ x ω -
          kpzLattice ϑ N ((m' N : ℝ) / N) h₀ x ω) := by
      funext ω
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heq t x ω, heq (t + (r N : ℝ) / N) x ω]
    rw [htest]
    exact forwardClock_tested_increment_le ϑ hN hm hm' (evenCeil_even _) (evenCeil_even _)
      (hLEven N) hc h₀ φ
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [hbound, ENNReal.tendsto_nhds_zero.mp hsum ε hε] with N hN hsmall
  exact hN.trans hsmall

end Critical2DKPZ.LocalSobolev
