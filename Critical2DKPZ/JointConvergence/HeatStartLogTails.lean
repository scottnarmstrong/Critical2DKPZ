/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartInverseMoment
public import Critical2DKPZ.Analysis.Lattice.Volume
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Uniform logarithmic tails for heat-start profiles

Cell averages of a bounded exponential terminal weight stay between its deterministic
exponential bounds. Positivity of path weights transfers these bounds to the polymer profile;
finite-polymer Gaussian calculus controls the negative tail of its unweighted counterpart.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.JointConvergence

private theorem cellAverage_exp_bounds {N : ℕ} (hN : 0 < N) (z : Site)
    (hz : z ∈ evenLattice) (h₀ : Plane →ᵇ ℝ) {H : ℝ} (hH : ‖h₀‖ ≤ H) :
    Real.exp (-H) ≤ cellAverage N (fun y => Real.exp (h₀ y)) z ∧
      cellAverage N (fun y => Real.exp (h₀ y)) z ≤ Real.exp H := by
  have hfinite : volume (cell N z) ≠ ∞ := (volume_cell_lt_top hN hz).ne
  have hfint : IntegrableOn (fun y : Plane => Real.exp (h₀ y)) (cell N z) volume := by
    apply volume.integrableOn_of_bounded hfinite
      ((Real.continuous_exp.comp h₀.continuous).measurable.aestronglyMeasurable)
    filter_upwards [] with y
    change |Real.exp (h₀ y)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      h₀ y ≤ |h₀ y| := le_abs_self _
      _ = ‖h₀ y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖h₀‖ := h₀.norm_coe_le_norm y
      _ ≤ H := hH
  have hlowConstInt : IntegrableOn (fun _ : Plane => Real.exp (-H)) (cell N z) volume :=
    integrableOn_const hfinite
  have huppConstInt : IntegrableOn (fun _ : Plane => Real.exp H) (cell N z) volume :=
    integrableOn_const hfinite
  have hpointLow (y : Plane) : Real.exp (-H) ≤ Real.exp (h₀ y) := by
    apply Real.exp_le_exp.mpr
    have hy : |h₀ y| ≤ H := by
      calc
        |h₀ y| = ‖h₀ y‖ := Real.norm_eq_abs _
        _ ≤ ‖h₀‖ := h₀.norm_coe_le_norm y
        _ ≤ H := hH
    exact (abs_le.mp hy).1
  have hpointUpp (y : Plane) : Real.exp (h₀ y) ≤ Real.exp H := by
    apply Real.exp_le_exp.mpr
    have hy : |h₀ y| ≤ H := by
      calc
        |h₀ y| = ‖h₀ y‖ := Real.norm_eq_abs _
        _ ≤ ‖h₀‖ := h₀.norm_coe_le_norm y
        _ ≤ H := hH
    exact (abs_le.mp hy).2
  have hlowInt :
      (∫ y in cell N z, Real.exp (-H) ∂volume) ≤
        ∫ y in cell N z, Real.exp (h₀ y) ∂volume :=
    setIntegral_mono_on hlowConstInt hfint (measurableSet_cell N z) (fun y _ => hpointLow y)
  have huppInt :
      (∫ y in cell N z, Real.exp (h₀ y) ∂volume) ≤
        ∫ y in cell N z, Real.exp H ∂volume :=
    setIntegral_mono_on hfint huppConstInt (measurableSet_cell N z) (fun y _ => hpointUpp y)
  have hscale : 0 ≤ (volume (cell N z)).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hlowAvg :
      cellAverage N (fun _ => Real.exp (-H)) z ≤
        cellAverage N (fun y => Real.exp (h₀ y)) z := by
    unfold cellAverage
    exact mul_le_mul_of_nonneg_left hlowInt hscale
  have huppAvg :
      cellAverage N (fun y => Real.exp (h₀ y)) z ≤
        cellAverage N (fun _ => Real.exp H) z := by
    unfold cellAverage
    exact mul_le_mul_of_nonneg_left huppInt hscale
  constructor
  · simpa only [cellAverage_const hN hz] using hlowAvg
  · simpa only [cellAverage_const hN hz] using huppAvg

/-- An endpoint reached after an even number of walk steps preserves even-lattice parity. -/
theorem evenLattice_of_even_duration {w z : Site} {n : ℕ}
    (hw : w ∈ evenLattice) (hn : Even n) (hz : z ∈ Polymer.endpoints w n) :
    z ∈ evenLattice := by
  obtain ⟨s, hs⟩ := Polymer.mem_endpoints_iff w z n |>.mp hz
  have hwalk := Polymer.walkPosition_parity w s
  have hpar : (z 0 + z 1) ≡ (w 0 + w 1 + (n : ℤ)) [ZMOD 2] := by
    simpa only [hs] using hwalk
  have hsumEven : Even (w 0 + w 1 + (n : ℤ)) := by
    have hn' : Even (n : ℤ) := by exact_mod_cast hn
    exact hw.add hn'
  have hzero : (0 : ℤ) ≡ (w 0 + w 1 + (n : ℤ)) [ZMOD 2] :=
    (even_iff_two_dvd.mp hsumEven).zero_modEq_int
  have hmod : (z 0 + z 1) ≡ 0 [ZMOD 2] := hpar.trans hzero.symm
  have hdiv : (2 : ℤ) ∣ z 0 + z 1 := by
    have hdiv' : (2 : ℤ) ∣ -(z 0 + z 1) := by simpa using hmod.dvd
    exact dvd_neg.mp hdiv'
  exact even_iff_two_dvd.mpr hdiv

private theorem terminalProfile_le_of_reachable {β : ℝ} (a d : ℕ) (w : Site)
    (f g : Site → ℝ) (ω : Disorder)
    (hfg : ∀ z ∈ Polymer.endpoints w d, f z ≤ g z) :
    (∑' z, pointToPoint β a d w z ω * f z) ≤
      ∑' z, pointToPoint β a d w z ω * g z := by
  rw [Polymer.tsum_pointToPoint_mul_eq_sum β a d w f ω,
    Polymer.tsum_pointToPoint_mul_eq_sum β a d w g ω]
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_left (hfg z hz)
    (Polymer.pointToPoint_nonneg β a d w z ω)

/-- Pointwise monotonicity of the polymer profile when terminal weights are ordered on all
reachable endpoints of its finitely supported start profile. -/
theorem profileP2Fun_le_of_reachable {β : ℝ} (a b : ℕ) (ν f g : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hfg : ∀ w ∈ A, ∀ z ∈ Polymer.endpoints w (b - a), f z ≤ g z) (ω : Disorder) :
    profileP2Fun β a b ν f ω ≤ profileP2Fun β a b ν g ω := by
  rw [Polymer.profileP2Fun_eq_sum β a b ν f A hνA ω,
    Polymer.profileP2Fun_eq_sum β a b ν g A hνA ω]
  apply Finset.sum_le_sum
  intro w hw
  exact mul_le_mul_of_nonneg_left
    (terminalProfile_le_of_reachable (β := β) (a := a) (d := b - a)
      w f g ω (hfg w hw))
    (hν0 w)

/-- A constant terminal weight factors out of a polymer profile. -/
theorem profileP2Fun_const_terminal {β : ℝ} (a b : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (c : ℝ) (ω : Disorder) :
    profileP2Fun β a b ν (fun _ => c) ω =
      c * profileP2Fun β a b ν (fun _ => 1) ω := by
  have hflat : profileP2Fun β a b ν (fun _ => 1) ω =
      ∑ w ∈ A, ν w * pointToPlane β a (b - a) w ω := by
    rw [Polymer.profileP2Fun_eq_sum β a b ν (fun _ => 1) A hνA ω]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [mul_one, Polymer.tsum_pointToPoint]
  rw [Polymer.profileP2Fun_eq_sum β a b ν (fun _ => c) A hνA ω]
  calc
    (∑ w ∈ A, ν w * (∑' z, pointToPoint β a (b - a) w z ω * c)) =
        ∑ w ∈ A, ν w * (pointToPlane β a (b - a) w ω * c) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [tsum_mul_right, Polymer.tsum_pointToPoint]
    _ = c * ∑ w ∈ A, ν w * pointToPlane β a (b - a) w ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = c * profileP2Fun β a b ν (fun _ => 1) ω := by rw [hflat]

/-- Lattice log tails with the constant displayed in terms of a horizon bound. -/
theorem measure_abs_log_profileP2Fun_heatStart_gt_le_of_horizon_bound_constants
    (ϑ : ℝ) {s T δ U : ℝ}
    (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) (hU : δ + (T - s) + 2 ≤ U)
    (C₂ D : ℝ)
    (hC₂ : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ Set.Icc (-|ϑ|) |ϑ|, ∀ m n : ℕ,
      m ≤ n → 1 ≤ n → (n : ℝ) ≤ U * N →
      ∫ ω, smoothedP2Plane (criticalBeta θ N) m n 0 ω ^ 2 ∂disorderLaw ≤
        1 + C₂ * (replicaOverlap n - replicaOverlap m) /
          Real.log (1 + (N : ℝ) / n))
    (hD : ∀ m n : ℕ, m ≤ n →
      |Real.pi * (replicaOverlap n - replicaOverlap m) -
        Real.log (((max n 1 : ℕ) : ℝ) / ((max m 1 : ℕ) : ℝ))| ≤ D)
    (H : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ x : Plane, ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
      ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal ≤
        (Real.exp H * (1 + |1 + |C₂| *
          ((Real.log (U / δ) + D) / Real.pi) / Real.log (1 + 1 / U)|)) * Real.exp (-u) := by
  let Cinv : ℝ := 1 + |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
    Real.log (1 + 1 / U)
  have hDnonneg : 0 ≤ D := by
    have h := hD 1 1 (by omega)
    simpa using h
  have hInv := integral_inv_profileP2Fun_heatStart_le_of_horizon_bound_constants
    ϑ hs hsT hδ hU C₂ D hC₂ hD
  have hfactor : 0 ≤ 1 + |Cinv| := by positivity
  filter_upwards [hInv, Filter.eventually_ge_atTop 2] with N hInvN hN
  have hNr : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNr
  intro x h₀ hh₀ u hu
  have hHnonneg : 0 ≤ H := le_trans (norm_nonneg h₀) hh₀
  let a : ℕ := evenCeil (N * s)
  let b : ℕ := evenCeil (N * T)
  let m : ℕ := evenCeil (N * δ)
  let d : ℕ := b - a
  let x₀ : Site := latticePoint N x
  let A₀ : Finset Site := Polymer.endpoints x₀ m
  let ν : Site → ℝ := fun w => srwKernel m (w - x₀)
  let f : Site → ℝ := fun z => cellAverage N (fun y => Real.exp (h₀ y)) z
  let B : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω
  let F : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν f ω
  have ha_le_b : a ≤ b := by
    dsimp [a, b]
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg N)
  have hdEven : Even d := by
    obtain ⟨ka, hka⟩ := evenCeil_even (N * s)
    obtain ⟨kb, hkb⟩ := evenCeil_even (N * T)
    have hka_le : ka ≤ kb := by
      have h : evenCeil (N * s) ≤ evenCeil (N * T) := by
        apply evenCeil_mono
        exact mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg N)
      rw [hka, hkb] at h
      omega
    dsimp [d, a, b]
    rw [hka, hkb]
    refine ⟨kb - ka, ?_⟩
    omega
  have hmEven : Even m := by dsimp [m]; exact evenCeil_even (N * δ)
  have hx₀Even : x₀ ∈ evenLattice := by dsimp [x₀]; exact latticePoint_mem_evenLattice N x
  have hνA : ∀ w ∉ A₀, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem m x₀ w hw
  have hν0 : ∀ w, 0 ≤ ν w := by
    intro w
    exact Polymer.kernel_nonneg m (w - x₀)
  have hν1 : ∑ w ∈ A₀, ν w = 1 := by
    simpa [A₀, ν] using Polymer.sum_srwKernel_endpoints m x₀
  have htermLow : ∀ w ∈ A₀, ∀ z ∈ Polymer.endpoints w d, Real.exp (-H) ≤ f z := by
    intro w hw z hz
    have hwEven : w ∈ evenLattice := evenLattice_of_even_duration hx₀Even hmEven hw
    have hzEven : z ∈ evenLattice := evenLattice_of_even_duration hwEven hdEven hz
    exact (cellAverage_exp_bounds hNr z hzEven h₀ hh₀).1
  have htermUpp : ∀ w ∈ A₀, ∀ z ∈ Polymer.endpoints w d, f z ≤ Real.exp H := by
    intro w hw z hz
    have hwEven : w ∈ evenLattice := evenLattice_of_even_duration hx₀Even hmEven hw
    have hzEven : z ∈ evenLattice := evenLattice_of_even_duration hwEven hdEven hz
    exact (cellAverage_exp_bounds hNr z hzEven h₀ hh₀).2
  have hprofileLow : ∀ ω, Real.exp (-H) * B ω ≤ F ω := by
    intro ω
    have hmono := profileP2Fun_le_of_reachable (β := criticalBeta ϑ N) (a := a) (b := b) ν
      (fun _ => Real.exp (-H)) f A₀ hνA hν0 htermLow ω
    simpa [B, F, profileP2Fun_const_terminal (β := criticalBeta ϑ N) a b ν A₀ hνA
      (Real.exp (-H)) ω] using hmono
  have hprofileUpp : ∀ ω, F ω ≤ Real.exp H * B ω := by
    intro ω
    have hmono := profileP2Fun_le_of_reachable (β := criticalBeta ϑ N) (a := a) (b := b) ν
      f (fun _ => Real.exp H) A₀ hνA hν0 htermUpp ω
    simpa [B, F, profileP2Fun_const_terminal (β := criticalBeta ϑ N) a b ν A₀ hνA
      (Real.exp H) ω] using hmono
  have hBpos : ∀ ω, 0 < B ω := by
    intro ω
    exact OnePoint.profileP2Fun_pos_of_normalized (criticalBeta ϑ N) a b ν A₀
      hνA hν0 hν1 ω
  have hFpos : ∀ ω, 0 < F ω := by
    intro ω
    have h := hprofileLow ω
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (hBpos ω)) h
  have hlogDistance : ∀ ω, |Real.log (F ω) - Real.log (B ω)| ≤ H := by
    intro ω
    have hlo := Real.log_le_log (mul_pos (Real.exp_pos _) (hBpos ω)) (hprofileLow ω)
    have hhi := Real.log_le_log (hFpos ω) (hprofileUpp ω)
    have hlow' : -H + Real.log (B ω) ≤ Real.log (F ω) := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (hBpos ω)), Real.log_exp] at hlo
      exact hlo
    have hhi' : Real.log (F ω) ≤ H + Real.log (B ω) := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (hBpos ω)), Real.log_exp] at hhi
      exact hhi
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hlogTriangle (ω : Disorder) :
      |Real.log (F ω)| ≤ |Real.log (B ω)| + H := by
    calc
      |Real.log (F ω)| = |Real.log (B ω) + (Real.log (F ω) - Real.log (B ω))| := by congr 1; ring
      _ ≤ |Real.log (B ω)| + |Real.log (F ω) - Real.log (B ω)| := abs_add_le _ _
      _ ≤ |Real.log (B ω)| + H := add_le_add le_rfl (hlogDistance ω)
  have hBint : Integrable B disorderLaw := by
    exact memLp_one_iff_integrable.mp
      (Polymer.memLp_profileP2Fun_finset (criticalBeta ϑ N) a b ν
        (fun _ => 1) A₀ hνA 1 (by norm_num))
  have hBmean : ∫ ω, B ω ∂disorderLaw = 1 := by
    change ∫ ω, profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω ∂disorderLaw = 1
    rw [Polymer.integral_profileP2Fun_finset (criticalBeta ϑ N) a b ν
      (fun _ => 1) A₀ hνA]
    simp_rw [mul_one, Polymer.tsum_srwKernel]
    simpa only [mul_one] using hν1
  have hBInvInt : Integrable (fun ω => (B ω)⁻¹) disorderLaw := by
    have h := OnePoint.integrable_rpow_profileP2Fun (criticalBeta ϑ N) a b ν A₀
      hνA hν0 hν1 (-1)
    simpa only [B, Real.rpow_neg_one] using h
  have hBInv := hInvN x
  have hBInvAbs : ∫ ω, (B ω)⁻¹ ∂disorderLaw ≤ |Cinv| :=
    hBInv.trans (le_abs_self Cinv)
  have hGint : Integrable (fun ω => B ω + (B ω)⁻¹) disorderLaw := hBint.add hBInvInt
  have hGnonneg : ∀ ω, 0 ≤ B ω + (B ω)⁻¹ := by
    intro ω
    exact add_nonneg (le_of_lt (hBpos ω)) (inv_nonneg.mpr (hBpos ω).le)
  have hGmean : ∫ ω, B ω + (B ω)⁻¹ ∂disorderLaw ≤ 1 + |Cinv| := by
    rw [integral_add hBint hBInvInt, hBmean]
    exact add_le_add le_rfl hBInvAbs
  by_cases huH : u ≤ H
  · have hmeasure : (disorderLaw {ω | u < |Real.log (F ω)|}).toReal ≤ 1 := by
      simpa only [measureReal_def] using measureReal_le_one
    have hunit : 1 ≤ Real.exp H * (1 + |Cinv|) * Real.exp (-u) := by
      have hExp : 1 ≤ Real.exp H * Real.exp (-u) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      calc
        1 ≤ Real.exp H * Real.exp (-u) := hExp
        _ ≤ Real.exp H * (1 + |Cinv|) * Real.exp (-u) := by
          have hfactor1 : 1 ≤ 1 + |Cinv| := by nlinarith [abs_nonneg Cinv]
          calc
            Real.exp H * Real.exp (-u) =
                Real.exp H * (1 * Real.exp (-u)) := by ring
            _ ≤ Real.exp H * ((1 + |Cinv|) * Real.exp (-u)) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_right hfactor1 (Real.exp_nonneg _)
              · exact Real.exp_nonneg _
            _ = _ := by ring
    exact hmeasure.trans hunit
  · have huH' : H < u := lt_of_not_ge huH
    let v : ℝ := u - H
    have hv : 0 < v := by dsimp [v]; linarith
    have hsubset : {ω | u < |Real.log (F ω)|} ⊆ {ω | v < |Real.log (B ω)|} := by
      intro ω hω
      change u < |Real.log (F ω)| at hω
      have hlog := hlogTriangle ω
      dsimp [v]
      linarith
    let G : Disorder → ℝ := fun ω => Real.exp (-v) * (B ω + (B ω)⁻¹)
    have hGint' : Integrable G disorderLaw := hGint.const_mul (Real.exp (-v))
    have hGnonneg' : ∀ ω, 0 ≤ G ω := by
      intro ω
      exact mul_nonneg (Real.exp_nonneg _) (hGnonneg ω)
    have hmark : disorderLaw {ω | v < |Real.log (B ω)|} ≤
        ENNReal.ofReal (∫ ω, G ω ∂disorderLaw) := by
      apply Integrable.measure_le_integral hGint' (Filter.Eventually.of_forall hGnonneg')
      intro ω hω
      change v < |Real.log (B ω)| at hω
      dsimp [G]
      have hlarge : Real.exp v < Real.exp |Real.log (B ω)| :=
        Real.exp_lt_exp.mpr hω
      have hexpAbs : Real.exp |Real.log (B ω)| ≤ B ω + (B ω)⁻¹ := by
        by_cases hlog : 0 ≤ Real.log (B ω)
        · rw [abs_of_nonneg hlog, Real.exp_log (hBpos ω)]
          linarith [inv_nonneg.mpr (le_of_lt (hBpos ω))]
        · have hlog' : Real.log (B ω) ≤ 0 := le_of_not_ge hlog
          rw [abs_of_nonpos hlog', Real.exp_neg, Real.exp_log (hBpos ω)]
          linarith [le_of_lt (hBpos ω)]
      have hlarge' : Real.exp v < B ω + (B ω)⁻¹ := lt_of_lt_of_le hlarge hexpAbs
      have hmul := mul_lt_mul_of_pos_left hlarge' (Real.exp_pos (-v))
      have hexpCancel : Real.exp (-v) * Real.exp v = 1 := by
        rw [← Real.exp_add]
        simp
      rw [hexpCancel] at hmul
      exact hmul.le
    have hreal : (disorderLaw {ω | v < |Real.log (B ω)|}).toReal ≤
        (ENNReal.ofReal (∫ ω, G ω ∂disorderLaw)).toReal :=
      ENNReal.toReal_mono (ENNReal.ofReal_ne_top
        (r := ∫ ω, G ω ∂disorderLaw)) hmark
    have hGmean : ∫ ω, G ω ∂disorderLaw ≤ Real.exp (-v) * (1 + |Cinv|) := by
      change ∫ ω, Real.exp (-v) * (B ω + (B ω)⁻¹) ∂disorderLaw ≤ _
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hGmean (Real.exp_nonneg _)
    have hGnonnegInt : 0 ≤ ∫ ω, G ω ∂disorderLaw := integral_nonneg_of_ae
      (Filter.Eventually.of_forall hGnonneg')
    have htail :
        (disorderLaw {ω | v < |Real.log (B ω)|}).toReal ≤
          Real.exp (-v) * (1 + |Cinv|) := by
      calc
        _ ≤ (∫ ω, G ω ∂disorderLaw) := by
          simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae
            (Filter.Eventually.of_forall hGnonneg'))] using hreal
        _ ≤ _ := hGmean
    have htailF :
        (disorderLaw {ω | u < |Real.log (F ω)|}).toReal ≤
          Real.exp (-v) * (1 + |Cinv|) :=
      (measureReal_mono hsubset).trans htail
    have hexpShift : Real.exp (-v) = Real.exp H * Real.exp (-u) := by
      dsimp [v]
      rw [show -(u - H) = H + (-u) by ring, Real.exp_add]
    calc
      _ ≤ Real.exp (-v) * (1 + |Cinv|) := htailF
      _ = Real.exp H * (1 + |Cinv|) * Real.exp (-u) := by rw [hexpShift]; ring

/-- At fixed critical parameter and positive heat width, the logarithmic tails are exponentially bounded uniformly over spatial centers and terminal profiles with a common norm bound. -/
theorem measure_abs_log_profileP2Fun_heatStart_gt_le_of_horizon_bound
    (ϑ : ℝ) {s T δ U : ℝ} (hs : 0 ≤ s) (hsT : s < T)
    (hδ : 0 < δ) (hU : δ + (T - s) + 2 ≤ U) (H : ℝ) :
    ∃ C₂ D C : ℝ, 0 ≤ D ∧
      C = Real.exp H * (1 + |1 + |C₂| *
        ((Real.log (U / δ) + D) / Real.pi) / Real.log (1 + 1 / U)|) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : Plane, ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
      ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal ≤ C * Real.exp (-u) := by
  let A : ℝ := |ϑ|
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A U
  obtain ⟨D, hD⟩ := OnePoint.replicaOverlap_sub_log_bounded
  have hDnonneg : 0 ≤ D := by
    have h := hD 1 1 (by omega)
    simpa using h
  let C : ℝ := Real.exp H * (1 + |1 + |C₂| *
    ((Real.log (U / δ) + D) / Real.pi) / Real.log (1 + 1 / U)|)
  have hbound := measure_abs_log_profileP2Fun_heatStart_gt_le_of_horizon_bound_constants
    ϑ hs hsT hδ hU C₂ D hC₂ hD H
  refine ⟨C₂, D, C, hDnonneg, rfl, ?_⟩
  simpa [C] using hbound

/-- If the start time is `t + δ` and the heat width is `δ`, the lattice log-tail
coefficient grows at most linearly in `1 + |log δ|`, uniformly for small widths. -/
theorem measure_abs_log_profileP2Fun_heatStart_gt_le_log_width
    (ϑ : ℝ) {t T δ₁ : ℝ} (ht : 0 ≤ t) (htT : t < T)
    (hδ₁ : 0 < δ₁) (hδ₁T : δ₁ ≤ T - t) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Set.Ioo 0 δ₁,
      ∀ᶠ N : ℕ in atTop, ∀ x : Plane, ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
        ∀ u : ℝ, 0 ≤ u →
        (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N)
            (evenCeil (N * (t + δ))) (evenCeil (N * T))
            (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
            (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal ≤
          C * (1 + |Real.log δ|) * Real.exp (-u) := by
  let A : ℝ := |ϑ|
  let U : ℝ := T - t + δ₁ + 2
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A U
  obtain ⟨D, hD⟩ := OnePoint.replicaOverlap_sub_log_bounded
  have hDnonneg : 0 ≤ D := by
    have h := hD 1 1 (by omega)
    simpa using h
  have hUgt1 : 1 < U := by dsimp [U]; linarith
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hUgt1.le
  have hdenpos : 0 < Real.log (1 + 1 / U) := by
    apply Real.log_pos
    have : 0 < 1 / U := by positivity
    linarith
  let K : ℝ := |C₂| / (Real.pi * Real.log (1 + 1 / U))
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  let C : ℝ := Real.exp H * (2 + K * (Real.log U + D + 1))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro δ hδ
  have hs : 0 ≤ t + δ := by linarith [ht, hδ.1]
  have hsT : t + δ < T := by linarith [hδ.2, hδ₁T]
  have hUbound : δ + (T - (t + δ)) + 2 ≤ U := by
    calc
      δ + (T - (t + δ)) + 2 = T - t + 2 := by ring
      _ ≤ T - t + δ₁ + 2 := by linarith [hδ.2]
      _ = U := rfl
  have hUδ : δ ≤ U := by dsimp [U]; linarith [hδ.1, hδ₁T]
  have hUδ' : 1 * δ ≤ U := by simpa using hUδ
  have hlogratio : 0 ≤ Real.log (U / δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ.1).2 hUδ')
  have hBnonneg : 0 ≤ |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
      Real.log (1 + 1 / U) := by positivity
  have hBbound : |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
      Real.log (1 + 1 / U) ≤ K * (Real.log U + D + |Real.log δ|) := by
    have hlogdiv : Real.log (U / δ) = Real.log U - Real.log δ := by
      rw [Real.log_div (by positivity) hδ.1.ne']
    have hnum : Real.log (U / δ) + D ≤ Real.log U + D + |Real.log δ| := by
      rw [hlogdiv]
      linarith [neg_abs_le (Real.log δ)]
    have hcoeff : |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
        Real.log (1 + 1 / U) = K * (Real.log (U / δ) + D) := by
      dsimp [K]
      field_simp [Real.pi_ne_zero, ne_of_gt hdenpos]
    rw [hcoeff]
    exact mul_le_mul_of_nonneg_left hnum hKnonneg
  let Cδ : ℝ := Real.exp H *
    (1 + |1 + |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
      Real.log (1 + 1 / U)|)
  have hCδeq : Cδ = Real.exp H *
      (2 + |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
        Real.log (1 + 1 / U)) := by
    dsimp [Cδ]
    rw [abs_of_nonneg (by linarith [hBnonneg])]
    ring
  have hCδbound : Cδ ≤ C * (1 + |Real.log δ|) := by
    have hx : 0 ≤ |Real.log δ| := abs_nonneg _
    have hbase : 0 ≤ Real.log U + D := add_nonneg hlogU hDnonneg
    have hcross : 0 ≤ (K * (Real.log U + D)) * |Real.log δ| :=
      mul_nonneg (mul_nonneg hKnonneg hbase) hx
    have hfactor : 2 + K * (Real.log U + D + |Real.log δ|) ≤
        (2 + K * (Real.log U + D + 1)) * (1 + |Real.log δ|) := by
      nlinarith [hcross]
    calc
      Cδ = Real.exp H *
          (2 + |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
            Real.log (1 + 1 / U)) := hCδeq
      _ ≤ Real.exp H *
          (2 + K * (Real.log U + D + |Real.log δ|)) := by
        exact mul_le_mul_of_nonneg_left (by linarith [hBbound]) (Real.exp_nonneg _)
      _ ≤ Real.exp H *
          ((2 + K * (Real.log U + D + 1)) * (1 + |Real.log δ|)) :=
        mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg _)
      _ = C * (1 + |Real.log δ|) := by dsimp [C]; ring
  have hTail := measure_abs_log_profileP2Fun_heatStart_gt_le_of_horizon_bound_constants
    ϑ hs hsT hδ.1 hUbound C₂ D hC₂ hD H
  filter_upwards [hTail] with N hTailN
  intro x h₀ hh₀ u hu
  calc
    _ ≤ Cδ * Real.exp (-u) := hTailN x h₀ hh₀ u hu
    _ ≤ (C * (1 + |Real.log δ|)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hCδbound (Real.exp_nonneg _)

/-- Lattice log tails at a fixed heat-start width. -/
theorem measure_abs_log_profileP2Fun_heatStart_gt_le (ϑ : ℝ) {s T δ : ℝ}
    (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) (H : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ x : Plane, ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
      ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal ≤ C * Real.exp (-u) := by
  obtain ⟨C₂, D, C, hD, hC, hbound⟩ :=
    measure_abs_log_profileP2Fun_heatStart_gt_le_of_horizon_bound
      ϑ hs hsT hδ le_rfl H
  exact ⟨C, hbound⟩

end Critical2DKPZ.JointConvergence

end
