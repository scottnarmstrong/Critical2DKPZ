/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeReversalTerminalBoundary
public import Critical2DKPZ.LocalSobolev.LatticeReversalMass
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
public import Critical2DKPZ.Smoothing.Measurability
public import Critical2DKPZ.Smoothing.ChapmanKolmogorov
public import Critical2DKPZ.Smoothing.Decomposition
public import Critical2DKPZ.Smoothing.ParityHelpers
public import Critical2DKPZ.PolymerCalculus.TimeReversal
import Mathlib.Tactic

/-! # Terminally cancelled profile under lattice time reversal -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.LocalSobolev

/-- After shifting the reversed environment to the start of its point polymer, a reversed
point-profile factors at the penultimate time into its point-to-plane mass and terminal endpoint
profile. -/
theorem profileP2Fun_reversedPointFactor (β : ℝ) {L m : ℕ} (hmL : m ≤ L)
    (x : Site) (f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β (L - m) L (fun z => if z = x then 1 else 0) f
        (PolymerCalculus.reversedDisorder L ω) =
      pointToPlane β 0 (m - 1) x
          (Smoothing.shiftEnvironment (L - m)
            (PolymerCalculus.reversedDisorder L ω)) *
        profileP2Fun β (m - 1) m
          (endpointDist β (m - 1) x
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω))) f
          (Smoothing.shiftEnvironment (L - m)
            (PolymerCalculus.reversedDisorder L ω)) := by
  let d := L - m
  let ω' := Smoothing.shiftEnvironment d (PolymerCalculus.reversedDisorder L ω)
  let ν : Site → ℝ := fun z => if z = x then 1 else 0
  have hdm : d + m = L := by dsimp [d]; exact Nat.sub_add_cancel hmL
  have htime : profileP2Fun β (d + 0) (d + m) ν f
      (PolymerCalculus.reversedDisorder L ω) = profileP2Fun β 0 m ν f ω' :=
    Smoothing.profileP2Fun_timeShift β d 0 m ν f
      (PolymerCalculus.reversedDisorder L ω)
  have htime' : profileP2Fun β (L - m) L ν f
      (PolymerCalculus.reversedDisorder L ω) = profileP2Fun β 0 m ν f ω' := by
    simpa [d, ω', Nat.add_zero, hdm] using htime
  rw [htime']
  have hfactor := Smoothing.profileP2Fun_point_eq_mul β (Nat.sub_le m 1) x f ω'
  simpa only [ν, Nat.zero_add] using hfactor

/-- The logarithmic change from a terminal profile with its final Gaussian slice present to the
same profile with that slice removed is small in `L¹`; the square estimate is the random-endpoint
boundary estimate. -/
theorem integral_abs_log_endpointDist_terminal_ratio_le (β : ℝ) (n : ℕ)
    (x : Site) (f : Site → ℝ) (hf : ∀ z, 0 < f z) :
    Integrable (fun ω => |Real.log
      (profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω)|)
      disorderLaw ∧
    (∫ ω, |Real.log
      (profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω)|
      ∂disorderLaw) ≤ Real.sqrt (β ^ 2 + β ^ 4 / 4) := by
  let η : Disorder → Site → ℝ := endpointDist β n x
  let F : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β n (n + 1) (η ω) f ω) -
      Real.log (profileP2Fun 0 n (n + 1) (η ω) f ω)
  have hη (z : Site) : Measurable (fun ω : Disorder => η ω z) := by
    exact Polymer.measurable_endpointDist β n x z
  have hFmeas : Measurable F := by
    dsimp [F, η]
    exact (Smoothing.measurable_profileP2Fun_param β n (n + 1) f hη measurable_id).log.sub
      (Smoothing.measurable_profileP2Fun_param 0 n (n + 1) f hη measurable_id).log
  have hratio := integral_sq_log_endpointDist_terminal_ratio_le β n x f hf
  have hF2int : Integrable (fun ω => F ω ^ 2) disorderLaw := by
    simpa only [F, η] using hratio.1
  have hFmem : MemLp F 2 disorderLaw :=
    (memLp_two_iff_integrable_sq hFmeas.aestronglyMeasurable).2 (by
      simpa only [Real.norm_eq_abs, sq_abs] using hF2int)
  have hAbsMem : MemLp (fun ω => |F ω|) 2 disorderLaw := by
    have h := hFmem.norm
    simpa only [Real.norm_eq_abs] using h
  have hAbsMem' : MemLp (fun ω => |F ω|) (ENNReal.ofReal 2) disorderLaw := by
    simpa using hAbsMem
  have honeMem : MemLp (fun _ : Disorder => (1 : ℝ)) (ENNReal.ofReal 2) disorderLaw :=
    memLp_const 1
  have honeNonneg : 0 ≤ᵐ[disorderLaw] (fun _ : Disorder => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun _ => by norm_num
  have hAbsNonneg : 0 ≤ᵐ[disorderLaw] (fun ω => |F ω|) :=
    Filter.Eventually.of_forall fun ω => abs_nonneg _
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := disorderLaw) (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two honeNonneg hAbsNonneg honeMem hAbsMem'
  have hOne : ∫ ω, (1 : ℝ) ^ 2 ∂disorderLaw = 1 := by simp
  have hSq : ∫ ω, |F ω| ^ 2 ∂disorderLaw = ∫ ω, F ω ^ 2 ∂disorderLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Pi.pow_apply] using (sq_abs (F ω))
  have hL1 :
      (∫ ω, |F ω| ∂disorderLaw) ≤
        Real.sqrt (∫ ω, F ω ^ 2 ∂disorderLaw) := by
    calc
      _ = ∫ ω, (1 : ℝ) * |F ω| ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => by ring
      _ ≤ (∫ ω, (1 : ℝ) ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) *
          (∫ ω, |F ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by
        simpa only [Real.rpow_two] using hHolder
      _ = Real.sqrt (∫ ω, F ω ^ 2 ∂disorderLaw) := by
        rw [hOne, hSq]
        rw [Real.sqrt_eq_rpow]
        norm_num
  refine ⟨?_, ?_⟩
  · have hAbsMeas : Measurable (fun ω => |F ω|) := hFmeas.abs
    have hupperInt : Integrable (fun ω => 1 + F ω ^ 2) disorderLaw :=
      (integrable_const (1 : ℝ)).add hF2int
    have hdom : ∀ ω, |F ω| ≤ 1 + F ω ^ 2 := by
      intro ω
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (F ω - 1 / 2), sq_nonneg (F ω + 1 / 2)]
    exact hupperInt.mono' hAbsMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + F ω ^ 2)]
          using hdom ω)
  · calc
      _ = ∫ ω, |F ω| ∂disorderLaw := by rfl
      _ ≤ Real.sqrt (∫ ω, F ω ^ 2 ∂disorderLaw) := hL1
      _ ≤ Real.sqrt (β ^ 2 + β ^ 4 / 4) := Real.sqrt_le_sqrt hratio.2

/-- After shifting the reflected environment to the reversed polymer's starting time, the
terminally weighted point-to-point sum is exactly its zero-noise terminal profile. The fixed
initial endpoint factor is retained separately. -/
theorem tsum_weightedPointToPoint_time_reversal_cancelled_profile
    (β : ℝ) {L m : ℕ} (hmL : m ≤ L) (hm : 1 ≤ m) (x : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' z : Site, pointToPoint β (L - m) m x z
      (PolymerCalculus.reversedDisorder L ω) *
        (f z * Real.exp (-β * ω (0, z)))) =
      Real.exp (-(β ^ 2) / 2) *
        (pointToPlane β 0 (m - 1) x
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω)) *
          profileP2Fun 0 (m - 1) m
            (endpointDist β (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω))) f
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω))) := by
  let ω' := Smoothing.shiftEnvironment (L - m)
    (PolymerCalculus.reversedDisorder L ω)
  have hdm : (L - m) + m = L := Nat.sub_add_cancel hmL
  have hterminal (z : Site) : ω' (m, z) = ω (0, z) := by
    simp [ω', Smoothing.shiftEnvironment, PolymerCalculus.reversedDisorder,
      Gaussian.reindexDisorder, PolymerCalculus.timeReversalIndex,
      PolymerCalculus.reflectedTime, hdm]
  have hshift (z : Site) :
      pointToPoint β (L - m) m x z (PolymerCalculus.reversedDisorder L ω) =
        pointToPoint β 0 m x z ω' := by
    simpa only [Nat.add_zero, ω'] using
      (Smoothing.pointToPoint_timeShift β (L - m) 0 m x z
        (PolymerCalculus.reversedDisorder L ω))
  have hmEq : (m - 1) + 1 = m := Nat.sub_add_cancel hm
  have hterminal' (z : Site) : ω' ((m - 1) + 1, z) = ω (0, z) := by
    rw [hmEq]
    exact hterminal z
  have hlen (z : Site) :
      pointToPoint β 0 m x z ω' =
        pointToPoint β 0 ((m - 1) + 1) x z ω' := by
    rw [hmEq]
  have hsum :
      (∑' z : Site, pointToPoint β (L - m) m x z
        (PolymerCalculus.reversedDisorder L ω) *
          (f z * Real.exp (-β * ω (0, z)))) =
      (∑' z : Site, pointToPoint β 0 ((m - 1) + 1) x z ω' *
        (f z * Real.exp (-β * ω' ((m - 1) + 1, z)))) := by
    apply tsum_congr
    intro z
    calc
      _ = pointToPoint β 0 m x z ω' *
          (f z * Real.exp (-β * ω (0, z))) := by rw [hshift z]
      _ = pointToPoint β 0 m x z ω' *
          (f z * Real.exp (-β * ω' (m, z))) := by rw [hterminal z]
      _ = pointToPoint β 0 ((m - 1) + 1) x z ω' *
          (f z * Real.exp (-β * ω' ((m - 1) + 1, z))) := by
            rw [hterminal z, hlen z, ← hterminal' z]
  rw [hsum]
  simpa only [hmEq, ω'] using
    (tsum_weightedPointToPoint_remove_terminalSlice_eq_profile β (m - 1) x f ω')

/-- Exact time reversal followed by cancellation of the original initial slice expresses a
forward lattice mass using the reflected point-to-plane mass and its zero-noise terminal profile. -/
theorem tsum_pointToPoint_time_reversal_eq_cancelled_profile
    (β : ℝ) {L m : ℕ} (hmL : m ≤ L) (hm : 1 ≤ m) (x : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' z : Site, f z * pointToPoint β 0 m z x ω) =
      Real.exp (β * ω (m, x) - β ^ 2 / 2) *
        (pointToPlane β 0 (m - 1) x
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω)) *
          profileP2Fun 0 (m - 1) m
            (endpointDist β (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω))) f
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω))) := by
  have hrev := tsum_weightedPointToPoint_time_reversal β hmL x f ω
  have hcancel := tsum_weightedPointToPoint_time_reversal_cancelled_profile
    β hmL hm x f ω
  calc
    _ = Real.exp (β * ω (m, x)) *
        (∑' z : Site, pointToPoint β (L - m) m x z
          (PolymerCalculus.reversedDisorder L ω) *
          (f z * Real.exp (-β * ω (0, z)))) := hrev
    _ = Real.exp (β * ω (m, x)) *
        (Real.exp (-(β ^ 2) / 2) *
          (pointToPlane β 0 (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω)) *
            profileP2Fun 0 (m - 1) m
              (endpointDist β (m - 1) x
                (Smoothing.shiftEnvironment (L - m)
                  (PolymerCalculus.reversedDisorder L ω))) f
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω)))) := by rw [hcancel]
    _ = Real.exp (β * ω (m, x) - β ^ 2 / 2) *
        (pointToPlane β 0 (m - 1) x
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω)) *
          profileP2Fun 0 (m - 1) m
            (endpointDist β (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω))) f
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω))) := by
          calc
            _ = (Real.exp (β * ω (m, x)) * Real.exp (-(β ^ 2) / 2)) *
                (pointToPlane β 0 (m - 1) x
                  (Smoothing.shiftEnvironment (L - m)
                    (PolymerCalculus.reversedDisorder L ω)) *
                  profileP2Fun 0 (m - 1) m
                    (endpointDist β (m - 1) x
                      (Smoothing.shiftEnvironment (L - m)
                        (PolymerCalculus.reversedDisorder L ω))) f
                    (Smoothing.shiftEnvironment (L - m)
                      (PolymerCalculus.reversedDisorder L ω))) := by ring
            _ = Real.exp (β * ω (m, x) + (-(β ^ 2) / 2)) *
                (pointToPlane β 0 (m - 1) x
                  (Smoothing.shiftEnvironment (L - m)
                    (PolymerCalculus.reversedDisorder L ω)) *
                  profileP2Fun 0 (m - 1) m
                    (endpointDist β (m - 1) x
                      (Smoothing.shiftEnvironment (L - m)
                        (PolymerCalculus.reversedDisorder L ω))) f
                    (Smoothing.shiftEnvironment (L - m)
                      (PolymerCalculus.reversedDisorder L ω))) := by
                rw [← Real.exp_add]
            _ = _ := by congr 1; ring_nf

/-- The logarithmic forward mass differs from the reflected spatial profile only by the fixed
initial Gaussian factor and the one-slice terminal-profile ratio. -/
theorem log_tsum_pointToPoint_time_reversal_sub_profile (β : ℝ) {L m : ℕ}
    (hmL : m ≤ L) (hm : 1 ≤ m) (x : Site) (f : Site → ℝ)
    (hf : ∀ z, 0 < f z) (ω : Disorder) :
    Real.log (∑' z : Site, f z * pointToPoint β 0 m z x ω) -
      Real.log (profileP2Fun β (L - m) L (fun z => if z = x then 1 else 0) f
        (PolymerCalculus.reversedDisorder L ω)) =
      β * ω (m, x) - β ^ 2 / 2 +
        (Real.log (profileP2Fun 0 (m - 1) m
            (endpointDist β (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω))) f
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω))) -
          Real.log (profileP2Fun β (m - 1) m
            (endpointDist β (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω))) f
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω)))) := by
  let ω' := Smoothing.shiftEnvironment (L - m)
    (PolymerCalculus.reversedDisorder L ω)
  let A := Polymer.endpoints x (m - 1)
  let η := endpointDist β (m - 1) x
  have hηA (ω₀ : Disorder) (z : Site) (hz : z ∉ A) : η ω₀ z = 0 := by
    exact Polymer.endpointDist_eq_zero_of_not_mem β (m - 1) x z ω₀ (by simpa [A] using hz)
  have hη0 (ω₀ : Disorder) (z : Site) : 0 ≤ η ω₀ z :=
    Polymer.endpointDist_nonneg β (m - 1) x z ω₀
  have hη1 (ω₀ : Disorder) : ∑ z ∈ A, η ω₀ z = 1 := by
    exact (Smoothing.endpointDist_probability β (m - 1) x ω₀).2.2
  have hηpos (ω₀ : Disorder) : ∃ z ∈ A, 0 < η ω₀ z := by
    have hsumPos : 0 < ∑ z ∈ A, η ω₀ z := by rw [hη1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun z hz => hη0 ω₀ z)).mp hsumPos
  have hbase : 0 < pointToPlane β 0 (m - 1) x ω' :=
    Polymer.pointToPlane_pos β 0 (m - 1) x ω'
  have hprofile0 : 0 < profileP2Fun 0 (m - 1) m (η ω') f ω' :=
    Smoothing.profileP2Fun_pos_terminal 0 (m - 1) m (η ω') f A (hηA ω')
      (hη0 ω') (hηpos ω') hf ω'
  have hprofileβ : 0 < profileP2Fun β (m - 1) m (η ω') f ω' :=
    Smoothing.profileP2Fun_pos_terminal β (m - 1) m (η ω') f A (hηA ω')
      (hη0 ω') (hηpos ω') hf ω'
  have hforward := tsum_pointToPoint_time_reversal_eq_cancelled_profile
    β hmL hm x f ω
  have hreverse := profileP2Fun_reversedPointFactor β hmL x f ω
  rw [hforward, hreverse]
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (mul_pos hbase hprofile0)), Real.log_exp]
  rw [Real.log_mul (ne_of_gt hbase) (ne_of_gt hprofile0),
    Real.log_mul (ne_of_gt hbase) (ne_of_gt hprofileβ)]
  ring

private theorem no_modEq_even_odd {a b : ℤ} (ha : Even a) (hb : ¬ Even b) :
    ¬ Int.ModEq 2 a b := by
  intro h
  change a % 2 = b % 2 at h
  apply hb
  apply Int.even_iff.mpr
  rw [← h]
  exact Int.even_iff.mp ha

private theorem tsum_pointToPoint_evenTerminal_congr (β : ℝ) (m : ℕ) (x : Site)
    (hx : Even (x 0 + x 1)) (hm : Even m) (f g : Site → ℝ)
    (hfg : ∀ z, Even (z 0 + z 1) → f z = g z) (ω : Disorder) :
    (∑' z : Site, f z * pointToPoint β 0 m z x ω) =
      ∑' z : Site, g z * pointToPoint β 0 m z x ω := by
  apply tsum_congr
  intro z
  by_cases hz : Even (z 0 + z 1)
  · rw [hfg z hz]
  · have hmInt : Even (m : ℤ) := by exact_mod_cast hm
    have hsumOdd : ¬ Even (z 0 + z 1 + (m : ℤ)) := by
      intro hsum
      have hpar := Int.even_add.mp hsum
      exact hz (hpar.mpr hmInt)
    have hnot := no_modEq_even_odd hx hsumOdd
    simp [Polymer.pointToPoint_eq_zero_of_parity β 0 m z x ω hnot]

private theorem profileP2Fun_congr_of_oddStart_oneStep (β : ℝ) {a b : ℕ}
    (hba : b - a = 1)
    (ν f g : Site → ℝ)
    (hν : ∀ w, ν w ≠ 0 → ¬ Even (w 0 + w 1))
    (hfg : ∀ z, Even (z 0 + z 1) → f z = g z) (ω : Disorder) :
    profileP2Fun β a b ν f ω = profileP2Fun β a b ν g ω := by
  unfold profileP2Fun
  rw [hba]
  apply tsum_congr
  intro w
  by_cases hw : ν w = 0
  · simp [hw]
  · have hwodd := hν w hw
    have hinner :
        (∑' z : Site, pointToPoint β a 1 w z ω * f z) =
          ∑' z : Site, pointToPoint β a 1 w z ω * g z := by
      apply tsum_congr
      intro z
      by_cases hz : Even (z 0 + z 1)
      · rw [hfg z hz]
      · have hwplus : Even (w 0 + w 1 + (1 : ℤ)) := Int.even_add_one.mpr hwodd
        have hnot : ¬ Int.ModEq 2 (z 0 + z 1) (w 0 + w 1 + 1) := by
          intro h
          have hs : Int.ModEq 2 (w 0 + w 1 + 1) (z 0 + z 1) := h.symm
          exact no_modEq_even_odd hwplus hz hs
        have hzero : pointToPoint β a 1 w z ω = 0 :=
          Polymer.pointToPoint_eq_zero_of_parity β a 1 w z ω hnot
        rw [hzero]
        simp
    rw [hinner]

private theorem odd_endpoint_of_oddDuration {n : ℕ} (x y : Site)
    (hx : Even (x 0 + x 1)) (hn : ¬ Even n)
    (hy : y ∈ Polymer.endpoints x n) : ¬ Even (y 0 + y 1) := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff x y n).mp hy
  have hwalk := walkPosition_parity x s
  rw [hs] at hwalk
  intro hyEven
  have hnInt : ¬ Even (n : ℤ) := by
    simpa only [Int.even_coe_nat] using hn
  have hsum : Even (x 0 + x 1 + (n : ℤ)) := hwalk.mpr hyEven
  have hpar := Int.even_add.mp hsum
  have hnContr : Even (n : ℤ) := hpar.mp hx
  exact hnInt hnContr

/-- A terminal profile at the endpoint law of an odd-length walk from an even site only
depends on its weight on the even lattice. -/
theorem profileP2Fun_endpointDist_congr_of_oddDuration (β : ℝ) {n : ℕ}
    (hn : ¬ Even n) (x : Site) (hx : Even (x 0 + x 1)) (f g : Site → ℝ)
    (hfg : ∀ z, Even (z 0 + z 1) → f z = g z) (ω : Disorder) :
    profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω =
      profileP2Fun β n (n + 1) (endpointDist β n x ω) g ω := by
  apply profileP2Fun_congr_of_oddStart_oneStep β (by omega)
    (endpointDist β n x ω) f g
  · intro y hy
    have hyA : y ∈ Polymer.endpoints x n := by
      by_contra hnot
      exact hy (Polymer.endpointDist_eq_zero_of_not_mem β n x y ω hnot)
    exact odd_endpoint_of_oddDuration x y hx hn hyA
  · exact hfg

/-- The one-slice terminal-profile log ratio has the same uniform `L¹` bound when the terminal
weight is positive only on the parity class reachable from the last-step endpoint law. -/
theorem integral_abs_log_endpointDist_terminal_ratio_le_of_oddDuration
    (β : ℝ) (n : ℕ) (x : Site) (hx : Even (x 0 + x 1)) (hn : ¬ Even n)
    (f : Site → ℝ) (hf : ∀ z, Even (z 0 + z 1) → 0 < f z) :
    Integrable (fun ω => |Real.log
      (profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω)|)
      disorderLaw ∧
    (∫ ω, |Real.log
      (profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω)|
      ∂disorderLaw) ≤ Real.sqrt (β ^ 2 + β ^ 4 / 4) := by
  let F : Site → ℝ := Smoothing.evenExtension f
  have hFpos (z : Site) : 0 < F z := by
    by_cases hz : Even (z 0 + z 1)
    · simpa [F, Smoothing.evenExtension, hz] using hf z hz
    · simp [F, Smoothing.evenExtension, hz]
  have hFeven (z : Site) (hz : Even (z 0 + z 1)) : f z = F z := by
    simp [F, Smoothing.evenExtension, hz]
  have hratio := integral_abs_log_endpointDist_terminal_ratio_le β n x F hFpos
  have hηodd (ω : Disorder) (z : Site) (hz : endpointDist β n x ω z ≠ 0) :
      ¬ Even (z 0 + z 1) := by
    have hzA : z ∈ Polymer.endpoints x n := by
      by_contra hnot
      exact hz (Polymer.endpointDist_eq_zero_of_not_mem β n x z ω hnot)
    exact odd_endpoint_of_oddDuration x z hx hn hzA
  have hfun :
      (fun ω => |Real.log (profileP2Fun β n (n + 1)
            (endpointDist β n x ω) f ω) -
          Real.log (profileP2Fun 0 n (n + 1)
            (endpointDist β n x ω) f ω)|) =
        fun ω => |Real.log (profileP2Fun β n (n + 1)
            (endpointDist β n x ω) F ω) -
          Real.log (profileP2Fun 0 n (n + 1)
            (endpointDist β n x ω) F ω)| := by
    funext ω
    have hbeta := profileP2Fun_endpointDist_congr_of_oddDuration
      β hn x hx f F hFeven ω
    have hzero := profileP2Fun_congr_of_oddStart_oneStep 0
      (a := n) (b := n + 1) (by omega)
      (endpointDist β n x ω) f F (hηodd ω) hFeven ω
    rw [hbeta, hzero]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hratio.1
  · rw [hfun]
    exact hratio.2

/-- At an even positive clock, the forward mass and reflected profile differ by the explicit endpoint-slice terms. -/
theorem log_tsum_pointToPoint_time_reversal_sub_profile_of_even
    (β : ℝ) {L m : ℕ} (hmL : m ≤ L) (hm : 1 ≤ m) (hmEven : Even m)
    (x : Site) (hx : Even (x 0 + x 1)) (f : Site → ℝ)
    (hf : ∀ z, Even (z 0 + z 1) → 0 < f z) (ω : Disorder) :
    Real.log (∑' z : Site, f z * pointToPoint β 0 m z x ω) -
      Real.log (profileP2Fun β (L - m) L (fun z => if z = x then 1 else 0) f
        (PolymerCalculus.reversedDisorder L ω)) =
      β * ω (m, x) - β ^ 2 / 2 +
        (Real.log (profileP2Fun 0 (m - 1) m
            (endpointDist β (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω))) f
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω))) -
          Real.log (profileP2Fun β (m - 1) m
            (endpointDist β (m - 1) x
              (Smoothing.shiftEnvironment (L - m)
                (PolymerCalculus.reversedDisorder L ω))) f
            (Smoothing.shiftEnvironment (L - m)
              (PolymerCalculus.reversedDisorder L ω)))) := by
  let F : Site → ℝ := Smoothing.evenExtension f
  have hFpos (z : Site) : 0 < F z := by
    by_cases hz : Even (z 0 + z 1)
    · simpa [F, Smoothing.evenExtension, hz] using hf z hz
    · simp [F, Smoothing.evenExtension, hz]
  have hFeven (z : Site) (hz : Even (z 0 + z 1)) : f z = F z := by
    simp [F, Smoothing.evenExtension, hz]
  have hsum := tsum_pointToPoint_evenTerminal_congr β m x hx hmEven f F hFeven ω
  let ν : Site → ℝ := fun z => if z = x then 1 else 0
  have hνeven (z : Site) (hz : ν z ≠ 0) : Even (z 0 + z 1) := by
    have hzx : z = x := by
      by_contra hne
      simp [ν, hne] at hz
    rw [hzx]
    exact hx
  have hmDiff : L - (L - m) = m := by omega
  have hreverse := Smoothing.profileP2Fun_congr_of_even β (Nat.sub_le L m)
    (by rw [hmDiff]; exact hmEven) ν f F hνeven hFeven
    (PolymerCalculus.reversedDisorder L ω)
  let η : Disorder → Site → ℝ := endpointDist β (m - 1) x
  let A : Finset Site := Polymer.endpoints x (m - 1)
  have hνodd (ω₀ : Disorder) (z : Site) (hz : η ω₀ z ≠ 0) :
      ¬ Even (z 0 + z 1) := by
    have hzA : z ∈ A := by
      by_contra hzA
      exact hz (Polymer.endpointDist_eq_zero_of_not_mem β (m - 1) x z ω₀ (by simpa [A] using hzA))
    apply odd_endpoint_of_oddDuration x z hx ?_ hzA
    intro hnEven
    have hmInt : Even (m : ℤ) := by exact_mod_cast hmEven
    have hnInt : Even ((m - 1 : ℕ) : ℤ) := by exact_mod_cast hnEven
    have hmEq : (m : ℤ) = ((m - 1 : ℕ) : ℤ) + 1 := by omega
    rw [hmEq, Int.even_add_one] at hmInt
    exact hmInt hnInt
  have hterm (b : ℝ) :
      profileP2Fun b (m - 1) m (η (Smoothing.shiftEnvironment (L - m)
        (PolymerCalculus.reversedDisorder L ω))) f
        (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)) =
      profileP2Fun b (m - 1) m (η (Smoothing.shiftEnvironment (L - m)
        (PolymerCalculus.reversedDisorder L ω))) F
        (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)) := by
    apply profileP2Fun_congr_of_oddStart_oneStep b (by omega)
      (η (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)))
      f F
    · exact hνodd _
    · exact hFeven
  have hmain := log_tsum_pointToPoint_time_reversal_sub_profile β hmL hm x F hFpos ω
  have hreverse' := hreverse
  change profileP2Fun β (L - m) L
      (fun z => if z = x then 1 else 0) f (PolymerCalculus.reversedDisorder L ω) =
    profileP2Fun β (L - m) L
      (fun z => if z = x then 1 else 0) F (PolymerCalculus.reversedDisorder L ω) at hreverse'
  calc
    _ = Real.log (∑' z : Site, F z * pointToPoint β 0 m z x ω) -
        Real.log (profileP2Fun β (L - m) L ν F (PolymerCalculus.reversedDisorder L ω)) := by
          rw [hsum, hreverse']
    _ = _ := hmain
    _ = _ := by rw [← hterm 0, ← hterm β]

end Critical2DKPZ.LocalSobolev

end
