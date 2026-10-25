/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminalFirstBlock
public import Critical2DKPZ.SHF.Moments.WordPotentialDomination
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGeneralBlock
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSeparatedScale
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitPotentialTube
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.WordLimitDominationMass
public import Critical2DKPZ.SHF.Moments.WordLimitPotentialSmoothing
public import Critical2DKPZ.SHF.Moments.WordLimitDominationTimes
public import Critical2DKPZ.Renewal.PolymerBridge
public import Critical2DKPZ.Renewal.CumulativeUniformLimit
public import Critical2DKPZ.SHF.Moments.CriticalWindowClockTail
public import Critical2DKPZ.SHF.Moments.CollisionEntrance
public import Critical2DKPZ.SHF.Moments.GapOverlap
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Critical2DKPZ.Renewal.ReturnSeries
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.Renewal.ExponentialTilt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Critical2DKPZ.SHF.Moments.ClockTail
import Mathlib.Tactic

/-! # Time-boundary control for a moving first collision -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

private theorem exists_critical_run_mass_short_bound (ϑ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
        ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ η * N →
          (∑ r ∈ Finset.range (K + 1),
            sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
              (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := Renewal.criticalRenewalFunction_log_bound ϑ
  refine ⟨C, hC, fun ε hε => ?_⟩
  let L : ℝ := C / ε + 1
  let η₀ : ℝ := min (1 / 2) (1 / (2 * Real.exp L))
  have hL : 0 < L := by dsimp [L]; positivity
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hη₀η
  have hηhalf : η < 1 / 2 := hη₀η.trans_le (min_le_left _ _)
  have hηexp : η < 1 / (2 * Real.exp L) := hη₀η.trans_le (min_le_right _ _)
  have hNlarge : ∀ᶠ N : ℕ in atTop, 1 / η ≤ N :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 / η))
  filter_upwards [hbound, hNlarge, criticalBeta_spec ϑ,
    eventually_ge_atTop 2, Renewal.criticalSigmaSq_eventually_pos ϑ]
      with N hboundN hNlargeN hspec hN hσ
  intro K hK
  have hNpos : (0 : ℝ) < N := by positivity
  have hone' : (1 : ℝ) ≤ N * η :=
    (div_le_iff₀ hη).mp (by exact_mod_cast hNlargeN)
  have hone : (1 : ℝ) ≤ η * N := by nlinarith only [hone']
  have hKplus : ((K + 1 : ℕ) : ℝ) ≤ 2 * η * N := by
    push_cast
    nlinarith only [hK, hone]
  have hKNr : ((K + 1 : ℕ) : ℝ) < N := by
    have h2η : 2 * η < 1 := by linarith only [hηhalf]
    nlinarith only [hKplus, h2η, hNpos]
  have hKN : K + 1 ≤ N := by exact_mod_cast hKNr.le
  have hratio : 1 / (2 * η) ≤ (N : ℝ) / ((K + 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hNpos, hKplus]
  have hexp : Real.exp L < 1 / (2 * η) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * η)).2
    have hmul : η * (2 * Real.exp L) < 1 :=
      (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.exp L)).mp hηexp
    nlinarith only [hmul]
  have hlog : L < Real.log (1 + (N : ℝ) / ((K + 1 : ℕ) : ℝ)) := by
    rw [← Real.log_exp L]
    apply Real.log_lt_log (Real.exp_pos L)
    linarith only [hratio, hexp]
  have hboundK : criticalSigmaSq ϑ N *
      Renewal.renewalFunction (fun k => criticalSigmaSq ϑ N * Renewal.returnWeight k)
        (K + 1) ≤ C / Real.log (1 + (N : ℝ) / ((K + 1 : ℕ) : ℝ)) :=
    hboundN (K + 1) (by omega) hKN
  have hspec' : sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N := by
    change Real.exp (criticalBeta ϑ N ^ 2) - 1 = criticalSigmaSq ϑ N
    exact hspec
  have hsum :
      (∑ r ∈ Finset.range (K + 1),
        sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
          (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) =
        sigmaSq (criticalBeta ϑ N) * Renewal.renewalFunction
          (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) K := by
    rw [← Finset.mul_sum, Renewal.sum_renewalMass_range]
  rw [hsum, hspec']
  have hmono : criticalSigmaSq ϑ N *
      Renewal.renewalFunction (fun k => criticalSigmaSq ϑ N * Renewal.returnWeight k) K ≤
      criticalSigmaSq ϑ N *
        Renewal.renewalFunction (fun k => criticalSigmaSq ϑ N * Renewal.returnWeight k)
          (K + 1) := by
    apply mul_le_mul_of_nonneg_left _ hσ.le
    exact Renewal.renewalFunction_mono_time
      (fun j => mul_nonneg hσ.le (srwKernel_nonneg _ _)) (Nat.le_succ K)
  have hsmall : C / Real.log (1 + (N : ℝ) / ((K + 1 : ℕ) : ℝ)) < ε := by
    have hratioPos : 0 < (N : ℝ) / ((K + 1 : ℕ) : ℝ) := by positivity
    have hden : 0 < Real.log (1 + (N : ℝ) / ((K + 1 : ℕ) : ℝ)) :=
      Real.log_pos (by linarith only [hratioPos])
    apply (div_lt_iff₀ hden).2
    have hprod := mul_lt_mul_of_pos_left hlog hε
    have hprod' : C + ε <
        ε * Real.log (1 + (N : ℝ) / ((K + 1 : ℕ) : ℝ)) := by
      dsimp [L] at hprod
      calc
        C + ε = ε * (C / ε + 1) := by field_simp [ne_of_gt hε]
        _ < _ := hprod
    exact (lt_add_of_pos_right C hε).trans hprod'
  exact le_of_lt (hmono.trans_lt (hboundK.trans_lt hsmall))

private theorem sum_wordTimeTriangle_swap (n : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r) =
      ∑ r ∈ Finset.range (n + 1), ∑ s ∈ Finset.Icc 1 n,
        if r ∈ Finset.range (n - s + 1) then F s r else 0 := by
  classical
  have hexpand (s : ℕ) :
      (∑ r ∈ Finset.range (n - s + 1), F s r) =
        ∑ r ∈ Finset.range (n + 1),
          if r ∈ Finset.range (n - s + 1) then F s r else 0 := by
    have hsubset : Finset.range (n - s + 1) ⊆ Finset.range (n + 1) :=
      Finset.range_mono (by omega)
    calc
      _ = ∑ r ∈ Finset.range (n - s + 1),
          if r ∈ Finset.range (n - s + 1) then F s r else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [hr]
      _ = _ := Finset.sum_subset hsubset (by intro r hr hnot; simp [hnot])
  calc
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n + 1),
        if r ∈ Finset.range (n - s + 1) then F s r else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hexpand s
    _ = _ := Finset.sum_comm

private theorem sum_wordBoundaryPotential_run_cutoff_le
    (n K : ℕ) (z : Site) (q : ℕ → ℝ) (hq : ∀ r, 0 ≤ q r) :
    (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
      if r ≤ K then srwKernel (2 * s) z * q r /
        Real.sqrt ((s : ℝ) + r + 1) else 0) ≤
      (∑ r ∈ Finset.range (K + 1), q r) * wordGapPotential n z := by
  have hqsum (s : ℕ) :
      (∑ r ∈ Finset.range (n - s + 1), if r ≤ K then q r else 0) ≤
        ∑ r ∈ Finset.range (K + 1), q r := by
    classical
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (s := Finset.range (n - s + 1) |>.filter (fun r => r ≤ K))
      (t := Finset.range (K + 1))
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      simp only [Finset.mem_range]
      omega
    · intro r hr hnot
      exact hq r
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n,
        (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) *
          (∑ r ∈ Finset.range (K + 1), q r) := by
      apply Finset.sum_le_sum
      intro s hs
      calc
        _ ≤ ∑ r ∈ Finset.range (n - s + 1),
            (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) *
              (if r ≤ K then q r else 0) := by
          apply Finset.sum_le_sum
          intro r hr
          by_cases hrK : r ≤ K
          · have hden : Real.sqrt ((s : ℝ) + 1) ≤
                Real.sqrt ((s : ℝ) + r + 1) := by
              apply Real.sqrt_le_sqrt
              have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
              linarith only [hr0]
            have hkernel := srwKernel_nonneg (2 * s) z
            have hq' := hq r
            have hdiv := div_le_div_of_nonneg_left
              (mul_nonneg hkernel hq') (Real.sqrt_pos.mpr (by positivity)) hden
            simpa only [hrK, ↓reduceIte, mul_div_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hdiv
          · simp [hrK]
        _ = (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) *
              ∑ r ∈ Finset.range (n - s + 1), if r ≤ K then q r else 0 := by
          rw [Finset.mul_sum]
        _ ≤ (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) *
              ∑ r ∈ Finset.range (K + 1), q r :=
          mul_le_mul_of_nonneg_left (hqsum s)
            (div_nonneg (srwKernel_nonneg _ _) (Real.sqrt_nonneg _))
    _ = (∑ r ∈ Finset.range (K + 1), q r) * wordGapPotential n z := by
      rw [← Finset.sum_mul, wordGapPotential]
      ring


private theorem sum_wordBoundaryPotential_entrance_cutoff_le
    (n K : ℕ) (z : Site) (q : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hq : ∀ r, 0 ≤ q r)
    (hRun : ∀ s ∈ Finset.Icc 1 n,
      (∑ r ∈ Finset.range (n - s + 1), q r) ≤ B) :
    (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
      if s ≤ K then srwKernel (2 * s) z * q r /
        Real.sqrt ((s : ℝ) + r + 1) else 0) ≤
      B * wordGapPotential K z := by
  have hslice (s : ℕ) (hs : s ∈ Finset.Icc 1 n) :
      (∑ r ∈ Finset.range (n - s + 1),
        if s ≤ K then srwKernel (2 * s) z * q r /
          Real.sqrt ((s : ℝ) + r + 1) else 0) ≤
        if s ≤ K then B * (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) else 0 := by
    by_cases hsK : s ≤ K
    · simp only [hsK, ↓reduceIte]
      calc
        _ ≤ ∑ r ∈ Finset.range (n - s + 1),
            (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) * q r := by
          apply Finset.sum_le_sum
          intro r hr
          have hden : Real.sqrt ((s : ℝ) + 1) ≤
              Real.sqrt ((s : ℝ) + r + 1) := by
            apply Real.sqrt_le_sqrt
            have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
            linarith only [hr0]
          have hdiv := div_le_div_of_nonneg_left
            (mul_nonneg (srwKernel_nonneg (2 * s) z) (hq r))
            (Real.sqrt_pos.mpr (by positivity)) hden
          calc
            _ = srwKernel (2 * s) z * q r /
                Real.sqrt ((s : ℝ) + r + 1) := by ring
            _ ≤ _ := hdiv
            _ = _ := by ring
        _ = (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) *
              ∑ r ∈ Finset.range (n - s + 1), q r := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hRun s hs)
          (div_nonneg (srwKernel_nonneg _ _) (Real.sqrt_nonneg _))
        _ = _ := by ring
    · simp [hsK]
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n,
        if s ≤ K then B * (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) else 0 :=
      Finset.sum_le_sum (fun s hs => hslice s hs)
    _ = ∑ s ∈ (Finset.Icc 1 n).filter (fun s => s ≤ K),
        B * (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) := by
      rw [Finset.sum_filter]
    _ ≤ ∑ s ∈ Finset.Icc 1 K,
        B * (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_Icc] at hs
        simp only [Finset.mem_Icc]
        exact ⟨hs.1.1, hs.2⟩
      · intro s hs hnot
        exact mul_nonneg hB
          (div_nonneg (srwKernel_nonneg _ _) (Real.sqrt_nonneg _))
    _ = B * wordGapPotential K z := by
      rw [wordGapPotential, Finset.mul_sum]

private theorem abs_wordFirstBlock_nil_le
    {h : ℕ} (N : ℕ) (ρ : ℝ) (α : CollisionPair h) (s r L : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) (M : ℝ)
    (hΨ : ∀ y, |Ψ y| ≤ M) :
    |∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
      wordFirstBlockKernel ρ α s r x v *
        wordTerminalTest N (sigmaSq ρ) [] L v Ψ| ≤
      M * (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
        (sigmaSq ρ * Renewal.renewalMass
          (fun k => sigmaSq ρ * Renewal.returnWeight k) r)) := by
  calc
    _ ≤ ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        |wordFirstBlockKernel ρ α s r x v *
          wordTerminalTest N (sigmaSq ρ) [] L v Ψ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        M * wordFirstBlockKernel ρ α s r x v := by
      apply Finset.sum_le_sum
      intro v hv
      rw [abs_mul, abs_of_nonneg (wordFirstBlockKernel_nonneg ρ α s r x v)]
      have htail := abs_wordTerminalTest_le_mass N (sigmaSq_nonneg ρ) [] L v Ψ hΨ
      have htail' : |wordTerminalTest N (sigmaSq ρ) [] L v Ψ| ≤ M := by
        simpa [wordTerminalTest_nil_one] using htail
      calc
        _ ≤ wordFirstBlockKernel ρ α s r x v * M :=
          mul_le_mul_of_nonneg_left htail' (wordFirstBlockKernel_nonneg ρ α s r x v)
        _ = _ := by rw [mul_comm]
    _ = M * (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        wordFirstBlockKernel ρ α s r x v) := by rw [Finset.mul_sum]
    _ = _ := by rw [sum_wordFirstBlockKernel]

private theorem abs_wordFirstBlock_cons_le_of_tail_potential_bound
    {h : ℕ} (N : ℕ) (ρ : ℝ) (α β : CollisionPair h) (w : List (CollisionPair h))
    (s r L n : ℕ) (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (M D A : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hL : L ≤ n)
    (hTail : ∀ v : LatticeConfiguration h,
      wordTerminalTest N (sigmaSq ρ) (β :: w) L v (fun _ => 1) ≤
        D * Real.sqrt (N : ℝ) * wordGapPotential L (v β.1.2 - v β.1.1))
    (hΨ : ∀ y, |Ψ y| ≤ M)
    (hBlock :
      (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        wordFirstBlockKernel ρ α s r x v *
          wordGapPotential n (v β.1.2 - v β.1.1)) ≤
        (A / Real.sqrt ((s : ℝ) + r + 1)) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass
              (fun k => sigmaSq ρ * Renewal.returnWeight k) r))) :
    |∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
      wordFirstBlockKernel ρ α s r x v *
        wordTerminalTest N (sigmaSq ρ) (β :: w) L v Ψ| ≤
      (M * D * Real.sqrt (N : ℝ)) *
        ((A / Real.sqrt ((s : ℝ) + r + 1)) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass
              (fun k => sigmaSq ρ * Renewal.returnWeight k) r))) := by
  have hcoef : 0 ≤ M * D * Real.sqrt (N : ℝ) :=
    mul_nonneg (mul_nonneg hM hD) (Real.sqrt_nonneg _)
  calc
    _ ≤ ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        |wordFirstBlockKernel ρ α s r x v *
          wordTerminalTest N (sigmaSq ρ) (β :: w) L v Ψ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        (M * D * Real.sqrt (N : ℝ)) *
          (wordFirstBlockKernel ρ α s r x v *
            wordGapPotential n (v β.1.2 - v β.1.1)) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [abs_mul, abs_of_nonneg (wordFirstBlockKernel_nonneg ρ α s r x v)]
      have htailMass := abs_wordTerminalTest_le_mass N (sigmaSq_nonneg ρ)
        (β :: w) L v Ψ hΨ
      have htailBound :
          |wordTerminalTest N (sigmaSq ρ) (β :: w) L v Ψ| ≤
            (M * D * Real.sqrt (N : ℝ)) *
              wordGapPotential n (v β.1.2 - v β.1.1) := by
        calc
          _ ≤ M * wordTerminalTest N (sigmaSq ρ) (β :: w) L v (fun _ => 1) :=
            htailMass
          _ ≤ M * (D * Real.sqrt (N : ℝ) *
              wordGapPotential L (v β.1.2 - v β.1.1)) :=
            mul_le_mul_of_nonneg_left (hTail v) hM
          _ ≤ M * (D * Real.sqrt (N : ℝ) *
              wordGapPotential n (v β.1.2 - v β.1.1)) := by
            apply mul_le_mul_of_nonneg_left _ hM
            exact mul_le_mul_of_nonneg_left
              (wordGapPotential_mono_time (v β.1.2 - v β.1.1) hL)
              (mul_nonneg hD (Real.sqrt_nonneg _))
          _ = _ := by ring
      calc
        _ ≤ wordFirstBlockKernel ρ α s r x v *
            ((M * D * Real.sqrt (N : ℝ)) *
              wordGapPotential n (v β.1.2 - v β.1.1)) :=
          mul_le_mul_of_nonneg_left htailBound
            (wordFirstBlockKernel_nonneg ρ α s r x v)
        _ = (M * D * Real.sqrt (N : ℝ)) *
            (wordFirstBlockKernel ρ α s r x v *
              wordGapPotential n (v β.1.2 - v β.1.1)) := by ring
    _ = (M * D * Real.sqrt (N : ℝ)) *
        ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          wordFirstBlockKernel ρ α s r x v *
            wordGapPotential n (v β.1.2 - v β.1.1) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hBlock hcoef






private theorem sum_word_terminal_strip_le
    (n K : ℕ) (a q : ℕ → ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (hq : ∀ r, 0 ≤ q r) (ha : ∀ s ∈ Finset.Icc 1 n, a s ≤ A)
    (hB : (∑ r ∈ Finset.range (n + 1), q r) ≤ B) :
    (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
      if n - s - r ≤ K then a s * q r else 0) ≤ A * (K + 1) * B := by
  classical
  rw [sum_wordTimeTriangle_swap]
  have hslice (r : ℕ) :
      (∑ s ∈ Finset.Icc 1 n,
        if r ∈ Finset.range (n - s + 1) then
          (if n - s - r ≤ K then a s * q r else 0) else 0) ≤
        A * (K + 1) * q r := by
    let D := (Finset.Icc 1 n).filter
      (fun s => r ∈ Finset.range (n - s + 1) ∧ n - s - r ≤ K)
    have hsub : D ⊆ Finset.Icc (n - r - K) (n - r) := by
      intro s hs
      simp only [D, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hs
      simp only [Finset.mem_Icc]
      omega
    have hcard : D.card ≤ K + 1 := by
      have hh := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hh
      omega
    calc
      _ = ∑ s ∈ D, a s * q r := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro s hs
        split_ifs <;> simp_all
      _ ≤ ∑ _s ∈ D, A * q r := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_right (ha s (Finset.mem_filter.mp hs).1) (hq r))
      _ = (D.card : ℝ) * (A * q r) := by simp
      _ ≤ ((K + 1 : ℕ) : ℝ) * (A * q r) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (mul_nonneg hA (hq r))
      _ = _ := by push_cast; ring
  calc
    _ ≤ ∑ r ∈ Finset.range (n + 1), A * (K + 1) * q r :=
      Finset.sum_le_sum (fun r _ => hslice r)
    _ = A * (K + 1) * ∑ r ∈ Finset.range (n + 1), q r := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)


private theorem sum_word_terminal_strip_weighted_le
    (N n K : ℕ) (a q : ℕ → ℝ) (A B c : ℝ)
    (hN : 0 < N) (hc : 0 < c) (hclock : c * N ≤ (n : ℝ) - K)
    (hA : 0 ≤ A) (hq : ∀ r, 0 ≤ q r) (ha0 : ∀ s, 0 ≤ a s)
    (ha : ∀ s ∈ Finset.Icc 1 n, a s ≤ A)
    (hB : (∑ r ∈ Finset.range (n + 1), q r) ≤ B) :
    (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
      if n - s - r ≤ K then
        Real.sqrt (N : ℝ) * (a s * q r / Real.sqrt ((s : ℝ) + r + 1)) else 0) ≤
      (1 / Real.sqrt c) * (A * (K + 1) * B) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound (s r : ℕ) (hs : s ∈ Finset.Icc 1 n)
      (hr : r ∈ Finset.range (n - s + 1)) (hK : n - s - r ≤ K) :
      Real.sqrt (N : ℝ) / Real.sqrt ((s : ℝ) + r + 1) ≤ 1 / Real.sqrt c := by
    have hfit : s + r ≤ n := by
      have := (Finset.mem_Icc.mp hs).2
      have := Finset.mem_range.mp hr
      omega
    have hsub : ((n - s - r : ℕ) : ℝ) = (n : ℝ) - s - r := by
      rw [Nat.cast_sub (by omega : r ≤ n - s), Nat.cast_sub (by omega : s ≤ n)]
    have hKr : ((n - s - r : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    rw [hsub] at hKr
    have htime : c * N ≤ (s : ℝ) + r + 1 := by
      linarith
    have hsqrt : Real.sqrt c * Real.sqrt (N : ℝ) ≤
        Real.sqrt ((s : ℝ) + r + 1) := by
      rw [← Real.sqrt_mul hc.le]
      exact Real.sqrt_le_sqrt htime
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_pos.mpr hc)).2
    simpa only [one_mul, mul_comm] using hsqrt
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        (1 / Real.sqrt c) * (if n - s - r ≤ K then a s * q r else 0) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro r hr
      split_ifs with hK
      · calc
          _ = (Real.sqrt (N : ℝ) / Real.sqrt ((s : ℝ) + r + 1)) *
              (a s * q r) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hbound s r hs hr hK)
            (mul_nonneg (ha0 s) (hq r))
      · simp
    _ = (1 / Real.sqrt c) *
        (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          if n - s - r ≤ K then a s * q r else 0) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_word_terminal_strip_le n K a q A B hA hq ha hB) (by positivity)

private theorem exists_scaled_srwKernel_separated_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (δ : ℝ), 0 < δ → ∀ z : Site,
      δ ≤ ‖latticeRepresentative N z‖ → ∀ s : ℕ,
        srwKernel (2 * s) z ≤ C / (δ ^ 2 * N) := by
  obtain ⟨C, hC, hkernel⟩ := srwKernel_inverse_square_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN δ hδ z hz s
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hraw : ‖siteToPlane z‖ ^ 2 =
      ((N : ℝ) / 2) * ‖latticeRepresentative N z‖ ^ 2 := by
    rw [norm_latticeRepresentative_sq]
    field_simp
  have hrawpos : 0 < ‖siteToPlane z‖ ^ 2 := by
    rw [hraw]
    exact mul_pos (by positivity) (pow_pos (hδ.trans_le hz) _)
  calc
    _ ≤ C / ‖siteToPlane z‖ ^ 2 := hkernel (2 * s) z hrawpos
    _ = (2 * C) / (‖latticeRepresentative N z‖ ^ 2 * N) := by
      rw [hraw]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ.le hz 2) hNr.le)


private theorem indicator_cover_three_le (A B C D : Prop)
    [Decidable A] [Decidable B] [Decidable C] [Decidable D] (u : ℝ) (hu : 0 ≤ u)
    (hcover : D → A ∨ B ∨ C) :
    (if D then u else 0) ≤
      (if A then u else 0) + (if B then u else 0) + (if C then u else 0) := by
  have ha : 0 ≤ if A then u else 0 := by split_ifs <;> positivity
  have hb : 0 ≤ if B then u else 0 := by split_ifs <;> positivity
  have hc : 0 ≤ if C then u else 0 := by split_ifs <;> positivity
  by_cases hd : D
  · rw [ite_eq_left hd]
    rcases hcover hd with h | h | h
    · rw [ite_eq_left h]
      linarith only [hb, hc]
    · rw [ite_eq_left h]
      linarith only [ha, hc]
    · rw [ite_eq_left h]
      linarith only [ha, hb]
  · rw [ite_eq_right hd]
    exact add_nonneg (add_nonneg ha hb) hc

private theorem weighted_time_boundary_small
    (ϑ T c δ : ℝ) (hT : 0 < T) (hc : 0 < c) (hδ : 0 < δ)
    (nN : ℕ → ℕ) (zN : ℕ → Site)
    (hclock : ∀ᶠ N : ℕ in atTop,
      2 * c * N ≤ (nN N : ℝ) ∧ (nN N : ℝ) ≤ T * N)
    (hsep : ∀ᶠ N : ℕ in atTop, δ ≤ ‖latticeRepresentative N (zN N)‖) :
    ∀ ε > 0, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∀ᶠ N : ℕ in atTop,
        (∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
          if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
              ((nN N - s - r : ℕ) : ℝ) < η * N then
            Real.sqrt (N : ℝ) *
              (srwKernel (2 * s) (zN N) *
                (sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
                  (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) /
                Real.sqrt ((s : ℝ) + r + 1))
          else 0) ≤ ε := by
  obtain ⟨B, hB, hmass⟩ := eventually_critical_run_mass_le ϑ T hT
  obtain ⟨C, hC, hpotential⟩ := exists_scaled_wordGapPotential_separated_bound
  obtain ⟨G, hG, hkernel⟩ := exists_scaled_srwKernel_separated_bound
  let P₀ := 4 * C * Real.sqrt 2 / δ ^ 4
  let E := B * P₀
  let P := 4 * C * T * Real.sqrt (T + 1) / δ ^ 4
  let D := G * B / (Real.sqrt c * δ ^ 2)
  have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
  have hE : 0 < E := mul_pos hB hP₀
  have hP : 0 < P := by dsimp [P]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  intro ε hε
  let e := ε / (4 * (E + P + D + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have heq : 4 * (E + P + D + 1) * e = ε := by
    dsimp [e]
    field_simp
  obtain ⟨_, _, hshort⟩ := exists_critical_run_mass_short_bound ϑ
  obtain ⟨ηrun, hηrun, hshort⟩ := hshort e he
  let η₀ := min 1 (min c (min ηrun e))
  refine ⟨η₀, by dsimp [η₀]; positivity, ?_⟩
  intro η hη hη₀
  have hηone : η < 1 := hη₀.trans_le (min_le_left _ _)
  have hηc : η < c := hη₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηrun' : η < ηrun := hη₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηe : η < e := hη₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 / e ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hmass, hclock, hsep, hshort η hη hηrun', hlarge,
    eventually_ge_atTop 1] with N hm hn hz hqsmall hlargeN hN
  let n := nN N
  let z := zN N
  let K := ⌊η * (N : ℝ)⌋₊
  let q : ℕ → ℝ := fun r => sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
    (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r
  let H : ℕ → ℕ → ℝ := fun s r => Real.sqrt (N : ℝ) *
    (srwKernel (2 * s) z * q r / Real.sqrt ((s : ℝ) + r + 1))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hK : (K : ℝ) ≤ η * N := Nat.floor_le (by positivity)
  have hq (r : ℕ) : 0 ≤ q r := mul_nonneg (sigmaSq_nonneg _)
    (Renewal.renewalMass_nonneg (fun k => mul_nonneg (sigmaSq_nonneg _)
      (srwKernel_nonneg _ _)) r)
  have hH (s r : ℕ) : 0 ≤ H s r :=
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg
      (mul_nonneg (srwKernel_nonneg _ _) (hq r)) (Real.sqrt_nonneg _))
  have hqtotal : (∑ r ∈ Finset.range (n + 1), q r) ≤ B := by
    dsimp [q]
    rw [← Finset.mul_sum, Renewal.sum_renewalMass_range]
    exact hm n hn.2
  have hqrun (s : ℕ) (_hs : s ∈ Finset.Icc 1 n) :
      (∑ r ∈ Finset.range (n - s + 1), q r) ≤ B := by
    dsimp [q]
    rw [← Finset.mul_sum, Renewal.sum_renewalMass_range]
    exact hm (n - s) ((Nat.cast_le.mpr (Nat.sub_le _ _)).trans hn.2)
  have hqK : (∑ r ∈ Finset.range (K + 1), q r) ≤ e := hqsmall K hK
  have hpotK : Real.sqrt (N : ℝ) * wordGapPotential K z ≤ P₀ * η := by
    calc
      _ ≤ 4 * C * η * Real.sqrt (η + 1) / δ ^ 4 :=
        hpotential η δ hη hδ N K hN hK z hz
      _ ≤ 4 * C * η * Real.sqrt 2 / δ ^ 4 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity))
          (by positivity)
      _ = _ := by dsimp [P₀]; ring
  have hpotn : Real.sqrt (N : ℝ) * wordGapPotential n z ≤ P :=
    hpotential T δ hT hδ N n hN hn.2 z hz
  have hentrance :
      (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        if s ≤ K then H s r else 0) ≤ E * e := by
    calc
      _ = Real.sqrt (N : ℝ) *
          (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            if s ≤ K then srwKernel (2 * s) z * q r /
              Real.sqrt ((s : ℝ) + r + 1) else 0) := by
        simp only [H, Finset.mul_sum, mul_ite, mul_zero]
      _ ≤ Real.sqrt (N : ℝ) * (B * wordGapPotential K z) :=
        mul_le_mul_of_nonneg_left
          (sum_wordBoundaryPotential_entrance_cutoff_le n K z q B hB.le hq hqrun)
          (Real.sqrt_nonneg _)
      _ = B * (Real.sqrt (N : ℝ) * wordGapPotential K z) := by ring
      _ ≤ B * (P₀ * η) := mul_le_mul_of_nonneg_left hpotK hB.le
      _ = E * η := by dsimp [E]; ring
      _ ≤ E * e := mul_le_mul_of_nonneg_left hηe.le hE.le
  have hrun :
      (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        if r ≤ K then H s r else 0) ≤ e * P := by
    calc
      _ = Real.sqrt (N : ℝ) *
          (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            if r ≤ K then srwKernel (2 * s) z * q r /
              Real.sqrt ((s : ℝ) + r + 1) else 0) := by
        simp only [H, Finset.mul_sum, mul_ite, mul_zero]
      _ ≤ Real.sqrt (N : ℝ) *
          ((∑ r ∈ Finset.range (K + 1), q r) * wordGapPotential n z) :=
        mul_le_mul_of_nonneg_left
          (sum_wordBoundaryPotential_run_cutoff_le n K z q hq) (Real.sqrt_nonneg _)
      _ = (∑ r ∈ Finset.range (K + 1), q r) *
          (Real.sqrt (N : ℝ) * wordGapPotential n z) := by ring
      _ ≤ e * (Real.sqrt (N : ℝ) * wordGapPotential n z) :=
        mul_le_mul_of_nonneg_right hqK
          (mul_nonneg (Real.sqrt_nonneg _) (wordGapPotential_nonneg _ _))
      _ ≤ e * P := mul_le_mul_of_nonneg_left hpotn he.le
  have hinv : 1 / (N : ℝ) ≤ e := by
    apply (div_le_iff₀ hNr).2
    have hh := (div_le_iff₀ he).mp hlargeN
    nlinarith
  have hremain :
      (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        if n - s - r ≤ K then H s r else 0) ≤ 2 * D * e := by
    have hclock' : c * N ≤ (n : ℝ) - K := by
      have hh := mul_le_mul_of_nonneg_right hηc.le (Nat.cast_nonneg N)
      linarith only [hh, hn.1, hK]
    have hbound := sum_word_terminal_strip_weighted_le N n K
      (fun s => srwKernel (2 * s) z) q (G / (δ ^ 2 * N)) B c
      (by omega) hc hclock' (by positivity) hq (fun s => srwKernel_nonneg _ _)
      (fun s _ => hkernel N (by omega) δ hδ z hz s) hqtotal
    have hratio : ((K : ℝ) + 1) / N ≤ η + 1 / N := by
      apply (div_le_iff₀ hNr).2
      have heq' : (η + 1 / (N : ℝ)) * N = η * N + 1 := by field_simp
      rw [heq']
      linarith
    calc
      _ ≤ (1 / Real.sqrt c) * ((G / (δ ^ 2 * N)) * (K + 1) * B) := hbound
      _ = D * (((K : ℝ) + 1) / N) := by dsimp [D]; ring
      _ ≤ D * (η + 1 / N) := mul_le_mul_of_nonneg_left hratio hD.le
      _ ≤ D * (e + e) := mul_le_mul_of_nonneg_left (add_le_add hηe.le hinv) hD.le
      _ = 2 * D * e := by ring
  have hcover (s r : ℕ) :
      ((s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨ ((n - s - r : ℕ) : ℝ) < η * N) →
        s ≤ K ∨ r ≤ K ∨ n - s - r ≤ K := by
    intro hh
    rcases hh with hh | hh | hh
    · exact Or.inl (Nat.le_floor hh.le)
    · exact Or.inr (Or.inl (Nat.le_floor hh.le))
    · exact Or.inr (Or.inr (Nat.le_floor hh.le))
  have hpoint (s r : ℕ) :
      (if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨ ((n - s - r : ℕ) : ℝ) < η * N
        then H s r else 0) ≤
      (if s ≤ K then H s r else 0) + (if r ≤ K then H s r else 0) +
        (if n - s - r ≤ K then H s r else 0) := by
    exact indicator_cover_three_le _ _ _ _ (H s r) (hH s r) (hcover s r)
  change (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
    if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨ ((n - s - r : ℕ) : ℝ) < η * N
      then H s r else 0) ≤ ε
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ((if s ≤ K then H s r else 0) + (if r ≤ K then H s r else 0) +
          (if n - s - r ≤ K then H s r else 0)) :=
      Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun r _ => hpoint s r))
    _ ≤ E * e + e * P + 2 * D * e := by
      simp only [Finset.sum_add_distrib]
      linarith only [hentrance, hrun, hremain]
    _ ≤ ε := by
      nlinarith only [heq, mul_nonneg hE.le he.le, mul_nonneg hP.le he.le,
        mul_nonneg hD.le he.le, he.le]


private theorem exists_wordFirstBlock_test_time_envelope
    (ϑ T : ℝ) (hT : 0 < T) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
    (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ s r : ℕ, s + r ≤ n → ∀ x : LatticeConfiguration h,
        |∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          wordFirstBlockKernel (criticalBeta ϑ N) α s r x v *
            wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (n - s - r) v Ψ| ≤
          C * (Real.sqrt (N : ℝ) *
            (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
              (sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
                (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) /
              Real.sqrt ((s : ℝ) + r + 1))) := by
  cases w with
  | nil =>
      refine ⟨(M + 1) * Real.sqrt (T + 1), by positivity, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with N hN
      intro n hn s r hfit x
      have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hfitreal : (s : ℝ) + r ≤ n := by exact_mod_cast hfit
      have htime : (s : ℝ) + r + 1 ≤ (T + 1) * N := by
        nlinarith only [hn, hfitreal, hNreal]
      have hsqrt : Real.sqrt ((s : ℝ) + r + 1) ≤
          Real.sqrt (T + 1) * Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ T + 1)]
        exact Real.sqrt_le_sqrt htime
      have hcoef : M ≤ ((M + 1) * Real.sqrt (T + 1) * Real.sqrt (N : ℝ)) /
          Real.sqrt ((s : ℝ) + r + 1) := by
        apply (le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))).2
        calc
          _ ≤ M * (Real.sqrt (T + 1) * Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hsqrt hM
          _ ≤ (M + 1) * (Real.sqrt (T + 1) * Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
          _ = _ := by ring
      have hq : 0 ≤ srwKernel (2 * s) (x α.1.2 - x α.1.1) *
          (sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
            (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) :=
        mul_nonneg (srwKernel_nonneg _ _) (mul_nonneg (sigmaSq_nonneg _)
          (Renewal.renewalMass_nonneg (fun k => mul_nonneg (sigmaSq_nonneg _)
            (srwKernel_nonneg _ _)) r))
      calc
        _ ≤ M * (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
              (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r)) :=
          abs_wordFirstBlock_nil_le N (criticalBeta ϑ N) α s r (n - s - r) x Ψ M hΨ
        _ ≤ _ := (mul_le_mul_of_nonneg_right hcoef hq).trans_eq (by ring)
  | cons β w =>
      have hne : α ≠ β := (List.isChain_cons_cons.mp hw).1
      obtain ⟨D, hDpos, htail⟩ := hD hT β w hw.tail
      obtain ⟨A, hA, hblock⟩ := exists_wordFirstBlock_gapPotential_bound
      refine ⟨(M + 1) * D * A, by positivity, ?_⟩
      filter_upwards [htail] with N htailN
      intro n hn s r _hfit x
      have hLn : n - s - r ≤ n := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
      have hL : ((n - s - r : ℕ) : ℝ) ≤ T * N := (Nat.cast_le.mpr hLn).trans hn
      have hb := abs_wordFirstBlock_cons_le_of_tail_potential_bound N
        (criticalBeta ϑ N) α β w s r (n - s - r) (n - s - r) x Ψ M D A
        hM hDpos.le le_rfl (fun v => htailN _ hL v) hΨ
        (hblock (criticalBeta ϑ N) α β hne s r (n - s - r) x)
      have hcoef : M * D * A ≤ (M + 1) * D * A :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hDpos.le) hA.le
      have hq : 0 ≤ Real.sqrt (N : ℝ) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
              (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) /
              Real.sqrt ((s : ℝ) + r + 1)) := by
        apply mul_nonneg (Real.sqrt_nonneg _)
        apply div_nonneg _ (Real.sqrt_nonneg _)
        exact mul_nonneg (srwKernel_nonneg _ _) (mul_nonneg (sigmaSq_nonneg _)
          (Renewal.renewalMass_nonneg (fun k => mul_nonneg (sigmaSq_nonneg _)
            (srwKernel_nonneg _ _)) r))
      calc
        _ ≤ _ := hb
        _ = (M * D * A) * (Real.sqrt (N : ℝ) *
            (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
              (sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
                (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) /
              Real.sqrt ((s : ℝ) + r + 1))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hq


/-- All three microscopic boundary strips vanish uniformly as their macroscopic width
shrinks. The next-word potential is evaluated at the remaining horizon. -/
theorem wordFirstLetter_time_boundary_small_of_potentialDomination
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
    {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hsep : x α.1.1 ≠ x α.1.2)
    (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M) :
    ∀ ε > 0, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∀ᶠ N : ℕ in atTop,
        |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
          if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
              ((nN N - s - r : ℕ) : ℝ) < η * N then
            ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) (xN N),
              wordFirstBlockKernel (criticalBeta ϑ N) α s r (xN N) v *
                wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ
          else 0| ≤ ε := by
  let T := τ + 1
  let c := τ / 4
  have hT : 0 < T := by dsimp [T]; linarith only [hτ]
  have hc : 0 < c := by dsimp [c]; positivity
  have hnear : ∀ᶠ N : ℕ in atTop,
      τ / 2 < (nN N : ℝ) / N ∧ (nN N : ℝ) / N < τ + 1 :=
    hn.eventually (Ioo_mem_nhds (by linarith only [hτ]) (by linarith))
  have hclock : ∀ᶠ N : ℕ in atTop,
      2 * c * N ≤ (nN N : ℝ) ∧ (nN N : ℝ) ≤ T * N := by
    filter_upwards [hnear, eventually_ge_atTop 1] with N hnearN hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    constructor
    · have hh := (lt_div_iff₀ hNr).mp hnearN.1
      dsimp [c]
      linarith only [hh]
    · exact ((div_lt_iff₀ hNr).mp hnearN.2).le
  let zN : ℕ → Site := fun N => xN N α.1.2 - xN N α.1.1
  let δ := ‖x α.1.2 - x α.1.1‖ / 2
  have hδ : 0 < δ := half_pos
    (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hsep)))
  have hgap : Tendsto (fun N => latticeRepresentative N (zN N)) atTop
      (𝓝 (x α.1.2 - x α.1.1)) := by
    simpa only [zN, latticeRepresentative_sub] using (hx α.1.2).sub (hx α.1.1)
  have hseparated : ∀ᶠ N : ℕ in atTop, δ ≤ ‖latticeRepresentative N (zN N)‖ := by
    filter_upwards [(Metric.tendsto_nhds.mp hgap) δ hδ] with N hclose
    have hnorm := norm_le_norm_sub_add (x α.1.2 - x α.1.1)
      (latticeRepresentative N (zN N))
    have hclose' : ‖(x α.1.2 - x α.1.1) - latticeRepresentative N (zN N)‖ < δ := by
      simpa only [dist_eq_norm, norm_sub_rev] using hclose
    dsimp [δ] at hclose' ⊢
    linarith only [hnorm, hclose']
  obtain ⟨C, hC, hterms⟩ := exists_wordFirstBlock_test_time_envelope
    ϑ T hT hD α w hw Ψ M hM hΨ
  intro ε hε
  obtain ⟨η₀, hη₀, hsmall⟩ := weighted_time_boundary_small ϑ T c δ hT hc hδ
    nN zN hclock hseparated (ε / C) (div_pos hε hC)
  refine ⟨η₀, hη₀, fun η hη hηsmall => ?_⟩
  filter_upwards [hsmall η hη hηsmall, hterms, hclock] with N hsmallN htermsN hclockN
  let F : ℕ → ℕ → ℝ := fun s r =>
    ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) (xN N),
      wordFirstBlockKernel (criticalBeta ϑ N) α s r (xN N) v *
        wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ
  let H : ℕ → ℕ → ℝ := fun s r => Real.sqrt (N : ℝ) *
    (srwKernel (2 * s) (zN N) *
      (sigmaSq (criticalBeta ϑ N) * Renewal.renewalMass
        (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) r) /
      Real.sqrt ((s : ℝ) + r + 1))
  have hbound (s : ℕ) (hs : s ∈ Finset.Icc 1 (nN N))
      (r : ℕ) (hr : r ∈ Finset.range (nN N - s + 1)) : |F s r| ≤ C * H s r := by
    have hfit : s + r ≤ nN N := by
      have := (Finset.mem_Icc.mp hs).2
      have := Finset.mem_range.mp hr
      omega
    exact htermsN (nN N) hclockN.2 s r hfit (xN N)
  have hscalar :
      (∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
        if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
          ((nN N - s - r : ℕ) : ℝ) < η * N then H s r else 0) ≤ ε / C := hsmallN
  change |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
    if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
      ((nN N - s - r : ℕ) : ℝ) < η * N then F s r else 0| ≤ ε
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 (nN N),
        |∑ r ∈ Finset.range (nN N - s + 1),
          if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
            ((nN N - s - r : ℕ) : ℝ) < η * N then F s r else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
        |if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
          ((nN N - s - r : ℕ) : ℝ) < η * N then F s r else 0| :=
      Finset.sum_le_sum (fun s _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ C * (∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
        if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
          ((nN N - s - r : ℕ) : ℝ) < η * N then H s r else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro r hr
      split_ifs
      · exact hbound s hs r hr
      · simp only [abs_zero, le_refl]
    _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left hscalar hC.le
    _ = ε := by field_simp

end Critical2DKPZ.SHF.Moments
