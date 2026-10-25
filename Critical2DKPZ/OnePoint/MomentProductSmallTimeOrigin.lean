/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.MomentProductGridBound
public import Critical2DKPZ.OnePoint.MomentProductOffGrid
import Critical2DKPZ.OnePoint.OnePointInverseMomentComparison
import Critical2DKPZ.MomentBounds.BlockVarianceReduction
import Critical2DKPZ.OnePoint.CriticalGap
import Critical2DKPZ.OnePoint.Annealing
import Critical2DKPZ.Blocks.GridAlignment
import Mathlib.Tactic

/-! # Small-time comparison at the origin -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem smoothedP2Plane_secondMoment_ge_one (β : ℝ) (s n : ℕ) :
    1 ≤ ∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw := by
  have hmem : MemLp (smoothedP2Plane β s n 0) 2 disorderLaw :=
    Polymer.memLp_smoothedP2Plane β s n 0 2 (by norm_num)
  have hv := ProbabilityTheory.variance_nonneg
    (smoothedP2Plane β s n 0) disorderLaw
  rw [ProbabilityTheory.variance_eq_sub hmem,
    Polymer.integral_smoothedP2Plane] at hv
  norm_num at hv
  linarith

/-- The grid comparison and off-grid estimate imply the small-time origin bound. -/
theorem smallTimeOriginBound_of (hC6 : BlockMomentsBound) (hQ : TiltedRatioBound)
    (A : ℝ) : SmallTimeOriginBound A := by
  obtain ⟨ρ₀, hρ₀, hGridForρ⟩ := log_secondMoment_div_inv_moment_grid_le_of hC6 hQ A
  obtain ⟨Cgrid, J₀, hGrid⟩ := hGridForρ (ρ₀ ^ 2)
  obtain ⟨Cgap, hGapEventually⟩ := renewalGap_criticalBeta_sub_log_bounded A
  obtain ⟨Cperiod, hPeriod⟩ := replicaOverlap_sub_log_bounded
  have hρpos : 0 < ρ₀ := lt_trans (by norm_num) hρ₀
  have hlogρ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
  have hinvPos : 0 < ρ₀⁻¹ := inv_pos.mpr hρpos
  have hinvLt : ρ₀⁻¹ < 1 := (inv_lt_one₀ hρpos).2 hρ₀
  have hinvSqLt : ρ₀⁻¹ ^ 2 < 1 := by
    have hprod := mul_pos hinvPos (by linarith : 0 < 1 - ρ₀⁻¹)
    nlinarith [hprod]
  let Hgap := 4 * (Real.log 2 + |Cgap| + 1)
  let δ₀ := min (ρ₀⁻¹ ^ 2)
    (min (Real.exp (-4 * (J₀ : ℝ) * Real.log ρ₀))
      (min (Real.exp (-Hgap)) (1 / 4)))
  let CperiodAbs := |Cperiod|
  let CgapAbs := |Cgap|
  let Csmall := |Cgrid| * (4 * Real.log ρ₀) ^ ((1 : ℝ) / 4) +
    4 * (Real.log (ρ₀ ^ 2 + 2) + CperiodAbs)
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    positivity
  have hδ₀lt : δ₀ < 1 := by
    dsimp [δ₀]
    exact lt_of_le_of_lt (min_le_left _ _) hinvSqLt
  have hδ₀leρ : δ₀ ≤ ρ₀⁻¹ ^ 2 := min_le_left _ _
  have hδ₀leJ : δ₀ ≤ Real.exp (-4 * (J₀ : ℝ) * Real.log ρ₀) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀leGap : δ₀ ≤ Real.exp (-Hgap) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₀leQuarter : δ₀ ≤ (1 / 4 : ℝ) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨δ₀, Csmall, hδ₀pos, hδ₀lt, ?_⟩
  intro δ hδ hδle
  let q := Real.sqrt δ
  let H := |Real.log δ|
  let γ := gridRatio δ ρ₀
  let J := gridBlocks δ ρ₀
  have hδlt : δ < 1 := lt_of_le_of_lt hδle (lt_of_le_of_lt hδ₀leρ hinvSqLt)
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδlt
  have hHpos : 0 < H := by dsimp [H]; rw [abs_of_neg hlogδ]; exact neg_pos.mpr hlogδ
  have hHgap : Hgap ≤ H := by
    have hδexp : δ ≤ Real.exp (-Hgap) := le_trans hδle hδ₀leGap
    have hlogδle : Real.log δ ≤ -Hgap := by
      calc
        Real.log δ ≤ Real.log (Real.exp (-Hgap)) := Real.log_le_log hδ hδexp
        _ = -Hgap := Real.log_exp _
    dsimp [H]
    rw [abs_of_neg hlogδ]
    linarith
  have hHgrid : 4 * (J₀ : ℝ) * Real.log ρ₀ ≤ H := by
    have hδexp : δ ≤ Real.exp (-4 * (J₀ : ℝ) * Real.log ρ₀) :=
      le_trans hδle hδ₀leJ
    have hlogδle : Real.log δ ≤ -4 * (J₀ : ℝ) * Real.log ρ₀ := by
      calc
        Real.log δ ≤ Real.log (Real.exp (-4 * (J₀ : ℝ) * Real.log ρ₀)) :=
          Real.log_le_log hδ hδexp
        _ = -4 * (J₀ : ℝ) * Real.log ρ₀ := Real.log_exp _
    dsimp [H]
    rw [abs_of_neg hlogδ]
    linarith
  have hδρ : δ ≤ ρ₀⁻¹ ^ 2 := le_trans hδle hδ₀leρ
  have hGridBounds := gridBlocks_bounds hρ₀ hδ hδρ
  have h4logρ : 0 < 4 * Real.log ρ₀ := by positivity
  have hJ₀real : (J₀ : ℝ) ≤ (J : ℝ) := by
    calc
      (J₀ : ℝ) ≤ H / (4 * Real.log ρ₀) := by
        apply (le_div_iff₀ h4logρ).2
        calc
          (J₀ : ℝ) * (4 * Real.log ρ₀) = 4 * (J₀ : ℝ) * Real.log ρ₀ := by ring
          _ ≤ H := hHgrid
      _ ≤ (J : ℝ) := hGridBounds.2.1
  have hJ₀le : J₀ ≤ J := by exact_mod_cast hJ₀real
  have hJpos : 0 < (J : ℝ) := by
    have hJnat : 1 ≤ J := hGridBounds.1
    exact_mod_cast (show 0 < J by omega)
  have hGridRatioMem := gridRatio_mem hρ₀ hδ hδρ
  have hγ : 1 < γ := lt_of_lt_of_le hρ₀ hGridRatioMem.1
  have hγupper : γ ≤ ρ₀ ^ 2 := hGridRatioMem.2
  have hGridEventual := hGrid γ ⟨hGridRatioMem.1, hGridRatioMem.2⟩
  have hAlignmentEventual := blockTime_gridRatio hρ₀ hδ hδρ
  have hOffGridEventual := smoothedP2Plane_secondMoment_sub_le A
  have hClockEventual := blockTime_monotone hγ
  let Nmin := max ⌈γ⌉₊ ⌈2 / q⌉₊
  have hNlarge := eventually_ge_atTop Nmin
  refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
  filter_upwards [hGridEventual, hAlignmentEventual, hOffGridEventual,
    hGapEventually, hNlarge, hClockEventual] with N hGridN hAlignment hOffGrid hGapN hNlarge hClock
  intro ϑ hϑ s hsEven hs
  let n := Critical2DKPZ.evenCeil (q * N)
  let K := blockCount N γ
  let b := K - J
  have hAlignmentK := hAlignment.1
  have hJleK : J ≤ K := by
    dsimp [J, K, γ] at hAlignmentK ⊢
    omega
  have hb : b = K - J := rfl
  have hEnd : blockTime N γ b = n := by
    simpa [b, K, J, n, γ] using hAlignment.2.2
  have hsupport : b + J₀ ≤ K := by
    dsimp [b, K, J, γ] at *
    omega
  have hKminusb : (K : ℝ) - (b : ℝ) = (J : ℝ) := by
    change (K : ℝ) - ((K - J : ℕ) : ℝ) = (J : ℝ)
    rw [Nat.cast_sub hJleK]
    ring
  have hqpos : 0 < q := by dsimp [q]; exact Real.sqrt_pos.2 hδ
  have hceilreal : (1 : ℝ) ≤ (⌈γ⌉₊ : ℝ) :=
    le_trans (le_of_lt hγ) (Nat.le_ceil γ)
  have hNceil : 1 ≤ ⌈γ⌉₊ := by exact_mod_cast hceilreal
  have hNnat : 1 ≤ N := le_trans hNceil
    (le_trans (Nat.le_max_left _ _) hNlarge)
  have hNcast : (⌈γ⌉₊ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show ⌈γ⌉₊ ≤ N from le_trans (Nat.le_max_left _ _) hNlarge)
  have hγleN : γ ≤ (N : ℝ) := le_trans (Nat.le_ceil γ) hNcast
  have hqceil : (⌈2 / q⌉₊ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show ⌈2 / q⌉₊ ≤ N from le_trans (Nat.le_max_right _ _) hNlarge)
  have hqN : 2 ≤ q * (N : ℝ) := by
    have hdiv : 2 / q ≤ (N : ℝ) := le_trans (Nat.le_ceil _) hqceil
    have hmul := (div_le_iff₀ hqpos).1 hdiv
    nlinarith only [hmul]
  have hδquarter : δ ≤ (1 / 4 : ℝ) := le_trans hδle hδ₀leQuarter
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  have hNpos : 1 ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hqNhalf : q * (N : ℝ) ≤ (N : ℝ) / 2 := by
    calc
      q * (N : ℝ) ≤ (1 / 2) * (N : ℝ) := mul_le_mul_of_nonneg_right hqhalf (by positivity)
      _ = (N : ℝ) / 2 := by ring
  have h2qNleN : 2 * q * (N : ℝ) ≤ (N : ℝ) := by nlinarith only [hqNhalf]
  have hnLower : q * (N : ℝ) ≤ (n : ℝ) := by
    dsimp [n, q]
    exact Critical2DKPZ.le_evenCeil _
  have hnUpperStrict : (n : ℝ) < q * (N : ℝ) + 2 := by
    dsimp [n, q]
    exact Critical2DKPZ.evenCeil_lt_add_two (by positivity)
  have hnUpper : (n : ℝ) < 2 * q * (N : ℝ) := by
    linarith only [hnUpperStrict, hqN]
  have hnle : n ≤ N := by
    have hcast : (n : ℝ) < (N : ℝ) := by linarith [hnUpperStrict, hqN, h2qNleN]
    exact_mod_cast (le_of_lt hcast)
  have hnOne : 1 ≤ (n : ℝ) := le_trans (by norm_num) (le_trans hqN hnLower)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnOne
  have hratioN : 1 / (2 * q) ≤ (N : ℝ) / n := by
    apply (le_div_iff₀ hnpos).2
    calc
      (1 / (2 * q)) * (n : ℝ) ≤ (1 / (2 * q)) * (2 * q * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hnUpper) (by positivity)
      _ = (N : ℝ) := by field_simp [ne_of_gt hqpos]
  have hlogq : Real.log q = Real.log δ / 2 := by
    dsimp [q]
    exact Real.log_sqrt hδ.le
  have hlogSmallRatio : Real.log (1 / (2 * q)) = H / 2 - Real.log 2 := by
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (ne_of_gt hqpos), hlogq]
    dsimp [H]
    rw [abs_of_neg hlogδ]
    ring
  have hlogN : Real.log (1 / (2 * q)) ≤ Real.log ((N : ℝ) / n) :=
    Real.log_le_log (by positivity) hratioN
  have hgapBound := hGapN ϑ hϑ n hnle
  have hgapBound' : |renewalGap (criticalBeta ϑ N) n -
      Real.log ((N : ℝ) / n)| ≤ Cgap := by
    simpa [max_eq_left (show 1 ≤ n by exact_mod_cast hnOne)] using hgapBound
  have hgapLower : H / 2 - Real.log 2 - CgapAbs ≤ renewalGap (criticalBeta ϑ N) n := by
    have hbound := (abs_le.mp hgapBound').1
    have hCgapLe : Cgap ≤ CgapAbs := le_abs_self Cgap
    have hbound' : -CgapAbs ≤
        renewalGap (criticalBeta ϑ N) n - Real.log ((N : ℝ) / n) := by
      linarith only [hbound, hCgapLe]
    have hlogLower : H / 2 - Real.log 2 ≤ Real.log ((N : ℝ) / n) := by
      calc
        H / 2 - Real.log 2 = Real.log (1 / (2 * q)) := hlogSmallRatio.symm
        _ ≤ Real.log ((N : ℝ) / n) := hlogN
    calc
      H / 2 - Real.log 2 - CgapAbs ≤ Real.log ((N : ℝ) / n) - CgapAbs :=
        sub_le_sub_right hlogLower CgapAbs
      _ ≤ renewalGap (criticalBeta ϑ N) n := by linarith only [hbound']
  have hgapQuarter : H / 4 ≤ renewalGap (criticalBeta ϑ N) n := by
    dsimp [Hgap] at hHgap
    linarith
  have hgapPos : 0 < renewalGap (criticalBeta ϑ N) n :=
    lt_of_lt_of_le (by positivity : 0 < H / 4) hgapQuarter
  let M := fun a : ℕ =>
    ∫ ω, smoothedP2Plane (criticalBeta ϑ N) a n 0 ω ^ 2 ∂disorderLaw
  let I := fun a : ℕ =>
    ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) a n 0 ω)⁻¹ ∂disorderLaw
  have hExists : ∃ j : ℕ, j ≤ b ∧ s ≤ blockTime N γ j := by
    refine ⟨b, le_rfl, ?_⟩
    rw [hEnd]
    exact hs
  let j := Nat.find hExists
  have hjSpec : j ≤ b ∧ s ≤ blockTime N γ j := by
    simpa [j] using Nat.find_spec hExists
  have hjEnd : blockTime N γ j ≤ n := by
    calc
      blockTime N γ j ≤ blockTime N γ b := hClock hjSpec.1
      _ = n := hEnd
  have hGridLog := hGridN ϑ hϑ j b hjSpec.1 hsupport
  rw [hEnd] at hGridLog
  have hGridLog' : Real.log (M (blockTime N γ j) / I (blockTime N γ j)) ≤
      Cgrid / ((K : ℝ) - b) ^ ((1 : ℝ) / 4) := by
    simpa [M, I] using hGridLog
  have hKminusb' : (K : ℝ) - b = (J : ℝ) := hKminusb
  rw [hKminusb'] at hGridLog'
  have hJpowPos : 0 < (J : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hJpos _
  have hGridLogAbs : Real.log (M (blockTime N γ j) / I (blockTime N γ j)) ≤
      |Cgrid| / (J : ℝ) ^ ((1 : ℝ) / 4) :=
    hGridLog'.trans (div_le_div_of_nonneg_right (le_abs_self Cgrid) hJpowPos.le)
  let ε := |Cgrid| / (J : ℝ) ^ ((1 : ℝ) / 4)
  have hεnonneg : 0 ≤ ε := by dsimp [ε]; positivity
  have hGridMomentOne : 1 ≤ M (blockTime N γ j) := by
    simpa [M] using smoothedP2Plane_secondMoment_ge_one
      (criticalBeta ϑ N) (blockTime N γ j) n
  have hGridInverseOne : 1 ≤ I (blockTime N γ j) := by
    simpa [I] using one_le_integral_inv_smoothedP2Plane
      (criticalBeta ϑ N) (blockTime N γ j) n 0
  have hGridRatioPos : 0 < M (blockTime N γ j) / I (blockTime N γ j) :=
    div_pos (lt_of_lt_of_le zero_lt_one hGridMomentOne)
      (lt_of_lt_of_le zero_lt_one hGridInverseOne)
  have hGridExp : M (blockTime N γ j) / I (blockTime N γ j) ≤ Real.exp ε :=
    (Real.log_le_iff_le_exp hGridRatioPos).1 (by simpa [ε] using hGridLogAbs)
  have hprevlt : j = 0 ∨ (j ≠ 0 ∧ blockTime N γ (j - 1) < s) := by
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    · right
      constructor
      · exact hj0
      have hnot : ¬ (j - 1 ≤ b ∧ s ≤ blockTime N γ (j - 1)) :=
        Nat.find_min hExists (by omega)
      have hprevle : j - 1 ≤ b := by omega
      have hsnot : ¬ s ≤ blockTime N γ (j - 1) := fun h => hnot ⟨hprevle, h⟩
      omega
  have hscaleRatio :
      ((max (blockTime N γ j) 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ) ≤ γ + 2 := by
    rcases hprevlt with hj0 | ⟨hjnonzero, hprev⟩
    · have hsle0 : s ≤ blockTime N γ 0 := by simpa [hj0] using hjSpec.2
      have hs0 : s = 0 := by
        have hsle : s ≤ 0 := by simpa [Critical2DKPZ.blockTime] using hsle0
        omega
      have hsimple : (1 : ℝ) ≤ γ + 2 := by linarith only [hγ]
      simpa [Critical2DKPZ.blockTime, hj0, hs0] using hsimple
    · have hj1 : 1 ≤ j := by omega
      have hratioPrev :
          ((max (blockTime N γ j) 1 : ℕ) : ℝ) /
            ((max (blockTime N γ (j - 1)) 1 : ℕ) : ℝ) ≤ γ + 2 := by
        by_cases hjone : j = 1
        · have hOneSub : j - 1 = 0 := by omega
          simpa [hjone, hOneSub] using
            (Critical2DKPZ.MomentBounds.blockTime_first_endpoint_ratio_le hγ hγleN)
        · have hjtwo : 2 ≤ j := by omega
          have hjK : j < K := by
            dsimp [b] at hjSpec
            omega
          exact Critical2DKPZ.MomentBounds.blockTime_endpoint_ratio_le hγ hjtwo hjK
      have hmaxprevNat : max (blockTime N γ (j - 1)) 1 ≤ max s 1 :=
        max_le_max (Nat.le_of_lt hprev) le_rfl
      have hmaxprev :
          ((max (blockTime N γ (j - 1)) 1 : ℕ) : ℝ) ≤ ((max s 1 : ℕ) : ℝ) := by
        exact_mod_cast hmaxprevNat
      have hratioMono :
          ((max (blockTime N γ j) 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ) ≤
            ((max (blockTime N γ j) 1 : ℕ) : ℝ) /
              ((max (blockTime N γ (j - 1)) 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hmaxprev
      exact hratioMono.trans hratioPrev
  have hperiodBound := hPeriod s (blockTime N γ j) hjSpec.2
  have hperiodUpper :
      Real.pi * (replicaOverlap (blockTime N γ j) - replicaOverlap s) -
        Real.log (((max (blockTime N γ j) 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ CperiodAbs := by
    have h := (abs_le.mp hperiodBound).2
    dsimp [CperiodAbs]
    exact le_trans h (le_abs_self Cperiod)
  have hlogScale :
      Real.log (((max (blockTime N γ j) 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤
        Real.log (ρ₀ ^ 2 + 2) := by
    apply Real.log_le_log (by positivity)
    linarith only [hscaleRatio, hγupper]
  let L := Real.log (ρ₀ ^ 2 + 2) + CperiodAbs
  have hOverlapBound :
      Real.pi * (replicaOverlap (blockTime N γ j) - replicaOverlap s) ≤ L := by
    dsimp [L]
    calc
      Real.pi * (replicaOverlap (blockTime N γ j) - replicaOverlap s) =
          (Real.pi * (replicaOverlap (blockTime N γ j) - replicaOverlap s) -
            Real.log (((max (blockTime N γ j) 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ))) +
            Real.log (((max (blockTime N γ j) 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) := by ring
      _ ≤ CperiodAbs + Real.log (ρ₀ ^ 2 + 2) :=
        add_le_add hperiodUpper hlogScale
      _ = Real.log (ρ₀ ^ 2 + 2) + CperiodAbs := by ring
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log (ρ₀ ^ 2 + 2) :=
      Real.log_nonneg (by linarith only [sq_nonneg ρ₀])
    positivity
  have hMdiff := hOffGrid ϑ hϑ s (blockTime N γ j) n hjSpec.2 hjEnd hgapPos
  have hMdiffUpper : M s - M (blockTime N γ j) ≤
      Real.pi * (replicaOverlap (blockTime N γ j) - replicaOverlap s) /
        renewalGap (criticalBeta ϑ N) n := by
    simpa [M] using hMdiff.2
  let Δ := 4 * L / H
  have hΔnonneg : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hMupper : M s ≤ M (blockTime N γ j) + Δ := by
    have hfrac :
        Real.pi * (replicaOverlap (blockTime N γ j) - replicaOverlap s) /
          renewalGap (criticalBeta ϑ N) n ≤ Δ := by
      dsimp [Δ]
      calc
        _ ≤ L / renewalGap (criticalBeta ϑ N) n :=
          div_le_div_of_nonneg_right hOverlapBound hgapPos.le
        _ ≤ L / (H / 4) := div_le_div_of_nonneg_left hLnonneg (by positivity) hgapQuarter
        _ = 4 * L / H := by field_simp [ne_of_gt hHpos]
    linarith [hMdiffUpper, hfrac]
  have hIanti : I (blockTime N γ j) ≤ I s := by
    simpa [I] using integral_inv_smoothedP2Plane_anti
      (criticalBeta ϑ N) 0 hjSpec.2 hjEnd
  have hMpos : 0 ≤ M s := integral_nonneg fun ω => sq_nonneg _
  have hRatioCmp : M s / I s ≤ M (blockTime N γ j) / I (blockTime N γ j) + Δ := by
    have hfirst : M s / I s ≤ M s / I (blockTime N γ j) :=
      div_le_div_of_nonneg_left hMpos
        (lt_of_lt_of_le zero_lt_one hGridInverseOne) hIanti
    have hsecond : M s / I (blockTime N γ j) ≤
        (M (blockTime N γ j) + Δ) / I (blockTime N γ j) :=
      div_le_div_of_nonneg_right hMupper
        (lt_of_lt_of_le zero_lt_one hGridInverseOne).le
    have hsum : (M (blockTime N γ j) + Δ) / I (blockTime N γ j) ≤
        M (blockTime N γ j) / I (blockTime N γ j) + Δ := by
      rw [add_div]
      have hΔdiv : Δ / I (blockTime N γ j) ≤ Δ := by
        calc
          Δ / I (blockTime N γ j) ≤ Δ / 1 :=
            div_le_div_of_nonneg_left hΔnonneg (by norm_num) hGridInverseOne
          _ = Δ := by simp
      calc
        M (blockTime N γ j) / I (blockTime N γ j) +
            Δ / I (blockTime N γ j) =
            Δ / I (blockTime N γ j) + M (blockTime N γ j) / I (blockTime N γ j) := by ring
        _ ≤ Δ + M (blockTime N γ j) / I (blockTime N γ j) := by
          exact add_le_add_left hΔdiv _
        _ = M (blockTime N γ j) / I (blockTime N γ j) + Δ := by ring
    calc
      M s / I s ≤ M s / I (blockTime N γ j) := hfirst
      _ ≤ (M (blockTime N γ j) + Δ) / I (blockTime N γ j) := hsecond
      _ ≤ M (blockTime N γ j) / I (blockTime N γ j) + Δ := hsum
  have hGridRatioUpper : M (blockTime N γ j) / I (blockTime N γ j) + Δ ≤
      Real.exp ε + Δ := by
    calc
      M (blockTime N γ j) / I (blockTime N γ j) + Δ =
          Δ + M (blockTime N γ j) / I (blockTime N γ j) := by ring
      _ ≤ Δ + Real.exp ε := add_le_add_right hGridExp Δ
      _ = Real.exp ε + Δ := by ring
  have hRatioExp : M s / I s ≤ Real.exp (ε + Δ) := by
    calc
      M s / I s ≤ M (blockTime N γ j) / I (blockTime N γ j) + Δ := hRatioCmp
      _ ≤ Real.exp ε + Δ := hGridRatioUpper
      _ ≤ Real.exp ε * Real.exp Δ := by
        calc
          Real.exp ε + Δ ≤ Real.exp ε + Real.exp ε * Δ :=
            by
              have hExpMul : Δ ≤ Real.exp ε * Δ :=
                by
                  simpa only [one_mul] using mul_le_mul_of_nonneg_right
                    (Real.one_le_exp_iff.mpr hεnonneg) hΔnonneg
              linarith only [hExpMul]
          _ = Real.exp ε * (1 + Δ) := by ring
          _ ≤ Real.exp ε * Real.exp Δ :=
            mul_le_mul_of_nonneg_left
              (by linarith only [Real.add_one_le_exp Δ]) (Real.exp_nonneg ε)
      _ = Real.exp (ε + Δ) := (Real.exp_add ε Δ).symm
  have hRatioPos : 0 < M s / I s := by
    have hMs : 0 < M s := by
      have h := smoothedP2Plane_secondMoment_ge_one (criticalBeta ϑ N) s n
      simpa [M] using lt_of_lt_of_le zero_lt_one h
    have hIs : 0 < I s := by
      have h := one_le_integral_inv_smoothedP2Plane (criticalBeta ϑ N) s n 0
      simpa [I] using lt_of_lt_of_le zero_lt_one h
    exact div_pos hMs hIs
  have hlogFinal : Real.log (M s / I s) ≤ ε + Δ :=
    (Real.log_le_iff_le_exp hRatioPos).2 hRatioExp
  let Hpow := H ^ ((1 : ℝ) / 4)
  let Jpow := (J : ℝ) ^ ((1 : ℝ) / 4)
  let CgridScaled := |Cgrid| * (4 * Real.log ρ₀) ^ ((1 : ℝ) / 4)
  have hHone : 1 ≤ H := by
    dsimp [Hgap, H] at hHgap
    rw [abs_of_neg hlogδ] at hHgap
    dsimp [H]
    rw [abs_of_neg hlogδ]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have habs : 0 ≤ |Cgap| := abs_nonneg Cgap
    have hbase : 1 ≤ Real.log 2 + |Cgap| + 1 := by linarith only [hlog2, habs]
    have hfour : 4 ≤ 4 * (Real.log 2 + |Cgap| + 1) := by nlinarith only [hbase]
    linarith only [hHgap, hfour]
  have hHpowPos : 0 < Hpow := by dsimp [Hpow]; exact Real.rpow_pos_of_pos hHpos _
  have hJpowPos : 0 < Jpow := by dsimp [Jpow]; exact Real.rpow_pos_of_pos hJpos _
  have hJlower : H ≤ 4 * Real.log ρ₀ * (J : ℝ) := by
    have h := (div_le_iff₀ h4logρ).mp hGridBounds.2.1
    nlinarith only [h]
  have hHpowLower : Hpow ≤ (4 * Real.log ρ₀) ^ ((1 : ℝ) / 4) * Jpow := by
    calc
      Hpow ≤ (4 * Real.log ρ₀ * (J : ℝ)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (le_of_lt hHpos) hJlower (by norm_num)
      _ = (4 * Real.log ρ₀) ^ ((1 : ℝ) / 4) * Jpow := by
        dsimp [Jpow]
        rw [Real.mul_rpow (by positivity) (by positivity)]
  have hGridScaled : ε ≤ CgridScaled / Hpow := by
    apply (div_le_div_iff₀ hJpowPos hHpowPos).2
    dsimp [ε, Jpow, CgridScaled]
    have hmul := mul_le_mul_of_nonneg_left hHpowLower (abs_nonneg Cgrid)
    simpa [Jpow, mul_assoc] using hmul
  have hHpowLe : Hpow ≤ H := by
    calc
      Hpow = H ^ ((1 : ℝ) / 4) := rfl
      _ ≤ H ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hHone (by norm_num)
      _ = H := by rw [Real.rpow_one]
  have hΔscaled : Δ ≤ (4 * L) / Hpow := by
    apply (div_le_div_of_nonneg_left (by positivity) hHpowPos hHpowLe)
  have htotal : ε + Δ ≤ Csmall / Hpow := by
    calc
      ε + Δ ≤ CgridScaled / Hpow + (4 * L) / Hpow :=
        add_le_add hGridScaled hΔscaled
      _ = Csmall / Hpow := by
        dsimp [Csmall, CgridScaled, L, CperiodAbs]
        rw [← add_div]
  have hfinal : Real.log (M s / I s) ≤ Csmall / Hpow := hlogFinal.trans htotal
  simpa [M, I, Hpow, H] using hfinal

end Critical2DKPZ.OnePoint

end
