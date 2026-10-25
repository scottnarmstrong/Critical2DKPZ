/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.BlockVarianceReduction
public import Critical2DKPZ.MomentBounds.AiiKProfileSpread
public import Critical2DKPZ.MomentBounds.AiiKNormMGF
public import Critical2DKPZ.MomentBounds.AiiKSmoothedShift
public import Critical2DKPZ.MomentBounds.AiiKProfileHypotheses
public import Critical2DKPZ.MomentBounds.CSZ25AssemblyLemmas
public import Critical2DKPZ.MomentBounds.CSZ25ReturnWeights
public import Critical2DKPZ.MomentBounds.CSZ25LocalUniformity
public import Critical2DKPZ.MomentBounds.GreenDiagonal
public import Critical2DKPZ.MomentBounds.ShortBlockMoments
public import Critical2DKPZ.Renewal.CriticalParameter
public import Critical2DKPZ.SHF.Moments.CriticalBoundary
import Mathlib.Tactic

/-! # CSZ25 moment bounds assembled into block estimates -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.MomentBounds

private theorem criticalBeta_le_eventually_on_interval (A β₀ : ℝ) (hβ₀ : 0 < β₀) :
    ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      0 ≤ criticalBeta ϑ N ∧ criticalBeta ϑ N ≤ β₀ := by
  let Aabs := |A|
  have hpos := Renewal.criticalSigmaSq_eventually_pos (-Aabs)
  have hsmall := (SHF.Moments.tendsto_criticalBeta_zero Aabs).eventually_lt_const hβ₀
  filter_upwards [hpos, hsmall, Filter.eventually_ge_atTop 2] with N hpos hsmall hN
  intro ϑ hϑ
  have hθbounds : -Aabs ≤ ϑ ∧ ϑ ≤ Aabs := by
    constructor
    · exact (neg_le_neg (le_abs_self A)).trans hϑ.1
    · exact hϑ.2.trans (le_abs_self A)
  have hmono := Renewal.criticalSigmaSq_mono_parameter hN
  have hσϑ : 0 < criticalSigmaSq ϑ N :=
    lt_of_lt_of_le hpos (hmono hθbounds.1)
  have hσA : 0 < criticalSigmaSq Aabs N :=
    lt_of_lt_of_le hσϑ (hmono hθbounds.2)
  have hσle := hmono hθbounds.2
  have hlog : Real.log (1 + criticalSigmaSq ϑ N) ≤
      Real.log (1 + criticalSigmaSq Aabs N) :=
    Real.log_le_log (by linarith) (by linarith)
  have hβle : criticalBeta ϑ N ≤ criticalBeta Aabs N := by
    unfold criticalBeta
    exact Real.sqrt_le_sqrt hlog
  exact ⟨Real.sqrt_nonneg _, (hβle.trans_lt hsmall).le⟩

/-- Every centered moment in `GenMomentBound` is integrable, for any center. -/
theorem integrable_centeredMoment_profileP2Fun (h : ℕ) (β : ℝ) (L : ℕ)
    (φ : Site → ℝ) (m : ℝ) (hφ : ∀ z, 0 ≤ φ z) (hφ1 : HasSum φ 1) :
    Integrable (fun ω : Disorder =>
      (profileP2Fun β 0 L φ (fun _ => 1) ω - m) ^ h) disorderLaw := by
  let F : Disorder → ℝ := fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω
  have hFmeas : Measurable F := Polymer.measurable_profileP2Fun β 0 L φ (fun _ => 1)
  have hFmem : MemLp F h disorderLaw :=
    Polymer.memLp_profile_probability β 0 L φ (fun _ => 1) hφ hφ1.tsum_eq
      1 (by norm_num) (by intro z; norm_num) h (by simp)
  let c : ℝ := m
  have hcenter : MemLp (fun ω => F ω - c) h disorderLaw :=
    hFmem.sub (memLp_const c : MemLp (fun _ : Disorder => c) h disorderLaw)
  have hcenterMeas : Measurable (fun ω => (F ω - c) ^ h) :=
    (hFmeas.sub_const c).pow_const h
  have hnormInt : Integrable (fun ω : Disorder => ‖F ω - c‖ ^ h) disorderLaw :=
    hcenter.integrable_norm_pow'
  have hcenterInt : Integrable (fun ω : Disorder => (F ω - c) ^ h) disorderLaw :=
    hnormInt.mono' hcenterMeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      exact le_of_eq (norm_pow _ _))
  simpa [F, c] using hcenterInt

/-- The centered moment of order `h` is bounded by a constant times the variance to power `h / 2`, uniformly over localized probability profiles with bounded variance. -/
def GenMomentBound (h : ℕ) : Prop :=
  ∀ t c₁ c₂ c₃ : ℝ, 0 < t → 0 < c₁ → 0 < c₂ → 0 < c₃ →
    ∃ (L₀ : ℕ) (C : ℝ), ∀ β : ℝ, 0 ≤ β → ∀ L : ℕ, L₀ ≤ L → ∀ φ : Site → ℝ, (∀ z, 0 ≤ φ z) →
      HasSum φ 1 → ExpLocalized t c₁ L φ → ∑' z, φ z ^ 2 ≤ c₂ / profileSpread φ →
      Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ≤ c₃ →
      |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
        C * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ ((h : ℝ) / 2)

/-- Geometric-block fourth moments are bounded by the squared variance uniformly in the ratio and block index, with a horizon threshold allowed to depend on the ratio. -/
def BlockFourthMomentBound : Prop :=
  ∀ A ρ₀ ρ₁ : ℝ, 1 < ρ₀ → ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁,
    ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i ≤ blockCount N ρ →
        ∫ ω, |smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (i - 1))
            (blockTime N ρ i) 0 ω - 1| ^ 4 ∂disorderLaw ≤
          C * Var[fun ω => smoothedP2Plane (criticalBeta ϑ N)
              (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω; disorderLaw] ^ 2

private theorem blockTime_interior_start_le_multiple_duration {N i : ℕ} {ρ₀ ρ : ℝ}
    (hρ₀ : 1 < ρ₀) (hρ₀ρ : ρ₀ ≤ ρ)
    (hclock : Monotone (blockTime N ρ)) (hi : 2 ≤ i)
    (hiK : i < blockCount N ρ)
    (hD : (2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹) + 2 ≤
      ((blockTime N ρ i - blockTime N ρ (i - 1) : ℕ) : ℝ)) :
    (blockTime N ρ (i - 1) : ℝ) ≤
      (2 / (ρ₀ - 1)) * (blockTime N ρ i - blockTime N ρ (i - 1) : ℕ) := by
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ
  have hρpos : 0 < ρ := by linarith
  have hρ₀pos : 0 < ρ₀ := by linarith
  have ha : 0 < ρ₀ - 1 := by linarith
  have hδ₀ : 0 < 1 - ρ₀⁻¹ := by
    have hinv : ρ₀⁻¹ < 1 := (inv_lt_one₀ hρ₀pos).2 hρ₀
    linarith
  have hInv : ρ⁻¹ ≤ ρ₀⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hρ₀pos hρ₀ρ
  have hδ : 1 - ρ₀⁻¹ ≤ 1 - ρ⁻¹ := by linarith
  have haOver : (ρ₀ - 1) / ρ ≤ 1 - ρ⁻¹ := by
    calc
      (ρ₀ - 1) / ρ ≤ (ρ - 1) / ρ :=
        div_le_div_of_nonneg_right (sub_le_sub_right hρ₀ρ 1) hρpos.le
      _ = 1 - ρ⁻¹ := by rw [sub_div, div_self hρpos.ne', one_div]
  let K := blockCount N ρ
  let s := blockTime N ρ (i - 1)
  let n := blockTime N ρ i
  let x : ℝ := (N : ℝ) * ρ ^ ((i : ℝ) - (K : ℝ))
  have hiPrev : 1 ≤ i - 1 := by omega
  have hiPrevK : i - 1 < blockCount N ρ := by omega
  have htimeN : (n : ℝ) = evenCeil x := by
    dsimp [n, x, K]
    simp [blockTime, Nat.ne_of_gt (by omega : 0 < i), hiK]
  have hiCast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ i by omega))
  have hprevExp : ((i - 1 : ℕ) : ℝ) - (K : ℝ) =
      ((i : ℝ) - (K : ℝ)) - 1 := by linarith
  have hpowMul : ρ ^ (((i - 1 : ℕ) : ℝ) - (K : ℝ)) * ρ =
      ρ ^ ((i : ℝ) - (K : ℝ)) := by
    calc
      _ = ρ ^ (((i - 1 : ℕ) : ℝ) - (K : ℝ)) * ρ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ρ ^ ((((i - 1 : ℕ) : ℝ) - (K : ℝ)) + 1) := by
        rw [← Real.rpow_add (by linarith : 0 < ρ)]
      _ = ρ ^ ((i : ℝ) - (K : ℝ)) := by congr 1; linarith [hiCast]
  have hpowDiv : ρ ^ (((i - 1 : ℕ) : ℝ) - (K : ℝ)) =
      ρ ^ ((i : ℝ) - (K : ℝ)) / ρ := by
    apply (eq_div_iff hρpos.ne').2
    simpa only [mul_comm] using hpowMul
  have hxprev : (N : ℝ) * ρ ^ (((i - 1 : ℕ) : ℝ) - (K : ℝ)) = x / ρ := by
    rw [hpowDiv]
    dsimp [x]
    ring
  have htimeS : (s : ℝ) = evenCeil (x / ρ) := by
    have hformula : (s : ℝ) = evenCeil
        ((N : ℝ) * ρ ^ (((i - 1 : ℕ) : ℝ) - (K : ℝ))) := by
      dsimp [s]
      simp [blockTime, K, Nat.ne_of_gt (by omega : 0 < i - 1), hiPrevK]
    rw [hformula, hxprev]
  have hsUpper : (s : ℝ) < x / ρ + 2 := by
    rw [htimeS]
    exact evenCeil_lt_add_two (by positivity)
  have hnLower : x ≤ (n : ℝ) := by
    rw [htimeN]
    exact le_evenCeil x
  have hnUpper : (n : ℝ) < x + 2 := by
    rw [htimeN]
    exact evenCeil_lt_add_two (by positivity)
  have hsn : s ≤ n := by dsimp [s, n]; exact hclock (Nat.sub_le i 1)
  have hsubCast : ((n - s : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) := by
    rw [Nat.cast_sub hsn]
  have hdUpper : ((n - s : ℕ) : ℝ) < x + 2 := by
    rw [hsubCast]
    have hsNonneg : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    linarith
  have hdelta : 0 ≤ 1 - ρ⁻¹ := by linarith
  have hdLower : x * (1 - ρ⁻¹) - 2 ≤ ((n - s : ℕ) : ℝ) := by
    have h := blockTime_duration_lower_geometric_scale hρ (by omega) hiK
    simpa only [x, K, s, n, hsubCast] using h
  have hxLarge : (2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹) < x := by
    linarith
  have hxDelta : 2 * (ρ₀ - 1) + 6 ≤ x * (1 - ρ⁻¹) := by
    have hδ₀x : 2 * (ρ₀ - 1) + 6 ≤ x * (1 - ρ₀⁻¹) := by
      calc
        _ = ((2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹)) * (1 - ρ₀⁻¹) := by
          field_simp [ne_of_gt hδ₀]
        _ ≤ x * (1 - ρ₀⁻¹) :=
          mul_le_mul_of_nonneg_right (le_of_lt hxLarge) hδ₀.le
    exact hδ₀x.trans (mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ x))
  have haS : (ρ₀ - 1) * (s : ℝ) ≤ x * (1 - ρ⁻¹) + 2 * (ρ₀ - 1) := by
    calc
      _ ≤ (ρ₀ - 1) * (x / ρ + 2) := mul_le_mul_of_nonneg_left hsUpper.le ha.le
      _ = x * ((ρ₀ - 1) / ρ) + 2 * (ρ₀ - 1) := by ring
      _ ≤ x * (1 - ρ⁻¹) + 2 * (ρ₀ - 1) := by
        have hx0 : 0 ≤ x := by dsimp [x]; positivity
        exact add_le_add (mul_le_mul_of_nonneg_left haOver hx0) le_rfl
  have hAd : (ρ₀ - 1) * (s : ℝ) ≤ 2 * ((n - s : ℕ) : ℝ) := by
    linarith [hdLower, hxDelta, haS]
  have htarget : (s : ℝ) ≤ 2 * ((n - s : ℕ) : ℝ) / (ρ₀ - 1) :=
    (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hAd)
  simpa [s, n, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htarget

private theorem blockTime_final_start_le_multiple_duration {N : ℕ} {ρ₀ ρ : ℝ}
    (hρ₀ : 1 < ρ₀) (hρ₀ρ : ρ₀ ≤ ρ)
    (hK : 2 ≤ blockCount N ρ)
    (hclock : Monotone (blockTime N ρ))
    (hD : (2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹) + 2 ≤
      ((blockTime N ρ (blockCount N ρ) -
        blockTime N ρ (blockCount N ρ - 1) : ℕ) : ℝ)) :
    (blockTime N ρ (blockCount N ρ - 1) : ℝ) ≤
      (2 / (ρ₀ - 1)) *
        (blockTime N ρ (blockCount N ρ) -
          blockTime N ρ (blockCount N ρ - 1) : ℕ) := by
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ
  have hρpos : 0 < ρ := by linarith
  have hρ₀pos : 0 < ρ₀ := by linarith
  have ha : 0 < ρ₀ - 1 := by linarith
  have hδ₀ : 0 < 1 - ρ₀⁻¹ := by
    have hinv : ρ₀⁻¹ < 1 := (inv_lt_one₀ hρ₀pos).2 hρ₀
    linarith
  have hInv : ρ⁻¹ ≤ ρ₀⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hρ₀pos hρ₀ρ
  have hδ : 1 - ρ₀⁻¹ ≤ 1 - ρ⁻¹ := by linarith
  have haOver : (ρ₀ - 1) / ρ ≤ 1 - ρ⁻¹ := by
    calc
      (ρ₀ - 1) / ρ ≤ (ρ - 1) / ρ :=
        div_le_div_of_nonneg_right (sub_le_sub_right hρ₀ρ 1) hρpos.le
      _ = 1 - ρ⁻¹ := by rw [sub_div, div_self hρpos.ne', one_div]
  let K := blockCount N ρ
  let s := blockTime N ρ (K - 1)
  have hKpos : 0 < K := by dsimp [K]; omega
  have hspos : 1 ≤ K - 1 := by dsimp [K]; omega
  have hslt : K - 1 < K := by dsimp [K]; omega
  have hsn : s ≤ N := by
    have hend : blockTime N ρ (blockCount N ρ) = N := by
      simp [blockTime, Nat.ne_of_gt (by omega : 0 < blockCount N ρ)]
    have hmono := hclock (Nat.sub_le (blockCount N ρ) 1)
    rw [hend] at hmono
    simpa [s, K] using hmono
  have hsubCast : ((N - s : ℕ) : ℝ) = (N : ℝ) - (s : ℝ) := by rw [Nat.cast_sub hsn]
  have hDleN : ((N - s : ℕ) : ℝ) ≤ (N : ℝ) := by
    rw [hsubCast]
    exact sub_le_self _ (by positivity)
  have hend : blockTime N ρ K = N := by
    simp [blockTime, K, Nat.ne_of_gt (by omega : 0 < blockCount N ρ)]
  have hD' : (2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹) + 2 ≤ (N - s : ℕ) := by
    simpa [s, K, hend] using hD
  have hxLarge : (2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹) ≤ (N : ℝ) := by
    have hDcast : (2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹) + 2 ≤ ((N - s : ℕ) : ℝ) := by
      exact_mod_cast hD'
    linarith [hDleN, hDcast]
  have hxDelta : 2 * (ρ₀ - 1) + 6 ≤ (N : ℝ) * (1 - ρ⁻¹) := by
    have hδ₀N : 2 * (ρ₀ - 1) + 6 ≤ (N : ℝ) * (1 - ρ₀⁻¹) := by
      calc
        _ = ((2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹)) * (1 - ρ₀⁻¹) := by
          field_simp [ne_of_gt hδ₀]
        _ ≤ (N : ℝ) * (1 - ρ₀⁻¹) :=
          mul_le_mul_of_nonneg_right hxLarge hδ₀.le
    exact hδ₀N.trans (mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ (N : ℝ)))
  have hgap : 2 ≤ (N : ℝ) * (1 - ρ⁻¹) := by linarith [hxDelta]
  have hdurLower : (N : ℝ) * (1 - ρ⁻¹) - 2 ≤ ((N - s : ℕ) : ℝ) := by
    have h := blockTime_final_duration_lower_geometric_scale hρ hK hgap
    simpa [s, K, hend] using h
  have hprevCast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K)]
    norm_num
  have hprevTime : (s : ℝ) = evenCeil ((N : ℝ) * ρ⁻¹) := by
    dsimp [s]
    have hprev : K - 1 ≠ 0 := by omega
    simp [blockTime, K, hprev, hslt]
    rw [hprevCast]
    congr 1
    rw [show (K : ℝ) - 1 - (K : ℝ) = -1 by ring, Real.rpow_neg_one]
  have hsUpper : (s : ℝ) < (N : ℝ) / ρ + 2 := by
    rw [hprevTime]
    have h := evenCeil_lt_add_two (by positivity : 0 ≤ (N : ℝ) * ρ⁻¹)
    convert h using 1; ring
  have haS : (ρ₀ - 1) * (s : ℝ) ≤ (N : ℝ) * (1 - ρ⁻¹) + 2 * (ρ₀ - 1) := by
    calc
      _ ≤ (ρ₀ - 1) * ((N : ℝ) / ρ + 2) := mul_le_mul_of_nonneg_left hsUpper.le ha.le
      _ = (N : ℝ) * ((ρ₀ - 1) / ρ) + 2 * (ρ₀ - 1) := by ring
      _ ≤ (N : ℝ) * (1 - ρ⁻¹) + 2 * (ρ₀ - 1) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left haOver (Nat.cast_nonneg N)) le_rfl
  have hAd : (ρ₀ - 1) * (s : ℝ) ≤
      2 * ((N - s : ℕ) : ℝ) := by
    linarith [hdurLower, hxDelta, haS]
  have htarget : (s : ℝ) ≤ 2 * ((N - s : ℕ) : ℝ) / (ρ₀ - 1) :=
    (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hAd)
  simpa [s, K, hend, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htarget

/-- The fourth-moment comparison of CSZ25 Theorem 1.11 implies the uniform geometric-block fourth-moment bound. -/
theorem blockFourthMomentBound_of_genMomentBound (h4 : GenMomentBound 4) :
    BlockFourthMomentBound := by
  intro A ρ₀ ρ₁ hρ₀
  let κ : ℝ := 2 / (ρ₀ - 1)
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  obtain ⟨t, c₁, c₂, ht, hc₁, hc₂, hprofile⟩ :=
    srwKernel_profile_hypotheses κ hκ
  obtain ⟨Cint, _hCint, hInterior⟩ :=
    block_interior_variance_le_inverse_remaining_compact A ρ₀ ρ₁ hρ₀
  obtain ⟨Cfinal, _hCfinal, hFinal⟩ :=
    block_final_variance_le_uniform A ρ₀ ρ₁ hρ₀
  let c₃ : ℝ := max |Cint| |Cfinal| + 1
  have hc₃ : 0 < c₃ := by dsimp [c₃]; positivity
  obtain ⟨L₀, Cgen, hgen⟩ := h4 t c₁ c₂ c₃ ht hc₁ hc₂ hc₃
  let Mgeom : ℝ := (2 * (ρ₀ - 1) + 6) / (1 - ρ₀⁻¹) + 2
  let Lgeom : ℕ := ⌈Mgeom⌉₊
  let Llong : ℕ := max L₀ Lgeom
  let Lfirst : ℕ := ⌈ρ₁ + 2⌉₊
  let Ldur : ℕ := max Llong Lfirst
  obtain ⟨βint, CshortInt, hβint, hShortInt⟩ :=
    block_shortDuration_fourth_moment Ldur hρ₀
  obtain ⟨βfinal, CshortFinal, hβfinal, hShortFinal⟩ :=
    block_final_shortDuration_fourth_moment Ldur hρ₀
  have hβ₀ : 0 < min βint βfinal := lt_min hβint hβfinal
  obtain ⟨Nβ, hNβ⟩ := Filter.eventually_atTop.1
    (criticalBeta_le_eventually_on_interval A (min βint βfinal) hβ₀)
  let Nclock : ℕ := ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊
  let Nrho : ℕ := ⌈ρ₁⌉₊
  let N₀ : ℕ := max Nβ (max Nclock Nrho)
  refine ⟨max (max |CshortInt| |CshortFinal|) |Cgen|, ?_⟩
  intro ρ hρrange
  filter_upwards [hInterior, hFinal, Filter.eventually_ge_atTop N₀] with
    N hInteriorN hFinalN hNN₀
  have hNβ' : Nβ ≤ N := by
    dsimp [N₀] at hNN₀
    exact (Nat.le_max_left Nβ _).trans hNN₀
  have hNclock : Nclock ≤ N := by
    dsimp [N₀] at hNN₀
    exact (Nat.le_max_left Nclock Nrho).trans
      ((Nat.le_max_right Nβ (max Nclock Nrho)).trans hNN₀)
  have hNrho : Nrho ≤ N := by
    dsimp [N₀] at hNN₀
    exact (Nat.le_max_right Nclock Nrho).trans
      ((Nat.le_max_right Nβ (max Nclock Nrho)).trans hNN₀)
  have hρparts : ρ₀ ≤ ρ ∧ ρ ≤ ρ₁ := Set.mem_Icc.mp hρrange
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρparts.1
  have hρN : ρ ≤ (N : ℝ) := by
    have hceil : ρ₁ ≤ (Nrho : ℝ) := by
      simpa [Nrho] using (Nat.le_ceil ρ₁)
    have hcast : (Nrho : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNrho
    exact hρparts.2.trans (hceil.trans hcast)
  have hclockN : Nclock ≤ N := by simpa [Nclock] using hNclock
  have hclock := blockTime_monotone_of_large_horizon hρ₀ hρparts.1 hclockN
  have hKtwo : 2 ≤ blockCount N ρ := blockCount_ge_two_of_ratio_le_horizon hρ hρN
  have hEnd : blockTime N ρ (blockCount N ρ) = N := by
    simp [blockTime, Nat.ne_of_gt (by omega : 0 < blockCount N ρ)]
  have hβbounds := hNβ N hNβ'
  have hρlower : ρ₀ ≤ ρ := hρparts.1
  have hρupper : ρ ≤ ρ₁ := hρparts.2
  have hprofileMoment
      (β : ℝ) (hβnonneg : 0 ≤ β) {s n : ℕ} (hsn : s ≤ n) (hs : 1 ≤ s)
      (hL : L₀ ≤ n - s) (hscale : (s : ℝ) ≤ κ * (n - s : ℕ))
      (hvarBlock : Var[fun ω : Disorder => smoothedP2Plane β s n 0 ω; disorderLaw] ≤ c₃) :
      ∫ ω : Disorder, |smoothedP2Plane β s n 0 ω - 1| ^ 4 ∂disorderLaw ≤
        |Cgen| * Var[fun ω : Disorder => smoothedP2Plane β s n 0 ω; disorderLaw] ^ 2 := by
    let φ : Site → ℝ := fun y => srwKernel s y
    have hφ : ∀ y, 0 ≤ φ y := fun y => by
      dsimp [φ]
      exact srwKernel_nonneg s y
    obtain ⟨hmass, hloc, hsq⟩ := hprofile s (n - s) hs (by simpa [κ] using hscale)
    have hmean : ∫ ω : Disorder, profileP2Fun β 0 (n - s) φ (fun _ => 1) ω
        ∂disorderLaw = 1 :=
      Polymer.integral_profile_flat_probability β 0 (n - s) φ hφ hmass.tsum_eq
    have hFmeas : Measurable (fun ω : Disorder =>
        profileP2Fun β 0 (n - s) φ (fun _ => 1) ω) :=
      Polymer.measurable_profileP2Fun β 0 (n - s) φ (fun _ => 1)
    have hshift : (fun ω : Disorder => smoothedP2Plane β s n 0 ω) =
        fun ω => profileP2Fun β 0 (n - s) φ (fun _ => 1)
          (Smoothing.shiftEnvironment s ω) := by
      funext ω
      exact smoothedP2Plane_eq_profileP2Fun_shift β hsn ω
    have hvarEq : Var[fun ω : Disorder =>
          profileP2Fun β 0 (n - s) φ (fun _ => 1) ω; disorderLaw] =
        Var[fun ω : Disorder => smoothedP2Plane β s n 0 ω; disorderLaw] := by
      rw [hshift]
      exact (Smoothing.measurePreserving_shiftEnvironment s).variance_fun_comp
        hFmeas.aemeasurable |>.symm
    have hvarProfile : Var[fun ω : Disorder =>
        profileP2Fun β 0 (n - s) φ (fun _ => 1) ω; disorderLaw] ≤ c₃ := by
      rw [hvarEq]
      exact hvarBlock
    have hgen := hgen β hβnonneg (n - s) hL φ hφ hmass hloc hsq hvarProfile
    have hmomentShift :
        (∫ ω : Disorder, |smoothedP2Plane β s n 0 ω - 1| ^ 4 ∂disorderLaw) =
          ∫ ω : Disorder,
            |profileP2Fun β 0 (n - s) φ (fun _ => 1) ω - 1| ^ 4 ∂disorderLaw := by
      calc
        _ = ∫ ω : Disorder,
              |profileP2Fun β 0 (n - s) φ (fun _ => 1)
                  (Smoothing.shiftEnvironment s ω) - 1| ^ 4 ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact congrArg (fun x : ℝ => |x - 1| ^ 4) (congrFun hshift ω)
        _ = _ := Smoothing.integral_shiftEnvironment s (by
          have habs : Measurable (fun ω : Disorder =>
              |profileP2Fun β 0 (n - s) φ (fun _ => 1) ω - 1|) := by
            have habsNorm : Measurable (fun ω : Disorder =>
                ‖profileP2Fun β 0 (n - s) φ (fun _ => 1) ω - 1‖) :=
              measurable_norm.comp (hFmeas.sub_const 1)
            simpa only [Real.norm_eq_abs] using habsNorm
          exact habs.pow_const 4)
    have hmomentCentered :
        (∫ ω : Disorder,
          |profileP2Fun β 0 (n - s) φ (fun _ => 1) ω - 1| ^ 4 ∂disorderLaw) =
          ∫ ω : Disorder,
            (profileP2Fun β 0 (n - s) φ (fun _ => 1) ω -
              ∫ ω', profileP2Fun β 0 (n - s) φ (fun _ => 1) ω' ∂disorderLaw) ^ 4
              ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [hmean]
      exact abs_pow_four_eq _
    have hgen2 :
        |∫ ω : Disorder,
          (profileP2Fun β 0 (n - s) φ (fun _ => 1) ω -
            ∫ ω', profileP2Fun β 0 (n - s) φ (fun _ => 1) ω' ∂disorderLaw) ^ 4
            ∂disorderLaw| ≤ Cgen *
          Var[fun ω : Disorder => profileP2Fun β 0 (n - s) φ (fun _ => 1) ω;
            disorderLaw] ^ 2 := by
      convert hgen using 1
      norm_num
    calc
      _ = ∫ ω : Disorder,
            |profileP2Fun β 0 (n - s) φ (fun _ => 1) ω - 1| ^ 4 ∂disorderLaw :=
          hmomentShift
      _ = ∫ ω : Disorder,
            (profileP2Fun β 0 (n - s) φ (fun _ => 1) ω -
              ∫ ω', profileP2Fun β 0 (n - s) φ (fun _ => 1) ω' ∂disorderLaw) ^ 4
              ∂disorderLaw := hmomentCentered
      _ ≤ |∫ ω : Disorder,
                (profileP2Fun β 0 (n - s) φ (fun _ => 1) ω -
                  ∫ ω', profileP2Fun β 0 (n - s) φ (fun _ => 1) ω' ∂disorderLaw) ^ 4
                  ∂disorderLaw| := le_abs_self _
      _ ≤ Cgen * Var[fun ω : Disorder =>
            profileP2Fun β 0 (n - s) φ (fun _ => 1) ω; disorderLaw] ^ 2 := hgen2
      _ ≤ |Cgen| * Var[fun ω : Disorder =>
            profileP2Fun β 0 (n - s) φ (fun _ => 1) ω; disorderLaw] ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ = |Cgen| * Var[fun ω : Disorder => smoothedP2Plane β s n 0 ω; disorderLaw] ^ 2 := by
          rw [hvarEq]
  intro ϑ hϑ i hi hiK
  have hβ : 0 ≤ criticalBeta ϑ N ∧ criticalBeta ϑ N ≤ min βint βfinal :=
    hβbounds ϑ hϑ
  let β := criticalBeta ϑ N
  let K := blockCount N ρ
  have hEndK : blockTime N ρ K = N := by simpa [K] using hEnd
  have hvarInterior (hilt : i < K) :
      Var[fun ω : Disorder => smoothedP2Plane β (blockTime N ρ (i - 1))
        (blockTime N ρ i) 0 ω; disorderLaw] ≤ c₃ := by
    have hv := hInteriorN ϑ hϑ ρ hρlower hρupper i hi hilt
    have hgapNat : 1 ≤ K - i := by omega
    have hgap : 1 ≤ ((K - i : ℕ) : ℝ) := by exact_mod_cast hgapNat
    have hden : 0 < ((K - i : ℕ) : ℝ) := by positivity
    have hciBound : Cint / ((K - i : ℕ) : ℝ) ≤ |Cint| := by
      rw [div_le_iff₀ hden]
      calc
        Cint ≤ |Cint| := le_abs_self _
        _ = |Cint| * 1 := by ring
        _ ≤ |Cint| * ((K - i : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hgap (abs_nonneg _)
    have hciAbs : |Cint| ≤ c₃ := by
      dsimp [c₃]
      linarith [le_max_left (|Cint|) (|Cfinal|)]
    exact hv.trans (hciBound.trans hciAbs)
  have hvarFinal :
      Var[fun ω : Disorder => smoothedP2Plane β (blockTime N ρ (K - 1))
        (blockTime N ρ K) 0 ω; disorderLaw] ≤ c₃ := by
    have hv := hFinalN ϑ hϑ ρ hρlower hρupper
    have hv' : Var[fun ω : Disorder => smoothedP2Plane β
        (blockTime N ρ (K - 1)) N 0 ω; disorderLaw] ≤ Cfinal := by
      simpa [K, hEnd] using hv
    have hfinalAbs : |Cfinal| ≤ c₃ := by
      dsimp [c₃]
      have hmax : |Cfinal| ≤ max |Cint| |Cfinal| := le_max_right _ _
      linarith
    have hEndK : blockTime N ρ K = N := by simpa [K] using hEnd
    calc
      Var[fun ω : Disorder => smoothedP2Plane β (blockTime N ρ (K - 1))
          (blockTime N ρ K) 0 ω; disorderLaw] =
        Var[fun ω : Disorder => smoothedP2Plane β (blockTime N ρ (K - 1))
          N 0 ω; disorderLaw] := by rw [hEndK]
      _ ≤ Cfinal := hv'
      _ ≤ c₃ := le_trans (le_abs_self _) hfinalAbs
  by_cases hiFinal : i = K
  · subst i
    let s := blockTime N ρ (K - 1)
    let L := N - s
    have hsn : s ≤ N := by
      change blockTime N ρ (blockCount N ρ - 1) ≤ N
      calc
        blockTime N ρ (blockCount N ρ - 1) ≤
            blockTime N ρ (blockCount N ρ) := hclock (Nat.sub_le _ _)
        _ = N := hEnd
    have hdur : blockTime N ρ K - blockTime N ρ (K - 1) = L := by
      dsimp [L, s]
      rw [hEnd]
    by_cases hlong : Ldur ≤ L
    · have hD : Mgeom ≤ (L : ℝ) := by
        calc
          Mgeom ≤ (Lgeom : ℝ) := by simpa [Lgeom] using (Nat.le_ceil Mgeom)
          _ ≤ (Ldur : ℝ) := by
            have hnat : Lgeom ≤ Ldur := by
              dsimp [Ldur, Llong]
              exact Nat.le_trans (Nat.le_max_right L₀ Lgeom) (Nat.le_max_left _ _)
            exact_mod_cast hnat
          _ ≤ (L : ℝ) := by exact_mod_cast hlong
      have hD' : Mgeom ≤ ((blockTime N ρ K - blockTime N ρ (K - 1) : ℕ) : ℝ) := by
        simpa [hdur] using hD
      have hscale := blockTime_final_start_le_multiple_duration hρ₀ hρlower hKtwo hclock hD'
      have hdurBlock : blockTime N ρ (blockCount N ρ) -
          blockTime N ρ (blockCount N ρ - 1) = L := by simpa [K] using hdur
      have hscaleL : (s : ℝ) ≤ κ * (L : ℝ) := by
        rw [← hdurBlock]
        simpa [κ, s, K] using hscale
      have hs : 1 ≤ s := by
        have hlow := blockTime_lower_geometric_scale hρ (by omega : 1 ≤ K - 1)
          (by omega : K - 1 < K)
        have hpos : 0 < ρ ^ (((K - 1 : ℕ) : ℝ) - 1) :=
          Real.rpow_pos_of_pos (by linarith) _
        have hspos : 0 < (s : ℝ) := lt_of_lt_of_le hpos (by simpa [s, K] using hlow)
        exact_mod_cast hspos
      have hL0dur : L₀ ≤ Ldur := by
        dsimp [Ldur, Llong]
        exact le_trans (Nat.le_max_left L₀ Lgeom) (Nat.le_max_left _ _)
      have hmoment := hprofileMoment β hβ.1 hsn hs (hL0dur.trans hlong)
        hscaleL (by simpa [s, hEndK] using hvarFinal)
      have hmoment' : ∫ ω, |smoothedP2Plane β (blockTime N ρ (K - 1))
          (blockTime N ρ K) 0 ω - 1| ^ 4 ∂disorderLaw ≤
          |Cgen| * Var[fun ω : Disorder => smoothedP2Plane β
            (blockTime N ρ (K - 1)) (blockTime N ρ K) 0 ω; disorderLaw] ^ 2 := by
        simpa [s, hEndK] using hmoment
      exact le_trans hmoment' (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    · have hshortDur : blockTime N ρ K - blockTime N ρ (K - 1) ≤ Ldur := by
        simpa [hdur] using (Nat.lt_of_not_ge hlong).le
      have hshort := hShortFinal hρlower hclock hshortDur β hβ.1
        (hβ.2.trans (min_le_right _ _))
      calc
        _ ≤ CshortFinal * Var[fun ω : Disorder => smoothedP2Plane β
              (blockTime N ρ (K - 1)) (blockTime N ρ K) 0 ω; disorderLaw] ^ 2 := hshort.1
        _ ≤ |CshortFinal| * _ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        _ ≤ max (max |CshortInt| |CshortFinal|) |Cgen| * _ :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (sq_nonneg _)
  · have hiLt : i < K := by omega
    by_cases hfirst : i = 1
    · subst i
      have hstart0 : blockTime N ρ 0 = 0 := by simp [blockTime]
      have hfirstDur : blockTime N ρ 1 - blockTime N ρ (1 - 1) ≤ Ldur := by
        have hendpoint := blockTime_first_endpoint_lt hρ hρN
        have hcast : ((blockTime N ρ 1 - blockTime N ρ (1 - 1) : ℕ) : ℝ) =
            (blockTime N ρ 1 : ℝ) := by
          rw [show 1 - 1 = 0 by omega, hstart0]
          simp
        have hceil : ρ₁ + 2 ≤ (Lfirst : ℝ) := by
          simpa [Lfirst] using (Nat.le_ceil (ρ₁ + 2))
        have hLfirst : (Lfirst : ℝ) ≤ (Ldur : ℝ) := by
          have hnat : Lfirst ≤ Ldur := by
            dsimp [Ldur]
            exact Nat.le_max_right Llong Lfirst
          exact_mod_cast hnat
        have hReal : (blockTime N ρ 1 - blockTime N ρ (1 - 1) : ℕ) < (Ldur : ℝ) := by
          rw [hcast]
          calc
            (blockTime N ρ 1 : ℝ) < ρ + 2 := hendpoint
            _ ≤ ρ₁ + 2 := add_le_add hρupper le_rfl
            _ ≤ (Lfirst : ℝ) := hceil
            _ ≤ (Ldur : ℝ) := hLfirst
        exact_mod_cast hReal.le
      have hshort := hShortInt hρlower hclock (by omega) hiLt hfirstDur β hβ.1
        (hβ.2.trans (min_le_left _ _))
      calc
        _ ≤ CshortInt * Var[fun ω : Disorder => smoothedP2Plane β
              (blockTime N ρ (1 - 1)) (blockTime N ρ 1) 0 ω; disorderLaw] ^ 2 := hshort.1
        _ ≤ |CshortInt| * _ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        _ ≤ max (max |CshortInt| |CshortFinal|) |Cgen| * _ :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) (sq_nonneg _)
    · have hiTwo : 2 ≤ i := by omega
      let s := blockTime N ρ (i - 1)
      let n := blockTime N ρ i
      let L := n - s
      have hsn : s ≤ n := by dsimp [s, n]; exact hclock (Nat.sub_le i 1)
      by_cases hlong : Ldur ≤ L
      · have hgeom : Mgeom ≤ (L : ℝ) := by
          calc
            Mgeom ≤ (Lgeom : ℝ) := by simpa [Lgeom] using (Nat.le_ceil Mgeom)
            _ ≤ (Ldur : ℝ) := by
              have hnat : Lgeom ≤ Ldur := by
                dsimp [Ldur, Llong]
                exact Nat.le_trans (Nat.le_max_right L₀ Lgeom) (Nat.le_max_left _ _)
              exact_mod_cast hnat
            _ ≤ (L : ℝ) := by exact_mod_cast hlong
        have hscale := blockTime_interior_start_le_multiple_duration
          hρ₀ hρlower hclock hiTwo hiLt hgeom
        have hdurBlock : blockTime N ρ i - blockTime N ρ (i - 1) = L := by rfl
        have hscaleL : (s : ℝ) ≤ κ * (L : ℝ) := by
          rw [← hdurBlock]
          simpa [κ, s] using hscale
        have hs : 1 ≤ s := by
          have hlow := blockTime_lower_geometric_scale hρ (by omega : 1 ≤ i - 1)
            (by omega : i - 1 < K)
          have hpos : 0 < ρ ^ (((i - 1 : ℕ) : ℝ) - 1) :=
            Real.rpow_pos_of_pos (by linarith) _
          have hspos : 0 < (s : ℝ) := lt_of_lt_of_le hpos (by simpa [s, K] using hlow)
          exact_mod_cast hspos
        have hL0dur : L₀ ≤ Ldur := by
          dsimp [Ldur, Llong]
          exact le_trans (Nat.le_max_left L₀ Lgeom) (Nat.le_max_left _ _)
        have hmoment := hprofileMoment β hβ.1 hsn hs (hL0dur.trans hlong)
          hscaleL (by simpa [s, n] using hvarInterior hiLt)
        simpa [s, n] using
          (le_trans hmoment (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))
      · have hshortDur : L ≤ Ldur := Nat.le_of_lt (Nat.lt_of_not_ge hlong)
        have hshort := hShortInt hρlower hclock hi hiLt hshortDur β hβ.1
          (hβ.2.trans (min_le_left _ _))
        calc
          _ ≤ CshortInt * Var[fun ω : Disorder => smoothedP2Plane β
                (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω; disorderLaw] ^ 2 := hshort.1
          _ ≤ |CshortInt| * _ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
          _ ≤ max (max |CshortInt| |CshortFinal|) |Cgen| * _ :=
            mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) (sq_nonneg _)

/-- The geometric-block fourth-moment comparison and variance bounds give inverse-remaining-block bounds for the variance and fourth moment. -/
theorem blockMoments_of_blockFourthMomentBound (hBlockFourthMomentInput : BlockFourthMomentBound)
    (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i ≤ blockCount N ρ →
        Var[fun ω => smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (i - 1))
            (blockTime N ρ i) 0 ω; disorderLaw] ≤ C / ((blockCount N ρ : ℝ) + 1 - i) ∧
        ∫ ω, |smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (i - 1))
            (blockTime N ρ i) 0 ω - 1| ^ 4 ∂disorderLaw ≤
          C / ((blockCount N ρ : ℝ) + 1 - i) ^ 2 := by
  obtain ⟨Ck, hK⟩ := hBlockFourthMomentInput A ρ₀ ρ₁ hρ
  obtain ⟨Ci, hCi, hInterior⟩ :=
    block_interior_variance_le_inverse_remaining_compact A ρ₀ ρ₁ hρ
  obtain ⟨Cf, hCf, hFinal⟩ := block_final_variance_le_uniform A ρ₀ ρ₁ hρ
  let Cv := max (2 * Ci) |Cf|
  let C4 := |Ck| * Cv ^ 2
  let C := max Cv C4
  have hCv : 0 ≤ Cv := by
    dsimp [Cv]
    exact le_max_of_le_right (abs_nonneg Cf)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_max_of_le_left hCv
  refine ⟨C, ?_⟩
  intro ρ hρrange
  filter_upwards [hK ρ hρrange, hInterior, hFinal] with N hK hInterior hFinal
  intro ϑ hϑ i hi hiK
  let K := blockCount N ρ
  let D : ℝ := (K : ℝ) + 1 - i
  have hKpos : 0 < K := by dsimp [K]; omega
  have hDpos : 0 < D := by
    dsimp [D, K]
    have hiK' : i ≤ blockCount N ρ := hiK
    have hcast : (i : ℝ) ≤ (blockCount N ρ : ℝ) := by exact_mod_cast hiK'
    linarith
  have hDnonneg : 0 ≤ D := hDpos.le
  have hvarNonneg : 0 ≤ ProbabilityTheory.variance
      (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
        (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω) disorderLaw :=
    ProbabilityTheory.variance_nonneg _ _
  have hvar : ProbabilityTheory.variance
      (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
        (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω) disorderLaw ≤ Cv / D := by
    by_cases hiFinal : i = K
    · have hiEq : i = blockCount N ρ := by simpa [K] using hiFinal
      subst i
      have hEnd : blockTime N ρ (blockCount N ρ) = N := by
        simp [blockTime, Nat.ne_of_gt (show 0 < blockCount N ρ by omega)]
      have hv0 := hFinal ϑ hϑ ρ (Set.mem_Icc.mp hρrange).1 (Set.mem_Icc.mp hρrange).2
      have hv : ProbabilityTheory.variance
          (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
            (blockTime N ρ (blockCount N ρ - 1))
            (blockTime N ρ (blockCount N ρ)) 0 ω) disorderLaw ≤ Cf := by
        simpa only [hEnd] using hv0
      have hD : D = 1 := by simp [D]
      rw [hD]
      calc
        _ ≤ Cf := hv
        _ ≤ |Cf| := le_abs_self _
        _ ≤ Cv := le_max_right _ _
        _ = Cv / 1 := by simp
    · have hiLt : i < K := by omega
      have hvi0 := hInterior ϑ hϑ ρ (Set.mem_Icc.mp hρrange).1
        (Set.mem_Icc.mp hρrange).2 i hi hiLt
      have hvi : ProbabilityTheory.variance
          (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
            (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω) disorderLaw ≤
          Ci / ((K - i : ℕ) : ℝ) := by simpa [K] using hvi0
      have hgapNat : 1 ≤ K - i := by omega
      have hgap : 1 ≤ ((K - i : ℕ) : ℝ) := by exact_mod_cast hgapNat
      have hDgap : D = ((K - i : ℕ) : ℝ) + 1 := by
        dsimp [D, K]
        rw [Nat.cast_sub (by omega : i ≤ blockCount N ρ)]
        ring
      rw [hDgap]
      have hCiNonneg : 0 ≤ Ci := hCi
      have h2Ci : 0 ≤ 2 * Ci := by positivity
      have hCv2 : 2 * Ci ≤ Cv := le_max_left _ _
      have hdenpos : 0 < ((K - i : ℕ) : ℝ) := by positivity
      have hdenpluspos : 0 < ((K - i : ℕ) : ℝ) + 1 := by positivity
      have hbasic : Ci / ((K - i : ℕ) : ℝ) ≤ (2 * Ci) / (((K - i : ℕ) : ℝ) + 1) := by
        apply (div_le_div_iff₀ hdenpos hdenpluspos).2
        have hprod : 0 ≤ Ci * (((K - i : ℕ) : ℝ) - 1) :=
          mul_nonneg hCiNonneg (sub_nonneg.mpr hgap)
        linarith only [hprod]
      have hCvbound : (2 * Ci) / (((K - i : ℕ) : ℝ) + 1) ≤
          Cv / (((K - i : ℕ) : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right hCv2
        positivity
      calc
        _ ≤ Ci / ((K - i : ℕ) : ℝ) := hvi
        _ ≤ (2 * Ci) / (((K - i : ℕ) : ℝ) + 1) := hbasic
        _ ≤ Cv / (((K - i : ℕ) : ℝ) + 1) := hCvbound
  have hmoment := hK ϑ hϑ i hi hiK
  have hvarSq : ProbabilityTheory.variance
      (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
        (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω) disorderLaw ^ 2 ≤ (Cv / D) ^ 2 := by
    exact (sq_le_sq₀ hvarNonneg (div_nonneg hCv hDnonneg)).2 hvar
  have hmomentLe : (∫ ω, |smoothedP2Plane (criticalBeta ϑ N)
      (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω - 1| ^ 4 ∂disorderLaw) ≤
      C4 / D ^ 2 := by
    calc
      _ ≤ Ck * ProbabilityTheory.variance
          (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
            (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω) disorderLaw ^ 2 := hmoment
      _ ≤ |Ck| * ProbabilityTheory.variance
          (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
            (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω) disorderLaw ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |Ck| * (Cv / D) ^ 2 := mul_le_mul_of_nonneg_left hvarSq (abs_nonneg _)
      _ = C4 / D ^ 2 := by dsimp [C4]; rw [div_pow]; ring
  have hvarFinal : ProbabilityTheory.variance
      (fun ω : Disorder => smoothedP2Plane (criticalBeta ϑ N)
        (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω) disorderLaw ≤ C / D := by
    apply le_trans hvar
    exact div_le_div_of_nonneg_right (le_max_left _ _) hDnonneg
  have hmomentFinal : (∫ ω, |smoothedP2Plane (criticalBeta ϑ N)
      (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω - 1| ^ 4 ∂disorderLaw) ≤ C / D ^ 2 := by
    apply le_trans hmomentLe
    apply div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg D)
  exact ⟨by simpa [D, K] using hvarFinal, by simpa [D, K] using hmomentFinal⟩

private theorem summable_centered_quadratic_of_localization
    (t : ℝ) (ht : 0 < t) (L : ℕ) (hL : 0 < L) (φ : Site → ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1) (x₀ m : Plane)
    (hweight : Summable (fun z => φ z * Real.exp
      (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)))) :
    Summable (fun z => ‖siteToPlane z - m‖ ^ 2 * φ z) := by
  let d : Site → ℝ := fun z => ‖siteToPlane z - x₀‖
  have hquadX : Summable (fun z => d z ^ 2 * φ z) := by
    apply Summable.of_nonneg_of_le (fun z => mul_nonneg (sq_nonneg _) (hφ z))
      (fun z => ?_) (hweight.mul_left ((L : ℝ) / t ^ 2))
    have hterm := square_le_scaled_exp_of_sqrt t ht L hL (d z) (norm_nonneg _)
    calc
      d z ^ 2 * φ z ≤ (((L : ℝ) / t ^ 2) * Real.exp
          (2 * t * d z / Real.sqrt (L : ℝ))) * φ z :=
        mul_le_mul_of_nonneg_right hterm (hφ z)
      _ = ((L : ℝ) / t ^ 2) *
          (φ z * Real.exp (2 * t * d z / Real.sqrt (L : ℝ))) := by ring
  have hbound (z : Site) :
      ‖siteToPlane z - m‖ ^ 2 ≤ 2 * (d z ^ 2 + ‖x₀ - m‖ ^ 2) := by
    have htriangle : ‖siteToPlane z - m‖ ≤ d z + ‖x₀ - m‖ := by
      dsimp [d]
      calc
        ‖siteToPlane z - m‖ =
            ‖(siteToPlane z - x₀) + (x₀ - m)‖ := by congr 1; abel
        _ ≤ ‖siteToPlane z - x₀‖ + ‖x₀ - m‖ := norm_add_le _ _
    have hd : 0 ≤ d z := norm_nonneg _
    have hc : 0 ≤ ‖x₀ - m‖ := norm_nonneg _
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ d z + ‖x₀ - m‖)).2 htriangle
    exact hsq.trans add_sq_le
  have htarget : ∀ z, 0 ≤ ‖siteToPlane z - m‖ ^ 2 * φ z :=
    fun z => mul_nonneg (sq_nonneg _) (hφ z)
  apply Summable.of_nonneg_of_le htarget (fun z => ?_)
    (hquadX.mul_left 2 |>.add (hmass.summable.mul_left (2 * ‖x₀ - m‖ ^ 2)))
  calc
    ‖siteToPlane z - m‖ ^ 2 * φ z ≤
        (2 * (d z ^ 2 + ‖x₀ - m‖ ^ 2)) * φ z :=
      mul_le_mul_of_nonneg_right (hbound z) (hφ z)
    _ = 2 * (d z ^ 2 * φ z) + (2 * ‖x₀ - m‖ ^ 2) * φ z := by ring

private theorem profileSpread_pos_of_two_positive_support
    (φ : Site → ℝ) (A : Finset Site) (hφA : ∀ z ∉ A, φ z = 0)
    (hφ : ∀ z, 0 ≤ φ z)
    {a b : Site} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hφa : 0 < φ a) (hφb : 0 < φ b) : 0 < profileSpread φ := by
  rw [profileSpread_eq_sum_of_support φ A hφA]
  have hsumNonneg : ∀ z ∈ A,
      0 ≤ ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z := by
    intro z hz
    exact mul_nonneg (sq_nonneg _) (hφ z)
  have hsumNonneg' : 0 ≤ ∑ z ∈ A,
      ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z := Finset.sum_nonneg fun z hz => hsumNonneg z hz
  by_contra hnot
  have hzero : (∑ z ∈ A,
      ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z) = 0 := by linarith
  have hterm (z : Site) (hz : z ∈ A) :
      ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z = 0 := by
    have hle := Finset.single_le_sum (f := fun z =>
      ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z) (fun w hw => hsumNonneg w hw) hz
    have hle' : ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z ≤
        ∑ w ∈ A, ‖siteToPlane w - profileMean φ‖ ^ 2 * φ w := by
      simpa only [Finset.sum_attach] using hle
    exact le_antisymm (by simpa [hzero] using hle') (hsumNonneg z hz)
  have hmeanA : siteToPlane a = profileMean φ := by
    have := hterm a ha
    have hnorm : ‖siteToPlane a - profileMean φ‖ ^ 2 = 0 :=
      (mul_eq_zero.mp this).resolve_right (ne_of_gt hφa)
    have hnorm0 : ‖siteToPlane a - profileMean φ‖ = 0 := sq_eq_zero_iff.mp hnorm
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  have hmeanB : siteToPlane b = profileMean φ := by
    have := hterm b hb
    have hnorm : ‖siteToPlane b - profileMean φ‖ ^ 2 = 0 :=
      (mul_eq_zero.mp this).resolve_right (ne_of_gt hφb)
    have hnorm0 : ‖siteToPlane b - profileMean φ‖ = 0 := sq_eq_zero_iff.mp hnorm
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  have : siteToPlane a = siteToPlane b := hmeanA.trans hmeanB.symm
  apply hab
  ext i
  have hcoord := congrArg (fun x : Plane => x i) this
  simpa [Critical2DKPZ.siteToPlane] using hcoord

private theorem variance_profileP2Fun_le_four_of_pointwise_le_two
    (β : ℝ) (L : ℕ) (φ ψ : Site → ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (hψ : ∀ z, 0 ≤ ψ z)
    (hmassφ : HasSum φ 1) (hmassψ : HasSum ψ 1)
    (hψφ : ∀ z, ψ z ≤ 2 * φ z) :
    Var[fun ω => profileP2Fun β 0 L ψ (fun _ => 1) ω; disorderLaw] ≤
      4 * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] := by
  let pair (g : Site → ℝ) (m : ℕ) : Site × Site → ℝ := fun p =>
    g p.1 * srwKernel (2 * m) (p.1 - p.2) * g p.2
  have hpairφ (m : ℕ) : Summable (pair φ m) := by
    simpa only [pair] using summable_evenTimeEnergy_terms m φ hφ hmassφ.summable
  have hpairψ (m : ℕ) : Summable (pair ψ m) := by
    simpa only [pair] using summable_evenTimeEnergy_terms m ψ hψ hmassψ.summable
  have hpairle (m : ℕ) (p : Site × Site) : pair ψ m p ≤ 4 * pair φ m p := by
    dsimp [pair]
    have hK := srwKernel_nonneg (2 * m) (p.1 - p.2)
    have hleft := mul_le_mul_of_nonneg_right (hψφ p.1) hK
    have hbase : 0 ≤ 2 * φ p.1 * srwKernel (2 * m) (p.1 - p.2) :=
      mul_nonneg (mul_nonneg (by norm_num) (hφ p.1)) hK
    calc
      ψ p.1 * srwKernel (2 * m) (p.1 - p.2) * ψ p.2 ≤
          (2 * φ p.1 * srwKernel (2 * m) (p.1 - p.2)) * ψ p.2 :=
        mul_le_mul_of_nonneg_right hleft (hψ p.2)
      _ ≤ (2 * φ p.1 * srwKernel (2 * m) (p.1 - p.2)) * (2 * φ p.2) :=
        mul_le_mul_of_nonneg_left (hψφ p.2) hbase
      _ = 4 * (φ p.1 * srwKernel (2 * m) (p.1 - p.2) * φ p.2) := by ring
  have hdouble (m : ℕ) :
      (∑' z, ∑' w, ψ z * srwKernel (2 * m) (z - w) * ψ w) ≤
        4 * (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) := by
    calc
      (∑' z, ∑' w, ψ z * srwKernel (2 * m) (z - w) * ψ w) =
          ∑' p : Site × Site, pair ψ m p := by rw [(hpairψ m).tsum_prod]
      _ ≤ ∑' p : Site × Site, 4 * pair φ m p :=
        (hpairψ m).tsum_le_tsum (hpairle m) ((hpairφ m).mul_left 4)
      _ = 4 * ∑' p : Site × Site, pair φ m p := tsum_mul_left
      _ = 4 * (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) := by
        rw [(hpairφ m).tsum_prod]
  have hσ : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    have he := Real.one_le_exp (sq_nonneg β)
    linarith
  have hF (m : ℕ) : 0 ≤
      Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m) := by
    apply mul_nonneg hσ
    exact integral_nonneg fun ω => sq_nonneg (pointToPlane β 0 (L - m) 0 ω)
  rw [variance_profileP2Fun_eq_sum β L ψ hψ hmassψ.summable,
      variance_profileP2Fun_eq_sum β L φ hφ hmassφ.summable]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 L,
          ((4 * (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w)) *
            Polymer.sigmaSq β) * Renewal.freeSecondMoment β (L - m) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        _ = (∑' z, ∑' w, ψ z * srwKernel (2 * m) (z - w) * ψ w) *
            (Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m)) := by ring
        _ ≤ (4 * (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w)) *
            (Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m)) :=
          mul_le_mul_of_nonneg_right (hdouble m) (hF m)
        _ = ((4 * (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w)) *
            Polymer.sigmaSq β) * Renewal.freeSecondMoment β (L - m) := by ring
    _ = ∑ m ∈ Finset.Icc 1 L, 4 *
          ((∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) *
            (Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m))) := by
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = 4 * ∑ m ∈ Finset.Icc 1 L,
          (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) *
            Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m) := by
      calc
        _ = ∑ m ∈ Finset.Icc 1 L, 4 *
            ((∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) *
              Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m)) := by
          apply Finset.sum_congr rfl
          intro m hm
          ring
        _ = 4 * ∑ m ∈ Finset.Icc 1 L,
            (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) *
              Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m) :=
          (Finset.mul_sum (Finset.Icc 1 L) _ 4).symm

/-- CSZ25 Theorem 1.11: the finite-support CCR estimate extends to every
probability profile by normalized box truncation. -/
theorem genMomentBound_of_ccr (h : ℕ) (hccr : 3 ≤ h → CCRMomentBound h) :
    GenMomentBound h := by
  unfold GenMomentBound
  intro t c₁ c₂ c₃ ht hc₁ hc₂ hc₃
  by_cases hh : 3 ≤ h
  · have hccrH := hccr hh
    let c₁loc : ℝ := 2 * Real.exp (2 * t) * c₁
    let c₂loc : ℝ := 8 * c₂
    let c₃loc : ℝ := 4 * c₃
    have hc₁loc : 0 < c₁loc := by dsimp [c₁loc]; positivity
    have hc₂loc : 0 < c₂loc := by dsimp [c₂loc]; positivity
    have hc₃loc : 0 < c₃loc := by dsimp [c₃loc]; positivity
    obtain ⟨c₂', hc₂', hlogGreen⟩ :=
      log_mul_sq_le_greenEnergy t c₁loc c₂loc ht hc₁loc hc₂loc
    obtain ⟨L₀, C, hfinite⟩ := abs_centeredMoment_le_variance_pow_of_greenEnergy_of_ccr
      hh hccrH t c₁loc c₂' c₃loc ht hc₁loc hc₂' hc₃loc
    let L₀' := max 2 L₀
    refine ⟨L₀', C, fun β hβ L hL φ hφ hmass hlocal hsq hvar => ?_⟩
    have hL₀ : L₀ ≤ L := (le_max_right _ _).trans hL
    have hLtwo : 2 ≤ L := (le_max_left _ _).trans hL
    have hLpos : 0 < L := by omega
    obtain ⟨x₀, hweight, hweightBound⟩ := hlocal
    let massn : ℕ → ℝ := fun n => ∑ z ∈ boxSites n, φ z
    have hmassTendsto : Tendsto massn atTop (nhds 1) := by
      change Tendsto (fun n : ℕ => ∑ z ∈ boxSites n, φ z) atTop (𝓝 1)
      exact hmass.comp tendsto_boxSites_atTop
    have hmassHalf : ∀ᶠ n : ℕ in atTop, 1 / 2 < massn n :=
      hmassTendsto.eventually (Ioi_mem_nhds (by norm_num))
    have hsqSummable := summable_sq_probability_profile φ hφ hmass
    have hsqPos : 0 < ∑' z, φ z ^ 2 := by
      have hexists : ∃ z, 0 < φ z := by
        by_contra hnone
        push Not at hnone
        have hzero : ∀ z, φ z = 0 := fun z => le_antisymm (hnone z) (hφ z)
        have htsum : (∑' z, φ z) = 0 := by simp [hzero]
        linarith [hmass.tsum_eq]
      obtain ⟨z, hz⟩ := hexists
      exact hsqSummable.tsum_pos (fun z => sq_nonneg (φ z)) z (sq_pos_of_pos hz)
    have hspreadNonneg := profileSpread_nonneg φ hφ
    have hspreadPos : 0 < profileSpread φ := by
      by_contra hnot
      have hzero : profileSpread φ = 0 := le_antisymm (not_lt.mp hnot) hspreadNonneg
      have hsqZero : (∑' z, φ z ^ 2) ≤ 0 := by
        simpa [hzero] using hsq
      linarith
    have hexists : ∃ a b : Site, a ≠ b ∧ 0 < φ a ∧ 0 < φ b := by
      obtain ⟨a, ha⟩ := (show ∃ z, 0 < φ z from by
        by_contra hnone
        push Not at hnone
        have hzero : ∀ z, φ z = 0 := fun z => le_antisymm (hnone z) (hφ z)
        have htsum : (∑' z, φ z) = 0 := by simp [hzero]
        linarith [hmass.tsum_eq])
      by_contra hnone
      push Not at hnone
      have hsupport : ∀ z ≠ a, φ z = 0 := by
        intro z haz
        by_contra hne
        have hz : 0 < φ z := lt_of_le_of_ne (hφ z) (Ne.symm hne)
        have hzle := hnone a z haz.symm ha
        exact not_lt_of_ge hzle hz
      let A₀ : Finset Site := {a}
      have hφA₀ : ∀ z ∉ A₀, φ z = 0 := by
        intro z hz
        exact hsupport z (by simpa [A₀] using hz)
      have hmassA₀ : ∑ z ∈ A₀, φ z = 1 := by
        have hfiniteSum : HasSum φ (∑ z ∈ A₀, φ z) :=
          hasSum_sum_of_ne_finset_zero (s := A₀) (f := φ) hφA₀
        exact hfiniteSum.unique hmass
      have hspreadZero : profileSpread φ = 0 := by
        rw [profileSpread_eq_sum_of_support φ A₀ hφA₀,
          profileMean_eq_sum_of_support φ A₀ hφA₀]
        have hφaone : φ a = 1 := by simpa [A₀] using hmassA₀
        simp [A₀, hφaone]
      exact (ne_of_gt hspreadPos) hspreadZero
    obtain ⟨a, b, hab, ha, hb⟩ := hexists
    let Aab : Finset Site := {a, b}
    obtain ⟨n₀, hn₀⟩ := exists_boxSites_superset Aab
    have hcontains : ∀ᶠ n : ℕ in atTop, Aab ⊆ boxSites n := by
      filter_upwards [eventually_ge_atTop n₀] with n hn
      exact hn₀.trans (boxSites_mono hn)
    let raw (n : ℕ) : Site → ℝ := (↑(boxSites n) : Set Site).indicator φ
    let ψ (n : ℕ) : Site → ℝ := fun z => raw n z / massn n
    have hrawNonneg (n : ℕ) (z : Site) : 0 ≤ raw n z := by
      by_cases hz : z ∈ boxSites n
      · simp [raw, hz, hφ z]
      · simp [raw, hz]
    have hrawSupport (n : ℕ) : ∀ z ∉ boxSites n, raw n z = 0 := by
      intro z hz
      simp [raw, hz]
    have hrawSum (n : ℕ) : ∑ z ∈ boxSites n, raw n z = massn n := by
      dsimp [massn, raw]
      apply Finset.sum_congr rfl
      intro z hz
      simp [Set.indicator_of_mem, Finset.mem_coe.mpr hz]
    have hψData (n : ℕ) (hmn : 1 / 2 < massn n) :
        (∀ z, 0 ≤ ψ n z) ∧ (∀ z ∉ boxSites n, ψ n z = 0) ∧ HasSum (ψ n) 1 := by
      have hmnpos : 0 < massn n := by linarith
      have hψnonneg : ∀ z, 0 ≤ ψ n z := fun z => div_nonneg (hrawNonneg n z) hmnpos.le
      have hψsupport : ∀ z ∉ boxSites n, ψ n z = 0 := by
        intro z hz
        simp [ψ, hrawSupport n z hz]
      have hψsum : ∑ z ∈ boxSites n, ψ n z = 1 := by
        calc
          _ = (∑ z ∈ boxSites n, raw n z) / massn n := by rw [Finset.sum_div]
          _ = 1 := by rw [hrawSum]; exact div_self (ne_of_gt hmnpos)
      have hψhas : HasSum (ψ n) 1 := by
        have hs : HasSum (ψ n) (∑ z ∈ boxSites n, ψ n z) :=
          hasSum_sum_of_ne_finset_zero (s := boxSites n) (f := ψ n) hψsupport
        rw [hψsum] at hs
        exact hs
      exact ⟨hψnonneg, hψsupport, hψhas⟩
    have hmassLeOne (n : ℕ) : massn n ≤ 1 := by
      have h := hmass.summable.sum_le_tsum (boxSites n) (fun z _ => hφ z)
      simpa only [hmass.tsum_eq, massn] using h
    have hlocalSite (n : ℕ) (hmn : 1 / 2 < massn n) :
        ∃ z₀ : Site, ∑ z ∈ boxSites n, ψ n z * Real.exp
          (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt (L : ℝ)) ≤ c₁loc := by
      let z₀ := Critical2DKPZ.nearestEven x₀
      have hmnpos : 0 < massn n := by linarith
      have hψle : ∀ z, ψ n z ≤ 2 * φ z := by
        intro z
        by_cases hz : z ∈ boxSites n
        · have hraw : raw n z = φ z := by simp [raw, hz]
          simp only [ψ]
          rw [hraw]
          apply (div_le_iff₀ hmnpos).2
          have hfactor : 1 ≤ 2 * massn n := by linarith only [hmn]
          calc
            φ z = φ z * 1 := (mul_one _).symm
            _ ≤ φ z * (2 * massn n) :=
              mul_le_mul_of_nonneg_left hfactor (hφ z)
            _ = 2 * φ z * massn n := by ring
        · simp only [ψ, raw, Set.indicator_of_notMem hz, zero_div]
          exact mul_nonneg (by norm_num) (hφ z)
      have hsub (z : Site) :
          siteToPlane (z - z₀) = siteToPlane z - siteToPlane z₀ := by
        ext i
        simp [Critical2DKPZ.siteToPlane]
      have hdist (z : Site) :
          ‖siteToPlane (z - z₀)‖ ≤ ‖siteToPlane z - x₀‖ + 1 := by
        rw [hsub]
        calc
          ‖siteToPlane z - siteToPlane z₀‖ ≤
              ‖siteToPlane z - x₀‖ + ‖x₀ - siteToPlane z₀‖ := by
            calc
              _ = ‖(siteToPlane z - x₀) + (x₀ - siteToPlane z₀)‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
          _ ≤ ‖siteToPlane z - x₀‖ + 1 := by
            gcongr
            simpa [z₀] using Critical2DKPZ.norm_sub_nearestEven_le_one x₀
      have hroot : 1 ≤ Real.sqrt (L : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        have hLreal : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLtwo
        exact le_trans (by norm_num : (1 : ℝ) ^ 2 ≤ 2) hLreal
      have hpoint (z : Site) :
          ψ n z * Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt (L : ℝ)) ≤
            2 * Real.exp (2 * t) *
              (φ z * Real.exp (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) := by
        have hrootpos : 0 < Real.sqrt (L : ℝ) := by positivity
        have harg : 2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt (L : ℝ) ≤
            2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ) + 2 * t := by
          apply (div_le_iff₀ hrootpos).2
          have hmul := mul_le_mul_of_nonneg_left (hdist z) (by positivity : 0 ≤ 2 * t)
          have hrootmul := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 2 * t)
          calc
            2 * t * ‖siteToPlane (z - z₀)‖ ≤
                2 * t * (‖siteToPlane z - x₀‖ + 1) := hmul
            _ = 2 * t * ‖siteToPlane z - x₀‖ + 2 * t := by ring
            _ ≤ 2 * t * ‖siteToPlane z - x₀‖ + 2 * t * Real.sqrt (L : ℝ) :=
              add_le_add le_rfl (by simpa only [mul_one] using hrootmul)
            _ = (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ) + 2 * t) *
                Real.sqrt (L : ℝ) := by field_simp [ne_of_gt hrootpos]
        have hexp := Real.exp_le_exp.mpr harg
        have hexp' : Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt (L : ℝ)) ≤
            Real.exp (2 * t) * Real.exp
              (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)) := by
          rw [Real.exp_add] at hexp
          simpa [mul_comm] using hexp
        calc
          _ ≤ 2 * φ z * Real.exp
              (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt (L : ℝ)) :=
            mul_le_mul_of_nonneg_right (hψle z) (Real.exp_nonneg _)
          _ ≤ 2 * φ z *
              (Real.exp (2 * t) * Real.exp
                (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hexp'
              (mul_nonneg (by norm_num) (hφ z))
          _ = _ := by ring
      have hfinite : ∑ z ∈ boxSites n,
          ψ n z * Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt (L : ℝ)) ≤
          2 * Real.exp (2 * t) * c₁ := by
        calc
          _ ≤ ∑ z ∈ boxSites n, 2 * Real.exp (2 * t) *
              (φ z * Real.exp
                (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) :=
            Finset.sum_le_sum fun z hz => hpoint z
          _ ≤ 2 * Real.exp (2 * t) * ∑' z, φ z * Real.exp
              (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)) := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left
              (hweight.sum_le_tsum (boxSites n) (fun z _ =>
                mul_nonneg (hφ z) (Real.exp_nonneg _))) (by positivity)
          _ ≤ 2 * Real.exp (2 * t) * c₁ :=
            mul_le_mul_of_nonneg_left hweightBound (by positivity)
      exact ⟨z₀, by simpa [c₁loc] using hfinite⟩
    have hlocalExp (n : ℕ) (hmn : 1 / 2 < massn n) : ExpLocalized t c₁loc L (ψ n) := by
      obtain ⟨z₀, hlocalFin⟩ := hlocalSite n hmn
      have hsub (z : Site) :
          siteToPlane (z - z₀) = siteToPlane z - siteToPlane z₀ := by
        ext i
        simp [Critical2DKPZ.siteToPlane]
      let weight (z : Site) := ψ n z * Real.exp
        (2 * t * ‖siteToPlane z - siteToPlane z₀‖ / Real.sqrt (L : ℝ))
      have hweightSupport : ∀ z ∉ boxSites n, weight z = 0 := by
        intro z hz
        simp [weight, (hψData n hmn).2.1 z hz]
      have hweightsum : HasSum weight (∑ z ∈ boxSites n, weight z) :=
        hasSum_sum_of_ne_finset_zero (s := boxSites n) (f := weight) hweightSupport
      have hsumBound : ∑ z ∈ boxSites n, weight z ≤ c₁loc := by
        simpa [weight, hsub] using hlocalFin
      refine ⟨siteToPlane z₀, ?_, ?_⟩
      · have hEq : (fun z : Site => weight z) = fun z =>
            ψ n z * Real.exp (2 * t * ‖siteToPlane z - siteToPlane z₀‖ /
              Real.sqrt (L : ℝ)) := rfl
        simpa only [hEq] using hweightsum.summable
      · rw [hweightsum.tsum_eq]
        exact hsumBound
    have hspreadQuadraticSummable (n : ℕ) (hmn : 1 / 2 < massn n) :
        Summable (fun z => ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z) :=
      summable_centered_quadratic_of_localization t ht L hLpos φ hφ hmass x₀
        (profileMean φ) hweight
    let α : ℝ := (h : ℝ) / 2
    let Itr (n : ℕ) := ∫ ω, (profileP2Fun β 0 L (raw n) (fun _ => 1) ω -
      ∫ ω', profileP2Fun β 0 L (raw n) (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw
    let Vtr (n : ℕ) := Var[fun ω => profileP2Fun β 0 L (raw n) (fun _ => 1) ω; disorderLaw]
    have htrunc := tendsto_centeredMoment_profileP2Fun_truncate β L h φ hφ hmass.summable
    have hboundEvent : ∀ᶠ n : ℕ in atTop, |Itr n| ≤ C * Vtr n ^ α := by
      filter_upwards [hmassHalf, hcontains] with n hmn hcontainsN
      have hmnpos : 0 < massn n := by linarith
      obtain ⟨hψnonneg, hψsupport, hψmass⟩ := hψData n hmn
      have hψφ : ∀ z, ψ n z ≤ 2 * φ z := by
        intro z
        by_cases hz : z ∈ boxSites n
        · simp only [ψ]
          rw [show raw n z = φ z by simp [raw, hz]]
          apply (div_le_iff₀ hmnpos).2
          have hfactor : 1 ≤ 2 * massn n := by linarith only [hmn]
          calc
            φ z = φ z * 1 := (mul_one _).symm
            _ ≤ φ z * (2 * massn n) :=
              mul_le_mul_of_nonneg_left hfactor (hφ z)
            _ = 2 * φ z * massn n := by ring
        · simp only [ψ, raw, Set.indicator_of_notMem hz, zero_div]
          exact mul_nonneg (by norm_num) (hφ z)
      have haIn : a ∈ boxSites n := hcontainsN (by simp [Aab])
      have hbIn : b ∈ boxSites n := hcontainsN (by simp [Aab])
      have hψspreadPos : 0 < profileSpread (ψ n) := by
        apply profileSpread_pos_of_two_positive_support (ψ n) (boxSites n) hψsupport
          hψnonneg
        · exact haIn
        · exact hbIn
        · exact hab
        · simp only [ψ]
          rw [show raw n a = φ a by simp [raw, haIn]]
          exact div_pos ha hmnpos
        · simp only [ψ]
          rw [show raw n b = φ b by simp [raw, hbIn]]
          exact div_pos hb hmnpos
      have hquad := hspreadQuadraticSummable n hmn
      have hmassRecip : 1 / massn n ≤ 2 := by
        apply (div_le_iff₀ hmnpos).2
        linarith only [hmn]
      have hψquadratic :
          ∑ z ∈ boxSites n, ‖siteToPlane z - profileMean φ‖ ^ 2 * ψ n z ≤
            2 * profileSpread φ := by
        have hsumIdent :
            ∑ z ∈ boxSites n, ‖siteToPlane z - profileMean φ‖ ^ 2 * ψ n z =
              (∑ z ∈ boxSites n,
                ‖siteToPlane z - profileMean φ‖ ^ 2 * raw n z) / massn n := by
          calc
            _ = ∑ z ∈ boxSites n,
                (‖siteToPlane z - profileMean φ‖ ^ 2 * raw n z) / massn n := by
              apply Finset.sum_congr rfl
              intro z hz
              simp only [ψ]
              ring
            _ = _ := by rw [Finset.sum_div]
        have hsumLe :
            ∑ z ∈ boxSites n,
              ‖siteToPlane z - profileMean φ‖ ^ 2 * raw n z ≤ profileSpread φ := by
          calc
            _ = ∑ z ∈ boxSites n,
                ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z := by
              apply Finset.sum_congr rfl
              intro z hz
              simp [raw, hz]
            _ ≤ ∑' z, ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z :=
              hquad.sum_le_tsum (boxSites n) (fun z _ => mul_nonneg (sq_nonneg _) (hφ z))
            _ = profileSpread φ := by rfl
        have hfactor : 1 ≤ 2 * massn n := by linarith only [hmn]
        have hDfactor : profileSpread φ ≤
            2 * profileSpread φ * massn n := by
          calc
            profileSpread φ = profileSpread φ * 1 := (mul_one _).symm
            _ ≤ profileSpread φ * (2 * massn n) :=
              mul_le_mul_of_nonneg_left hfactor hspreadNonneg
            _ = 2 * profileSpread φ * massn n := by ring
        rw [hsumIdent]
        apply (div_le_iff₀ hmnpos).2
        exact hsumLe.trans hDfactor
      have hψmassFin : ∑ z ∈ boxSites n, ψ n z = 1 := by
        have hs : HasSum (ψ n) (∑ z ∈ boxSites n, ψ n z) :=
          hasSum_sum_of_ne_finset_zero (s := boxSites n) (f := ψ n) hψsupport
        exact hs.unique hψmass
      have hψspreadUpper : profileSpread (ψ n) ≤ 2 * profileSpread φ := by
        calc
          profileSpread (ψ n) ≤
              ∑ z ∈ boxSites n, ‖siteToPlane z - profileMean φ‖ ^ 2 * ψ n z :=
            profileSpread_le_quadratic_about_of_support (ψ n) (boxSites n)
              hψsupport hψmassFin (profileMean φ)
          _ ≤ 2 * profileSpread φ := hψquadratic
      have hψsumSq : ∑' z, ψ n z ^ 2 ≤ 8 * c₂ / profileSpread (ψ n) := by
        have hfiniteSq : ∑' z, ψ n z ^ 2 =
            (∑ z ∈ boxSites n, raw n z ^ 2) / massn n ^ 2 := by
          rw [tsum_eq_sum (fun z hz => by simp [hψsupport z hz])]
          calc
            _ = ∑ z ∈ boxSites n, raw n z ^ 2 / massn n ^ 2 := by
              apply Finset.sum_congr rfl
              intro z hz
              simp only [ψ]
              ring
            _ = _ := by rw [Finset.sum_div]
        have htruncSq : ∑ z ∈ boxSites n, raw n z ^ 2 ≤ ∑' z, φ z ^ 2 := by
          calc
            _ = ∑ z ∈ boxSites n, φ z ^ 2 := by
              apply Finset.sum_congr rfl
              intro z hz
              simp [raw, hz]
            _ ≤ _ := hsqSummable.sum_le_tsum _ (fun z _ => sq_nonneg _)
        have hrecipSq : 1 / massn n ^ 2 ≤ 4 := by
          simpa only [div_pow, one_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
            pow_le_pow_left₀ (by positivity : 0 ≤ 1 / massn n) hmassRecip 2
        have hsumFour : ∑' z, ψ n z ^ 2 ≤ 4 * (∑' z, φ z ^ 2) := by
          rw [hfiniteSq]
          have hrawSqNonneg : 0 ≤ ∑ z ∈ boxSites n, raw n z ^ 2 :=
            Finset.sum_nonneg fun z _ => sq_nonneg _
          calc
            _ = (1 / massn n ^ 2) *
                (∑ z ∈ boxSites n, raw n z ^ 2) := by ring
            _ ≤ 4 * ∑ z ∈ boxSites n, raw n z ^ 2 :=
              mul_le_mul_of_nonneg_right hrecipSq hrawSqNonneg
            _ ≤ 4 * ∑' z, φ z ^ 2 := mul_le_mul_of_nonneg_left htruncSq (by norm_num)
        have hfromOriginal :
            4 * (∑' z, φ z ^ 2) ≤ 4 * (c₂ / profileSpread φ) :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
        have htransfer : 4 * (c₂ / profileSpread φ) ≤
            8 * c₂ / profileSpread (ψ n) := by
          have hcross := mul_le_mul_of_nonneg_left hψspreadUpper (by positivity : 0 ≤ 4 * c₂)
          have hcross' : 4 * c₂ * profileSpread (ψ n) ≤
              8 * c₂ * profileSpread φ := by
            calc
              4 * c₂ * profileSpread (ψ n) ≤
                  4 * c₂ * (2 * profileSpread φ) := hcross
              _ = 8 * c₂ * profileSpread φ := by ring
          have hdiv : (4 * c₂) / profileSpread φ ≤
              (8 * c₂) / profileSpread (ψ n) :=
            (div_le_div_iff₀ hspreadPos hψspreadPos).2 hcross'
          calc
            4 * (c₂ / profileSpread φ) = (4 * c₂) / profileSpread φ := by ring
            _ ≤ (8 * c₂) / profileSpread (ψ n) := hdiv
            _ = 8 * c₂ / profileSpread (ψ n) := rfl
        exact hsumFour.trans (hfromOriginal.trans htransfer)
      obtain ⟨z₀, hlocalBoundN⟩ := hlocalSite n hmn
      have hgreen := hlogGreen L hLtwo (ψ n) hψnonneg hψmass
        (hlocalExp n hmn) hψsumSq
      have hgreenFinite : Real.log ((L : ℝ) *
          ∑ z ∈ boxSites n, ψ n z ^ 2) ≤ c₂' * greenEnergy L (ψ n) := by
        have hsqEq : ∑' z, ψ n z ^ 2 = ∑ z ∈ boxSites n, ψ n z ^ 2 :=
          tsum_eq_sum (fun z hz => by simp [hψsupport z hz])
        simpa only [← hsqEq] using hgreen
      have hvarψ : Var[fun ω => profileP2Fun β 0 L (ψ n) (fun _ => 1) ω;
          disorderLaw] ≤ c₃loc := by
        have hle := variance_profileP2Fun_le_four_of_pointwise_le_two β L φ (ψ n)
          hφ hψnonneg hmass hψmass hψφ
        exact hle.trans (by
          dsimp [c₃loc]
          exact mul_le_mul_of_nonneg_left hvar (by norm_num))
      have hfiniteBound := hfinite β L hL₀ (ψ n) (boxSites n) hψnonneg hψsupport
        hψmass ⟨z₀, hlocalBoundN⟩ hgreenFinite hvarψ
      have hFraw (ω : Disorder) :
          profileP2Fun β 0 L (raw n) (fun _ => 1) ω =
            massn n * profileP2Fun β 0 L (ψ n) (fun _ => 1) ω := by
        rw [Polymer.profileP2Fun_eq_sum β 0 L (raw n) (fun _ => 1)
          (boxSites n) (hrawSupport n) ω,
          Polymer.profileP2Fun_eq_sum β 0 L (ψ n) (fun _ => 1)
          (boxSites n) hψsupport ω]
        calc
          _ = ∑ z ∈ boxSites n, massn n *
              (ψ n z * ∑' w, pointToPoint β 0 (L - 0) z w ω * (1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro z hz
            simp only [ψ]
            have hraw : raw n z = φ z := by simp [raw, hz]
            rw [hraw]
            field_simp [ne_of_gt hmnpos]
          _ = _ := by rw [Finset.mul_sum]
      let G : Disorder → ℝ := profileP2Fun β 0 L (ψ n) (fun _ => 1)
      let F : Disorder → ℝ := profileP2Fun β 0 L (raw n) (fun _ => 1)
      have hFfun : F = fun ω => massn n * G ω := by
        funext ω
        exact hFraw ω
      have hmeanScale : (∫ ω, F ω ∂disorderLaw) =
          massn n * ∫ ω, G ω ∂disorderLaw := by
        rw [hFfun, integral_const_mul]
      have hcenterScale (ω : Disorder) :
          F ω - ∫ ω', F ω' ∂disorderLaw =
            massn n * (G ω - ∫ ω', G ω' ∂disorderLaw) := by
        calc
          F ω - ∫ ω', F ω' ∂disorderLaw =
              massn n * G ω - ∫ ω', F ω' ∂disorderLaw := by
                rw [show F ω = massn n * G ω by exact congrFun hFfun ω]
          _ = massn n * G ω - massn n * ∫ ω', G ω' ∂disorderLaw := by
                rw [hmeanScale]
          _ = massn n * (G ω - ∫ ω', G ω' ∂disorderLaw) := by ring
      have hmomentScale : Itr n = massn n ^ h *
          (∫ ω, (G ω - ∫ ω', G ω' ∂disorderLaw) ^ h ∂disorderLaw) := by
        rw [show Itr n = ∫ ω, (F ω - ∫ ω', F ω' ∂disorderLaw) ^ h ∂disorderLaw by rfl]
        rw [show (fun ω => (F ω - ∫ ω', F ω' ∂disorderLaw) ^ h) =
            fun ω => massn n ^ h * (G ω - ∫ ω', G ω' ∂disorderLaw) ^ h by
          funext ω
          rw [hcenterScale, mul_pow]]
        rw [integral_const_mul]
      have hvarScale : Vtr n = massn n ^ 2 *
          Var[fun ω => G ω; disorderLaw] := by
        rw [show Vtr n = Var[fun ω => F ω; disorderLaw] by rfl, hFfun, variance_const_mul]
      have hvarψNonneg := variance_nonneg (fun ω : Disorder => G ω) disorderLaw
      have hmnNonneg : 0 ≤ massn n := by linarith
      have hpow : (massn n ^ 2) ^ α = massn n ^ h := by
        calc
          (massn n ^ 2) ^ α = massn n ^ ((2 : ℕ) * α) :=
            (Real.rpow_natCast_mul hmnNonneg 2 α).symm
          _ = massn n ^ (h : ℝ) := by
            congr 1
            dsimp [α]
            ring
          _ = massn n ^ h := Real.rpow_natCast _ _
      have hmomentRawBound : |Itr n| ≤ C * Vtr n ^ α := by
        calc
          |Itr n| = |massn n ^ h *
              (∫ ω, (G ω - ∫ ω', G ω' ∂disorderLaw) ^ h ∂disorderLaw)| := by
            rw [hmomentScale]
          _ = massn n ^ h *
              |∫ ω, (G ω - ∫ ω', G ω' ∂disorderLaw) ^ h ∂disorderLaw| := by
            rw [abs_mul, abs_of_nonneg (pow_nonneg hmnNonneg h)]
          _ ≤ massn n ^ h *
              (C * Var[fun ω => G ω; disorderLaw] ^ α) :=
            mul_le_mul_of_nonneg_left hfiniteBound (pow_nonneg hmnNonneg h)
          _ = C * (massn n ^ h * Var[fun ω => G ω; disorderLaw] ^ α) := by ring
          _ = C * ((massn n ^ 2) ^ α * Var[fun ω => G ω; disorderLaw] ^ α) := by rw [hpow]
          _ = C * ((massn n ^ 2 * Var[fun ω => G ω; disorderLaw]) ^ α) := by
            rw [Real.mul_rpow (sq_nonneg _) hvarψNonneg]
          _ = C * Vtr n ^ α := by rw [← hvarScale]
      exact hmomentRawBound
    have hleft : Tendsto (fun n : ℕ => |Itr n|) atTop
        (𝓝 |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw|) := by
      convert continuous_abs.continuousAt.tendsto.comp htrunc.1 using 1
      all_goals rfl
    have hright : Tendsto (fun n : ℕ => C * Vtr n ^ α) atTop
        (𝓝 (C * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ α)) := by
      have hpowTendsto : Tendsto (fun n : ℕ => Vtr n ^ α) atTop
          (𝓝 (Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ α)) := by
        exact (Real.continuous_rpow_const (by dsimp [α]; positivity)).continuousAt.tendsto.comp htrunc.2
      simpa only [Vtr, raw] using tendsto_const_nhds.mul hpowTendsto
    exact le_of_tendsto_of_tendsto hleft hright hboundEvent
  · have hh₂ : h ≤ 2 := by omega
    refine ⟨0, 1, ?_⟩
    intro β hβ L hL φ hφ hmass hlocal hsq hvar
    simpa using abs_centeredMoment_le_variance_pow_of_le_two hh₂ β L φ hφ hmass

end Critical2DKPZ.MomentBounds
