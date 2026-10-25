/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordContinuumCutoffApproximation
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialIntegral
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitTimeWindow
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitTimeRepresentation
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFunctionalAlgebra
public import Critical2DKPZ.SHF.Moments.WordLimitFirstBlock
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitDiagonal
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic

/-! # Removing first-letter space and time cutoffs

Convergence for shorter words, vanishing time-boundary errors, spatial tightness and the continuum action identity imply convergence of the full first-letter action. -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments



/-- A continuous time cutoff that vanishes up to `η` and is one from `2η`.
Using this transition avoids any convention about the boundary of a time cell. -/
def wordConsTimeCutoff (η t : ℝ) : ℝ := max 0 (min 1 ((t - η) / η))

theorem continuous_wordConsTimeCutoff (η : ℝ) : Continuous (wordConsTimeCutoff η) := by
  unfold wordConsTimeCutoff
  fun_prop

theorem wordConsTimeCutoff_mem_Icc (η t : ℝ) :
    0 ≤ wordConsTimeCutoff η t ∧ wordConsTimeCutoff η t ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem wordConsTimeCutoff_eq_zero {η t : ℝ} (hη : 0 < η) (ht : t ≤ η) :
    wordConsTimeCutoff η t = 0 := by
  unfold wordConsTimeCutoff
  exact max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ht) hη.le))

theorem wordConsTimeCutoff_eq_one {η t : ℝ} (hη : 0 < η) (ht : 2 * η ≤ t) :
    wordConsTimeCutoff η t = 1 := by
  have he : 1 ≤ (t - η) / η := (le_div_iff₀ hη).mpr (by linarith only [ht])
  simp only [wordConsTimeCutoff, min_eq_left he, max_eq_right zero_le_one]


/-- The product time cutoff uses the entrance, run and remaining durations. -/
def wordConsTimeWeight (η a b c : ℝ) : ℝ :=
  wordConsTimeCutoff η a * wordConsTimeCutoff η b * wordConsTimeCutoff η c

theorem wordConsTimeWeight_mem_Icc (η a b c : ℝ) :
    0 ≤ wordConsTimeWeight η a b c ∧ wordConsTimeWeight η a b c ≤ 1 := by
  dsimp only [wordConsTimeWeight]
  obtain ⟨ha, ha'⟩ := wordConsTimeCutoff_mem_Icc η a
  obtain ⟨hb, hb'⟩ := wordConsTimeCutoff_mem_Icc η b
  obtain ⟨hc, hc'⟩ := wordConsTimeCutoff_mem_Icc η c
  refine ⟨mul_nonneg (mul_nonneg ha hb) hc, ?_⟩
  have hab : wordConsTimeCutoff η a * wordConsTimeCutoff η b ≤ 1 := by
    simpa only [mul_one] using mul_le_mul ha' hb' hb zero_le_one
  simpa only [mul_one] using mul_le_mul hab hc' hc zero_le_one

theorem wordConsTimeWeight_eq_one {η a b c : ℝ} (hη : 0 < η)
    (ha : 2 * η ≤ a) (hb : 2 * η ≤ b) (hc : 2 * η ≤ c) :
    wordConsTimeWeight η a b c = 1 := by
  simp only [wordConsTimeWeight, wordConsTimeCutoff_eq_one hη ha,
    wordConsTimeCutoff_eq_one hη hb, wordConsTimeCutoff_eq_one hη hc, mul_one]

theorem wordConsTimeWeight_ne_zero {η a b c : ℝ} (hη : 0 < η)
    (hw : wordConsTimeWeight η a b c ≠ 0) : η < a ∧ η < b ∧ η < c := by
  have hz : wordConsTimeCutoff η a ≠ 0 ∧ wordConsTimeCutoff η b ≠ 0 ∧
      wordConsTimeCutoff η c ≠ 0 := by
    simpa only [wordConsTimeWeight, mul_ne_zero_iff, and_assoc] using hw
  exact ⟨lt_of_not_ge (fun h => hz.1 (wordConsTimeCutoff_eq_zero hη h)),
    lt_of_not_ge (fun h => hz.2.1 (wordConsTimeCutoff_eq_zero hη h)),
    lt_of_not_ge (fun h => hz.2.2 (wordConsTimeCutoff_eq_zero hη h))⟩

theorem tendsto_wordConsTimeWeight_clocks {τ η s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hsr : s + r < τ)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ)) :
    Tendsto (fun N => wordConsTimeWeight η
      ((wordEntranceClock N s : ℝ) / N) ((⌊(N : ℝ) * r⌋₊ : ℝ) / N)
      ((wordRemainingClock N (nN N) s r : ℝ) / N)) atTop
        (𝓝 (wordConsTimeWeight η s r (τ - s - r))) := by
  exact (((continuous_wordConsTimeCutoff η).tendsto s |>.comp
    (tendsto_wordEntranceClock_scaled hs)).mul
      ((continuous_wordConsTimeCutoff η).tendsto r |>.comp
        (tendsto_wordRunClock_scaled hr))).mul
      ((continuous_wordConsTimeCutoff η).tendsto (τ - s - r) |>.comp
        (wordClocks_interior hs hr hsr nN hn).2)

/-- The smooth time-boundary error is dominated by the sharp boundary
weight at twice the cutoff scale. -/
theorem wordConsTimeWeight_boundary_le {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) (n s r : ℕ) :
    1 - wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
        (((n - s - r : ℕ) : ℝ) / N) ≤
      if (s : ℝ) < (2 * η) * N ∨ (r : ℝ) < (2 * η) * N ∨
        ((n - s - r : ℕ) : ℝ) < (2 * η) * N then 1 else 0 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  split_ifs with hb
  · exact sub_le_self _ (wordConsTimeWeight_mem_Icc η _ _ _).1
  · push Not at hb
    rw [wordConsTimeWeight_eq_one hη
      ((le_div_iff₀ hNr).mpr hb.1) ((le_div_iff₀ hNr).mpr hb.2.1)
      ((le_div_iff₀ hNr).mpr hb.2.2), sub_self]

/-- The smooth time weight is dominated by the sharp interior weight at
its own cutoff scale. -/
theorem wordConsTimeWeight_interior_le {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) (n s r : ℕ) :
    wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
        (((n - s - r : ℕ) : ℝ) / N) ≤
      if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
        η * N ≤ ((n - s - r : ℕ) : ℝ) then 1 else 0 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  split_ifs with hi
  · exact (wordConsTimeWeight_mem_Icc η _ _ _).2
  · have hz : wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
        (((n - s - r : ℕ) : ℝ) / N) = 0 := by
      by_contra hz
      obtain ⟨hs, hr, ht⟩ := wordConsTimeWeight_ne_zero hη hz
      exact hi ⟨((lt_div_iff₀ hNr).mp hs).le,
        ((lt_div_iff₀ hNr).mp hr).le, ((lt_div_iff₀ hNr).mp ht).le⟩
    rw [hz]

/-- A nonzero lattice time cutoff lies in a single fixed interior continuum
window, uniformly over the two cell coordinates. -/
theorem eventually_wordConsTimeWeight_support {τ η : ℝ} (hη : 0 < η)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ)) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℝ × ℝ,
      0 ≤ q.1 → 0 ≤ q.2 → wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ nN N →
      wordConsTimeWeight η ((wordEntranceClock N q.1 : ℝ) / N)
        ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N)
        ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N) ≠ 0 →
      q ∈ wordInteriorTimeWindow τ (η / 2) := by
  have hnear := hn.eventually (Iio_mem_nhds (show τ < τ + η / 4 by linarith only [hη]))
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) / η ≤ N :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hnear, hlarge, eventually_gt_atTop 0] with N hn' hlarge' hN
  intro q hq₁ hq₂ hfit hw
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hηN : 4 ≤ η * (N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hlarge'
  obtain ⟨hs, hr, ht⟩ := wordConsTimeWeight_ne_zero hη hw
  have hs' := (lt_div_iff₀ hNr).mp hs
  have hr' := (lt_div_iff₀ hNr).mp hr
  have ht' := (lt_div_iff₀ hNr).mp ht
  have hn' := (div_lt_iff₀ hNr).mp hn'
  have hslo := Nat.floor_le (show 0 ≤ (N : ℝ) * q.1 by positivity)
  have hrlo := Nat.floor_le (show 0 ≤ (N : ℝ) * q.2 by positivity)
  have hsupper := Nat.lt_floor_add_one ((N : ℝ) * q.1)
  have hrupper := Nat.lt_floor_add_one ((N : ℝ) * q.2)
  have hsub : (wordRemainingClock N (nN N) q.1 q.2 : ℝ) =
      (nN N : ℝ) - (wordEntranceClock N q.1 : ℝ) - (⌊(N : ℝ) * q.2⌋₊ : ℝ) := by
    rw [wordRemainingClock, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  rw [hsub] at ht'
  simp only [wordEntranceClock, Nat.cast_add, Nat.cast_one] at hs' ht'
  change η / 2 ≤ q.1 ∧ η / 2 ≤ q.2 ∧ q.1 + q.2 ≤ τ - η / 2
  refine ⟨?_, ?_, ?_⟩
  · apply (le_of_mul_le_mul_left ?_ hNr)
    nlinarith only [hs', hslo, hηN]
  · apply (le_of_mul_le_mul_left ?_ hNr)
    nlinarith only [hr', hrlo, hηN]
  · apply (le_of_mul_le_mul_left ?_ hNr)
    nlinarith only [hsupper, hrupper, ht', hn', hηN]

/-- The full staircase integral with a continuous three-clock cutoff equals
its integral on a fixed compact interior window. -/
theorem eventually_wordConsTimeWeight_integral_eq {τ η : ℝ} (hη : 0 < η)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (F : ℕ → ℕ → ℕ → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∫ q : ℝ × ℝ,
        if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ nN N then
          wordConsTimeWeight η ((wordEntranceClock N q.1 : ℝ) / N)
            ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N)
            ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N) *
            F N (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) =
      ∫ q in wordInteriorTimeWindow τ (η / 2),
        wordConsTimeWeight η ((wordEntranceClock N q.1 : ℝ) / N)
          ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N)
          ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N) *
          F N (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ := by
  classical
  filter_upwards [eventually_wordConsTimeWeight_support hη nN hn,
    wordClocks_interior_uniform (half_pos hη) nN hn] with N hsupp hclocks
  rw [← integral_indicator (isCompact_wordInteriorTimeWindow τ (half_pos hη)).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ wordInteriorTimeWindow τ (η / 2)
  · rw [Set.indicator_of_mem hq, ite_eq_left]
    exact ⟨(half_pos hη).le.trans hq.1, (half_pos hη).le.trans hq.2.1,
      (hclocks.2 q.1 q.2 hq.1 hq.2.1 hq.2.2).2.2.le⟩
  · rw [Set.indicator_of_notMem hq]
    split_ifs with hguard
    · have hz : wordConsTimeWeight η ((wordEntranceClock N q.1 : ℝ) / N)
          ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N)
          ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N) = 0 := by
        by_contra hz
        exact hq (hsupp q hguard.1 hguard.2.1 hguard.2.2 hz)
      rw [hz, zero_mul]
    · rfl


/-- The clock weight is measurable as a function of its two cell coordinates. -/
theorem measurable_wordConsTimeWeight_clocks (N n : ℕ) (η : ℝ) :
    Measurable (fun q : ℝ × ℝ => wordConsTimeWeight η
      ((wordEntranceClock N q.1 : ℝ) / N) ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N)
      ((wordRemainingClock N n q.1 q.2 : ℝ) / N)) := by
  have hc : Measurable (fun q : ℝ × ℝ =>
      (wordEntranceClock N q.1, ⌊(N : ℝ) * q.2⌋₊)) :=
    (((measurable_const.mul measurable_fst).nat_floor).add_const 1).prodMk
      ((measurable_const.mul measurable_snd).nat_floor)
  simpa only [Function.comp_def, wordRemainingClock] using
    (measurable_of_countable (fun c : ℕ × ℕ =>
      wordConsTimeWeight η ((c.1 : ℝ) / N) ((c.2 : ℝ) / N)
        (((n - c.1 - c.2 : ℕ) : ℝ) / N))).comp hc

/-- Compact time integration also permits the continuous cutoff evaluated at the three lattice clocks. -/
theorem integrable_tendsto_wordFirstLetter_weighted_time_integral_of_tail
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    (ψ : Fin h → C_c(Plane, ℝ))
    (hTail : ∀ {q : ℝ}, 0 < q → ∀ kN : ℕ → ℕ,
      Tendsto (fun N : ℕ => (kN N : ℝ) / N) atTop (𝓝 q) →
      ∀ (yN : ℕ → Fin h → Site) (y : Configuration h),
      (∀ i, Tendsto (fun N => latticeRepresentative N (yN N i)) atTop (𝓝 (y i))) →
      (∀ i, ∀ᶠ N : ℕ in atTop, Even (yN N i 0 + yN N i 1 + (kN N : ℤ))) →
      (∀ β ∈ w.head?, y β.1.1 ≠ y β.1.2) →
      Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (kN N) (yN N)
        (fun z => ∏ i, ψ i (z i))) atTop
        (𝓝 (∫ z : Configuration h, (∏ i, ψ i (z i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) w q y z).toReal)))
    {τ ε R δ η : ℝ} (hε : 0 < ε) (hετ : ε ≤ τ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχR : ∀ p, χ p ≠ 0 → ‖p‖ ≤ R)
    (hχsep : ∀ p, χ p ≠ 0 → ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖)
    (M : ℝ) (hM : 0 ≤ M) (hψ : ∀ y : Configuration h, |∏ i, ψ i (y i)| ≤ M) :
    IntegrableOn (fun q : ℝ × ℝ => wordConsTimeWeight η q.1 q.2 (τ - q.1 - q.2) *
      ∫ p : FusedConfiguration α × FusedConfiguration α,
      wordContinuumFirstLetterSpatialIntegrand (ϑ - Real.eulerMascheroniConstant)
        τ q.1 q.2 α w x (fun y => ∏ i, ψ i (y i)) χ p) (wordInteriorTimeWindow τ ε) ∧
    Tendsto (fun N => ∫ q in wordInteriorTimeWindow τ ε,
      wordConsTimeWeight η ((wordEntranceClock N q.1 : ℝ) / N)
        ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N) ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N) *
      ∫ p : FusedConfiguration α × FusedConfiguration α,
        wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
          (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ p) atTop
      (𝓝 (∫ q in wordInteriorTimeWindow τ ε,
        wordConsTimeWeight η q.1 q.2 (τ - q.1 - q.2) *
        ∫ p : FusedConfiguration α × FusedConfiguration α,
          wordContinuumFirstLetterSpatialIntegrand (ϑ - Real.eulerMascheroniConstant)
            τ q.1 q.2 α w x (fun y => ∏ i, ψ i (y i)) χ p)) := by
  let K := wordInteriorTimeWindow τ ε
  let μ : Measure (ℝ × ℝ) := volume.restrict K
  have hK := isCompact_wordInteriorTimeWindow τ hε
  have : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  let F := fun N (q : ℝ × ℝ) =>
    wordConsTimeWeight η ((wordEntranceClock N q.1 : ℝ) / N)
      ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N) ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N) *
    ∫ p : FusedConfiguration α × FusedConfiguration α,
    wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
      (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ p
  let f := fun q : ℝ × ℝ => wordConsTimeWeight η q.1 q.2 (τ - q.1 - q.2) *
      ∫ p : FusedConfiguration α × FusedConfiguration α,
    wordContinuumFirstLetterSpatialIntegrand (ϑ - Real.eulerMascheroniConstant)
      τ q.1 q.2 α w x (fun y => ∏ i, ψ i (y i)) χ p
  have hmeas (N : ℕ) : AEStronglyMeasurable (F N) μ :=
    (measurable_wordConsTimeWeight_clocks N (nN N) η).aestronglyMeasurable.mul
      (measurable_wordFirstLetterSpatialIntegral_time N (criticalBeta ϑ N) α w (nN N) (xN N)
        (fun y => ∏ i, ψ i (y i)) χ).aestronglyMeasurable
  have hpoint (q : ℝ × ℝ) (hq : q ∈ K) : Tendsto (fun N => F N q) atTop (𝓝 (f q)) := by
    have hs : 0 < q.1 := hε.trans_le hq.1
    have hr : 0 < q.2 := hε.trans_le hq.2.1
    have hsr : q.1 + q.2 < τ := by linarith only [hq.2.2, hε]
    exact (tendsto_wordConsTimeWeight_clocks (η := η) hs hr hsr nN hn).mul
      (integrable_tendsto_integral_wordFirstLetterSpatialIntegrand_of_tail
        ϑ hD α w hw ψ hTail hs hr hsr hR hδ nN hn xN x hx hphase χ hχR hχsep M hM hψ).2.2
  obtain ⟨C, hC, hbound⟩ := eventually_wordFirstLetterSpatialIntegral_timeWindow_bound
    ϑ hD α w hw hε hετ hR hδ nN hn χ hχR hχsep (fun y => ∏ i, ψ i (y i)) M hM hψ
  have hnormpoint (N : ℕ) (q : ℝ × ℝ) :
      ‖F N q‖ ≤ |∫ p : FusedConfiguration α × FusedConfiguration α,
        wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
          (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ p| := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hb := wordConsTimeWeight_mem_Icc η ((wordEntranceClock N q.1 : ℝ) / N)
      ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N) ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N)
    rw [abs_of_nonneg hb.1]
    exact (mul_le_mul_of_nonneg_right hb.2 (abs_nonneg _)).trans_eq (one_mul _)
  have hnorm : ∀ᶠ N : ℕ in atTop, ∀ᵐ q ∂μ, ‖F N q‖ ≤ C := by
    filter_upwards [hbound] with N hb
    filter_upwards [self_mem_ae_restrict hK.measurableSet] with q hq
    exact (hnormpoint N q).trans (hb q hq (xN N)).2
  have hlim : ∀ᵐ q ∂μ, Tendsto (fun N => F N q) atTop (𝓝 (f q)) := by
    filter_upwards [self_mem_ae_restrict hK.measurableSet] with q hq
    exact hpoint q hq
  have hlimitBound : ∀ᵐ q ∂μ, ‖f q‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict hK.measurableSet] with q hq
    apply le_of_tendsto (hpoint q hq).norm
    filter_upwards [hbound] with N hb
    exact (hnormpoint N q).trans (hb q hq (xN N)).2
  refine ⟨(integrable_const C).mono'
    (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim) hlimitBound, ?_⟩
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall hmeas) hnorm (integrable_const C) hlim

/-- Exact time cells and the uniform cutoff support turn the lattice
functional into the compact integral used in dominated convergence. -/
theorem eventually_wordFirstLetterLatticeFunctional_eq_weighted_time_integral
    (hTimeCells : ∀ {N : ℕ} (hN : 0 < N) (n : ℕ) (F : ℕ → ℕ → ℝ),
      Integrable (fun q : ℝ × ℝ =>
        if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
        then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) ∧
      (∫ q : ℝ × ℝ,
        if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
        then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) =
        (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r) / (N : ℝ)^2)
    {h : ℕ} (βN : ℕ → ℝ) (α : CollisionPair h) (w : List (CollisionPair h))
    {τ η : ℝ} (hη : 0 < η) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h)
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (Ψ : Configuration h → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      wordFirstLetterLatticeFunctional N (βN N) α w (nN N) (xN N) Ψ
        (fun s r => wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
          (((nN N - s - r : ℕ) : ℝ) / N)) χ =
      ∫ q in wordInteriorTimeWindow τ (η / 2),
        wordConsTimeWeight η ((wordEntranceClock N q.1 : ℝ) / N)
          ((⌊(N : ℝ) * q.2⌋₊ : ℝ) / N)
          ((wordRemainingClock N (nN N) q.1 q.2 : ℝ) / N) *
          ∫ p : FusedConfiguration α × FusedConfiguration α,
            wordFirstLetterSpatialIntegrand N (βN N) α w (nN N) (wordEntranceClock N q.1)
              ⌊(N : ℝ) * q.2⌋₊ (xN N) Ψ χ p := by
  let F := fun N s r => ∫ p : FusedConfiguration α × FusedConfiguration α,
    wordFirstLetterSpatialIntegrand N (βN N) α w (nN N) s r (xN N) Ψ χ p
  filter_upwards [eventually_gt_atTop 0, eventually_all.mpr hphase,
    eventually_wordConsTimeWeight_integral_eq hη nN hn F] with N hN hp hi
  have ht := wordFirstLetterLatticeFunctional_time_integral_of_timeCells hN (nN N)
    (hTimeCells hN (nN N)) (βN N) α w (xN N) hp Ψ
    (fun s r => wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
      (((nN N - s - r : ℕ) : ℝ) / N)) χ
  exact ht.2.symm.trans hi

/-- The first-letter continuum action before inserting spatial cutoffs. -/
def wordConsContinuumAction {h : ℕ} (θ τ : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (x : Configuration h) (ψ : Fin h → C_c(Plane, ℝ))
    (q : ℝ × ℝ) (p : FusedConfiguration α × FusedConfiguration α) : ℝ :=
  incomingKernel α q.1 p.1 x * collisionKernel α θ q.2 p.1 p.2 *
    (∫ y : Configuration h, (∏ i, ψ i (y i)) *
      (diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y).toReal)

/-- The uncut first-letter action is jointly measurable in time and space. -/
theorem measurable_wordConsContinuumAction {h : ℕ} (θ τ : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (x : Configuration h) (ψ : Fin h → C_c(Plane, ℝ)) :
    Measurable (Function.uncurry (wordConsContinuumAction θ τ α w x ψ)) := by
  let E := FusedConfiguration α × FusedConfiguration α
  have hψ : Continuous (fun y : Configuration h => ∏ i, ψ i (y i)) := by fun_prop
  have hk : Measurable (fun z : ((ℝ × ℝ) × E) × Configuration h =>
      diagramKernel θ w (τ - z.1.1.1 - z.1.1.2) (collisionEmbedding α z.1.2.2) z.2) :=
    measurable_diagramKernel_comp w measurable_const (by fun_prop)
      ((measurable_collisionEmbedding α).comp measurable_fst.snd.snd) measurable_snd
  have hb : Measurable (fun z : ((ℝ × ℝ) × E) × Configuration h =>
      (∏ i, ψ i (z.2 i)) *
        (diagramKernel θ w (τ - z.1.1.1 - z.1.1.2) (collisionEmbedding α z.1.2.2) z.2).toReal) :=
    (hψ.measurable.comp measurable_snd).mul hk.ennreal_toReal
  have ht := (hb.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Configuration h)))).measurable
  have hi : Measurable (fun z : (ℝ × ℝ) × E => incomingKernel α z.1.1 z.2.1 x) :=
    (measurable_incomingKernel α).comp
      (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk measurable_const))
  have hc : Measurable (fun z : (ℝ × ℝ) × E => collisionKernel α θ z.1.2 z.2.1 z.2.2) :=
    (measurable_collisionKernel α).comp
      ((measurable_const.prodMk measurable_fst.snd).prodMk measurable_snd)
  exact (hi.mul hc).mul ht

/-- The action of the absolute-value tensor bounds the absolute value of the signed action. -/
theorem abs_wordConsContinuumAction_le {h : ℕ} (θ τ : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (x : Configuration h) (ψ : Fin h → C_c(Plane, ℝ))
    (q : ℝ × ℝ) (hq₁ : 0 < q.1) (hq₂ : 0 < q.2)
    (p : FusedConfiguration α × FusedConfiguration α) :
    |wordConsContinuumAction θ τ α w x ψ q p| ≤
      wordConsContinuumAction θ τ α w x (fun i => |ψ i|) q p := by
  have hk : 0 ≤ incomingKernel α q.1 p.1 x * collisionKernel α θ q.2 p.1 p.2 :=
    mul_nonneg (incomingKernel_pos α hq₁ p.1 x).le (collisionKernel_pos α θ hq₂ p.1 p.2).le
  dsimp only [wordConsContinuumAction]
  rw [abs_mul, abs_of_nonneg hk]
  apply mul_le_mul_of_nonneg_left _ hk
  convert (abs_integral_le_integral_abs (f := fun y : Configuration h =>
    (∏ i, ψ i (y i)) *
      (diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y).toReal)) using 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [abs_mul, Finset.abs_prod, abs_of_nonneg ENNReal.toReal_nonneg]
  rfl

/-- The continuum action hypothesis for the absolute tensor supplies joint
integrability, including absolute integrability of the signed action. -/
theorem integrable_wordConsContinuumAction_of_absolute_action {h : ℕ} (θ τ : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (x : Configuration h)
    (ψ : Fin h → C_c(Plane, ℝ))
    (hspace : ∀ q ∈ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ},
      Integrable (wordConsContinuumAction θ τ α w x (fun i => |ψ i|) q))
    (htime : IntegrableOn (fun q => ∫ p,
      wordConsContinuumAction θ τ α w x (fun i => |ψ i|) q p)
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}) :
    Integrable (Function.uncurry (wordConsContinuumAction θ τ α w x ψ))
      ((volume.restrict {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}).prod volume) := by
  have : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  have : SigmaFinite (volume : Measure (FusedConfiguration α)) := by infer_instance
  have : SigmaFinite (volume : Measure (FusedConfiguration α × FusedConfiguration α)) := by
    infer_instance
  let D := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
  let μ : Measure (ℝ × ℝ) := volume.restrict D
  have hD : MeasurableSet D := by
    exact ((isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))).measurableSet
  let A := wordConsContinuumAction θ τ α w x (fun i => |ψ i|)
  have hn (q : ℝ × ℝ) (hq : q ∈ D) (p : FusedConfiguration α × FusedConfiguration α) :
      0 ≤ A q p :=
    (abs_nonneg _).trans (abs_wordConsContinuumAction_le θ τ α w x ψ q hq.1 hq.2.1 p)
  have hA : Integrable (Function.uncurry A) (μ.prod volume) := by
    apply (integrable_prod_iff (μ := μ)
      (ν := (volume : Measure (FusedConfiguration α × FusedConfiguration α)))
      (measurable_wordConsContinuumAction θ τ α w x (fun i => |ψ i|)).aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hD] with q hq
      exact hspace q hq
    · apply htime.congr
      filter_upwards [ae_restrict_mem hD] with q hq
      apply integral_congr_ae
      filter_upwards [] with p
      exact (Real.norm_of_nonneg (hn q hq p)).symm
  apply hA.mono' ((measurable_wordConsContinuumAction θ τ α w x ψ).aestronglyMeasurable
    (μ := μ.prod (volume : Measure (FusedConfiguration α × FusedConfiguration α))))
  have hq : ∀ᵐ z : (ℝ × ℝ) × (FusedConfiguration α × FusedConfiguration α) ∂μ.prod volume,
      z.1 ∈ D :=
    (Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := (volume : Measure (FusedConfiguration α × FusedConfiguration α)))).ae
        (ae_restrict_mem hD)
  filter_upwards [hq] with z hz
  exact abs_wordConsContinuumAction_le θ τ α w x ψ z.1 hz.1 hz.2.1 z.2

/-- The two supplied sharp cutoff errors control every larger spatial
cutoff with the smooth time weight. -/
theorem abs_wordTerminalTest_sub_smoothCutoff_le {h N : ℕ} (hN : 0 < N)
    (β : ℝ) (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hΨ : ∀ y, |Ψ y| ≤ M) {η : ℝ} (hη : 0 < η)
    (χ₀ χ : (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (hχ : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hχ₀χ : ∀ p, χ₀ p ≤ χ p)
    (b e : ℝ)
    (hboundary : wordFirstLetterLatticeFunctional N β α w n x (fun _ => M)
      (fun s r => if (s : ℝ) < (2 * η) * N ∨ (r : ℝ) < (2 * η) * N ∨
        ((n - s - r : ℕ) : ℝ) < (2 * η) * N then 1 else 0) (fun _ => 1) ≤ b)
    (hspatial : wordFirstLetterLatticeFunctional N β α w n x (fun _ => M)
      (fun s r => if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
        η * N ≤ ((n - s - r : ℕ) : ℝ) then 1 else 0) (fun p => 1 - χ₀ p) ≤ e) :
    |wordTerminalTest N (sigmaSq β) (α :: w) n x Ψ -
      wordFirstLetterLatticeFunctional N β α w n x Ψ
        (fun s r => wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
          (((n - s - r : ℕ) : ℝ) / N)) χ| ≤ b + e := by
  classical
  let κ := fun s r : ℕ => wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
    (((n - s - r : ℕ) : ℝ) / N)
  let B := fun s r : ℕ => if (s : ℝ) < (2 * η) * N ∨ (r : ℝ) < (2 * η) * N ∨
    ((n - s - r : ℕ) : ℝ) < (2 * η) * N then (1 : ℝ) else 0
  let I := fun s r : ℕ => if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
    η * N ≤ ((n - s - r : ℕ) : ℝ) then (1 : ℝ) else 0
  have hκ (s r : ℕ) : 0 ≤ κ s r ∧ κ s r ≤ 1 := wordConsTimeWeight_mem_Icc η _ _ _
  have hI (s r : ℕ) : 0 ≤ I s r := by dsimp only [I]; split_ifs <;> norm_num
  refine (abs_wordTerminalTest_sub_latticeFunctional_le_const
    N β α w n x Ψ κ χ M hΨ hκ hχ).trans (add_le_add ?_ ?_)
  · exact (wordFirstLetterLatticeFunctional_mono_time N β α w n x (fun _ => M)
      (fun s r => 1 - κ s r) B (fun _ => 1) (fun _ => hM)
      (fun s r => wordConsTimeWeight_boundary_le hN hη n s r)
      (fun _ => zero_le_one)).trans hboundary
  · exact ((wordFirstLetterLatticeFunctional_mono_time N β α w n x (fun _ => M)
      κ I (fun p => 1 - χ p) (fun _ => hM)
      (fun s r => wordConsTimeWeight_interior_le hN hη n s r)
      (fun p => sub_nonneg.mpr (hχ p).2)).trans
      (wordFirstLetterLatticeFunctional_mono_spatial N β α w n x (fun _ => M) I
        (fun p => 1 - χ p) (fun p => 1 - χ₀ p) (fun _ => hM) hI
        (fun p => sub_le_sub_left (hχ₀χ p) 1))).trans hspatial

/-- The maximum of two admissible fused cutoffs is admissible and retains
both lower bounds, using the larger radius and smaller positive separation. -/
theorem exists_wordFusedSpatialCutoff_sup_support {h : ℕ} (α : CollisionPair h)
    (w : List (CollisionPair h)) (χ₀ χ₁ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hs₀ : ∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ₀ p ≠ 0 → ‖p‖ ≤ R ∧
      ∀ β ∈ w.head?, δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖)
    (hs₁ : ∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ₁ p ≠ 0 → ‖p‖ ≤ R ∧
      ∀ β ∈ w.head?, δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) :
    ∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, (χ₀ ⊔ χ₁) p ≠ 0 → ‖p‖ ≤ R ∧
      ∀ β ∈ w.head?, δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖ := by
  obtain ⟨R₀, δ₀, hR₀, hδ₀, hs₀⟩ := hs₀
  obtain ⟨R₁, δ₁, hR₁, hδ₁, hs₁⟩ := hs₁
  refine ⟨max R₀ R₁, min δ₀ δ₁,
    (by simpa only [max_self] using max_le_max hR₀ hR₁), lt_min hδ₀ hδ₁, ?_⟩
  intro p hp
  by_cases h₀ : χ₀ p = 0
  · have h₁ : χ₁ p ≠ 0 := by intro he; simp [h₀, he] at hp
    exact ⟨(hs₁ p h₁).1.trans (le_max_right _ _), fun β hβ =>
      (min_le_right _ _).trans ((hs₁ p h₁).2 β hβ)⟩
  · exact ⟨(hs₀ p h₀).1.trans (le_max_left _ _), fun β hβ =>
      (min_le_left _ _).trans ((hs₀ p h₀).2 β hβ)⟩

/-- The interior spatial error equals the two spatial sums in the cutoff estimate at the lattice representatives. -/
theorem wordFirstLetterLatticeFunctional_interior_error_eq {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) (η : ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ
      (fun s r => if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
        η * N ≤ ((n - s - r : ℕ) : ℝ) then 1 else 0) (fun p => 1 - χ p) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧ η * N ≤ ((n - s - r : ℕ) : ℝ) then
          ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
              wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) *
                (1 - χ ((latticeRepresentative N (u α.1.1),
                  fun i : Spectator α => latticeRepresentative N (u i.1)),
                    (latticeRepresentative N (v α.1.1),
                      fun i : Spectator α => latticeRepresentative N (v i.1))))
        else 0 := by
  classical
  rw [wordFirstLetterLatticeFunctional_eq_tsum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · rw [one_mul]
    apply tsum_congr
    intro u
    apply tsum_congr
    intro v
    dsimp only [wordFusedCoordinateRepresentative, wordFusedSiteProjection]
    ring
  · exact zero_mul _

/-- The shorter-word limit, spatial-cutoff bounds, continuum action identity and time-boundary control imply the first-letter limit, including the zero-run contribution. -/
theorem tendsto_wordTerminalTest_cons_of_cutoff_inputs
    (hTimeCells : ∀ {N : ℕ} (hN : 0 < N) (n : ℕ)
          (F : ℕ → ℕ → ℝ),
      Integrable (fun q : ℝ × ℝ =>
            if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
            then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) ∧
          (∫ q : ℝ × ℝ,
            if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
            then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) =
            (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r) / (N : ℝ)^2)
    (hTimeBoundary : ∀ (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
          (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
          {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
          (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
          (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
          (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
          (hsep : x α.1.1 ≠ x α.1.2)
          (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M),
      ∀ ε > 0, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
            ∀ᶠ N : ℕ in atTop,
              |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
                if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
                    ((nN N - s - r : ℕ) : ℝ) < η * N then
                  ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) (xN N),
                    wordFirstBlockKernel (criticalBeta ϑ N) α s r (xN N) v *
                      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ
                else 0| ≤ ε)
    (hSpatialCutoff : ∀ (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
          (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
          {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
          (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
          (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
          (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
          (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M),
      ∀ ε > 0, ∃ χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
            (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
            (∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ p ≠ 0 →
              ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
                δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) ∧
            ∀ᶠ N : ℕ in atTop,
              |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
                if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
                    η * N ≤ ((nN N - s - r : ℕ) : ℝ) then
                  ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                    (((∏ i, srwKernel s (u i - xN N i)) *
                      collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v) *
                      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ) *
                    (1 - χ ((latticeRepresentative N (u α.1.1),
                               fun i : Spectator α => latticeRepresentative N (u i.1)),
                             (latticeRepresentative N (v α.1.1),
                               fun i : Spectator α => latticeRepresentative N (v i.1))))
                else 0| ≤ ε)
    (hContinuumAction : ∀ (θ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
          (hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (hτ : 0 < τ)
          (x : Configuration h) (hsep : x α.1.1 ≠ x α.1.2)
          (ψ : Fin h → C_c(Plane, ℝ)),
      let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
          let A : (ℝ × ℝ) → (FusedConfiguration α × FusedConfiguration α) → ℝ :=
            fun q p => incomingKernel α q.1 p.1 x * collisionKernel α θ q.2 p.1 p.2 *
              (∫ y : Configuration h, (∏ i, ψ i (y i)) *
                (diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y).toReal)
          Integrable (fun y : Configuration h =>
            (∏ i, ψ i (y i)) * (diagramKernel θ (α :: w) τ x y).toReal) ∧
          (∀ q ∈ D, Integrable (A q)) ∧
          IntegrableOn (fun q => ∫ p, A q p) D ∧
          (∫ y : Configuration h, (∏ i, ψ i (y i)) *
            (diagramKernel θ (α :: w) τ x y).toReal) = ∫ q in D, ∫ p, A q p)
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
    (ψ : Fin h → C_c(Plane, ℝ))
    (hTail : ∀ {q : ℝ}, 0 < q → ∀ kN : ℕ → ℕ,
      Tendsto (fun N : ℕ => (kN N : ℝ) / N) atTop (𝓝 q) →
      ∀ (yN : ℕ → Fin h → Site) (y : Configuration h),
      (∀ i, Tendsto (fun N => latticeRepresentative N (yN N i)) atTop (𝓝 (y i))) →
      (∀ i, ∀ᶠ N : ℕ in atTop, Even (yN N i 0 + yN N i 1 + (kN N : ℤ))) →
      (∀ β ∈ w.head?, y β.1.1 ≠ y β.1.2) →
      Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (kN N) (yN N)
        (fun z => ∏ i, ψ i (z i))) atTop
        (𝓝 (∫ z : Configuration h, (∏ i, ψ i (z i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) w q y z).toReal)))
    {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (hsep : x α.1.1 ≠ x α.1.2) :
    Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) (nN N) (xN N)
      (fun y => ∏ i, ψ i (y i))) atTop
      (𝓝 (∫ y : Configuration h, (∏ i, ψ i (y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) (α :: w) τ x y).toReal)) := by
  classical
  have : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  have : SigmaFinite (volume : Measure (FusedConfiguration α)) := by infer_instance
  have : SigmaFinite (volume : Measure (FusedConfiguration α × FusedConfiguration α)) := by
    infer_instance
  let θ := ϑ - Real.eulerMascheroniConstant
  let D := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
  let μ := (volume.restrict D).prod
    (volume : Measure (FusedConfiguration α × FusedConfiguration α))
  let A := wordConsContinuumAction θ τ α w x ψ
  let F := Function.uncurry A
  let Ψ := fun y : Configuration h => ∏ i, ψ i (y i)
  have hAct := hContinuumAction θ α w hw hτ x hsep ψ
  have hActAbs := hContinuumAction θ α w hw hτ x hsep (fun i => |ψ i|)
  have hF : Integrable F μ := integrable_wordConsContinuumAction_of_absolute_action
    θ τ α w x ψ hActAbs.2.1 hActAbs.2.2.1
  have htarget : (∫ z, F z ∂μ) =
      ∫ y : Configuration h, Ψ y * (diagramKernel θ (α :: w) τ x y).toReal :=
    (integral_prod F hF).trans hAct.2.2.2.symm
  let M := ∏ i, ‖(ψ i).toBoundedContinuousFunction‖
  have hM : 0 ≤ M := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hΨ : ∀ y : Configuration h, |Ψ y| ≤ M := by
    intro y
    dsimp only [Ψ, M]
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
    intro i hi
    simpa only [Real.norm_eq_abs, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
      (ψ i).toBoundedContinuousFunction.norm_coe_le_norm (y i)
  have hconst : ∀ y : Configuration h, |(fun _ => M) y| ≤ M :=
    fun _ => (abs_of_nonneg hM).le
  have hηlim : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  rw [Metric.tendsto_nhds]
  intro ε hε
  let e := ε / 4
  have he : 0 < e := div_pos hε (by norm_num)
  obtain ⟨χ₀, hχ₀, hs₀, k₀, happrox⟩ :=
    exists_wordCons_continuum_cutoff_approximation α w hw hτ F hF e he
  obtain ⟨η₀, hη₀, hboundary⟩ :=
    hTimeBoundary ϑ hD α w hw hτ nN hn xN x hx hsep (fun _ => M) M hM hconst e he
  obtain ⟨k, hk, hsmall⟩ := ((eventually_ge_atTop k₀).and
    (hηlim.eventually (Iio_mem_nhds (lt_min (half_pos hη₀) hτ)))).exists
  let η : ℝ := 1 / ((k : ℝ) + 1)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hητ : η / 2 ≤ τ := by
    have hlt : η < τ := lt_of_lt_of_le hsmall (min_le_right _ _)
    linarith only [hlt, hη]
  have hbd := hboundary (2 * η) (by positivity)
    (by have hlt := lt_of_lt_of_le hsmall (min_le_left _ _); linarith only [hlt])
  obtain ⟨χ₁, hχ₁, hs₁, hsp⟩ :=
    hSpatialCutoff ϑ hD α w hw hτ hη nN hn xN x hx (fun _ => M) M hM hconst e he
  let χ := χ₀ ⊔ χ₁
  have hχ (p) : 0 ≤ χ p ∧ χ p ≤ 1 :=
    ⟨(hχ₀ p).1.trans (le_max_left _ _), max_le (hχ₀ p).2 (hχ₁ p).2⟩
  obtain ⟨R, δ, hR, hδ, hs⟩ := exists_wordFusedSpatialCutoff_sup_support α w χ₀ χ₁ hs₀ hs₁
  have hχR (p) (hp : χ p ≠ 0) : ‖p‖ ≤ R := (hs p hp).1
  have hχsep (p) (hp : χ p ≠ 0) : ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖ := (hs p hp).2
  let L := ∫ q in wordInteriorTimeWindow τ (η / 2),
    wordConsTimeWeight η q.1 q.2 (τ - q.1 - q.2) * ∫ p, χ p * A q p
  have hc : |(∫ z, F z ∂μ) - L| ≤ e := (happrox k hk χ
    (fun p => ⟨le_max_left _ _, (hχ p).2⟩)).2.2
  let T := fun N => wordFirstLetterLatticeFunctional N (criticalBeta ϑ N) α w (nN N)
    (xN N) Ψ (fun s r => wordConsTimeWeight η ((s : ℝ) / N) ((r : ℝ) / N)
      (((nN N - s - r : ℕ) : ℝ) / N)) χ
  have hcompact := (integrable_tendsto_wordFirstLetter_weighted_time_integral_of_tail (η := η)
    ϑ hD α w hw.tail ψ hTail (half_pos hη) hητ hR hδ nN hn xN x hx hphase χ
      hχR hχsep M hM hΨ).2
  have hrepr := eventually_wordFirstLetterLatticeFunctional_eq_weighted_time_integral
    hTimeCells (criticalBeta ϑ) α w hη nN hn xN hphase Ψ χ
  have hT : Tendsto T atTop (𝓝 L) := by
    apply hcompact.congr'
    filter_upwards [hrepr] with N hN
    exact hN.symm
  have hc' : |L - (∫ y : Configuration h, Ψ y * (diagramKernel θ (α :: w) τ x y).toReal)| ≤ e := by
    rw [htarget] at hc
    simpa only [abs_sub_comm] using hc
  have hnear := (Metric.tendsto_nhds.mp hT) e he
  filter_upwards [hbd, hsp, hnear, eventually_gt_atTop 0] with N hb hp ht hN
  have hb' : wordFirstLetterLatticeFunctional N (criticalBeta ϑ N) α w (nN N) (xN N)
      (fun _ => M)
      (fun s r => if (s : ℝ) < (2 * η) * N ∨ (r : ℝ) < (2 * η) * N ∨
        ((nN N - s - r : ℕ) : ℝ) < (2 * η) * N then 1 else 0) (fun _ => 1) ≤ e := by
    rw [wordFirstLetterLatticeFunctional_one_spatial_eq_firstBlock]
    simp only [ite_mul, one_mul, zero_mul]
    exact (le_abs_self _).trans hb
  have hp' : wordFirstLetterLatticeFunctional N (criticalBeta ϑ N) α w (nN N) (xN N)
      (fun _ => M)
      (fun s r => if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
        η * N ≤ ((nN N - s - r : ℕ) : ℝ) then 1 else 0) (fun p => 1 - χ₁ p) ≤ e := by
    rw [wordFirstLetterLatticeFunctional_interior_error_eq]
    exact (le_abs_self _).trans hp
  have hd := abs_wordTerminalTest_sub_smoothCutoff_le hN (criticalBeta ϑ N) α w (nN N)
    (xN N) Ψ M hM hΨ hη χ₁ χ hχ (fun _ => le_max_right _ _) e e hb' hp'
  have heq : e + e + e + e = ε := by dsimp only [e]; ring
  rw [Real.dist_eq] at ht ⊢
  have htri := (abs_sub_le
    (wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) (nN N) (xN N) Ψ) (T N)
    (∫ y : Configuration h, Ψ y * (diagramKernel θ (α :: w) τ x y).toReal)).trans
      (add_le_add (le_refl _) (abs_sub_le (T N) L
        (∫ y : Configuration h, Ψ y * (diagramKernel θ (α :: w) τ x y).toReal)))
  change |wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) (nN N) (xN N) Ψ -
    (∫ y : Configuration h, Ψ y * (diagramKernel θ (α :: w) τ x y).toReal)| < ε
  linarith only [htri, hd, ht, hc', heq]

end Critical2DKPZ.SHF.Moments
