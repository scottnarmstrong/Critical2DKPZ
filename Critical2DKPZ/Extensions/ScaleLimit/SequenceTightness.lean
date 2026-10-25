/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.ModulusTightness
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-! # From an eventual modulus to tightness along sequences

Each individual path law has a modulus in probability by compact approximation.
Finitely many early indices can therefore be absorbed by decreasing the modulus
scale; no uniform bound over a whole real-parameter tail is asserted.
-/

@[expose] public section
noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped NNReal ENNReal Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Every Borel probability law on continuous paths has a modulus in probability. -/
theorem exists_modulus_bound (S : ℝ≥0) (μ : ProbabilityMeasure (ScalePath S))
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ),
      (μ : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} ≤ ENNReal.ofReal ε := by
  have htight : IsTightMeasureSet {(μ : Measure (ScalePath S))} := isTightMeasureSet_singleton
  obtain ⟨K, hK, htail⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    htight (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  let inst : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : K × ScaleInterval S => p.1.val p.2) := by fun_prop
  obtain ⟨δ, hδ, hctrl⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hc) η hη
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  apply (measure_mono (show {f : ScalePath S | ∃ s r : ScaleInterval S,
      dist (s : ℝ) (r : ℝ) ≤ δ / 2 ∧ η < |f s - f r|} ⊆ Kᶜ from ?_)).trans
    (htail _ (Set.mem_singleton _))
  rintro f ⟨s, r, hsr, hv⟩ hf
  change dist s r ≤ δ / 2 at hsr
  have hd : dist ((⟨f, hf⟩ : K), s) ((⟨f, hf⟩ : K), r) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist s r)] using
      hsr.trans_lt (half_lt_self hδ)
  have hh := hctrl hd
  change |f s - f r| < η at hh
  exact (not_lt_of_ge hh.le) hv

/-- An eventual modulus for a sequence of continuous-path laws extends to every index. -/
theorem uniform_modulus_of_eventual {S : ℝ≥0} (μ : ℕ → ProbabilityMeasure (ScalePath S))
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hev : ∃ δ > (0 : ℝ), ∀ᶠ n in atTop,
      (μ n : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} ≤ ENNReal.ofReal ε) :
    ∃ δ > (0 : ℝ), ∀ n,
      (μ n : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} ≤ ENNReal.ofReal ε := by
  have hmono (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
      (μ n : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ a ∧ η < |f s - f r|} ≤
      (μ n : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ b ∧ η < |f s - f r|} := by
    apply measure_mono
    rintro f ⟨s, r, hsr, hv⟩
    exact ⟨s, r, hsr.trans hab, hv⟩
  have hprefix : ∀ N : ℕ, ∃ δ > (0 : ℝ), ∀ n ≤ N,
      (μ n : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} ≤ ENNReal.ofReal ε := by
    intro N
    induction N with
    | zero =>
      obtain ⟨δ, hδ, hb⟩ := exists_modulus_bound S (μ 0) hη hε
      exact ⟨δ, hδ, fun n hn => by simpa only [Nat.le_zero.mp hn] using hb⟩
    | succ N ih =>
      obtain ⟨a, ha, hbound⟩ := ih
      obtain ⟨b, hb, hlast⟩ := exists_modulus_bound S (μ (N+1)) hη hε
      refine ⟨min a b, lt_min ha hb, ?_⟩
      intro n hn
      rcases Nat.eq_or_lt_of_le hn with rfl | hn'
      · exact (hmono _ (min_le_right _ _)).trans hlast
      · exact (hmono _ (min_le_left _ _)).trans (hbound n (Nat.le_of_lt_succ hn'))
  obtain ⟨a, ha, htail⟩ := hev
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  obtain ⟨b, hb, hpre⟩ := hprefix N
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hmono _ (min_le_left _ _)).trans (hN n hn)
  · exact (hmono _ (min_le_right _ _)).trans (hpre n (le_of_not_ge hn))

/-- A sequence is tight under tight initial values and an eventual modulus. -/
theorem isTightMeasureSet_of_eventual_modulus {S : ℝ≥0}
    (μ : ℕ → ProbabilityMeasure (ScalePath S))
    (h0 : ∀ ε > (0 : ℝ), ∃ M : ℝ, ∀ n,
      (μ n : Measure (ScalePath S)) {f | M < |f ⟨0, by simp⟩|} ≤ ENNReal.ofReal ε)
    (hmod : ∀ η > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ᶠ n in atTop,
      (μ n : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} ≤ ENNReal.ofReal ε) :
    IsTightMeasureSet (Set.range (fun n => (μ n : Measure (ScalePath S)))) :=
  isTightMeasureSet_of_modulus μ h0 (fun η hη ε hε =>
    uniform_modulus_of_eventual μ hη hε (hmod η hη ε hε))

end Critical2DKPZ.Extensions.ScaleLimit
