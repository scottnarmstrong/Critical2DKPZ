/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.LowReplicaLongWordLimits
public import Critical2DKPZ.SHF.Moments.LongWordLimitCellLimit
public import Critical2DKPZ.SHF.Moments.LongWordLimitCellBounds
import Critical2DKPZ.SHF.Moments.TimeRounding
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

/-! # From moving-start terminal limits to tested long-word limits

Potential domination and moving-start terminal-test convergence imply convergence against compactly supported initial-terminal pair tests. -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- Potential domination and moving-start terminal-test limits imply the tested limits for collision words of length at least two. -/
theorem longWordLimits_of_moving_terminal_limits (ϑ : ℝ) {h : ℕ}
    (hD : WordPotentialDomination ϑ h)
    (hterminal : ∀ (w : List (CollisionPair h)), w.IsChain (· ≠ ·) →
      ∀ {τ : ℝ}, 0 < τ → ∀ (nN : ℕ → ℕ),
      Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ) →
      ∀ (xN : ℕ → Fin h → Site) (x : Configuration h),
      (∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i))) →
      (∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ))) →
      (∀ α ∈ w.head?, x α.1.1 ≠ x α.1.2) → ∀ (ψ : Fin h → C_c(Plane, ℝ)),
      Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N) (xN N)
        (fun y => ∏ i, ψ i (y i))) atTop
        (𝓝 (∫ y : Configuration h, (∏ i, ψ i (y i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) w τ x y).toReal))) :
    LongWordLimits ϑ h := by
  intro s t hs hst sN tN hsN htN hsN0 φ m w
  let W := List.ofFn w.1
  have hWne : W ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [W, List.length_ofFn, List.length_nil] at hh
    omega
  obtain ⟨α, v, hW⟩ := List.exists_cons_of_ne_nil hWne
  have hchain : (α :: v).IsChain (· ≠ ·) := by
    rw [← hW]
    apply List.isChain_ofFn.mpr
    intro i hi
    exact w.2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  let nN (N : ℕ) := evenCeil (N * tN N) - evenCeil (N * sN N)
  have hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 (t - s)) :=
    tendsto_evenCeil_moving_gap_div sN tN hsN htN hs hsN0 hst
  have ht : 0 < t - s := sub_pos.mpr hst
  have heven (N : ℕ) : Even (nN N) :=
    (evenCeil_even (N * tN N)).tsub (evenCeil_even (N * sN N))
  let F (x : Configuration h) := ∫ y : Configuration h, (∏ i, φ i (x i, y i)) *
    (diagramKernel (ϑ - Real.eulerMascheroniConstant) (α :: v) (t - s) x y).toReal
  have hpoint : ∀ᵐ x : Configuration h,
      Tendsto (fun N => wordCellInitialAction ϑ N (nN N) φ (α :: v) x) atTop (𝓝 (F x)) := by
    filter_upwards [ae_configuration_pair_ne α] with x hx
    apply tendsto_wordCellInitialAction_of_terminal_limit ϑ hD α v hchain ht nN hn heven x hx φ (F x)
    have hp (i : Fin h) : ∀ᶠ N : ℕ in atTop,
        Even (latticePoint N (x i) 0 + latticePoint N (x i) 1 + (nN N : ℤ)) :=
      Filter.Eventually.of_forall fun N =>
        (latticePoint_mem_evenLattice N (x i)).add (by exact_mod_cast heven N)
    have hsep : ∀ β ∈ (α :: v).head?, x β.1.1 ≠ x β.1.2 := by
      intro β hβ
      have hb : α = β := by simpa only [List.head?_cons, Option.mem_some_iff] using hβ
      simpa only [← hb] using hx
    simpa only [terminalSectionTest_apply] using
      hterminal (α :: v) hchain ht nN hn (fun N i => latticePoint N (x i)) x
        (fun i => tendsto_cellSample (x i)) hp hsep (fun i => terminalSectionTest (φ i) (x i))
  obtain ⟨B, hB, hbound⟩ := eventually_wordCellInitialAction_integrable_bound ϑ hD
    (show 0 < t - s + 1 by linarith only [ht]) α v hchain φ
  have hclock : ∀ᶠ N : ℕ in atTop, (nN N : ℝ) ≤ (t - s + 1) * N := by
    filter_upwards [hn.eventually (Iio_mem_nhds (show t - s < t - s + 1 by linarith)),
      eventually_gt_atTop 0] with N htime hN
    exact (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mp htime.le
  have hlim : Tendsto (fun N => ∫ x : Configuration h,
      wordCellInitialAction ϑ N (nN N) φ (α :: v) x) atTop (𝓝 (∫ x, F x)) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact (integrable_integral_wordCellInitialAction ϑ hN (sN N) (tN N) φ (α :: v)).1.aestronglyMeasurable
    · filter_upwards [hbound, hclock] with N hboundN hnN
      simpa only [Real.norm_eq_abs] using hboundN (nN N) hnN
    · exact hB
    · exact hpoint
  have heq : (fun N => testedBlockWord ϑ N (sN N) (tN N) φ (α :: v)) =ᶠ[atTop]
      (fun N => ∫ x : Configuration h, wordCellInitialAction ϑ N (nN N) φ (α :: v) x) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integrable_integral_wordCellInitialAction ϑ hN (sN N) (tN N) φ (α :: v)).2.symm
  change Tendsto (fun N => testedBlockWord ϑ N (sN N) (tN N) φ W) atTop
    (𝓝 (∫ x : Configuration h, ∫ y : Configuration h, (∏ i, φ i (x i, y i)) *
      (diagramKernel (ϑ - Real.eulerMascheroniConstant) W (t - s) x y).toReal))
  rw [hW]
  exact hlim.congr' heq.symm

end Critical2DKPZ.SHF.Moments
