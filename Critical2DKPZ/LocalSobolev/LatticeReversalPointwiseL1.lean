/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeReversalPointwise
public import Critical2DKPZ.LocalSobolev.LatticeReversalTerminalRatio
public import Critical2DKPZ.LocalSobolev.LatticeReversalInitialSlice
public import Critical2DKPZ.Assembly.LatticeCentring
import Mathlib.Tactic

/-! # Pointwise L¹ control at the exact reflected lattice clock -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

/-- At a fixed even clock, the exact-clock forward/reversed log-field error is integrable and
has an L¹ bound consisting of the initial slice, the terminal profile ratio, and centering. -/
theorem integral_abs_kpzLattice_sub_exactReverseField_le (ϑ : ℝ) {N m L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmEven : Even m) (hLEven : Even L) (hmL : m ≤ L)
    (h₀ : Plane →ᵇ ℝ) (x : Plane)
    (hcenter : |kpzLatticeCentring ϑ N ((m : ℝ) / N) -
      ∫ ζ, Real.log (pointToPlane (criticalBeta ϑ N) 0 m 0 ζ) ∂disorderLaw| ≤
        (criticalBeta ϑ N) ^ 2 / 2) :
    Integrable (fun ω => |kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ x
        (PolymerCalculus.reversedDisorder L ω)|) disorderLaw ∧
    (∫ ω, |kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ x
        (PolymerCalculus.reversedDisorder L ω)| ∂disorderLaw) ≤
      |criticalBeta ϑ N| + (criticalBeta ϑ N) ^ 2 +
        Real.sqrt ((criticalBeta ϑ N) ^ 2 + (criticalBeta ϑ N) ^ 4 / 4) := by
  let β : ℝ := criticalBeta ϑ N
  let q : ℕ := L - m
  let x₀ : Site := latticePoint N x
  let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  let ω' : Disorder → Disorder := fun ω =>
    Smoothing.shiftEnvironment q (PolymerCalculus.reversedDisorder L ω)
  let A : Disorder → ℝ := fun ω => β * ω (m, x₀) - β ^ 2 / 2
  let B : Disorder → ℝ := fun ω => Real.log (profileP2Fun β (m - 1) m
    (endpointDist β (m - 1) x₀ (ω' ω)) f (ω' ω)) -
      Real.log (profileP2Fun 0 (m - 1) m
        (endpointDist β (m - 1) x₀ (ω' ω)) f (ω' ω))
  let C : ℝ := (∫ ζ, Real.log (pointToPlane β 0 m 0 ζ) ∂disorderLaw) -
    kpzLatticeCentring ϑ N ((m : ℝ) / N)
  have hxEven : Even (x₀ 0 + x₀ 1) := by
    have hmem := latticePoint_mem_evenLattice N x
    simpa [x₀, evenLattice] using hmem
  have hfEven (z : Site) (hz : Even (z 0 + z 1)) : 0 < f z := by
    exact (Smoothing.cellAverage_exp_bounds_of_even N hN h₀ hz).1
  have hpoint (ω : Disorder) :=
    kpzLattice_sub_exactReverseField_eq ϑ hN hm hmEven hLEven hmL h₀ x ω
  have hpoint' (ω : Disorder) :
      kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
        kpzLatticeReversed ϑ N ((q : ℝ) / N) ((L : ℝ) / N) h₀ x
          (PolymerCalculus.reversedDisorder L ω) = A ω - B ω + C := by
    rw [hpoint ω]
    dsimp [A, B, C, q, β, x₀, f, ω']
    ring
  have hA := integral_abs_exactReverse_initial_slice_le β m x₀
  have hB := integral_abs_exactReverse_terminal_profile_ratio_le β (L := L) hm hmEven x₀
    hxEven f hfEven
  have hC : |C| ≤ β ^ 2 / 2 := by
    dsimp [C, β]
    simpa only [abs_sub_comm] using hcenter
  have hcoordLaw := Gaussian.hasLaw_disorder_eval (m, x₀)
  have hIdInt : Integrable id (gaussianReal 0 1) :=
    (memLp_one_iff_integrable).1 (memLp_id_gaussianReal' 1 (by norm_num))
  have hAInt : Integrable A disorderLaw := by
    dsimp [A, β]
    exact ((hcoordLaw.integrable hIdInt).const_mul (criticalBeta ϑ N)).sub
      (integrable_const _)
  have hω'meas : Measurable ω' :=
    (Smoothing.measurable_shiftEnvironment q).comp
      (PolymerCalculus.measurePreserving_reversedDisorder L).measurable
  have hηmeas (z : Site) : Measurable (fun ω => endpointDist β (m - 1) x₀ (ω' ω) z) :=
    (Polymer.measurable_endpointDist β (m - 1) x₀ z).comp hω'meas
  have hprofileMeas (γ : ℝ) : Measurable (fun ω => profileP2Fun γ (m - 1) m
      (endpointDist β (m - 1) x₀ (ω' ω)) f (ω' ω)) :=
    Smoothing.measurable_profileP2Fun_param γ (m - 1) m f hηmeas hω'meas
  have hBmeas : Measurable B := by
    dsimp [B]
    exact (Real.measurable_log.comp (hprofileMeas β)).sub
      (Real.measurable_log.comp (hprofileMeas 0))
  have hBInt : Integrable B disorderLaw := by
    have hAbsInt : Integrable (fun ω => |B ω|) disorderLaw := by
      simpa [B] using hB.1
    apply (integrable_norm_iff hBmeas.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hAbsInt
  have hlinInt : Integrable (fun ω => A ω - B ω + C) disorderLaw := by
    exact (hAInt.sub hBInt).add (integrable_const C)
  have herrorInt : Integrable (fun ω => |kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N ((q : ℝ) / N) ((L : ℝ) / N) h₀ x
        (PolymerCalculus.reversedDisorder L ω)|) disorderLaw := by
    have heq : (fun ω => kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
        kpzLatticeReversed ϑ N ((q : ℝ) / N) ((L : ℝ) / N) h₀ x
          (PolymerCalculus.reversedDisorder L ω)) = fun ω => A ω - B ω + C := by
      funext ω
      exact hpoint' ω
    apply hlinInt.abs.congr
    filter_upwards [] with ω
    rw [hpoint' ω]
  have hAabs : Integrable (fun ω => |A ω|) disorderLaw := by
    simpa [A] using hA.1
  have hBabs : Integrable (fun ω => |B ω|) disorderLaw := by
    simpa [B] using hB.1
  have hmajorInt : Integrable (fun ω => |A ω| + |B ω| + |C|) disorderLaw := by
    exact (hAabs.add hBabs).add (integrable_const |C|)
  have htri (ω : Disorder) : |A ω - B ω + C| ≤ |A ω| + |B ω| + |C| := by
    calc
      _ ≤ |A ω - B ω| + |C| := abs_add_le _ _
      _ ≤ |A ω| + |B ω| + |C| := by
        exact add_le_add
          (calc
            |A ω - B ω| = |A ω + (-B ω)| := by rw [sub_eq_add_neg]
            _ ≤ |A ω| + |-B ω| := abs_add_le _ _
            _ = |A ω| + |B ω| := by simp) le_rfl
  have hpointwise (ω : Disorder) :
      |kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
        kpzLatticeReversed ϑ N ((q : ℝ) / N) ((L : ℝ) / N) h₀ x
          (PolymerCalculus.reversedDisorder L ω)| ≤ |A ω| + |B ω| + |C| := by
    rw [hpoint' ω]
    exact htri ω
  refine ⟨?_, ?_⟩
  · have heq : (fun ω => kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
        kpzLatticeReversed ϑ N ((q : ℝ) / N) ((L : ℝ) / N) h₀ x
          (PolymerCalculus.reversedDisorder L ω)) = fun ω => A ω - B ω + C := by
      funext ω
      exact hpoint' ω
    simpa [q] using herrorInt
  · have hmono := integral_mono_ae herrorInt hmajorInt
      (Filter.Eventually.of_forall hpointwise)
    have hsplit :
        (∫ ω, (|A ω| + |B ω|) + |C| ∂disorderLaw) =
          ((∫ ω, |A ω| ∂disorderLaw) + (∫ ω, |B ω| ∂disorderLaw)) + |C| := by
      let c : ℝ := |C|
      have hab : (∫ ω, |A ω| + |B ω| ∂disorderLaw) =
          (∫ ω, |A ω| ∂disorderLaw) + (∫ ω, |B ω| ∂disorderLaw) :=
        integral_add hAabs hBabs
      have hc : (∫ ω, c ∂disorderLaw) = c := by
        rw [integral_const]
        simp
      change (∫ ω, ((fun ω => |A ω|) + (fun ω => |B ω|)) ω +
          (fun _ : Disorder => c) ω ∂disorderLaw) = _
      calc
        _ = (∫ ω, ((fun ω => |A ω|) + (fun ω => |B ω|)) ω ∂disorderLaw) +
              (∫ ω, (fun _ : Disorder => c) ω ∂disorderLaw) :=
          integral_add (hAabs.add hBabs) (integrable_const c)
        _ = ((∫ ω, |A ω| ∂disorderLaw) + (∫ ω, |B ω| ∂disorderLaw)) + |C| := by
          change (∫ ω, |A ω| + |B ω| ∂disorderLaw) +
              (∫ ω, c ∂disorderLaw) = _
          rw [hab, hc]
    calc
      _ ≤ ∫ ω, |A ω| + |B ω| + |C| ∂disorderLaw := by simpa [q] using hmono
      _ = ((∫ ω, |A ω| ∂disorderLaw) + (∫ ω, |B ω| ∂disorderLaw)) + |C| := hsplit
      _ ≤ (|β| + β ^ 2 / 2) + Real.sqrt (β ^ 2 + β ^ 4 / 4) + β ^ 2 / 2 := by
        exact add_le_add (add_le_add hA.2 hB.2) hC
      _ = _ := by ring

end Critical2DKPZ.LocalSobolev

end
