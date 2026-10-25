/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.LocalSobolev.DistributionValuedLimits
public import Critical2DKPZ.LocalSobolev.RegularizedFieldCauchy
public import Critical2DKPZ.JointConvergence.ThmToyJointParts
public import Critical2DKPZ.PolymerCalculus.TimeReversal
import Mathlib.Tactic
import Critical2DKPZ.Analysis.Sobolev.Rellich.DistributionRepresentation
import Critical2DKPZ.SHF.Symmetries.LatticeReversalDiscrete

/-! # Comparison of forward and reversed lattice laws -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.LocalSobolev

/-- Measurability of a forward lattice field's test pairing, using the canonical measurable
distribution evaluation. -/
theorem measurable_integral_kpzLattice_testPairing (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    Measurable (fun ω : Disorder => ∫ x, φ x * kpzLattice ϑ N t h₀ x ω) := by
  have hm := measurable_kpzLattice_distribution_pairing ϑ N t h₀ φ
  have hEq : (fun ω : Disorder =>
      (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) φ) =
      fun ω => ∫ x, φ x * kpzLattice ϑ N t h₀ x ω := by
    funext ω
    simpa only [smul_eq_mul] using
      (Distribution.ofFun_apply
        ((kpzLattice_locallyIntegrable ϑ N t h₀ ω).locallyIntegrableOn _))
  rw [← hEq]
  exact hm

/-- Complementary even-ceil clocks leave the forward endpoint unchanged or move it back
exactly two lattice steps. This is the integer perturbation required by the tested clock lemma. -/
theorem kpzLattice_reverseClockShift_spec (N : ℕ) (T : ℝ) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ T) :
    let m := evenCeil ((N : ℝ) * t)
    let L := evenCeil ((N : ℝ) * T)
    let r := evenCeil ((N : ℝ) * (T - t))
    (((L - r : ℕ) : ℤ) - (m : ℤ) = -2) ∨
      (((L - r : ℕ) : ℤ) - (m : ℤ) = 0) := by
  dsimp only
  have hmL : evenCeil ((N : ℝ) * t) ≤ evenCeil ((N : ℝ) * T) :=
    evenCeil_mono (mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg N))
  have hrL : evenCeil ((N : ℝ) * (T - t)) ≤ evenCeil ((N : ℝ) * T) :=
    evenCeil_mono (mul_le_mul_of_nonneg_left (sub_le_self T ht.le)
      (Nat.cast_nonneg N))
  rcases Critical2DKPZ.SHF.Symmetries.evenCeil_reflected_clock_cases
      (N := N) (t := t) (T := T) ht.le htT with h | h
  · right
    omega
  · left
    omega

/-- An L¹ reversal coupling and an integrable second-moment bound give asymptotically equal bounded continuous expectations. -/
theorem tendsto_integral_kpzLattice_reverse_sub_of_tested_L1
    (ϑ T : ℝ) (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ))
    (φ : Fin k → TestFn) (_ht : ∀ i, 0 < t i ∧ t i ≤ T)
    (g : (Fin k → ℝ) →ᵇ ℝ)
    (hsecondTransfer : ∀ {Ω : Type} [MeasurableSpace Ω] {k : ℕ}
      (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℕ → Ω → Fin k → ℝ)
      (_hX : ∀ N, AEMeasurable (X N) P) (_hY : ∀ N, AEMeasurable (Y N) P)
      (_hsecond : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
        Integrable (fun ω => ‖X N ω‖ ^ 2) P ∧
          (∫ ω, ‖X N ω‖ ^ 2 ∂P) ≤ C)
      (_hclose : Tendsto (fun N : ℕ =>
        eLpNorm (fun ω => ‖X N ω - Y N ω‖) 1 P) atTop (𝓝 0))
      (g : (Fin k → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ =>
        (∫ ω, g (X N ω) ∂P) - ∫ ω, g (Y N ω) ∂P) atTop (𝓝 0))
    (hsecond : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => ‖(fun i =>
        ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω)‖ ^ 2) disorderLaw ∧
        (∫ ω, ‖(fun i =>
          ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω)‖ ^ 2 ∂disorderLaw) ≤ C)
    (hclose : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => ‖(fun i =>
        ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω) -
          (fun i => ∫ x, φ i x * kpzLatticeReversed ϑ N (T - t i) T (h₀ i) x
            (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω))‖)
        1 disorderLaw) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
        (∫ ω, g (fun i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω)
          ∂disorderLaw) -
          ∫ ω, g (fun i => ∫ x, φ i x * kpzLatticeReversed ϑ N (T - t i) T
            (h₀ i) x ω) ∂disorderLaw)
      atTop (𝓝 0) := by
  let X : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω
  let Y : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * kpzLatticeReversed ϑ N (T - t i) T (h₀ i) x ω
  let Yrev : ℕ → Disorder → Fin k → ℝ := fun N ω =>
    Y N (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)
  have hX : ∀ N, AEMeasurable (X N) disorderLaw := by
    intro N
    apply aemeasurable_pi_iff.mpr
    intro i
    have hm := measurable_kpzLattice_distribution_pairing ϑ N (t i) (h₀ i) (φ i)
    have hEq (ω : Disorder) :
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω)
          volume ⊤) (φ i) = X N ω i := by
      dsimp [X]
      simpa only [smul_eq_mul] using
        (Distribution.ofFun_apply
          ((kpzLattice_locallyIntegrable ϑ N (t i) (h₀ i) ω).locallyIntegrableOn _))
    have hfun : (fun ω : Disorder =>
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω)
          volume ⊤) (φ i)) = fun ω => X N ω i := by
      funext ω
      exact hEq ω
    rw [← hfun]
    exact hm.aemeasurable
  have hY : ∀ N, AEMeasurable (Y N) disorderLaw := by
    intro N
    apply aemeasurable_pi_iff.mpr
    intro i
    exact JointConvergence.aemeasurable_integral_kpzLatticeReversed
      ϑ N (T - t i) T (h₀ i) (φ i)
  have hYrev : ∀ N, AEMeasurable (Yrev N) disorderLaw := by
    intro N
    let L : ℕ := evenCeil ((N : ℝ) * T)
    have hmp := PolymerCalculus.measurePreserving_reversedDisorder L
    have h := (hY N).aestronglyMeasurable.comp_measurePreserving hmp
    exact h.aemeasurable
  have hclose' : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => ‖X N ω - Yrev N ω‖) 1 disorderLaw) atTop (𝓝 0) := by
    simpa [X, Y, Yrev] using hclose
  have htrans := hsecondTransfer (P := disorderLaw) (X := X) (Y := Yrev)
    hX hYrev hsecond hclose' g
  have hmap (N : ℕ) :
      (∫ ω, g (Yrev N ω) ∂disorderLaw) =
        ∫ ω, g (Y N ω) ∂disorderLaw := by
    let L : ℕ := evenCeil ((N : ℝ) * T)
    let R : Disorder → Disorder := PolymerCalculus.reversedDisorder L
    have hmp := PolymerCalculus.measurePreserving_reversedDisorder L
    have hmeasMap : AEStronglyMeasurable (fun ω : Disorder => g (Y N ω))
        (disorderLaw.map R) := by
      rw [hmp.map_eq]
      exact (g.continuous.measurable.comp_aemeasurable (hY N)).aestronglyMeasurable
    calc
      (∫ ω, g (Yrev N ω) ∂disorderLaw) =
          ∫ ω, g (Y N (R ω)) ∂disorderLaw := by
            rfl
      _ = ∫ ω, g (Y N ω) ∂disorderLaw := by
            calc
              _ = ∫ ω, g (Y N ω) ∂(disorderLaw.map R) := by
                    symm
                    exact integral_map hmp.measurable.aemeasurable hmeasMap
              _ = ∫ ω, g (Y N ω) ∂disorderLaw := by rw [hmp.map_eq]
  have htrans' : Tendsto (fun N : ℕ =>
      (∫ ω, g (X N ω) ∂disorderLaw) -
        ∫ ω, g (Y N ω) ∂disorderLaw) atTop (𝓝 0) := by
    have heq : (fun N : ℕ =>
        (∫ ω, g (X N ω) ∂disorderLaw) -
          ∫ ω, g (Y N ω) ∂disorderLaw) = fun N =>
        (∫ ω, g (X N ω) ∂disorderLaw) -
          ∫ ω, g (Yrev N ω) ∂disorderLaw := by
      funext N
      rw [hmap N]
    rw [heq]
    exact htrans
  simpa [X, Y] using htrans'

end Critical2DKPZ.LocalSobolev

end
