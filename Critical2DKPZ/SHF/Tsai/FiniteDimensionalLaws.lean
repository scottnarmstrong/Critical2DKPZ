/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.GridFiniteLaws
public import Critical2DKPZ.SHF.Tsai.FiniteTimeGrid

/-! # Finite-dimensional dense-flow laws from interval laws

A common finite grid contains all requested endpoints. Common measurable
coarse-interval factors transfer the equal elementary-block laws to the
requested joint law. The empty family is handled by probability normalization.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- For flows satisfying the dense-time moment, composition, and independence conditions, equal interval marginal laws imply equal finite-dimensional increment laws. -/
theorem isDenseSHF_fdd_eq_of_law_eq (θ : ℝ) (D : Set ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    (hlaw : ∀ s ∈ D, ∀ t ∈ D, s < t → P.map (Z s t) = P'.map (Z' s t)) (k : ℕ) (s t : Fin k → ℝ)
    (hst : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) :
    P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω) := by
  classical
  by_cases hk : k = 0
  · subst k
    have heq : (fun ω (i : Fin 0) => Z (s i) (t i) ω) = fun _ : Ω => (0 : Fin 0 → Measure (Plane × Plane)) := by
      funext ω i
      exact Fin.elim0 i
    have heq' : (fun ω (i : Fin 0) => Z' (s i) (t i) ω) = fun _ : Ω' => (0 : Fin 0 → Measure (Plane × Plane)) := by
      funext ω i
      exact Fin.elim0 i
    simp only [heq, heq', Measure.map_const, measure_univ, one_smul]
  obtain ⟨m, q, hq, hqD, a, b, hab, hsa, htb⟩ :=
    exists_common_time_grid D (Nat.pos_of_ne_zero hk) s t hst
  have h := isDenseSHF_grid_fdd_eq_of_law_eq P P' Z Z' hZ hZ' hlaw m q hq hqD k a b hab
  simpa only [hsa, htb] using h

end Critical2DKPZ.SHF.Tsai

end
