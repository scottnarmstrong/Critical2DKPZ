/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TensorComposition

/-! # Joint laws of adjacent dense-time intervals

Independence expresses each adjacent-pair law as the product of its two
marginal laws. Equality of single-interval laws therefore compares the pair.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Equal interval laws determine the joint law of two adjacent increments. -/
theorem isDenseSHF_adjacent_pair_law_eq_of_law_eq {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    (hlaw : ∀ s ∈ D, ∀ t ∈ D, s < t → P.map (Z s t) = P'.map (Z' s t))
    {a b c : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hab : a < b) (hbc : b < c) :
    P.map (fun ω => (Z a b ω, Z b c ω)) = P'.map (fun ω => (Z' a b ω, Z' b c ω)) := by
  have hi : IndepFun (Z a b) (Z b c) P := by
    simpa using
      (hZ.iIndepFun_twoConsecutive ha hb hc hab hbc).indepFun (by decide : (0 : Fin 2) ≠ 1)
  have hi' : IndepFun (Z' a b) (Z' b c) P' := by
    simpa using
      (hZ'.iIndepFun_twoConsecutive ha hb hc hab hbc).indepFun (by decide : (0 : Fin 2) ≠ 1)
  rw [hi.map_prod_eq_prod_map_map (hZ.1 a ha b hb hab).1.aemeasurable (hZ.1 b hb c hc hbc).1.aemeasurable,
    hi'.map_prod_eq_prod_map_map (hZ'.1 a ha b hb hab).1.aemeasurable (hZ'.1 b hb c hc hbc).1.aemeasurable,
    hlaw a ha b hb hab, hlaw b hb c hc hbc]

end Critical2DKPZ.SHF.Tsai

end
