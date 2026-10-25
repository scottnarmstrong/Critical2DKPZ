/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs

/-! # Joint laws of consecutive flow increments

Consecutive increments are independent, so their joint law is the product of their
marginal laws.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Equal single-interval laws give equal joint laws for consecutive flow increments. -/
theorem isDenseSHF_consecutive_law_eq_of_law_eq (θ : ℝ) (D : Set ℝ)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    (hlaw : ∀ s ∈ D, ∀ t ∈ D, s < t → P.map (Z s t) = P'.map (Z' s t))
    (k : ℕ) (t : Fin (k + 1) → ℝ) (ht : StrictMono t) (htD : ∀ i, t i ∈ D) :
    P.map (fun ω (i : Fin k) => Z (t i.castSucc) (t i.succ) ω) =
      P'.map (fun ω (i : Fin k) => Z' (t i.castSucc) (t i.succ) ω) := by
  have hst (i : Fin k) : t i.castSucc < t i.succ := ht i.castSucc_lt_succ
  have hm (i : Fin k) : AEMeasurable (Z (t i.castSucc) (t i.succ)) P :=
    (hZ.1 _ (htD i.castSucc) _ (htD i.succ) (hst i)).1.aemeasurable
  have hm' (i : Fin k) : AEMeasurable (Z' (t i.castSucc) (t i.succ)) P' :=
    (hZ'.1 _ (htD i.castSucc) _ (htD i.succ) (hst i)).1.aemeasurable
  rw [(hZ.2.2.1 k t ht htD).map_fun_eq_pi_map hm,
    (hZ'.2.2.1 k t ht htD).map_fun_eq_pi_map hm']
  congr 1
  funext i
  exact hlaw _ (htD i.castSucc) _ (htD i.succ) (hst i)

end Critical2DKPZ.SHF.Tsai

end
