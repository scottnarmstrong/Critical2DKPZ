/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BallAverageLaw
public import Critical2DKPZ.Extensions.ScaleLimit.CountableSupLaw

/-! # Stationarity of the radius-truncated maximal function

Finite-family stationarity passes through ball integration and then through a
countable supremum of radii. The endpoint radius is included explicitly.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The law of a radius-truncated maximal function is independent of its center. -/
theorem maximalFnLe_identDistrib {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (y i + z) ω) (fun ω i => g (y i) ω) P P)
    (hcont : ∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀))
    (hint : Integrable (g 0) P) (R : ℝ) (y : Plane) :
    IdentDistrib (fun ω => maximalFnLe R (fun z => g z ω) y)
      (fun ω => maximalFnLe R (fun z => g z ω) 0) P P := by
  classical
  by_cases hR : 0 < R
  · let I := Option {q : ℚ // 0 < q ∧ (q : ℝ) < R}
    let ρ : I → ℝ := fun i => i.elim R (fun q => (q : ℚ))
    let F : I → Ω → ℝ≥0∞ := fun i ω => ballAverage (fun z => g z ω) y (ρ i)
    let G : I → Ω → ℝ≥0∞ := fun i ω => ballAverage (fun z => g z ω) 0 (ρ i)
    have hfd (n : ℕ) (i : Fin n → I) :
        IdentDistrib (fun ω j => F (i j) ω) (fun ω j => G (i j) ω) P P :=
      ballAverages_identDistrib hg hstat hcont hint n (fun j => ρ (i j)) y
    have hh := identDistrib_iSup F G
      (fun i => measurable_ballAverage hg y (ρ i))
      (fun i => measurable_ballAverage hg 0 (ρ i)) hfd
    have heq (z : Plane) (ω : Ω) : maximalFnLe R (fun w => g w ω) z =
        ⨆ i : I, ballAverage (fun w => g w ω) z (ρ i) := by
      rw [maximalFnLe_eq_iSup_rat, ite_eq_left hR, iSup_option]
      change (⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < R},
        ballAverage (fun w => g w ω) z (q : ℚ)) ⊔ ballAverage (fun w => g w ω) z R =
          ballAverage (fun w => g w ω) z R ⊔
            (⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < R}, ballAverage (fun w => g w ω) z (q : ℚ))
      exact sup_comm _ _
    have hy : (fun ω => maximalFnLe R (fun z => g z ω) y) = fun ω => ⨆ i : I, F i ω :=
      funext (heq y)
    have h₀ : (fun ω => maximalFnLe R (fun z => g z ω) 0) = fun ω => ⨆ i : I, G i ω :=
      funext (heq 0)
    rw [hy, h₀]
    exact hh
  · have hzero (z : Plane) (ω : Ω) : maximalFnLe R (fun w => g w ω) z = 0 := by
      apply le_antisymm _ bot_le
      apply iSup_le
      intro r
      exact (hR (r.2.1.trans_le r.2.2)).elim
    simp_rw [hzero]
    exact IdentDistrib.refl measurable_const.aemeasurable

end Critical2DKPZ.Extensions.ScaleLimit

end
