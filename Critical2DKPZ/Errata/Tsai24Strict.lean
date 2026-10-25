/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.HeatWeight
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-! # Exponential transport into weighted function spaces

Multiplication by the negative exponential weight bijectively transports unweighted functions into the positively weighted space of Tsai24 while preserving distance and weighted integrability. -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.Errata

/-- Multiplication by the inverse of the printed planar exponential weight. -/
def tsai24InverseWeight (a : ℝ) (f : Plane → ℝ) (x : Plane) : ℝ :=
  Real.exp (-(a * planeOneNorm x)) * f x

/-- Inverse-weight multiplication is a bijective isometry with the corresponding weighted integrability condition. -/
theorem tsai24_inverse_weight_strict_corrected (a : ℝ) (p : ℝ≥0∞) :
    Function.Bijective (tsai24InverseWeight a) ∧
      (∀ f g : Plane → ℝ,
        eLpNorm (fun x => (tsai24InverseWeight a f x - tsai24InverseWeight a g x) *
          Real.exp (a * planeOneNorm x)) p volume = eLpNorm (fun x => f x - g x) p volume) ∧
      (∀ f : Plane → ℝ,
        MemLp (fun x => tsai24InverseWeight a f x * Real.exp (a * planeOneNorm x)) p volume ↔
          MemLp f p volume) := by
  have hcancel (f : Plane → ℝ) (x : Plane) :
      tsai24InverseWeight a f x * Real.exp (a * planeOneNorm x) = f x := by
    rw [tsai24InverseWeight, mul_right_comm, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, one_mul]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro f g hfg
    funext x
    have h := congrArg (fun h : Plane → ℝ => h x * Real.exp (a * planeOneNorm x)) hfg
    simpa only [hcancel] using h
  · intro f
    refine ⟨fun x => f x * Real.exp (a * planeOneNorm x), ?_⟩
    funext x
    rw [tsai24InverseWeight, mul_left_comm, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, mul_one]
  · intro f g
    congr 1
    funext x
    rw [sub_mul, hcancel, hcancel]
  · intro f
    simp only [hcancel]

/-- A strictly growing collision sequence can have consecutive covered sets intersecting in two labels. -/
theorem tsai24_growth_cases_strict_counterexample :
    ∃ η : Fin 2 → CollisionPair 4,
      let ω₁ : Finset (Fin 4) := {(η 0).1.1, (η 0).1.2}
      let ω₂ : Finset (Fin 4) := ω₁ ∪ {(η 1).1.1, (η 1).1.2}
      ω₁ ⊂ ω₂ ∧
        ¬ ((ω₂ ∩ ω₁).card = 1 ∨ (ω₂ ∩ ω₁).card = 0) ∧
        ({(η 1).1.1, (η 1).1.2} ∩ ω₁).card = 1 := by
  refine ⟨![⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩], ?_⟩
  decide

/-- Under strict growth, the new collision pair meets the preceding covered set in zero or one label. -/
theorem tsai24_growth_cases_strict_corrected {n : ℕ}
    (S : Finset (Fin n)) (η : CollisionPair n)
    (hgrow : S ⊂ S ∪ {η.1.1, η.1.2}) :
    ({η.1.1, η.1.2} ∩ S).card = 0 ∨ ({η.1.1, η.1.2} ∩ S).card = 1 := by
  let A : Finset (Fin n) := {η.1.1, η.1.2}
  have hnot : ¬ A ⊆ S := by
    intro h
    have he : S ∪ A = S := Finset.union_eq_left.mpr h
    change S ⊂ S ∪ A at hgrow
    rw [he] at hgrow
    exact (Finset.ssubset_iff_subset_ne.mp hgrow).2 rfl
  have hne : A ∩ S ≠ A := by
    intro h
    apply hnot
    intro x hx
    have hx' : x ∈ A ∩ S := h.symm ▸ hx
    exact (Finset.mem_inter.mp hx').2
  have hss : A ∩ S ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hne⟩
  have hcard : A.card = 2 := by
    simp only [A, Finset.card_pair (ne_of_lt η.2)]
  have hlt : (A ∩ S).card < 2 := by simpa only [hcard] using Finset.card_lt_card hss
  change (A ∩ S).card = 0 ∨ (A ∩ S).card = 1
  omega

end Critical2DKPZ.Errata
