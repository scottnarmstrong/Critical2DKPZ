/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.PathConvexity
public import Critical2DKPZ.Gaussian.DisorderLaws
import Mathlib.Tactic

/-! Reflecting times in `[0,L]` and fixing later times preserves the Gaussian disorder law and reverses open-endpoint path energies within that interval. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.PolymerCalculus

/-- Reflection of the integer time interval `[0,L]`, fixing all later coordinates. -/
def reflectedTime (L j : ℕ) : ℕ := if j ≤ L then L - j else j

/-- Reflecting a time index twice recovers the original index. -/
@[simp] theorem reflectedTime_involutive (L j : ℕ) :
    reflectedTime L (reflectedTime L j) = j := by
  unfold reflectedTime
  split_ifs <;> omega

/-- A permutation acting on every slab in a joint time-reversal statement. -/
def timeReversalIndex (L : ℕ) : (ℕ × Site) ≃ (ℕ × Site) where
  toFun p := (reflectedTime L p.1, p.2)
  invFun p := (reflectedTime L p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The reversed environment evaluates the original disorder at the reflected time index. -/
def reversedDisorder (L : ℕ) (ω : Disorder) : Disorder :=
  Gaussian.reindexDisorder (timeReversalIndex L) ω

/-- Reversing the disorder coordinates preserves their Gaussian product measure. -/
theorem measurePreserving_reversedDisorder (L : ℕ) :
    MeasurePreserving (reversedDisorder L) disorderLaw disorderLaw :=
  Gaussian.measurePreserving_reindexDisorder (timeReversalIndex L)


/-- The open-endpoint path energy sums the centered disorder contributions at strictly interior walk times. -/
def interiorEnergy (β : ℝ) (a n : ℕ) (z : ℕ → Site) (ω : Disorder) : ℝ :=
  ∑ j ∈ Finset.Ioo 0 n, (β * ω (a + j, z j) - β ^ 2 / 2)

/-- Time reflection preserves the open-endpoint energy on the reversed interval `(L-a-n,L-a)`. -/
theorem interiorEnergy_time_reversal (β : ℝ) (L a n : ℕ) (hL : a + n ≤ L)
    (z : ℕ → Site) (ω : Disorder) :
    interiorEnergy β (L - (a + n)) n (fun j => z (n - j)) (reversedDisorder L ω) =
      interiorEnergy β a n z ω := by
  unfold interiorEnergy
  apply Finset.sum_bij (fun j _ => n - j)
  · intro j hj
    simp only [Finset.mem_Ioo] at hj ⊢
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ioo] at hi hj
    omega
  · intro j hj
    refine ⟨n - j, ?_, ?_⟩
    · simp only [Finset.mem_Ioo] at hj ⊢
      omega
    · have hj' := Finset.mem_Ioo.mp hj
      omega
  · intro j hj
    have hj' := Finset.mem_Ioo.mp hj
    have htime : reflectedTime L (L - (a + n) + j) = a + (n - j) := by
      unfold reflectedTime
      split_ifs <;> omega
    simp only [reversedDisorder, Gaussian.reindexDisorder, timeReversalIndex, Equiv.coe_fn_mk,
      htime]

/-- Removing the terminal slice leaves precisely the open-endpoint energy. -/
theorem pathEnergy_eq_interior_add_terminal (β : ℝ) (a n : ℕ) (hn : 1 ≤ n)
    (w : Site) (s : Fin n → Fin 4) (ω : Disorder) :
    pathEnergy β a w s ω = interiorEnergy β a n (fun j => walkPosition w s j) ω +
      (β * ω (a + n, walkPosition w s n) - β ^ 2 / 2) := by
  have he : Finset.Icc 1 n = insert n (Finset.Ioo 0 n) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  unfold pathEnergy interiorEnergy
  rw [he, Finset.sum_insert (by simp)]
  ring

end Critical2DKPZ.PolymerCalculus
