/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.PathConvexity
public import Critical2DKPZ.Polymer.Moments
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic

/-! For nonnegative coefficients with at least one positive, the logarithm of a finite path mass has exponential moments of every real order. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.PolymerCalculus

/-- Every scaled path energy has finite exponential moments. -/
theorem integrable_exp_mul_pathEnergy (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (q : ℝ) :
    Integrable (fun ω => Real.exp (q * pathEnergy β a w s ω)) disorderLaw := by
  have he : (fun ω => Real.exp (q * pathEnergy β a w s ω)) = fun ω =>
      Real.exp (∑ _j ∈ Finset.Icc 1 n, ((q * β) ^ 2 / 2 - q * (β ^ 2 / 2))) *
        Polymer.pathWeight (q * β) a w s ω := by
    funext ω
    unfold Polymer.pathWeight
    rw [← Real.exp_add]
    congr 1
    simp only [pathEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact (Polymer.integrable_pathWeight (q * β) a w s).const_mul _

/-- Every finite linear combination of polymer path weights belongs to Lᵖ for every finite exponent. -/
theorem memLp_finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) (c : ι × (Fin n → Fin 4) → ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (finitePathMass β a n w c) p disorderLaw := by
  exact memLp_finsetSum _ fun j _ =>
    (Polymer.memLp_pathWeight β a (w j.1) j.2 p hp).const_mul (c j)

/-- Each positive coefficient gives a lower affine bound on the logarithm. -/
theorem affine_le_log_finitePathMass {ι : Type*} [Fintype ι]
    (β : ℝ) (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ j, 0 ≤ c j) {j : ι × (Fin n → Fin 4)} (hj : 0 < c j) (ω : Disorder) :
    Real.log (c j) + pathEnergy β a (w j.1) j.2 ω ≤
      Real.log (finitePathMass β a n w c ω) := by
  have hterm : c j * Real.exp (pathEnergy β a (w j.1) j.2 ω) ≤
      finitePathMass β a n w c ω := by
    unfold finitePathMass
    exact Finset.single_le_sum (f := fun i => c i * Real.exp (pathEnergy β a (w i.1) i.2 ω))
      (fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le)
      (Finset.mem_univ j)
  have h := Real.log_le_log (mul_pos hj (Real.exp_pos _)) hterm
  rwa [Real.log_mul hj.ne' (Real.exp_pos _).ne', Real.log_exp] at h

/-- The logarithm of a positive finite path sum has all real exponential moments. -/
theorem integrable_exp_mul_log_finitePathMass {ι : Type*} [Fintype ι]
    (β : ℝ) (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hpos : ∃ j, 0 < c j) (q : ℝ) :
    Integrable (fun ω => Real.exp (q * Real.log (finitePathMass β a n w c ω)))
      disorderLaw := by
  have hm : AEStronglyMeasurable (fun ω =>
      Real.exp (q * Real.log (finitePathMass β a n w c ω))) disorderLaw := by
    exact (measurable_const.mul (measurable_log_finitePathMass β a n w c)).exp.aestronglyMeasurable
  rcases le_total q 0 with hq | hq
  · obtain ⟨j, hj⟩ := hpos
    have hg : Integrable (fun ω => Real.exp (q * (Real.log (c j) +
        pathEnergy β a (w j.1) j.2 ω))) disorderLaw := by
      simp_rw [mul_add, Real.exp_add]
      exact (integrable_exp_mul_pathEnergy β a (w j.1) j.2 q).const_mul _
    apply hg.mono' hm
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (affine_le_log_finitePathMass β a n w hc hj ω) hq)
  · let k := ⌈q⌉₊
    have hk : q ≤ (k : ℝ) := Nat.le_ceil q
    have hpow : Integrable (fun ω => finitePathMass β a n w c ω ^ k) disorderLaw := by
      have h := (memLp_finitePathMass β a n w c k (by simp)).integrable_norm_pow'
      simpa only [Real.norm_eq_abs, abs_of_pos (finitePathMass_pos β a n w hc hpos _)] using h
    apply ((integrable_const 1).add hpow).mono' hm
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change _ ≤ 1 + finitePathMass β a n w c ω ^ k
    by_cases hl : Real.log (finitePathMass β a n w c ω) ≤ 0
    · exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hq hl)).trans
        (le_add_of_nonneg_right (pow_nonneg (finitePathMass_pos β a n w hc hpos ω).le k))
    · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk (le_of_not_ge hl))
      rw [Real.exp_nat_mul, Real.exp_log (finitePathMass_pos β a n w hc hpos ω)] at he
      exact he.trans (le_add_of_nonneg_left zero_le_one)

/-- The exponential-integrability domain of the logarithm of a positive finite path mass is all of `ℝ`. -/
theorem integrableExpSet_log_finitePathMass {ι : Type*} [Fintype ι]
    (β : ℝ) (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hpos : ∃ j, 0 < c j) :
    integrableExpSet (fun ω => Real.log (finitePathMass β a n w c ω)) disorderLaw = univ := by
  ext q
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
  exact integrable_exp_mul_log_finitePathMass β a n w hc hpos q

end Critical2DKPZ.PolymerCalculus
