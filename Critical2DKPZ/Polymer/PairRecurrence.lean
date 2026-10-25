/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Replica
public import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! # One-step recursion for the exact annealed two-replica kernel -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- Annealed two-point free polymer moment at fixed inverse temperature. -/
def pairMoment (β : ℝ) (n : ℕ) (w v : Site) : ℝ :=
  ∫ ω, pointToPlane β 0 n w ω * pointToPlane β 0 n v ω ∂disorderLaw

/-- The mixed second moment of point-to-plane partition functions is invariant under time translation. -/
theorem integral_pairMoment (β : ℝ) (a n : ℕ) (w v : Site) :
    (∫ ω, pointToPlane β a n w ω * pointToPlane β a n v ω ∂disorderLaw) =
      pairMoment β n w v := by
  unfold pairMoment
  rw [pointToPlane_two_replica, pointToPlane_two_replica]

/-- The pair moment is invariant under simultaneous spatial translation. -/
theorem pairMoment_translate (β : ℝ) (n : ℕ) (w v z : Site) :
    pairMoment β n (w + z) (v + z) = pairMoment β n w v := by
  unfold pairMoment
  rw [pointToPlane_two_replica, pointToPlane_two_replica]
  simp only [walkPosition_translate, add_left_inj]

/-- The mixed second moment for equal starting sites is independent of their common site. -/
theorem pairMoment_diagonal (β : ℝ) (n : ℕ) (z : Site) :
    pairMoment β n z z = pairMoment β n 0 0 := by
  simpa only [zero_add] using pairMoment_translate β n 0 0 z

/-- The pair moment at zero duration equals one. -/
@[simp]
theorem pairMoment_zero (β : ℝ) (w v : Site) : pairMoment β 0 w v = 1 := by
  simp only [pairMoment, pointToPlane_zero, one_mul, integral_const, probReal_univ, one_smul]

/-- The pair moment at equal starting sites equals the partition function's second moment. -/
theorem pairMoment_eq_secondMoment (β : ℝ) (n : ℕ) :
    pairMoment β n 0 0 = ∫ ω, pointToPlane β 0 n 0 ω ^ 2 ∂disorderLaw := by
  simp only [pairMoment, pow_two]

/-- The product of two partition functions is integrable. -/
theorem integrable_pairProduct (β : ℝ) (a n : ℕ) (w v : Site) :
    Integrable (fun ω => pointToPlane β a n w ω * pointToPlane β a n v ω) disorderLaw :=
  memLp_one_iff_integrable.mp (memLp_mul_double 1
    (by simpa only [mul_one] using memLp_pointToPlane β a n w 2 (by norm_num))
    (by simpa only [mul_one] using memLp_pointToPlane β a n v 2 (by norm_num)))

/-- The pair moment satisfies the one-step recursion with its collision factor. -/
theorem pairMoment_succ (β : ℝ) (n : ℕ) (w v : Site) :
    pairMoment β (n + 1) w v =
      ∑ i : Fin 4, ∑ j : Fin 4, ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹) *
        (if w + srwStep i = v + srwStep j then Real.exp (β ^ 2) else 1) *
        pairMoment β n (w + srwStep i) (v + srwStep j) := by
  let A (i j : Fin 4) (ω : Disorder) :=
    boltzmann β (1, w + srwStep i) ω * boltzmann β (1, v + srwStep j) ω
  let B (i j : Fin 4) (ω : Disorder) :=
    pointToPlane β 1 n (w + srwStep i) ω * pointToPlane β 1 n (v + srwStep j) ω
  have hAm (i j : Fin 4) : Measurable[Gaussian.disorderBlock 0 1] (A i j) := by
    have hc (z : Site) := measurable_block_coordinate 0 1 (1, z) (by omega)
    exact ((measurable_const.mul (hc _)).sub measurable_const).exp.mul
      (((measurable_const.mul (hc _)).sub measurable_const).exp)
  have hBm (i j : Fin 4) : Measurable[Gaussian.disorderBlock 1 (1 + n)] (B i j) :=
    (measurable_pointToPlane_block β 1 n _).mul (measurable_pointToPlane_block β 1 n _)
  have hind (i j : Fin 4) : IndepFun (A i j) (B i j) disorderLaw := by
    rw [IndepFun_iff]
    intro s t hs ht
    exact (Indep_iff _ _ _).1
      (Gaussian.indep_disorderBlock_of_le (show 1 ≤ 1 from le_rfl)) s t
      ((hAm i j).comap_le s hs) ((hBm i j).comap_le t ht)
  have hint (i j : Fin 4) : Integrable (fun ω => A i j ω * B i j ω) disorderLaw := by
    have hA : MemLp (A i j) 2 disorderLaw := memLp_mul_double 2
      (memLp_boltzmann β _ (2 * 2) (by norm_num))
      (memLp_boltzmann β _ (2 * 2) (by norm_num))
    have hB : MemLp (B i j) 2 disorderLaw := memLp_mul_double 2
      (memLp_pointToPlane β 1 n _ (2 * 2) (by norm_num))
      (memLp_pointToPlane β 1 n _ (2 * 2) (by norm_num))
    exact memLp_one_iff_integrable.mp (memLp_mul_double 1
      (by simpa only [mul_one] using hA) (by simpa only [mul_one] using hB))
  have heq (ω : Disorder) :
      pointToPlane β 0 (n + 1) w ω * pointToPlane β 0 (n + 1) v ω =
        ∑ i : Fin 4, ∑ j : Fin 4, ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹) *
          (A i j ω * B i j ω) := by
    rw [pointToPlane_succ, pointToPlane_succ, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [A, B, boltzmann, Nat.zero_add]
    ring
  unfold pairMoment
  simp_rw [heq]
  rw [integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, (hind i j).integral_fun_mul_eq_mul_integral
    ((hAm i j).mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable
    ((hBm i j).mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable]
  change (4⁻¹ * 4⁻¹) * ((∫ ω, boltzmann β _ ω * boltzmann β _ ω ∂disorderLaw) *
    (∫ ω, pointToPlane β 1 n _ ω * pointToPlane β 1 n _ ω ∂disorderLaw)) = _
  rw [integral_boltzmann_mul, integral_pairMoment]
  simp only [Prod.mk.injEq, true_and, pairMoment]
  ring

end Critical2DKPZ.Polymer
