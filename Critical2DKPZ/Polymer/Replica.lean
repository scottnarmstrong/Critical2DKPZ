/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Orthogonality
public import Critical2DKPZ.Polymer.Locality
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! The mixed second moment of Gaussian polymer partition functions is a two-walk average with a factor `exp(β²)` for every common disorder coordinate, including the terminal time. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Polymer

/-- The single-site Boltzmann factor is `exp(β ωᵢ - β²/2)`. -/
def boltzmann (β : ℝ) (i : ℕ × Site) (ω : Disorder) : ℝ :=
  Real.exp (β * ω i - β ^ 2 / 2)

/-- The single-site Boltzmann factor is measurable. -/
theorem measurable_boltzmann (β : ℝ) (i : ℕ × Site) :
    Measurable (boltzmann β i) := by
  unfold boltzmann
  fun_prop

/-- The single-site Boltzmann factor belongs to Lᵖ for every finite exponent. -/
theorem memLp_boltzmann (β : ℝ) (i : ℕ × Site)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (boltzmann β i) p disorderLaw := by
  have heq : boltzmann β i = fun ω => xi β i ω + 1 := by
    funext ω
    simp only [boltzmann, xi, sub_add_cancel]
  rw [heq]
  exact (memLp_xi β i p hp).add (memLp_const 1)

/-- A normalized single-site Boltzmann factor has expectation one. -/
theorem integral_boltzmann (β : ℝ) (i : ℕ × Site) :
    ∫ ω, boltzmann β i ω ∂disorderLaw = 1 := by
  have heq : boltzmann β i = fun ω => xi β i ω + 1 := by
    funext ω
    simp only [boltzmann, xi, sub_add_cancel]
  rw [heq, integral_add (memLp_one_iff_integrable.mp (memLp_xi β i 1 (by simp)))
    (integrable_const 1)]
  simp only [integral_xi, integral_const, probReal_univ, one_smul, zero_add]

/-- The product of two unit-mean Boltzmann factors has expectation `exp(β²)` for equal disorder coordinates and one for distinct coordinates. -/
theorem integral_boltzmann_mul (β : ℝ) (i j : ℕ × Site) :
    ∫ ω, boltzmann β i ω * boltzmann β j ω ∂disorderLaw =
      if i = j then Real.exp (β ^ 2) else 1 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have heq (ω : Disorder) : boltzmann β i ω * boltzmann β i ω =
        Real.exp ((2 * β) * ω i) * Real.exp (-(β ^ 2)) := by
      simp only [boltzmann, ← Real.exp_add]
      congr 1
      ring
    simp_rw [heq]
    rw [integral_mul_const, integral_exp_coordinate, ← Real.exp_add]
    congr 1
    ring
  · rw [ite_eq_right hij]
    have hind := (coordinates_independent.indepFun hij).comp
      (show Measurable (fun x : ℝ => Real.exp (β * x - β ^ 2 / 2)) by fun_prop)
      (show Measurable (fun x : ℝ => Real.exp (β * x - β ^ 2 / 2)) by fun_prop)
    change IndepFun (boltzmann β i) (boltzmann β j) disorderLaw at hind
    rw [hind.integral_fun_mul_eq_mul_integral
      (measurable_boltzmann β i).aestronglyMeasurable
      (measurable_boltzmann β j).aestronglyMeasurable,
      integral_boltzmann, integral_boltzmann, one_mul]

/-- Functions measurable in disjoint disorder blocks are independent. -/
theorem independent_of_blockMeasurable {ι : Type*} (a b : ι → ℕ)
    (hdisj : Pairwise fun i j => Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (f : ι → Disorder → ℝ)
    (hf : ∀ i, Measurable[Gaussian.disorderBlock (a i) (b i)] (f i)) :
    iIndepFun f disorderLaw := by
  rw [iIndepFun_iff]
  intro t sets hsets
  exact (iIndep_iff _ _).1 (Gaussian.iIndep_disorderBlock a b hdisj) t
    (fun i hi => (hf i).comap_le (sets i) (hsets i hi))

/-- A path weight factors into its single-site Boltzmann factors. -/
theorem pathWeight_eq_prod (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) :
    pathWeight β a w s ω =
      ∏ j ∈ Finset.Icc 1 n, boltzmann β (a + j, walkPosition w s j) ω :=
  Real.exp_sum _ _

/-- The product expectation of two path weights is determined by their collision count. -/
theorem integral_pathWeight_mul (β : ℝ) (a : ℕ) (w v : Site) {n : ℕ}
    (s t : Fin n → Fin 4) :
    ∫ ω, pathWeight β a w s ω * pathWeight β a v t ω ∂disorderLaw =
      ∏ j ∈ Finset.Icc 1 n,
        if walkPosition w s j = walkPosition v t j then Real.exp (β ^ 2) else 1 := by
  let F : ↥(Finset.Icc 1 n) → Disorder → ℝ := fun j ω =>
    boltzmann β (a + j.val, walkPosition w s j.val) ω *
    boltzmann β (a + j.val, walkPosition v t j.val) ω
  have hm : ∀ j, Measurable[Gaussian.disorderBlock (a + j.val - 1) (a + j.val)] (F j) := by
    intro j
    have htime : a + j.val - 1 < a + j.val ∧ a + j.val ≤ a + j.val := by
      have hj := (Finset.mem_Icc.1 j.property).1
      omega
    exact ((measurable_const.mul (measurable_block_coordinate _ _ _ htime)).sub
      measurable_const).exp.mul
        (((measurable_const.mul (measurable_block_coordinate _ _ _ htime)).sub
          measurable_const).exp)
  have hd : Pairwise fun i j : ↥(Finset.Icc 1 n) =>
      Disjoint (Set.Ioc (a + i.val - 1) (a + i.val))
        (Set.Ioc (a + j.val - 1) (a + j.val)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro r hi hj
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    omega
  have hind := independent_of_blockMeasurable
    (fun j : ↥(Finset.Icc 1 n) => a + j.val - 1)
    (fun j => a + j.val) hd F hm
  have hh := hind.integral_fun_prod_eq_prod_integral (fun j =>
    (show Measurable (F j) from (hm j).mono (Gaussian.disorderBlock_le _ _) le_rfl
      ).aestronglyMeasurable)
  have heq (ω : Disorder) :
      pathWeight β a w s ω * pathWeight β a v t ω =
        ∏ j : ↥(Finset.Icc 1 n), F j ω := by
    rw [pathWeight_eq_prod, pathWeight_eq_prod, ← Finset.prod_mul_distrib]
    exact (Finset.prod_coe_sort _ _).symm
  simp_rw [heq]
  rw [hh]
  calc
    _ = ∏ j : ↥(Finset.Icc 1 n),
        if walkPosition w s j.val = walkPosition v t j.val
          then Real.exp (β ^ 2) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      change (∫ ω, boltzmann β _ ω * boltzmann β _ ω ∂disorderLaw) = _
      rw [integral_boltzmann_mul]
      simp only [Prod.mk.injEq, true_and]
    _ = _ := Finset.prod_coe_sort (Finset.Icc 1 n) (fun j =>
      if walkPosition w s j = walkPosition v t j then Real.exp (β ^ 2) else 1)

/-- The second mixed partition moment equals the two-replica collision-weight average. -/
theorem pointToPlane_two_replica (β : ℝ) (a n : ℕ) (w v : Site) :
    ∫ ω, pointToPlane β a n w ω * pointToPlane β a n v ω ∂disorderLaw =
      ∑ s : Fin n → Fin 4, ∑ t : Fin n → Fin 4,
        ((4 : ℝ)⁻¹ ^ n * (4 : ℝ)⁻¹ ^ n) *
          ∏ j ∈ Finset.Icc 1 n,
            if walkPosition w s j = walkPosition v t j then Real.exp (β ^ 2) else 1 := by
  have heq (ω : Disorder) :
      pointToPlane β a n w ω * pointToPlane β a n v ω =
        ∑ s : Fin n → Fin 4, ∑ t : Fin n → Fin 4,
          ((4 : ℝ)⁻¹ ^ n * (4 : ℝ)⁻¹ ^ n) *
            (pathWeight β a w s ω * pathWeight β a v t ω) := by
    rw [pointToPlane_eq_sum, pointToPlane_eq_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp_rw [heq]
  have hint (s t : Fin n → Fin 4) :
      Integrable (fun ω => pathWeight β a w s ω * pathWeight β a v t ω) disorderLaw :=
    memLp_one_iff_integrable.mp (memLp_mul_double 1
      (by simpa only [mul_one] using memLp_pathWeight β a w s 2 (by norm_num))
      (by simpa only [mul_one] using memLp_pathWeight β a v t 2 (by norm_num)))
  rw [integral_finsetSum _ fun s _ =>
    integrable_finsetSum _ fun t _ => (hint s t).const_mul _]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finsetSum _ fun t _ => (hint s t).const_mul _]
  simp_rw [integral_const_mul, integral_pathWeight_mul]

end Critical2DKPZ.Polymer
