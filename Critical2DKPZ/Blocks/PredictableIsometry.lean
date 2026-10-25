/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.PredictableNoise
import Mathlib.Tactic

/-! # Finite predictable-noise isometry -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Blocks

private theorem memLp_coefficient_mul_xi (β : ℝ) (a : ℕ) (x : Site)
    (F : Disorder → ℝ) (hF : MemLp F 4 disorderLaw) :
    MemLp (fun ω => F ω * Polymer.xi β (a + 1, x) ω) 2 disorderLaw :=
  Polymer.memLp_mul_double 2 (by convert hF using 1; norm_num)
    (by convert Polymer.memLp_xi β (a + 1, x) 4 (by norm_num) using 1; norm_num)


/-- Finite sums of predictable centered increments have zero mean. -/
theorem integral_finset_predictable_eq_zero {ι : Type*} (β : ℝ) (I : Finset ι)
    (a : ι → ℕ) (x : ι → Site) (F : ι → Disorder → ℝ)
    (hm : ∀ i ∈ I, Measurable[Gaussian.disorderBlock 0 (a i)] (F i))
    (hF : ∀ i ∈ I, MemLp (F i) 4 disorderLaw) :
    (∫ ω, ∑ i ∈ I, F i ω * Polymer.xi β (a i + 1, x i) ω ∂disorderLaw) = 0 := by
  rw [integral_finsetSum _ (fun i hi => memLp_one_iff_integrable.1
    ((memLp_coefficient_mul_xi β (a i) (x i) (F i) (hF i hi)).mono_exponent
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)))]
  exact Finset.sum_eq_zero fun i hi => integral_past_mul_xi_eq_zero β (a i) (x i)
    (F i) (hm i hi)

/-- The integral of two predictable noise sums over distinct time-site coordinates is the noise variance times the sum of the diagonal coefficient-product integrals. -/
theorem integral_mul_finset_predictable {ι : Type*} (β : ℝ) (I : Finset ι)
    (a : ι → ℕ) (x : ι → Site) (F G : ι → Disorder → ℝ)
    (hinj : Set.InjOn (fun i => (a i, x i)) I)
    (hmF : ∀ i ∈ I, Measurable[Gaussian.disorderBlock 0 (a i)] (F i))
    (hmG : ∀ i ∈ I, Measurable[Gaussian.disorderBlock 0 (a i)] (G i))
    (hF : ∀ i ∈ I, MemLp (F i) 4 disorderLaw)
    (hG : ∀ i ∈ I, MemLp (G i) 4 disorderLaw) :
    (∫ ω, (∑ i ∈ I, F i ω * Polymer.xi β (a i + 1, x i) ω) *
      (∑ i ∈ I, G i ω * Polymer.xi β (a i + 1, x i) ω) ∂disorderLaw) =
      ∑ i ∈ I, Polymer.sigmaSq β * (∫ ω, F i ω * G i ω ∂disorderLaw) := by
  classical
  have hInt (i j) (hi : i ∈ I) (hj : j ∈ I) :=
    integrable_predictable_xi_mul β (a i) (a j) (x i) (x j) (F i) (G j)
      (hF i hi) (hG j hj)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hInt i j hi hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => hInt i j hi hj)]
  have hterm (j) (hj : j ∈ I) :
      (∫ ω, (F i ω * Polymer.xi β (a i + 1, x i) ω) *
        (G j ω * Polymer.xi β (a j + 1, x j) ω) ∂disorderLaw) =
        if i = j then Polymer.sigmaSq β * (∫ ω, F i ω * G i ω ∂disorderLaw) else 0 := by
    rw [integral_predictable_xi_mul β (a i) (a j) (x i) (x j) (F i) (G j)
      (hmF i hi) (hmG j hj)]
    by_cases hij : i = j
    · subst j
      simp only [and_self, ite_true]
    · have hne : ¬ (a i = a j ∧ x i = x j) :=
        fun h => hij (hinj hi hj (Prod.ext h.1 h.2))
      simp only [hne, hij, ite_false]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [Ne.symm hji, ite_false]
  · exact fun h => (h hi).elim



/-- Adding deterministic constants to predictable noise sums adds their product to the diagonal bilinear identity. -/
theorem integral_const_add_finset_predictable_mul {ι : Type*} (β c d : ℝ) (I : Finset ι)
    (a : ι → ℕ) (x : ι → Site) (F G : ι → Disorder → ℝ)
    (hinj : Set.InjOn (fun i => (a i, x i)) I)
    (hmF : ∀ i ∈ I, Measurable[Gaussian.disorderBlock 0 (a i)] (F i))
    (hmG : ∀ i ∈ I, Measurable[Gaussian.disorderBlock 0 (a i)] (G i))
    (hF : ∀ i ∈ I, MemLp (F i) 4 disorderLaw)
    (hG : ∀ i ∈ I, MemLp (G i) 4 disorderLaw) :
    (∫ ω, (c + ∑ i ∈ I, F i ω * Polymer.xi β (a i + 1, x i) ω) *
      (d + ∑ i ∈ I, G i ω * Polymer.xi β (a i + 1, x i) ω) ∂disorderLaw) =
      c * d + ∑ i ∈ I, Polymer.sigmaSq β * (∫ ω, F i ω * G i ω ∂disorderLaw) := by
  let X : Disorder → ℝ := fun ω => ∑ i ∈ I, F i ω * Polymer.xi β (a i + 1, x i) ω
  let Y : Disorder → ℝ := fun ω => ∑ i ∈ I, G i ω * Polymer.xi β (a i + 1, x i) ω
  have hXlp : MemLp X 2 disorderLaw := memLp_finsetSum _ fun i hi =>
    memLp_coefficient_mul_xi β (a i) (x i) (F i) (hF i hi)
  have hYlp : MemLp Y 2 disorderLaw := memLp_finsetSum _ fun i hi =>
    memLp_coefficient_mul_xi β (a i) (x i) (G i) (hG i hi)
  have hX : Integrable X disorderLaw := memLp_one_iff_integrable.1
    (hXlp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hY : Integrable Y disorderLaw := memLp_one_iff_integrable.1
    (hYlp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hXY : Integrable (fun ω => X ω * Y ω) disorderLaw := memLp_one_iff_integrable.1
    (Polymer.memLp_mul_double 1 (by simpa only [mul_one] using hXlp)
      (by simpa only [mul_one] using hYlp))
  have hxmean : (∫ ω, X ω ∂disorderLaw) = 0 :=
    integral_finset_predictable_eq_zero β I a x F hmF hF
  have hymean : (∫ ω, Y ω ∂disorderLaw) = 0 :=
    integral_finset_predictable_eq_zero β I a x G hmG hG
  have hpair : (∫ ω, X ω * Y ω ∂disorderLaw) =
      ∑ i ∈ I, Polymer.sigmaSq β * (∫ ω, F i ω * G i ω ∂disorderLaw) :=
    integral_mul_finset_predictable β I a x F G hinj hmF hmG hF hG
  have hconst : Integrable (fun _ : Disorder => c * d) disorderLaw := integrable_const _
  have hcY : Integrable (fun ω => c * Y ω) disorderLaw := hY.const_mul _
  have hdX : Integrable (fun ω => d * X ω) disorderLaw := hX.const_mul _
  have heq (ω : Disorder) : (c + X ω) * (d + Y ω) =
      ((c * d + c * Y ω) + d * X ω) + X ω * Y ω := by ring
  change (∫ ω, (c + X ω) * (d + Y ω) ∂disorderLaw) = _
  simp_rw [heq]
  rw [integral_add (f := fun ω => (c * d + c * Y ω) + d * X ω)
      (g := fun ω => X ω * Y ω) ((hconst.add hcY).add hdX) hXY,
    integral_add (f := fun ω => c * d + c * Y ω) (g := fun ω => d * X ω)
      (hconst.add hcY) hdX, integral_add hconst hcY,
    integral_const_mul c Y, integral_const_mul d X, hxmean, hymean, hpair,
    integral_const, probReal_univ, one_smul, mul_zero, mul_zero, add_zero, add_zero]

end Critical2DKPZ.Blocks
