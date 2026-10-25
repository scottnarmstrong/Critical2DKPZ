/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Orthogonality
public import Mathlib.Tactic
public import Critical2DKPZ.Gaussian.TimeBlocks
import Critical2DKPZ.Polymer.Locality
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! # Orthogonality of centered noise with coefficients measurable in the past -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.Blocks

/-- Centered noise is measurable on every time block containing its time coordinate. -/
theorem measurable_xi_disorderBlock (β : ℝ) (a b : ℕ) (i : ℕ × Site)
    (hi : a < i.1 ∧ i.1 ≤ b) :
    Measurable[Gaussian.disorderBlock a b] (Polymer.xi β i) := by
  have hc := Polymer.measurable_block_coordinate a b i hi
  exact (((measurable_const.mul hc).sub measurable_const).exp).sub measurable_const

/-- The covariance of two centered disorder coordinates. -/
theorem integral_xi_mul (β : ℝ) (i j : ℕ × Site) :
    (∫ ω, Polymer.xi β i ω * Polymer.xi β j ω ∂disorderLaw) =
      if i = j then Polymer.sigmaSq β else 0 := by
  simpa only [Polymer.chaosMonomial, Finset.prod_singleton, Finset.singleton_inj,
    Finset.card_singleton, pow_one] using
    Polymer.integral_chaosMonomial_mul β {i} {j}

private theorem integral_past_mul_current (b : ℕ) (F H : Disorder → ℝ)
    (hF : Measurable[Gaussian.disorderBlock 0 b] F)
    (hH : Measurable[Gaussian.disorderBlock b (b + 1)] H) :
    (∫ ω, F ω * H ω ∂disorderLaw) =
      (∫ ω, F ω ∂disorderLaw) * ∫ ω, H ω ∂disorderLaw := by
  have hind : IndepFun F H disorderLaw := by
    rw [IndepFun_iff]
    intro s t hs ht
    exact (Indep_iff _ _ _).1
      (Gaussian.indep_disorderBlock_of_le (m := 0) (n := b)
        (a := b) (b := b + 1) le_rfl) s t (hF.comap_le s hs) (hH.comap_le t ht)
  exact hind.integral_fun_mul_eq_mul_integral
    (hF.mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable
    (hH.mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable

/-- The integral of a past-measurable observable times a fresh centered noise coordinate is zero. -/
theorem integral_past_mul_xi_eq_zero (β : ℝ) (b : ℕ) (x : Site) (F : Disorder → ℝ)
    (hF : Measurable[Gaussian.disorderBlock 0 b] F) :
    (∫ ω, F ω * Polymer.xi β (b + 1, x) ω ∂disorderLaw) = 0 := by
  rw [integral_past_mul_current b F (Polymer.xi β (b + 1, x)) hF
    (measurable_xi_disorderBlock β b (b + 1) (b + 1, x) (by constructor <;> dsimp <;> omega)),
    Polymer.integral_xi, mul_zero]

/-- The integral of two past-measurable coefficients times fresh noise coordinates vanishes off the spatial diagonal and equals the noise variance times the coefficient product integral on the diagonal. -/
theorem integral_predictable_xi_mul (β : ℝ) (a b : ℕ) (x y : Site)
    (F G : Disorder → ℝ)
    (hF : Measurable[Gaussian.disorderBlock 0 a] F)
    (hG : Measurable[Gaussian.disorderBlock 0 b] G) :
    (∫ ω, (F ω * Polymer.xi β (a + 1, x) ω) *
      (G ω * Polymer.xi β (b + 1, y) ω) ∂disorderLaw) =
      if a = b ∧ x = y then
        Polymer.sigmaSq β * (∫ ω, F ω * G ω ∂disorderLaw) else 0 := by
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [ite_eq_right (by omega : ¬ (a = b ∧ x = y))]
    have hF' := hF.mono (Gaussian.disorderBlock_mono le_rfl hab.le) le_rfl
    have hxi := measurable_xi_disorderBlock β 0 b (a + 1, x)
      (by constructor <;> dsimp <;> omega)
    have heq : (fun ω => (F ω * Polymer.xi β (a + 1, x) ω) *
        (G ω * Polymer.xi β (b + 1, y) ω)) =
        (fun ω => ((F ω * Polymer.xi β (a + 1, x) ω) * G ω) *
          Polymer.xi β (b + 1, y) ω) := by funext ω; ring
    rw [heq]
    exact integral_past_mul_xi_eq_zero β b y _ ((hF'.mul hxi).mul hG)
  · subst b
    have hxiX := measurable_xi_disorderBlock β a (a + 1) (a + 1, x)
      (by constructor <;> dsimp <;> omega)
    have hxiY := measurable_xi_disorderBlock β a (a + 1) (a + 1, y)
      (by constructor <;> dsimp <;> omega)
    have heq : (fun ω => (F ω * Polymer.xi β (a + 1, x) ω) *
        (G ω * Polymer.xi β (a + 1, y) ω)) =
        (fun ω => (F ω * G ω) *
          (Polymer.xi β (a + 1, x) ω * Polymer.xi β (a + 1, y) ω)) := by funext ω; ring
    rw [heq, integral_past_mul_current a (fun ω => F ω * G ω)
      (fun ω => Polymer.xi β (a + 1, x) ω * Polymer.xi β (a + 1, y) ω)
      (hF.mul hG) (hxiX.mul hxiY), integral_xi_mul]
    by_cases hxy : x = y <;> simp [hxy, mul_comm]
  · rw [ite_eq_right (by omega : ¬ (a = b ∧ x = y))]
    have hG' := hG.mono (Gaussian.disorderBlock_mono le_rfl hba.le) le_rfl
    have hxi := measurable_xi_disorderBlock β 0 a (b + 1, y)
      (by constructor <;> dsimp <;> omega)
    have heq : (fun ω => (F ω * Polymer.xi β (a + 1, x) ω) *
        (G ω * Polymer.xi β (b + 1, y) ω)) =
        (fun ω => ((G ω * Polymer.xi β (b + 1, y) ω) * F ω) *
          Polymer.xi β (a + 1, x) ω) := by funext ω; ring
    rw [heq]
    exact integral_past_mul_xi_eq_zero β a x _ ((hG'.mul hxi).mul hF)

/-- Noise terms with fourth-integrable coefficients have an integrable product. -/
theorem integrable_predictable_xi_mul (β : ℝ) (a b : ℕ) (x y : Site)
    (F G : Disorder → ℝ) (hF : MemLp F 4 disorderLaw) (hG : MemLp G 4 disorderLaw) :
    Integrable (fun ω => (F ω * Polymer.xi β (a + 1, x) ω) *
      (G ω * Polymer.xi β (b + 1, y) ω)) disorderLaw := by
  have hFX : MemLp (fun ω => F ω * Polymer.xi β (a + 1, x) ω) 2 disorderLaw :=
    Polymer.memLp_mul_double 2 (by convert hF using 1; norm_num)
      (by convert Polymer.memLp_xi β (a + 1, x) 4 (by norm_num) using 1; norm_num)
  have hGY : MemLp (fun ω => G ω * Polymer.xi β (b + 1, y) ω) 2 disorderLaw :=
    Polymer.memLp_mul_double 2 (by convert hG using 1; norm_num)
      (by convert Polymer.memLp_xi β (b + 1, y) 4 (by norm_num) using 1; norm_num)
  exact memLp_one_iff_integrable.1 (Polymer.memLp_mul_double 1
    (by simpa only [mul_one] using hFX) (by simpa only [mul_one] using hGY))

end Critical2DKPZ.Blocks
