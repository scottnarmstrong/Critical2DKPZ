/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.FirstNoise
public import Critical2DKPZ.Collision.SpatialRenewal
import Mathlib.Tactic

/-! # Arrival kernels before the terminal disorder coordinate

The parameter `n` counts the weighted steps before the last, unweighted step.
Thus the arrival time is `a + n + 1`, and all disorder in the arrival kernel is
strictly earlier than that time.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.Blocks

/-- Propagation for `n` weighted steps followed by one unweighted arrival step. -/
def preTerminalKernel (β : ℝ) (a n : ℕ) (w y : Site) (ω : Disorder) : ℝ :=
  ∑' z, pointToPoint β a n w z ω * srwKernel 1 (y - z)

/-- The one-step polymer kernel has exactly one disorder factor. -/
theorem pointToPoint_one_step (β : ℝ) (a : ℕ) (w y : Site) (ω : Disorder) :
    pointToPoint β a 1 w y ω =
      srwKernel 1 (y - w) * Polymer.boltzmann β (a + 1, y) ω := by
  rw [pointToPoint_firstNoise]
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self,
    Polymer.pointToPoint_zero, mul_ite, mul_one, mul_zero, tsum_ite_eq]
  unfold Polymer.xi Polymer.boltzmann
  ring

/-- Removing the final Boltzmann factor leaves the arrival kernel. -/
theorem pointToPoint_terminalFactor (β : ℝ) (a n : ℕ) (w y : Site) (ω : Disorder) :
    pointToPoint β a (n + 1) w y ω =
      preTerminalKernel β a n w y ω * Polymer.boltzmann β (a + n + 1, y) ω := by
  rw [Polymer.pointToPoint_chapmanKolmogorov]
  simp_rw [pointToPoint_one_step, ← mul_assoc]
  exact tsum_mul_right


/-- An arrival without weighted steps is the single-step walk kernel. -/
theorem preTerminalKernel_zero (β : ℝ) (a : ℕ) (w y : Site) (ω : Disorder) :
    preTerminalKernel β a 0 w y ω = srwKernel 1 (y - w) := by
  simp only [preTerminalKernel, Polymer.pointToPoint_zero, ite_mul, one_mul, zero_mul,
    tsum_ite_eq']

/-- An arrival kernel has the finite support of an `(n + 1)`-step walk. -/
theorem preTerminalKernel_eq_zero_of_not_mem (β : ℝ) (a n : ℕ) (w y : Site)
    (ω : Disorder) (hy : y ∉ Polymer.endpoints w (n + 1)) :
    preTerminalKernel β a n w y ω = 0 := by
  have hzero := Polymer.pointToPoint_eq_zero_of_not_mem β a (n + 1) w y ω hy
  rw [pointToPoint_terminalFactor] at hzero
  exact (mul_eq_zero.1 hzero).resolve_right (Real.exp_ne_zero _)

/-- The arrival kernel obeys the usual first weighted-step recursion. -/
theorem preTerminalKernel_succ (β : ℝ) (a n : ℕ) (w y : Site) (ω : Disorder) :
    preTerminalKernel β a (n + 1) w y ω =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ * Polymer.boltzmann β (a + 1, w + srwStep i) ω *
        preTerminalKernel β (a + 1) n (w + srwStep i) y ω := by
  exact Polymer.terminalProfile_succ β a n w (fun z => srwKernel 1 (y - z)) ω

/-- The arrival kernel is measurable before the terminal time. -/
theorem measurable_preTerminalKernel_block (β : ℝ) (a n : ℕ) (w y : Site) :
    Measurable[Gaussian.disorderBlock a (a + n)] (preTerminalKernel β a n w y) :=
  Collision.measurable_terminalProfile_block β a n w (fun z => srwKernel 1 (y - z))

/-- Arrival kernels have all finite moments. -/
theorem memLp_preTerminalKernel (β : ℝ) (a n : ℕ) (w y : Site) (p : ℝ≥0∞)
    (hp : p ≠ ∞) : MemLp (preTerminalKernel β a n w y) p disorderLaw :=
  Polymer.memLp_terminalProfile β a n w (fun z => srwKernel 1 (y - z)) p hp


/-- The terminal disorder multiplies the arrival-kernel second moment by one plus the disorder variance. -/
theorem pointToPoint_sq_integral_terminalFactor (β : ℝ) (a n : ℕ) (w y : Site) :
    (∫ ω, pointToPoint β a (n + 1) w y ω ^ 2 ∂disorderLaw) =
      (1 + Polymer.sigmaSq β) *
        ∫ ω, preTerminalKernel β a n w y ω ^ 2 ∂disorderLaw := by
  let F : Disorder → ℝ := fun ω => preTerminalKernel β a n w y ω ^ 2
  let B : Disorder → ℝ := fun ω => Polymer.boltzmann β (a + n + 1, y) ω ^ 2
  have hF : Measurable[Gaussian.disorderBlock a (a + n)] F :=
    (measurable_preTerminalKernel_block β a n w y).pow_const 2
  have hcoord := Polymer.measurable_block_coordinate (a + n) (a + n + 1)
    (a + n + 1, y) (by constructor <;> dsimp <;> omega)
  have hB : Measurable[Gaussian.disorderBlock (a + n) (a + n + 1)] B := by
    exact (((measurable_const.mul hcoord).sub measurable_const).exp).pow_const 2
  have hind : IndepFun F B disorderLaw := by
    rw [IndepFun_iff]
    intro s t hs ht
    exact (Indep_iff _ _ _).1
      (Gaussian.indep_disorderBlock_of_le (m := a) (n := a + n)
        (a := a + n) (b := a + n + 1) le_rfl) s t
      (hF.comap_le s hs) (hB.comap_le t ht)
  have hfglobal := hF.mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hbglobal := hB.mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hfactor := hind.integral_fun_mul_eq_mul_integral
    hfglobal.aestronglyMeasurable hbglobal.aestronglyMeasurable
  have hboltz : (∫ ω, B ω ∂disorderLaw) = 1 + Polymer.sigmaSq β := by
    simp only [B, pow_two, Polymer.integral_boltzmann_mul, ite_true,
      Polymer.sigmaSq, add_sub_cancel]
  simp_rw [pointToPoint_terminalFactor, mul_pow]
  change (∫ ω, F ω * B ω ∂disorderLaw) = _
  rw [hfactor, hboltz, mul_comm]

/-- The arrival-kernel second moment times the disorder variance equals the spatial renewal weight, including at zero coupling. -/
theorem sigmaSq_mul_preTerminalKernel_sq_integral (β : ℝ) (a n : ℕ) (w y : Site) :
    Polymer.sigmaSq β * (∫ ω, preTerminalKernel β a n w y ω ^ 2 ∂disorderLaw) =
      Collision.spatialRenewal (Polymer.sigmaSq β) (n + 1) (y - w) := by
  by_cases hβ : β = 0
  · subst β
    rw [Collision.spatialRenewal_succ]
    simp only [Polymer.sigmaSq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Real.exp_zero, sub_self, zero_mul, mul_zero, tsum_zero, Finset.sum_const_zero]
  have hσ : 0 < Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    exact sub_pos.2 (Real.one_lt_exp_iff.2 (sq_pos_of_ne_zero hβ))
  have hterminal : 0 < 1 + Polymer.sigmaSq β := by linarith only [hσ]
  have hshift := Collision.terminalPairMoment_timeShift β a (n + 1) w w
    (fun z => if z = y then 1 else 0) (fun z => if z = y then 1 else 0)
  have hshift' : (∫ ω, pointToPoint β a (n + 1) w y ω ^ 2 ∂disorderLaw) =
      ∫ ω, pointToPoint β 0 (n + 1) w y ω ^ 2 ∂disorderLaw := by
    simpa only [Collision.terminalPairMoment, mul_ite, mul_one, mul_zero,
      tsum_ite_eq, ← pow_two] using hshift
  have hnorm : (1 + Polymer.sigmaSq β) *
      (∫ ω, preTerminalKernel β a n w y ω ^ 2 ∂disorderLaw) =
      (1 + Polymer.sigmaSq β) / Polymer.sigmaSq β *
        Collision.spatialRenewal (Polymer.sigmaSq β) (n + 1) (y - w) := by
    rw [← pointToPoint_sq_integral_terminalFactor, hshift',
      Collision.pointToPoint_sq_integral_translate,
      Collision.spatialRenewal_secondMoment hβ (by omega)]
  apply mul_left_cancel₀ hterminal.ne'
  calc
    (1 + Polymer.sigmaSq β) *
        (Polymer.sigmaSq β * (∫ ω, preTerminalKernel β a n w y ω ^ 2 ∂disorderLaw)) =
        Polymer.sigmaSq β * ((1 + Polymer.sigmaSq β) *
          (∫ ω, preTerminalKernel β a n w y ω ^ 2 ∂disorderLaw)) := by ring
    _ = _ := by rw [hnorm]; field_simp

end Critical2DKPZ.Blocks
