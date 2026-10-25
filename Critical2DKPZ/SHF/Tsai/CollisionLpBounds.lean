/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Tech
import Mathlib.Tactic

/-! # Fixed-time `Lᵖ` bounds for collision blocks -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The collision block has its exact scalar mass as an `Lᵖ` bilinear bound.
The row and column masses agree by symmetry, so this is the equal-mass Schur
estimate. -/
theorem weightedFormBound_collisionKernel_lp {n : ℕ} (α : CollisionPair n)
    (θ : ℝ) {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
      (fun _ : FusedConfiguration α => 0) p (p / (p - 1))
      (fun y z => ENNReal.ofReal (collisionKernel α θ t y z))
      (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t)) := by
  let q : ℝ := p / (p - 1)
  let M : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi * scalarDensity θ t)
  have hpq : p.HolderConjugate q := by
    apply (Real.holderConjugate_iff_eq_conjExponent hp).2
    rfl
  have hmassReal : 0 < 4 * Real.pi * scalarDensity θ t := by
    exact mul_pos (by positivity) (scalarDensity_pos θ ht)
  have hM0 : M ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hmassReal)
  have hMtop : M ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK : Measurable (Function.uncurry
      (fun y z : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ t y z))) := by
    have hArgs : Measurable (fun x : FusedConfiguration α × FusedConfiguration α =>
        ((θ, t), x.1, x.2)) := by fun_prop
    exact ((measurable_collisionKernel α).comp hArgs).ennreal_ofReal
  have hrow (y : FusedConfiguration α) :
      (∫⁻ z : FusedConfiguration α,
        ENNReal.ofReal (collisionKernel α θ t y z)) ≤ M := by
    rw [lintegral_collisionKernel_right α θ ht y]
  have hcol (z : FusedConfiguration α) :
      (∫⁻ y : FusedConfiguration α,
        ENNReal.ofReal (collisionKernel α θ t y z)) ≤ M := by
    simpa only [collisionKernel_symm α θ t] using hrow z
  intro f g hf hg
  let A : FusedConfiguration α → ℝ≥0∞ := fun y =>
    ∫⁻ z : FusedConfiguration α,
      ENNReal.ofReal (collisionKernel α θ t y z) * f z
  have hA : Measurable A := measurable_kernelAction volume hK hf
  have hSchur := lintegral_kernel_lp_schur_of_mass_bound hK hpq hM0 hMtop hrow hcol hf
  let F : ℝ≥0∞ := ∫⁻ z : FusedConfiguration α, f z ^ p
  let G : ℝ≥0∞ := ∫⁻ y : FusedConfiguration α, g y ^ q
  have hNorm : (∫⁻ y : FusedConfiguration α, A y ^ p) ^ (1 / p : ℝ) ≤
      M * F ^ (1 / p : ℝ) := by
    calc
      _ ≤ (M ^ p * F) ^ (1 / p : ℝ) := by
        apply ENNReal.monotone_rpow_of_nonneg (by positivity : 0 ≤ (1 / p : ℝ))
        simpa [A, F] using hSchur
      _ = M * F ^ (1 / p : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (1 / p : ℝ)),
          ← ENNReal.rpow_mul]
        have hpInv : p * (1 / p : ℝ) = 1 := by
          field_simp [ne_of_gt (by linarith : 0 < p)]
        rw [hpInv, ENNReal.rpow_one]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    hA.aemeasurable hg.aemeasurable
  calc
    (∫⁻ y : FusedConfiguration α,
      g y * (∫⁻ z : FusedConfiguration α,
        ENNReal.ofReal (collisionKernel α θ t y z) * f z))
      ≤ (∫⁻ y : FusedConfiguration α, A y ^ p) ^ (1 / p : ℝ) * G ^ (1 / q : ℝ) := by
        simpa only [A, G, Pi.mul_apply, mul_comm] using hHolder
    _ ≤ M * F ^ (1 / p : ℝ) * G ^ (1 / q : ℝ) :=
      mul_le_mul' hNorm le_rfl
    _ = ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) *
        (∫⁻ z : FusedConfiguration α,
          (f z * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ p) ^ (1 / p) *
        (∫⁻ y : FusedConfiguration α,
          (g y * ENNReal.ofReal (Real.exp (0 : ℝ))) ^ (p / (p - 1))) ^
          (1 / (p / (p - 1))) := by
      simp [M, F, G, q, Real.exp_zero, ENNReal.ofReal_one]

end Critical2DKPZ.SHF.Tsai

end
