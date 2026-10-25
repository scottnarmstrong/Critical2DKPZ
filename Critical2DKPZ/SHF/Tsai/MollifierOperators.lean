/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.SHF.Tsai.StrongOperatorLimits
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.Integral

/-! # Bounded convolution operators of applicable mollifiers

Applicable mollifiers define bounded convolution operators on `L²` that converge strongly
to the identity. Banach–Steinhaus gives a uniform operator-norm bound for the whole family.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The convolution action, with the orientation fixed in the flow axioms. -/
def mollifierAction (w φ : Plane → ℝ) (x : Plane) : ℝ :=
  ∫ y, w (x - y) * φ y

/-- The convolution action depends only on the almost-everywhere class of the input. -/
theorem mollifierAction_congr_ae (w : Plane → ℝ) {φ ψ : Plane → ℝ}
    (h : φ =ᵐ[volume] ψ) : mollifierAction w φ = mollifierAction w ψ := by
  funext x
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- For `L²` data `w` and `φ`, each integrand `y ↦ w (x - y) * φ y` is integrable. -/
theorem integrable_mollifierAction_integrand {w φ : Plane → ℝ}
    (hw : MemLp w 2) (hφ : MemLp φ 2) (x : Plane) :
    Integrable (fun y => w (x - y) * φ y) := by
  simpa only [Function.comp_def, Pi.mul_def] using
    (hw.comp_measurePreserving (volume.measurePreserving_sub_left x)).integrable_mul hφ

/-- The convolution action is additive on `L²` data. -/
theorem mollifierAction_add {w φ ψ : Plane → ℝ}
    (hw : MemLp w 2) (hφ : MemLp φ 2) (hψ : MemLp ψ 2) :
    mollifierAction w (φ + ψ) = mollifierAction w φ + mollifierAction w ψ := by
  funext x
  simp only [mollifierAction, Pi.add_apply, mul_add]
  exact integral_add (integrable_mollifierAction_integrand hw hφ x)
    (integrable_mollifierAction_integrand hw hψ x)

/-- Subtraction commutes with the actual convolution action on `L²` data.
Absolute integrability of each row is `integrable_mollifierAction_integrand`. -/
theorem mollifierAction_sub {w φ ψ : Plane → ℝ}
    (hw : MemLp w 2) (hφ : MemLp φ 2) (hψ : MemLp ψ 2) :
    mollifierAction w (φ - ψ) = mollifierAction w φ - mollifierAction w ψ := by
  funext x
  change (∫ y, w (x - y) * (φ y - ψ y)) = _
  simp_rw [mul_sub]
  exact integral_sub (integrable_mollifierAction_integrand hw hφ x)
    (integrable_mollifierAction_integrand hw hψ x)

/-- The convolution action commutes with real scalar multiplication. -/
theorem mollifierAction_smul (w φ : Plane → ℝ) (c : ℝ) :
    mollifierAction w (c • φ) = c • mollifierAction w φ := by
  funext x
  simp only [mollifierAction, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- The convolution action of an applicable mollifier maps `L²` data to `L²` functions. -/
theorem mollifierAction_memLp {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w)
    (j : ℕ) {φ : Plane → ℝ} (hφ : MemLp φ 2) : MemLp (mollifierAction (w j) φ) 2 := by
  obtain ⟨M, _, hM⟩ := hw.2.2.2.1 j
  exact (hM φ hφ).1

/-- Convolution by an applicable mollifier as a linear map on `L²` equivalence classes. -/
def mollifierLinearMap {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) (j : ℕ) :
    Lp ℝ 2 (volume : Measure Plane) →ₗ[ℝ] Lp ℝ 2 (volume : Measure Plane) where
  toFun φ := (mollifierAction_memLp hw j (Lp.memLp φ)).toLp (mollifierAction (w j) φ)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    apply Eventually.of_forall
    intro x
    change mollifierAction (w j) (⇑(φ + ψ)) x =
      mollifierAction (w j) φ x + mollifierAction (w j) ψ x
    rw [mollifierAction_congr_ae (w j) (Lp.coeFn_add φ ψ),
      mollifierAction_add (hw.2.2.1 j) (Lp.memLp φ) (Lp.memLp ψ)]
    rfl
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    apply Eventually.of_forall
    intro x
    change mollifierAction (w j) (⇑(c • φ)) x = c * mollifierAction (w j) φ x
    rw [mollifierAction_congr_ae (w j) (Lp.coeFn_smul c φ), mollifierAction_smul]
    rfl

/-- The linear map `mollifierLinearMap` satisfies a bound `‖T φ‖ ≤ C * ‖φ‖`. -/
theorem exists_mollifierLinearMap_bound {w : ℕ → Plane → ℝ}
    (hw : IsL2ApplicableMollifier w) (j : ℕ) :
    ∃ C : ℝ, ∀ φ : Lp ℝ 2 (volume : Measure Plane),
      ‖mollifierLinearMap hw j φ‖ ≤ C * ‖φ‖ := by
  obtain ⟨M, hMtop, hM⟩ := hw.2.2.2.1 j
  refine ⟨M.toReal, fun φ => ?_⟩
  change ‖(mollifierAction_memLp hw j (Lp.memLp φ)).toLp (mollifierAction (w j) φ)‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have h := ENNReal.toReal_mono (by finiteness : M * eLpNorm φ 2 volume ≠ ⊤)
    (hM φ (Lp.memLp φ)).2
  change (eLpNorm (fun x : Plane => ∫ y, w j (x - y) * φ y) 2 volume).toReal ≤
    M.toReal * (eLpNorm φ 2 volume).toReal
  simpa only [ENNReal.toReal_mul] using h

/-- The bounded convolution operator of an applicable mollifier. -/
def mollifierOperator {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) (j : ℕ) :
    Lp ℝ 2 (volume : Measure Plane) →L[ℝ] Lp ℝ 2 (volume : Measure Plane) :=
  (mollifierLinearMap hw j).mkContinuousOfExistsBound (exists_mollifierLinearMap_bound hw j)

/-- The operator is represented by the literal convolution, almost everywhere. -/
theorem coe_mollifierOperator {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w)
    (j : ℕ) (φ : Lp ℝ 2 (volume : Measure Plane)) :
    ⇑(mollifierOperator hw j φ) =ᵐ[volume] mollifierAction (w j) φ :=
  (mollifierAction_memLp hw j (Lp.memLp φ)).coeFn_toLp

/-- The mollifier operators converge strongly to the identity on `L²`. -/
theorem tendsto_mollifierOperator {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w)
    (φ : Lp ℝ 2 (volume : Measure Plane)) :
    Tendsto (fun j => mollifierOperator hw j φ) atTop (𝓝 φ) := by
  have heq : (fun j => eLpNorm (⇑(mollifierOperator hw j φ) - ⇑φ) 2 volume) =
      (fun j => eLpNorm (fun x => mollifierAction (w j) φ x - φ x) 2 volume) := by
    funext j
    apply eLpNorm_congr_ae
    filter_upwards [coe_mollifierOperator hw j φ] with x hx
    change mollifierOperator hw j φ x - φ x = mollifierAction (w j) φ x - φ x
    rw [hx]
  have hlim : Tendsto (fun j => eLpNorm (⇑(mollifierOperator hw j φ) - ⇑φ) 2 volume)
      atTop (𝓝 0) := by
    rw [heq]
    exact hw.2.2.2.2 φ (Lp.memLp φ)
  have h := Lp.tendsto_Lp_of_tendsto_eLpNorm (φ : Plane → ℝ) (Lp.memLp φ) hlim
  simpa only [Lp.toLp_coeFn] using h

/-- Banach–Steinhaus supplies one operator bound for the entire mollifier sequence. -/
theorem exists_mollifierOperator_uniform_bound {w : ℕ → Plane → ℝ}
    (hw : IsL2ApplicableMollifier w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖mollifierOperator hw j‖ ≤ C := by
  exact exists_operator_uniform_bound_of_tendsto (A := mollifierOperator hw)
    (B := ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume : Measure Plane)))
    (fun φ => tendsto_mollifierOperator hw φ)


/-- The pointwise-in-index bounds in the definition admit one common finite constant. -/
theorem exists_mollifierAction_uniform_bound {w : ℕ → Plane → ℝ}
    (hw : IsL2ApplicableMollifier w) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ j (φ : Plane → ℝ), MemLp φ 2 →
      eLpNorm (mollifierAction (w j) φ) 2 ≤ M * eLpNorm φ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_mollifierOperator_uniform_bound hw
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun j φ hφ => ?_⟩
  have hact := mollifierAction_congr_ae (w j) hφ.coeFn_toLp
  have hnorm : ‖mollifierOperator hw j (hφ.toLp φ)‖ =
      (eLpNorm (mollifierAction (w j) φ) 2 volume).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (coe_mollifierOperator hw j (hφ.toLp φ)), hact]
  apply (ENNReal.toReal_le_toReal (mollifierAction_memLp hw j hφ).eLpNorm_ne_top
    (by finiteness)).1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0, ← Lp.norm_toLp φ hφ, ← hnorm]
  exact ((mollifierOperator hw j).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hC j) (norm_nonneg _))

end Critical2DKPZ.SHF.Tsai

end
