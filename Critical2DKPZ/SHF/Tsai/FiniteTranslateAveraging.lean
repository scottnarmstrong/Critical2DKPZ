/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.FiniteAveraging
public import Critical2DKPZ.Definitions.Plane

/-! # Finite averages of spatial `L²` translates

Haar invariance gives the same `L²` norm to every translated reflection.
Tonelli computes the product-space norm. Finite averaging then gives the
spatial `L²` bound and almost-everywhere absolute convergence.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A measurable family of translated reflections has the exact product-space squared norm. -/
theorem memLp_translates_prod {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (a : Y → Plane) (ha : Measurable a)
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    MemLp (fun q : Plane × Y => w (a q.2 - q.1)) 2 (volume.prod ν) ∧
    eLpNorm (fun q : Plane × Y => w (a q.2 - q.1)) 2 (volume.prod ν) ^ (2 : ℕ) =
      ν Set.univ * eLpNorm w 2 ^ (2 : ℕ) := by
  let f (q : Plane × Y) := w (a q.2 - q.1)
  have hfm : Measurable f := hwm.comp ((ha.comp measurable_snd).sub measurable_fst)
  have hrow (y : Y) : (∫⁻ x : Plane, ‖f (x, y)‖ₑ ^ (2 : ℕ)) = eLpNorm w 2 ^ (2 : ℕ) := by
    have hm : AEStronglyMeasurable (fun x => w (a y - x)) volume :=
      (hwm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    rw [← sq_eLpNorm_two_eq_lintegral_enorm hm]
    have h := eLpNorm_comp_measurePreserving hw.aestronglyMeasurable
      (volume.measurePreserving_sub_left (a y)) (p := 2)
    exact congrArg (fun z : ℝ≥0∞ => z ^ (2 : ℕ)) h
  have heq : eLpNorm f 2 (volume.prod ν) ^ (2 : ℕ) = ν Set.univ * eLpNorm w 2 ^ (2 : ℕ) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm hfm.aestronglyMeasurable,
      lintegral_prod_symm _ (hfm.enorm.pow_const (2 : ℕ)).aemeasurable]
    simp_rw [hrow]
    rw [lintegral_const, mul_comm]
  have hfin : eLpNorm f 2 (volume.prod ν) ^ (2 : ℕ) ≠ ⊤ := by
    rw [heq]
    exact ENNReal.mul_ne_top (measure_ne_top ν Set.univ) (ENNReal.pow_ne_top hw.eLpNorm_ne_top)
  refine ⟨?_, heq⟩
  exact ((ENNReal.pow_ne_top_iff.1 hfin).resolve_right (by norm_num : (2 : ℕ) ≠ 0)).lt_top

/-- Averaging spatial translates against a finite measure preserves `L²`, with absolute
convergence almost everywhere and the total-mass squared norm bound. -/
theorem memLp_integral_translates_finite {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (a : Y → Plane) (ha : Measurable a)
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    MemLp (fun x => ∫ y, w (a y - x) ∂ν) 2 ∧
    (∀ᵐ x ∂volume, Integrable (fun y => w (a y - x)) ν) ∧
    eLpNorm (fun x => ∫ y, w (a y - x) ∂ν) 2 ^ (2 : ℕ) ≤
      ν Set.univ ^ (2 : ℕ) * eLpNorm w 2 ^ (2 : ℕ) := by
  have hprod := memLp_translates_prod ν a ha w hwm hw
  have h := memLp_integral_finite_right volume ν
    (hwm.comp ((ha.comp measurable_snd).sub measurable_fst)) hprod.1
  refine ⟨h.1, h.2.1, h.2.2.trans_eq ?_⟩
  change ν Set.univ * eLpNorm (fun q : Plane × Y => w (a q.2 - q.1)) 2 (volume.prod ν) ^ (2 : ℕ) = _
  rw [hprod.2]
  simp only [pow_two, mul_assoc]

/-- Bounded measurable coefficients can be included in a finite average of `L²` translates.
The conclusion includes absolute convergence of the rows. -/
theorem memLp_integral_bounded_translates_finite {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (a : Y → Plane) (ha : Measurable a)
    (c : Y → ℝ) (hcm : Measurable c) (hc : ∀ y, |c y| ≤ 1)
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    MemLp (fun x => ∫ y, c y * w (a y - x) ∂ν) 2 ∧
    (∀ᵐ x ∂volume, Integrable (fun y => c y * w (a y - x)) ν) ∧
    eLpNorm (fun x => ∫ y, c y * w (a y - x) ∂ν) 2 ^ (2 : ℕ) ≤
      ν Set.univ ^ (2 : ℕ) * eLpNorm w 2 ^ (2 : ℕ) := by
  let f (q : Plane × Y) := c q.2 * w (a q.2 - q.1)
  let b (q : Plane × Y) := w (a q.2 - q.1)
  have hfm : Measurable f := (hcm.comp measurable_snd).mul
    (hwm.comp ((ha.comp measurable_snd).sub measurable_fst))
  have hbase := memLp_translates_prod ν a ha w hwm hw
  have hle : ∀ q : Plane × Y, ‖f q‖ ≤ ‖b q‖ := by
    intro q
    dsimp only [f, b]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hc q.2)
  have hf : MemLp f 2 (volume.prod ν) :=
    hbase.1.of_le hfm.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  have hn : eLpNorm f 2 (volume.prod ν) ≤ eLpNorm b 2 (volume.prod ν) :=
    eLpNorm_mono_ae hfm.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  have havg := memLp_integral_finite_right volume ν hfm hf
  refine ⟨havg.1, havg.2.1, havg.2.2.trans ?_⟩
  calc
    _ ≤ ν Set.univ * eLpNorm b 2 (volume.prod ν) ^ (2 : ℕ) :=
      mul_le_mul' le_rfl (pow_le_pow_left' hn 2)
    _ = _ := by
      change ν Set.univ * eLpNorm (fun q : Plane × Y => w (a q.2 - q.1)) 2 (volume.prod ν) ^ (2 : ℕ) = _
      rw [hbase.2]
      simp only [pow_two, mul_assoc]

end Critical2DKPZ.SHF.Tsai

end
