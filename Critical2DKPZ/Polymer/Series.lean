/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Locality
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-! Absolutely summable initial profiles and bounded terminal weights give finite polymer moments and permit termwise integration. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Critical2DKPZ.Polymer

/-- For `1 ≤ p ≤ ∞`, a countable family with summable Lᵖ norms has a pointwise sum in Lᵖ. -/
theorem memLp_tsum_of_norm {ι : Type*} [Countable ι] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : ι → Disorder → ℝ) (hf : ∀ i, MemLp (f i) p disorderLaw)
    (hs : ∑' i, eLpNorm (f i) p disorderLaw ≠ ∞) :
    MemLp (fun ω => ∑' i, f i ω) p disorderLaw := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  let F (i : ι) : Lp ℝ p disorderLaw := (hf i).toLp (f i)
  have hsum : ∑' i, ‖F i‖ₑ ≠ ∞ := by
    simpa only [F, Lp.enorm_toLp] using hs
  have hcoe := Lp.coeFn_tsum (f := F) hsum
  have heach : ∀ᵐ ω ∂disorderLaw, ∀ i, F i ω = f i ω :=
    ae_all_iff.2 fun i => (hf i).coeFn_toLp
  have heq : (⇑(∑' i, F i)) =ᵐ[disorderLaw] fun ω => ∑' i, f i ω := by
    filter_upwards [hcoe, heach] with ω hω hi
    rw [hω]
    exact tsum_congr (fun i => hi i)
  have hH : MemLp (fun ω => (∑' i, F i) ω) p disorderLaw :=
    Lp.memLp (∑' i, F i)
  exact (memLp_congr_ae heq).mp hH

/-- Spatial translation preserves the Lᵖ norm of a point-to-plane partition function. -/
theorem eLpNorm_pointToPlane_translate (β : ℝ) (a n : ℕ) (w : Site) (p : ℝ≥0∞) :
    eLpNorm (pointToPlane β a n w) p disorderLaw =
      eLpNorm (pointToPlane β a n 0) p disorderLaw := by
  have heq : pointToPlane β a n w = (pointToPlane β a n 0) ∘
      (fun ω : Disorder => fun i => ω (i.1, i.2 + w)) := by
    funext ω
    simpa only [zero_add, Function.comp_apply] using pointToPlane_translate β a n 0 w ω
  rw [heq]
  exact eLpNorm_comp_measurePreserving
    (measurable_pointToPlane β a n 0).aestronglyMeasurable
    (Gaussian.measurePreserving_disorder_translation w)

/-- A bounded terminal profile gives the corresponding bound by the point-to-plane partition function. -/
theorem terminalProfile_abs_le (β : ℝ) (a n : ℕ) (w : Site) (f : Site → ℝ)
    (M : ℝ) (hM : ∀ z, |f z| ≤ M) (ω : Disorder) :
    |∑' z, pointToPoint β a n w z ω * f z| ≤ M * pointToPlane β a n w ω := by
  rw [tsum_pointToPoint_mul, pointToPlane_eq_sum, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  rw [abs_mul, abs_of_nonneg
    (mul_nonneg (by positivity) (pathWeight_pos β a w s ω).le)]
  calc
    _ ≤ ((4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω) * M :=
      mul_le_mul_of_nonneg_left (hM _) (mul_nonneg (by positivity) (pathWeight_pos β a w s ω).le)
    _ = _ := mul_comm _ _

/-- An absolutely summable initial profile and a bounded terminal weight give a summable family of Lᵖ norms for every finite exponent. -/
theorem profile_term_norms_ne_top (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ z, |f z| ≤ M) (p : ℝ≥0∞) (hptop : p ≠ ∞) :
    (∑' w, eLpNorm (fun ω => ν w *
      ∑' z, pointToPoint β a (b - a) w z ω * f z) p disorderLaw) ≠ ∞ := by
  let Z (w : Site) (ω : Disorder) := ∑' z, pointToPoint β a (b - a) w z ω * f z
  have hZ (w : Site) : MemLp (Z w) p disorderLaw := memLp_terminalProfile β a (b - a) w f p hptop
  have hbound (w : Site) :
      eLpNorm (Z w) p disorderLaw ≤
        ENNReal.ofReal M * eLpNorm (pointToPlane β a (b - a) 0) p disorderLaw := by
    calc
      _ ≤ eLpNorm (fun ω => M * pointToPlane β a (b - a) w ω) p disorderLaw := by
        apply eLpNorm_mono_ae (hZ w).aestronglyMeasurable
        exact Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg hM0 (pointToPlane_pos β a (b - a) w ω).le)]
          exact terminalProfile_abs_le β a (b - a) w f M hM ω
      _ = _ := by
        change eLpNorm (M • pointToPlane β a (b - a) w) p disorderLaw = _
        rw [eLpNorm_const_smul, eLpNorm_pointToPlane_translate]
        simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hM0]
  have hs : ∑' w, eLpNorm (fun ω => ν w * Z w ω) p disorderLaw ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hν.tsum_ofReal_lt_top.ne ENNReal.ofReal_ne_top)
        (memLp_pointToPlane β a (b - a) 0 p hptop).eLpNorm_ne_top)
    calc
      _ ≤ ∑' w, ENNReal.ofReal |ν w| *
          (ENNReal.ofReal M * eLpNorm (pointToPlane β a (b - a) 0) p disorderLaw) := by
        apply ENNReal.tsum_le_tsum
        intro w
        change eLpNorm (ν w • Z w) p disorderLaw ≤ _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
        exact mul_le_mul_right (hbound w) _
      _ = _ := by rw [ENNReal.tsum_mul_right, mul_assoc]
  exact hs

/-- For `1 ≤ p < ∞`, the partition function with an absolutely summable initial profile and bounded terminal weight belongs to Lᵖ. -/
theorem memLp_profile_series (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ z, |f z| ≤ M) (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞) :
    MemLp (profileP2Fun β a b ν f) p disorderLaw := by
  exact memLp_tsum_of_norm p hp
    (fun w ω => ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z)
    (fun w => (memLp_terminalProfile β a (b - a) w f p hptop).const_mul _)
    (profile_term_norms_ne_top β a b ν f hν M hM0 hM p hptop)

/-- A partition function with an absolutely summable initial profile and bounded terminal weight belongs to Lᵖ for every finite exponent. -/
theorem memLp_profileP2Fun_summable (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ z, |f z| ≤ M) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (profileP2Fun β a b ν f) p disorderLaw :=
  (memLp_profile_series β a b ν f hν M hM0 hM (max 1 p)
    (le_max_left 1 p) (max_lt (by norm_num) hp.lt_top).ne).mono_exponent (le_max_right 1 p)

/-- The mean summable-profile partition function equals its deterministic kernel pairing. -/
theorem integral_profileP2Fun_summable (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ z, |f z| ≤ M) :
    (∫ ω, profileP2Fun β a b ν f ω ∂disorderLaw) =
      ∑' w, ν w * ∑' z, srwKernel (b - a) (z - w) * f z := by
  unfold profileP2Fun
  rw [integral_tsum]
  · apply tsum_congr
    intro w
    rw [integral_const_mul, integral_terminalProfile]
  · intro w
    exact ((memLp_one_iff_integrable.mp
      (memLp_terminalProfile β a (b - a) w f 1 (by simp))).const_mul _).aestronglyMeasurable
  · have h := profile_term_norms_ne_top β a b ν f hν M hM0 hM 1 (by simp)
    have heq (w : Site) :
        eLpNorm (fun ω => ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z)
          1 disorderLaw =
        ∫⁻ ω, ‖ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z‖ₑ ∂disorderLaw :=
      eLpNorm_one_eq_lintegral_enorm
        (((memLp_one_iff_integrable.mp
          (memLp_terminalProfile β a (b - a) w f 1 (by simp))).const_mul _).aestronglyMeasurable)
    simpa only [heq] using h

end Critical2DKPZ.Polymer
