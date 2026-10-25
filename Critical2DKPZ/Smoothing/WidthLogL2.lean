/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ProfileLogL2
public import Critical2DKPZ.Smoothing.ProfileKernelPerturbation
public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.Tactic

/-! # Logarithmic stability under finite walk-kernel width changes -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.Smoothing

/-- For a fixed start and horizon and a bounded positive terminal weight, the `L²` distance between two smoothed profile logarithms is bounded by the profile difference and inverse moments. -/
theorem eLpNorm_log_walkKernel_profile_difference_le (β : ℝ) (a T p q : ℕ) (x : Site)
    (f : Site → ℝ) (H : ℝ)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) :
    eLpNorm (fun ω =>
      Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) f ω) -
      Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) f ω)) 2 disorderLaw ≤
      ENNReal.ofReal logHolderConstant *
        eLpNorm (fun ω =>
          profileP2Fun β a (a + T) (fun w => srwKernel (2 * q) (w - x)) f ω -
            profileP2Fun β a (a + T) (fun w => srwKernel (2 * p) (w - x)) f ω)
          2 disorderLaw ^ ((1 : ℝ) / 3) *
        (eLpNorm (fun ω =>
            (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * q) (w - x)) f ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3) +
          eLpNorm (fun ω =>
            (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * p) (w - x)) f ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3)) := by
  classical
  let νq : Site → ℝ := fun w => srwKernel (2 * q) (w - x)
  let νp : Site → ℝ := fun w => srwKernel (2 * p) (w - x)
  let A : Finset Site := Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)
  have hνqA : ∀ w ∉ A, νq w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w (by
      intro hwq
      exact hw (Finset.mem_union_right _ hwq))
  have hνpA : ∀ w ∉ A, νp w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w (by
      intro hwp
      exact hw (Finset.mem_union_left _ hwp))
  have hνq0 : ∀ w, 0 ≤ νq w := fun w => Polymer.kernel_nonneg (2 * q) (w - x)
  have hνp0 : ∀ w, 0 ≤ νp w := fun w => Polymer.kernel_nonneg (2 * p) (w - x)
  have hνq1 : ∑ w ∈ A, νq w = 1 := by
    dsimp [νq, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * q), srwKernel (2 * q) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * q) x
  have hνp1 : ∑ w ∈ A, νp w = 1 := by
    dsimp [νp, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * p), srwKernel (2 * p) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * p) x
  have hνqpos : ∃ w ∈ A, 0 < νq w := by
    have hsum : 0 < ∑ w ∈ A, νq w := by rw [hνq1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hνq0 w)).mp hsum
  have hνppos : ∃ w ∈ A, 0 < νp w := by
    have hsum : 0 < ∑ w ∈ A, νp w := by rw [hνp1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hνp0 w)).mp hsum
  let X : Disorder → ℝ := fun ω => profileP2Fun β a (a + T) νq f ω
  let Y : Disorder → ℝ := fun ω => profileP2Fun β a (a + T) νp f ω
  let X₀ : Disorder → ℝ := fun ω => profileP2Fun β a (a + T) νq (fun _ => 1) ω
  let Y₀ : Disorder → ℝ := fun ω => profileP2Fun β a (a + T) νp (fun _ => 1) ω
  have hXpos (ω : Disorder) : 0 < X ω := by
    exact profileP2Fun_pos_terminal β a (a + T) νq f A hνqA hνq0 hνqpos
      (fun z => (hf z).1) ω
  have hYpos (ω : Disorder) : 0 < Y ω := by
    exact profileP2Fun_pos_terminal β a (a + T) νp f A hνpA hνp0 hνppos
      (fun z => (hf z).1) ω
  have hX₀pos (ω : Disorder) : 0 < X₀ ω := by
    exact OnePoint.profileP2Fun_pos_of_normalized β a (a + T) νq A hνqA hνq0 hνq1 ω
  have hY₀pos (ω : Disorder) : 0 < Y₀ ω := by
    exact OnePoint.profileP2Fun_pos_of_normalized β a (a + T) νp A hνpA hνp0 hνp1 ω
  have hXmeas : Measurable X := by
    change Measurable (fun ω => profileP2Fun β a (a + T) (νq) f ω)
    exact measurable_profileP2Fun_param β a (a + T) f (fun _ => measurable_const) measurable_id
  have hYmeas : Measurable Y := by
    change Measurable (fun ω => profileP2Fun β a (a + T) (νp) f ω)
    exact measurable_profileP2Fun_param β a (a + T) f (fun _ => measurable_const) measurable_id
  have hX₀inv : Integrable (fun ω => (X₀ ω)⁻¹) disorderLaw := by
    have h := OnePoint.integrable_rpow_profileP2Fun β a (a + T) νq A hνqA hνq0 hνq1 (-1)
    have heq : (fun ω => profileP2Fun β a (a + T) νq (fun _ => 1) ω ^ (-1 : ℝ)) =
        fun ω => (X₀ ω)⁻¹ := by
      funext ω
      rw [Real.rpow_neg_one]
    rw [heq] at h
    exact h
  have hY₀inv : Integrable (fun ω => (Y₀ ω)⁻¹) disorderLaw := by
    have h := OnePoint.integrable_rpow_profileP2Fun β a (a + T) νp A hνpA hνp0 hνp1 (-1)
    have heq : (fun ω => profileP2Fun β a (a + T) νp (fun _ => 1) ω ^ (-1 : ℝ)) =
        fun ω => (Y₀ ω)⁻¹ := by
      funext ω
      rw [Real.rpow_neg_one]
    rw [heq] at h
    exact h
  have hXlogBound (ω : Disorder) :=
    FutureProfiles.abs_log_profileP2Fun_sub_le β a (a + T) νq A hνqA hνq0 hνq1 f H hf ω
  have hYlogBound (ω : Disorder) :=
    FutureProfiles.abs_log_profileP2Fun_sub_le β a (a + T) νp A hνpA hνp0 hνp1 f H hf ω
  have hXinvPoint (ω : Disorder) :
      (X ω)⁻¹ ≤ Real.exp H * (X₀ ω)⁻¹ := by
    have hlog : Real.log (X₀ ω) - Real.log (X ω) ≤ H := by
      have hb := abs_le.mp (hXlogBound ω)
      linarith
    have hflatle : X₀ ω ≤ Real.exp H * X ω := by
      have hexp : Real.exp (Real.log (X₀ ω)) ≤ Real.exp (H + Real.log (X ω)) :=
        Real.exp_le_exp.mpr (by linarith [hlog])
      rw [Real.exp_log (hX₀pos ω), Real.exp_add, Real.exp_log (hXpos ω)] at hexp
      simpa [mul_comm] using hexp
    have hdiv : X₀ ω / X ω ≤ Real.exp H := (div_le_iff₀ (hXpos ω)).2 hflatle
    have hmul : (X ω)⁻¹ * X₀ ω ≤ Real.exp H := by
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    exact (le_div_iff₀ (hX₀pos ω)).2 (by simpa [div_eq_mul_inv, mul_comm] using hmul)
  have hYinvPoint (ω : Disorder) :
      (Y ω)⁻¹ ≤ Real.exp H * (Y₀ ω)⁻¹ := by
    have hlog : Real.log (Y₀ ω) - Real.log (Y ω) ≤ H := by
      have hb := abs_le.mp (hYlogBound ω)
      linarith
    have hflatle : Y₀ ω ≤ Real.exp H * Y ω := by
      have hexp : Real.exp (Real.log (Y₀ ω)) ≤ Real.exp (H + Real.log (Y ω)) :=
        Real.exp_le_exp.mpr (by linarith [hlog])
      rw [Real.exp_log (hY₀pos ω), Real.exp_add, Real.exp_log (hYpos ω)] at hexp
      simpa [mul_comm] using hexp
    have hdiv : Y₀ ω / Y ω ≤ Real.exp H := (div_le_iff₀ (hYpos ω)).2 hflatle
    have hmul : (Y ω)⁻¹ * Y₀ ω ≤ Real.exp H := by
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    exact (le_div_iff₀ (hY₀pos ω)).2 (by simpa [div_eq_mul_inv, mul_comm] using hmul)
  have hXinv : Integrable (fun ω => (X ω)⁻¹) disorderLaw := by
    have hmajor : Integrable (fun ω => Real.exp H * (X₀ ω)⁻¹) disorderLaw :=
      hX₀inv.const_mul (Real.exp H)
    refine hmajor.mono' (hXmeas.inv.aestronglyMeasurable) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hXpos ω).le)]
    have hmajor0 : 0 ≤ Real.exp H * (X₀ ω)⁻¹ :=
      mul_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr (hX₀pos ω).le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor0] using hXinvPoint ω
  have hYinv : Integrable (fun ω => (Y ω)⁻¹) disorderLaw := by
    have hmajor : Integrable (fun ω => Real.exp H * (Y₀ ω)⁻¹) disorderLaw :=
      hY₀inv.const_mul (Real.exp H)
    refine hmajor.mono' (hYmeas.inv.aestronglyMeasurable) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hYpos ω).le)]
    have hmajor0 : 0 ≤ Real.exp H * (Y₀ ω)⁻¹ :=
      mul_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr (hY₀pos ω).le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor0] using hYinvPoint ω
  have hdiff := integral_profileP2Fun_initial_difference_sq_le β a T νq νp A
    hνqA hνpA f (Real.exp H) (Real.exp_nonneg H) (by
      intro z
      rw [abs_of_pos (hf z).1]
      calc
        f z = Real.exp (Real.log (f z)) := (Real.exp_log (hf z).1).symm
        _ ≤ Real.exp H := Real.exp_le_exp.mpr (abs_le.mp (hf z).2).2)
  have hDsq : Integrable (fun ω => (X ω - Y ω) ^ 2) disorderLaw := by
    simpa [X, Y] using hdiff.1
  apply eLpNorm_log_sub_le_of_sq_diff_inv disorderLaw X Y hXmeas hYmeas hXpos hYpos
    hDsq hXinv hYinv

/-- Quantitative form of `eLpNorm_log_walkKernel_profile_difference_le`, with the first-collision
bound for the squared profile difference made explicit. -/
theorem eLpNorm_log_walkKernel_profile_difference_le_collision (β : ℝ) (a T p q : ℕ)
    (x : Site) (f : Site → ℝ) (F H : ℝ) (hF : 0 ≤ F)
    (hfb : ∀ z, |f z| ≤ F)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) :
    eLpNorm (fun ω =>
      Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) f ω) -
      Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) f ω)) 2 disorderLaw ≤
      ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 *
          (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
            |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
          (1 + ∑ r ∈ Finset.Icc 1 T,
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                ((r : ℝ) + 1)))) ^ ((1 : ℝ) / 3) *
        (eLpNorm (fun ω =>
            (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * q) (w - x)) f ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3) +
          eLpNorm (fun ω =>
            (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * p) (w - x)) f ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3)) := by
  classical
  let νq : Site → ℝ := fun w => srwKernel (2 * q) (w - x)
  let νp : Site → ℝ := fun w => srwKernel (2 * p) (w - x)
  let A : Finset Site := Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)
  let X : Disorder → ℝ := fun ω => profileP2Fun β a (a + T) νq f ω
  let Y : Disorder → ℝ := fun ω => profileP2Fun β a (a + T) νp f ω
  have hνqA : ∀ w ∉ A, νq w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w (by
      intro hwq
      exact hw (Finset.mem_union_right _ hwq))
  have hνpA : ∀ w ∉ A, νp w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w (by
      intro hwp
      exact hw (Finset.mem_union_left _ hwp))
  have hνq0 : ∀ w, 0 ≤ νq w := fun w => Polymer.kernel_nonneg (2 * q) (w - x)
  have hνp0 : ∀ w, 0 ≤ νp w := fun w => Polymer.kernel_nonneg (2 * p) (w - x)
  have hνq1 : ∑ w ∈ A, νq w = 1 := by
    dsimp [νq, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * q), srwKernel (2 * q) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * q) x
  have hνp1 : ∑ w ∈ A, νp w = 1 := by
    dsimp [νp, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * p), srwKernel (2 * p) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * p) x
  have hνqpos : ∃ w ∈ A, 0 < νq w := by
    have hsum : 0 < ∑ w ∈ A, νq w := by rw [hνq1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hνq0 w)).mp hsum
  have hνppos : ∃ w ∈ A, 0 < νp w := by
    have hsum : 0 < ∑ w ∈ A, νp w := by rw [hνp1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hνp0 w)).mp hsum
  have hXpos (ω : Disorder) : 0 < X ω :=
    profileP2Fun_pos_terminal β a (a + T) νq f A hνqA hνq0 hνqpos
      (fun z => (hf z).1) ω
  have hYpos (ω : Disorder) : 0 < Y ω :=
    profileP2Fun_pos_terminal β a (a + T) νp f A hνpA hνp0 hνppos
      (fun z => (hf z).1) ω
  have hXmeas : Measurable X := by
    exact measurable_profileP2Fun_param β a (a + T) f (fun _ => measurable_const) measurable_id
  have hYmeas : Measurable Y := by
    exact measurable_profileP2Fun_param β a (a + T) f (fun _ => measurable_const) measurable_id
  have hdiff := integral_profileP2Fun_initial_difference_sq_le β a T νq νp A
    hνqA hνpA f F hF hfb
  have hDsq : Integrable (fun ω => (X ω - Y ω) ^ 2) disorderLaw := by
    simpa [X, Y] using hdiff.1
  have hDmem : MemLp (fun ω => X ω - Y ω) 2 disorderLaw := by
    apply (memLp_two_iff_integrable_sq (hXmeas.sub hYmeas).aestronglyMeasurable).2
    simpa [Pi.sub_apply, X, Y] using hDsq
  have hDnorm : eLpNorm (fun ω => X ω - Y ω) 2 disorderLaw ≤
      ENNReal.ofReal (Real.sqrt (F ^ 2 *
        (∑ w ∈ A, |νq w - νp w|) ^ 2 *
          (1 + ∑ r ∈ Finset.Icc 1 T,
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                ((r : ℝ) + 1)))) := by
    apply eLpNorm_le_of_integral_sq_le disorderLaw hDmem
    simpa [X, Y] using hdiff.2
  have hlog := eLpNorm_log_walkKernel_profile_difference_le β a T p q x f H hf
  calc
    _ ≤ ENNReal.ofReal logHolderConstant *
          eLpNorm (fun ω => X ω - Y ω) 2 disorderLaw ^ ((1 : ℝ) / 3) *
          (eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3) +
            eLpNorm (fun ω => (Y ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3)) := by
      simpa [X, Y] using hlog
    _ ≤ _ := by
      gcongr

end Critical2DKPZ.Smoothing

end
