/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CenteredArrayCLT
public import Critical2DKPZ.Extensions.ScaleLimit.SlutskyTools
import Mathlib.Tactic

/-! # Identification of subsequential centring and variance limits

A Gaussian limit of the original centered field identifies both parameters of
any subsequential Gaussian limit of the bounded independent partial sums.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Any limiting normalized variance and centring drift must be one and zero. -/
theorem centring_parameters_of_limits {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y P) (hm : ∀ i, AEMeasurable (Y i) P)
    (K : ℝ) (hK : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ K)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Integrable (F n) P)
    (herror : TendstoInMeasure P
      (fun n ω => (F n ω - partialSumRange Y n ω) / a n) atTop (fun _ => 0))
    (hclt : TendstoInDistribution
      (fun n ω => (F n ω - ∫ ω', F n ω' ∂P) / a n)
      atTop id (fun _ => P) (gaussianReal 0 1))
    (u : ℕ → ℕ) (hu : Tendsto u atTop atTop) (v : ℝ≥0) (d : ℝ)
    (hv : Tendsto (fun n => variance (partialSumRange Y (u n)) P / a (u n) ^ 2)
      atTop (𝓝 (v : ℝ)))
    (hd : Tendsto (fun n => ((∫ ω, F (u n) ω ∂P) -
      ∫ ω, partialSumRange Y (u n) ω ∂P) / a (u n)) atTop (𝓝 d)) :
    v = 1 ∧ d = 0 := by
  have hS (n : ℕ) : MemLp (partialSumRange Y n) 2 P :=
    memLp_finsetSum _ (fun i _ => memLp_of_ae_abs_le P (hm i) K (hK i) 2)
  have hbase : TendstoInDistribution
      (fun n ω => (partialSumRange Y (u n) ω -
        ∫ ω', partialSumRange Y (u n) ω' ∂P) / a (u n))
      atTop id (fun _ => P) (gaussianReal 0 v) := by
    exact tendstoInDistribution_centered_bounded_sums P atTop Y hind hm K hK
      u (fun n => a (u n)) (ha.comp hu) v hv
  have hshift := hbase.add_of_tendstoInMeasure_const
    (tendstoInMeasure_const_of_tendsto P hd.neg) (fun _ => measurable_const.aemeasurable)
  have herr := herror.comp hu
  have hshifted := hshift.add_of_tendstoInMeasure_const herr (fun n =>
    (((hF (u n)).aemeasurable.sub (hS (u n)).aemeasurable).div_const _))
  have hsource (n : ℕ) :
      (fun ω => ((partialSumRange Y (u n) ω -
        ∫ ω', partialSumRange Y (u n) ω' ∂P) / a (u n) +
        -(((∫ ω', F (u n) ω' ∂P) - ∫ ω', partialSumRange Y (u n) ω' ∂P) / a (u n))) +
        (F (u n) ω - partialSumRange Y (u n) ω) / a (u n)) =
      (fun ω => (F (u n) ω - ∫ ω', F (u n) ω' ∂P) / a (u n)) := by
    funext ω
    ring
  have hshifted' : TendstoInDistribution
      (fun n ω => (F (u n) ω - ∫ ω', F (u n) ω' ∂P) / a (u n))
      atTop (fun y : ℝ => y - d) (fun _ => P) (gaussianReal 0 v) := by
    refine hshifted.congr (fun n => Eventually.of_forall (fun ω => ?_)) ?_
    · exact congrFun (hsource n) ω
    · filter_upwards [] with y
      simp only [id_eq, add_zero, sub_eq_add_neg]
  have horiginal : TendstoInDistribution
      (fun n ω => (F (u n) ω - ∫ ω', F (u n) ω' ∂P) / a (u n))
      atTop id (fun _ => P) (gaussianReal 0 1) :=
    ⟨fun n => hclt.forall_aemeasurable (u n), hclt.aemeasurable_limit, hclt.tendsto.comp hu⟩
  have hlaw := tendstoInDistribution_unique _ horiginal hshifted'
  rw [Measure.map_id] at hlaw
  have hmap : (gaussianReal 0 v).map (fun y : ℝ => y - d) = gaussianReal (-d) v := by
    simpa only [sub_eq_add_neg, zero_add] using
      (gaussianReal_map_add_const (-d) :
        (gaussianReal 0 v).map (fun y => y + -d) = gaussianReal (0 + -d) v)
  rw [hmap] at hlaw
  obtain ⟨hd0, hv1⟩ := gaussianReal_ext_iff.mp hlaw
  exact ⟨hv1.symm, by linarith⟩

end Critical2DKPZ.Extensions.ScaleLimit
