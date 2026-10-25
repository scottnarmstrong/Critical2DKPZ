/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! # Measurability of parameter integrals against random measures -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.JointConvergence

/-- A measurable family of measures with an almost surely finite compact exhaustion has a jointly
measurable nonnegative parameter integral. The finite-mass cutoffs make each approximating family
an s-finite kernel, even when the original measure family is only locally finite almost surely. -/
theorem measurable_lintegral_measurableMeasure
    {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
    (ν : Measure β) (P : Measure Ω) [SFinite ν] [SFinite P]
    (μ : Ω → Measure α) (hμ : Measurable μ)
    (K : ℕ → Set α) (hKmeas : ∀ n, MeasurableSet (K n))
    (hKmono : Monotone K) (hKcover : ⋃ n, K n = Set.univ)
    (hKfinite : ∀ᵐ ω ∂P, ∀ n, μ ω (K n) < ∞)
    (f : β → α → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    AEMeasurable (fun q : β × Ω => ∫⁻ a, f q.1 a ∂μ q.2) (ν.prod P) := by
  classical
  let κ (n m : ℕ) : Kernel (β × Ω) α := {
    toFun := fun q => if μ q.2 (K n) ≤ (m : ℝ≥0∞) then (μ q.2).restrict (K n) else 0
    measurable' := by
      apply Measure.measurable_of_measurable_coe
      intro s hs
      let hmass : Measurable (fun q : β × Ω => μ q.2 (K n)) :=
        (Measure.measurable_coe (hKmeas n)).comp (hμ.comp measurable_snd)
      have hcond : MeasurableSet {q : β × Ω | μ q.2 (K n) ≤ (m : ℝ≥0∞)} :=
        measurableSet_le hmass measurable_const
      have hrestrict : Measurable (fun q : β × Ω => (μ q.2).restrict (K n) s) := by
        have hEq : (fun q : β × Ω => (μ q.2).restrict (K n) s) =
            fun q => μ q.2 (s ∩ K n) := by
          funext q
          exact Measure.restrict_apply hs
        rw [hEq]
        exact (Measure.measurable_coe (hs.inter (hKmeas n))).comp (hμ.comp measurable_snd)
      change Measurable fun q : β × Ω =>
        (if μ q.2 (K n) ≤ (m : ℝ≥0∞) then (μ q.2).restrict (K n) else 0) s
      have hfun : (fun q : β × Ω =>
          (if μ q.2 (K n) ≤ (m : ℝ≥0∞) then (μ q.2).restrict (K n) else 0) s) =
          fun q => if μ q.2 (K n) ≤ (m : ℝ≥0∞) then (μ q.2).restrict (K n) s else 0 := by
        funext q
        split_ifs <;> rfl
      rw [hfun]
      have hzero : Measurable (fun _ : β × Ω => (0 : ℝ≥0∞)) := measurable_const
      simpa only [Measure.coe_zero] using Measurable.ite hcond hrestrict hzero
  }
  have hκfinite (n m : ℕ) : IsFiniteKernel (κ n m) := by
    refine ⟨⟨(m : ℝ≥0∞), ENNReal.natCast_lt_top m, ?_⟩⟩
    intro q
    by_cases hq : μ q.2 (K n) ≤ (m : ℝ≥0∞)
    · calc
        κ n m q Set.univ = μ q.2 (K n) := by simp [κ, hq]
        _ ≤ (m : ℝ≥0∞) := hq
    · simp [κ, hq]
  let A (n m : ℕ) (q : β × Ω) : ℝ≥0∞ :=
    ∫⁻ a, f q.1 a ∂κ n m q
  have hA (n m : ℕ) : Measurable (A n m) := by
    have hf' : Measurable (fun z : (β × Ω) × α => f z.1.1 z.2) := by
      exact hf.comp (measurable_fst.fst.prodMk measurable_snd)
    exact hf'.lintegral_kernel_prod_right' (κ := κ n m)
  let B (n : ℕ) (q : β × Ω) : ℝ≥0∞ :=
    ∫⁻ a in K n, f q.1 a ∂μ q.2
  have hB (n : ℕ) (q : β × Ω) :
      B n q = ∫⁻ a, (K n).indicator (f q.1) a ∂μ q.2 := by
    exact (lintegral_indicator (hKmeas n) (f q.1)).symm
  have hfull (q : β × Ω) :
      ∫⁻ a, f q.1 a ∂μ q.2 = ⨆ n, B n q := by
    have hpoint : (fun a : α => f q.1 a) =
        fun a => ⨆ n, (K n).indicator (f q.1) a := by
      funext a
      apply le_antisymm
      · by_cases ha : a ∈ ⋃ n, K n
        · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
          exact le_iSup_of_le n (by simp [hn])
        · simp [hKcover] at ha
      · exact iSup_le fun n => by
          by_cases ha : a ∈ K n <;> simp [ha]
    calc
      (∫⁻ a, f q.1 a ∂μ q.2) =
          ∫⁻ a, (⨆ n, (K n).indicator (f q.1) a) ∂μ q.2 := by
            rw [hpoint]
      _ = ⨆ n, ∫⁻ a, (K n).indicator (f q.1) a ∂μ q.2 :=
        lintegral_iSup
          (fun n => (hf.comp (measurable_const.prodMk measurable_id)).indicator (hKmeas n))
          (fun i j hij a => by
            by_cases hai : a ∈ K i
            · have haj : a ∈ K j := hKmono hij hai
              simp [hai, haj]
            · simp [hai])
      _ = ⨆ n, B n q := by
        congr 1
        funext n
        exact (hB n q).symm
  have hAeq (n m : ℕ) (q : β × Ω) (hq : μ q.2 (K n) ≤ (m : ℝ≥0∞)) :
      A n m q = B n q := by
    dsimp [A, B, κ]
    rw [ite_eq_left hq]
  have hAle (n m : ℕ) (q : β × Ω) : A n m q ≤ ∫⁻ a, f q.1 a ∂μ q.2 := by
    by_cases hq : μ q.2 (K n) ≤ (m : ℝ≥0∞)
    · rw [hAeq n m q hq, hB]
      exact lintegral_mono fun a => Set.indicator_le_self (K n) (f q.1) a
    · simp [A, κ, hq]
  have hgood (q : β × Ω) (hq : ∀ n, μ q.2 (K n) < ∞) :
      (∫⁻ a, f q.1 a ∂μ q.2) = ⨆ n, ⨆ m, A n m q := by
    rw [hfull]
    apply le_antisymm
    · apply iSup_le
      intro n
      obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ne_top_of_lt (hq n))
      have hle : μ q.2 (K n) ≤ (m : ℝ≥0∞) := hm.le
      calc
        B n q = A n m q := (hAeq n m q hle).symm
        _ ≤ ⨆ m, A n m q := le_iSup_of_le m le_rfl
        _ ≤ ⨆ n, ⨆ m, A n m q := le_iSup_of_le n le_rfl
    · apply iSup_le
      intro n
      apply iSup_le
      intro m
      calc
        A n m q ≤ ∫⁻ a, f q.1 a ∂μ q.2 := hAle n m q
        _ = ⨆ n, B n q := hfull q
  have hmeas : Measurable (fun q : β × Ω => ⨆ n, ⨆ m, A n m q) := by
    exact Measurable.iSup fun n => Measurable.iSup fun m => hA n m
  have hgoodSet : MeasurableSet {q : β × Ω | ∀ n, μ q.2 (K n) < ∞} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      (measurableSet_lt ((Measure.measurable_coe (hKmeas n)).comp
        (hμ.comp measurable_snd)) measurable_const)
  have hgoodAE : ∀ᵐ q : β × Ω ∂(ν.prod P), ∀ n, μ q.2 (K n) < ∞ :=
    (Measure.ae_prod_iff_ae_ae hgoodSet).2 (Filter.Eventually.of_forall fun _ => hKfinite)
  have hae : (fun q : β × Ω => ∫⁻ a, f q.1 a ∂μ q.2) =ᵐ[ν.prod P]
      fun q => ⨆ n, ⨆ m, A n m q := by
    filter_upwards [hgoodAE] with q hq
    exact hgood q hq
  exact hmeas.aemeasurable.congr hae.symm

end Critical2DKPZ.JointConvergence

end
