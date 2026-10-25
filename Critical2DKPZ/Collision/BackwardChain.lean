/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.BackwardRenewal
import Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Critical2DKPZ.SHF.DeltaBose.CausalComposition
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # Iterated backward renewal bounds -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open MeasureTheory
open Set
open scoped ENNReal

private def piLastEquiv (m : ℕ) :
    (Fin (m + 1) → ℝ × ℝ) ≃ᵐ (Fin m → ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ × ℝ) (Fin.last m)).trans
    MeasurableEquiv.prodComm

private theorem piLastEquiv_symm_castSucc (m : ℕ) (q : Fin m → ℝ × ℝ)
    (z : ℝ × ℝ) (j : Fin m) :
    (piLastEquiv m).symm (q, z) j.castSucc = q j := by
  change (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (m + 1) => ℝ × ℝ) (Fin.last m)).symm (z, q) j.castSucc = q j
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

private theorem piLastEquiv_symm_last (m : ℕ) (q : Fin m → ℝ × ℝ)
    (z : ℝ × ℝ) :
    (piLastEquiv m).symm (q, z) (Fin.last m) = z := by
  change (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (m + 1) => ℝ × ℝ) (Fin.last m)).symm (z, q) (Fin.last m) = z
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

private theorem measurePreserving_piLastEquiv (m : ℕ)
    (μ : Fin (m + 1) → Measure (ℝ × ℝ)) [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (piLastEquiv m)
      (Measure.pi μ)
      ((Measure.pi (fun j : Fin m => μ j.castSucc)).prod (μ (Fin.last m))) := by
  have hsplit : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ × ℝ) (Fin.last m))
      (Measure.pi μ)
      ((μ (Fin.last m)).prod
        (Measure.pi (fun j : Fin m => μ ((Fin.last m).succAbove j)))) :=
    measurePreserving_piFinSuccAbove μ (Fin.last m)
  have hswap : MeasurePreserving Prod.swap
      ((μ (Fin.last m)).prod
        (Measure.pi (fun j : Fin m => μ ((Fin.last m).succAbove j))))
      ((Measure.pi (fun j : Fin m => μ ((Fin.last m).succAbove j))).prod
        (μ (Fin.last m))) := Measure.measurePreserving_swap
  have hcomp := hswap.comp hsplit
  change MeasurePreserving
    (Prod.swap ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ × ℝ) (Fin.last m)))
    (Measure.pi μ)
    ((Measure.pi (fun j : Fin m => μ j.castSucc)).prod (μ (Fin.last m)))
  simpa [Fin.succAbove_last] using hcomp

private theorem lintegral_piLast {m : ℕ} {F : (Fin (m + 1) → ℝ × ℝ) → ℝ≥0∞}
    (μ : Fin (m + 1) → Measure (ℝ × ℝ)) [∀ j, SigmaFinite (μ j)]
    (hF : Measurable F) :
    (∫⁻ p : Fin (m + 1) → ℝ × ℝ, F p ∂Measure.pi μ) =
      ∫⁻ q : Fin m → ℝ × ℝ,
        (∫⁻ z : ℝ × ℝ, F ((piLastEquiv m).symm (q, z)) ∂μ (Fin.last m))
          ∂(Measure.pi (fun j : Fin m => μ j.castSucc)) := by
  have he := (measurePreserving_piLastEquiv m μ).symm.lintegral_comp hF
  calc
    (∫⁻ p : Fin (m + 1) → ℝ × ℝ, F p ∂Measure.pi μ) =
        ∫⁻ q : (Fin m → ℝ × ℝ) × (ℝ × ℝ),
          F ((piLastEquiv m).symm q)
            ∂((Measure.pi (fun j : Fin m => μ j.castSucc)).prod (μ (Fin.last m))) := he.symm
    _ = ∫⁻ q : Fin m → ℝ × ℝ,
        (∫⁻ z : ℝ × ℝ, F ((piLastEquiv m).symm (q, z)) ∂μ (Fin.last m))
          ∂(Measure.pi (fun j : Fin m => μ j.castSucc)) :=
      lintegral_prod _ (hF.comp (piLastEquiv m).symm.measurable).aemeasurable

private def backwardTriangle (S T : ℝ) : Set (ℝ × ℝ) :=
  {p | S < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}

private def backwardChainDomain {n : ℕ} (S T : Fin n → ℝ) :
    Set (Fin n → ℝ × ℝ) :=
  Set.univ.pi (fun j => backwardTriangle (S j) (T j))

private def backwardChainMeasures {n : ℕ} (S T : Fin n → ℝ) :
    Fin n → Measure (ℝ × ℝ) :=
  fun j => volume.restrict (backwardTriangle (S j) (T j))

private instance backwardChainMeasures_sigmaFinite {n : ℕ} (S T : Fin n → ℝ) :
    ∀ j, SigmaFinite (backwardChainMeasures S T j) := by
  intro j
  dsimp [backwardChainMeasures]
  infer_instance

private theorem measurableSet_backwardTriangle (S T : ℝ) :
    MeasurableSet (backwardTriangle S T) := by
  dsimp [backwardTriangle]
  measurability

private theorem backwardChainDomain_eq {n : ℕ} (S T : Fin n → ℝ) :
    {p : Fin n → ℝ × ℝ | ∀ j, S j < (p j).1 ∧ (p j).1 < (p j).2 ∧ (p j).2 ≤ T j} =
      backwardChainDomain S T := by
  ext p
  simp [backwardChainDomain, backwardTriangle]

private theorem lintegral_backwardChainDomain {n : ℕ} {S T : Fin n → ℝ}
    {f : (Fin n → ℝ × ℝ) → ℝ≥0∞} :
    ∫⁻ p : Fin n → ℝ × ℝ in backwardChainDomain S T, f p =
      ∫⁻ p : Fin n → ℝ × ℝ, f p ∂Measure.pi (backwardChainMeasures S T) := by
  change ∫⁻ p, f p ∂(volume.restrict (Set.univ.pi fun j =>
      backwardTriangle (S j) (T j))) = _
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl

private def backwardTailDensity {m : ℕ} (ϑ τ : ℝ)
    (p : Fin (m + 1) → ℝ × ℝ) : ℝ :=
  (τ / ((p 0).1 * ((p 0).1 - τ))) *
    (∏ j, DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant)
      ((p j).2 - (p j).1)) *
    ∏ j : Fin m,
      (p j.castSucc).2 / ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))



private theorem lintegral_backwardTriangle_le {f : ℝ × ℝ → ℝ≥0∞}
    (hf : Measurable f) {S T : ℝ} :
    ∫⁻ p in backwardTriangle S T, f p =
      ∫⁻ x in Ioo S T, ∫⁻ y in Ioo x T, f (x, y) := by
  have htri : MeasurableSet (backwardTriangle S T) := by
    dsimp [backwardTriangle]
    measurability
  have hfun (x y : ℝ) : (backwardTriangle S T).indicator f (x, y) =
      if x ∈ Ioo S T then (Ioc x T).indicator (fun y => f (x, y)) y else 0 := by
    by_cases hx : x ∈ Ioo S T
    · by_cases hy : y ∈ Ioc x T
      · have hxy : S < x ∧ x < y ∧ y ≤ T := ⟨hx.1, hy.1, hy.2⟩
        simp only [Set.indicator_apply]
        simp [backwardTriangle, hxy, hx, hy]
      · have hxy : ¬(S < x ∧ x < y ∧ y ≤ T) := by
          intro h
          exact hy ⟨h.2.1, h.2.2⟩
        simp only [Set.indicator_apply]
        simp [backwardTriangle, hxy, hx, hy]
    · have hxy : ¬(S < x ∧ x < y ∧ y ≤ T) := by
        intro h
        exact hx ⟨h.1, lt_of_lt_of_le h.2.1 h.2.2⟩
      simp only [Set.indicator_apply]
      simp [backwardTriangle, hxy, hx]
  have hinner (x : ℝ) :
      ∫⁻ y, (Ioc x T).indicator (fun y => f (x, y)) y =
        ∫⁻ y in Ioo x T, f (x, y) := by
    rw [lintegral_indicator measurableSet_Ioc]
    rw [← restrict_Ioo_eq_restrict_Ioc]
  calc
    _ = ∫⁻ p, (backwardTriangle S T).indicator f p ∂(volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      rw [lintegral_indicator htri]
    _ = ∫⁻ x, ∫⁻ y, (backwardTriangle S T).indicator f (x, y) ∂volume ∂volume :=
      lintegral_prod _ ((hf.indicator htri).aemeasurable)
    _ = ∫⁻ x, if x ∈ Ioo S T then ∫⁻ y in Ioo x T, f (x, y) else 0 := by
      apply lintegral_congr
      intro x
      rw [show (fun y => (backwardTriangle S T).indicator f (x, y)) =
          fun y => if x ∈ Ioo S T then (Ioc x T).indicator (fun y => f (x, y)) y else 0 by
        funext y
        exact hfun x y]
      by_cases hx : x ∈ Ioo S T <;> simp [hx, hinner]
    _ = ∫⁻ x in Ioo S T, ∫⁻ y in Ioo x T, f (x, y) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro x
      simp only [Set.indicator, mem_Ioo]

private theorem lintegral_backwardTriangle_eq_open {f : ℝ × ℝ → ℝ≥0∞}
    (hf : Measurable f) {S T : ℝ} :
    ∫⁻ p in backwardTriangle S T, f p =
      ∫⁻ p : ℝ × ℝ in {p | S < p.1 ∧ p.1 < p.2 ∧ p.2 < T}, f p := by
  rw [lintegral_backwardTriangle_le hf, lintegral_openTriangle_eq hf]

private theorem lintegral_backwardBlock_to_U_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ τ U S T : ℝ,
      0 < τ → τ < U → U ≤ S → 4 * S ≤ T → T < 1 →
      ∫⁻ p in backwardTriangle S T,
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
            (τ / (p.1 * (p.1 - τ))) * backwardWeight T p.2) ≤
        ENNReal.ofReal (C / (-Real.log T) * (τ / S) * backwardWeight U τ) := by
  obtain ⟨C, hC, hblock⟩ := lintegral_backwardBlock_le A
  refine ⟨C, hC, ?_⟩
  intro ϑ hϑ τ U S T hτ hτU hUS hblock' hT
  have hτS : τ < S := lt_of_lt_of_le hτU hUS
  have hS : 0 < S := lt_trans hτ hτS
  have hweight : backwardWeight S τ ≤ backwardWeight U τ :=
    backwardWeight_antitone_horizon hτ.le hτU hUS
  have hscalar : Measurable (fun t : ℝ => DeltaBose.scalarDensity
      (ϑ - Real.eulerMascheroniConstant) t) :=
    DeltaBose.measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hback : Measurable (backwardWeight T) := by
    change Measurable (fun t : ℝ => Real.log (2 * T) - Real.log (T - t))
    fun_prop
  have hratio : Measurable (fun p : ℝ × ℝ => τ / (p.1 * (p.1 - τ))) := by
    fun_prop
  have hf : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
        (τ / (p.1 * (p.1 - τ))) * backwardWeight T p.2)) := by
    exact (hscalar.comp (measurable_snd.sub measurable_fst)).mul hratio |>.mul
      (hback.comp measurable_snd) |>.ennreal_ofReal
  rw [lintegral_backwardTriangle_eq_open hf]
  calc
    _ ≤ ENNReal.ofReal (C / (-Real.log T) * (τ / S) * backwardWeight S τ) :=
      hblock ϑ hϑ τ S T hτ hτS hblock' hT
    _ ≤ ENNReal.ofReal (C / (-Real.log T) * (τ / S) * backwardWeight U τ) := by
      apply ENNReal.ofReal_le_ofReal
      have hTpos : 0 < T := by linarith [hS, hblock']
      have hlog : 0 < -Real.log T := by
        have h := Real.log_lt_log hTpos hT
        rw [Real.log_one] at h
        linarith
      have hnonneg : 0 ≤ C / (-Real.log T) * (τ / S) := by positivity
      exact mul_le_mul_of_nonneg_left hweight hnonneg

private theorem ae_snd_ne_volume (T : ℝ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ T := by
  have hprod : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.2 ≠ T := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with x
    exact volume.ae_ne T
  change ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.2 ≠ T
  exact hprod

private theorem ae_backwardChain_y_lt {n : ℕ} (S T : Fin n → ℝ) :
    ∀ᵐ p : Fin n → ℝ × ℝ ∂Measure.pi (backwardChainMeasures S T),
      ∀ j, (p j).2 < T j := by
  have hcoord : ∀ j, ∀ᵐ z ∂backwardChainMeasures S T j, z.2 < T j := by
    intro j
    change ∀ᵐ z ∂volume.restrict (backwardTriangle (S j) (T j)), z.2 < T j
    rw [ae_restrict_iff' (measurableSet_backwardTriangle (S j) (T j))]
    filter_upwards [ae_snd_ne_volume (T j)] with z hz hzmem
    dsimp [backwardTriangle] at hzmem
    exact lt_of_le_of_ne hzmem.2.2 hz
  apply (Filter.eventually_all.2 ?_)
  intro j
  exact (MeasureTheory.Measure.tendsto_eval_ae_ae
    (μ := backwardChainMeasures S T) (i := j)).eventually (hcoord j)

private theorem ae_mem_backwardChainDomain {n : ℕ} (S T : Fin n → ℝ) :
    ∀ᵐ p : Fin n → ℝ × ℝ ∂Measure.pi (backwardChainMeasures S T),
      p ∈ backwardChainDomain S T := by
  have hcoord : ∀ j, ∀ᵐ z ∂backwardChainMeasures S T j,
      z ∈ backwardTriangle (S j) (T j) := by
    intro j
    change ∀ᵐ z ∂volume.restrict (backwardTriangle (S j) (T j)),
      z ∈ backwardTriangle (S j) (T j)
    exact ae_restrict_mem (measurableSet_backwardTriangle (S j) (T j))
  have h := Filter.eventually_all.2 fun j =>
    (MeasureTheory.Measure.tendsto_eval_ae_ae
      (μ := backwardChainMeasures S T) (i := j)).eventually (hcoord j)
  filter_upwards [h] with p hp
  change p ∈ Set.univ.pi (fun j => backwardTriangle (S j) (T j))
  simpa using hp

private def backwardInitialDensity {m : ℕ} (ϑ : ℝ)
    (p : Fin (m + 1) → ℝ × ℝ) : ℝ :=
  (p 0).1⁻¹ *
    (∏ j, DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant)
      ((p j).2 - (p j).1)) *
    ∏ j : Fin m,
      (p j.castSucc).2 / ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))

private theorem measurable_backwardInitialDensity {m : ℕ} (ϑ : ℝ) :
    Measurable (backwardInitialDensity (m := m) ϑ) := by
  have hscalar : Measurable (fun t : ℝ =>
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t) :=
    DeltaBose.measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hfirst : Measurable (fun p : Fin (m + 1) → ℝ × ℝ => (p 0).1⁻¹) := by
    fun_prop
  have hG : Measurable (fun p : Fin (m + 1) → ℝ × ℝ =>
      ∏ j, DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant)
        ((p j).2 - (p j).1)) := by
    apply Finset.measurable_fun_prod Finset.univ
    intro j _
    exact hscalar.comp ((measurable_snd.comp (measurable_pi_apply j)).sub
      (measurable_fst.comp (measurable_pi_apply j)))
  have hE : Measurable (fun p : Fin (m + 1) → ℝ × ℝ =>
      ∏ j : Fin m, (p j.castSucc).2 /
        ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))) := by
    apply Finset.measurable_fun_prod Finset.univ
    intro j _
    fun_prop
  exact (hfirst.mul hG).mul hE

private theorem measurable_backwardInitialWeightedDensity {m : ℕ} (ϑ : ℝ)
    (T : Fin (m + 1) → ℝ) :
    Measurable (fun p : Fin (m + 1) → ℝ × ℝ =>
      backwardInitialDensity ϑ p * backwardWeight (T (Fin.last m)) (p (Fin.last m)).2) := by
  have hback : Measurable (backwardWeight (T (Fin.last m))) := by
    change Measurable (fun t : ℝ =>
      Real.log (2 * T (Fin.last m)) - Real.log (T (Fin.last m) - t))
    fun_prop
  exact (measurable_backwardInitialDensity ϑ).mul
    (hback.comp (measurable_snd.comp (measurable_pi_apply (Fin.last m))))

private theorem backwardInitialDensity_split {m : ℕ} (ϑ : ℝ)
    (q : Fin (m + 1) → ℝ × ℝ) (z : ℝ × ℝ) :
    backwardInitialDensity ϑ ((piLastEquiv (m + 1)).symm (q, z)) =
      backwardInitialDensity ϑ q *
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (z.2 - z.1) *
          ((q (Fin.last m)).2 / (z.1 * (z.1 - (q (Fin.last m)).2)))) := by
  have hzero : (piLastEquiv (m + 1)).symm (q, z) 0 = q 0 := by
    simpa only [Fin.castSucc_zero] using piLastEquiv_symm_castSucc (m + 1) q z 0
  simp only [backwardInitialDensity, Fin.prod_univ_castSucc,
    hzero, ← Fin.castSucc_succ, Fin.succ_last,
    piLastEquiv_symm_castSucc, piLastEquiv_symm_last]
  ring

private theorem backwardInitialDensity_nonneg {m : ℕ} {ϑ : ℝ}
    {S T : Fin (m + 1) → ℝ} {p : Fin (m + 1) → ℝ × ℝ}
    (hS : ∀ j, 0 < S j)
    (hsep : ∀ j : Fin m, T j.castSucc ≤ S j.succ)
    (hp : p ∈ backwardChainDomain S T) : 0 ≤ backwardInitialDensity ϑ p := by
  have hp' (j) : S j < (p j).1 ∧ (p j).1 < (p j).2 ∧ (p j).2 ≤ T j :=
    hp j (Set.mem_univ j)
  unfold backwardInitialDensity
  apply mul_nonneg
  · apply mul_nonneg
    · exact inv_nonneg.2 (lt_trans (hS 0) (hp' 0).1).le
    · apply Finset.prod_nonneg
      intro j _
      exact (DeltaBose.scalarDensity_pos _ (sub_pos.2 (hp' j).2.1)).le
  · apply Finset.prod_nonneg
    intro j _
    have hy : 0 < (p j.castSucc).2 :=
      lt_trans (lt_trans (hS j.castSucc) (hp' j.castSucc).1) (hp' j.castSucc).2.1
    have hx : 0 < (p j.succ).1 := lt_trans (hS j.succ) (hp' j.succ).1
    have hgap : 0 < (p j.succ).1 - (p j.castSucc).2 := by
      have := hsep j
      have := (hp' j.castSucc).2.2
      have := (hp' j.succ).1
      linarith
    exact (div_pos hy (mul_pos hx hgap)).le

private theorem backwardChain_positive {m : ℕ} {S T : Fin (m + 1) → ℝ}
    (hS : 0 < S 0) (hfirst : 2 * S 0 ≤ T 0)
    (hblock : ∀ j : Fin m, 4 * S j.succ ≤ T j.succ)
    (hsep : ∀ j : Fin m, T j.castSucc ≤ S j.succ) :
    ∀ j, 0 < S j ∧ 0 < T j := by
  apply Fin.induction
  · exact ⟨hS, by linarith⟩
  · intro j hj
    have hs : 0 < S j.succ := lt_of_lt_of_le hj.2 (hsep j)
    exact ⟨hs, by linarith [hblock j]⟩

private theorem lintegral_backwardInitialWeighted_step (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A,
    ∀ (m : ℕ) (S T : Fin (m + 2) → ℝ),
    (∀ j, 0 < S j) → (∀ j : Fin (m + 1), T j.castSucc ≤ S j.succ) →
    4 * S (Fin.last (m + 1)) ≤ T (Fin.last (m + 1)) →
    T (Fin.last (m + 1)) < 1 →
    (∫⁻ p, ENNReal.ofReal (backwardInitialDensity ϑ p *
      backwardWeight (T (Fin.last (m + 1))) (p (Fin.last (m + 1))).2)
      ∂Measure.pi (backwardChainMeasures S T)) ≤
    ENNReal.ofReal (C / (-Real.log (T (Fin.last (m + 1)))) *
      (T (Fin.last m).castSucc / S (Fin.last (m + 1)))) *
      ∫⁻ q, ENNReal.ofReal (backwardInitialDensity ϑ q *
        backwardWeight (T (Fin.last m).castSucc) (q (Fin.last m)).2)
        ∂Measure.pi (backwardChainMeasures (S ∘ Fin.castSucc) (T ∘ Fin.castSucc)) := by
  obtain ⟨C, hC, hblock⟩ := lintegral_backwardBlock_to_U_le A
  refine ⟨C, hC, ?_⟩
  intro ϑ hϑ m S T hS hsep hlast hT
  let S' : Fin (m + 1) → ℝ := S ∘ Fin.castSucc
  let T' : Fin (m + 1) → ℝ := T ∘ Fin.castSucc
  let U := T (Fin.last m).castSucc
  let V := T (Fin.last (m + 1))
  let R := S (Fin.last (m + 1))
  let c := C / (-Real.log V) * (U / R)
  have hR : 0 < R := hS _
  have hV : 0 < V := by dsimp [V, R] at *; linarith [hS (Fin.last (m + 1))]
  have hlogV : 0 < -Real.log V := by
    have := Real.log_neg hV hT
    linarith
  have hUR : U ≤ R := by simpa only [U, R, Fin.succ_last] using hsep (Fin.last m)
  have hmeas := (measurable_backwardInitialWeightedDensity ϑ T).ennreal_ofReal
  rw [lintegral_piLast (backwardChainMeasures S T) hmeas]
  simp_rw [piLastEquiv_symm_last]
  change (∫⁻ q : Fin (m + 1) → ℝ × ℝ,
      ∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (backwardInitialDensity ϑ ((piLastEquiv (m + 1)).symm (q, z)) *
          backwardWeight V z.2) ∂volume.restrict (backwardTriangle R V)
      ∂Measure.pi (backwardChainMeasures S' T')) ≤ _
  have hinner (q : Fin (m + 1) → ℝ × ℝ)
      (hq : q ∈ backwardChainDomain S' T') (hlt : (q (Fin.last m)).2 < U) :
      (∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (backwardInitialDensity ϑ ((piLastEquiv (m + 1)).symm (q, z)) *
          backwardWeight V z.2) ∂volume.restrict (backwardTriangle R V)) ≤
        ENNReal.ofReal c * ENNReal.ofReal
          (backwardInitialDensity ϑ q * backwardWeight U (q (Fin.last m)).2) := by
    let τ := (q (Fin.last m)).2
    have hqmem := hq (Fin.last m) (Set.mem_univ _)
    have hτ : 0 < τ := lt_trans (lt_trans (hS _) hqmem.1) hqmem.2.1
    have hD : 0 ≤ backwardInitialDensity ϑ q := by
      apply backwardInitialDensity_nonneg (fun j => hS j.castSucc) _ hq
      intro j
      simpa only [T', S', Function.comp_apply, ← Fin.castSucc_succ] using hsep j.castSucc
    have hW : 0 ≤ backwardWeight U τ := backwardWeight_nonneg (hτ.trans hlt) hτ.le hlt
    have hU : 0 < U := hτ.trans hlt
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hbound := hblock ϑ hϑ τ U R V hτ hlt hUR hlast hT
    calc
      _ = ENNReal.ofReal (backwardInitialDensity ϑ q) *
          ∫⁻ z in backwardTriangle R V,
            ENNReal.ofReal (DeltaBose.scalarDensity
              (ϑ - Real.eulerMascheroniConstant) (z.2 - z.1) *
              (τ / (z.1 * (z.1 - τ))) * backwardWeight V z.2) := by
        simp_rw [backwardInitialDensity_split, mul_assoc, ENNReal.ofReal_mul hD]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (backwardInitialDensity ϑ q) *
          ENNReal.ofReal (C / (-Real.log V) * (τ / R) * backwardWeight U τ) :=
        mul_le_mul' le_rfl hbound
      _ ≤ ENNReal.ofReal c *
          ENNReal.ofReal (backwardInitialDensity ϑ q * backwardWeight U τ) := by
        rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul hc]
        apply ENNReal.ofReal_le_ofReal
        have hratio : τ / R ≤ U / R := div_le_div_of_nonneg_right hlt.le hR.le
        have hcoef : C / (-Real.log V) * (τ / R) ≤ c :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        calc
          _ ≤ backwardInitialDensity ϑ q * (c * backwardWeight U τ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hW) hD
          _ = _ := by ring
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal c * ENNReal.ofReal
        (backwardInitialDensity ϑ q * backwardWeight U (q (Fin.last m)).2)
        ∂Measure.pi (backwardChainMeasures S' T') := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_backwardChainDomain S' T', ae_backwardChain_y_lt S' T']
        with q hq hlt
      exact hinner q hq (hlt (Fin.last m))
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem lintegral_backwardInitialWeighted_one (ϑ : ℝ) (S T : Fin 1 → ℝ) :
    (∫⁻ p, ENNReal.ofReal (backwardInitialDensity ϑ p *
      backwardWeight (T 0) (p 0).2) ∂Measure.pi (backwardChainMeasures S T)) =
      ∫⁻ z in backwardTriangle (S 0) (T 0), ENNReal.ofReal
        (z.1⁻¹ * DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (z.2 - z.1) *
          backwardWeight (T 0) z.2) := by
  have heq := lintegral_piLast (backwardChainMeasures S T)
    ((measurable_backwardInitialWeightedDensity ϑ T).ennreal_ofReal)
  simp only [Fin.last_zero] at heq
  rw [heq]
  have hzero (q : Fin 0 → ℝ × ℝ) (z : ℝ × ℝ) :
      (piLastEquiv 0).symm (q, z) 0 = z := by
    simpa only [Fin.last_zero] using piLastEquiv_symm_last 0 q z
  simp only [backwardInitialDensity, Fin.prod_univ_zero, mul_one]
  simp_rw [hzero]
  simp [backwardChainMeasures, hzero]

/-- The iterated backward-weight integral bound retaining the logarithmic weight on the last cell. -/
private theorem lintegral_backwardChain_weighted_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A,
    ∀ (m : ℕ) (S T : Fin (m + 1) → ℝ),
    0 < S 0 → 2 * S 0 ≤ T 0 →
    (∀ j : Fin m, 4 * S j.succ ≤ T j.succ) →
    (∀ j : Fin m, T j.castSucc ≤ S j.succ) → (∀ j, T j < 1) →
    (∫⁻ p : Fin (m + 1) → ℝ × ℝ in
      {p | ∀ j, S j < (p j).1 ∧ (p j).1 < (p j).2 ∧ (p j).2 ≤ T j},
      ENNReal.ofReal (backwardInitialDensity ϑ p *
        backwardWeight (T (Fin.last m)) (p (Fin.last m)).2)) ≤
      ENNReal.ofReal (C ^ (m + 1) * Real.log (T 0 / S 0) *
        (∏ j : Fin m, T j.castSucc / S j.succ) * ∏ j, (-Real.log (T j))⁻¹) := by
  obtain ⟨Ci, hCi, hinitial⟩ := lintegral_backwardInitial_le A
  obtain ⟨Cb, hCb, hstep⟩ := lintegral_backwardInitialWeighted_step A
  let C := max Ci Cb
  have hC : 0 < C := hCi.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro ϑ hϑ m
  induction m with
  | zero =>
    intro S T hS hfirst _ _ hT
    rw [backwardChainDomain_eq, lintegral_backwardChainDomain]
    simp only [Fin.last_zero]
    rw [lintegral_backwardInitialWeighted_one]
    have hf : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
        (z.1⁻¹ * DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (z.2 - z.1) *
          backwardWeight (T 0) z.2)) := by
      have hscalar : Measurable (fun t : ℝ =>
          DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t) :=
        DeltaBose.measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
      have hback : Measurable (backwardWeight (T 0)) := by
        change Measurable (fun t : ℝ => Real.log (2 * T 0) - Real.log (T 0 - t))
        fun_prop
      exact (((measurable_fst.inv).mul
        (hscalar.comp (measurable_snd.sub measurable_fst))).mul
        (hback.comp measurable_snd)).ennreal_ofReal
    rw [lintegral_backwardTriangle_eq_open hf]
    have hb := hinitial ϑ hϑ (S 0) (T 0) hS hfirst (hT 0)
    have hTp : 0 < T 0 := by linarith
    have hlogT : 0 < -Real.log (T 0) := neg_pos.2 (Real.log_neg hTp (hT 0))
    have hlogratio : 0 ≤ Real.log (T 0 / S 0) :=
      Real.log_nonneg ((le_div_iff₀ hS).2 (by linarith))
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcoef := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Ci Cb) (inv_nonneg.2 hlogT.le)) hlogratio
    simpa [C, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hcoef
  | succ m ih =>
    intro S T hS hfirst hblock hsep hT
    let S' : Fin (m + 1) → ℝ := S ∘ Fin.castSucc
    let T' : Fin (m + 1) → ℝ := T ∘ Fin.castSucc
    have hpositive := backwardChain_positive hS hfirst hblock hsep
    have hS' : 0 < S' 0 := hS
    have hfirst' : 2 * S' 0 ≤ T' 0 := hfirst
    have hblock' (j : Fin m) : 4 * S' j.succ ≤ T' j.succ := by
      simpa only [S', T', Function.comp_apply, ← Fin.castSucc_succ] using hblock j.castSucc
    have hsep' (j : Fin m) : T' j.castSucc ≤ S' j.succ := by
      simpa only [S', T', Function.comp_apply, ← Fin.castSucc_succ] using hsep j.castSucc
    have hT' (j) : T' j < 1 := hT j.castSucc
    have hprefix := ih S' T' hS' hfirst' hblock' hsep' hT'
    rw [backwardChainDomain_eq, lintegral_backwardChainDomain] at hprefix ⊢
    have hreduce := hstep ϑ hϑ m S T (fun j => (hpositive j).1) hsep
      (by simpa only [Fin.succ_last] using hblock (Fin.last m)) (hT _)
    refine hreduce.trans ?_
    let V := T (Fin.last (m + 1))
    let U := T (Fin.last m).castSucc
    let R := S (Fin.last (m + 1))
    have hV : 0 < V := (hpositive _).2
    have hU : 0 < U := (hpositive _).2
    have hR : 0 < R := (hpositive _).1
    have hlogV : 0 < -Real.log V := neg_pos.2 (Real.log_neg hV (hT _))
    have hc : 0 ≤ Cb / (-Real.log V) * (U / R) := by positivity
    calc
      _ ≤ ENNReal.ofReal (Cb / (-Real.log V) * (U / R)) *
          ENNReal.ofReal (C ^ (m + 1) * Real.log (T' 0 / S' 0) *
            (∏ j : Fin m, T' j.castSucc / S' j.succ) *
            ∏ j, (-Real.log (T' j))⁻¹) := mul_le_mul' le_rfl hprefix
      _ = ENNReal.ofReal ((Cb / (-Real.log V) * (U / R)) *
          (C ^ (m + 1) * Real.log (T' 0 / S' 0) *
            (∏ j : Fin m, T' j.castSucc / S' j.succ) *
            ∏ j, (-Real.log (T' j))⁻¹)) := (ENNReal.ofReal_mul hc).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hlogratio : 0 ≤ Real.log (T' 0 / S' 0) :=
          Real.log_nonneg ((le_div_iff₀ hS').2 (by linarith only [hfirst', hS']))
        have hprod : 0 ≤ C ^ (m + 1) * Real.log (T' 0 / S' 0) *
            (∏ j : Fin m, T' j.castSucc / S' j.succ) *
            ∏ j, (-Real.log (T' j))⁻¹ := by
          apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · exact Finset.prod_nonneg fun j _ =>
                (div_pos (hpositive _).2 (hpositive _).1).le
          · apply Finset.prod_nonneg
            intro j _
            exact inv_nonneg.2 (neg_pos.2 (Real.log_neg (hpositive _).2 (hT _))).le
        have hcoef : Cb / (-Real.log V) * (U / R) ≤ C / (-Real.log V) * (U / R) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (le_max_right Ci Cb) hlogV.le) (by positivity)
        calc
          _ ≤ (C / (-Real.log V) * (U / R)) *
              (C ^ (m + 1) * Real.log (T' 0 / S' 0) *
                (∏ j : Fin m, T' j.castSucc / S' j.succ) *
                ∏ j, (-Real.log (T' j))⁻¹) := mul_le_mul_of_nonneg_right hcoef hprod
          _ = _ := by
            simp only [Fin.prod_univ_castSucc, S', T', Function.comp_apply,
              ← Fin.castSucc_succ, Fin.succ_last, Fin.castSucc_zero, pow_succ,
              V, U, R, div_eq_mul_inv]
            ring

/-- The backward-weight integral bound iterated along a chain of cells, with the terminal weight removed. -/
theorem lintegral_backwardChain_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A,
    ∀ (m : ℕ) (S T : Fin (m + 1) → ℝ),
    0 < S 0 → 2 * S 0 ≤ T 0 →
    (∀ j : Fin m, 4 * S j.succ ≤ T j.succ) →
    (∀ j : Fin m, T j.castSucc ≤ S j.succ) → (∀ j, T j < 1) →
    ∫⁻ p : Fin (m + 1) → ℝ × ℝ in
      {p | ∀ j, S j < (p j).1 ∧ (p j).1 < (p j).2 ∧ (p j).2 ≤ T j},
      ENNReal.ofReal ((p 0).1⁻¹ *
        (∏ j, DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) ((p j).2 - (p j).1)) *
        ∏ j : Fin m, (p j.castSucc).2 /
          ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))) ≤
      ENNReal.ofReal (C ^ (m + 1) * Real.log (T 0 / S 0) *
        (∏ j : Fin m, T j.castSucc / S j.succ) * ∏ j, (-Real.log (T j))⁻¹) := by
  obtain ⟨Cw, hCw, hweighted⟩ := lintegral_backwardChain_weighted_le A
  let B := max 1 (Real.log 2)⁻¹
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B * Cw, mul_pos hBpos hCw, ?_⟩
  intro ϑ hϑ m S T hS hfirst hblock hsep hT
  have hpositive := backwardChain_positive hS hfirst hblock hsep
  have hbound := hweighted ϑ hϑ m S T hS hfirst hblock hsep hT
  rw [backwardChainDomain_eq, lintegral_backwardChainDomain] at hbound ⊢
  change (∫⁻ p, ENNReal.ofReal (backwardInitialDensity ϑ p)
    ∂Measure.pi (backwardChainMeasures S T)) ≤ _
  have hcoeff : (Real.log 2)⁻¹ ≤ B ^ (m + 1) := by
    calc
      (Real.log 2)⁻¹ ≤ B := le_max_right _ _
      _ = B ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ B ^ (m + 1) := pow_le_pow_right₀ hB (by omega)
  have hrest : 0 ≤ Real.log (T 0 / S 0) *
      (∏ j : Fin m, T j.castSucc / S j.succ) * ∏ j, (-Real.log (T j))⁻¹ := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact Real.log_nonneg ((le_div_iff₀ hS).2 (by linarith))
      · exact Finset.prod_nonneg fun j _ =>
          (div_pos (hpositive _).2 (hpositive _).1).le
    · exact Finset.prod_nonneg fun j _ =>
        inv_nonneg.2 (neg_pos.2 (Real.log_neg (hpositive j).2 (hT j))).le
  calc
    _ ≤ ENNReal.ofReal ((Real.log 2)⁻¹) *
        ∫⁻ p, ENNReal.ofReal (backwardInitialDensity ϑ p *
          backwardWeight (T (Fin.last m)) (p (Fin.last m)).2)
          ∂Measure.pi (backwardChainMeasures S T) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_mem_backwardChainDomain S T, ae_backwardChain_y_lt S T]
        with p hp hlt
      have hD := backwardInitialDensity_nonneg (ϑ := ϑ) (fun j => (hpositive j).1) hsep hp
      have hmem := hp (Fin.last m) (Set.mem_univ _)
      have hy : 0 ≤ (p (Fin.last m)).2 := by
        have := (hpositive (Fin.last m)).1
        linarith only [this, hmem.1, hmem.2.1]
      have hW := backwardWeight_ge_log_two hy (hlt (Fin.last m))
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hlog2.le)]
      apply ENNReal.ofReal_le_ofReal
      calc
        backwardInitialDensity ϑ p =
            (Real.log 2)⁻¹ * (backwardInitialDensity ϑ p * Real.log 2) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hW hD) (inv_nonneg.2 hlog2.le)
    _ ≤ ENNReal.ofReal ((Real.log 2)⁻¹) *
        ENNReal.ofReal (Cw ^ (m + 1) * Real.log (T 0 / S 0) *
          (∏ j : Fin m, T j.castSucc / S j.succ) *
          ∏ j, (-Real.log (T j))⁻¹) := mul_le_mul' le_rfl hbound
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hlog2.le)]
      apply ENNReal.ofReal_le_ofReal
      have hpower := mul_le_mul_of_nonneg_right hcoeff (pow_pos hCw (m + 1)).le
      have htotal := mul_le_mul_of_nonneg_right hpower hrest
      simpa only [mul_pow, mul_assoc] using htotal

private theorem lintegral_backwardOpenBlock_to_U_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ τ U S T : ℝ,
      0 < τ → τ < U → U ≤ S → 4 * S ≤ T → T ≤ 2 →
      (∫⁻ p in backwardTriangle S T,
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
            (τ / (p.1 * (p.1 - τ))))) ≤
        ENNReal.ofReal (C * (τ / S) * backwardWeight U τ) := by
  let M := Real.exp (Real.exp (A - Real.eulerMascheroniConstant + 1) * 2)
  let B := M / Real.log 2
  let D : ℝ := 24 / Real.log 2 + 8
  have hM : 0 < M := Real.exp_pos _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B := div_pos hM hlog2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B * D, mul_pos hB hD, ?_⟩
  intro ϑ hϑ τ U S T hτ hτU hUS hblock hT
  have hτS : τ < S := hτU.trans_le hUS
  have hS : 0 < S := hτ.trans hτS
  have hTpos : 0 < T := by linarith
  have hscalar : Measurable (fun t : ℝ =>
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t) :=
    DeltaBose.measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hratio : Measurable (fun p : ℝ × ℝ => τ / (p.1 * (p.1 - τ))) := by fun_prop
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
        (τ / (p.1 * (p.1 - τ))))) :=
    ((hscalar.comp (measurable_snd.sub measurable_fst)).mul hratio).ennreal_ofReal
  rw [lintegral_backwardTriangle_le hmeas]
  have hmass (x : ℝ) (hx : x ∈ Ioo S T) :
      (∫⁻ y in Ioo x T, ENNReal.ofReal
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x))) ≤
        ENNReal.ofReal M := by
    rw [← DeltaBose.lintegral_Ioo_sub_right x T (fun r =>
      ENNReal.ofReal (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r))]
    refine DeltaBose.lintegral_scalarDensity_Ioo_le.trans (ENNReal.ofReal_le_ofReal ?_)
    apply Real.exp_le_exp.2
    have he : Real.exp (ϑ - Real.eulerMascheroniConstant + 1) ≤
        Real.exp (A - Real.eulerMascheroniConstant + 1) :=
      Real.exp_le_exp.2 (by linarith only [hϑ.2])
    have hgap : T - x ≤ 2 := by linarith only [hT, hx.1, hS]
    exact mul_le_mul he hgap (sub_pos.2 hx.2).le (Real.exp_pos _).le
  have houter := lintegral_backwardBlock_outer_le hτ.le hτS hS hblock
  have hinner :
      (∫⁻ x in Ioo S T, ∫⁻ y in Ioo x T,
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (y - x) *
            (τ / (x * (x - τ))))) ≤
      ENNReal.ofReal B * (∫⁻ x in Ioo S T,
        ENNReal.ofReal ((τ / (x * (x - τ))) * backwardWeight T x)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxpos : 0 < x := hS.trans hx.1
    have hr : 0 ≤ τ / (x * (x - τ)) := by
      exact (div_pos hτ (mul_pos hxpos (sub_pos.2 (hτS.trans hx.1)))).le
    have hW := backwardWeight_ge_log_two hxpos.le hx.2
    calc
      _ = ENNReal.ofReal (τ / (x * (x - τ))) *
          (∫⁻ y in Ioo x T, ENNReal.ofReal
            (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x))) := by
        simp_rw [mul_comm (DeltaBose.scalarDensity _ _), ENNReal.ofReal_mul hr]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (τ / (x * (x - τ))) * ENNReal.ofReal M :=
        mul_le_mul' le_rfl (hmass x hx)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul hB.le]
        apply ENNReal.ofReal_le_ofReal
        have hMW : M ≤ B * backwardWeight T x := by
          change M ≤ M / Real.log 2 * backwardWeight T x
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          exact mul_le_mul_of_nonneg_left hW hM.le
        calc
          _ ≤ (τ / (x * (x - τ))) * (B * backwardWeight T x) :=
            mul_le_mul_of_nonneg_left hMW hr
          _ = _ := by ring
  refine hinner.trans ((mul_le_mul' le_rfl houter).trans ?_)
  rw [← ENNReal.ofReal_mul hB.le]
  apply ENNReal.ofReal_le_ofReal
  have hweight := backwardWeight_antitone_horizon hτ.le hτU hUS
  calc
    _ = (B * D) * (τ / S) * backwardWeight S τ := by dsimp [D]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)

private theorem lintegral_backwardInitialOpen_step (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A,
    ∀ (m : ℕ) (S T : Fin (m + 2) → ℝ),
    (∀ j, 0 < S j) → (∀ j : Fin (m + 1), T j.castSucc ≤ S j.succ) →
    4 * S (Fin.last (m + 1)) ≤ T (Fin.last (m + 1)) →
    T (Fin.last (m + 1)) ≤ 2 →
    (∫⁻ p, ENNReal.ofReal (backwardInitialDensity ϑ p)
      ∂Measure.pi (backwardChainMeasures S T)) ≤
    ENNReal.ofReal (C *
      (T (Fin.last m).castSucc / S (Fin.last (m + 1)))) *
      ∫⁻ q, ENNReal.ofReal (backwardInitialDensity ϑ q *
        backwardWeight (T (Fin.last m).castSucc) (q (Fin.last m)).2)
        ∂Measure.pi (backwardChainMeasures (S ∘ Fin.castSucc) (T ∘ Fin.castSucc)) := by
  obtain ⟨C, hC, hblock⟩ := lintegral_backwardOpenBlock_to_U_le A
  refine ⟨C, hC, ?_⟩
  intro ϑ hϑ m S T hS hsep hlast hT
  let S' : Fin (m + 1) → ℝ := S ∘ Fin.castSucc
  let T' : Fin (m + 1) → ℝ := T ∘ Fin.castSucc
  let U := T (Fin.last m).castSucc
  let V := T (Fin.last (m + 1))
  let R := S (Fin.last (m + 1))
  let c := C * (U / R)
  have hR : 0 < R := hS _
  have hUR : U ≤ R := by simpa only [U, R, Fin.succ_last] using hsep (Fin.last m)
  have hmeas := (measurable_backwardInitialDensity (m := m + 1) ϑ).ennreal_ofReal
  rw [lintegral_piLast (backwardChainMeasures S T) hmeas]
  change (∫⁻ q : Fin (m + 1) → ℝ × ℝ,
      ∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (backwardInitialDensity ϑ ((piLastEquiv (m + 1)).symm (q, z))) ∂volume.restrict (backwardTriangle R V)
      ∂Measure.pi (backwardChainMeasures S' T')) ≤ _
  have hinner (q : Fin (m + 1) → ℝ × ℝ)
      (hq : q ∈ backwardChainDomain S' T') (hlt : (q (Fin.last m)).2 < U) :
      (∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (backwardInitialDensity ϑ ((piLastEquiv (m + 1)).symm (q, z))) ∂volume.restrict (backwardTriangle R V)) ≤
        ENNReal.ofReal c * ENNReal.ofReal
          (backwardInitialDensity ϑ q * backwardWeight U (q (Fin.last m)).2) := by
    let τ := (q (Fin.last m)).2
    have hqmem := hq (Fin.last m) (Set.mem_univ _)
    have hτ : 0 < τ := lt_trans (lt_trans (hS _) hqmem.1) hqmem.2.1
    have hD : 0 ≤ backwardInitialDensity ϑ q := by
      apply backwardInitialDensity_nonneg (fun j => hS j.castSucc) _ hq
      intro j
      simpa only [T', S', Function.comp_apply, ← Fin.castSucc_succ] using hsep j.castSucc
    have hW : 0 ≤ backwardWeight U τ := backwardWeight_nonneg (hτ.trans hlt) hτ.le hlt
    have hU : 0 < U := hτ.trans hlt
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hbound := hblock ϑ hϑ τ U R V hτ hlt hUR hlast hT
    calc
      _ = ENNReal.ofReal (backwardInitialDensity ϑ q) *
          ∫⁻ z in backwardTriangle R V,
            ENNReal.ofReal (DeltaBose.scalarDensity
              (ϑ - Real.eulerMascheroniConstant) (z.2 - z.1) *
              (τ / (z.1 * (z.1 - τ)))) := by
        simp_rw [backwardInitialDensity_split, ENNReal.ofReal_mul hD]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (backwardInitialDensity ϑ q) *
          ENNReal.ofReal (C * (τ / R) * backwardWeight U τ) :=
        mul_le_mul' le_rfl hbound
      _ ≤ ENNReal.ofReal c *
          ENNReal.ofReal (backwardInitialDensity ϑ q * backwardWeight U τ) := by
        rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul hc]
        apply ENNReal.ofReal_le_ofReal
        have hratio : τ / R ≤ U / R := div_le_div_of_nonneg_right hlt.le hR.le
        have hcoef : C * (τ / R) ≤ c :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        calc
          _ ≤ backwardInitialDensity ϑ q * (c * backwardWeight U τ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hW) hD
          _ = _ := by ring
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal c * ENNReal.ofReal
        (backwardInitialDensity ϑ q * backwardWeight U (q (Fin.last m)).2)
        ∂Measure.pi (backwardChainMeasures S' T') := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_backwardChainDomain S' T', ae_backwardChain_y_lt S' T']
        with q hq hlt
      exact hinner q hq (hlt (Fin.last m))
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top


/-- The open-string chain: the last cell may reach time two and costs no final logarithm. -/
theorem lintegral_backwardChain_open_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A,
    ∀ (m : ℕ) (S T : Fin (m + 2) → ℝ),
    0 < S 0 → 2 * S 0 ≤ T 0 →
    (∀ j : Fin (m + 1), 4 * S j.succ ≤ T j.succ) →
    (∀ j : Fin (m + 1), T j.castSucc ≤ S j.succ) →
    (∀ j : Fin (m + 1), T j.castSucc < 1) → T (Fin.last (m + 1)) ≤ 2 →
    ∫⁻ p : Fin (m + 2) → ℝ × ℝ in
      {p | ∀ j, S j < (p j).1 ∧ (p j).1 < (p j).2 ∧ (p j).2 ≤ T j},
      ENNReal.ofReal ((p 0).1⁻¹ *
        (∏ j, DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) ((p j).2 - (p j).1)) *
        ∏ j : Fin (m + 1), (p j.castSucc).2 /
          ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))) ≤
      ENNReal.ofReal (C ^ (m + 2) * Real.log (T 0 / S 0) *
        (∏ j : Fin (m + 1), T j.castSucc / S j.succ) *
        ∏ j : Fin (m + 1), (-Real.log (T j.castSucc))⁻¹) := by
  obtain ⟨Cw, hCw, hweighted⟩ := lintegral_backwardChain_weighted_le A
  obtain ⟨Cb, hCb, hopen⟩ := lintegral_backwardInitialOpen_step A
  let C := max Cw Cb
  have hC : 0 < C := hCw.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro ϑ hϑ m S T hS hfirst hblock hsep hT hlast
  let S' : Fin (m + 1) → ℝ := S ∘ Fin.castSucc
  let T' : Fin (m + 1) → ℝ := T ∘ Fin.castSucc
  have hpositive := backwardChain_positive hS hfirst hblock hsep
  have hS' : 0 < S' 0 := hS
  have hfirst' : 2 * S' 0 ≤ T' 0 := hfirst
  have hblock' (j : Fin m) : 4 * S' j.succ ≤ T' j.succ := by
    simpa only [S', T', Function.comp_apply, ← Fin.castSucc_succ] using hblock j.castSucc
  have hsep' (j : Fin m) : T' j.castSucc ≤ S' j.succ := by
    simpa only [S', T', Function.comp_apply, ← Fin.castSucc_succ] using hsep j.castSucc
  have hT' (j) : T' j < 1 := hT j
  have hprefix := hweighted ϑ hϑ m S' T' hS' hfirst' hblock' hsep' hT'
  rw [backwardChainDomain_eq, lintegral_backwardChainDomain] at hprefix ⊢
  have hreduce := hopen ϑ hϑ m S T (fun j => (hpositive j).1) hsep
    (by simpa only [Fin.succ_last] using hblock (Fin.last m)) hlast
  change (∫⁻ p, ENNReal.ofReal (backwardInitialDensity ϑ p)
    ∂Measure.pi (backwardChainMeasures S T)) ≤ _
  refine hreduce.trans ?_
  let U := T (Fin.last m).castSucc
  let R := S (Fin.last (m + 1))
  have hU : 0 < U := (hpositive _).2
  have hR : 0 < R := (hpositive _).1
  have hc : 0 ≤ Cb * (U / R) := by positivity
  calc
    _ ≤ ENNReal.ofReal (Cb * (U / R)) *
        ENNReal.ofReal (Cw ^ (m + 1) * Real.log (T' 0 / S' 0) *
          (∏ j : Fin m, T' j.castSucc / S' j.succ) *
          ∏ j, (-Real.log (T' j))⁻¹) := mul_le_mul' le_rfl hprefix
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      have hpower : Cb * Cw ^ (m + 1) ≤ C ^ (m + 2) := by
        calc
          Cb * Cw ^ (m + 1) ≤ C * C ^ (m + 1) :=
            mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ hCw.le (le_max_left _ _) _)
              (pow_pos hCw _).le hC.le
          _ = _ := by ring
      have hlogratio : 0 ≤ Real.log (T' 0 / S' 0) :=
        Real.log_nonneg ((le_div_iff₀ hS').2 (by linarith only [hfirst', hS']))
      have hrest : 0 ≤ Real.log (T' 0 / S' 0) *
          ((∏ j : Fin m, T' j.castSucc / S' j.succ) * (U / R)) *
          ∏ j, (-Real.log (T' j))⁻¹ := by
        apply mul_nonneg
        · apply mul_nonneg hlogratio
          apply mul_nonneg
          · exact Finset.prod_nonneg fun j _ =>
              (div_pos (hpositive _).2 (hpositive _).1).le
          · positivity
        · exact Finset.prod_nonneg fun j _ =>
            inv_nonneg.2 (neg_pos.2 (Real.log_neg (hpositive _).2 (hT _))).le
      calc
        _ = (Cb * Cw ^ (m + 1)) *
            (Real.log (T' 0 / S' 0) *
              ((∏ j : Fin m, T' j.castSucc / S' j.succ) * (U / R)) *
              ∏ j, (-Real.log (T' j))⁻¹) := by ring
        _ ≤ C ^ (m + 2) *
            (Real.log (T' 0 / S' 0) *
              ((∏ j : Fin m, T' j.castSucc / S' j.succ) * (U / R)) *
              ∏ j, (-Real.log (T' j))⁻¹) := mul_le_mul_of_nonneg_right hpower hrest
        _ = _ := by
          simp only [Fin.prod_univ_castSucc, S', T', Function.comp_apply,
            ← Fin.castSucc_succ, Fin.succ_last, Fin.castSucc_zero, U, R]
          ring

end Critical2DKPZ.Collision

end
