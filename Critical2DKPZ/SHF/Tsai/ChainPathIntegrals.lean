/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainPathTests

/-! # The literal path integral of an endpoint chain

Sigma-finite block measures give s-finite endpoint chains. Tonelli and the
canonical final-coordinate splitting identify their positive pairings with
the finite product path measure, with no convergence or integrability premise.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Split a finite path measure at its final pair, putting that pair in the outer integral. -/
theorem lintegral_path_snoc {X : Type*} [MeasurableSpace X] (m : ℕ) (μ : Fin (m + 1) → Measure (X))
    [∀ i, SigmaFinite (μ i)] {J : (Fin (m + 1) → X) → ℝ≥0∞}
    (hJ : Measurable J) :
    (∫⁻ p, J p ∂Measure.pi μ) =
      ∫⁻ z, (∫⁻ q, J (Fin.snoc q z) ∂Measure.pi (fun i : Fin m => μ i.castSucc)) ∂μ (Fin.last m) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) (Fin.last m)
  have he := measurePreserving_piFinSuccAbove μ (Fin.last m)
  have hinv (z : X) (q : Fin m → X) : e.symm (z, q) = Fin.snoc q z := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have h := (he.symm e).lintegral_comp hJ
  calc
    _ = ∫⁻ p : X × (Fin m → X), J (e.symm p)
        ∂((μ (Fin.last m)).prod (Measure.pi (fun i => μ ((Fin.last m).succAbove i)))) := h.symm
    _ = ∫⁻ z, (∫⁻ q, J (e.symm (z, q)) ∂Measure.pi (fun i => μ ((Fin.last m).succAbove i)))
        ∂μ (Fin.last m) := lintegral_prod _ (hJ.comp e.symm.measurable).aemeasurable
    _ = _ := by simp only [hinv, Fin.succAbove_last]

/-- Positive chain pairings equal their finite product path integral. -/
theorem lintegral_chainProduct_eq_lintegral_path (μ : ℕ → Measure (Plane × Plane))
    [∀ k, SigmaFinite (μ k)] {w : ℕ → Plane → ℝ} (hw : ∀ k, Measurable (w k)) (K : ℕ)
    {H : Plane × Plane → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H p ∂chainProduct μ w K) =
      ∫⁻ p, chainPathTest K w H p ∂Measure.pi (fun k : Fin (K + 1) => μ k) := by
  induction K generalizing H with
  | zero =>
    have he := measurePreserving_piUnique (fun k : Fin 1 => μ k)
    have h := he.lintegral_comp hH
    have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
    have hlast : Fin.last 0 = 0 := rfl
    simpa only [chainProduct, chainPathTest, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
      MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      hdef, hlast, Fin.val_zero, Prod.eta] using h.symm
  | succ K ih =>
    let : SFinite (chainProduct μ w K) := sFinite_chainProduct μ (fun _ => inferInstance) w K
    have houter : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
        ENNReal.ofReal (w K (q.1.2 - q.2.1)) * H (q.1.1, q.2.2)) := by
      exact ((hw K).comp (measurable_fst.snd.sub measurable_snd.fst)).ennreal_ofReal.mul
        (hH.comp (measurable_fst.fst.prodMk measurable_snd.snd))
    rw [chainProduct, lintegral_smoothedProductMeasure _ _ _ (hw K) _ hH,
      lintegral_prod_symm (μ := chainProduct μ w K) (ν := μ (K + 1))
        (fun q => ENNReal.ofReal (w K (q.1.2 - q.2.1)) * H (q.1.1, q.2.2)) houter.aemeasurable,
      lintegral_path_snoc (K + 1) _ (measurable_chainPathTest (K + 1) hw hH)]
    apply lintegral_congr
    intro z
    have hz : Measurable (fun p : Plane × Plane => ENNReal.ofReal (w K (p.2 - z.1)) * H (p.1, z.2)) :=
      ((hw K).comp (measurable_snd.sub measurable_const)).ennreal_ofReal.mul
        (hH.comp (measurable_fst.prodMk measurable_const))
    rw [ih hz]
    apply lintegral_congr
    intro p
    exact (chainPathTest_snoc K w H p z).symm

end Critical2DKPZ.SHF.Tsai

end
