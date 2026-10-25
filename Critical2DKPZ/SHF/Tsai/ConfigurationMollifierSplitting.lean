/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationMollifiers
public import Critical2DKPZ.SHF.Tsai.LiftedMollifiers

/-! # Fubini decomposition of configuration mollification

Every row is absolutely integrable. The canonical coordinate splitting and
Fubini therefore identify the full product convolution with convolution in
the remaining coordinates followed by planar convolution in the first one.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Split the first coordinate of a product convolution, retaining actual integrals. -/
theorem configurationMollifierAction_succ {n : ℕ} {w : Fin (n + 1) → Plane → ℝ}
    (hw : ∀ i, MemLp (w i) 2) {F : Configuration (n + 1) → ℝ} (hF : MemLp F 2)
    (x : Configuration (n + 1)) :
    configurationMollifierAction w F x =
      leftMollifierAction (w 0) (fun q : Plane × Configuration n =>
        configurationMollifierAction (fun i => w i.succ)
          (fun y => F (Fin.cons q.1 y)) q.2) (x 0, Fin.tail x) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Plane) 0
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure Plane)) 0
  let f (y : Configuration (n + 1)) := (∏ i, w i (x i - y i)) * F y
  have hf : Integrable f := integrable_configurationMollifierAction_integrand hw hF x
  have hI := (he.symm e).integrable_comp_of_integrable hf
  have hsplit (q : Plane × Configuration n) : f (e.symm q) =
      w 0 (x 0 - q.1) * (∏ i : Fin n, w i.succ (x i.succ - q.2 i)) * F (Fin.cons q.1 q.2) := by
    simp only [f, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
      Fin.prod_univ_succ, Equiv.coe_fn_mk, cast_eq, Fin.cons_zero, Fin.cons_succ]
  calc
    configurationMollifierAction w F x = ∫ q : Plane × Configuration n, f (e.symm q) :=
      ((he.symm e).integral_comp' f).symm
    _ = ∫ y : Plane, ∫ z : Configuration n, f (e.symm (y, z)) := integral_prod _ hI
    _ = _ := by
      simp only [leftMollifierAction, configurationMollifierAction]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      rw [hsplit]
      exact mul_assoc _ _ _

end Critical2DKPZ.SHF.Tsai

end
