/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationMollifierSplitting
public import Critical2DKPZ.SHF.Tsai.LiftedMollifierOperators

/-! # Strong approximation by full configuration connectors

Induction on the number of coordinates uses fiberwise dominated convergence
for the remaining coordinates, then the planar operator on the first one.
Fubini identifies this composition with the literal product convolution.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Product mollifiers approximate the identity on configuration `L²`. -/
theorem tendsto_configurationMollifierAction (n : ℕ) :
    ∀ {w : Fin n → ℕ → Plane → ℝ}, (∀ i, IsL2ApplicableMollifier (w i)) →
      ∀ {F : Configuration n → ℝ}, Measurable F → MemLp F 2 →
      Tendsto (fun j => eLpNorm (configurationMollifierAction (fun i => w i j) F - F) 2)
        atTop (𝓝 0) := by
  induction n with
  | zero =>
    intro w hw F hFm hF
    have heq (j) : configurationMollifierAction (fun i => w i j) F = F := by
      funext x
      simp [configurationMollifierAction, integral_unique, volume_pi,
        measureReal_def, Measure.pi_empty_univ]
      exact congrArg F (Subsingleton.elim _ _)
    simp only [heq, sub_self, eLpNorm_zero]
    exact tendsto_const_nhds
  | succ n ih =>
    intro w hw F hFm hF
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Plane) 0
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure Plane)) 0
    have hecons (q : Plane × Configuration n) : e.symm q = Fin.cons q.1 q.2 := by
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
    let Fp (q : Plane × Configuration n) := F (e.symm q)
    have hFpm : Measurable Fp := hFm.comp e.symm.measurable
    have hFp : MemLp Fp 2 ((volume : Measure Plane).prod (volume : Measure (Configuration n))) :=
      hF.comp_measurePreserving (he.symm e)
    let Fs (q : Configuration n × Plane) := Fp q.swap
    have hFsm : Measurable Fs := hFpm.comp measurable_swap
    have hFs : MemLp Fs 2 ((volume : Measure (Configuration n)).prod (volume : Measure Plane)) :=
      hFp.comp_measurePreserving (Measure.measurePreserving_swap)
    let T (j : ℕ) := configurationMollifierAction (fun i : Fin n => w i.succ j)
    obtain ⟨M, hMfin, hM⟩ := exists_configurationMollifierAction_uniform_bound (fun i => hw i.succ)
    have hTm (j) : Measurable (fun q : Configuration n × Plane => T j (fun x => Fs (x, q.2)) q.1) :=
      measurable_fiber_configurationMollifierAction (fun i => ((hw i.succ).2.1 j).measurable) hFsm
    have hRf := fiberAction_memLp_and_tendsto
      (volume : Measure (Configuration n)) (volume : Measure Plane) T hMfin hM
      (fun φ hφm hφ => ih (fun i => hw i.succ) hφm hφ) hFsm hFs hTm
    let R (j : ℕ) (q : Plane × Configuration n) := T j (fun x => Fp (q.1, x)) q.2
    have hRm (j) : Measurable (R j) := (hTm j).comp measurable_swap
    have hRfiber (j) : MemLp (fun q : Configuration n × Plane => T j (fun x => Fs (x, q.2)) q.1)
        2 ((volume : Measure (Configuration n)).prod (volume : Measure Plane)) := hRf.1 j
    have hswapFun (j) : (fun q : Configuration n × Plane => T j (fun x => Fs (x, q.2)) q.1) ∘
        Prod.swap = R j := by
      funext q
      dsimp only [Function.comp_apply, Fs, R, Prod.swap]
    have hR (j) : MemLp (R j) 2 ((volume : Measure Plane).prod (volume : Measure (Configuration n))) := by
      have hmem := (hRfiber j).comp_measurePreserving (Measure.measurePreserving_swap
        (μ := (volume : Measure Plane)) (ν := (volume : Measure (Configuration n))))
      rw [hswapFun j] at hmem
      exact hmem
    have hRnorm (j) : eLpNorm (R j - Fp) 2
        ((volume : Measure Plane).prod (volume : Measure (Configuration n))) =
        eLpNorm (fun q : Configuration n × Plane => T j (fun x => Fs (x, q.2)) q.1 - Fs q)
          2 ((volume : Measure (Configuration n)).prod (volume : Measure Plane)) := by
      have hh := eLpNorm_comp_measurePreserving (p := 2) ((hTm j).sub hFsm).aestronglyMeasurable
        (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
          (ν := (volume : Measure (Configuration n))))
      have hdiff : ((fun q : Configuration n × Plane => T j (fun x => Fs (x, q.2)) q.1) - Fs) ∘
          Prod.swap = R j - Fp := by
        funext q
        dsimp only [Function.comp_apply, Fs, R, Prod.swap, Pi.sub_apply]
      rw [hdiff] at hh
      exact hh
    have hRlim : Tendsto (fun j => eLpNorm (R j - Fp) 2
        ((volume : Measure Plane).prod (volume : Measure (Configuration n)))) atTop (𝓝 0) := by
      simpa only [hRnorm] using hRf.2
    have hRLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' R hR Fp hFp).2 hRlim
    have hA := tendsto_operator_apply_of_tendsto
      (A := fun j => leftMollifierOperator (volume : Measure (Configuration n)) (hw 0) j)
      (B := ContinuousLinearMap.id ℝ _)
      (tendsto_leftMollifierOperator (volume : Measure (Configuration n)) (hw 0)) hRLp
    have hAlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm
      (fun j => leftMollifierOperator (volume : Measure (Configuration n)) (hw 0) j ((hR j).toLp (R j)))
      Fp hFp).1 hA
    have hArepr (j) : ⇑(leftMollifierOperator (volume : Measure (Configuration n))
        (hw 0) j ((hR j).toLp (R j))) =ᵐ[(volume : Measure Plane).prod (volume : Measure (Configuration n))]
        leftMollifierAction (w 0 j) (R j) :=
      (coe_leftMollifierOperator _ (hw 0) j _).trans
        (leftMollifierAction_congr_ae _ (w 0 j) (hR j).coeFn_toLp)
    have hAnorm (j) := eLpNorm_congr_ae (p := 2) ((hArepr j).sub (Filter.EventuallyEq.rfl (f := Fp)))
    simp_rw [hAnorm] at hAlim
    have hsplit (j) : (configurationMollifierAction (fun i => w i j) F - F) ∘ e.symm =
        leftMollifierAction (w 0 j) (R j) - Fp := by
      funext q
      have h := configurationMollifierAction_succ (fun i => (hw i).2.2.1 j) hF (e.symm q)
      simpa only [Function.comp_apply, Pi.sub_apply, R, T, Fp, hecons,
        Fin.cons_zero, Fin.tail_cons] using congrArg (fun a => a - Fp q) h
    have hnorm (j) : eLpNorm (configurationMollifierAction (fun i => w i j) F - F) 2 =
        eLpNorm (leftMollifierAction (w 0 j) (R j) - Fp) 2
          ((volume : Measure Plane).prod (volume : Measure (Configuration n))) := by
      rw [← hsplit j]
      exact (eLpNorm_comp_measurePreserving
        ((measurable_configurationMollifierAction (fun i => ((hw i).2.1 j).measurable) hFm).sub hFm).aestronglyMeasurable
        (he.symm e)).symm
    simpa only [hnorm] using hAlim

end Critical2DKPZ.SHF.Tsai

end
