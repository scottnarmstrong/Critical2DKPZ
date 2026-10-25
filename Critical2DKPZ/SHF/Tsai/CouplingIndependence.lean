/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Independent block families on a product coupling

An independent finite family on the second probability space remains
independent after adjoining one variable from the first space. The proof
identifies the joint law by the product-map formula and the finite product
measure's first-coordinate splitting.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- A variable on the first factor can be adjoined to an independent finite family on the second. -/
theorem iIndepFun_fin_cons_prod {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {n : ℕ} (A : Ω' → X) (B : Fin n → Ω → X) (hA : Measurable A)
    (hB : ∀ i, Measurable (B i)) (hind : iIndepFun B P) :
    iIndepFun (fun i : Fin (n + 1) => fun ω : Ω' × Ω =>
      Fin.cons (α := fun _ : Fin (n + 1) => X) (A ω.1) (fun j => B j ω.2) i) (P'.prod P) := by
  classical
  let V (ω : Ω) (i : Fin n) := B i ω
  have hV : Measurable V := Measurable.of_eval hB
  let M : Fin (n + 1) → Measure X := Fin.cons (α := fun _ : Fin (n + 1) => Measure X) (P'.map A) (fun i => P.map (B i))
  let : IsProbabilityMeasure (P'.map A) := by infer_instance
  let : ∀ i, IsProbabilityMeasure (P.map (B i)) :=
    fun _ => inferInstance
  have hM (i : Fin (n + 1)) : IsProbabilityMeasure (M i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsProbabilityMeasure (P'.map A)
      infer_instance
    · change IsProbabilityMeasure (P.map (B j))
      infer_instance
  let : ∀ i, IsProbabilityMeasure (M i) := hM
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
  have he := measurePreserving_piFinSuccAbove M 0
  have hecons (q : X × (Fin n → X)) : e.symm q = Fin.cons (α := fun _ : Fin (n + 1) => X) q.1 q.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  have hconsmap : ((P'.map A).prod (Measure.pi (fun i => P.map (B i)))).map
      (fun q : X × (Fin n → X) => Fin.cons (α := fun _ : Fin (n + 1) => X) q.1 q.2) = Measure.pi M := by
    have h := (he.symm e).map_eq
    rw [funext hecons] at h
    simpa only [M, Fin.cons_zero, Fin.succAbove_zero, Fin.cons_succ] using h
  let T (ω : Ω' × Ω) : Fin (n + 1) → X := Fin.cons (α := fun _ : Fin (n + 1) => X) (A ω.1) (fun i => B i ω.2)
  have hpair : Measurable (Prod.map A V) := hA.prodMap hV
  have hpairmap : (P'.prod P).map (Prod.map A V) =
      (P'.map A).prod (Measure.pi (fun i => P.map (B i))) := by
    rw [← Measure.map_prod_map P' P hA hV, ← hind.map_fun_eq_pi_map (fun i => (hB i).aemeasurable)]
  have hT : T = e.symm ∘ Prod.map A V := by
    funext ω
    exact (hecons (A ω.1, V ω.2)).symm
  have hjoint : (P'.prod P).map T = Measure.pi M := by
    rw [hT, ← Measure.map_map e.symm.measurable hpair, hpairmap, funext hecons, hconsmap]
  have hmarg (i : Fin (n + 1)) :
      (P'.prod P).map (fun ω => T ω i) = M i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change (P'.prod P).map (fun ω => A ω.1) = P'.map A
      rw [← Function.comp_def, ← Measure.map_map hA measurable_fst,
        Measure.map_fst_prod, measure_univ, one_smul]
    · change (P'.prod P).map (fun ω => B j ω.2) = P.map (B j)
      rw [← Function.comp_def, ← Measure.map_map (hB j) measurable_snd,
        Measure.map_snd_prod, measure_univ, one_smul]
  have hTm : Measurable T := by
    rw [hT]
    exact e.symm.measurable.comp hpair
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((measurable_pi_apply i).comp hTm).aemeasurable)).2
  change (P'.prod P).map T = _
  calc
    _ = Measure.pi M := hjoint
    _ = _ := by
      congr 1
      funext i
      exact (hmarg i).symm

/-- A variable on the first probability factor can be appended after the independent family. -/
theorem iIndepFun_fin_snoc_prod {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {n : ℕ} (A : Ω' → X) (B : Fin n → Ω → X) (hA : Measurable A)
    (hB : ∀ i, Measurable (B i)) (hind : iIndepFun B P) :
    iIndepFun (fun i : Fin (n + 1) => fun ω : Ω' × Ω =>
      Fin.snoc (α := fun _ : Fin (n + 1) => X) (fun j => B j ω.2) (A ω.1) i) (P'.prod P) := by
  have h := iIndepFun_fin_cons_prod P P' A B hA hB hind
  have hr := iIndepFun.precomp (finRotate (n + 1)).injective h
  simpa only [Fin.snoc_eq_cons_rotate] using hr

/-- Adjoining an independent-coordinate variable to a finite vector preserves measurability. -/
theorem measurable_fin_snoc_prod {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] {n : ℕ}
    (A : Ω' → X) (B : Fin n → Ω → X) (hA : Measurable A) (hB : ∀ i, Measurable (B i)) :
    Measurable (fun ω : Ω' × Ω => Fin.snoc (α := fun _ : Fin (n + 1) => X)
      (fun i => B i ω.2) (A ω.1)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last, Function.comp_def] using hA.comp measurable_fst
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using (hB j).comp measurable_snd

/-- An independent block tuple has the same joint law after moving its final coordinate to an independent probability copy. -/
theorem iIndepFun.map_eq_map_snoc_prod {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (B : Fin (n + 1) → Ω → X) (hB : ∀ i, Measurable (B i)) (hind : iIndepFun B P) :
    P.map (fun ω i => B i ω) =
      (P.prod P).map (fun ω : Ω × Ω => Fin.snoc (α := fun _ : Fin (n + 1) => X)
        (fun i => B i.castSucc ω.2) (B (Fin.last n) ω.1)) := by
  have hPrefix : iIndepFun (fun i : Fin n => B i.castSucc) P :=
    hind.precomp (Fin.castSucc_injective n)
  have hCopy := iIndepFun_fin_snoc_prod P P (B (Fin.last n)) (fun i : Fin n => B i.castSucc)
    (hB _) (fun i => hB _) hPrefix
  have hCopyMeas (i : Fin (n + 1)) : Measurable (fun ω : Ω × Ω =>
      Fin.snoc (α := fun _ : Fin (n + 1) => X) (fun j => B j.castSucc ω.2) (B (Fin.last n) ω.1) i) :=
    (measurable_pi_apply i).comp (measurable_fin_snoc_prod (B (Fin.last n))
      (fun j : Fin n => B j.castSucc) (hB _) (fun j => hB _))
  rw [hind.map_fun_eq_pi_map (fun i => (hB i).aemeasurable),
    hCopy.map_fun_eq_pi_map (fun i => (hCopyMeas i).aemeasurable)]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have hmap := congrArg (fun ν : Measure Ω => ν.map (B (Fin.last n)))
      (measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).map_eq
    rw [Measure.map_map (hB (Fin.last n)) measurable_fst] at hmap
    simpa only [Function.comp_def] using hmap.symm
  · simp only [Fin.snoc_castSucc]
    have hmap := congrArg (fun ν : Measure Ω => ν.map (B j.castSucc))
      (measurePreserving_snd : MeasurePreserving Prod.snd (P.prod P) P).map_eq
    rw [Measure.map_map (hB j.castSucc) measurable_snd] at hmap
    simpa only [Function.comp_def] using hmap.symm

/-- Moving the last independent block to another copy preserves its joint law with any measurable prefix factor. -/
theorem iIndepFun.map_eq_map_snoc_prod_with_factor {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (B : Fin (n + 1) → Ω → X) (hB : ∀ i, Measurable (B i)) (hind : iIndepFun B P)
    (C : Ω → Y) (φ : (Fin n → X) → Y) (hφ : Measurable φ)
    (hC : C =ᵐ[P] fun ω => φ (fun i => B i.castSucc ω)) :
    P.map (fun ω => ((fun i => B i ω), C ω)) =
      (P.prod P).map (fun ω : Ω × Ω =>
        (Fin.snoc (α := fun _ : Fin (n + 1) => X) (fun i => B i.castSucc ω.2)
          (B (Fin.last n) ω.1), C ω.2)) := by
  let Ψ (μ : Fin (n + 1) → X) := (μ, φ (fun i : Fin n => μ i.castSucc))
  have hΨ : Measurable Ψ := measurable_id.prodMk
    (hφ.comp (Measurable.of_eval (fun i => measurable_pi_apply i.castSucc)))
  have hMap := congrArg (fun ν : Measure (Fin (n + 1) → X) => ν.map Ψ)
    (iIndepFun.map_eq_map_snoc_prod P n B hB hind)
  rw [Measure.map_map hΨ (Measurable.of_eval hB),
    Measure.map_map hΨ (measurable_fin_snoc_prod (B (Fin.last n)) (fun i : Fin n => B i.castSucc)
      (hB _) (fun i => hB _))] at hMap
  have hSrc : (fun ω => ((fun i => B i ω), C ω)) =ᵐ[P] Ψ ∘ (fun ω i => B i ω) := by
    filter_upwards [hC] with ω hω
    change ((fun i => B i ω), C ω) = ((fun i => B i ω), φ (fun i => B i.castSucc ω))
    rw [hω]
  have hTgt : (fun ω : Ω × Ω =>
      (Fin.snoc (α := fun _ : Fin (n + 1) => X) (fun i => B i.castSucc ω.2)
        (B (Fin.last n) ω.1), C ω.2)) =ᵐ[P.prod P]
      Ψ ∘ (fun ω : Ω × Ω => Fin.snoc (α := fun _ : Fin (n + 1) => X)
        (fun i => B i.castSucc ω.2) (B (Fin.last n) ω.1)) := by
    filter_upwards [(measurePreserving_snd : MeasurePreserving Prod.snd (P.prod P) P).quasiMeasurePreserving.ae hC]
      with ω hω
    change (_, C ω.2) = (_, φ (fun i : Fin n => Fin.snoc (α := fun _ : Fin (n + 1) => X)
      (fun i => B i.castSucc ω.2) (B (Fin.last n) ω.1) i.castSucc))
    simp only [Fin.snoc_castSucc]
    rw [hω]
  rw [Measure.map_congr hSrc, Measure.map_congr hTgt]
  exact hMap

end Critical2DKPZ.SHF.Tsai

end
