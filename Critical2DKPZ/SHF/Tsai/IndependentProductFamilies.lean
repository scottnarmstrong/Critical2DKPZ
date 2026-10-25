/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CouplingIndependence
public import Critical2DKPZ.SHF.Tsai.IndependenceTransport
import Mathlib.Probability.Independence.InfinitePi

/-! # Combining independent families on the two coupling coordinates

The two vector-valued families are independent on a product measure. Pullback
preserves independence within each vector, and the uncurry theorem flattens
the two groups into one mutually independent family.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Two finite independent families on separate coordinates remain mutually independent together. -/
theorem iIndepFun_prod_families {Ω Ω' ι X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [MeasurableSpace X]
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (A : ι → Ω' → X) (B : ι → Ω → X)
    (hA : ∀ i, Measurable (A i)) (hB : ∀ i, Measurable (B i))
    (hindA : iIndepFun A P') (hindB : iIndepFun B P) :
    iIndepFun (fun ij : Fin 2 × ι => fun ω : Ω' × Ω =>
      if (ij.1 : ℕ) = 0 then A ij.2 ω.1 else B ij.2 ω.2) (P'.prod P) := by
  classical
  let F (i : Fin 2) (j : ι) (ω : Ω' × Ω) :=
    if (i : ℕ) = 0 then A j ω.1 else B j ω.2
  have hFm (i : Fin 2) (j : ι) : Measurable (F i j) := by
    fin_cases i
    · exact (hA j).comp measurable_fst
    · exact (hB j).comp measurable_snd
  have hind1 : iIndepFun (fun _ : Fin 1 => fun ω j => B j ω) P := iIndepFun.of_subsingleton
  have hGroup := iIndepFun_fin_cons_prod P P' (fun ω j => A j ω)
    (fun _ : Fin 1 => fun ω j => B j ω) (Measurable.of_eval hA)
    (fun _ => Measurable.of_eval hB) hind1
  have h1 : iIndepFun (fun i : Fin 2 => fun ω => fun j => F i j ω) (P'.prod P) := by
    have heq : (fun i : Fin 2 => fun ω : Ω' × Ω => fun j => F i j ω) =
        (fun i : Fin 2 => fun ω : Ω' × Ω =>
          Fin.cons (α := fun _ : Fin 2 => ι → X) (fun j => A j ω.1)
            (fun _ => fun j => B j ω.2) i) := by
      funext i ω j
      fin_cases i <;> rfl
    rw [heq]
    exact hGroup
  have h2 (i : Fin 2) : iIndepFun (F i) (P'.prod P) := by
    fin_cases i
    · exact iIndepFun_comp_measurePreserving A hA hindA
        (measurePreserving_fst : MeasurePreserving Prod.fst (P'.prod P) P')
    · exact iIndepFun_comp_measurePreserving B hB hindB
        (measurePreserving_snd : MeasurePreserving Prod.snd (P'.prod P) P)
  exact iIndepFun_uncurry' hFm h1 h2

end Critical2DKPZ.SHF.Tsai

end
