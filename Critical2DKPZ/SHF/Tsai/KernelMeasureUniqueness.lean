/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.KernelMeasureRectangles

/-! # Uniqueness from configuration rectangle masses

Configuration rectangles form a generating pi-system. Finite-volume spanning
rectangles have finite kernel mass by the positive form bound. Hence equality
on rectangles determines the entire kernel measure without assuming it finite.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Rectangle identities determine a positive form-bounded kernel measure. -/
theorem kernelMeasure_eq_of_rectangles {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hF : FormBound volume volume K c) (ν : Measure (Configuration n × Configuration n))
    (hrect : ∀ A B : Fin n → Set Plane, (∀ i, MeasurableSet (A i)) → (∀ i, MeasurableSet (B i)) →
      (volume.withDensity (Function.uncurry K)) ((univ.pi A) ×ˢ (univ.pi B)) =
        ν ((univ.pi A) ×ˢ (univ.pi B))) :
    volume.withDensity (Function.uncurry K) = ν := by
  let C : Set (Set (Configuration n)) :=
    (Set.pi univ) '' Set.pi univ (fun _ : Fin n => {s : Set Plane | MeasurableSet s})
  let S : (volume : Measure (Configuration n)).FiniteSpanningSetsIn C :=
    Measure.FiniteSpanningSetsIn.pi (fun _ : Fin n => (volume : Measure Plane).toFiniteSpanningSetsIn)
  let T : (volume : Measure (Configuration n)).FiniteSpanningSetsIn
      {A | A ∈ C ∧ volume A < ⊤} := S.mono' (fun _ h => h)
  let U := T.prod T
  have hmeas {A : Set (Configuration n)} (hA : A ∈ C) : MeasurableSet A := by
    rcases hA with ⟨a, ha, rfl⟩
    exact MeasurableSet.pi (Set.to_countable univ) (fun i _ => ha i (mem_univ i))
  let V : (volume.withDensity (Function.uncurry K)).FiniteSpanningSetsIn (image2 (· ×ˢ ·) C C) :=
    { set := U.set
      set_mem := fun j => by
        rcases U.set_mem j with ⟨A, hA, B, hB, hAB⟩
        exact ⟨A, hA.1, B, hB.1, hAB⟩
      finite := fun j => by
        rcases U.set_mem j with ⟨A, hA, B, hB, hAB⟩
        rw [← hAB]
        exact kernelMeasure_rectangle_lt_top hK hc hF (hmeas hA.1) (hmeas hB.1) hA.2 hB.2
      spanning := U.spanning }
  have hgen : (inferInstance : MeasurableSpace (Configuration n × Configuration n)) =
      MeasurableSpace.generateFrom (image2 (· ×ˢ ·) C C) :=
    (generateFrom_eq_prod generateFrom_pi generateFrom_pi S.isCountablySpanning S.isCountablySpanning).symm
  apply V.ext hgen (isPiSystem_pi.prod isPiSystem_pi)
  rintro _ ⟨A, hA, B, hB, rfl⟩
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  exact hrect a b (fun i => ha i (mem_univ i)) (fun i => hb i (mem_univ i))

end Critical2DKPZ.SHF.Tsai

end
