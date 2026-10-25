/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.IndependentProductFamilies
public import Critical2DKPZ.SHF.Tsai.TensorComposition

/-! # Mutual independence of the four hybrid replacement increments

The left process supplies the prefix and replacement middle increment; the
right process supplies the original middle and suffix. Consecutive-increment
independence within each process and the product coupling combine all four.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- The prefix, original middle, suffix, and replacement middle blocks are mutually independent. -/
theorem IsDenseSHF.iIndepFun_hybridSwap {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a b t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D) (ht : t ∈ D)
    (hsa : s < a) (hab : a < b) (hbt : b < t) :
    iIndepFun (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a b ω.2,
      fun ω => Z b t ω.2, fun ω => Z' a b ω.1] : Fin 4 → Ω' × Ω → Measure (Plane × Plane)) (P'.prod P) := by
  classical
  let A (i : Fin 2) := if (i : ℕ) = 0 then Z' s a else Z' a b
  let B (i : Fin 2) := if (i : ℕ) = 0 then Z a b else Z b t
  have hA (i : Fin 2) : Measurable (A i) := by
    fin_cases i
    · exact (hZ'.1 s hs a ha hsa).1
    · exact (hZ'.1 a ha b hb hab).1
  have hB (i : Fin 2) : Measurable (B i) := by
    fin_cases i
    · exact (hZ.1 a ha b hb hab).1
    · exact (hZ.1 b hb t ht hbt).1
  have h := iIndepFun_prod_families P P' A B hA hB
    (hZ'.iIndepFun_twoConsecutive hs ha hb hsa hab)
    (hZ.iIndepFun_twoConsecutive ha hb ht hab hbt)
  let e : Fin 4 → Fin 2 × Fin 2 := ![(0, 0), (1, 0), (1, 1), (0, 1)]
  have he : Function.Injective e := by decide
  have hperm := h.precomp he
  have heq : (fun i : Fin 4 => fun ω : Ω' × Ω =>
      if ((e i).1 : ℕ) = 0 then A (e i).2 ω.1 else B (e i).2 ω.2) =
      (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a b ω.2,
        fun ω => Z b t ω.2, fun ω => Z' a b ω.1] : Fin 4 → Ω' × Ω → Measure (Plane × Plane)) := by
    funext i ω
    fin_cases i <;> rfl
  rwa [heq] at hperm

/-- At the initial endpoint, the original first block, suffix, and independent replacement are mutually independent. -/
theorem IsDenseSHF.iIndepFun_hybridSwap_leftEndpoint {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s b t : ℝ} (hs : s ∈ D) (hb : b ∈ D) (ht : t ∈ D) (hsb : s < b) (hbt : b < t) :
    iIndepFun (![fun ω : Ω' × Ω => Z s b ω.2, fun ω => Z b t ω.2,
      fun ω => Z' s b ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) (P'.prod P) := by
  classical
  let B (i : Fin 2) := if (i : ℕ) = 0 then Z s b else Z b t
  have hB (i : Fin 2) : Measurable (B i) := by
    fin_cases i
    · exact (hZ.1 s hs b hb hsb).1
    · exact (hZ.1 b hb t ht hbt).1
  have h := iIndepFun_fin_snoc_prod P P' (Z' s b) B (hZ'.1 s hs b hb hsb).1 hB
    (hZ.iIndepFun_twoConsecutive hs hb ht hsb hbt)
  have heq : (fun i : Fin 3 => fun ω : Ω' × Ω =>
      Fin.snoc (α := fun _ : Fin 3 => Measure (Plane × Plane)) (fun j => B j ω.2) (Z' s b ω.1) i) =
      (![fun ω : Ω' × Ω => Z s b ω.2, fun ω => Z b t ω.2,
        fun ω => Z' s b ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) := by
    funext i ω
    fin_cases i <;> rfl
  rwa [heq] at h

/-- At the terminal endpoint, the prefix, original last block, and replacement last block are mutually independent. -/
theorem IsDenseSHF.iIndepFun_hybridSwap_rightEndpoint {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (ht : t ∈ D) (hsa : s < a) (hat : a < t) :
    iIndepFun (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a t ω.2,
      fun ω => Z' a t ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) (P'.prod P) := by
  classical
  let B (i : Fin 2) := if (i : ℕ) = 0 then Z' s a else Z' a t
  have hB (i : Fin 2) : Measurable (B i) := by
    fin_cases i
    · exact (hZ'.1 s hs a ha hsa).1
    · exact (hZ'.1 a ha t ht hat).1
  let R (i : Fin 3) (ω : Ω × Ω') :=
    Fin.snoc (α := fun _ : Fin 3 => Measure (Plane × Plane)) (fun j => B j ω.2) (Z a t ω.1) i
  have hR : iIndepFun R (P.prod P') := iIndepFun_fin_snoc_prod P' P (Z a t) B
    (hZ.1 a ha t ht hat).1 hB (hZ'.iIndepFun_twoConsecutive hs ha ht hsa hat)
  have hRm (i : Fin 3) : Measurable (R i) := by
    fin_cases i
    · exact (hZ'.1 s hs a ha hsa).1.comp measurable_snd
    · exact (hZ'.1 a ha t ht hat).1.comp measurable_snd
    · exact (hZ.1 a ha t ht hat).1.comp measurable_fst
  have hCopy := iIndepFun_comp_measurePreserving R hRm hR
    (Measure.measurePreserving_swap : MeasurePreserving Prod.swap (P'.prod P) (P.prod P'))
  let e : Fin 3 → Fin 3 := ![0, 2, 1]
  have he : Function.Injective e := by decide
  have hperm := hCopy.precomp he
  have heq : (fun i : Fin 3 => fun ω : Ω' × Ω => R (e i) ω.swap) =
      (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a t ω.2,
        fun ω => Z' a t ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) := by
    funext i ω
    fin_cases i <;> rfl
  rwa [heq] at hperm

end Critical2DKPZ.SHF.Tsai

end
