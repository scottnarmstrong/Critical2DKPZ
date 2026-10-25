/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ThreeBlockMergeRight
public import Critical2DKPZ.SHF.Tsai.ThreeBlockMergeLeft
import Critical2DKPZ.SHF.Tsai.JointScalarLimits

/-! # Common limits of three-block and composed pairings

The joint three-block expectation and either adjacent-composed two-block expectation have
the same limit as the connector indices tend to infinity.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The joint three-block expectation and the right-merged two-block expectation have the same limit. -/
theorem exists_integral_threeBlockPairing_merge_right_limit {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    (A : Ω' → Measure (Plane × Plane)) {τA : ℝ} (hτA : 0 < τA) (hA : HasDeltaBoseMoments θ τA P' A)
    {a b t : ℝ} (ha : a ∈ D) (hb : b ∈ D) (ht : t ∈ D) (hab : a < b) (hbt : b < t)
    (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    ∃ L : ℝ,
      Tendsto (fun q : ℕ × ℕ => ∫ ω, H (threeBlockPairing
        ![fun ω : Ω' × Ω => A ω.1, fun ω => Z a b ω.2, fun ω => Z b t ω.2]
        u g g' q.1 q.2 ω) ∂P'.prod P) atTop (𝓝 L) ∧
      Tendsto (fun ℓ => ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (A ω.1) (u ℓ) (Z a t ω.2)) ∂P'.prod P) atTop (𝓝 L) := by
  classical
  let Bs (i : Fin 2) := if (i : ℕ) = 0 then Z a b else Z b t
  have hBs (i : Fin 2) : Measurable (Bs i) := by
    fin_cases i
    · exact (hZ.1 a ha b hb hab).1
    · exact (hZ.1 b hb t ht hbt).1
  let B (i : Fin 3) (ω : Ω' × Ω) :=
    Fin.cons (α := fun _ : Fin 3 => Measure (Plane × Plane)) (A ω.1) (fun j => Bs j ω.2) i
  let σ : Fin 3 → ℝ := ![τA, b - a, t - b]
  have hσ (i : Fin 3) : 0 < σ i := by
    fin_cases i
    · exact hτA
    · exact sub_pos.2 hab
    · exact sub_pos.2 hbt
  have hB (i : Fin 3) : HasDeltaBoseMoments θ (σ i) (P'.prod P) (B i) := by
    fin_cases i
    · exact hA.comp_measurePreserving measurePreserving_fst
    · exact (hZ.hasDeltaBoseMoments ha hb hab).comp_measurePreserving measurePreserving_snd
    · exact (hZ.hasDeltaBoseMoments hb ht hbt).comp_measurePreserving measurePreserving_snd
  have hind : iIndepFun B (P'.prod P) := iIndepFun_fin_cons_prod P P' A Bs hA.1 hBs
    (hZ.iIndepFun_twoConsecutive ha hb ht hab hbt)
  have hBeq : B = ![fun ω : Ω' × Ω => A ω.1, fun ω => Z a b ω.2, fun ω => Z b t ω.2] := by
    funext i ω
    fin_cases i <;> rfl
  obtain ⟨L, hJoint⟩ := tendsto_integral_threeBlockPairing σ hσ B hB hind u hu g g' H hH CH hCH
  rw [hBeq] at hJoint
  refine ⟨L, hJoint, ?_⟩
  have hswap : Tendsto (Prod.swap : ℕ × ℕ → ℕ × ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_prod_swap
  exact tendsto_of_joint_of_scalar_fiber_limits _ _ L (hJoint.comp hswap)
    (fun ℓ => tendsto_integral_threeBlockPairing_merge_right D P P' Z hZ A hτA hA
      ha hb ht hab hbt u hu g g' H hH CH hCH ℓ)

/-- The joint three-block expectation and the left-merged two-block expectation have the same limit. -/
theorem exists_integral_threeBlockPairing_merge_left_limit {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (hZ' : IsDenseSHF θ D P' Z')
    (C : Ω → Measure (Plane × Plane)) {τC : ℝ} (hτC : 0 < τC) (hC : HasDeltaBoseMoments θ τC P C)
    {s a b : ℝ} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hsa : s < a) (hab : a < b)
    (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    ∃ L : ℝ,
      Tendsto (fun q : ℕ × ℕ => ∫ ω, H (threeBlockPairing
        ![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z' a b ω.1, fun ω => C ω.2]
        u g g' q.1 q.2 ω) ∂P'.prod P) atTop (𝓝 L) ∧
      Tendsto (fun ℓ => ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s b ω.1) (u ℓ) (C ω.2)) ∂P'.prod P) atTop (𝓝 L) := by
  classical
  let Bs (i : Fin 2) := if (i : ℕ) = 0 then Z' s a else Z' a b
  have hBs (i : Fin 2) : Measurable (Bs i) := by
    fin_cases i
    · exact (hZ'.1 s hs a ha hsa).1
    · exact (hZ'.1 a ha b hb hab).1
  let B (i : Fin 3) (ω : Ω × Ω') :=
    Fin.snoc (α := fun _ : Fin 3 => Measure (Plane × Plane)) (fun j => Bs j ω.2) (C ω.1) i
  let σ : Fin 3 → ℝ := ![a - s, b - a, τC]
  have hσ (i : Fin 3) : 0 < σ i := by
    fin_cases i
    · exact sub_pos.2 hsa
    · exact sub_pos.2 hab
    · exact hτC
  have hB (i : Fin 3) : HasDeltaBoseMoments θ (σ i) (P.prod P') (B i) := by
    fin_cases i
    · exact (hZ'.hasDeltaBoseMoments hs ha hsa).comp_measurePreserving measurePreserving_snd
    · exact (hZ'.hasDeltaBoseMoments ha hb hab).comp_measurePreserving measurePreserving_snd
    · exact hC.comp_measurePreserving measurePreserving_fst
  have hind : iIndepFun B (P.prod P') := iIndepFun_fin_snoc_prod P' P C Bs hC.1 hBs
    (hZ'.iIndepFun_twoConsecutive hs ha hb hsa hab)
  obtain ⟨L, hJoint⟩ := tendsto_integral_threeBlockPairing σ hσ B hB hind u hu g g' H hH CH hCH
  have hswap (q : ℕ × ℕ) : (∫ ω, H (threeBlockPairing B u g g' q.1 q.2 ω) ∂P.prod P') =
      ∫ ω, H (threeBlockPairing
        ![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z' a b ω.1, fun ω => C ω.2]
        u g g' q.1 q.2 ω) ∂P'.prod P := by
    calc
      _ = ∫ ω : Ω' × Ω, H (threeBlockPairing B u g g' q.1 q.2 ω.swap) ∂P'.prod P :=
        integral_prod_swap (fun ω : Ω' × Ω => H (threeBlockPairing B u g g' q.1 q.2 ω.swap))
      _ = _ := by rfl
  simp only [hswap] at hJoint
  exact ⟨L, hJoint, tendsto_of_joint_of_scalar_fiber_limits _ _ L hJoint
    (fun ℓ => tendsto_integral_threeBlockPairing_merge_left D P P' Z' hZ' C hτC hC
      hs ha hb hsa hab u hu g g' H hH CH hCH ℓ)⟩

end Critical2DKPZ.SHF.Tsai

end
