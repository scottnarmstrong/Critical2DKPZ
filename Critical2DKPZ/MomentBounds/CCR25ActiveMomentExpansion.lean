/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25ActivePathCompression
public import Critical2DKPZ.MomentBounds.CCR25ActiveGapTimes
public import Critical2DKPZ.MomentBounds.CCR25GapRunEncoding
public import Critical2DKPZ.MomentBounds.CCR25GapRunPath
public import Critical2DKPZ.MomentBounds.CCR25RunExpansion
public import Critical2DKPZ.MomentBounds.CCR25StartBoundaryIdentity
import Mathlib.Tactic

/-! # Start-profile moments as active collision-path sums -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds


/-- The absolute centered moment of a finitely supported nonnegative starting profile is bounded by the sum of its moment-weighted active paths. -/
theorem abs_centeredMoment_profileP2Fun_le_activeMomentSum {h L : ℕ}
    (β : ℝ) (φ : Site → ℝ) (A : Finset Site)
    (hφ : ∀ z, 0 ≤ φ z) (hφA : ∀ z ∉ A, φ z = 0) :
    |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
      ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ∑ I ∈ fullSupportSequences h L,
            ccr25ActiveMomentKernelPathWeight β ⊥
              (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) w := by
  classical
  let starts : Finset (LatticeConfiguration h) :=
    Fintype.piFinset (fun _ : Fin h => A)
  have hexpansion := centeredMoment_profileP2Fun_eq_sum_starts (h := h) β L φ A hφA
  rw [hexpansion]
  have hweight (w : LatticeConfiguration h) : 0 ≤ ∏ i : Fin h, φ (w i) :=
    Finset.prod_nonneg fun i hi => hφ (w i)
  calc
    |∑ w ∈ starts,
        (∏ i : Fin h, φ (w i)) *
          ∫ ω, ∏ i : Fin h,
            (Critical2DKPZ.pointToPlane β 0 L (w i) ω - 1) ∂disorderLaw| ≤
      ∑ w ∈ starts,
        |(∏ i : Fin h, φ (w i)) *
          ∫ ω, ∏ i : Fin h,
            (Critical2DKPZ.pointToPlane β 0 L (w i) ω - 1) ∂disorderLaw| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w ∈ starts,
        (∏ i : Fin h, φ (w i)) *
          |∫ ω, ∏ i : Fin h,
            (Critical2DKPZ.pointToPlane β 0 L (w i) ω - 1) ∂disorderLaw| := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [abs_mul, abs_of_nonneg (hweight w)]
    _ ≤ ∑ w ∈ starts,
        (∏ i : Fin h, φ (w i)) *
          ∑ I ∈ fullSupportSequences h L,
            (∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) *
              replicaPathWeight (List.ofFn I) w := by
      apply Finset.sum_le_sum
      intro w hw
      apply mul_le_mul_of_nonneg_left
      · exact abs_integral_prod_pointToPlane_sub_one_le_abs_partitionSum
          (h := h) (n := L) β 0 w
      · exact hweight w
    _ = ∑ w ∈ starts,
        (∏ i : Fin h, φ (w i)) *
          ∑ I ∈ fullSupportSequences h L,
            ccr25ActiveMomentKernelPathWeight β ⊥
              (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) w := by
      apply Finset.sum_congr rfl
      intro w hw
      apply congrArg (fun x : ℝ => (∏ i : Fin h, φ (w i)) * x)
      apply Finset.sum_congr rfl
      intro I hI
      exact absMoment_mul_replicaPathWeight_eq_activeMomentKernelPathWeight β I w




/-- The finite image of full-support time partitions under maximal gap-run
encoding. Each record stores its label, entry gap and internal gaps. -/
noncomputable def ccr25FullSupportGapRunStreams (h L : ℕ) :
    Finset (List (CCR25GapRun h)) := by
  classical
  exact (fullSupportSequences h L).image fun I =>
    ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))

/-- Reindex the start-profile moment expansion directly by maximal collision
gap runs. Their labels and all timing data are retained exactly. -/
theorem fullSupport_startProfile_momentSum_eq_sum_gapRunImage
    {h L : ℕ} (β : ℝ) (A : Finset Site) (φ : Site → ℝ) :
    (∑ I ∈ fullSupportSequences h L,
      ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ((∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) *
            replicaPathWeight (List.ofFn I) w)) =
      ∑ runs ∈ ccr25FullSupportGapRunStreams h L,
        ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (w i)) *
            ccr25ActiveMomentKernelPathWeight β ⊥
              (ccr25GapRunExpand runs) w := by
  classical
  let F := fullSupportSequences h L
  let encode : (Fin L → ReplicaPartition h) → List (CCR25GapRun h) :=
    fun I => ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))
  let G : List (CCR25GapRun h) → ℝ := fun runs =>
    ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (w i)) *
        ccr25ActiveMomentKernelPathWeight β ⊥ (ccr25GapRunExpand runs) w
  calc
    (∑ I ∈ F,
        ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (w i)) *
            ((∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) *
              replicaPathWeight (List.ofFn I) w)) =
      ∑ I ∈ F, G (encode I) := by
        apply Finset.sum_congr rfl
        intro I hI
        dsimp [G, encode]
        apply Finset.sum_congr rfl
        intro w hw
        rw [ccr25GapRunExpand_encode,
          absMoment_mul_replicaPathWeight_eq_activeMomentKernelPathWeight β I w]
    _ = ∑ runs ∈ F.image encode, G runs := by
      symm
      apply Finset.sum_image
      intro I hI J hJ heq
      apply ccr25ActiveGapEncodeFrom_zero_ofFn_injective
      have hExpand := congrArg ccr25GapRunExpand heq
      simpa only [encode, ccr25GapRunExpand_encode] using hExpand

/-- Reindex the full-support start-profile expansion directly by maximal
gap-run paths. Unlike the active-event representation, each run record keeps
its full internal gap list, so no duration has yet been summed out. -/
theorem fullSupport_startProfile_momentSum_eq_sum_gapRunPathImage
    {h L : ℕ} (β : ℝ) (A : Finset Site) (φ : Site → ℝ) :
    (∑ I ∈ fullSupportSequences h L,
      ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ((∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) *
            replicaPathWeight (List.ofFn I) w)) =
      ∑ runs ∈ ccr25FullSupportGapRunStreams h L,
        ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (w i)) *
            ccr25GapRunPathWeight β ⊥ runs w := by
  classical
  let F := fullSupportSequences h L
  let encode : (Fin L → ReplicaPartition h) → List (CCR25GapRun h) :=
    fun I => ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))
  let G : List (CCR25GapRun h) → ℝ := fun runs =>
    ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (w i)) * ccr25GapRunPathWeight β ⊥ runs w
  calc
    (∑ I ∈ F,
        ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (w i)) *
            ((∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) *
              replicaPathWeight (List.ofFn I) w)) =
      ∑ runs ∈ F.image encode,
        ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (w i)) *
            ccr25ActiveMomentKernelPathWeight β ⊥
              (ccr25GapRunExpand runs) w := by
        simpa [F, encode, G, ccr25FullSupportGapRunStreams] using
          fullSupport_startProfile_momentSum_eq_sum_gapRunImage β A φ
    _ = ∑ runs ∈ F.image encode, G runs := by
        apply Finset.sum_congr rfl
        intro runs hruns
        apply Finset.sum_congr rfl
        intro w hw
        apply congrArg (fun v : ℝ => (∏ i : Fin h, φ (w i)) * v)
        obtain ⟨I, hI, hrun⟩ := Finset.mem_image.mp hruns
        have hencodeExpand :
            ccr25GapRunEncode (ccr25GapRunExpand runs) = runs := by
          have h := congrArg ccr25GapRunEncode
            (ccr25GapRunExpand_encode
              (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)))
          simpa [encode, hrun] using h
        rw [ccr25ActiveMomentKernelPathWeight_eq_runFactored,
          ccr25ActiveRunFactoredPathWeight_eq_gapRunPathWeight,
          hencodeExpand]
    _ = ∑ runs ∈ ccr25FullSupportGapRunStreams h L, G runs := by
        rfl

end Critical2DKPZ.MomentBounds

end
