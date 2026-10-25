/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Definitions.ScalePath
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Compact sets of paths with a common modulus

A bound at time zero and countably many common oscillation bounds give compact
sets in the uniform topology. These are the deterministic sets used for tightness.
-/

@[expose] public section
noncomputable section
open TopologicalSpace Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A local oscillation bound propagates a bound at zero across a compact interval. -/
theorem exists_bound_of_local_modulus (S : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ f : ScalePath S,
      (∀ s r : ScaleInterval S, dist (s : ℝ) (r : ℝ) ≤ δ → |f s - f r| ≤ 1) →
      ∀ s, |f s| ≤ |f ⟨0, by simp⟩| + C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((S : ℝ) / δ) 0)
  have hNp : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hstep : (S : ℝ) / N ≤ δ := by
    apply (div_le_iff₀ hNp).mpr
    have hh := (div_lt_iff₀ hδ).mp (lt_of_le_of_lt (le_max_left _ _) hN)
    nlinarith
  refine ⟨N, ?_⟩
  intro f hf s
  let p : (k : ℕ) → k ≤ N → ScaleInterval S := fun k hk =>
    ⟨(k : ℝ) / N * s, by
      constructor
      · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hNp.le) s.property.1
      · have hk' : (k : ℝ) / N ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast hk)
        exact (mul_le_of_le_one_left s.property.1 hk').trans s.property.2⟩
  have hp : ∀ k (hk : k ≤ N), |f (p k hk)| ≤ |f ⟨0, by simp⟩| + k := by
    intro k
    induction k with
    | zero => intro hk; simp [p]
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      have hd : dist ((p (k+1) hk : ScaleInterval S) : ℝ) (p k hk' : ℝ) ≤ δ := by
        change |((k+1 : ℕ) : ℝ) / N * (s : ℝ) - (k : ℝ) / N * s| ≤ δ
        have hid : ((k+1 : ℕ) : ℝ) / N * (s : ℝ) - (k : ℝ) / N * s = (s : ℝ) / N := by
          push_cast
          ring
        rw [hid, abs_of_nonneg (div_nonneg s.property.1 hNp.le)]
        exact (div_le_div_of_nonneg_right s.property.2 hNp.le).trans hstep
      have hosc := hf (p (k+1) hk) (p k hk') hd
      have htri : |f (p (k+1) hk)| ≤ |f (p (k+1) hk) - f (p k hk')| + |f (p k hk')| := by
        simpa only [sub_add_cancel] using abs_add_le (f (p (k+1) hk) - f (p k hk')) (f (p k hk'))
      have hi := ih hk'
      push_cast
      linarith
  simpa [p, hNp.ne'] using hp N (le_refl N)

/-- Arzelà–Ascoli on compact real-path spaces, stated with a uniform range bound. -/
theorem isCompact_of_closed_equicontinuous {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Set C(K, ℝ)) (hA : IsClosed A) (heq : Equicontinuous (fun f : A => (f : C(K, ℝ))))
    (M : ℝ) (hM : ∀ f ∈ A, ∀ x, |f x| ≤ M) : IsCompact A := by
  let e := (ContinuousMap.isometryEquivBoundedOfCompact K ℝ : C(K, ℝ) ≃ᵢ (K →ᵇ ℝ)).toHomeomorph
  have hclosed : IsClosed (e '' A) := e.isClosedMap _ hA
  have hcomp : IsCompact (e '' A) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (-M) M) isCompact_Icc _ hclosed
    · intro f x hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact abs_le.mp (hM g hg x)
    · let q : (e '' A) → A := fun f => ⟨e.symm f, by
        obtain ⟨g, hg, he⟩ := f.property
        simpa only [← he, e.symm_apply_apply] using hg⟩
      exact heq.comp q
  exact e.isCompact_image.mp hcomp

/-- Paths bounded at zero and with a specified sequence of common oscillation bounds. -/
def modulusCompactSet (S : ℝ≥0) (M : ℝ) (δ : ℕ → ℝ) : Set (ScalePath S) :=
  {f | |f ⟨0, by simp⟩| ≤ M ∧ ∀ n (s r : ScaleInterval S),
    dist (s : ℝ) (r : ℝ) ≤ δ n → |f s - f r| ≤ 1 / ((n : ℝ) + 1)}

/-- The modulus constraints are closed in the uniform topology. -/
theorem isClosed_modulusCompactSet (S : ℝ≥0) (M : ℝ) (δ : ℕ → ℝ) :
    IsClosed (modulusCompactSet S M δ) := by
  have hev (s : ScaleInterval S) : Continuous (fun f : ScalePath S => f s) := by fun_prop
  apply IsClosed.inter
  · exact isClosed_le ((hev _).abs) continuous_const
  · have hh (n : ℕ) (s r : ScaleInterval S) :
        IsClosed {f : ScalePath S | |f s - f r| ≤ 1 / ((n : ℝ) + 1)} :=
      isClosed_le (((hev s).sub (hev r)).abs) continuous_const
    convert (isClosed_iInter (fun n : ℕ => isClosed_iInter (fun s : ScaleInterval S =>
      isClosed_iInter (fun r : ScaleInterval S => isClosed_iInter
        (fun _ : dist (s : ℝ) (r : ℝ) ≤ δ n => hh n s r))))) using 2
    apply Iff.of_eq
    congr 1
    ext f
    change (∀ n (s r : ScaleInterval S), dist (s : ℝ) (r : ℝ) ≤ δ n →
      |f s - f r| ≤ 1 / ((n : ℝ) + 1)) ↔ _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]

/-- The countable modulus constraints imply equicontinuity. -/
theorem equicontinuous_modulusCompactSet (S : ℝ≥0) (M : ℝ) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 < δ n) :
    Equicontinuous (fun f : modulusCompactSet S M δ => (f : ScalePath S)) := by
  apply UniformEquicontinuous.equicontinuous
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨δ n, hδ n, ?_⟩
  intro s r hsr f
  change |f.val s - f.val r| < ε
  exact (f.property.2 n s r hsr.le).trans_lt hn

/-- Arzelà–Ascoli compactness from the initial bound and positive modulus scales. -/
theorem isCompact_modulusCompactSet (S : ℝ≥0) (M : ℝ) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 < δ n) : IsCompact (modulusCompactSet S M δ) := by
  obtain ⟨C, hC⟩ := exists_bound_of_local_modulus S (hδ 0)
  apply isCompact_of_closed_equicontinuous _ (isClosed_modulusCompactSet S M δ)
    (equicontinuous_modulusCompactSet S M δ hδ) (M + C)
  intro f hf s
  have hlocal : ∀ s r : ScaleInterval S,
      dist (s : ℝ) (r : ℝ) ≤ δ 0 → |f s - f r| ≤ 1 := by
    simpa using hf.2 0
  have hh := hC f hlocal s
  linarith [hf.1]

end Critical2DKPZ.Extensions.ScaleLimit
