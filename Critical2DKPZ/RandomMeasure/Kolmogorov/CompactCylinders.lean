/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
public import Mathlib.Topology.Compactness.CompactSystem
public import Mathlib.Topology.Separation.CompletelyRegular

/-! For a completely regular Hausdorff state space, cylinders with closed compact finite-dimensional bases form a compact system, even for an uncountable index set. -/

@[expose] public noncomputable section

open Set MeasureTheory

namespace Critical2DKPZ.RandomMeasure.Kolmogorov

private theorem isCompactSystem_closedCompactCylinders_nonempty {ι X : Type*}
    [TopologicalSpace X] [T35Space X] [Nonempty X] :
    IsCompactSystem (closedCompactCylinders (fun _ : ι => X)) := by
  classical
  apply IsCompactSystem.of_nonempty_iInter
  intro C hC hfinite
  choose J K hclosed hcompact hCK using fun n => (mem_closedCompactCylinders (C n)).mp (hC n)
  let e : X → StoneCech X := stoneCechUnit
  obtain ⟨r, hr⟩ := (injective_stoneCechUnit_of_t35Space (X := X)).hasLeftInverse
  let E (n : ℕ) : (J n → X) → (J n → StoneCech X) := fun z i => e (z i)
  have hE (n : ℕ) : Continuous (E n) := by
    apply continuous_pi
    intro i
    exact continuous_stoneCechUnit.comp (continuous_apply i)
  let D (n : ℕ) : Set (ι → StoneCech X) := cylinder (J n) (E n '' K n)
  have hDcompact (n : ℕ) : IsCompact (D n) := by
    have hc : IsCompact (E n '' K n) := (hcompact n).image (hE n)
    exact (hc.isClosed.preimage (J n).continuous_restrict).isCompact
  have hDfinite (n : ℕ) : (dissipate D n).Nonempty := by
    obtain ⟨x, hx⟩ := hfinite n
    refine ⟨fun i => e (x i), ?_⟩
    simp only [dissipate, mem_iInter] at hx ⊢
    intro k hk
    have hxk : x ∈ cylinder (J k) (K k) := by simpa only [← hCK k] using hx k hk
    exact ⟨(J k).restrict x, hxk, rfl⟩
  obtain ⟨y, hy⟩ := (isCompactSystem_isCompact (ι → StoneCech X)).nonempty_iInter
    (fun n => hDcompact n) hDfinite
  refine ⟨fun i => r (y i), ?_⟩
  simp only [mem_iInter] at hy ⊢
  intro n
  rw [hCK n]
  obtain ⟨z, hz, hez⟩ := hy n
  have hres : (J n).restrict (fun i => r (y i)) = z := by
    funext i
    have hi := congrFun hez i
    change e (z i) = y i at hi
    change r (y i) = z i
    rw [← hi]
    exact hr (z i)
  change (J n).restrict (fun i => r (y i)) ∈ K n
  rw [hres]
  exact hz

/-- For a completely regular Hausdorff state space, closed compact-base cylinders form a compact system for every index set. -/
theorem isCompactSystem_closedCompactCylinders {ι X : Type*}
    [TopologicalSpace X] [T35Space X] :
    IsCompactSystem (closedCompactCylinders (fun _ : ι => X)) := by
  cases isEmpty_or_nonempty X with
  | inl h =>
    apply (isCompactSystem_isCompact (ι → X)).mono
    intro s hs
    obtain ⟨J, K, hKclosed, _, rfl⟩ := (mem_closedCompactCylinders s).mp hs
    exact (hKclosed.preimage J.continuous_restrict).isCompact
  | inr h => exact isCompactSystem_closedCompactCylinders_nonempty

end Critical2DKPZ.RandomMeasure.Kolmogorov

end
