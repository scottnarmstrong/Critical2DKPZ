/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredKernel
public import Critical2DKPZ.SHF.Tsai.CoveringKernel
public import Critical2DKPZ.SHF.Tsai.CenteredKernelForms
public import Critical2DKPZ.SHF.Tsai.ChainKernels
public import Critical2DKPZ.SHF.Tsai.DiagramSpectatorFactorization
public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFinite
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Inclusion-exclusion for covering collision words

Alternating subset signs cancel words omitting a particle label, so the centered moment
kernel is almost everywhere the finite sum of diagrams touching every label.
-/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The alternating sum of subset signs vanishes unless the indexing set is empty. -/
theorem alternating_sum_powerset_card_real {α : Type*} [DecidableEq α] (s : Finset α) :
    (∑ u ∈ s.powerset, (-1 : ℝ) ^ u.card) = if s = ∅ then 1 else 0 := by
  classical
  have hz : (∑ u ∈ s.powerset, (-1 : ℤ) ^ u.card) = if s = ∅ then 1 else 0 :=
    Finset.sum_powerset_neg_one_pow_card
  exact_mod_cast hz

/-- Möbius cancellation leaves exactly the full-support term among supersets. -/
theorem alternating_sum_supersets_eq_univ {n : ℕ} (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      if T ⊆ S then (-1 : ℝ) ^ (n - S.card) else 0) =
        if T = Finset.univ then 1 else 0 := by
  classical
  let e : Finset (Fin n) ≃ Finset (Fin n) :=
    { toFun := fun S => Sᶜ
      invFun := fun S => Sᶜ
      left_inv := by intro S; simp
      right_inv := by intro S; simp }
  have hreindex :
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if T ⊆ S then (-1 : ℝ) ^ (n - S.card) else 0) =
      ∑ V ∈ (Finset.univ : Finset (Fin n)).powerset,
        if T ⊆ Vᶜ then (-1 : ℝ) ^ (n - Vᶜ.card) else 0 := by
    refine Finset.sum_equiv e (by simp) ?_
    intro S hS
    simp [e]
  rw [hreindex]
  have hcomm :
      (∑ V ∈ (Finset.univ : Finset (Fin n)).powerset,
        if T ⊆ Vᶜ then (-1 : ℝ) ^ (n - Vᶜ.card) else 0) =
      ∑ V ∈ (Finset.univ : Finset (Fin n)).powerset,
        if V ⊆ Tᶜ then (-1 : ℝ) ^ (n - Vᶜ.card) else 0 := by
    apply Finset.sum_congr rfl
    intro V hV
    simp only [Finset.subset_compl_comm]
  rw [hcomm]
  have hexp :
      (∑ V ∈ (Finset.univ : Finset (Fin n)).powerset,
        if V ⊆ Tᶜ then (-1 : ℝ) ^ (n - Vᶜ.card) else 0) =
      ∑ V ∈ (Finset.univ : Finset (Fin n)).powerset,
        if V ⊆ Tᶜ then (-1 : ℝ) ^ V.card else 0 := by
    apply Finset.sum_congr rfl
    intro V hV
    by_cases h : V ⊆ Tᶜ
    · have hle : V.card ≤ n := by
        calc
          V.card ≤ Finset.univ.card := Finset.card_le_card (Finset.mem_powerset.mp hV)
          _ = n := by simp
      have hc : Vᶜ.card = n - V.card := by simp [Finset.card_compl]
      by_cases h : V ⊆ Tᶜ
      · have hsub : n - (n - V.card) = V.card := by omega
        simp [h, hc, hsub]
      · simp [h]
    · simp [h]
  rw [hexp]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.powerset.filter (fun V : Finset (Fin n) => V ⊆ Tᶜ)) = Tᶜ.powerset := by
    ext V
    simp [Finset.mem_powerset]
  rw [hfilter]
  have hcompl : Tᶜ = ∅ ↔ T = Finset.univ := by
    constructor
    · intro h
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_contra hiNot
      have hiCompl : i ∈ Tᶜ := Finset.mem_compl.mpr hiNot
      rw [h] at hiCompl
      simp at hiCompl
    · intro h
      simp [h]
  simpa [hcompl] using alternating_sum_powerset_card_real (Tᶜ)

/-- Finite inclusion-exclusion of collision-word contributions keeps exactly
the words whose support is all labels. This is the length-by-length algebraic
step in the centered-to-covering-kernel identity. -/
theorem alternating_sum_word_support_filter {n m : ℕ}
    (D : CollisionWord n m → ℝ) :
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
      ∑ w : CollisionWord n m,
        if wordSupport w.1 ⊆ S then D w else 0) =
    ∑ w : CollisionWord n m,
      if wordSupport w.1 = Finset.univ then D w else 0 := by
  classical
  have hsubsetSum (f : Finset (Fin n) → ℝ) :
      (∑ S : Finset (Fin n), f S) =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, f S := by
    apply Finset.sum_bij (fun S _ => S)
    · intro S hS
      exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · intro S hS T hT hST
      exact hST
    · intro T hT
      exact ⟨T, Finset.mem_univ T, rfl⟩
    · intro S hS
      rfl
  simp_rw [Finset.mul_sum]
  change (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      ∑ w ∈ (Finset.univ : Finset (CollisionWord n m)),
        (-1 : ℝ) ^ (n - S.card) *
          (if wordSupport w.1 ⊆ S then D w else 0)) =
    ∑ w : CollisionWord n m,
      if wordSupport w.1 = Finset.univ then D w else 0
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have hcoeff := alternating_sum_supersets_eq_univ (wordSupport w.1)
  calc
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        (if wordSupport w.1 ⊆ S then D w else 0)) =
      D w * ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if wordSupport w.1 ⊆ S then (-1 : ℝ) ^ (n - S.card) else 0 := by
          rw [hsubsetSum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          by_cases h : wordSupport w.1 ⊆ S
          · simp [h, mul_comm]
          · simp [h]
    _ = D w * (if wordSupport w.1 = Finset.univ then 1 else 0) := by
      rw [hcoeff]
    _ = if wordSupport w.1 = Finset.univ then D w else 0 := by
      by_cases h : wordSupport w.1 = Finset.univ <;> simp [h]

private theorem supportedDiagramSeries_le_momentSeries {n : ℕ} (S : Finset (Fin n))
    (θ t : ℝ) (x y : Configuration n) :
    (∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 ⊆ S then diagramKernel θ (List.ofFn w.1) t x y else 0) ≤
      ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
        diagramKernel θ (List.ofFn w.1) t x y := by
  apply ENNReal.tsum_le_tsum
  intro m
  apply Finset.sum_le_sum
  intro w hw
  split_ifs <;> simp

private theorem mixedBlockKernel_eq_supportedDiagramSeries {n : ℕ}
    (S : Finset (Fin n)) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (x y : Configuration n) :
    mixedBlockKernel n θ t S x y =
      ENNReal.ofReal (freeKernel n t x y) +
        ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
          if wordSupport w.1 ⊆ S then
            diagramKernel θ (List.ofFn w.1) t x y else 0 := by
  rw [mixedBlockKernel]
  rw [← prod_orderEmbOfFin Sᶜ
    (fun i => ENNReal.ofReal (heatKernel t (y i - x i)))]
  exact momentKernel_subset_factor S θ ht x y

private theorem mixedBlockKernel_le_momentKernel {n : ℕ} (S : Finset (Fin n))
    (θ : ℝ) {t : ℝ} (ht : 0 < t) (x y : Configuration n) :
    mixedBlockKernel n θ t S x y ≤ momentKernel n θ t x y := by
  rw [mixedBlockKernel_eq_supportedDiagramSeries S θ ht x y,
    Critical2DKPZ.DeltaBose.momentKernel]
  exact add_le_add_right
    (supportedDiagramSeries_le_momentSeries S θ t x y)
    (ENNReal.ofReal (freeKernel n t x y))

private theorem mixedBlockKernel_toReal_eq_supportedDiagramSeries {n : ℕ}
    (S : Finset (Fin n)) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (x y : Configuration n)
    (hfull : momentKernel n θ t x y ≠ ⊤) :
    (mixedBlockKernel n θ t S x y).toReal =
      freeKernel n t x y +
        ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
          if wordSupport w.1 ⊆ S then
            (diagramKernel θ (List.ofFn w.1) t x y).toReal else 0 := by
  classical
  let W : ℕ → ℝ≥0∞ := fun m =>
    ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 ⊆ S then
        diagramKernel θ (List.ofFn w.1) t x y else 0
  let R : ℕ → ℝ := fun m =>
    ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 ⊆ S then
        (diagramKernel θ (List.ofFn w.1) t x y).toReal else 0
  have hseries_le : (∑' m : ℕ, W m) ≤ momentKernel n θ t x y := by
    rw [Critical2DKPZ.DeltaBose.momentKernel]
    calc
      (∑' m : ℕ, W m) ≤
          ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
            diagramKernel θ (List.ofFn w.1) t x y := by
              exact supportedDiagramSeries_le_momentSeries S θ t x y
      _ ≤ ENNReal.ofReal (freeKernel n t x y) +
          ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
            diagramKernel θ (List.ofFn w.1) t x y := by
              exact le_add_of_nonneg_left (by positivity)
  have hmix_ne : mixedBlockKernel n θ t S x y ≠ ⊤ :=
    ne_top_of_le_ne_top hfull (mixedBlockKernel_le_momentKernel S θ ht x y)
  have hseries_le_mix : (∑' m : ℕ, W m) ≤ mixedBlockKernel n θ t S x y := by
    rw [mixedBlockKernel_eq_supportedDiagramSeries S θ ht x y]
    calc
      (∑' m : ℕ, W m) ≤ (∑' m : ℕ, W m) + ENNReal.ofReal (freeKernel n t x y) :=
        le_self_add
      _ = ENNReal.ofReal (freeKernel n t x y) + ∑' m : ℕ, W m := add_comm _ _
  have hseries_ne : (∑' m : ℕ, W m) ≠ ⊤ :=
    ne_top_of_le_ne_top hmix_ne hseries_le_mix
  have hW_ne (m : ℕ) : W m ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top hseries_ne m
  have hterm_ne (m : ℕ) (w : CollisionWord n (m + 1)) :
      (if wordSupport w.1 ⊆ S then
        diagramKernel θ (List.ofFn w.1) t x y else 0) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (hW_ne m)
    change (if wordSupport w.1 ⊆ S then
        diagramKernel θ (List.ofFn w.1) t x y else 0) ≤
      ∑ v : CollisionWord n (m + 1),
        if wordSupport v.1 ⊆ S then
          diagramKernel θ (List.ofFn v.1) t x y else 0
    exact Finset.single_le_sum
      (f := fun v : CollisionWord n (m + 1) =>
        if wordSupport v.1 ⊆ S then
          diagramKernel θ (List.ofFn v.1) t x y else 0)
      (by intro v hv; split_ifs <;> positivity) (Finset.mem_univ w)
  have hW_real (m : ℕ) : (W m).toReal = R m := by
    change (∑ w : CollisionWord n (m + 1),
        if wordSupport w.1 ⊆ S then
          diagramKernel θ (List.ofFn w.1) t x y else 0).toReal = _
    rw [ENNReal.toReal_sum (fun w hw => hterm_ne m w)]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : wordSupport w.1 ⊆ S <;> simp [h]
  calc
    (mixedBlockKernel n θ t S x y).toReal =
        (ENNReal.ofReal (freeKernel n t x y) + ∑' m : ℕ, W m).toReal := by
          rw [mixedBlockKernel_eq_supportedDiagramSeries S θ ht x y]
    _ = freeKernel n t x y + ∑' m : ℕ, R m := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hseries_ne,
            ENNReal.toReal_ofReal (freeKernel_pos n ht x y).le,
            ENNReal.tsum_toReal_eq (fun m => hW_ne m)]
          congr 1
          apply tsum_congr
          intro m
          exact hW_real m

private theorem coveringKernel_le_momentKernel {n : ℕ} (θ t : ℝ)
    (x y : Configuration n) :
    coveringKernel n θ t x y ≤ momentKernel n θ t x y := by
  rw [coveringKernel, Critical2DKPZ.DeltaBose.momentKernel]
  calc
    (∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 = Finset.univ then
        diagramKernel θ (List.ofFn w.1) t x y else 0) ≤
        ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
          diagramKernel θ (List.ofFn w.1) t x y := by
            apply ENNReal.tsum_le_tsum
            intro m
            apply Finset.sum_le_sum
            intro w hw
            split_ifs <;> simp
    _ ≤ ENNReal.ofReal (freeKernel n t x y) +
        ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
          diagramKernel θ (List.ofFn w.1) t x y := by
            exact le_add_of_nonneg_left (by positivity)

private theorem coveringKernel_toReal_eq_wordSeries {n : ℕ} (θ t : ℝ)
    (x y : Configuration n) (hcover : coveringKernel n θ t x y ≠ ⊤) :
    (coveringKernel n θ t x y).toReal =
      ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
        if wordSupport w.1 = Finset.univ then
          (diagramKernel θ (List.ofFn w.1) t x y).toReal else 0 := by
  classical
  let W : ℕ → ℝ≥0∞ := fun m =>
    ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 = Finset.univ then
        diagramKernel θ (List.ofFn w.1) t x y else 0
  let R : ℕ → ℝ := fun m =>
    ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 = Finset.univ then
        (diagramKernel θ (List.ofFn w.1) t x y).toReal else 0
  have hWseries_ne : (∑' m : ℕ, W m) ≠ ⊤ := by
    change coveringKernel n θ t x y ≠ ⊤
    exact hcover
  have hW_ne (m : ℕ) : W m ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top hWseries_ne m
  have hterm_ne (m : ℕ) (w : CollisionWord n (m + 1)) :
      (if wordSupport w.1 = Finset.univ then
        diagramKernel θ (List.ofFn w.1) t x y else 0) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (hW_ne m)
    change (if wordSupport w.1 = Finset.univ then
        diagramKernel θ (List.ofFn w.1) t x y else 0) ≤
      ∑ v : CollisionWord n (m + 1),
        if wordSupport v.1 = Finset.univ then
          diagramKernel θ (List.ofFn v.1) t x y else 0
    exact Finset.single_le_sum
      (f := fun v : CollisionWord n (m + 1) =>
        if wordSupport v.1 = Finset.univ then
          diagramKernel θ (List.ofFn v.1) t x y else 0)
      (by intro v hv; split_ifs <;> positivity) (Finset.mem_univ w)
  have hW_real (m : ℕ) : (W m).toReal = R m := by
    change (∑ w : CollisionWord n (m + 1),
        if wordSupport w.1 = Finset.univ then
          diagramKernel θ (List.ofFn w.1) t x y else 0).toReal = _
    rw [ENNReal.toReal_sum (fun w hw => hterm_ne m w)]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : wordSupport w.1 = Finset.univ <;> simp [h]
  calc
    (coveringKernel n θ t x y).toReal = (∑' m : ℕ, W m).toReal := by
      rfl
    _ = ∑' m : ℕ, R m := by
      rw [ENNReal.tsum_toReal_eq (fun m => hW_ne m)]
      apply tsum_congr
      intro m
      exact hW_real m

/-- Almost everywhere, the centered moment kernel is the sum of diagrams whose collision
words touch every particle, and that sum is finite. -/
theorem centeredMomentKernel_eq_coveringKernel {n : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      coveringKernel n θ t xy.1 xy.2 ≠ ⊤ ∧
        centeredMomentKernel n θ t xy.1 xy.2 =
          (coveringKernel n θ t xy.1 xy.2).toReal := by
  have hmoment := Critical2DKPZ.DeltaBose.momentKernel_ne_top n hn4 θ ht
  filter_upwards [hmoment] with xy hfull
  let W : Finset (Fin n) → ℕ → ℝ≥0∞ := fun S m =>
    ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 ⊆ S then
        diagramKernel θ (List.ofFn w.1) t xy.1 xy.2 else 0
  let R : Finset (Fin n) → ℕ → ℝ := fun S m =>
    ∑ w : CollisionWord n (m + 1),
      if wordSupport w.1 ⊆ S then
        (diagramKernel θ (List.ofFn w.1) t xy.1 xy.2).toReal else 0
  have hWseries_le (S : Finset (Fin n)) :
      (∑' m : ℕ, W S m) ≤ momentKernel n θ t xy.1 xy.2 := by
    rw [Critical2DKPZ.DeltaBose.momentKernel]
    calc
      (∑' m : ℕ, W S m) ≤
          ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
            diagramKernel θ (List.ofFn w.1) t xy.1 xy.2 := by
              simpa [W] using supportedDiagramSeries_le_momentSeries
                S θ t xy.1 xy.2
      _ ≤ ENNReal.ofReal (freeKernel n t xy.1 xy.2) +
          ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
            diagramKernel θ (List.ofFn w.1) t xy.1 xy.2 :=
              le_add_of_nonneg_left (by positivity)
  have hWseries_ne (S : Finset (Fin n)) : (∑' m : ℕ, W S m) ≠ ⊤ :=
    ne_top_of_le_ne_top hfull (hWseries_le S)
  have hR_summable (S : Finset (Fin n)) : Summable (R S) := by
    have hW_ne (m : ℕ) : W S m ≠ ⊤ :=
      ENNReal.ne_top_of_tsum_ne_top (hWseries_ne S) m
    have hterm_ne (m : ℕ) (w : CollisionWord n (m + 1)) :
        (if wordSupport w.1 ⊆ S then
          diagramKernel θ (List.ofFn w.1) t xy.1 xy.2 else 0) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (hW_ne m)
      change (if wordSupport w.1 ⊆ S then
          diagramKernel θ (List.ofFn w.1) t xy.1 xy.2 else 0) ≤
        ∑ v : CollisionWord n (m + 1),
          if wordSupport v.1 ⊆ S then
            diagramKernel θ (List.ofFn v.1) t xy.1 xy.2 else 0
      exact Finset.single_le_sum
        (f := fun v : CollisionWord n (m + 1) =>
          if wordSupport v.1 ⊆ S then
            diagramKernel θ (List.ofFn v.1) t xy.1 xy.2 else 0)
        (by intro v hv; split_ifs <;> positivity) (Finset.mem_univ w)
    have hreal : (fun m : ℕ => (W S m).toReal) = R S := by
      funext m
      change (∑ w : CollisionWord n (m + 1),
          if wordSupport w.1 ⊆ S then
            diagramKernel θ (List.ofFn w.1) t xy.1 xy.2 else 0).toReal = _
      rw [ENNReal.toReal_sum (fun w hw => hterm_ne m w)]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : wordSupport w.1 ⊆ S <;> simp [h]
    rw [← hreal]
    exact ENNReal.summable_toReal (hWseries_ne S)
  have hsign :
      (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card)) = 0 := by
    have hsum :
        (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card)) =
          ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            if (∅ : Finset (Fin n)) ⊆ S then (-1 : ℝ) ^ (n - S.card) else 0 := by
      apply Finset.sum_bij (fun S _ => S)
      · intro S hS
        exact Finset.mem_powerset.mpr (Finset.subset_univ _)
      · intro S hS T hT hST
        exact hST
      · intro T hT
        exact ⟨T, Finset.mem_univ T, rfl⟩
      · intro S hS
        simp
    have hcancel := alternating_sum_supersets_eq_univ (∅ : Finset (Fin n))
    rw [← hsum] at hcancel
    have hempty : (∅ : Finset (Fin n)) ≠ Finset.univ := by
      intro h
      have hc := congrArg Finset.card h
      simp at hc
      omega
    simpa [hempty] using hcancel
  have hswap :
      (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) * ∑' m : ℕ, R S m) =
        ∑' m : ℕ, ∑ S : Finset (Fin n),
          (-1 : ℝ) ^ (n - S.card) * R S m := by
    calc
      _ = ∑ S : Finset (Fin n), ∑' m : ℕ,
            (-1 : ℝ) ^ (n - S.card) * R S m := by
              apply Finset.sum_congr rfl
              intro S hS
              rw [← tsum_mul_left]
      _ = _ := (Summable.tsum_finsetSum
        (s := Finset.univ)
        (fun S hS => Summable.mul_left _ (hR_summable S))).symm
  have hlength (m : ℕ) :
      (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) * R S m) =
        ∑ w : CollisionWord n (m + 1),
          if wordSupport w.1 = Finset.univ then
            (diagramKernel θ (List.ofFn w.1) t xy.1 xy.2).toReal else 0 := by
    simpa [R] using alternating_sum_word_support_filter
      (fun w : CollisionWord n (m + 1) =>
        (diagramKernel θ (List.ofFn w.1) t xy.1 xy.2).toReal)
  have hseries :
      (∑' m : ℕ, ∑ S : Finset (Fin n),
        (-1 : ℝ) ^ (n - S.card) * R S m) =
        ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
          if wordSupport w.1 = Finset.univ then
            (diagramKernel θ (List.ofFn w.1) t xy.1 xy.2).toReal else 0 := by
    apply tsum_congr
    intro m
    exact hlength m
  have hcentered :
      centeredMomentKernel n θ t xy.1 xy.2 =
        ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
          if wordSupport w.1 = Finset.univ then
            (diagramKernel θ (List.ofFn w.1) t xy.1 xy.2).toReal else 0 := by
    rw [centeredMomentKernel_eq_sum_mixedBlockKernel n θ ht.le]
    have hblocks :
        (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
          (mixedBlockKernel n θ t S xy.1 xy.2).toReal) =
        (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
          (freeKernel n t xy.1 xy.2 + ∑' m : ℕ, R S m)) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [mixedBlockKernel_toReal_eq_supportedDiagramSeries S θ ht
        xy.1 xy.2 hfull]
    calc
      _ = ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
          (freeKernel n t xy.1 xy.2 + ∑' m : ℕ, R S m) := hblocks
      _ = (freeKernel n t xy.1 xy.2 *
            ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card)) +
          ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) * ∑' m : ℕ, R S m := by
            calc
              _ = ∑ S : Finset (Fin n),
                    ((-1 : ℝ) ^ (n - S.card) * freeKernel n t xy.1 xy.2 +
                      (-1 : ℝ) ^ (n - S.card) * ∑' m : ℕ, R S m) := by
                  apply Finset.sum_congr rfl
                  intro S hS
                  rw [mul_add]
              _ = (∑ S : Finset (Fin n),
                    (-1 : ℝ) ^ (n - S.card) * freeKernel n t xy.1 xy.2) +
                  ∑ S : Finset (Fin n),
                    (-1 : ℝ) ^ (n - S.card) * ∑' m : ℕ, R S m :=
                    Finset.sum_add_distrib
              _ = _ := by
                  congr 1
                  calc
                    _ = (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card)) *
                        freeKernel n t xy.1 xy.2 := by
                          rw [Finset.sum_mul]
                    _ = _ := by ring
      _ = ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) * ∑' m : ℕ, R S m := by
            rw [hsign, mul_zero, zero_add]
      _ = _ := by rw [hswap, hseries]
  have hcover_ne : coveringKernel n θ t xy.1 xy.2 ≠ ⊤ :=
    ne_top_of_le_ne_top hfull (coveringKernel_le_momentKernel θ t xy.1 xy.2)
  exact ⟨hcover_ne, hcentered.trans
    (coveringKernel_toReal_eq_wordSeries θ t xy.1 xy.2 hcover_ne).symm⟩

end Critical2DKPZ.SHF.Tsai

end
