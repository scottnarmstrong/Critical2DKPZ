/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansionRuns
import Critical2DKPZ.SHF.Flow.SlabProductsCore
import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
import Mathlib.Tactic

/-! # Endpoint support for finite word and run sums -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose
attribute [local instance] Classical.propDecidable

/-- The configurations whose `i`-th site is an `n`-step endpoint of `x i`, for every `i`. -/
def configurationEndpointSet {h : ℕ} (n : ℕ) (x : Fin h → Site) :
    Finset (Fin h → Site) :=
  Fintype.piFinset fun i => Polymer.endpoints (x i) n

/-- The collision-subset coefficient vanishes if some `x i` is not an `n`-step endpoint of `y i`. -/
theorem collisionSubsetCoefficient_zero_of_start_endpoint_not_mem {n h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) (x y : Fin h → Site) (i : Fin h)
    (hi : x i ∉ Polymer.endpoints (y i) n) :
    collisionSubsetCoefficient n h A x y = 0 := by
  classical
  rw [collisionSubsetCoefficient]
  apply Finset.sum_eq_zero
  intro p hp
  have hnot : walkPosition (x i) (p i) n ≠ y i := by
    intro heq
    apply hi
    have hyReach : y i ∈ Polymer.endpoints (x i) n :=
      (Polymer.mem_endpoints_iff (x i) (y i) n).2 ⟨p i, heq⟩
    exact Critical2DKPZ.SHF.Flow.mem_endpoints_reverse hyReach
  have hzero : (∏ j, if walkPosition (x j) (p j) n = y j then (1 : ℝ) else 0) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hnot])
  simp [hzero]

/-- The union, over `x ∈ R`, of the `n`-step endpoint sets of configurations from `x`. -/
def configEndpointBiUnion {h : ℕ} (R : Finset (Fin h → Site)) (n : ℕ) :
    Finset (Fin h → Site) :=
  R.biUnion fun x => configurationEndpointSet n x

/-- The product of free kernels vanishes unless `u` lies in `configurationEndpointSet n x`. -/
theorem freeKernelProduct_zero_of_not_mem {h : ℕ} (n : ℕ)
    (x u : Fin h → Site) (hu : u ∉ configurationEndpointSet n x) :
    (∏ i, srwKernel n (u i - x i)) = 0 := by
  classical
  have hmiss : ∃ i, u i ∉ Polymer.endpoints (x i) n := by
    by_contra hn
    apply hu
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmiss
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (Polymer.srwKernel_eq_zero_of_not_mem n (x i) (u i) hi)

/-- For `u ∈ R` and `v` outside `configEndpointBiUnion R r`, the coefficient vanishes. -/
theorem runCoefficient_zero_of_endpoint_biUnion_not_mem {h : ℕ}
    {R : Finset (Fin h → Site)} {r : ℕ} {A : Finset (ℕ × CollisionPair h)}
    {u v : Fin h → Site} (hu : u ∈ R)
    (hv : v ∉ configEndpointBiUnion R r) :
    collisionSubsetCoefficient r h A u v = 0 := by
  classical
  have hv' : v ∉ configurationEndpointSet r u := by
    intro hvR
    exact hv (Finset.mem_biUnion.mpr ⟨u, hu, hvR⟩)
  have hmiss : ∃ i, v i ∉ Polymer.endpoints (u i) r := by
    by_contra hn
    apply hv'
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmiss
  exact collisionSubsetCoefficient_zero_of_endpoint_not_mem A u v i hi

/-- The collision-subset coefficient vanishes unless `x ∈ configurationEndpointSet n y`. -/
theorem collisionSubsetCoefficient_zero_of_startSet_not_mem {n h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) (x y : Fin h → Site)
    (hx : x ∉ configurationEndpointSet n y) :
    collisionSubsetCoefficient n h A x y = 0 := by
  classical
  have hmiss : ∃ i, x i ∉ Polymer.endpoints (y i) n := by
    by_contra hn
    apply hx
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmiss
  exact collisionSubsetCoefficient_zero_of_start_endpoint_not_mem A x y i hi

/-- Exchange two `tsum`s with a finite sum when `f a` vanishes off `Rβ` in `b` and off `Rγ` in
`c` for every `a ∈ s`. -/
theorem sum_tsum_tsum_eq_tsum_tsum_sum_of_support
    {α β γ : Type*} [Countable β] [Countable γ]
    (s : Finset α) (Rβ : Finset β) (Rγ : Finset γ)
    (f : α → β → γ → ℝ)
    (hβ : ∀ a ∈ s, ∀ b ∉ Rβ, ∀ c, f a b c = 0)
    (hγ : ∀ a ∈ s, ∀ b, ∀ c ∉ Rγ, f a b c = 0) :
    (∑ a ∈ s, ∑' b, ∑' c, f a b c) =
      ∑' b, ∑' c, ∑ a ∈ s, f a b c := by
  classical
  calc
    _ = ∑' b, ∑ a ∈ s, ∑' c, f a b c := by
      exact sum_tsum_eq_tsum_sum_of_support s Rβ
        (fun a b => ∑' c, f a b c)
        (by
          intro a ha b hb
          have hf : (fun c => f a b c) = fun _ => (0 : ℝ) := by
            funext c
            exact hβ a ha b hb c
          rw [hf]
          simp)
    _ = ∑' b, ∑' c, ∑ a ∈ s, f a b c := by
      apply tsum_congr
      intro b
      exact sum_tsum_eq_tsum_sum_of_support s Rγ
        (fun a c => f a b c) (by
          intro a ha c hc
          exact hγ a ha b c hc)

/-- An `r`-step endpoint of an `m`-step endpoint of `u` is an `(m + r)`-step endpoint of `u`. -/
theorem endpoints_compose_collisionRun {u z x : Site} {m r : ℕ}
    (hz : z ∈ Polymer.endpoints u m) (hx : x ∈ Polymer.endpoints z r) :
    x ∈ Polymer.endpoints u (m + r) := by
  obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff u z m).mp hz
  obtain ⟨q, hq⟩ := (Polymer.mem_endpoints_iff z x r).mp hx
  apply (Polymer.mem_endpoints_iff u x (m + r)).mpr
  refine ⟨Fin.append p q, ?_⟩
  rw [Polymer.walkPosition_append_end, hp]
  exact hq

/-- A nonzero spatial renewal weight `r` steps from `u` to `v` forces `v ∈ endpoints u r`. -/
theorem spatialRenewal_nonzero_endpoint {σ2 : ℝ} {r : ℕ} {u v : Site}
    (hR : Collision.spatialRenewal σ2 r (v - u) ≠ 0) :
    v ∈ Polymer.endpoints u r := by
  by_contra hv
  have hzero : v - u ∉ Polymer.endpoints 0 r := by
    intro hz
    obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff 0 (v - u) r).mp hz
    apply hv
    apply (Polymer.mem_endpoints_iff u v r).mpr
    refine ⟨p, ?_⟩
    rw [Polymer.walkPosition_eq_start_add, hp]
    abel
  rw [spatialRenewal_eq_zero_of_not_mem_endpoints σ2 r (v - u) hzero] at hR
  exact hR rfl

/-- A block word kernel vanishes unless `x ∈ configurationEndpointSet n y`. -/
theorem blockWordKernel_zero_of_start_endpoint_not_mem {h : ℕ} (σ2 : ℝ) :
    ∀ (w : List (CollisionPair h)) (n : ℕ) (x y : Fin h → Site),
      x ∉ configurationEndpointSet n y → blockWordKernel σ2 w n x y = 0 := by
  intro w
  induction w with
  | nil =>
      intro n x y hx
      have hmiss : ∃ i, x i ∉ Polymer.endpoints (y i) n := by
        by_contra hn
        apply hx
        apply Fintype.mem_piFinset.mpr
        intro i
        by_contra hi
        exact hn ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hmiss
      have hyx : y i ∉ Polymer.endpoints (x i) n := by
        intro hmem
        exact hi (Critical2DKPZ.SHF.Flow.mem_endpoints_reverse hmem)
      have hkernel : srwKernel n (y i - x i) = 0 :=
        Polymer.srwKernel_eq_zero_of_not_mem n (x i) (y i) hyx
      change (∏ j, srwKernel n (y j - x j)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) hkernel
  | cons α w ih =>
      intro n x y hx
      classical
      simp only [blockWordKernel]
      apply Finset.sum_eq_zero
      intro s hs
      apply Finset.sum_eq_zero
      intro r hr
      let m := n - s - r
      have hsIcc := Finset.mem_Icc.mp hs
      have hrRange := Finset.mem_range.mp hr
      have hduration : s + r + m = n := by
        dsimp [m]
        omega
      have hterm_zero (u v : Fin h → Site) :
          (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * σ2 *
            Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
            (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
              srwKernel r (v i - u i)) * blockWordKernel σ2 w m v y = 0 := by
        by_contra hne
        have hpair : u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 := by
          by_contra hp
          simp [hp] at hne
        have hfree : (∏ i, srwKernel s (u i - x i)) ≠ 0 := by
          intro hz
          simp [hz] at hne
        have hrenew : Collision.spatialRenewal σ2 r
            (v α.1.1 - u α.1.1) ≠ 0 := by
          intro hz
          simp [hz] at hne
        have hspectator : (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
            srwKernel r (v i - u i)) ≠ 0 := by
          intro hz
          simp [hz] at hne
        have htail : blockWordKernel σ2 w m v y ≠ 0 := by
          intro hz
          simp [hz] at hne
        have huReach : u ∈ configurationEndpointSet s x := by
          apply Fintype.mem_piFinset.mpr
          intro i
          by_contra hi
          have hkernel : srwKernel s (u i - x i) = 0 :=
            Polymer.srwKernel_eq_zero_of_not_mem s (x i) (u i) hi
          have hzero : (∏ j, srwKernel s (u j - x j)) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) hkernel
          exact hfree hzero
        have hvRun : v ∈ configurationEndpointSet r u := by
          apply Fintype.mem_piFinset.mpr
          intro i
          by_cases hia : i = α.1.1
          · subst i
            exact spatialRenewal_nonzero_endpoint hrenew
          · by_cases hib : i = α.1.2
            · subst i
              simpa [hpair.1, hpair.2] using
                (spatialRenewal_nonzero_endpoint hrenew)
            · have hfactor : (if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                  srwKernel r (v i - u i)) ≠ 0 := by
                intro hz
                exact hspectator (Finset.prod_eq_zero (Finset.mem_univ i) hz)
              have hkernel : srwKernel r (v i - u i) ≠ 0 := by
                simpa [hia, hib] using hfactor
              by_contra hi
              exact hkernel (Polymer.srwKernel_eq_zero_of_not_mem r (u i) (v i) hi)
        have hvTail : v ∈ configurationEndpointSet m y := by
          by_contra hv
          exact htail (ih m v y hv)
        have hxReach : x ∈ configurationEndpointSet n y := by
          apply Fintype.mem_piFinset.mpr
          intro i
          have htailCoord := Fintype.mem_piFinset.mp hvTail i
          have hrunCoord := Fintype.mem_piFinset.mp hvRun i
          have hfreeCoord := Fintype.mem_piFinset.mp huReach i
          have hbackRun := Critical2DKPZ.SHF.Flow.mem_endpoints_reverse hrunCoord
          have hbackFree := Critical2DKPZ.SHF.Flow.mem_endpoints_reverse hfreeCoord
          have hfirst := endpoints_compose_collisionRun htailCoord hbackRun
          have hsecond := endpoints_compose_collisionRun hfirst hbackFree
          have hduration' : m + r + s = n := by omega
          simpa [hduration'] using hsecond
        exact hx hxReach
      have hsumV (u₀ : Fin h → Site) :
          (∑' v₀ : Fin h → Site,
            (if u₀ α.1.1 = u₀ α.1.2 ∧ v₀ α.1.1 = v₀ α.1.2 then (1 : ℝ) else 0) *
              (∏ i, srwKernel s (u₀ i - x i)) * σ2 *
              Collision.spatialRenewal σ2 r (v₀ α.1.1 - u₀ α.1.1) *
              (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                srwKernel r (v₀ i - u₀ i)) * blockWordKernel σ2 w m v₀ y) = 0 := by
        have hfun : (fun v₀ : Fin h → Site =>
            (if u₀ α.1.1 = u₀ α.1.2 ∧ v₀ α.1.1 = v₀ α.1.2 then (1 : ℝ) else 0) *
              (∏ i, srwKernel s (u₀ i - x i)) * σ2 *
              Collision.spatialRenewal σ2 r (v₀ α.1.1 - u₀ α.1.1) *
              (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                srwKernel r (v₀ i - u₀ i)) * blockWordKernel σ2 w m v₀ y) =
            fun _ => (0 : ℝ) := by
          funext v₀
          exact hterm_zero u₀ v₀
        rw [hfun]
        simp
      have hfun : (fun u₀ : Fin h → Site =>
          ∑' v₀ : Fin h → Site,
            (if u₀ α.1.1 = u₀ α.1.2 ∧ v₀ α.1.1 = v₀ α.1.2 then (1 : ℝ) else 0) *
              (∏ i, srwKernel s (u₀ i - x i)) * σ2 *
              Collision.spatialRenewal σ2 r (v₀ α.1.1 - u₀ α.1.1) *
              (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
                srwKernel r (v₀ i - u₀ i)) * blockWordKernel σ2 w m v₀ y) =
            fun _ => (0 : ℝ) := by
        funext u₀
        exact hsumV u₀
      rw [hfun]
      simp

/-- The word sum is the finite sum over word lengths `m ≤ n`. -/
theorem wordSumFrom_eq_sum_range {h : ℕ} (σ2 : ℝ)
    (L : Finset (CollisionPair h)) (n : ℕ) (x y : Fin h → Site) :
    wordSumFrom σ2 L n x y =
      ∑ m ∈ Finset.range (n + 1), ∑ w : CollisionWord h m,
        if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ∈ L then
          blockWordKernel σ2 (List.ofFn w.1) n x y else 0 := by
  classical
  unfold wordSumFrom
  rw [tsum_eq_sum (s := Finset.range (n + 1))]
  intro m hm
  have hmn : n < m := by
    simp only [Finset.mem_range, not_lt] at hm
    omega
  apply Finset.sum_eq_zero
  intro w hw
  split_ifs with hfirst
  · apply blockWordKernel_eq_zero_of_length_gt
    simpa using hmn
  · rfl

/-- For `k < n`, words of length `< n` whose first letter is not `α` sum to `wordSumFrom`
with `L = univ.erase α` and time `k`. -/
theorem filteredTailWordSum_eq_wordSumFrom {h : ℕ} (σ2 : ℝ)
    (α : CollisionPair h) {k n : ℕ} (hkn : k < n) (x y : Fin h → Site) :
    (∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
      if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
        blockWordKernel σ2 (List.ofFn w.1) k x y else 0) =
      wordSumFrom σ2 (Finset.univ.erase α) k x y := by
  classical
  have hsmall :
      wordSumFrom σ2 (Finset.univ.erase α) k x y =
        ∑ m ∈ Finset.range (k + 1), ∑ w : CollisionWord h m,
          if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
            blockWordKernel σ2 (List.ofFn w.1) k x y else 0 := by
    rw [wordSumFrom_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro w hw
    congr 1
    simp [Finset.mem_erase]
  have hlarge :
      (∑ m ∈ Finset.range n, ∑ w : CollisionWord h m,
        if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
          blockWordKernel σ2 (List.ofFn w.1) k x y else 0) =
      ∑ m ∈ Finset.range (k + 1), ∑ w : CollisionWord h m,
        if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
          blockWordKernel σ2 (List.ofFn w.1) k x y else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m hm hnot
    have hkm : k < m := by
      simp only [Finset.mem_range, not_lt] at hnot
      omega
    apply Finset.sum_eq_zero
    intro w hw
    split_ifs with hfirst
    · apply blockWordKernel_eq_zero_of_length_gt
      simpa using hkm
    · rfl
  exact hlarge.trans hsmall.symm

/-- The word sum is the empty-word term plus the sums over words `α :: w` with `α ∈ L`, `w`
of length `< n` not starting with `α`. -/
theorem wordSumFrom_length_decomp {h : ℕ} (σ2 : ℝ)
    (L : Finset (CollisionPair h)) (n : ℕ) (x y : Fin h → Site) :
    wordSumFrom σ2 L n x y =
      (∏ i, srwKernel n (y i - x i)) +
        ∑ m ∈ Finset.range n, ∑ α ∈ L,
          ∑ w : CollisionWord h m,
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              blockWordKernel σ2 (α :: List.ofFn w.1) n x y else 0 := by
  classical
  rw [wordSumFrom_eq_sum_range, Finset.sum_range_succ']
  let w0 : CollisionWord h 0 := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  have huniv : (Finset.univ : Finset (CollisionWord h 0)) = {w0} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_singleton]
    constructor
    · intro _
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    · intro _
      trivial
  have hbase :
      (∑ w : CollisionWord h 0,
        if ∀ hm : 0 < 0, w.1 ⟨0, hm⟩ ∈ L then
          blockWordKernel σ2 (List.ofFn w.1) n x y else 0) =
        ∏ i, srwKernel n (y i - x i) := by
    rw [huniv, Finset.sum_singleton]
    simp [w0, blockWordKernel]
  have hsucc :
      (∑ m ∈ Finset.range n, ∑ w : CollisionWord h (m + 1),
        if ∀ hm : 0 < m + 1, w.1 ⟨0, hm⟩ ∈ L then
          blockWordKernel σ2 (List.ofFn w.1) n x y else 0) =
      ∑ m ∈ Finset.range n, ∑ α ∈ L,
        ∑ w : CollisionWord h m,
          if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
            blockWordKernel σ2 (α :: List.ofFn w.1) n x y else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    have hcond (w : CollisionWord h (m + 1)) :
        (∀ hm' : 0 < m + 1, w.1 ⟨0, hm'⟩ ∈ L) ↔ w.1 0 ∈ L := by
      constructor
      · intro hw
        exact hw (by omega)
      · intro hw hm'
        exact hw
    simp_rw [hcond]
    rw [sum_collisionWord_succ_firstIn L m
      (fun word => blockWordKernel σ2 word n x y)]
  calc
    _ = (∏ i, srwKernel n (y i - x i)) +
        (∑ m ∈ Finset.range n, ∑ w : CollisionWord h (m + 1),
          if ∀ hm : 0 < m + 1, w.1 ⟨0, hm⟩ ∈ L then
            blockWordKernel σ2 (List.ofFn w.1) n x y else 0) := by
      rw [hbase]
      ring
    _ = _ := congrArg (fun z : ℝ => (∏ i, srwKernel n (y i - x i)) + z) hsucc

/-- The weighted coefficient of a first `α`-run followed by `A'` as a double `tsum` over
intermediate configurations `u`, `v`. -/
theorem weighted_firstRun_coefficient_eq {h : ℕ} (σ2 : ℝ)
    (α : CollisionPair h) {s r m : ℕ} (hs : 1 ≤ s)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 r)
    {A' : Finset (ℕ × CollisionPair h)} (hA' : A' ⊆ collisionEdges m h)
    (x y : Fin h → Site) :
    σ2 ^ (runEdges α s S ∪ shiftEdges (s + r) A').card *
        collisionSubsetCoefficient (s + r + m) h
          (runEdges α s S ∪ shiftEdges (s + r) A') x y =
      ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) *
          (σ2 * σ2 ^ S.card) * σ2 ^ A'.card *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
          collisionSubsetCoefficient m h A' v y := by
  rw [card_runEdges_union_shiftEdges α hs hS hA']
  rw [show S.card + A'.card + 1 = (S.card + A'.card) + 1 by omega,
    pow_add, pow_add]
  rw [collisionSubsetCoefficient_runEdges_union α hs hS hA' x y]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro u
  rw [← tsum_mul_left]
  apply tsum_congr
  intro v
  ring


end Critical2DKPZ.SHF.Moments

end
