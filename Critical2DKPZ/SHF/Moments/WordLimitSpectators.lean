/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansionStageProps
public import Critical2DKPZ.SHF.Moments.SinglePairWord
public import Critical2DKPZ.SHF.Moments.WordDominationFreeTail
public import Critical2DKPZ.SHF.Tsai.DiagramSpectatorFactorization
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Pi

/-! Empty and one-collision word limits factor through the free spectator coordinates. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose
open scoped BigOperators CompactlySupported Topology

namespace Critical2DKPZ.SHF.Moments

/-- The two colliding labels of a pair, as a two-replica family. -/
def pairRestrict {h : ℕ} {X : Type*} (α : CollisionPair h) (x : Fin h → X) : Fin 2 → X :=
  ![x α.1.1, x α.1.2]

private def wordLimitSpectatorRestrict {h : ℕ} {X : Type*} (α : CollisionPair h)
    (x : Fin h → X) : Spectator α → X := fun i => x i.1

private def wordLimitPairIndexSet {h : ℕ} (α : CollisionPair h) : Finset (Fin h) :=
  {α.1.1, α.1.2}

private def wordLimitSpectatorComplementEquiv {h : ℕ} (α : CollisionPair h) :
    Spectator α ≃ {i : Fin h // i ∈ (wordLimitPairIndexSet α)ᶜ} where
  toFun i := ⟨i.1, by simpa [wordLimitPairIndexSet] using i.2⟩
  invFun i := ⟨i.1, by simpa [wordLimitPairIndexSet] using i.2⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

private def wordLimitPairSpectatorEquiv {h : ℕ} (α : CollisionPair h) :
    (Fin h → Site) ≃ (Fin 2 → Site) × (Spectator α → Site) where
  toFun x := (pairRestrict α x, wordLimitSpectatorRestrict α x)
  invFun p i :=
    if hi : i = α.1.1 then p.1 0
    else if hj : i = α.1.2 then p.1 1
    else p.2 ⟨i, fun heq => hi heq, fun heq => hj heq⟩
  left_inv x := by
    funext i
    by_cases hi : i = α.1.1
    · simp [pairRestrict, hi]
    · by_cases hj : i = α.1.2
      · simp [pairRestrict, hj, ne_of_gt α.2]
      · simp [wordLimitSpectatorRestrict, hi, hj]
  right_inv p := by
    rcases p with ⟨q, z⟩
    apply Prod.ext
    · change pairRestrict α (fun i =>
        if hi : i = α.1.1 then q 0
        else if hj : i = α.1.2 then q 1
        else z ⟨i, fun heq => hi heq, fun heq => hj heq⟩) = q
      funext i
      fin_cases i
      · simp [pairRestrict]
      · simp [pairRestrict, ne_of_gt α.2]
    · change wordLimitSpectatorRestrict α (fun i =>
        if hi : i = α.1.1 then q 0
        else if hj : i = α.1.2 then q 1
        else z ⟨i, fun heq => hi heq, fun heq => hj heq⟩) = z
      funext i
      simp [wordLimitSpectatorRestrict, i.2.1, i.2.2]

@[simp] private theorem wordLimitPairSpectatorEquiv_apply {h : ℕ} (α : CollisionPair h)
    (x : Fin h → Site) :
    wordLimitPairSpectatorEquiv α x = (pairRestrict α x, wordLimitSpectatorRestrict α x) := rfl

/-- A finite configuration sum splits into the colliding pair and its independent spectators. -/
theorem wordLimit_sum_pair_spectator_coordinates {h : ℕ} (α : CollisionPair h)
    (D : Fin h → Finset Site) (F : (Fin 2 → Site) → ℝ)
    (G : Spectator α → Site → ℝ) :
    (∑ x ∈ Fintype.piFinset D,
      F (pairRestrict α x) * ∏ i : Spectator α, G i (x i.1)) =
      (∑ p ∈ Fintype.piFinset (fun j : Fin 2 => D (if j = 0 then α.1.1 else α.1.2)), F p) *
        ∏ i : Spectator α, ∑ a ∈ D i.1, G i a := by
  classical
  let Dp : Fin 2 → Finset Site := fun j => D (if j = 0 then α.1.1 else α.1.2)
  let Ds : Spectator α → Finset Site := fun i => D i.1
  let P := Fintype.piFinset Dp
  let Z := Fintype.piFinset Ds
  have hmem (x : Fin h → Site) :
      x ∈ Fintype.piFinset D ↔ wordLimitPairSpectatorEquiv α x ∈ P ×ˢ Z := by
    simp only [Fintype.mem_piFinset, Finset.mem_product, P, Z, Dp, Ds,
      wordLimitPairSpectatorEquiv_apply, pairRestrict, wordLimitSpectatorRestrict]
    constructor
    · intro hx
      constructor
      · intro j
        fin_cases j
        · exact hx α.1.1
        · exact hx α.1.2
      · intro i
        exact hx i.1
    · rintro ⟨hp, hz⟩ i
      by_cases hi₁ : i = α.1.1
      · subst i
        simpa [Dp] using hp 0
      · by_cases hi₂ : i = α.1.2
        · subst i
          simpa [Dp, ne_of_gt α.2] using hp 1
        · simpa [Ds] using hz ⟨i, hi₁, hi₂⟩
  let f : (Fin h → Site) → ℝ := fun x =>
    F (pairRestrict α x) * ∏ i : Spectator α, G i (x i.1)
  let g : ((Fin 2 → Site) × (Spectator α → Site)) → ℝ := fun q =>
    F q.1 * ∏ i : Spectator α, G i (q.2 i)
  have hsum :
      (∑ x ∈ Fintype.piFinset D, f x) =
        ∑ q ∈ P ×ˢ Z, g q := by
    apply Finset.sum_bij (fun x _ => wordLimitPairSpectatorEquiv α x)
    · intro x hx
      exact (hmem x).mp hx
    · intro x hx y hy hxy
      exact (wordLimitPairSpectatorEquiv α).injective hxy
    · intro q hq
      have hq' : wordLimitPairSpectatorEquiv α
          ((wordLimitPairSpectatorEquiv α).symm q) ∈ P ×ˢ Z := by
        simpa only [(wordLimitPairSpectatorEquiv α).apply_symm_apply] using hq
      exact ⟨(wordLimitPairSpectatorEquiv α).symm q, (hmem _).mpr hq',
        (wordLimitPairSpectatorEquiv α).apply_symm_apply q⟩
    · intro x hx
      simp [f, g, wordLimitPairSpectatorEquiv_apply, wordLimitSpectatorRestrict]
  calc
    _ = ∑ p ∈ P, ∑ z ∈ Z, g (p, z) := by
      simpa only [f, P, Z, Finset.sum_product] using hsum
    _ = _ := by
      have hZ :
          (∑ z ∈ Z, ∏ i : Spectator α, G i (z i)) =
            ∏ i : Spectator α, ∑ a ∈ Ds i, G i a := by
        simpa only [Z] using
          Critical2DKPZ.MomentBounds.finite_sum_product_over_piFinset_eq_product_sums
            Ds (fun i z => G i z)
      calc
        _ = ∑ p ∈ P, F p * (∑ z ∈ Z, ∏ i : Spectator α, G i (z i)) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [g]
          rw [Finset.mul_sum]
        _ = ∑ p ∈ P, F p * ∏ i : Spectator α, ∑ a ∈ Ds i, G i a := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hZ]
        _ = _ := by
          rw [Finset.sum_mul]

private theorem wordLimit_sum_pair_spectator_double {h : ℕ} (α : CollisionPair h)
    (D E : Fin h → Finset Site) (F : (Fin 2 → Site) → (Fin 2 → Site) → ℝ)
    (G : Spectator α → Site → Site → ℝ) :
    (∑ x ∈ Fintype.piFinset D, ∑ y ∈ Fintype.piFinset E,
      F (pairRestrict α x) (pairRestrict α y) *
        ∏ i : Spectator α, G i (x i.1) (y i.1)) =
      (∑ p ∈ Fintype.piFinset (fun j : Fin 2 => D (if j = 0 then α.1.1 else α.1.2)),
        ∑ q ∈ Fintype.piFinset (fun j : Fin 2 => E (if j = 0 then α.1.1 else α.1.2)),
          F p q) *
        ∏ i : Spectator α, ∑ a ∈ D i.1, ∑ b ∈ E i.1, G i a b := by
  classical
  let DU : Spectator α → Finset Site := fun i => D i.1
  let DV : Spectator α → Finset Site := fun i => E i.1
  let PU := Fintype.piFinset (fun j : Fin 2 => D (if j = 0 then α.1.1 else α.1.2))
  let PV := Fintype.piFinset (fun j : Fin 2 => E (if j = 0 then α.1.1 else α.1.2))
  calc
    _ = ∑ y ∈ Fintype.piFinset E, ∑ x ∈ Fintype.piFinset D,
          F (pairRestrict α x) (pairRestrict α y) *
            ∏ i : Spectator α, G i (x i.1) (y i.1) := by
      rw [Finset.sum_comm]
    _ = ∑ y ∈ Fintype.piFinset E,
          (∑ p ∈ PU, F p (pairRestrict α y)) *
            ∏ i : Spectator α, ∑ a ∈ DU i, G i a (y i.1) := by
      apply Finset.sum_congr rfl
      intro y hy
      simpa [DU, PU] using
        (wordLimit_sum_pair_spectator_coordinates α D
          (fun p => F p (pairRestrict α y)) (fun i a => G i a (y i.1)))
    _ = (∑ q ∈ PV, ∑ p ∈ PU, F p q) *
          ∏ i : Spectator α, ∑ b ∈ DV i, ∑ a ∈ DU i, G i a b := by
      simpa [DV, DU, PV, PU] using
        (wordLimit_sum_pair_spectator_coordinates α E
          (fun q => ∑ p ∈ PU, F p q)
          (fun i b => ∑ a ∈ DU i, G i a b))
    _ = _ := by
      have hpairs :
          (∑ q ∈ PV, ∑ p ∈ PU, F p q) = ∑ p ∈ PU, ∑ q ∈ PV, F p q :=
        Finset.sum_comm
      have hspectators :
          (∏ i : Spectator α, ∑ b ∈ DV i, ∑ a ∈ DU i, G i a b) =
            ∏ i : Spectator α, ∑ a ∈ DU i, ∑ b ∈ DV i, G i a b := by
        apply Finset.prod_congr rfl
        intro i hi
        exact Finset.sum_comm
      rw [hpairs, hspectators]

/-- A product over all labels splits into the colliding pair and the spectator labels. -/
theorem wordLimit_prod_pair_spectators {h : ℕ} (α : CollisionPair h)
    (f : Fin h → ℝ) :
    (∏ i : Fin h, f i) =
      (∏ j : Fin 2, f (if j = 0 then α.1.1 else α.1.2)) *
        ∏ i : Spectator α, f i.1 := by
  classical
  let S := wordLimitPairIndexSet α
  have hpair :
      (∏ i ∈ S, f i) = ∏ j : Fin 2, f (if j = 0 then α.1.1 else α.1.2) := by
    simp [S, wordLimitPairIndexSet, ne_of_lt α.2, Fin.prod_univ_two]
  have hcompl :
      (∏ i : Spectator α, f i.1) = ∏ i ∈ Sᶜ, f i := by
    calc
      _ = ∏ i : Spectator α, f (wordLimitSpectatorComplementEquiv α i).1 := by
        apply Finset.prod_congr rfl
        intro i hi
        rfl
      _ = ∏ i : {i : Fin h // i ∈ Sᶜ}, f i.1 :=
        Equiv.prod_comp (wordLimitSpectatorComplementEquiv α) (fun i => f i.1)
      _ = ∏ i ∈ Sᶜ, f i := Finset.prod_coe_sort Sᶜ (fun i => f i)
  rw [← Finset.prod_mul_prod_compl S f, hpair, hcompl]

private theorem wordLimit_srw_three_convolution (a b c : ℕ) (x y : Site) :
    (∑' u : Site, ∑' v : Site,
      srwKernel a (u - x) * srwKernel b (v - u) *
        srwKernel c (y - v)) =
      srwKernel (a + b + c) (y - x) := by
  calc
    _ = ∑' u : Site, srwKernel a (u - x) *
          (∑' v : Site, srwKernel b (v - u) * srwKernel c (y - v)) := by
      apply tsum_congr
      intro u
      rw [← tsum_mul_left]
      apply tsum_congr
      intro v
      ring
    _ = ∑' u : Site, srwKernel a (u - x) *
          srwKernel (b + c) (y - u) := by
      apply tsum_congr
      intro u
      congr 1
      exact (srwKernel_convolution b c u y).symm
    _ = srwKernel (a + (b + c)) (y - x) :=
      (srwKernel_convolution a (b + c) x y).symm
    _ = _ := by
      congr 1
      omega

private def wordLimitSingleLetterSummand {h : ℕ} (σ : ℝ) (a r k : ℕ)
    (α : CollisionPair h) (x y u v : Fin h → Site) : ℝ :=
  (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
    (∏ i, srwKernel a (u i - x i)) * σ *
      Collision.spatialRenewal σ r (v α.1.1 - u α.1.1) *
        (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else srwKernel r (v i - u i)) *
          blockWordKernel σ [] k v y

private def wordLimitPairLetterSummand (σ : ℝ) (a r k : ℕ)
    (x y u v : Fin 2 → Site) : ℝ :=
  (if u 0 = u 1 ∧ v 0 = v 1 then (1 : ℝ) else 0) *
    (∏ i, srwKernel a (u i - x i)) * σ *
      Collision.spatialRenewal σ r (v 0 - u 0) *
        (∏ i, if i = 0 ∨ i = 1 then (1 : ℝ) else srwKernel r (v i - u i)) *
          blockWordKernel σ [] k v y

private def wordLimitSpectatorLetterSummand {h : ℕ} (α : CollisionPair h)
    (a r k : ℕ) (x y : Fin h → Site)
    (i : Spectator α) (u v : Site) : ℝ :=
  srwKernel a (u - x i.1) * srwKernel r (v - u) * srwKernel k (y i.1 - v)

private theorem wordLimit_singleLetterSummand_eq_pair_spectators {h : ℕ} (σ : ℝ)
    (a r k : ℕ) (α : CollisionPair h) (x y u v : Fin h → Site) :
    wordLimitSingleLetterSummand σ a r k α x y u v =
      wordLimitPairLetterSummand σ a r k (pairRestrict α x) (pairRestrict α y)
        (pairRestrict α u) (pairRestrict α v) *
        ∏ i : Spectator α, wordLimitSpectatorLetterSummand α a r k x y i (u i.1) (v i.1) := by
  classical
  unfold wordLimitSingleLetterSummand wordLimitPairLetterSummand wordLimitSpectatorLetterSummand
    blockWordKernel
  rw [wordLimit_prod_pair_spectators α (fun i => srwKernel a (u i - x i))]
  rw [wordLimit_prod_pair_spectators α
    (fun i => if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else srwKernel r (v i - u i))]
  rw [wordLimit_prod_pair_spectators α (fun i => srwKernel k (y i - v i))]
  have hzero (z : Fin h → Site) : pairRestrict α z 0 = z α.1.1 := by
    simp [pairRestrict]
  have hone (z : Fin h → Site) : pairRestrict α z 1 = z α.1.2 := by
    simp [pairRestrict]
  have hspectMiddle :
      (∏ i : Spectator α,
        if i.1 = α.1.1 ∨ i.1 = α.1.2 then (1 : ℝ)
          else srwKernel r (v i.1 - u i.1)) =
        ∏ i : Spectator α, srwKernel r (v i.1 - u i.1) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [i.2.1, i.2.2]
  simp only [hzero, hone, Fin.prod_univ_two, Finset.prod_mul_distrib]
  rw [hspectMiddle]
  simp [ne_of_gt α.2]
  split_ifs <;> ring_nf

private theorem wordLimit_endpoint_translate (n : ℕ) (z y : Site)
    (hy : y ∈ Critical2DKPZ.Polymer.endpoints 0 n) :
    z + y ∈ Critical2DKPZ.Polymer.endpoints z n := by
  obtain ⟨s, hs⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff 0 y n).mp hy
  apply (Critical2DKPZ.Polymer.mem_endpoints_iff z (z + y) n).2
  refine ⟨s, ?_⟩
  calc
    Critical2DKPZ.walkPosition z s n = z +
        Critical2DKPZ.walkPosition 0 s n := by
      simpa using Critical2DKPZ.Polymer.walkPosition_add_start z 0 s n
    _ = z + y := by rw [hs]

private theorem wordLimit_endpoints_add {n m : ℕ} {w z x : Site}
    (hz : z ∈ Critical2DKPZ.Polymer.endpoints w n)
    (hx : x ∈ Critical2DKPZ.Polymer.endpoints z m) :
    x ∈ Critical2DKPZ.Polymer.endpoints w (n + m) := by
  obtain ⟨s, hs⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff w z n).mp hz
  obtain ⟨t, ht⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff z x m).mp hx
  apply (Critical2DKPZ.Polymer.mem_endpoints_iff w x (n + m)).2
  refine ⟨Fin.append s t, ?_⟩
  rw [Critical2DKPZ.Polymer.walkPosition_append_end, hs, ht]

private theorem wordLimit_endpoint_sub (n : ℕ) {z x : Site}
    (hx : x ∈ Critical2DKPZ.Polymer.endpoints z n) :
    x - z ∈ Critical2DKPZ.Polymer.endpoints 0 n := by
  obtain ⟨s, hs⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff z x n).mp hx
  apply (Critical2DKPZ.Polymer.mem_endpoints_iff 0 (x - z) n).2
  refine ⟨s, ?_⟩
  have hwalk : z + Critical2DKPZ.walkPosition 0 s n = x := by
    calc
      _ = Critical2DKPZ.walkPosition z s n := by
        symm
        simpa using Critical2DKPZ.Polymer.walkPosition_add_start z 0 s n
      _ = x := hs
  have hsub := congrArg (fun q : Site => q - z) hwalk
  simpa using hsub

private theorem wordLimit_spatialRenewal_supported {σ : ℝ} (r : ℕ) {z : Site}
    (hz : z ∉ Critical2DKPZ.Polymer.endpoints 0 r) :
    Collision.spatialRenewal σ r z = 0 := by
  cases r with
  | zero =>
      have hz0 : z ≠ 0 := by
        intro hz0
        apply hz
        subst z
        simp [Critical2DKPZ.Polymer.endpoints, Critical2DKPZ.walkPosition]
      simp [Collision.spatialRenewal_zero, hz0]
  | succ r =>
      rw [Collision.spatialRenewal_eq_sum_compositions σ (by omega) z]
      apply Finset.sum_eq_zero
      intro c hc
      have hnot : z ∉ Critical2DKPZ.Polymer.endpoints 0 c.blocks.sum := by
        simpa [c.blocks_sum] using hz
      rw [Collision.squareConvolution_eq_zero_of_not_mem_endpoints hnot]
      simp

private theorem wordLimit_displacement_not_endpoint {n r : ℕ} {x u v : Site}
    (hu : u ∈ Critical2DKPZ.Polymer.endpoints x n)
    (hv : v ∉ Critical2DKPZ.Polymer.endpoints x (n + r)) :
    v - u ∉ Critical2DKPZ.Polymer.endpoints 0 r := by
  intro hreach
  have htranslate := wordLimit_endpoint_translate r u (v - u) hreach
  have hadd := wordLimit_endpoints_add hu (by simpa using htranslate)
  exact hv (by simpa using hadd)

private theorem wordLimit_singleLetterSummand_zero_of_u_outside {h : ℕ} (σ : ℝ)
    (a r k : ℕ) (α : CollisionPair h) (x y u v : Fin h → Site)
    (hu : u ∉ Fintype.piFinset (fun i =>
      Critical2DKPZ.Polymer.endpoints (x i) a)) :
    wordLimitSingleLetterSummand σ a r k α x y u v = 0 := by
  classical
  have hmiss : ∃ i : Fin h, u i ∉ Critical2DKPZ.Polymer.endpoints (x i) a := by
    by_contra hn
    apply hu
    exact Fintype.mem_piFinset.mpr (by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hmiss
  have hkernel : srwKernel a (u i - x i) = 0 := by
    apply srwKernel_eq_zero_of_not_mem a (x i) (u i)
    simpa using hi
  have hprod : (∏ j : Fin h, srwKernel a (u j - x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hkernel
  simp [wordLimitSingleLetterSummand, hprod]

private theorem wordLimit_singleLetterSummand_zero_of_v_outside {h : ℕ} (σ : ℝ)
    (a r k : ℕ) (α : CollisionPair h) (x y u v : Fin h → Site)
    (hu : u ∈ Fintype.piFinset (fun i =>
      Critical2DKPZ.Polymer.endpoints (x i) a))
    (hv : v ∉ Fintype.piFinset (fun i =>
      Critical2DKPZ.Polymer.endpoints (x i) (a + r))) :
    wordLimitSingleLetterSummand σ a r k α x y u v = 0 := by
  classical
  have hmiss : ∃ i : Fin h,
      v i ∉ Critical2DKPZ.Polymer.endpoints (x i) (a + r) := by
    by_contra hn
    apply hv
    exact Fintype.mem_piFinset.mpr (by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hmiss
  by_cases hcollision : u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2
  · have hstart : u i ∈ Critical2DKPZ.Polymer.endpoints (x i) a := by
      exact (Fintype.mem_piFinset.mp hu) i
    have hdisp : v i - u i ∉ Critical2DKPZ.Polymer.endpoints 0 r := by
      apply wordLimit_displacement_not_endpoint hstart
      simpa using hi
    by_cases hi₁ : i = α.1.1
    · have hren : Collision.spatialRenewal σ r (v α.1.1 - u α.1.1) = 0 := by
        apply wordLimit_spatialRenewal_supported r
        simpa [hi₁] using hdisp
      unfold wordLimitSingleLetterSummand
      rw [ite_eq_left hcollision]
      simp [hren]
    · by_cases hi₂ : i = α.1.2
      · have hpairDisp : v α.1.1 - u α.1.1 = v i - u i := by
          subst i
          rw [hcollision.2, hcollision.1]
        have hren : Collision.spatialRenewal σ r (v α.1.1 - u α.1.1) = 0 := by
          apply wordLimit_spatialRenewal_supported r
          simpa [hpairDisp] using hdisp
        unfold wordLimitSingleLetterSummand
        rw [ite_eq_left hcollision]
        simp [hren]
      · have hkernel : srwKernel r (v i - u i) = 0 := by
          apply srwKernel_eq_zero_of_not_mem r (u i) (v i)
          intro hreach
          exact hdisp (wordLimit_endpoint_sub r hreach)
        have hprod : (∏ j : Fin h,
            if j = α.1.1 ∨ j = α.1.2 then (1 : ℝ) else srwKernel r (v j - u j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi₁, hi₂, hkernel])
        unfold wordLimitSingleLetterSummand
        rw [ite_eq_left hcollision]
        simp [hprod]
  · simp [wordLimitSingleLetterSummand, hcollision]

/-- The two-particle one-collision word has the stated tested limit. -/
def PairTwoWordLimit (ϑ : ℝ) : Prop :=
  ∀ {s t : ℝ}, 0 ≤ s → s < t → ∀ (sN tN : ℕ → ℝ), Tendsto sN atTop (𝓝 s) → Tendsto tN atTop (𝓝 t) →
    (∀ N, 0 ≤ sN N) → ∀ φ : Fin 2 → C_c(Plane × Plane, ℝ),
      Tendsto (fun N => testedBlockWord ϑ N (sN N) (tN N) φ [pairTwo]) atTop
        (𝓝 (∫ x : Configuration 2, ∫ y : Configuration 2, (∏ i, φ i (x i, y i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) [pairTwo] (t - s) x y).toReal))

private theorem wordLimit_tsum_eq_sum_piFinset_of_eq_zero {h : ℕ}
    (S : Fin h → Finset Site) (f : (Fin h → Site) → ℝ)
    (hzero : ∀ x, x ∉ Fintype.piFinset S → f x = 0) :
    ∑' x : Fin h → Site, f x = ∑ x ∈ Fintype.piFinset S, f x := by
  classical
  apply tsum_eq_sum
  intro x hx
  exact hzero x (by simpa using hx)

private theorem wordLimit_tsum_pair_rect_eq_sum {h : ℕ}
    (S T : Fin h → Finset Site) (f : (Fin h → Site) → (Fin h → Site) → ℝ)
    (hzeroS : ∀ x, x ∉ Fintype.piFinset S → ∀ y, f x y = 0)
    (hzeroT : ∀ x y, y ∉ Fintype.piFinset T → f x y = 0) :
    (∑' x : Fin h → Site, ∑' y : Fin h → Site, f x y) =
      ∑ x ∈ Fintype.piFinset S, ∑ y ∈ Fintype.piFinset T, f x y := by
  have hinner (x : Fin h → Site) :
      (∑' y : Fin h → Site, f x y) = ∑ y ∈ Fintype.piFinset T, f x y :=
    wordLimit_tsum_eq_sum_piFinset_of_eq_zero T (f x) (hzeroT x)
  rw [show (fun x : Fin h → Site => ∑' y : Fin h → Site, f x y) =
      fun x => ∑ y ∈ Fintype.piFinset T, f x y from funext hinner]
  apply tsum_eq_sum
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  exact hzeroS x (by simpa using hx) y

private theorem wordLimit_pairLetterSummand_zero_of_p_outside (σ : ℝ)
    (a r k : ℕ) (x y p q : Fin 2 → Site)
    (hp : p ∉ Fintype.piFinset (fun i =>
      Critical2DKPZ.Polymer.endpoints (x i) a)) :
    wordLimitPairLetterSummand σ a r k x y p q = 0 := by
  classical
  have hmiss : ∃ i : Fin 2, p i ∉ Critical2DKPZ.Polymer.endpoints (x i) a := by
    by_contra hn
    apply hp
    exact Fintype.mem_piFinset.mpr (by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hmiss
  have hkernel : srwKernel a (p i - x i) = 0 := by
    apply srwKernel_eq_zero_of_not_mem a (x i) (p i)
    simpa using hi
  have hprod : (∏ j : Fin 2, srwKernel a (p j - x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hkernel
  simp [wordLimitPairLetterSummand, hprod]

private theorem wordLimit_pairLetterSummand_zero_of_q_outside (σ : ℝ)
    (a r k : ℕ) (x y p q : Fin 2 → Site)
    (hp : p ∈ Fintype.piFinset (fun i =>
      Critical2DKPZ.Polymer.endpoints (x i) a))
    (hq : q ∉ Fintype.piFinset (fun i =>
      Critical2DKPZ.Polymer.endpoints (x i) (a + r))) :
    wordLimitPairLetterSummand σ a r k x y p q = 0 := by
  classical
  have hmiss : ∃ i : Fin 2,
      q i ∉ Critical2DKPZ.Polymer.endpoints (x i) (a + r) := by
    by_contra hn
    apply hq
    exact Fintype.mem_piFinset.mpr (by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hmiss
  by_cases hcollision : p 0 = p 1 ∧ q 0 = q 1
  · have hstart : p i ∈ Critical2DKPZ.Polymer.endpoints (x i) a :=
      (Fintype.mem_piFinset.mp hp) i
    have hdisp : q i - p i ∉ Critical2DKPZ.Polymer.endpoints 0 r := by
      apply wordLimit_displacement_not_endpoint hstart
      simpa using hi
    have hpairDisp : q 0 - p 0 = q i - p i := by
      by_cases hi0 : i = 0
      · subst i
        rfl
      · have hi1 : i = 1 := by
          fin_cases i
          · exact (hi0 rfl).elim
          · rfl
        subst i
        rw [hcollision.2, hcollision.1]
    have hren : Collision.spatialRenewal σ r (q 0 - p 0) = 0 := by
      apply wordLimit_spatialRenewal_supported r
      simpa [hpairDisp] using hdisp
    unfold wordLimitPairLetterSummand
    rw [ite_eq_left hcollision]
    simp [hren]
  · simp [wordLimitPairLetterSummand, hcollision]

private theorem wordLimit_spectator_finite_double_sum
    (a r k : ℕ) (x y : Site) :
    (∑ u ∈ Critical2DKPZ.Polymer.endpoints x a,
      ∑ v ∈ Critical2DKPZ.Polymer.endpoints x (a + r),
        srwKernel a (u - x) * srwKernel r (v - u) * srwKernel k (y - v)) =
      srwKernel (a + r + k) (y - x) := by
  classical
  let U := Critical2DKPZ.Polymer.endpoints x a
  let V := Critical2DKPZ.Polymer.endpoints x (a + r)
  let f : Site → Site → ℝ := fun u v =>
    srwKernel a (u - x) * srwKernel r (v - u) * srwKernel k (y - v)
  have hzeroU (u : Site) (hu : u ∉ U) : ∑' v : Site, f u v = 0 := by
    have hkernel : srwKernel a (u - x) = 0 := by
      apply srwKernel_eq_zero_of_not_mem a x u
      simpa [U] using hu
    simp [f, hkernel]
  have hzeroV (u v : Site) (hu : u ∈ U) (hv : v ∉ V) : f u v = 0 := by
    have hdisp : v - u ∉ Critical2DKPZ.Polymer.endpoints 0 r := by
      apply wordLimit_displacement_not_endpoint (by simpa [U] using hu)
      simpa [V] using hv
    have hkernel : srwKernel r (v - u) = 0 := by
      apply srwKernel_eq_zero_of_not_mem r u v
      intro hreach
      exact hdisp (wordLimit_endpoint_sub r hreach)
    simp [f, hkernel]
  have hinner (u : Site) (hu : u ∈ U) :
      (∑' v : Site, f u v) = ∑ v ∈ V, f u v := by
    apply tsum_eq_sum
    intro v hv
    by_cases hU : u ∈ U
    · exact hzeroV u v hU (by simpa [V] using hv)
    · exact (hU hu).elim
  have houter : (∑' u : Site, ∑' v : Site, f u v) =
      ∑ u ∈ U, ∑' v : Site, f u v := by
    apply tsum_eq_sum
    intro u hu
    exact hzeroU u (by simpa [U] using hu)
  calc
    _ = ∑ u ∈ U, ∑' v : Site, f u v := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (hinner u hu).symm
    _ = ∑' u : Site, ∑' v : Site, f u v := houter.symm
    _ = srwKernel (a + r + k) (y - x) := by
      simpa [f] using wordLimit_srw_three_convolution a r k x y

private theorem wordLimit_singleLetter_inner_factorization {h : ℕ} (σ : ℝ)
    (a r k : ℕ) (α : CollisionPair h) (x y : Fin h → Site) :
    (∑' u : Fin h → Site, ∑' v : Fin h → Site,
      wordLimitSingleLetterSummand σ a r k α x y u v) =
      (∑' p : Fin 2 → Site, ∑' q : Fin 2 → Site,
        wordLimitPairLetterSummand σ a r k (pairRestrict α x) (pairRestrict α y) p q) *
        ∏ i : Spectator α, srwKernel (a + r + k) (y i.1 - x i.1) := by
  classical
  let U : Fin h → Finset Site := fun i => Critical2DKPZ.Polymer.endpoints (x i) a
  let V : Fin h → Finset Site := fun i => Critical2DKPZ.Polymer.endpoints (x i) (a + r)
  let F : (Fin 2 → Site) → (Fin 2 → Site) → ℝ := fun p q =>
    wordLimitPairLetterSummand σ a r k (pairRestrict α x) (pairRestrict α y) p q
  let G : Spectator α → Site → Site → ℝ := fun i u v =>
    wordLimitSpectatorLetterSummand α a r k x y i u v
  have hzeroU : ∀ u, u ∉ Fintype.piFinset U → ∀ v,
      wordLimitSingleLetterSummand σ a r k α x y u v = 0 := by
    intro u hu v
    exact wordLimit_singleLetterSummand_zero_of_u_outside σ a r k α x y u v (by
      simpa [U] using hu)
  have hzeroV : ∀ u v, v ∉ Fintype.piFinset V →
      wordLimitSingleLetterSummand σ a r k α x y u v = 0 := by
    intro u v hv
    by_cases hu : u ∈ Fintype.piFinset U
    · exact wordLimit_singleLetterSummand_zero_of_v_outside σ a r k α x y u v
        (by simpa [U] using hu) (by simpa [V] using hv)
    · exact wordLimit_singleLetterSummand_zero_of_u_outside σ a r k α x y u v
        (by simpa [U] using hu)
  have hrect := wordLimit_tsum_pair_rect_eq_sum U V
    (wordLimitSingleLetterSummand σ a r k α x y) hzeroU hzeroV
  let UP : Fin 2 → Finset Site := fun j => U (if j = 0 then α.1.1 else α.1.2)
  let VP : Fin 2 → Finset Site := fun j => V (if j = 0 then α.1.1 else α.1.2)
  have hsplit :
      (∑ u ∈ Fintype.piFinset U, ∑ v ∈ Fintype.piFinset V,
        wordLimitSingleLetterSummand σ a r k α x y u v) =
        (∑ p ∈ Fintype.piFinset UP, ∑ q ∈ Fintype.piFinset VP, F p q) *
          ∏ i : Spectator α, ∑ b ∈ U i.1, ∑ c ∈ V i.1, G i b c := by
    calc
      _ = ∑ u ∈ Fintype.piFinset U, ∑ v ∈ Fintype.piFinset V,
          F (pairRestrict α u) (pairRestrict α v) *
            ∏ i : Spectator α, G i (u i.1) (v i.1) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact wordLimit_singleLetterSummand_eq_pair_spectators σ a r k α x y u v
      _ = _ := by
        simpa [F, G, UP, VP, U, V] using
          (wordLimit_sum_pair_spectator_double α U V F G)
  have hUP : UP = fun j =>
      Critical2DKPZ.Polymer.endpoints ((pairRestrict α x) j) a := by
    funext j
    fin_cases j <;> simp [UP, U, pairRestrict]
  have hVP : VP = fun j =>
      Critical2DKPZ.Polymer.endpoints ((pairRestrict α x) j) (a + r) := by
    funext j
    fin_cases j <;> simp [VP, V, pairRestrict]
  have hpzero (p : Fin 2 → Site) (hp : p ∉ Fintype.piFinset UP) (q : Fin 2 → Site) :
      F p q = 0 := by
    apply wordLimit_pairLetterSummand_zero_of_p_outside σ a r k
    simpa only [F, hUP] using hp
  have hqzero (p q : Fin 2 → Site) (hq : q ∉ Fintype.piFinset VP) : F p q = 0 := by
    by_cases hp : p ∈ Fintype.piFinset UP
    · apply wordLimit_pairLetterSummand_zero_of_q_outside σ a r k
      · simpa only [F, hUP] using hp
      · simpa only [hVP] using hq
    · exact hpzero p hp q
  have hpairTsum :
      (∑ p ∈ Fintype.piFinset UP, ∑ q ∈ Fintype.piFinset VP, F p q) =
        ∑' p : Fin 2 → Site, ∑' q : Fin 2 → Site, F p q := by
    symm
    exact wordLimit_tsum_pair_rect_eq_sum UP VP F hpzero hqzero
  have hspectators :
      (∏ i : Spectator α, ∑ b ∈ U i.1, ∑ c ∈ V i.1, G i b c) =
        ∏ i : Spectator α, srwKernel (a + r + k) (y i.1 - x i.1) := by
    apply Finset.prod_congr rfl
    intro i hi
    simpa [G, U, V, wordLimitSpectatorLetterSummand] using
      (wordLimit_spectator_finite_double_sum a r k (x i.1) (y i.1))
  calc
    _ = ∑ u ∈ Fintype.piFinset U, ∑ v ∈ Fintype.piFinset V,
        wordLimitSingleLetterSummand σ a r k α x y u v := hrect
    _ = _ := by rw [hsplit, hpairTsum, hspectators]

/-- One lattice collision letter is the two-replica pair word times free spectator walks. -/
theorem blockWordKernel_single_eq (σ2 : ℝ) {h : ℕ} (α : CollisionPair h) (n : ℕ)
    (x y : Fin h → Site) :
    blockWordKernel σ2 [α] n x y =
      blockWordKernel σ2 [pairTwo] n (pairRestrict α x) (pairRestrict α y) *
        ∏ i : Spectator α, srwKernel n (y i.1 - x i.1) := by
  classical
  rw [blockWordKernel_pairTwo_explicit]
  unfold blockWordKernel
  calc
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : Fin h → Site, ∑' v : Fin h → Site,
          wordLimitSingleLetterSummand σ2 s r (n - s - r) α x y u v := rfl
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        (∑' p : Fin 2 → Site, ∑' q : Fin 2 → Site,
          wordLimitPairLetterSummand σ2 s r (n - s - r)
            (pairRestrict α x) (pairRestrict α y) p q) *
          ∏ i : Spectator α, srwKernel n (y i.1 - x i.1) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      have hslo : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hsup : s ≤ n := (Finset.mem_Icc.mp hs).2
      have hrlt : r < n - s + 1 := Finset.mem_range.mp hr
      have htime : s + r + (n - s - r) = n := by omega
      simpa [htime] using
        (wordLimit_singleLetter_inner_factorization σ2 s r (n - s - r) α x y)
    _ = (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' p : Fin 2 → Site, ∑' q : Fin 2 → Site,
            wordLimitPairLetterSummand σ2 s r (n - s - r)
              (pairRestrict α x) (pairRestrict α y) p q) *
          ∏ i : Spectator α, srwKernel n (y i.1 - x i.1) := by
      calc
        _ = ∑ s ∈ Finset.Icc 1 n,
            (∑ r ∈ Finset.range (n - s + 1),
              ∑' p : Fin 2 → Site, ∑' q : Fin 2 → Site,
                wordLimitPairLetterSummand σ2 s r (n - s - r)
                  (pairRestrict α x) (pairRestrict α y) p q) *
              ∏ i : Spectator α, srwKernel n (y i.1 - x i.1) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
        _ = _ := by rw [Finset.sum_mul]
    _ = _ := by
      apply congrArg (fun z : ℝ => z * _)
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      apply tsum_congr
      intro p
      apply tsum_congr
      intro q
      rfl

private theorem testedBlockWord_nil_factorization (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    testedBlockWord ϑ N s t φ [] =
      ∏ i : Fin h, ∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
        N (φ i)).toFinset,
          cellTestWeight N (φ i) q.1 q.2 *
            srwKernel (evenCeil (N * t) - evenCeil (N * s)) (q.2 - q.1) := by
  classical
  let Q : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  let S : Fin h → Finset Site := fun i => (Q i).image Prod.fst
  let T : Fin h → Finset Site := fun i => (Q i).image Prod.snd
  let f : Fin h → Site → Site → ℝ := fun i a b =>
    cellTestWeight N (φ i) a b *
      srwKernel (evenCeil (N * t) - evenCeil (N * s)) (b - a)
  let G : (Fin h → Site) → (Fin h → Site) → ℝ := fun x y => ∏ i, f i (x i) (y i)
  have hzeroX (i : Fin h) (a : Site) (ha : a ∉ S i) (b : Site) :
      cellTestWeight N (φ i) a b = 0 := by
    have hq : (a, b) ∉ Q i := by
      intro hmem
      exact ha (Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩)
    have hint : (∫ p in cell N a ×ˢ cell N b, φ i p) = 0 := by
      by_contra hne
      exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
        N (φ i)).mem_toFinset.mpr hne)
    simp [cellTestWeight, hint]
  have hzeroY (i : Fin h) (b : Site) (hb : b ∉ T i) (a : Site) :
      cellTestWeight N (φ i) a b = 0 := by
    have hq : (a, b) ∉ Q i := by
      intro hmem
      exact hb (Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩)
    have hint : (∫ p in cell N a ×ˢ cell N b, φ i p) = 0 := by
      by_contra hne
      exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
        N (φ i)).mem_toFinset.mpr hne)
    simp [cellTestWeight, hint]
  have hzeroS : ∀ x, x ∉ Fintype.piFinset S → ∀ y, G x y = 0 := by
    intro x hx y
    have hmiss : ∃ i : Fin h, x i ∉ S i := by
      by_contra hn
      apply hx
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    have hw := hzeroX i (x i) hi (y i)
    dsimp [G, f]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hw])]
  have hzeroT : ∀ x y, y ∉ Fintype.piFinset T → G x y = 0 := by
    intro x y hy
    have hmiss : ∃ i : Fin h, y i ∉ T i := by
      by_contra hn
      apply hy
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    have hw := hzeroY i (y i) hi (x i)
    dsimp [G, f]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hw])]
  have hrect := wordLimit_tsum_pair_rect_eq_sum S T G hzeroS hzeroT
  unfold testedBlockWord
  calc
    _ = ∑' x : Fin h → Site, ∑' y : Fin h → Site, G x y := by
      apply tsum_congr
      intro x
      apply tsum_congr
      intro y
      simp [G, f, blockWordKernel, Finset.prod_mul_distrib]
    _ = ∑ x ∈ Fintype.piFinset S, ∑ y ∈ Fintype.piFinset T, G x y := hrect
    _ = ∑ x ∈ Fintype.piFinset S, ∑ y ∈ Fintype.piFinset T,
          ∏ i, f i (x i) (y i) := by
      rfl
    _ = ∏ i : Fin h, ∑ a ∈ S i, ∑ b ∈ T i, f i a b := by
      calc
        _ = ∑ x ∈ Fintype.piFinset S, ∏ i, ∑ b ∈ T i, f i (x i) b := by
          apply Finset.sum_congr rfl
          intro x hx
          exact Critical2DKPZ.MomentBounds.finite_sum_product_over_piFinset_eq_product_sums
            T (fun i b => f i (x i) b)
        _ = ∏ i : Fin h, ∑ a ∈ S i, ∑ b ∈ T i, f i a b :=
          Critical2DKPZ.MomentBounds.finite_sum_product_over_piFinset_eq_product_sums
            S (fun i a => ∑ b ∈ T i, f i a b)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      let Qᵢ := Q i
      let Sᵢ := S i
      let Tᵢ := T i
      have hsub : Qᵢ ⊆ Sᵢ ×ˢ Tᵢ := by
        intro q hq
        exact Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
      have hzero (q : Site × Site) (hq : q ∈ Sᵢ ×ˢ Tᵢ) (hqn : q ∉ Qᵢ) :
          f i q.1 q.2 = 0 := by
        have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, φ i p) = 0 := by
          by_contra hne
          exact hqn ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
            N (φ i)).mem_toFinset.mpr hne)
        simp [f, cellTestWeight, hcell]
      calc
        _ = ∑ q ∈ Sᵢ ×ˢ Tᵢ, f i q.1 q.2 := by
          simp only [Sᵢ, Tᵢ, f]
          rw [Finset.sum_product]
        _ = ∑ q ∈ Qᵢ, f i q.1 q.2 :=
          (Finset.sum_subset hsub (by
            intro q hq hqn
            exact hzero q hq hqn)).symm
        _ = _ := by simp only [Qᵢ, Q, f]

private theorem wordLimit_freeCellPairingSum_eq_annealed (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (φ : C_c(Plane × Plane, ℝ)) :
    (∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset,
      cellTestWeight N φ q.1 q.2 *
        srwKernel (evenCeil (N * t) - evenCeil (N * s)) (q.2 - q.1)) =
      ∫ p : Plane × Plane, φ p *
        (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) := by
  classical
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  let n := evenCeil (N * t) - evenCeil (N * s)
  have hzero (q : Site × Site) (hq : q ∉ S) :
      cellTestWeight N φ q.1 q.2 * srwKernel n (q.2 - q.1) = 0 := by
    have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, φ p) = 0 := by
      by_contra hne
      exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).mem_toFinset.mpr hne)
    simp [cellTestWeight, hcell]
  calc
    _ = ∑' q : Site × Site,
        cellTestWeight N φ q.1 q.2 * srwKernel n (q.2 - q.1) := by
      symm
      rw [tsum_eq_sum (s := S)]
      intro q hq
      exact hzero q hq
    _ = ((N : ℝ) / 4) * ∑' q : Site × Site,
        (∫ p in cell N q.1 ×ˢ cell N q.2, φ p) * srwKernel n (q.2 - q.1) := by
      calc
        _ = ∑' q : Site × Site,
            ((N : ℝ) / 4) * ((∫ p in cell N q.1 ×ˢ cell N q.2, φ p) *
              srwKernel n (q.2 - q.1)) := by
          apply tsum_congr
          intro q
          simp only [cellTestWeight]
          ring
        _ = _ := tsum_mul_left
    _ = ((N : ℝ) / 4) *
        ∫ p : Plane × Plane, φ p *
          srwKernel n (latticePoint N p.2 - latticePoint N p.1) := by
      congr 1
      exact (Critical2DKPZ.SHF.Flow.integral_latticePairing_eq_cellTsum N φ
        (fun a b => srwKernel n (b - a))).symm
    _ = ∫ p : Plane × Plane, φ p *
        (((N : ℝ) / 4) * srwKernel n (latticePoint N p.2 - latticePoint N p.1)) := by
      rw [← integral_const_mul]
      congr 1
      funext p
      ring
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simpa [n] using congrArg (fun x : ℝ => φ p * x)
          (integral_rescaledP2P ϑ N s t p).symm

private theorem wordLimit_integral_freeKernel_factorization
    (τ : ℝ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    (∫ x : Configuration h, ∫ y : Configuration h,
      (∏ i, φ i (x i, y i)) * freeKernel h τ x y) =
      ∏ i : Fin h, ∫ p : Plane × Plane,
        φ i p * heatKernel τ (p.2 - p.1) := by
  classical
  let g : Fin h → Plane → Plane → ℝ := fun i x y =>
    φ i (x, y) * heatKernel τ (y - x)
  have hpoint (x y : Configuration h) :
      (∏ i, φ i (x i, y i)) * freeKernel h τ x y = ∏ i, g i (x i) (y i) := by
    simp [g, DeltaBose.freeKernel, Finset.prod_mul_distrib]
  have hinner (x : Configuration h) :
      (∫ y : Configuration h, (∏ i, φ i (x i, y i)) * freeKernel h τ x y) =
        ∏ i : Fin h, ∫ y : Plane, g i (x i) y := by
    simp_rw [hpoint]
    exact integral_fintype_prod_volume_eq_prod (fun i y => g i (x i) y)
  calc
    _ = ∫ x : Configuration h, ∏ i : Fin h, ∫ y : Plane, g i (x i) y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    _ = ∏ i : Fin h, ∫ x : Plane, ∫ y : Plane, g i x y :=
      integral_fintype_prod_volume_eq_prod (fun i x => ∫ y : Plane, g i x y)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      have hcont : Continuous (fun p : Plane × Plane =>
          φ i p * heatKernel τ (p.2 - p.1)) := by
        exact (φ i).continuous.mul ((continuous_heatKernel τ).comp
          (continuous_snd.sub continuous_fst))
      have hcs : HasCompactSupport (fun p : Plane × Plane =>
          φ i p * heatKernel τ (p.2 - p.1)) := by
        exact HasCompactSupport.mul_right
          (f := fun p : Plane × Plane => φ i p)
          (f' := fun p : Plane × Plane => heatKernel τ (p.2 - p.1))
          (φ i).hasCompactSupport
      have hint : Integrable (fun p : Plane × Plane =>
          φ i p * heatKernel τ (p.2 - p.1)) :=
        hcont.integrable_of_hasCompactSupport hcs
      have hprod := integral_prod
        (fun p : Plane × Plane => φ i p * heatKernel τ (p.2 - p.1)) hint
      rw [← Measure.volume_eq_prod Plane Plane] at hprod
      simpa [g] using hprod.symm

/-- The empty word, for every number of replicas. -/
theorem testedBlockWord_tendsto_nil (ϑ : ℝ) {h : ℕ} {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (sN tN : ℕ → ℝ) (hsN : Tendsto sN atTop (𝓝 s)) (htN : Tendsto tN atTop (𝓝 t))
    (hsN0 : ∀ N, 0 ≤ sN N) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    Tendsto (fun N => testedBlockWord ϑ N (sN N) (tN N) φ []) atTop
      (𝓝 (∫ x : Configuration h, ∫ y : Configuration h, (∏ i, φ i (x i, y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) [] (t - s) x y).toReal)) := by
  classical
  let A : Fin h → ℕ → ℝ := fun i N =>
    ∑ q ∈ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset,
      cellTestWeight N (φ i) q.1 q.2 *
        srwKernel (evenCeil (N * tN N) - evenCeil (N * sN N)) (q.2 - q.1)
  have hfactor (N : ℕ) :
      testedBlockWord ϑ N (sN N) (tN N) φ [] = ∏ i : Fin h, A i N := by
    rw [testedBlockWord_nil_factorization]
  have hA (i : Fin h) : Tendsto (fun N => A i N) atTop
      (𝓝 (∫ p : Plane × Plane, φ i p * heatKernel (t - s) (p.2 - p.1))) := by
    have h := tendsto_pairing_annealed_rescaledP2P_moving ϑ hs hst sN tN
      hsN htN hsN0 (φ i).continuous (φ i).hasCompactSupport
    apply h.congr'
    filter_upwards with N
    exact (wordLimit_freeCellPairingSum_eq_annealed ϑ N (sN N) (tN N) (φ i)).symm
  have hprod : Tendsto (fun N => ∏ i : Fin h, A i N) atTop
      (𝓝 (∏ i : Fin h, ∫ p : Plane × Plane,
        φ i p * heatKernel (t - s) (p.2 - p.1))) := by
    exact tendsto_finsetProd Finset.univ (fun i hi => hA i)
  have hRHS :
      (∫ x : Configuration h, ∫ y : Configuration h, (∏ i, φ i (x i, y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) [] (t - s) x y).toReal) =
      ∏ i : Fin h, ∫ p : Plane × Plane,
        φ i p * heatKernel (t - s) (p.2 - p.1) := by
    have hkernel (x y : Configuration h) :
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) [] (t - s) x y).toReal =
          freeKernel h (t - s) x y := by
      rw [diagramKernel, ENNReal.toReal_ofReal]
      exact (freeKernel_pos h (sub_pos.mpr hst) x y).le
    simp_rw [hkernel]
    exact wordLimit_integral_freeKernel_factorization (t - s) φ
  rw [hRHS]
  apply hprod.congr'
  filter_upwards with N
  exact (hfactor N).symm

private theorem wordLimit_cellTestWeight_zero_of_fst_outside (N : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) (a b : Site)
    (ha : a ∉ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst) :
    cellTestWeight N φ a b = 0 := by
  have hq : (a, b) ∉ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset := by
    intro hmem
    exact ha (Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩)
  have hcell : (∫ p in cell N a ×ˢ cell N b, φ p) = 0 := by
    by_contra hne
    exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).mem_toFinset.mpr hne)
  simp [cellTestWeight, hcell]

private theorem wordLimit_cellTestWeight_zero_of_snd_outside (N : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) (a b : Site)
    (hb : b ∉ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.snd) :
    cellTestWeight N φ a b = 0 := by
  have hq : (a, b) ∉ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset := by
    intro hmem
    exact hb (Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩)
  have hcell : (∫ p in cell N a ×ˢ cell N b, φ p) = 0 := by
    by_contra hne
    exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).mem_toFinset.mpr hne)
  simp [cellTestWeight, hcell]

/-- A tested one-letter word factors into the tested pair word and its free
one-replica spectator contributions. -/
theorem testedBlockWord_single_eq (ϑ : ℝ) (N : ℕ) (s t : ℝ) {h : ℕ}
    (α : CollisionPair h) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    testedBlockWord ϑ N s t φ [α] =
      testedBlockWord ϑ N s t (pairRestrict α φ) [pairTwo] *
        ∏ i : Spectator α,
          testedBlockWord ϑ N s t (fun _ : Fin 1 => φ i.1) [] := by
  classical
  let n : ℕ := evenCeil (N * t) - evenCeil (N * s)
  let σ2 : ℝ := sigmaSq (criticalBeta ϑ N)
  let Q : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  let D : Fin h → Finset Site := fun i => (Q i).image Prod.fst
  let E : Fin h → Finset Site := fun i => (Q i).image Prod.snd
  let W : Fin h → Site → Site → ℝ := fun i a b => cellTestWeight N (φ i) a b
  let P : (Fin 2 → Site) → (Fin 2 → Site) → ℝ := fun p q =>
    (∏ j : Fin 2, cellTestWeight N ((pairRestrict α φ) j) (p j) (q j)) *
      blockWordKernel σ2 [pairTwo] n p q
  let G : Spectator α → Site → Site → ℝ := fun i a b =>
    W i.1 a b * srwKernel n (b - a)
  have hzeroX : ∀ x, x ∉ Fintype.piFinset D → ∀ y,
      (∏ i : Fin h, W i (x i) (y i)) * blockWordKernel σ2 [α] n x y = 0 := by
    intro x hx y
    have hmiss : ∃ i : Fin h, x i ∉ D i := by
      by_contra hn
      apply hx
      exact Fintype.mem_piFinset.mpr (by
        intro i
        by_contra hi
        exact hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hmiss
    have hW : W i (x i) (y i) = 0 := by
      exact wordLimit_cellTestWeight_zero_of_fst_outside N (φ i) (x i) (y i) (by
        simpa [D, Q] using hi)
    have hprod : (∏ j : Fin h, W j (x j) (y j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hW
    simp [hprod]
  have hzeroY : ∀ x y, y ∉ Fintype.piFinset E →
      (∏ i : Fin h, W i (x i) (y i)) * blockWordKernel σ2 [α] n x y = 0 := by
    intro x y hy
    have hmiss : ∃ i : Fin h, y i ∉ E i := by
      by_contra hn
      apply hy
      exact Fintype.mem_piFinset.mpr (by
        intro i
        by_contra hi
        exact hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hmiss
    have hW : W i (x i) (y i) = 0 := by
      exact wordLimit_cellTestWeight_zero_of_snd_outside N (φ i) (x i) (y i) (by
        simpa [E, Q] using hi)
    have hprod : (∏ j : Fin h, W j (x j) (y j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hW
    simp [hprod]
  have hrect := wordLimit_tsum_pair_rect_eq_sum D E
    (fun x y => (∏ i : Fin h, W i (x i) (y i)) * blockWordKernel σ2 [α] n x y)
    hzeroX hzeroY
  have hpoint (x y : Fin h → Site) :
      (∏ i : Fin h, W i (x i) (y i)) * blockWordKernel σ2 [α] n x y =
        P (pairRestrict α x) (pairRestrict α y) *
          ∏ i : Spectator α, G i (x i.1) (y i.1) := by
    have hφ0 : pairRestrict α φ 0 = φ α.1.1 := by simp [pairRestrict]
    have hφ1 : pairRestrict α φ 1 = φ α.1.2 := by simp [pairRestrict]
    have hx0 : pairRestrict α x 0 = x α.1.1 := by simp [pairRestrict]
    have hx1 : pairRestrict α x 1 = x α.1.2 := by simp [pairRestrict]
    have hy0 : pairRestrict α y 0 = y α.1.1 := by simp [pairRestrict]
    have hy1 : pairRestrict α y 1 = y α.1.2 := by simp [pairRestrict]
    rw [blockWordKernel_single_eq σ2 α n x y]
    simp only [P, G, W]
    rw [wordLimit_prod_pair_spectators α (fun i => cellTestWeight N (φ i) (x i) (y i))]
    simp only [Fin.prod_univ_two]
    rw [hφ0, hφ1, hx0, hx1, hy0, hy1]
    simp only [ite_true, ite_false, one_ne_zero]
    rw [Finset.prod_mul_distrib]
    ring_nf
  let DP : Fin 2 → Finset Site := fun j => D (if j = 0 then α.1.1 else α.1.2)
  let EP : Fin 2 → Finset Site := fun j => E (if j = 0 then α.1.1 else α.1.2)
  have hDP : DP = fun j =>
      ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N
        ((pairRestrict α φ) j)).toFinset.image Prod.fst) := by
    funext j
    fin_cases j <;> simp [DP, D, Q, pairRestrict]
  have hEP : EP = fun j =>
      ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N
        ((pairRestrict α φ) j)).toFinset.image Prod.snd) := by
    funext j
    fin_cases j <;> simp [EP, E, Q, pairRestrict]
  have hPzero (p : Fin 2 → Site) (hp : p ∉ Fintype.piFinset DP) (q : Fin 2 → Site) :
      P p q = 0 := by
    have hmiss : ∃ j : Fin 2, p j ∉ DP j := by
      by_contra hn
      apply hp
      exact Fintype.mem_piFinset.mpr (by
        intro j
        by_contra hj
        exact hn ⟨j, hj⟩)
    obtain ⟨j, hj⟩ := hmiss
    have hW : cellTestWeight N ((pairRestrict α φ) j) (p j) (q j) = 0 := by
      have hj' : p j ∉
          (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N
            ((pairRestrict α φ) j)).toFinset.image Prod.fst := by
        simpa only [hDP] using hj
      exact wordLimit_cellTestWeight_zero_of_fst_outside N ((pairRestrict α φ) j)
        (p j) (q j) hj'
    have hprod : (∏ j : Fin 2,
        cellTestWeight N ((pairRestrict α φ) j) (p j) (q j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hW
    simp only [P, hprod, zero_mul]
  have hQzero (p q : Fin 2 → Site) (hq : q ∉ Fintype.piFinset EP) : P p q = 0 := by
    by_cases hp : p ∈ Fintype.piFinset DP
    · have hmiss : ∃ j : Fin 2, q j ∉ EP j := by
        by_contra hn
        apply hq
        exact Fintype.mem_piFinset.mpr (by
          intro j
          by_contra hj
          exact hn ⟨j, hj⟩)
      obtain ⟨j, hj⟩ := hmiss
      have hW : cellTestWeight N ((pairRestrict α φ) j) (p j) (q j) = 0 := by
        have hj' : q j ∉
            (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N
              ((pairRestrict α φ) j)).toFinset.image Prod.snd := by
          simpa only [hEP] using hj
        exact wordLimit_cellTestWeight_zero_of_snd_outside N ((pairRestrict α φ) j)
          (p j) (q j) hj'
      have hprod : (∏ j : Fin 2,
          cellTestWeight N ((pairRestrict α φ) j) (p j) (q j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hW
      simp only [P, hprod, zero_mul]
    · exact hPzero p hp q
  have hpairTsum :
      (∑ p ∈ Fintype.piFinset DP, ∑ q ∈ Fintype.piFinset EP, P p q) =
        testedBlockWord ϑ N s t (pairRestrict α φ) [pairTwo] := by
    symm
    unfold testedBlockWord
    simpa [P, W, n, σ2, cellTestWeight] using
      (wordLimit_tsum_pair_rect_eq_sum DP EP P hPzero hQzero)
  have hspectator (i : Spectator α) :
      (∑ a ∈ D i.1, ∑ b ∈ E i.1, G i a b) =
        testedBlockWord ϑ N s t (fun _ : Fin 1 => φ i.1) [] := by
    have hnil := testedBlockWord_nil_factorization ϑ N s t
      (fun _ : Fin 1 => φ i.1)
    let Qi := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
      N (φ i.1)).toFinset
    let Di := Qi.image Prod.fst
    let Ei := Qi.image Prod.snd
    have hsubset : Qi ⊆ Di ×ˢ Ei := by
      intro q hq
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    have hout (q : Site × Site) (hq : q ∈ Di ×ˢ Ei) (hqn : q ∉ Qi) :
        W i.1 q.1 q.2 * srwKernel n (q.2 - q.1) = 0 := by
      have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, φ i.1 p) = 0 := by
        by_contra hne
        exact hqn ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
          N (φ i.1)).mem_toFinset.mpr hne)
      simp [W, cellTestWeight, n, hcell]
    have hfinite :
        (∑ a ∈ D i.1, ∑ b ∈ E i.1, W i.1 a b * srwKernel n (b - a)) =
          ∑ q ∈ Qi, W i.1 q.1 q.2 * srwKernel n (q.2 - q.1) := by
      calc
        _ = ∑ q ∈ Di ×ˢ Ei, W i.1 q.1 q.2 * srwKernel n (q.2 - q.1) := by
          rw [Finset.sum_product]
        _ = _ := (Finset.sum_subset hsubset (by
          intro q hq hqn
          exact hout q hq hqn)).symm
    rw [hnil]
    simpa [G, W, D, E, Q, n, Qi, Fin.prod_univ_one] using hfinite
  calc
    _ = ∑' x : Fin h → Site, ∑' y : Fin h → Site,
        (∏ i : Fin h, W i (x i) (y i)) * blockWordKernel σ2 [α] n x y := by
      unfold testedBlockWord
      apply tsum_congr
      intro x
      apply tsum_congr
      intro y
      simp [W, n, σ2, cellTestWeight]
    _ = ∑ x ∈ Fintype.piFinset D, ∑ y ∈ Fintype.piFinset E,
        (∏ i : Fin h, W i (x i) (y i)) * blockWordKernel σ2 [α] n x y := hrect
    _ = ∑ x ∈ Fintype.piFinset D, ∑ y ∈ Fintype.piFinset E,
        P (pairRestrict α x) (pairRestrict α y) *
          ∏ i : Spectator α, G i (x i.1) (y i.1) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact hpoint x y
    _ = (∑ p ∈ Fintype.piFinset DP, ∑ q ∈ Fintype.piFinset EP, P p q) *
          ∏ i : Spectator α, ∑ a ∈ D i.1, ∑ b ∈ E i.1, G i a b := by
      simpa [DP, EP, D, E] using
        (wordLimit_sum_pair_spectator_double α D E P G)
    _ = _ := by rw [hpairTsum]; simp_rw [hspectator]

end Critical2DKPZ.SHF.Moments

end
