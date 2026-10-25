/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.StringSumProfiles
public import Critical2DKPZ.Blocks.StringSumGaussian
import Critical2DKPZ.Collision.RenewalStringIntegral
import Mathlib.Tactic

/-! # Scalar bounds for occupied spatial-profile chains -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- The scalar renewal-string sum, indexed by occupied blocks. -/
def renewalStringSum (ϑ : ℝ) (N m : ℕ) (lo hi : Fin (m + 1) → ℕ) : ℝ :=
  ∑ a ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
    ∑ b ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
      if ∀ j, a j ≤ b j then
        (a 0 : ℝ)⁻¹ * (∏ j, criticalSigmaSq ϑ N *
          Renewal.criticalRenewalMass ϑ N (b j - a j)) *
            ∏ j : Fin m, (b j.castSucc : ℝ) /
              (a j.succ * ((a j.succ : ℝ) - b j.castSucc))
      else 0

/-- Split a finite product-domain sum into its first coordinate and its remaining coordinates.
This is the finite-sum form of `Fin.consEquiv`. -/
theorem sum_piFinset_cons {n : ℕ} (s₀ : Finset ℕ) (sₜ : Fin n → Finset ℕ)
    (F : (Fin (n + 1) → ℕ) → ℝ) :
    (∑ x ∈ Fintype.piFinset (Fin.cons s₀ sₜ), F x) =
      ∑ x₀ ∈ s₀, ∑ xₜ ∈ Fintype.piFinset sₜ, F (Fin.cons x₀ xₜ) := by
  classical
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun x _ => (x 0, Fin.tail x))
  · intro x hx
    exact Finset.mem_product.mpr ⟨(Fin.mem_piFinset_iff_zero_tail.mp hx).1,
      (Fin.mem_piFinset_iff_zero_tail.mp hx).2⟩
  · intro x hx y hy hxy
    funext i
    refine Fin.cases ?_ ?_ i
    · exact congrArg Prod.fst hxy
    · intro j
      exact congrFun (congrArg Prod.snd hxy) j
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp₀, hpₜ⟩
    refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
    · exact Fin.cons_mem_piFinset_cons.mpr ⟨hp₀, hpₜ⟩
    · simp
  · intro x hx
    rw [Fin.cons_self_tail]

/-- The scalar cost of a tail of occupied collision blocks, with its incoming last collision
time fixed. -/
def renewalStringTailSum (ϑ : ℝ) (N m : ℕ) (lo hi : Fin m → ℕ) (prev : ℕ) : ℝ :=
  ∑ a ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
    ∑ b ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
      if ∀ j, a j ≤ b j then
        (∏ j, criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b j - a j)) *
          ((∏ j : Fin m,
              ((Fin.cons (α := fun _ : Fin (m + 1) => ℕ) prev b) j.castSucc : ℝ)) /
            (∏ j : Fin m,
              (a j : ℝ) * ((a j : ℝ) -
                ((Fin.cons (α := fun _ : Fin (m + 1) => ℕ) prev b) j.castSucc : ℝ))))
      else 0

/-- List-indexed form of the scalar renewal sum for a tail of occupied blocks. -/
def renewalStringListTailSum (ϑ : ℝ) (N : ℕ) : List (ℕ × ℕ) → ℕ → ℝ
  | [], _ => 1
  | (lo, hi) :: rest, prev =>
      ∑ a ∈ Finset.Ioc lo hi, ∑ b ∈ Finset.Ioc lo hi,
        if a ≤ b then
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a)) *
            ((prev : ℝ) / ((a : ℝ) * ((a : ℝ) - prev))) *
              renewalStringListTailSum ϑ N rest b
        else 0

/-- List-indexed form of the scalar renewal sum, including its first occupied block. -/
def renewalStringListSum (ϑ : ℝ) (N : ℕ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | (lo, hi) :: rest =>
      ∑ a ∈ Finset.Ioc lo hi, ∑ b ∈ Finset.Ioc lo hi,
        if a ≤ b then
          (a : ℝ)⁻¹ * (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a)) *
            renewalStringListTailSum ϑ N rest b
        else 0

/-- Split the scalar sum at its first occupied block. -/
theorem renewalStringSum_cons (ϑ : ℝ) (N m : ℕ)
    (lo₀ hi₀ : ℕ) (loₜ hiₜ : Fin m → ℕ) :
    renewalStringSum ϑ N m
      (Fin.cons (α := fun _ : Fin (m + 1) => ℕ) lo₀ loₜ)
      (Fin.cons (α := fun _ : Fin (m + 1) => ℕ) hi₀ hiₜ) =
      ∑ a₀ ∈ Finset.Ioc lo₀ hi₀, ∑ b₀ ∈ Finset.Ioc lo₀ hi₀,
        if a₀ ≤ b₀ then
          (a₀ : ℝ)⁻¹ * (criticalSigmaSq ϑ N *
            Renewal.criticalRenewalMass ϑ N (b₀ - a₀)) *
              renewalStringTailSum ϑ N m loₜ hiₜ b₀
        else 0 := by
  classical
  unfold renewalStringSum
  have hdom : (fun j : Fin (m + 1) =>
      Finset.Ioc ((Fin.cons (α := fun _ : Fin (m + 1) => ℕ) lo₀ loₜ) j)
        ((Fin.cons (α := fun _ : Fin (m + 1) => ℕ) hi₀ hiₜ) j)) =
      (Fin.cons (α := fun _ : Fin (m + 1) => Finset ℕ) (Finset.Ioc lo₀ hi₀)
        (fun j => Finset.Ioc (loₜ j) (hiₜ j)) : Fin (m + 1) → Finset ℕ) := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cons]
  rw [hdom]
  simp_rw [sum_piFinset_cons]
  apply Finset.sum_congr rfl
  intro aFirst haFirst
  rw [Finset.sum_comm]
  simp_rw [Fin.forall_fin_succ, Fin.prod_univ_succ]
  simp_rw [Fin.cons_zero, Fin.cons_succ]
  simp only [renewalStringTailSum]
  apply Finset.sum_congr rfl
  intro bFirst hbFirst
  by_cases hab : aFirst ≤ bFirst
  · simp only [hab]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases htail : ∀ j : Fin m, a j ≤ b j
    · simp [htail, Finset.prod_div_distrib]
      ring
    · simp [htail]
  · simp [hab]

/-- Split a tail scalar sum at its first pair. The first transition uses the fixed incoming
collision time; the remaining product is again a tail sum. -/
theorem renewalStringTailSum_cons (ϑ : ℝ) (N m : ℕ)
    (lo₀ hi₀ : ℕ) (loₜ hiₜ : Fin m → ℕ) (prev : ℕ) :
    renewalStringTailSum ϑ N (m + 1)
      (Fin.cons (α := fun _ : Fin (m + 1) => ℕ) lo₀ loₜ)
      (Fin.cons (α := fun _ : Fin (m + 1) => ℕ) hi₀ hiₜ) prev =
      ∑ a₀ ∈ Finset.Ioc lo₀ hi₀, ∑ b₀ ∈ Finset.Ioc lo₀ hi₀,
        if a₀ ≤ b₀ then
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b₀ - a₀)) *
            ((prev : ℝ) / ((a₀ : ℝ) * ((a₀ : ℝ) - prev))) *
              renewalStringTailSum ϑ N m loₜ hiₜ b₀
        else 0 := by
  classical
  conv_lhs => rw [renewalStringTailSum]
  have hdom : (fun j : Fin (m + 1) =>
      Finset.Ioc ((Fin.cons (α := fun _ : Fin (m + 1) => ℕ) lo₀ loₜ) j)
        ((Fin.cons (α := fun _ : Fin (m + 1) => ℕ) hi₀ hiₜ) j)) =
      (Fin.cons (α := fun _ : Fin (m + 1) => Finset ℕ) (Finset.Ioc lo₀ hi₀)
        (fun j => Finset.Ioc (loₜ j) (hiₜ j)) : Fin (m + 1) → Finset ℕ) := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cons]
  rw [hdom]
  simp_rw [sum_piFinset_cons]
  apply Finset.sum_congr rfl
  intro aFirst haFirst
  rw [Finset.sum_comm]
  simp_rw [Fin.forall_fin_succ, Fin.prod_univ_succ]
  simp_rw [Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro bFirst hbFirst
  by_cases hab : aFirst ≤ bFirst
  · simp only [hab]
    conv_rhs => rw [renewalStringTailSum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases htail : ∀ j : Fin m, a j ≤ b j
    · simp [htail]
      field_simp
    · simp [htail]
  · simp [hab]

/-- The finite-product and list-indexed scalar renewal sums agree. -/
theorem renewalStringTailSum_eq_list (ϑ : ℝ) (N m : ℕ)
    (lo hi : Fin m → ℕ) (prev : ℕ) :
    renewalStringTailSum ϑ N m lo hi prev =
      renewalStringListTailSum ϑ N (List.ofFn fun j : Fin m => (lo j, hi j)) prev := by
  induction m generalizing prev with
  | zero =>
      simp [renewalStringTailSum, renewalStringListTailSum]
  | succ m ih =>
      rw [← Fin.cons_self_tail lo, ← Fin.cons_self_tail hi]
      rw [renewalStringTailSum_cons]
      have hlist :
          List.ofFn (fun j : Fin (m + 1) =>
            (Fin.cons (lo 0) (Fin.tail lo) j, Fin.cons (hi 0) (Fin.tail hi) j)) =
            (lo 0, hi 0) :: List.ofFn (fun j : Fin m => (Fin.tail lo j, Fin.tail hi j)) := by
        have hfun : (fun j : Fin (m + 1) =>
            (Fin.cons (lo 0) (Fin.tail lo) j, Fin.cons (hi 0) (Fin.tail hi) j)) =
            Fin.cons (lo 0, hi 0) (fun j => (Fin.tail lo j, Fin.tail hi j)) := by
          funext j
          refine Fin.cases ?_ ?_ j
          · rfl
          · intro i
            rfl
        rw [hfun, List.ofFn_cons]
      rw [hlist, renewalStringListTailSum]
      simp_rw [ih]

/-- The finite-product and list-indexed scalar renewal sums agree for the occupied tail. -/
theorem renewalStringSum_eq_list (ϑ : ℝ) (N m : ℕ)
    (lo hi : Fin (m + 1) → ℕ) :
    renewalStringSum ϑ N m lo hi =
      renewalStringListSum ϑ N (List.ofFn fun j : Fin (m + 1) => (lo j, hi j)) := by
  rw [← Fin.cons_self_tail lo, ← Fin.cons_self_tail hi]
  rw [renewalStringSum_cons]
  have hlist :
      List.ofFn (fun j : Fin (m + 1) =>
        (Fin.cons (lo 0) (Fin.tail lo) j, Fin.cons (hi 0) (Fin.tail hi) j)) =
        (lo 0, hi 0) :: List.ofFn (fun j : Fin m => (Fin.tail lo j, Fin.tail hi j)) := by
    have hfun : (fun j : Fin (m + 1) =>
        (Fin.cons (lo 0) (Fin.tail lo) j, Fin.cons (hi 0) (Fin.tail hi) j)) =
        Fin.cons (lo 0, hi 0) (fun j => (Fin.tail lo j, Fin.tail hi j)) := by
      funext j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro i
        rfl
    rw [hfun, List.ofFn_cons]
  rw [hlist, renewalStringListSum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : a ≤ b
  · simp only [hab]
    rw [renewalStringTailSum_eq_list ϑ N m (Fin.tail lo) (Fin.tail hi) b]
  · simp [hab]


/-- The occupied time cells are the vector of occupied cells, in list order. -/
theorem occupiedCells_ofFn_eq_list (t : ℕ → ℕ) (u v : ℕ) (S : Finset ℕ) :
    List.ofFn (fun j : Fin (S.card + 2) =>
      (occupiedLo t u v S j, occupiedHi t u v S j)) =
      (t (u - 1), t u) :: (S.sort (· ≤ ·) ++ [v]).map
        (fun i => (t (i - 1), t i)) := by
  let l := u :: (S.sort (· ≤ ·) ++ [v])
  let f : ℕ → ℕ × ℕ := fun i => (t (i - 1), t i)
  have hlen : l.length = S.card + 2 := by
    simp [l, Finset.length_sort]
  have hcastfun : (fun j : Fin (S.card + 2) => f (l.getD j 0)) =
      (fun j : Fin (S.card + 2) =>
        f (l[(Fin.cast hlen.symm j : Fin l.length)])) := by
    funext j
    have hj : (j : ℕ) < l.length := by omega
    rw [List.getD_eq_getElem l 0 hj]
    rfl
  have hmap := List.ofFn_getElem_eq_map l f
  have hmapCast := List.ofFn_congr hlen (fun j : Fin l.length => f l[j])
  have hofn : List.ofFn (fun j : Fin (S.card + 2) => f (l.getD j 0)) = List.map f l := by
    rw [hcastfun]
    exact hmapCast.symm.trans hmap
  simpa [occupiedLo, occupiedHi, occupiedIndex, f, l, List.map_append] using hofn


/-- A list of later occupied block indices, strictly following the previous index and bounded by
the terminal index. -/
def tailIndicesValid (u v : ℕ) : List ℕ → Prop
  | [] => True
  | i :: rest => u < i ∧ i ≤ v ∧ tailIndicesValid i v rest

/-- The total contribution after propagating an incoming spatial profile through the remaining occupied blocks. -/
def stringTailProfile (σ2 : ℝ) (t : ℕ → ℕ) : List ℕ → ℕ → (Site → ℝ) → ℝ
  | [], _, f => ∑' y, f y
  | i :: rest, k, f =>
      ∑ a ∈ Finset.Ioc (t (i - 1)) (t i), ∑ b ∈ Finset.Icc a (t i),
        stringTailProfile σ2 t rest b (transitionSpatialProfile σ2 k a b f)

/-- The scalar cost of a tail with its collision times summed. -/
def stringTailScalarCost (σ2 Cwalk Crenewal : ℝ) (t : ℕ → ℕ) :
    List ℕ → ℕ → ℝ
  | [], _ => 1
  | i :: rest, k =>
      ∑ a ∈ Finset.Ioc (t (i - 1)) (t i), ∑ b ∈ Finset.Icc a (t i),
        transitionProfileFactor σ2 Cwalk Crenewal k a b *
          stringTailScalarCost σ2 Cwalk Crenewal t rest b

/-- A finite set containing the support of the transition time-site integrand. -/
def transitionPairSupport (k a b : ℕ) (S : Finset Site) : Finset (Site × Site) :=
  S.biUnion fun y₀ =>
    (Polymer.endpoints y₀ (a - k) ∪ Polymer.endpoints 0 a).biUnion fun x =>
      (Polymer.endpoints x (b - a)).image fun y => (y₀, y)

/-- A finite set containing the support of the transition spatial integrand. -/
def transitionXYSupport (k a b : ℕ) (y₀ : Site) : Finset (Site × Site) :=
  (Polymer.endpoints y₀ (a - k) ∪ Polymer.endpoints 0 a).biUnion fun x =>
    (Polymer.endpoints x (b - a)).image fun y => (x, y)

/-- The transition pairing integrand vanishes outside its finite support. -/
theorem transitionPairTerm_eq_zero_of_not_mem_support {σ2 : ℝ} {k a b : ℕ}
    {f g : Site → ℝ} {S : Finset Site} {p : Site × Site}
    (hf : ∀ y, y ∉ S → f y = 0)
    (hp : p ∉ transitionPairSupport k a b S) :
    f p.1 *
      (∑' x, (srwKernel (a - k) (x - p.1) - srwKernel a x) ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (p.2 - x))) * g p.2 = 0 := by
  rcases p with ⟨y₀, y⟩
  by_cases hy₀ : y₀ ∈ S
  · have hinner : (fun x =>
        (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
          (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))) = 0 := by
      funext x
      by_cases hx : x ∈ Polymer.endpoints y₀ (a - k) ∪ Polymer.endpoints 0 a
      · have hyx : y ∉ Polymer.endpoints x (b - a) := by
          intro hxy
          apply hp
          exact Finset.mem_biUnion.mpr ⟨y₀, hy₀,
            Finset.mem_biUnion.mpr ⟨x, hx,
              Finset.mem_image.mpr ⟨y, hxy, rfl⟩⟩⟩
        have hu : Collision.spatialRenewal σ2 (b - a) (y - x) = 0 :=
          spatialRenewal_eq_zero_of_not_mem_endpoints
            (by simpa only [mem_endpoints_sub_iff] using hyx)
        simp [hu]
      · have hx₁ : x ∉ Polymer.endpoints y₀ (a - k) := by
          intro hx₁
          exact hx (Finset.mem_union.mpr (Or.inl hx₁))
        have hx₂ : x ∉ Polymer.endpoints 0 a := by
          intro hx₂
          exact hx (Finset.mem_union.mpr (Or.inr hx₂))
        have hq₁ := Polymer.srwKernel_eq_zero_of_not_mem (a - k) y₀ x hx₁
        have hq₂' := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx₂
        have hq₂ : srwKernel a x = 0 := by simpa only [sub_zero] using hq₂'
        simp [hq₁, hq₂]
    have hsum : ∑' x,
        (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
          (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) = 0 := by
      rw [hinner]
      exact tsum_zero
    rw [hsum]
    simp
  · rw [hf y₀ hy₀]
    simp

/-- The two-site transition integrand is summable by finite walk support. -/
theorem summable_transitionXYTerm {σ2 : ℝ} {k a b : ℕ} (y₀ : Site) (g : Site → ℝ) :
    Summable (fun p : Site × Site =>
      (srwKernel (a - k) (p.1 - y₀) - srwKernel a p.1) ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (p.2 - p.1)) * g p.2) := by
  apply summable_of_ne_finset_zero (s := transitionXYSupport k a b y₀)
  intro p hp
  rcases p with ⟨x, y⟩
  by_cases hx : x ∈ Polymer.endpoints y₀ (a - k) ∪ Polymer.endpoints 0 a
  · have hy : y ∉ Polymer.endpoints x (b - a) := by
      intro hy
      apply hp
      exact Finset.mem_biUnion.mpr ⟨x, hx,
        Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩
    have hu : Collision.spatialRenewal σ2 (b - a) (y - x) = 0 :=
      spatialRenewal_eq_zero_of_not_mem_endpoints
        (by simpa only [mem_endpoints_sub_iff] using hy)
    simp [hu]
  · have hx₁ : x ∉ Polymer.endpoints y₀ (a - k) := by
      intro hx₁
      exact hx (Finset.mem_union.mpr (Or.inl hx₁))
    have hx₂ : x ∉ Polymer.endpoints 0 a := by
      intro hx₂
      exact hx (Finset.mem_union.mpr (Or.inr hx₂))
    have hq₁ := Polymer.srwKernel_eq_zero_of_not_mem (a - k) y₀ x hx₁
    have hq₂' := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx₂
    have hq₂ : srwKernel a x = 0 := by simpa only [sub_zero] using hq₂'
    simp [hq₁, hq₂]

/-- Pairing a transition profile with a terminal function is the same spatial sum as its
collision-string kernel. -/
theorem transitionSpatialProfile_pairing {σ2 : ℝ} {k a b : ℕ}
    {f g : Site → ℝ} {S : Finset Site}
    (hf : ∀ y, y ∉ S → f y = 0) :
    ∑' y, transitionSpatialProfile σ2 k a b f y * g y =
      ∑' y₀, f y₀ * ∑' x, ∑' y,
        (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
          (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y := by
  let P : Site × Site → ℝ := fun p =>
    f p.1 *
      (∑' x, (srwKernel (a - k) (x - p.1) - srwKernel a x) ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (p.2 - x))) * g p.2
  have hP : Summable P := by
    apply summable_of_ne_finset_zero (s := transitionPairSupport k a b S)
    intro p hp
    exact transitionPairTerm_eq_zero_of_not_mem_support hf hp
  have hswap := Summable.tsum_comm (f := fun y₀ y => P (y₀, y)) hP
  calc
    _ = ∑' y, ∑' y₀, P (y₀, y) := by
      apply tsum_congr
      intro y
      rw [transitionSpatialProfile]
      rw [← tsum_mul_right]
    _ = ∑' y₀, ∑' y, P (y₀, y) := hswap
    _ = ∑' y₀, f y₀ * ∑' x, ∑' y,
          (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
            (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y := by
      apply tsum_congr
      intro y₀
      have hQ := summable_transitionXYTerm (σ2 := σ2) (k := k) (a := a) (b := b) y₀ g
      calc
        _ = f y₀ * ∑' y, (∑' x,
              (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
                (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))) * g y := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro y
          dsimp [P]
          ring
        _ = f y₀ * ∑' y, ∑' x,
              (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
                (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y := by
          congr 1
          apply tsum_congr
          intro y
          rw [← tsum_mul_right]
        _ = f y₀ * ∑' x, ∑' y,
              (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
                (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y := by
          apply congrArg (fun z : ℝ => f y₀ * z)
          exact Summable.tsum_comm (f := fun x y =>
            (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
              (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y) hQ

/-- A finite set containing the support of the initial time-site integrand. -/
def initialPairSupport (a b : ℕ) : Finset (Site × Site) :=
  (Polymer.endpoints 0 a).biUnion fun x =>
    (Polymer.endpoints x (b - a)).image fun y => (x, y)

/-- The initial-block summand vanishes outside its two-walk support. -/
theorem initialPairTerm_eq_zero_of_not_mem_support {σ2 : ℝ} {a b : ℕ}
    {g : Site → ℝ} {p : Site × Site} (hp : p ∉ initialPairSupport a b) :
    srwKernel a p.1 ^ 2 *
      (σ2 * Collision.spatialRenewal σ2 (b - a) (p.2 - p.1)) * g p.2 = 0 := by
  rcases p with ⟨x, y⟩
  by_cases hx : x ∈ Polymer.endpoints 0 a
  · have hy : y ∉ Polymer.endpoints x (b - a) := by
      intro hxy
      apply hp
      exact Finset.mem_biUnion.mpr ⟨x, hx,
        Finset.mem_image.mpr ⟨y, hxy, rfl⟩⟩
    have hu : Collision.spatialRenewal σ2 (b - a) (y - x) = 0 :=
      spatialRenewal_eq_zero_of_not_mem_endpoints
        (by simpa only [mem_endpoints_sub_iff] using hy)
    simp [hu]
  · have hq := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
    have hq' : srwKernel a x = 0 := by simpa only [sub_zero] using hq
    simp [hq']

/-- The initial spatial pairing is the corresponding sum over the first collision site. -/
theorem initialSpatialProfile_pairing {σ2 : ℝ} {a b : ℕ} {g : Site → ℝ} :
    ∑' y, initialSpatialProfile σ2 a b y * g y =
      ∑' x, ∑' y, srwKernel a x ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y := by
  have hP : Summable (fun p : Site × Site =>
      srwKernel a p.1 ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (p.2 - p.1)) * g p.2) := by
    apply summable_of_ne_finset_zero (s := initialPairSupport a b)
    intro p hp
    exact initialPairTerm_eq_zero_of_not_mem_support hp
  calc
    _ = ∑' y, ∑' x, srwKernel a x ^ 2 *
          (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y := by
      apply tsum_congr
      intro y
      rw [initialSpatialProfile]
      rw [← tsum_mul_right]
    _ = _ :=
      Summable.tsum_comm (f := fun x y =>
        srwKernel a x ^ 2 *
          (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * g y) hP

/-- Pairing a finite-support input profile with the recursively defined tail is equal to summing
the corresponding profile recursion. -/
theorem stringTailProfile_pairing {σ2 : ℝ} {t : ℕ → ℕ} {is : List ℕ}
    {k : ℕ} {f : Site → ℝ} {S : Finset Site}
    (hf : ∀ y, y ∉ S → f y = 0) :
    stringTailProfile σ2 t is k f = ∑' y, f y * stringTail σ2 t is k y := by
  induction is generalizing k f S with
  | nil => simp [stringTailProfile, stringTail]
  | cons i rest ih =>
      simp only [stringTailProfile, stringTail]
      let A := Finset.Ioc (t (i - 1)) (t i)
      let B (a : ℕ) := Finset.Icc a (t i)
      have hstep (a b : ℕ) :
          stringTailProfile σ2 t rest b (transitionSpatialProfile σ2 k a b f) =
            ∑' y, transitionSpatialProfile σ2 k a b f y * stringTail σ2 t rest b y := by
        apply ih (k := b) (f := transitionSpatialProfile σ2 k a b f)
          (S := transitionSpatialProfileSupport k a b S)
        intro y hy
        exact transitionSpatialProfile_eq_zero_of_not_mem_support hf hy
      have hpair (a b : ℕ) :
          ∑' y, transitionSpatialProfile σ2 k a b f y * stringTail σ2 t rest b y =
            ∑' y₀, f y₀ * ∑' x, ∑' y,
              (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
                (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
                  stringTail σ2 t rest b y :=
        transitionSpatialProfile_pairing hf
      have hfinite (F : Site → ℝ) :
          (∑' y, f y * F y) = ∑ y ∈ S, f y * F y :=
        tsum_eq_sum (s := S) (fun y hy => by simp [hf y hy])
      simp_rw [hstep, hpair, hfinite]
      change
        (∑ a ∈ A, ∑ b ∈ B a, ∑ y₀ ∈ S,
          f y₀ * ∑' x, ∑' y,
            (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
              (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
                stringTail σ2 t rest b y) =
        ∑ y₀ ∈ S, f y₀ * ∑ a ∈ A, ∑ b ∈ B a, ∑' x, ∑' y,
          (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
            (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
              stringTail σ2 t rest b y
      calc
        _ = ∑ a ∈ A, ∑ y₀ ∈ S, ∑ b ∈ B a, f y₀ *
              (∑' x, ∑' y,
                (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
                  (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
                    stringTail σ2 t rest b y) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = ∑ a ∈ A, ∑ y₀ ∈ S, f y₀ * ∑ b ∈ B a, ∑' x, ∑' y,
              (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
                (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
                  stringTail σ2 t rest b y := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro y₀ hy₀
          rw [← Finset.mul_sum]
        _ = ∑ y₀ ∈ S, ∑ a ∈ A, f y₀ * ∑ b ∈ B a, ∑' x, ∑' y,
              (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
                (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
                  stringTail σ2 t rest b y := by
          exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro y₀ hy₀
          rw [← Finset.mul_sum]

/-- The total tail contribution is bounded by the input Gaussian constant times the scalar tail cost and the Gaussian mass bound. -/
theorem stringTailProfile_le_scalarCost {c Cwalk Crenewal σ2 : ℝ}
    (hc : 0 < c) (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hvariance : ∀ k a : ℕ, 0 < k → k < a → ∀ x : Site,
      ∑' y, Collision.hatGaussian c k y *
        (srwKernel (a - k) (x - y) - srwKernel a x) ^ 2 ≤
          Cwalk * k / (a * (a - k)) * Collision.hatGaussian c a x)
    (hσ : 0 ≤ σ2) (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    (t : ℕ → ℕ) {u v : ℕ} (ht : MonotoneOn t (Set.Iic v))
    (is : List ℕ) (hidx : tailIndicesValid u v is)
    (k : ℕ) (hk : 1 ≤ k) (hku : k ≤ t u)
    (K : ℝ) (hK : 0 ≤ K) (f : Site → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (hf : ∀ y, f y ≤ K * Collision.hatGaussian c k y) (hfs : Summable f) :
    stringTailProfile σ2 t is k f ≤
      K * stringTailScalarCost σ2 Cwalk Crenewal t is k *
        (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
  revert u v ht hidx k hk hku K hK f hf0 hf hfs
  induction is with
  | nil =>
      intro u v ht hidx k hk hku K hK f hf0 hf hfs
      simp only [stringTailProfile, stringTailScalarCost]
      have htotal := Collision.hatGaussian_totalMass_le hc hk
      calc
        _ ≤ ∑' y, K * Collision.hatGaussian c k y :=
          hfs.tsum_le_tsum hf ((Collision.hatGaussian_summable hc hk).mul_left K)
        _ = K * ∑' y, Collision.hatGaussian c k y := tsum_mul_left
        _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left htotal hK
  | cons i rest ih =>
      intro u v ht hidx k hk hku K hK f hf0 hf hfs
      rcases hidx with ⟨hui, hiv, hrest⟩
      have hti : u ≤ i - 1 := by omega
      have huiV : u ∈ Set.Iic v := by simp only [Set.mem_Iic]; omega
      have him1V : i - 1 ∈ Set.Iic v := by simp only [Set.mem_Iic]; omega
      have htu : t u ≤ t (i - 1) := ht huiV him1V hti
      simp only [stringTailProfile, stringTailScalarCost]
      calc
        _ ≤ ∑ a ∈ Finset.Ioc (t (i - 1)) (t i),
            ∑ b ∈ Finset.Icc a (t i),
              (K * transitionProfileFactor σ2 Cwalk Crenewal k a b *
                stringTailScalarCost σ2 Cwalk Crenewal t rest b) *
                  (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          have haLower : t (i - 1) < a := (Finset.mem_Ioc.mp ha).1
          have hab : a ≤ b := (Finset.mem_Icc.mp hb).1
          have hbt : b ≤ t i := (Finset.mem_Icc.mp hb).2
          have hkLower : k < a := lt_of_le_of_lt (le_trans hku htu) haLower
          have haOne : 1 ≤ a := le_trans hk (Nat.le_of_lt hkLower)
          have hF : 0 ≤ transitionProfileFactor σ2 Cwalk Crenewal k a b :=
            transitionProfileFactor_nonneg hCwalk hCrenewal hσ hU hk hkLower
          let K' : ℝ := K * transitionProfileFactor σ2 Cwalk Crenewal k a b
          have hK' : 0 ≤ K' := mul_nonneg hK hF
          let f' := transitionSpatialProfile σ2 k a b f
          have hstep := transitionSpatialProfile_bounds hc hCwalk hCrenewal
            hconvolution hrenewal hvariance hσ hU hK hk hkLower hab f hf0 hf hfs
          have hf' : ∀ y, f' y ≤ K' * Collision.hatGaussian c b y := by
            intro y
            have hpoint := hstep.2.2 y
            change transitionSpatialProfile σ2 k a b f y ≤
              (K * transitionProfileFactor σ2 Cwalk Crenewal k a b) *
                Collision.hatGaussian c b y
            calc
              _ ≤ (K * Cwalk * k / (a * (a - k)) * Crenewal * Cwalk *
                  (σ2 * (∑' z, Collision.spatialRenewal σ2 (b - a) z))) *
                  Collision.hatGaussian c b y := hpoint
              _ = _ := by
                unfold transitionProfileFactor
                ring
          have hbOne : 1 ≤ b := le_trans haOne hab
          have hnext := ih (u := i) (v := v) ht hrest b hbOne hbt K' hK' f'
            hstep.1 hf' hstep.2.1
          simpa only [f', K'] using hnext
        _ = K * stringTailScalarCost σ2 Cwalk Crenewal t (i :: rest) k *
            (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
          simp only [stringTailScalarCost]
          let Aset := Finset.Ioc (t (i - 1)) (t i)
          let Bset (a : ℕ) := Finset.Icc a (t i)
          let g (a b : ℕ) :=
            transitionProfileFactor σ2 Cwalk Crenewal k a b *
              stringTailScalarCost σ2 Cwalk Crenewal t rest b
          have hinner (a : ℕ) (ha : a ∈ Aset) :
              (∑ b ∈ Bset a,
                (K * transitionProfileFactor σ2 Cwalk Crenewal k a b *
                  stringTailScalarCost σ2 Cwalk Crenewal t rest b) *
                    (1 + Real.sqrt (Real.pi / c)) ^ 2) =
                (K * ∑ b ∈ Bset a, g a b) * (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
            calc
              _ = (∑ b ∈ Bset a,
                    K * (transitionProfileFactor σ2 Cwalk Crenewal k a b *
                      stringTailScalarCost σ2 Cwalk Crenewal t rest b)) *
                    (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
                rw [Finset.sum_mul]
                congr 1
                funext b
                ring
              _ = _ := by rw [Finset.mul_sum]
          calc
            _ = ∑ a ∈ Aset,
                  (K * ∑ b ∈ Bset a, g a b) *
                    (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro a ha
              simpa only [Aset, Bset, g] using hinner a ha
            _ = (K * ∑ a ∈ Aset, ∑ b ∈ Bset a, g a b) *
                  (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
              calc
                _ = (∑ a ∈ Aset, K * ∑ b ∈ Bset a, g a b) *
                    (1 + Real.sqrt (Real.pi / c)) ^ 2 := by rw [Finset.sum_mul]
                _ = _ := by rw [Finset.mul_sum]
            _ = _ := by
              simp only [Aset, Bset, g]

/-- The sorted interior occupied blocks and terminal block form a valid tail. -/
theorem tailIndicesValid_sorted_occupied {u v : ℕ} {S : Finset ℕ}
    (huv : u < v) (hS : S ⊆ Finset.Ioo u v) :
    tailIndicesValid u v (S.sort (· ≤ ·) ++ [v]) := by
  have hsorted : (u :: (S.sort (· ≤ ·) ++ [v])).SortedLT := by
    rw [List.sortedLT_cons]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hxS | hxv
      · exact (Finset.mem_Ioo.mp (hS (Finset.mem_sort _ |>.1 hxS))).1
      · have hxv' : x = v := List.mem_singleton.mp hxv
        rw [hxv']
        exact huv
    · rw [List.sortedLT_append]
      refine ⟨S.sortedLT_sort, by simp [List.sortedLT_iff_pairwise], ?_⟩
      intro x hx y hy
      have hyv : y = v := List.mem_singleton.mp hy
      rw [hyv]
      exact (Finset.mem_Ioo.mp (hS (Finset.mem_sort _ |>.1 hx))).2
  have hbound : ∀ x ∈ S.sort (· ≤ ·) ++ [v], x ≤ v := by
    intro x hx
    rcases List.mem_append.mp hx with hxS | hxv
    · exact (Finset.mem_Ioo.mp (hS (Finset.mem_sort _ |>.1 hxS))).2.le
    · rw [List.mem_singleton.mp hxv]
  have aux : ∀ (head : ℕ) (l : List ℕ),
      (head :: l).Pairwise (· < ·) → (∀ x ∈ l, x ≤ v) → tailIndicesValid head v l := by
    intro head l
    induction l generalizing head with
    | nil => intro hp hb; trivial
    | cons i rest ih =>
        intro hp hb
        rcases List.pairwise_cons.mp hp with ⟨hhead, htail⟩
        refine ⟨hhead i (by simp), hb i (by simp), ?_⟩
        apply ih i htail
        intro x hx
        exact hb x (List.mem_cons_of_mem i hx)
  exact aux u (S.sort (· ≤ ·) ++ [v]) hsorted.pairwise hbound

/-- Every later index in a valid tail lies strictly after its incoming index. -/
theorem tailIndicesValid_lt_of_mem {u v : ℕ} {is : List ℕ}
    (hvalid : tailIndicesValid u v is) {i : ℕ} (hi : i ∈ is) : u < i := by
  induction is generalizing u with
  | nil => simp at hi
  | cons j rest ih =>
      rcases hvalid with ⟨huj, hjv, hrest⟩
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact huj
      · exact huj.trans (ih hrest hi)

/-- Every index in a valid tail is bounded by its terminal index. -/
theorem tailIndicesValid_le_of_mem {u v : ℕ} {is : List ℕ}
    (hvalid : tailIndicesValid u v is) {i : ℕ} (hi : i ∈ is) : i ≤ v := by
  induction is generalizing u with
  | nil => simp at hi
  | cons j rest ih =>
      rcases hvalid with ⟨huj, hjv, hrest⟩
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hjv
      · exact ih hrest hi

/-- The time cells of a valid occupied tail are chronologically separated. -/
def renewalCellsOrdered : List (ℕ × ℕ) → Prop
  | [] => True
  | (_, hi) :: rest => (∀ p ∈ rest, hi ≤ p.1) ∧ renewalCellsOrdered rest

/-- Monotone time grids send valid occupied indices to separated cells. -/
theorem renewalCellsOrdered_map_of_tailIndicesValid {u v : ℕ} {t : ℕ → ℕ}
    (ht : MonotoneOn t (Set.Iic v)) {is : List ℕ}
    (hvalid : tailIndicesValid u v is) :
    renewalCellsOrdered (is.map fun i => (t (i - 1), t i)) := by
  induction is generalizing u with
  | nil => trivial
  | cons i rest ih =>
      rcases hvalid with ⟨hui, hiv, hrest⟩
      constructor
      · intro p hp
        rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
        have hij : i < j := tailIndicesValid_lt_of_mem hrest hj
        have him1j : i ≤ j - 1 := by omega
        have hiIic : i ∈ Set.Iic v := by simp only [Set.mem_Iic]; exact hiv
        have hjle : j ≤ v := tailIndicesValid_le_of_mem hrest hj
        have hjm1Iic : j - 1 ∈ Set.Iic v := by
          simp only [Set.mem_Iic]
          omega
        exact ht hiIic hjm1Iic him1j
      · exact ih hrest

/-- Every cell in a valid occupied tail begins no earlier than the incoming block endpoint. -/
theorem timeCell_lower_ge_of_tailIndicesValid {u v : ℕ} {t : ℕ → ℕ}
    (ht : MonotoneOn t (Set.Iic v)) {is : List ℕ}
    (hvalid : tailIndicesValid u v is) (b : ℕ) (hb : b ≤ t u) :
    ∀ p ∈ is.map (fun i => (t (i - 1), t i)), b ≤ p.1 := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
  have hui : u < i := tailIndicesValid_lt_of_mem hvalid hi
  have hile : i ≤ v := tailIndicesValid_le_of_mem hvalid hi
  have hiIic : i ∈ Set.Iic v := by
    simp only [Set.mem_Iic]
    exact hile
  have him1Iic : i - 1 ∈ Set.Iic v := by
    simp only [Set.mem_Iic]
    omega
  have huIic : u ∈ Set.Iic v := by
    simp only [Set.mem_Iic]
    omega
  have htu : t u ≤ t (i - 1) := ht huIic him1Iic (by omega)
  exact hb.trans htu

/-- Scalar tail sums are nonnegative on chronologically ordered cells. -/
theorem renewalStringListTailSum_nonneg {ϑ : ℝ} {N : ℕ}
    (hσ : 0 ≤ criticalSigmaSq ϑ N)
    (hmass : ∀ n, 0 ≤ Renewal.criticalRenewalMass ϑ N n) :
    ∀ (cells : List (ℕ × ℕ)) (prev : ℕ),
      (∀ p ∈ cells, prev ≤ p.1) → renewalCellsOrdered cells →
        0 ≤ renewalStringListTailSum ϑ N cells prev := by
  intro cells
  induction cells with
  | nil => intro prev hbelow hordered; simp [renewalStringListTailSum]
  | cons cell rest ih =>
      rcases cell with ⟨lo, hi⟩
      intro prev hbelow hordered
      rcases hordered with ⟨hsep, horderedRest⟩
      have hprevLo : prev ≤ lo := hbelow (lo, hi) (by simp)
      simp only [renewalStringListTailSum]
      apply Finset.sum_nonneg
      intro a ha
      apply Finset.sum_nonneg
      intro b hb
      by_cases hab : a ≤ b
      · simp [hab]
        have haLo : lo < a := (Finset.mem_Ioc.mp ha).1
        have hbHi : b ≤ hi := (Finset.mem_Ioc.mp hb).2
        have haOne : 1 ≤ a := by omega
        have hbOne : 1 ≤ b := by omega
        have hprevLt : prev < a := lt_of_le_of_lt hprevLo haLo
        have hden : 0 < (a : ℝ) * ((a : ℝ) - prev) := by
          have haR : 0 < (a : ℝ) := by exact_mod_cast haOne
          have hprevLtR : (prev : ℝ) < (a : ℝ) := by exact_mod_cast hprevLt
          have hdiff : 0 < (a : ℝ) - (prev : ℝ) := sub_pos.mpr hprevLtR
          exact mul_pos haR hdiff
        have hcoef : 0 ≤ criticalSigmaSq ϑ N *
            Renewal.criticalRenewalMass ϑ N (b - a) := mul_nonneg hσ (hmass _)
        have hratio : 0 ≤ (prev : ℝ) / ((a : ℝ) * ((a : ℝ) - prev)) :=
          div_nonneg (Nat.cast_nonneg _) hden.le
        have hbelowRest : ∀ p ∈ rest, b ≤ p.1 := by
          intro p hp
          exact (le_trans hbHi (hsep p hp))
        have htail := ih b hbelowRest horderedRest
        exact mul_nonneg (mul_nonneg hcoef hratio) htail
      · simp [hab]


/-- Reindex the ordered pair of collision times in one block by its finite two-coordinate support. -/
theorem sum_collisionTimePair_eq_sum_filtered_product {lo hi : ℕ} (F : ℕ × ℕ → ℝ) :
    (∑ a ∈ Finset.Ioc lo hi, ∑ b ∈ Finset.Icc a hi, F (a, b)) =
      ∑ p ∈ ((Finset.Ioc lo hi) ×ˢ (Finset.Ioc lo hi)).filter (fun p => p.1 ≤ p.2), F p := by
  let S := Finset.Ioc lo hi
  have hset (a : ℕ) (ha : a ∈ S) :
      Finset.Icc a hi = S.filter (fun b => a ≤ b) := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ioc, S]
    have hla : lo < a := (Finset.mem_Ioc.mp (by simpa [S] using ha)).1
    constructor
    · rintro ⟨hab, hbhi⟩
      refine ⟨⟨?_, hbhi⟩, hab⟩
      omega
    · rintro ⟨⟨hblo, hbhi⟩, hab⟩
      exact ⟨hab, hbhi⟩
  calc
    _ = ∑ a ∈ S, ∑ b ∈ S.filter (fun b => a ≤ b), F (a, b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hset a ha]
    _ = ∑ a ∈ S, ∑ b ∈ S, (if a ≤ b then F (a, b) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter]
    _ = ∑ p ∈ S ×ˢ S, (if p.1 ≤ p.2 then F p else 0) := by
      exact (Finset.sum_product' S S
        (fun a b => if a ≤ b then F (a, b) else 0)).symm
    _ = ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≤ p.2), F p := by
      rw [← Finset.sum_filter]

/-- Replace the ordered second-time interval by the conditional product-cell sum. -/
theorem sum_collisionTimePair_eq_conditional {lo hi : ℕ} (F : ℕ × ℕ → ℝ) :
    (∑ a ∈ Finset.Ioc lo hi, ∑ b ∈ Finset.Icc a hi, F (a, b)) =
      ∑ a ∈ Finset.Ioc lo hi, ∑ b ∈ Finset.Ioc lo hi,
        if a ≤ b then F (a, b) else 0 := by
  calc
    _ = ∑ p ∈ ((Finset.Ioc lo hi) ×ˢ (Finset.Ioc lo hi)).filter
          (fun p => p.1 ≤ p.2), F p :=
        sum_collisionTimePair_eq_sum_filtered_product F
    _ = ∑ p ∈ Finset.Ioc lo hi ×ˢ Finset.Ioc lo hi,
          if p.1 ≤ p.2 then F p else 0 := by
        rw [Finset.sum_filter]
    _ = _ := by
      simpa only [Prod.fst, Prod.snd] using
        (Finset.sum_product' (Finset.Ioc lo hi) (Finset.Ioc lo hi)
          (fun a b => if a ≤ b then F (a, b) else 0))

/-- One Gaussian-profile transition is the scalar transition times its uniform constant. -/
theorem transitionProfileFactor_eq_renewalScalarFactor {ϑ σ2 Cwalk Crenewal : ℝ}
    {N k a b : ℕ} (hσ : σ2 = criticalSigmaSq ϑ N) :
    transitionProfileFactor σ2 Cwalk Crenewal k a b =
      (Cwalk ^ 2 * Crenewal) *
        (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a) *
          ((k : ℝ) / ((a : ℝ) * ((a : ℝ) - k)))) := by
  unfold transitionProfileFactor
  rw [hσ, tsum_spatialRenewal_eq_criticalRenewalMass]
  ring

/-- The profile scalar cost is exactly a constant power times the scalar tail sum. -/
theorem stringTailScalarCost_eq_renewalStringListTailSum
    {ϑ σ2 Cwalk Crenewal : ℝ} {N : ℕ} {t : ℕ → ℕ}
    (hσ : σ2 = criticalSigmaSq ϑ N) (is : List ℕ) (k : ℕ) :
    stringTailScalarCost σ2 Cwalk Crenewal t is k =
      (Cwalk ^ 2 * Crenewal) ^ is.length *
        renewalStringListTailSum ϑ N (is.map fun i => (t (i - 1), t i)) k := by
  classical
  induction is generalizing k with
  | nil => simp [stringTailScalarCost, renewalStringListTailSum]
  | cons i rest ih =>
      let D : ℝ := Cwalk ^ 2 * Crenewal
      have hsum :
          (∑ a ∈ Finset.Ioc (t (i - 1)) (t i),
            ∑ b ∈ Finset.Icc a (t i),
              transitionProfileFactor σ2 Cwalk Crenewal k a b *
                stringTailScalarCost σ2 Cwalk Crenewal t rest b) =
            D ^ (rest.length + 1) * renewalStringListTailSum ϑ N
              ((t (i - 1), t i) :: rest.map fun j => (t (j - 1), t j)) k := by
        have hpair := sum_collisionTimePair_eq_conditional
          (lo := t (i - 1)) (hi := t i)
          (F := fun p => transitionProfileFactor σ2 Cwalk Crenewal k p.1 p.2 *
            stringTailScalarCost σ2 Cwalk Crenewal t rest p.2)
        have hpair' :
            (∑ a ∈ Finset.Ioc (t (i - 1)) (t i),
              ∑ b ∈ Finset.Icc a (t i),
                transitionProfileFactor σ2 Cwalk Crenewal k a b *
                  stringTailScalarCost σ2 Cwalk Crenewal t rest b) =
              ∑ a ∈ Finset.Ioc (t (i - 1)) (t i),
                ∑ b ∈ Finset.Ioc (t (i - 1)) (t i),
                  if a ≤ b then transitionProfileFactor σ2 Cwalk Crenewal k a b *
                    stringTailScalarCost σ2 Cwalk Crenewal t rest b else 0 := by
          simpa only [Prod.fst, Prod.snd] using hpair
        rw [hpair']
        simp only [renewalStringListTailSum]
        calc
          _ = ∑ a ∈ Finset.Ioc (t (i - 1)) (t i),
                ∑ b ∈ Finset.Ioc (t (i - 1)) (t i),
                  if a ≤ b then
                    D ^ (rest.length + 1) *
                      (criticalSigmaSq ϑ N *
                        Renewal.criticalRenewalMass ϑ N (b - a) *
                        ((k : ℝ) / ((a : ℝ) * ((a : ℝ) - k))) *
                        renewalStringListTailSum ϑ N
                          (rest.map fun j => (t (j - 1), t j)) b)
                  else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              by_cases hab : a ≤ b
              · simp [hab]
                have hbUpper : b ≤ t i := (Finset.mem_Ioc.mp hb).2
                have hnext := ih b
                have hfactor := transitionProfileFactor_eq_renewalScalarFactor
                  (ϑ := ϑ) (σ2 := σ2) (Cwalk := Cwalk) (Crenewal := Crenewal)
                  (N := N) (k := k) (a := a) (b := b) hσ
                simp only [D] at hfactor ⊢
                rw [hfactor, hnext]
                simp only [pow_succ]
                ring
              · simp [hab]
          _ = D ^ (rest.length + 1) *
              ∑ a ∈ Finset.Ioc (t (i - 1)) (t i),
                ∑ b ∈ Finset.Ioc (t (i - 1)) (t i),
                  if a ≤ b then
                    criticalSigmaSq ϑ N *
                      Renewal.criticalRenewalMass ϑ N (b - a) *
                      ((k : ℝ) / ((a : ℝ) * ((a : ℝ) - k))) *
                      renewalStringListTailSum ϑ N
                        (rest.map fun j => (t (j - 1), t j)) b
                  else 0 := by
              calc
                _ = ∑ a ∈ Finset.Ioc (t (i - 1)) (t i),
                      D ^ (rest.length + 1) *
                        ∑ b ∈ Finset.Ioc (t (i - 1)) (t i),
                          if a ≤ b then
                            criticalSigmaSq ϑ N *
                              Renewal.criticalRenewalMass ϑ N (b - a) *
                              ((k : ℝ) / ((a : ℝ) * ((a : ℝ) - k))) *
                              renewalStringListTailSum ϑ N
                                (rest.map fun j => (t (j - 1), t j)) b
                          else 0 := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro b hb
                  by_cases hab : a ≤ b <;> simp [hab]
                _ = _ := by rw [Finset.mul_sum]
          _ = _ := by rfl
      simpa [stringTailScalarCost, renewalStringListTailSum, D,
        List.length_cons, pow_succ] using hsum

/-- The spatial sum in the first occupied block is bounded by its scalar renewal cost and the
costs of its valid occupied tail. -/
theorem initialStringTail_le_scalarCost {c Cwalk Crenewal σ2 : ℝ}
    (hc : 0 < c) (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hkernel : ∀ n x, srwKernel n x ≤ Cwalk * Collision.hatGaussian c n x)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hvariance : ∀ k a : ℕ, 0 < k → k < a → ∀ x : Site,
      ∑' y, Collision.hatGaussian c k y *
        (srwKernel (a - k) (x - y) - srwKernel a x) ^ 2 ≤
          Cwalk * k / (a * (a - k)) * Collision.hatGaussian c a x)
    (hσ : 0 ≤ σ2) (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    (t : ℕ → ℕ) {u v : ℕ} (ht : MonotoneOn t (Set.Iic v))
    (is : List ℕ) (hidx : tailIndicesValid u v is)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbu : b ≤ t u) :
    (∑' x, ∑' y, srwKernel a x ^ 2 *
      (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
        stringTail σ2 t is b y) ≤
      (Cwalk ^ 2 * (a : ℝ)⁻¹ * Crenewal * Cwalk *
        (σ2 * (∑' z, Collision.spatialRenewal σ2 (b - a) z))) *
        stringTailScalarCost σ2 Cwalk Crenewal t is b *
          (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
  obtain ⟨hf0, hfs, hf⟩ := initialSpatialProfile_bounds hc hCwalk hCrenewal
    hkernel hconvolution hrenewal hσ hU ha hab
  let K := Cwalk ^ 2 * (a : ℝ)⁻¹ * Crenewal * Cwalk *
    (σ2 * (∑' z, Collision.spatialRenewal σ2 (b - a) z))
  have hmass : 0 ≤ ∑' z : Site, Collision.spatialRenewal σ2 (b - a) z :=
    tsum_nonneg fun z => hU (b - a) z
  have hK : 0 ≤ K := by
    dsimp [K]
    have haR : 0 < (a : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le ha)
    positivity
  have htail := stringTailProfile_le_scalarCost hc hCwalk hCrenewal
    hconvolution hrenewal hvariance hσ hU t ht is hidx b
    (le_trans ha hab) hbu K hK
    (initialSpatialProfile σ2 a b) hf0 hf hfs
  have hsupport : ∀ y, y ∉ initialSpatialProfileSupport a b →
      initialSpatialProfile σ2 a b y = 0 :=
    fun y hy => initialSpatialProfile_eq_zero_of_not_mem_support hy
  calc
    _ = stringTailProfile σ2 t is b (initialSpatialProfile σ2 a b) := by
      calc
        _ = ∑' y, initialSpatialProfile σ2 a b y * stringTail σ2 t is b y :=
          initialSpatialProfile_pairing.symm
        _ = _ := (stringTailProfile_pairing hsupport).symm
    _ ≤ _ := by simpa only [K] using htail

/-- Sum the first occupied block and a valid tail into the corresponding scalar renewal sum. -/
theorem initialStringTail_le_renewalStringListSum
    {ϑ σ2 c Cwalk Crenewal C : ℝ} {N : ℕ} {t : ℕ → ℕ} {u v : ℕ}
    (hc : 0 < c) (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hkernel : ∀ n x, srwKernel n x ≤ Cwalk * Collision.hatGaussian c n x)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hvariance : ∀ k a : ℕ, 0 < k → k < a → ∀ x : Site,
      ∑' y, Collision.hatGaussian c k y *
        (srwKernel (a - k) (x - y) - srwKernel a x) ^ 2 ≤
          Cwalk * k / (a * (a - k)) * Collision.hatGaussian c a x)
    (hσ : 0 ≤ σ2) (hσeq : σ2 = criticalSigmaSq ϑ N)
    (hcrit : 0 ≤ criticalSigmaSq ϑ N)
    (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    (hmass : ∀ n, 0 ≤ Renewal.criticalRenewalMass ϑ N n)
    (ht : MonotoneOn t (Set.Iic v)) (is : List ℕ)
    (hidx : tailIndicesValid u v is)
    (hCtrans : Cwalk ^ 2 * Crenewal ≤ C)
    (hCinitial : Cwalk ^ 3 * Crenewal *
      (1 + Real.sqrt (Real.pi / c)) ^ 2 ≤ C)
    (hCone : 1 ≤ C) :
    (∑ a ∈ Finset.Ioc (t (u - 1)) (t u),
      ∑ b ∈ Finset.Icc a (t u),
        ∑' x, ∑' y, srwKernel a x ^ 2 *
          (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
            stringTail σ2 t is b y) ≤
      C ^ (is.length + 1) * renewalStringListSum ϑ N
        ((t (u - 1), t u) :: is.map fun i => (t (i - 1), t i)) := by
  classical
  rw [hσeq]
  let cells := is.map fun i => (t (i - 1), t i)
  let D : ℝ := Cwalk ^ 2 * Crenewal
  let Cinit : ℝ := Cwalk ^ 3 * Crenewal * (1 + Real.sqrt (Real.pi / c)) ^ 2
  let F : ℕ → ℕ → ℝ := fun a b =>
    ∑' x, ∑' y, srwKernel a x ^ 2 *
      (criticalSigmaSq ϑ N * Collision.spatialRenewal (criticalSigmaSq ϑ N) (b - a) (y - x)) *
        stringTail (criticalSigmaSq ϑ N) t is b y
  let Q : ℕ → ℕ → ℝ := fun a b =>
    (a : ℝ)⁻¹ * (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a)) *
      renewalStringListTailSum ϑ N cells b
  change (∑ a ∈ Finset.Ioc (t (u - 1)) (t u),
      ∑ b ∈ Finset.Icc a (t u), F a b) ≤
    C ^ (is.length + 1) * renewalStringListSum ϑ N
      ((t (u - 1), t u) :: cells)
  have horderedTail : renewalCellsOrdered cells := by
    exact renewalCellsOrdered_map_of_tailIndicesValid ht hidx
  have hbelowEndpoint (b : ℕ) (hb : b ≤ t u) : ∀ p ∈ cells, b ≤ p.1 := by
    exact timeCell_lower_ge_of_tailIndicesValid ht hidx b hb
  have hmassEq (n : ℕ) :
      (∑' z : Site, Collision.spatialRenewal σ2 n z) =
        Renewal.criticalRenewalMass ϑ N n := by
    rw [hσeq]
    exact tsum_spatialRenewal_eq_criticalRenewalMass ϑ N n
  have htailNonneg (b : ℕ) (hb : b ≤ t u) :
      0 ≤ renewalStringListTailSum ϑ N cells b := by
    exact renewalStringListTailSum_nonneg hcrit hmass cells b
      (hbelowEndpoint b hb) horderedTail
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hCnonneg : 0 ≤ C := le_trans (by norm_num) hCone
  have hDpow : D ^ is.length ≤ C ^ is.length :=
    pow_le_pow_left₀ hDnonneg hCtrans _
  have hCcoef : Cinit * D ^ is.length ≤ C ^ (is.length + 1) := by
    calc
      Cinit * D ^ is.length ≤ C * D ^ is.length :=
        mul_le_mul_of_nonneg_right hCinitial (pow_nonneg hDnonneg _)
      _ ≤ C * C ^ is.length := mul_le_mul_of_nonneg_left hDpow hCnonneg
      _ = C ^ (is.length + 1) := by rw [pow_succ]; ring
  have hpoint (a b : ℕ) (ha : a ∈ Finset.Ioc (t (u - 1)) (t u))
      (hb : b ∈ Finset.Icc a (t u)) :
      F a b ≤ C ^ (is.length + 1) * Q a b := by
    have haLower : t (u - 1) < a := (Finset.mem_Ioc.mp ha).1
    have haOne : 1 ≤ a := by omega
    have hab : a ≤ b := (Finset.mem_Icc.mp hb).1
    have hbu : b ≤ t u := (Finset.mem_Icc.mp hb).2
    have hinit := initialStringTail_le_scalarCost hc hCwalk hCrenewal
      hkernel hconvolution hrenewal hvariance hσ hU t ht is hidx haOne hab hbu
    have hcost := stringTailScalarCost_eq_renewalStringListTailSum
      (ϑ := ϑ) (σ2 := σ2) (Cwalk := Cwalk) (Crenewal := Crenewal)
      (N := N) (t := t) hσeq is b
    rw [hmassEq (b - a), hcost, hσeq] at hinit
    have hcoefEq :
        (Cwalk ^ 2 * (a : ℝ)⁻¹ * Crenewal * Cwalk *
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a))) *
            ((Cwalk ^ 2 * Crenewal) ^ is.length *
              renewalStringListTailSum ϑ N cells b) *
                (1 + Real.sqrt (Real.pi / c)) ^ 2 =
          (Cinit * D ^ is.length) * Q a b := by
      dsimp [Cinit, D, Q, cells]
      ring
    rw [hcoefEq] at hinit
    have hbase : 0 ≤ Q a b := by
      dsimp [Q]
      have haInv : 0 ≤ (a : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      have hrenewMass : 0 ≤ criticalSigmaSq ϑ N *
          Renewal.criticalRenewalMass ϑ N (b - a) := mul_nonneg hcrit (hmass _)
      exact mul_nonneg (mul_nonneg haInv hrenewMass) (htailNonneg b hbu)
    exact hinit.trans (mul_le_mul_of_nonneg_right hCcoef hbase)
  have hpair := sum_collisionTimePair_eq_conditional
    (lo := t (u - 1)) (hi := t u)
    (F := fun p => F p.1 p.2)
  have hpair' :
      (∑ a ∈ Finset.Ioc (t (u - 1)) (t u),
        ∑ b ∈ Finset.Icc a (t u), F a b) =
        ∑ a ∈ Finset.Ioc (t (u - 1)) (t u),
          ∑ b ∈ Finset.Ioc (t (u - 1)) (t u),
            if a ≤ b then F a b else 0 := by
    simpa only [Prod.fst, Prod.snd] using hpair
  rw [hpair']
  calc
    _ ≤ ∑ a ∈ Finset.Ioc (t (u - 1)) (t u),
          ∑ b ∈ Finset.Ioc (t (u - 1)) (t u),
            if a ≤ b then C ^ (is.length + 1) * Q a b else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases hab : a ≤ b
      · simp [hab]
        exact hpoint a b ha (Finset.mem_Icc.mpr ⟨hab, (Finset.mem_Ioc.mp hb).2⟩)
      · simp [hab]
    _ = C ^ (is.length + 1) * renewalStringListSum ϑ N
          ((t (u - 1), t u) :: cells) := by
      simp only [renewalStringListSum, Q]
      calc
        _ = ∑ a ∈ Finset.Ioc (t (u - 1)) (t u),
              C ^ (is.length + 1) *
                ∑ b ∈ Finset.Ioc (t (u - 1)) (t u),
                  if a ≤ b then
                    (a : ℝ)⁻¹ *
                      (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a)) *
                        renewalStringListTailSum ϑ N cells b
                  else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hab : a ≤ b <;> simp [hab]
        _ = _ := by rw [Finset.mul_sum]

/-- Bound the closed discrepancy-string chaos sum by the renewal-string sums. -/
theorem closedStringSum_le_renewalStringSum (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (t : ℕ → ℕ) (u v : ℕ),
        MonotoneOn t (Set.Iic v) → t v ≤ N → 1 ≤ u → u < v →
          closedStringSum (Polymer.sigmaSq (criticalBeta ϑ N)) t u v ≤
            ∑ S ∈ (Finset.Ioo u v).powerset, C ^ (S.card + 2) *
              renewalStringSum ϑ N (S.card + 1) (occupiedLo t u v S) (occupiedHi t u v S) := by
  obtain ⟨c, hc, hgaussian⟩ := exists_stringGaussian_bounds
  obtain ⟨Cwalk, Crenewal, hCwalk, hCrenewal, _, _, hkernel, hconvolution,
      hvariance, hrenewal₀⟩ := hgaussian c hc (le_rfl)
  have hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x := by
    intro σ hσ n hn x
    exact spatialRenewal_le_hatGaussian_all hCrenewal hrenewal₀ σ hσ n x
  let D : ℝ := Cwalk ^ 2 * Crenewal
  let Cinit : ℝ := Cwalk ^ 3 * Crenewal * (1 + Real.sqrt (Real.pi / c)) ^ 2
  let C : ℝ := max D Cinit
  have hCwalkSq : 1 ≤ Cwalk ^ 2 := by nlinarith only [hCwalk]
  have hD : 1 ≤ D := by
    dsimp [D]
    calc
      1 ≤ Cwalk ^ 2 := hCwalkSq
      _ = Cwalk ^ 2 * 1 := by ring
      _ ≤ Cwalk ^ 2 * Crenewal :=
        mul_le_mul_of_nonneg_left hCrenewal (sq_nonneg Cwalk)
  have hCone : 1 ≤ C := le_trans hD (le_max_left D Cinit)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hCone
  have hCtrans : Cwalk ^ 2 * Crenewal ≤ C := le_max_left D Cinit
  have hCinitial : Cwalk ^ 3 * Crenewal *
      (1 + Real.sqrt (Real.pi / c)) ^ 2 ≤ C := le_max_right D Cinit
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [eventually_sigmaSq_criticalBeta_eq A] with N hσEventually
  intro ϑ hϑ t u v ht htv hu huv
  have hσeq : Polymer.sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N :=
    hσEventually ϑ hϑ
  have hσ : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ N) := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have hcrit : 0 ≤ criticalSigmaSq ϑ N := by rw [← hσeq]; exact hσ
  have hU : ∀ n x, 0 ≤ Collision.spatialRenewal
      (Polymer.sigmaSq (criticalBeta ϑ N)) n x := by
    intro n x
    rw [hσeq]
    exact spatialRenewal_nonneg hcrit n x
  have hmass : ∀ n, 0 ≤ Renewal.criticalRenewalMass ϑ N n := by
    intro n
    rw [Renewal.criticalRenewalMass]
    apply Renewal.renewalMass_nonneg
    intro r
    exact mul_nonneg hcrit (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
  classical
  unfold closedStringSum
  apply Finset.sum_le_sum
  intro S hS
  have hSsubset : S ⊆ Finset.Ioo u v := Finset.mem_powerset.mp hS
  let is := S.sort (· ≤ ·) ++ [v]
  have hidx : tailIndicesValid u v is := by
    dsimp [is]
    exact tailIndicesValid_sorted_occupied huv hSsubset
  have htailCells : is.map (fun i => (t (i - 1), t i)) =
      (S.sort (· ≤ ·) ++ [v]).map (fun i => (t (i - 1), t i)) := rfl
  have hfirstBound := initialStringTail_le_renewalStringListSum
    (ϑ := ϑ) (σ2 := Polymer.sigmaSq (criticalBeta ϑ N)) (c := c)
    (Cwalk := Cwalk) (Crenewal := Crenewal) (C := C) (N := N)
    (t := t) (u := u) (v := v) hc hCwalk hCrenewal hkernel hconvolution
    hrenewal hvariance hσ hσeq hcrit hU hmass ht is hidx hCtrans hCinitial hCone
  have hscalarEq :
      renewalStringSum ϑ N (S.card + 1) (occupiedLo t u v S) (occupiedHi t u v S) =
        renewalStringListSum ϑ N ((t (u - 1), t u) :: is.map
          (fun i => (t (i - 1), t i))) := by
    rw [renewalStringSum_eq_list]
    rw [occupiedCells_ofFn_eq_list]
  have hlength : is.length + 1 = S.card + 2 := by
    simp [is, Finset.length_sort]
  rw [hscalarEq, ← hlength]
  simpa only [is] using hfirstBound

end Critical2DKPZ.Blocks

end
