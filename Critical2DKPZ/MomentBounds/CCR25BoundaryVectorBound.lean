/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.AiiKBoundaryConvolution
public import Critical2DKPZ.MomentBounds.PairSelection
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Boundary-vector bounds for CCR25 moment operators -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem finiteLpNorm_add_le {α : Type*} (s : Finset α) {p : ℝ}
    (hp : 1 ≤ p) (f g : α → ℝ) :
    finiteLpNorm s p (fun x => f x + g x) ≤
      finiteLpNorm s p f + finiteLpNorm s p g := by
  simpa [finiteLpNorm] using
    (Real.Lp_add_le (s := s) (f := f) (g := g) hp)


/-- Minkowski inequality for a finite sum of functions in the finite `ℓᵖ` norm, `1 ≤ p`. -/
theorem finiteLpNorm_sum_le {α β : Type*} [DecidableEq α]
    (s : Finset α) (u : Finset β) {p : ℝ} (hp : 1 ≤ p) (f : α → β → ℝ) :
    finiteLpNorm u p (fun x => ∑ i ∈ s, f i x) ≤
      ∑ i ∈ s, finiteLpNorm u p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
      have hpInv : 0 < 1 / p := one_div_pos.mpr hp0
      change (∑ x ∈ u, |(0 : ℝ)| ^ p) ^ (1 / p) ≤ 0
      have hsum0 : (∑ x ∈ u, |(0 : ℝ)| ^ p) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [abs_zero, Real.zero_rpow hp0.ne']
      rw [hsum0, Real.zero_rpow hpInv.ne']
  | @insert a s has ih =>
      have hsum : (fun x => ∑ i ∈ insert a s, f i x) =
          fun x => f a x + ∑ i ∈ s, f i x := by
        funext x
        rw [Finset.sum_insert has]
      rw [hsum]
      calc
        finiteLpNorm u p (fun x => f a x + ∑ i ∈ s, f i x) ≤
            finiteLpNorm u p (f a) +
              finiteLpNorm u p (fun x => ∑ i ∈ s, f i x) :=
          finiteLpNorm_add_le u hp (f a) (fun x => ∑ i ∈ s, f i x)
        _ ≤ finiteLpNorm u p (f a) + ∑ i ∈ s, finiteLpNorm u p (f i) := by
          simpa [add_comm] using add_le_add_left ih (finiteLpNorm u p (f a))
        _ = ∑ i ∈ insert a s, finiteLpNorm u p (f i) := by
          rw [Finset.sum_insert has]


/-- The finite `ℓᵖ` norm depends only on the absolute values on the index set. -/
theorem finiteLpNorm_abs_congr {α : Type*} (s : Finset α) (p : ℝ)
    (f g : α → ℝ) (h : ∀ x ∈ s, |f x| = |g x|) :
    finiteLpNorm s p f = finiteLpNorm s p g := by
  unfold finiteLpNorm
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x hx]

private theorem finiteLpNorm_zeroExtend_eq {α : Type*} [DecidableEq α]
    (s u : Finset α) (hsu : s ⊆ u) {p : ℝ} (hp : 0 < p) (f : α → ℝ) :
    finiteLpNorm u p (fun x => if x ∈ s then f x else 0) = finiteLpNorm s p f := by
  unfold finiteLpNorm
  congr 1
  have hsum :
      (∑ x ∈ u, |(if x ∈ s then f x else 0 : ℝ)| ^ p) =
        ∑ x ∈ s, |f x| ^ p := by
    calc
      (∑ x ∈ u, |(if x ∈ s then f x else 0 : ℝ)| ^ p) =
          ∑ x ∈ u, if x ∈ s then |f x| ^ p else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxs : x ∈ s
        · simp [hxs]
        · simp [hxs, Real.zero_rpow hp.ne']
      _ = ∑ x ∈ s, if x ∈ s then |f x| ^ p else 0 :=
        (Finset.sum_subset hsu (by intro x hxU hxs; simp [hxs])).symm
      _ = ∑ x ∈ s, |f x| ^ p := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hx]
  exact hsum

private theorem finiteLpNorm_one_eq_sum_of_nonneg {α : Type*} (s : Finset α)
    (f : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    finiteLpNorm s 1 f = ∑ x ∈ s, f x := by
  unfold finiteLpNorm
  rw [one_div_one, Real.rpow_one]
  apply Finset.sum_congr rfl
  intro x hx
  rw [abs_of_nonneg (hf x hx), Real.rpow_one]

/-- For `p ≥ 1`, the finite `ℓᵖ` norm of a nonnegative function is at most its sum. -/
theorem finiteLpNorm_nonneg_le_sum {α : Type*} (s : Finset α) {p : ℝ}
    (hp : 1 ≤ p) (f : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    finiteLpNorm s p f ≤ ∑ x ∈ s, f x := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have he : 0 ≤ p - 1 := by linarith
  let B : ℝ := ∑ x ∈ s, f x
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun x hx => hf x hx
  have hterm (x : α) (hx : x ∈ s) : f x ^ p ≤ B ^ (p - 1) * f x := by
    have hsingle : f x ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (fun y hy => hf y hy) hx
    have hpow : f x ^ (p - 1) ≤ B ^ (p - 1) :=
      Real.rpow_le_rpow (hf x hx) hsingle he
    calc
      f x ^ p = f x ^ (1 + (p - 1)) := by congr 1; ring
      _ = f x ^ 1 * f x ^ (p - 1) :=
        Real.rpow_add_of_nonneg (hf x hx) zero_le_one he
      _ = f x * f x ^ (p - 1) := by rw [Real.rpow_one]
      _ ≤ f x * B ^ (p - 1) := mul_le_mul_of_nonneg_left hpow (hf x hx)
      _ = B ^ (p - 1) * f x := by ring
  have hsum : (∑ x ∈ s, |f x| ^ p) ≤ B ^ p := by
    calc
      _ = ∑ x ∈ s, f x ^ p := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_of_nonneg (hf x hx)]
      _ ≤ ∑ x ∈ s, B ^ (p - 1) * f x :=
        Finset.sum_le_sum fun x hx => hterm x hx
      _ = B ^ (p - 1) * B := by
        dsimp [B]
        rw [← Finset.mul_sum]
      _ = B ^ p := by
        calc
          B ^ (p - 1) * B = B ^ (p - 1) * B ^ 1 := by rw [Real.rpow_one]
          _ = B ^ ((p - 1) + 1) :=
            (Real.rpow_add_of_nonneg hB he zero_le_one).symm
          _ = B ^ p := by congr 1; ring
  unfold finiteLpNorm
  calc
    (∑ x ∈ s, |f x| ^ p) ^ (1 / p) ≤ (B ^ p) ^ (1 / p) :=
      Real.rpow_le_rpow
        (Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _)
        hsum (one_div_nonneg.mpr hp0.le)
    _ = B := by
      rw [← Real.rpow_mul hB]
      have hpow : p * (1 / p) = 1 := by field_simp [ne_of_gt hp0]
      rw [hpow, Real.rpow_one]

/-- A function with vanishing finite `ℓᵖ` norm vanishes at every point of the index set. -/
theorem finiteLpNorm_eq_zero_forces_zero {α : Type*} (s : Finset α)
    {p : ℝ} (f : α → ℝ)
    (hzero : finiteLpNorm s p f = 0) (x : α) (hx : x ∈ s) : f x = 0 := by
  by_contra hne
  have hterm : 0 < |f x| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hne) _
  have hsum : 0 < ∑ y ∈ s, |f y| ^ p := by
    exact lt_of_lt_of_le hterm <| Finset.single_le_sum
      (fun y hy => Real.rpow_nonneg (abs_nonneg _) _) hx
  have hnorm : 0 < (∑ y ∈ s, |f y| ^ p) ^ (1 / p) :=
    Real.rpow_pos_of_pos hsum _
  unfold finiteLpNorm at hzero
  rw [hzero] at hnorm
  exact (lt_irrefl 0 hnorm)

private noncomputable def weightedBoundaryOneReplica (t : ℝ) (n : ℕ) (A : Finset Site)
    (f : Site → ℝ) (y : Site) : ℝ :=
  |finiteBoundaryConvolution n A f y| * Real.exp (t * ‖siteToPlane y‖)

private theorem replicaExponentialWeight_inv {h : ℕ} (t : ℝ)
    (x : LatticeConfiguration h) :
    (replicaExponentialWeight t x)⁻¹ =
      ∏ i : Fin h, Real.exp (t * ‖siteToPlane (x i)‖) := by
  unfold replicaExponentialWeight
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show -t * ‖siteToPlane (x i)‖ =
      -(t * ‖siteToPlane (x i)‖) by ring, Real.exp_neg, inv_inv]

private theorem replicaBoundaryVector_weighted_abs_eq_of_collision {h : ℕ} (t : ℝ) (n : ℕ)
    (I : ReplicaPartition h) (A : Finset Site) (f : Site → ℝ)
    (x : LatticeConfiguration h) (hc : IsCollisionConfiguration I x) :
    |replicaBoundaryVector n I A f x / replicaExponentialWeight t x| =
      ∏ i : Fin h, weightedBoundaryOneReplica t n A f (x i) := by
  classical
  simp only [replicaBoundaryVector, ite_eq_left hc]
  have hprod :
      (∏ i : Fin h, finiteBoundaryConvolution n A f (x i)) /
          replicaExponentialWeight t x =
        ∏ i : Fin h,
          (finiteBoundaryConvolution n A f (x i) *
            Real.exp (t * ‖siteToPlane (x i)‖)) := by
    calc
      _ = (∏ i : Fin h, finiteBoundaryConvolution n A f (x i)) *
          (replicaExponentialWeight t x)⁻¹ := by rw [div_eq_mul_inv]
      _ = (∏ i : Fin h, finiteBoundaryConvolution n A f (x i)) *
          (∏ i : Fin h, Real.exp (t * ‖siteToPlane (x i)‖)) := by
        rw [replicaExponentialWeight_inv]
      _ = ∏ i : Fin h,
          (finiteBoundaryConvolution n A f (x i) *
            Real.exp (t * ‖siteToPlane (x i)‖)) := by
        rw [← Finset.prod_mul_distrib]
  rw [hprod, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp [weightedBoundaryOneReplica, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- For `p > 1`, `∑_{n<N} (n+1)^(-1/p) ≤ p/(p-1) · N^(1-1/p)`. -/
theorem sum_shift_rpow_inv_le {p : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑ n ∈ Finset.range N, (n + 1 : ℝ) ^ (-1 / p)) ≤
      p / (p - 1) * (N : ℝ) ^ (1 - 1 / p) := by
  classical
  let α : ℝ := 1 / p
  let δ : ℝ := 1 - α
  let f : ℝ → ℝ := fun x => x ^ (-α)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hαlt : α < 1 := by
    dsimp [α]
    rw [div_lt_one hp0]
    exact hp
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hδle : δ ≤ 1 := by dsimp [δ]; linarith
  by_cases hN0 : N = 0
  · have hδ' : 0 < 1 - 1 / p := by simpa [δ, α] using hδpos
    simp [hN0]
    positivity
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hf : AntitoneOn f (Set.Icc (1 : ℝ) N) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    exact Real.rpow_le_rpow_of_nonpos hxpos hxy (by dsimp [α]; linarith)
  have hsumI :
      (∑ k ∈ Finset.Ico 1 N, f (k + 1 : ℕ)) ≤ ∫ x in (1 : ℝ)..N, f x := by
    have hf' : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
      simpa using hf
    simpa using AntitoneOn.sum_le_integral_Ico (by omega) hf'
  have hInt : (∫ x in (1 : ℝ)..N, f x) = ((N : ℝ) ^ δ - 1) / δ := by
    rw [show f = (fun x : ℝ => x ^ (-α)) by rfl,
      integral_rpow (a := (1 : ℝ)) (b := (N : ℝ))
        (r := -α) (Or.inl (by dsimp [α]; linarith))]
    rw [show -α + 1 = δ by dsimp [δ]; ring, Real.one_rpow]
  have hdecomp : Finset.range N = insert 0 (Finset.Ico 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hsum :
      (∑ n ∈ Finset.range N, (n + 1 : ℝ) ^ (-1 / p)) =
        1 + ∑ k ∈ Finset.Ico 1 N, f (k + 1 : ℕ) := by
    rw [hdecomp, Finset.sum_insert (by simp)]
    simp only [Nat.cast_zero, zero_add, Real.one_rpow]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    change ((k : ℝ) + 1) ^ (-1 / p) = ((k + 1 : ℕ) : ℝ) ^ (-α)
    rw [Nat.cast_add, Nat.cast_one]
    congr 1
    dsimp [α]
    ring
  have hq : 1 / δ = p / (p - 1) := by
    dsimp [δ, α]
    field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp)]
  have hq1 : 1 ≤ p / (p - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hp)]
    linarith
  have hpow : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (by positivity) _
  calc
    _ = 1 + ∑ k ∈ Finset.Ico 1 N, f (k + 1 : ℕ) := hsum
    _ ≤ 1 + ((N : ℝ) ^ δ - 1) / δ := by
      rw [← hInt]
      simpa [add_comm] using add_le_add_left hsumI (1 : ℝ)
    _ = (p / (p - 1)) * (N : ℝ) ^ δ + (1 - p / (p - 1)) := by
      rw [div_eq_mul_inv, ← hq]
      ring
    _ ≤ (p / (p - 1)) * (N : ℝ) ^ δ := by nlinarith [hpow, hq1]

/-- For `p > 1` and `1 ≤ N ≤ L`, `∑_{N≤n<L} (n+1)^(-(2-1/p)) ≤ p/(p-1) · N^(-(1-1/p))`. -/
theorem sum_shift_rpow_tail_le {p : ℝ} (hp : 1 < p) (N L : ℕ)
    (hN : 1 ≤ N) (hNL : N ≤ L) :
    (∑ n ∈ Finset.Ico N L, (n + 1 : ℝ) ^ (-(2 - 1 / p))) ≤
      p / (p - 1) * (N : ℝ) ^ (-(1 - 1 / p)) := by
  classical
  let β : ℝ := 2 - 1 / p
  let δ : ℝ := 1 - 1 / p
  let f : ℝ → ℝ := fun x => x ^ (-β)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hδpos : 0 < δ := by
    have hInv : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
    dsimp [δ]
    linarith
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hLreal : (N : ℝ) ≤ L := by exact_mod_cast hNL
  have hf : AntitoneOn f (Set.Icc (N : ℝ) (L : ℝ)) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le (by exact_mod_cast hN) hx.1
    exact Real.rpow_le_rpow_of_nonpos hxpos hxy (by dsimp [β]; linarith)
  have hsumI :
      (∑ n ∈ Finset.Ico N L, f (n + 1 : ℕ)) ≤ ∫ x in (N : ℝ)..L, f x := by
    simpa using AntitoneOn.sum_le_integral_Ico hNL hf
  have hInt : (∫ x in (N : ℝ)..L, f x) =
      ((L : ℝ) ^ (-δ) - (N : ℝ) ^ (-δ)) / (-δ) := by
    rw [show f = (fun x : ℝ => x ^ (-β)) by rfl,
      integral_rpow (a := (N : ℝ)) (b := (L : ℝ))
        (r := -β) (Or.inr ⟨by dsimp [β]; linarith, by
          have hzero : (0 : ℝ) ∉ Set.uIcc (N : ℝ) (L : ℝ) := by
            intro hz
            rw [Set.uIcc_of_le hLreal, Set.mem_Icc] at hz
            linarith
          exact hzero⟩)]
    rw [show -β + 1 = -δ by dsimp [β, δ]; ring]
  have hq : 1 / δ = p / (p - 1) := by
    dsimp [δ]
    field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp)]
  have hLpow : 0 ≤ (L : ℝ) ^ (-δ) := Real.rpow_nonneg (by positivity) _
  have hNpow : 0 ≤ (N : ℝ) ^ (-δ) := Real.rpow_nonneg (by positivity) _
  have hqpos : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  have hIntBound :
      (∫ x in (N : ℝ)..L, f x) ≤ (p / (p - 1)) * (N : ℝ) ^ (-δ) := by
    rw [hInt]
    have hrewrite :
        ((L : ℝ) ^ (-δ) - (N : ℝ) ^ (-δ)) / (-δ) =
          (1 / δ) * ((N : ℝ) ^ (-δ) - (L : ℝ) ^ (-δ)) := by
      field_simp [ne_of_gt hδpos]
      ring
    rw [hrewrite, hq]
    nlinarith [mul_nonneg hqpos.le hLpow]
  have hsumCast :
      (∑ n ∈ Finset.Ico N L, f (n + 1 : ℕ)) =
        ∑ n ∈ Finset.Ico N L, (n + 1 : ℝ) ^ (-(2 - 1 / p)) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [f, β]
  rw [← hsumCast]
  exact hsumI.trans hIntBound

private theorem finiteLpNorm_replicaProduct_le_of_pair {h : ℕ} (hh : 2 ≤ h)
    (s : Finset (LatticeConfiguration h)) (a b : Fin h) (hab : a ≠ b)
    (hpair : ∀ x ∈ s, x a = x b) {p : ℝ} (hp : 1 ≤ p)
    (U : Finset Site) (hcoords : ∀ x ∈ s, ∀ i, x i ∈ U)
    (u : Site → ℝ) (hu : ∀ y ∈ U, 0 ≤ u y)
    (Mshort Mtail : ℝ) (hMshort : 0 ≤ Mshort) (hSupShort : ∀ y ∈ U, u y ≤ Mshort)
    (hMtail : 0 ≤ Mtail) (hSupTail : ∀ y ∈ U, u y ≤ Mtail) (S : ℝ)
    (hS : 0 ≤ S) (hSum : (∑ y ∈ U, u y) ≤ S) :
    finiteLpNorm s p (fun x => ∏ i : Fin h, u (x i)) ≤
        Mshort * finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2) ∧
      finiteLpNorm s p (fun x => ∏ i : Fin h, u (x i)) ≤
        Mtail ^ (2 - 1 / p) * S ^ (1 / p) * finiteLpNorm U p u ^ (h - 2) := by
  classical
  let E : Type := {i : Fin h // i ≠ b}
  let ea : E := ⟨a, hab⟩
  let drop : LatticeConfiguration h → E → Site := fun x i => x i.1
  let T : Finset (E → Site) := s.image drop
  let D : Finset (E → Site) := Fintype.piFinset fun _ : E => U
  let R : Finset E := Finset.univ.erase ea
  let g : E → Site → ℝ := fun i y => if i = ea then u y ^ 2 else u y
  let G : (E → Site) → ℝ := fun y => ∏ i : E, g i (y i)
  have hdrop : Set.InjOn drop s := by
    intro x hx y hy hxy
    funext i
    by_cases hib : i = b
    · subst i
      calc
        x b = x a := (hpair x hx).symm
        _ = y a := congrFun hxy ea
        _ = y b := hpair y hy
    · exact congrFun hxy ⟨i, hib⟩
  have hT : T ⊆ D := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Fintype.mem_piFinset.mpr fun i => hcoords x hx i.1
  have hRcard : R.card = h - 2 := by
    have hEcard : Fintype.card E = h - 1 := by
      dsimp [E]
      simp [Fintype.card_subtype_compl]
    have hR : R.card = Fintype.card E - 1 := by
      simp [R]
    omega
  have hprodDrop (x : LatticeConfiguration h) (hx : x a = x b) :
      (∏ i : Fin h, u (x i)) = G (drop x) := by
    have haerase : a ∈ (Finset.univ.erase b) := by
      simp [hab]
    have hprod1 :
        (∏ i : Fin h, u (x i)) =
          (∏ i ∈ Finset.univ.erase b, u (x i)) * u (x b) := by
      symm
      exact Finset.prod_erase_mul Finset.univ (fun i => u (x i)) (Finset.mem_univ b)
    have hprod2 :
        (∏ i ∈ Finset.univ.erase b, u (x i)) =
          (∏ i ∈ (Finset.univ.erase b).erase a, u (x i)) * u (x a) := by
      symm
      exact Finset.prod_erase_mul (Finset.univ.erase b) (fun i => u (x i)) haerase
    have hindex :
        (∏ i ∈ (Finset.univ.erase b).erase a, u (x i)) =
          ∏ i ∈ R, u (x i.1) := by
      apply Finset.prod_bij (fun i hi => ⟨i, by
        have hi' : i ≠ a ∧ i ≠ b := by simpa using hi
        exact hi'.2⟩)
      · intro i hi
        have hi' : i ≠ a ∧ i ≠ b := by simpa using hi
        change (⟨i, hi'.2⟩ : E) ∈ R
        simp only [R, Finset.mem_erase, Finset.mem_univ]
        exact ⟨by
          intro heq
          apply hi'.1
          exact congrArg Subtype.val heq, trivial⟩
      · intro i hi j hj hij
        exact congrArg Subtype.val hij
      · intro j hj
        have hjne : j ≠ ea := (Finset.mem_erase.mp hj).1
        have hja : j.1 ≠ a := by
          intro heq
          apply hjne
          exact Subtype.ext heq
        refine ⟨j.1, ?_, ?_⟩
        · simp [hja, j.2]
        · exact Subtype.ext rfl
      · intro i hi
        rfl
    have hGerase :
        (∏ i ∈ Finset.univ.erase ea, g i (drop x i)) =
          ∏ i ∈ R, u (x i.1) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hie : i ≠ ea := (Finset.mem_erase.mp hi).1
      simp [g, drop, hie]
    have hGfactor :
        G (drop x) = (∏ i ∈ R, u (x i.1)) * u (x a) ^ 2 := by
      calc
        G (drop x) =
            (∏ i ∈ Finset.univ.erase ea, g i (drop x i)) * g ea (drop x ea) := by
          dsimp [G]
          rw [← Finset.prod_erase_mul Finset.univ
            (fun i : E => g i (drop x i)) (Finset.mem_univ ea)]
        _ = (∏ i ∈ R, u (x i.1)) * u (x a) ^ 2 := by
          rw [hGerase]
          simp [g, drop, ea]
    rw [hprod1, hprod2, hindex, hGfactor, hx]
    ring
  have hGnonneg (y : E → Site) (hy : y ∈ D) : 0 ≤ G y := by
    apply Finset.prod_nonneg
    intro i hi
    dsimp [g]
    split_ifs with hie
    · exact sq_nonneg (u (y i))
    · exact hu (y i) (Fintype.mem_piFinset.mp hy i)
  have hGpow (y : E → Site) (hy : y ∈ D) :
      |G y| ^ p = ∏ i : E, (g i (y i)) ^ p := by
    rw [abs_of_nonneg (hGnonneg y hy), ← Real.finsetProd_rpow Finset.univ
      (fun i => g i (y i)) (fun i hi => by
        dsimp [g]
        split_ifs with hie
        · exact sq_nonneg (u (y i))
        · exact hu (y i) (Fintype.mem_piFinset.mp hy i))]
  have hGpowEq (x : LatticeConfiguration h) (hx : x ∈ s) :
      |(∏ i : Fin h, u (x i))| ^ p = |G (drop x)| ^ p := by
    rw [hprodDrop x (hpair x hx)]
  have hsumImage :
      (∑ x ∈ s, |(∏ i : Fin h, u (x i))| ^ p) =
        ∑ y ∈ T, |G y| ^ p := by
    rw [Finset.sum_image hdrop]
    apply Finset.sum_congr rfl
    intro x hx
    exact hGpowEq x hx
  have hsumSubset :
      (∑ y ∈ T, |G y| ^ p) ≤ ∑ y ∈ D, |G y| ^ p :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun y hyD hyT => Real.rpow_nonneg (abs_nonneg _) _)
  let S1 : ℝ := ∑ y ∈ U, u y ^ p
  let S2 : ℝ := ∑ y ∈ U, u y ^ (2 * p)
  have hS1 : 0 ≤ S1 := by
    dsimp [S1]
    exact Finset.sum_nonneg fun y hy => Real.rpow_nonneg (hu y hy) _
  have hS2 : 0 ≤ S2 := by
    dsimp [S2]
    exact Finset.sum_nonneg fun y hy => Real.rpow_nonneg (hu y hy) _
  have hsumD : (∑ y ∈ D, |G y| ^ p) = S2 * S1 ^ (h - 2) := by
    calc
      (∑ y ∈ D, |G y| ^ p) =
          ∑ y ∈ D, ∏ i : E, (g i (y i)) ^ p := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hGpow y hy
      _ = ∏ i : E, ∑ z ∈ U, (g i z) ^ p := by
            simpa [D] using
              (Finset.sum_prod_piFinset U (fun i (z : Site) => (g i z) ^ p))
      _ = S2 * S1 ^ (h - 2) := by
            have hprod :
                (∏ i : E, ∑ z ∈ U, (g i z) ^ p) =
                  S2 * ∏ i ∈ R, S1 := by
              have hea : (∑ z ∈ U, (g ea z) ^ p) = S2 := by
                apply Finset.sum_congr rfl
                intro z hz
                have hg : g ea z = u z ^ 2 := by simp [g, ea]
                have hnat : (u z) ^ (2 : ℕ) = (u z) ^ (2 : ℝ) := by
                  exact (Real.rpow_natCast (u z) 2).symm
                calc
                  (g ea z) ^ p = ((u z) ^ (2 : ℝ)) ^ p := by rw [hg, hnat]
                  _ = (u z) ^ ((2 : ℝ) * p) :=
                    (Real.rpow_mul (hu z hz) (2 : ℝ) p).symm
              have hR :
                  (∏ i ∈ Finset.univ.erase ea, ∑ z ∈ U, (g i z) ^ p) =
                    ∏ i ∈ R, S1 := by
                apply Finset.prod_congr rfl
                intro i hi
                have hie : i ≠ ea := (Finset.mem_erase.mp hi).1
                calc
                  (∑ z ∈ U, (g i z) ^ p) = ∑ z ∈ U, u z ^ p := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    simp [g, hie]
                  _ = S1 := rfl
              calc
                _ = (∏ i ∈ Finset.univ.erase ea, ∑ z ∈ U, (g i z) ^ p) *
                    (∑ z ∈ U, (g ea z) ^ p) := by
                  rw [← Finset.prod_erase_mul Finset.univ
                    (fun i : E => ∑ z ∈ U, (g i z) ^ p) (Finset.mem_univ ea)]
                _ = (∏ i ∈ R, S1) * S2 := by rw [hR, hea]
                _ = S2 * ∏ i ∈ R, S1 := by ring
            rw [hprod, Finset.prod_const, hRcard]
  have hS2le : S2 ≤ Mshort ^ p * S1 := by
    dsimp [S2, S1]
    calc
      _ ≤ ∑ y ∈ U, Mshort ^ p * u y ^ p := by
        apply Finset.sum_le_sum
        intro y hy
        have hpow : u y ^ p ≤ Mshort ^ p :=
          Real.rpow_le_rpow (hu y hy) (hSupShort y hy) (le_trans zero_le_one hp)
        rw [show u y ^ (2 * p) = u y ^ p * u y ^ p by
          calc
            u y ^ (2 * p) = u y ^ (p + p) := by congr 1; ring
            _ = u y ^ p * u y ^ p :=
              Real.rpow_add_of_nonneg (hu y hy)
                (le_trans zero_le_one hp) (le_trans zero_le_one hp)]
        exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (hu y hy) _)
      _ = Mshort ^ p * ∑ y ∈ U, u y ^ p := by rw [Finset.mul_sum]
  have hβ : 0 ≤ 2 * p - 1 := by nlinarith [hp]
  have hS2leTail : S2 ≤ Mtail ^ (2 * p - 1) * S := by
    dsimp [S2]
    calc
      _ ≤ ∑ y ∈ U, u y * Mtail ^ (2 * p - 1) := by
        apply Finset.sum_le_sum
        intro y hy
        have huExp : u y ^ (2 * p) =
            u y * u y ^ (2 * p - 1) := by
          calc
            u y ^ (2 * p) = u y ^ (1 + (2 * p - 1)) := by
              congr 1
              ring
            _ = u y ^ 1 * u y ^ (2 * p - 1) :=
              Real.rpow_add_of_nonneg (hu y hy) zero_le_one hβ
            _ = u y * u y ^ (2 * p - 1) := by rw [Real.rpow_one]
        rw [huExp]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hu y hy) (hSupTail y hy) hβ) (hu y hy)
      _ = (∑ y ∈ U, u y) * Mtail ^ (2 * p - 1) := by
        rw [Finset.sum_mul]
      _ = Mtail ^ (2 * p - 1) * (∑ y ∈ U, u y) := by ring
      _ ≤ Mtail ^ (2 * p - 1) * S :=
        mul_le_mul_of_nonneg_left hSum (Real.rpow_nonneg hMtail _)
  have hsumBound :
      (∑ x ∈ s, |(∏ i : Fin h, u (x i))| ^ p) ≤ Mshort ^ p * S1 ^ (h - 1) := by
    rw [hsumImage]
    calc
      _ ≤ ∑ y ∈ D, |G y| ^ p := hsumSubset
      _ = S2 * S1 ^ (h - 2) := hsumD
      _ ≤ (Mshort ^ p * S1) * S1 ^ (h - 2) :=
        mul_le_mul_of_nonneg_right hS2le (pow_nonneg hS1 _)
      _ = Mshort ^ p * S1 ^ (h - 1) := by
        have hn : h - 1 = h - 2 + 1 := by omega
        rw [hn, pow_succ]
        ring
  have hnorm : finiteLpNorm U p u = S1 ^ (1 / p) := by
    unfold finiteLpNorm
    congr 1
    dsimp [S1]
    apply Finset.sum_congr rfl
    intro y hy
    rw [abs_of_nonneg (hu y hy)]
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpowM : (Mshort ^ p * S1 ^ (h - 1)) ^ (1 / p) =
      Mshort * (S1 ^ (1 / p)) ^ (h - 1) := by
    calc
      _ = (Mshort ^ p) ^ (1 / p) * (S1 ^ (h - 1)) ^ (1 / p) :=
        Real.mul_rpow (Real.rpow_nonneg hMshort _) (pow_nonneg hS1 _)
      _ = Mshort * (S1 ^ (1 / p)) ^ (h - 1) := by
        rw [← Real.rpow_mul hMshort]
        have hMexp : p * (1 / p) = 1 := by field_simp [ne_of_gt hp0]
        rw [hMexp, Real.rpow_one, ← Real.rpow_natCast_mul hS1 (h - 1) (1 / p)]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hS1]
        congr 2
        ring
  have hpowSplit :
      Mshort * (S1 ^ (1 / p)) ^ (h - 1) =
        Mshort * S1 ^ (1 / p) * (S1 ^ (1 / p)) ^ (h - 2) := by
    have hn : h - 1 = h - 2 + 1 := by omega
    rw [hn, pow_succ]
    ring
  have hshort : finiteLpNorm s p (fun x => ∏ i : Fin h, u (x i)) ≤
      Mshort * finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2) := by
    change (∑ x ∈ s, |(∏ i : Fin h, u (x i))| ^ p) ^ (1 / p) ≤
      Mshort * finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2)
    calc
      _ ≤ (Mshort ^ p * S1 ^ (h - 1)) ^ (1 / p) := Real.rpow_le_rpow
        (Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _)
        hsumBound (one_div_nonneg.mpr (le_trans zero_le_one hp))
      _ = Mshort * finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2) := by
        rw [hpowM, hpowSplit, ← hnorm]
  have hpowTail :
      (Mtail ^ (2 * p - 1) * S * S1 ^ (h - 2)) ^ (1 / p) =
        Mtail ^ (2 - 1 / p) * S ^ (1 / p) *
          (S1 ^ (1 / p)) ^ (h - 2) := by
    have hMpow : (Mtail ^ (2 * p - 1)) ^ (1 / p) = Mtail ^ (2 - 1 / p) := by
      rw [← Real.rpow_mul hMtail]
      congr 1
      field_simp [ne_of_gt hp0]
    have hS1pow : (S1 ^ (h - 2)) ^ (1 / p) =
        (S1 ^ (1 / p)) ^ (h - 2) := by
      calc
        (S1 ^ (h - 2)) ^ (1 / p) =
            S1 ^ ((h - 2 : ℕ) * (1 / p)) :=
          (Real.rpow_natCast_mul hS1 (h - 2) (1 / p)).symm
        _ = S1 ^ ((1 / p) * ((h - 2 : ℕ) : ℝ)) := by
          congr 1
          ring
        _ = (S1 ^ (1 / p)) ^ ((h - 2 : ℕ) : ℝ) :=
          Real.rpow_mul hS1 (1 / p) ((h - 2 : ℕ) : ℝ)
        _ = (S1 ^ (1 / p)) ^ (h - 2) := by rw [Real.rpow_natCast]
    calc
      _ = (Mtail ^ (2 * p - 1) * (S * S1 ^ (h - 2))) ^ (1 / p) := by
        congr 1
        ring
      _ = (Mtail ^ (2 * p - 1)) ^ (1 / p) *
          (S * S1 ^ (h - 2)) ^ (1 / p) :=
        Real.mul_rpow (Real.rpow_nonneg hMtail _) (mul_nonneg hS (pow_nonneg hS1 _))
      _ = (Mtail ^ (2 * p - 1)) ^ (1 / p) *
          (S ^ (1 / p) * (S1 ^ (h - 2)) ^ (1 / p)) := by
        rw [Real.mul_rpow hS (pow_nonneg hS1 _)]
      _ = Mtail ^ (2 - 1 / p) * S ^ (1 / p) *
          (S1 ^ (1 / p)) ^ (h - 2) := by
        rw [hMpow, hS1pow]
        ring
  have htail : finiteLpNorm s p (fun x => ∏ i : Fin h, u (x i)) ≤
      Mtail ^ (2 - 1 / p) * S ^ (1 / p) * finiteLpNorm U p u ^ (h - 2) := by
    change (∑ x ∈ s, |(∏ i : Fin h, u (x i))| ^ p) ^ (1 / p) ≤ _
    calc
      _ ≤ (Mtail ^ (2 * p - 1) * S * S1 ^ (h - 2)) ^ (1 / p) := by
        apply Real.rpow_le_rpow
          (Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _)
          _ (one_div_nonneg.mpr (le_trans zero_le_one hp))
        rw [hsumImage]
        calc
          _ ≤ ∑ y ∈ D, |G y| ^ p := hsumSubset
          _ = S2 * S1 ^ (h - 2) := hsumD
          _ ≤ Mtail ^ (2 * p - 1) * S * S1 ^ (h - 2) :=
            mul_le_mul_of_nonneg_right hS2leTail (pow_nonneg hS1 _)
      _ = Mtail ^ (2 - 1 / p) * S ^ (1 / p) *
            finiteLpNorm U p u ^ (h - 2) := by
        rw [hpowTail, ← hnorm]
  exact ⟨hshort, htail⟩

private theorem finiteLpNorm_collisionProfile_two_bounds {h : ℕ} (hh : 2 ≤ h)
    (I : ReplicaPartition h) (hI : I ≠ ⊥)
    (s : Finset (LatticeConfiguration h)) (U : Finset Site)
    (hcoords : ∀ x ∈ s, ∀ i, x i ∈ U) {p : ℝ} (hp : 1 < p) (n : ℕ)
    (hn : 1 ≤ n) (u : Site → ℝ) (hu : ∀ y, 0 ≤ u y)
    (P B K : ℝ) (hK : 1 ≤ K) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hNorm : finiteLpNorm U p u ≤ K * P)
    (hSum : (∑ y ∈ U, u y) ≤ K * B)
    (hSupP : ∀ y ∈ U, u y ≤ K * (n : ℝ) ^ (-1 / p) * P)
    (hSup1 : ∀ y ∈ U, u y ≤ K / (n : ℝ) * B)
    (v : LatticeConfiguration h → ℝ)
    (hvzero : ∀ x ∈ s, ¬ IsCollisionConfiguration I x → v x = 0)
    (hveq : ∀ x ∈ s, IsCollisionConfiguration I x →
      |v x| = ∏ i : Fin h, u (x i)) :
    finiteLpNorm s p v ≤
        K ^ h * (n : ℝ) ^ (-1 / p) * P ^ h ∧
      finiteLpNorm s p v ≤
        K ^ h * (n : ℝ) ^ (-(2 - 1 / p)) * B ^ 2 * P ^ (h - 2) := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hδ : 0 < 1 / p := one_div_pos.mpr hp0
  have hα : 0 < 2 - 1 / p := by
    have hInv : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  let sc : Finset (LatticeConfiguration h) := s.filter (fun x =>
    IsCollisionConfiguration I x)
  have hsc : sc ⊆ s := Finset.filter_subset _ _
  have hcoords' : ∀ x ∈ sc, ∀ i, x i ∈ U := by
    intro x hx i
    exact hcoords x (Finset.mem_filter.mp hx).1 i
  obtain ⟨α, hαrel⟩ := exists_collisionPair_of_ne_discrete I hI
  let a : Fin h := α.val.1
  let b : Fin h := α.val.2
  have hab : a ≠ b := ne_of_lt α.property
  have hpair : ∀ x ∈ sc, x a = x b := by
    intro x hx
    have hc : IsCollisionConfiguration I x := (Finset.mem_filter.mp hx).2
    exact hc.1 a b hαrel
  let Mshort : ℝ := K * (n : ℝ) ^ (-1 / p) * P
  let Mtail : ℝ := K * B / (n : ℝ)
  let S : ℝ := K * B
  have hMshort : 0 ≤ Mshort := by
    dsimp [Mshort]
    positivity
  have hMtail : 0 ≤ Mtail := by
    dsimp [Mtail]
    positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSupShort : ∀ y ∈ U, u y ≤ Mshort := by
    intro y hy
    simpa [Mshort] using hSupP y hy
  have hSupTail : ∀ y ∈ U, u y ≤ Mtail := by
    intro y hy
    have h := hSup1 y hy
    dsimp [Mtail]
    calc
      u y ≤ K / (n : ℝ) * B := h
      _ = K * B / (n : ℝ) := by field_simp [ne_of_gt hnR]
  let ProdFun : LatticeConfiguration h → ℝ := fun x => ∏ i : Fin h, u (x i)
  have hpairBound := finiteLpNorm_replicaProduct_le_of_pair hh sc a b hab hpair hp.le
    U hcoords' u (fun y _ => hu y) Mshort Mtail hMshort hSupShort hMtail hSupTail S hS hSum
  have hzeroExtension : finiteLpNorm s p v = finiteLpNorm sc p v := by
    calc
      finiteLpNorm s p v = finiteLpNorm s p (fun x => if x ∈ sc then v x else 0) := by
        apply finiteLpNorm_abs_congr
        intro x hx
        by_cases hxs : x ∈ sc
        · simp [hxs]
        · have hnot : ¬ IsCollisionConfiguration I x := by
            intro hc
            exact hxs (Finset.mem_filter.mpr ⟨hx, hc⟩)
          simp [hxs, hvzero x hx hnot]
      _ = finiteLpNorm sc p v :=
        finiteLpNorm_zeroExtend_eq sc s hsc (by exact hp0) v
  have hproductAbs : finiteLpNorm sc p v = finiteLpNorm sc p ProdFun := by
    apply finiteLpNorm_abs_congr
    intro x hx
    have hcollision : IsCollisionConfiguration I x := (Finset.mem_filter.mp hx).2
    rw [hveq x (Finset.mem_filter.mp hx).1 hcollision]
    exact (abs_of_nonneg (Finset.prod_nonneg fun i hi => hu (x i))).symm
  have hnormProduct : finiteLpNorm s p v = finiteLpNorm sc p ProdFun := by
    rw [hzeroExtension, hproductAbs]
  have hnormUp : 0 ≤ finiteLpNorm U p u := finiteLpNorm_nonneg U p u
  have hKnonneg : 0 ≤ K := le_trans (by norm_num) hK
  have hKP : 0 ≤ K * P := mul_nonneg hKnonneg hP
  have hPowNorm : finiteLpNorm U p u ^ (h - 2) ≤ (K * P) ^ (h - 2) := by
    exact pow_le_pow_left₀ hnormUp hNorm _
  have hshortProfile : finiteLpNorm s p v ≤
      Mshort * finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2) := by
    rw [hnormProduct]
    exact hpairBound.1
  have hshort : finiteLpNorm s p v ≤ K ^ h * (n : ℝ) ^ (-1 / p) * P ^ h := by
    calc
      finiteLpNorm s p v ≤
          Mshort * finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2) := hshortProfile
      _ ≤ Mshort * (K * P) * (K * P) ^ (h - 2) := by
        calc
          Mshort * finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2) =
              Mshort * (finiteLpNorm U p u * finiteLpNorm U p u ^ (h - 2)) := by ring
          _ ≤ Mshort * ((K * P) * (K * P) ^ (h - 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hNorm hPowNorm (pow_nonneg hnormUp _) hKP) hMshort
          _ = Mshort * (K * P) * (K * P) ^ (h - 2) := by ring
      _ = K ^ h * (n : ℝ) ^ (-1 / p) * P ^ h := by
        dsimp [Mshort]
        rw [mul_pow]
        calc
          (K * (n : ℝ) ^ (-1 / p) * P) * (K * P) *
              (K ^ (h - 2) * P ^ (h - 2)) =
              (K * K ^ (h - 2) * K) * (n : ℝ) ^ (-1 / p) *
                (P * P ^ (h - 2) * P) := by ring
          _ = K ^ ((h - 2) + 2) * (n : ℝ) ^ (-1 / p) *
                P ^ ((h - 2) + 2) := by
            have hKpow : K * K ^ (h - 2) * K = K ^ ((h - 2) + 2) := by
              calc
                K * K ^ (h - 2) * K = K ^ (h - 2) * K ^ 2 := by ring
                _ = K ^ ((h - 2) + 2) := (pow_add K (h - 2) 2).symm
            have hPpow : P * P ^ (h - 2) * P = P ^ ((h - 2) + 2) := by
              calc
                P * P ^ (h - 2) * P = P ^ (h - 2) * P ^ 2 := by ring
                _ = P ^ ((h - 2) + 2) := (pow_add P (h - 2) 2).symm
            rw [hKpow, hPpow]
          _ = K ^ h * (n : ℝ) ^ (-1 / p) * P ^ h := by
            have hpow : (h - 2) + 2 = h := by omega
            rw [hpow]
  have htailProfile : finiteLpNorm s p v ≤
      Mtail ^ (2 - 1 / p) * S ^ (1 / p) * finiteLpNorm U p u ^ (h - 2) := by
    rw [hnormProduct]
    exact hpairBound.2
  have htail : finiteLpNorm s p v ≤
      K ^ h * (n : ℝ) ^ (-(2 - 1 / p)) * B ^ 2 * P ^ (h - 2) := by
    have hQ : 0 ≤ K * B := mul_nonneg hKnonneg hB
    have hαnonneg : 0 ≤ 2 - 1 / p := hα.le
    have hQfactor :
        ((K * B) / (n : ℝ)) ^ (2 - 1 / p) * (K * B) ^ (1 / p) =
          K ^ 2 * (n : ℝ) ^ (-(2 - 1 / p)) * B ^ 2 := by
      have hdiv := Real.div_rpow hQ hnR.le (2 - 1 / p)
      have hneg : (n : ℝ) ^ (-(2 - 1 / p)) =
          ((n : ℝ) ^ (2 - 1 / p))⁻¹ := Real.rpow_neg hnR.le _
      have hsum : (2 - 1 / p) + 1 / p = 2 := by ring
      calc
        _ = ((K * B) ^ (2 - 1 / p) / (n : ℝ) ^ (2 - 1 / p)) *
              (K * B) ^ (1 / p) := by rw [hdiv]
        _ = (K * B) ^ ((2 - 1 / p) + 1 / p) *
              (n : ℝ) ^ (-(2 - 1 / p)) := by
          calc
            ((K * B) ^ (2 - 1 / p) / (n : ℝ) ^ (2 - 1 / p)) *
                (K * B) ^ (1 / p) =
                ((K * B) ^ (2 - 1 / p) * (K * B) ^ (1 / p)) *
                  ((n : ℝ) ^ (2 - 1 / p))⁻¹ := by ring
            _ = (K * B) ^ ((2 - 1 / p) + 1 / p) *
                  (n : ℝ) ^ (-(2 - 1 / p)) := by
              rw [← Real.rpow_add_of_nonneg hQ hαnonneg hδ.le, ← hneg]
        _ = (K * B) ^ (2 : ℝ) * (n : ℝ) ^ (-(2 - 1 / p)) := by
          rw [hsum]
        _ = K ^ 2 * (n : ℝ) ^ (-(2 - 1 / p)) * B ^ 2 := by
          have hpow : (K * B) ^ (2 : ℝ) = (K * B) ^ (2 : ℕ) := by
            norm_num [Real.rpow_natCast]
          rw [hpow]
          rw [mul_pow]
          ring
    have hPowNormTail :
        finiteLpNorm U p u ^ (h - 2) ≤ (K * P) ^ (h - 2) := hPowNorm
    calc
      finiteLpNorm s p v ≤
          Mtail ^ (2 - 1 / p) * S ^ (1 / p) *
            finiteLpNorm U p u ^ (h - 2) := htailProfile
      _ ≤ Mtail ^ (2 - 1 / p) * S ^ (1 / p) * (K * P) ^ (h - 2) := by
        apply mul_le_mul_of_nonneg_left hPowNormTail
        exact mul_nonneg (Real.rpow_nonneg hMtail _) (Real.rpow_nonneg hS _)
      _ = K ^ h * (n : ℝ) ^ (-(2 - 1 / p)) * B ^ 2 * P ^ (h - 2) := by
        dsimp [Mtail, S]
        rw [mul_pow]
        rw [hQfactor]
        calc
          (K ^ 2 * (n : ℝ) ^ (-(2 - 1 / p)) * B ^ 2) *
              (K ^ (h - 2) * P ^ (h - 2)) =
              (K ^ 2 * K ^ (h - 2)) * (n : ℝ) ^ (-(2 - 1 / p)) *
                B ^ 2 * P ^ (h - 2) := by ring
          _ = K ^ h * (n : ℝ) ^ (-(2 - 1 / p)) * B ^ 2 *
                P ^ (h - 2) := by
            have hpow : 2 + (h - 2) = h := by omega
            rw [← pow_add K 2 (h - 2), hpow]
  exact ⟨hshort, htail⟩

/-- The two `ℓᵖ` bounds for the weighted replica boundary vector at a fixed time, given the
convolution bounds `hconvBounds`: one with the factor `n^(-1/p)`, and one with `n^(-(2-1/p))`
and the squared weighted sum. -/
theorem finiteLpNorm_replicaBoundaryVector_time_two_bounds {h : ℕ}
    (hh : 2 ≤ h) (I : ReplicaPartition h) (hI : I ≠ ⊥)
    (A : Finset Site) (f : Site → ℝ) (hf : ∀ y, 0 ≤ f y)
    (s : Finset (LatticeConfiguration h)) (t : ℝ) (ht : 0 ≤ t)
    (n : ℕ) (hn : 1 ≤ n) {p : ℝ} (hp : 1 < p)
    (c : ℝ) (hc : 1 ≤ c)
    (hconvBounds : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, ∀ p : ℝ, 1 ≤ p →
      ∀ (A S : Finset Site) (f : Site → ℝ),
        finiteLpNorm S p
            (fun x => finiteBoundaryConvolution n A f x *
              Real.exp (t * ‖siteToPlane x‖)) ≤
          c * Real.exp (2 * c * t ^ 2 * n) *
            finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ∧
        (1 ≤ n → ∀ x : Site,
          |finiteBoundaryConvolution n A f x| * Real.exp (t * ‖siteToPlane x‖) ≤
            c * Real.exp (2 * c * t ^ 2 * n) / (n : ℝ) ^ (1 / p) *
              finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖)))) :
    finiteLpNorm s p
        (fun x => replicaBoundaryVector n I A f x / replicaExponentialWeight t x) ≤
        (c * Real.exp (2 * c * t ^ 2 * n)) ^ h *
          (n : ℝ) ^ (-1 / p) *
          finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ^ h ∧
      finiteLpNorm s p
        (fun x => replicaBoundaryVector n I A f x / replicaExponentialWeight t x) ≤
        (c * Real.exp (2 * c * t ^ 2 * n)) ^ h *
          (n : ℝ) ^ (-(2 - 1 / p)) *
          (∑ y ∈ A, f y * Real.exp (t * ‖siteToPlane y‖)) ^ 2 *
          finiteLpNorm A p
            (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ^ (h - 2) := by
  classical
  let U : Finset Site := s.biUnion (fun x => Finset.univ.image fun i : Fin h => x i)
  let u : Site → ℝ := fun y =>
    |finiteBoundaryConvolution n A f y| * Real.exp (t * ‖siteToPlane y‖)
  let F' : Site → ℝ := fun y => f y * Real.exp (t * ‖siteToPlane y‖)
  let P : ℝ := finiteLpNorm A p F'
  let B : ℝ := ∑ y ∈ A, F' y
  let K : ℝ := c * Real.exp (2 * c * t ^ 2 * n)
  have hF'nonneg : ∀ y ∈ A, 0 ≤ F' y := by
    intro y hy
    dsimp [F']
    exact mul_nonneg (hf y) (Real.exp_nonneg _)
  have hP : 0 ≤ P := finiteLpNorm_nonneg A p F'
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun y hy => hF'nonneg y hy
  have hK : 1 ≤ K := by
    dsimp [K]
    have harg : 0 ≤ 2 * c * t ^ 2 * n := by positivity
    have hexp : 1 ≤ Real.exp (2 * c * t ^ 2 * n) := by
      nlinarith [Real.add_one_le_exp (2 * c * t ^ 2 * n)]
    calc
      1 ≤ c := hc
      _ = c * 1 := by ring
      _ ≤ c * Real.exp (2 * c * t ^ 2 * n) :=
        mul_le_mul_of_nonneg_left hexp (le_trans (by norm_num) hc)
  have hUcoords : ∀ x ∈ s, ∀ i, x i ∈ U := by
    intro x hx i
    dsimp [U]
    exact Finset.mem_biUnion.mpr ⟨x, hx,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hconvP := hconvBounds t ht n p hp.le A U f
  have hconv1 := hconvBounds t ht n 1 (by norm_num) A U f
  have hu_nonneg (y : Site) : 0 ≤ u y := by
    dsimp [u]
    exact mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  have habsEq (y : Site) :
      |finiteBoundaryConvolution n A f y * Real.exp (t * ‖siteToPlane y‖)| = u y := by
    dsimp [u]
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hnormEqP := finiteLpNorm_abs_congr U p
    (fun y => finiteBoundaryConvolution n A f y * Real.exp (t * ‖siteToPlane y‖)) u
    (fun y _ => (habsEq y).trans (abs_of_nonneg (hu_nonneg y)).symm)
  have hnormU : finiteLpNorm U p u ≤ K * P := by
    calc
      finiteLpNorm U p u = finiteLpNorm U p
          (fun y => finiteBoundaryConvolution n A f y *
            Real.exp (t * ‖siteToPlane y‖)) := hnormEqP.symm
      _ ≤ c * Real.exp (2 * c * t ^ 2 * n) *
          finiteLpNorm A p F' := hconvP.1
      _ = K * P := rfl
  have hinput1 : finiteLpNorm A 1 F' = B := by
    dsimp [B]
    exact finiteLpNorm_one_eq_sum_of_nonneg A F' hF'nonneg
  have hnormEq1 := finiteLpNorm_abs_congr U 1
    (fun y => finiteBoundaryConvolution n A f y *
      Real.exp (t * ‖siteToPlane y‖)) u
    (fun y _ => (habsEq y).trans (abs_of_nonneg (hu_nonneg y)).symm)
  have hsumU : (∑ y ∈ U, u y) ≤ K * B := by
    calc
      (∑ y ∈ U, u y) = finiteLpNorm U 1 u :=
        (finiteLpNorm_one_eq_sum_of_nonneg U u (fun y _ => mul_nonneg
          (abs_nonneg _) (Real.exp_nonneg _))).symm
      _ = finiteLpNorm U 1
          (fun y => finiteBoundaryConvolution n A f y *
            Real.exp (t * ‖siteToPlane y‖)) := hnormEq1.symm
      _ ≤ c * Real.exp (2 * c * t ^ 2 * n) * finiteLpNorm A 1 F' := hconv1.1
      _ = K * B := by rw [hinput1]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnegp : (n : ℝ) ^ (-1 / p) = ((n : ℝ) ^ (1 / p))⁻¹ := by
    rw [show (-1 : ℝ) / p = -(1 / p) by ring, Real.rpow_neg hnR.le]
  have hSupP : ∀ y ∈ U, u y ≤ K * (n : ℝ) ^ (-1 / p) * P := by
    intro y hy
    have hpoint := (hconvP.2 hn y)
    change u y ≤ K / (n : ℝ) ^ (1 / p) * P at hpoint
    rw [div_eq_mul_inv, ← hnegp] at hpoint
    exact hpoint
  have hSup1 : ∀ y ∈ U, u y ≤ K / (n : ℝ) * B := by
    intro y hy
    have hpoint := (hconv1.2 hn y)
    change u y ≤ K / (n : ℝ) ^ (1 / 1) * finiteLpNorm A 1 F' at hpoint
    rw [hinput1] at hpoint
    simpa [one_div_one, Real.rpow_one] using hpoint
  let v : LatticeConfiguration h → ℝ := fun x =>
    replicaBoundaryVector n I A f x / replicaExponentialWeight t x
  have hvzero : ∀ x ∈ s, ¬ IsCollisionConfiguration I x → v x = 0 := by
    intro x hx hxc
    simp [v, replicaBoundaryVector, hxc]
  have hveq : ∀ x ∈ s, IsCollisionConfiguration I x →
      |v x| = ∏ i : Fin h, u (x i) := by
    intro x hx hcoll
    simpa [v, u, weightedBoundaryOneReplica] using
      replicaBoundaryVector_weighted_abs_eq_of_collision t n I A f x hcoll
  have hprofile := finiteLpNorm_collisionProfile_two_bounds hh I
    hI s U hUcoords hp n hn u
    (fun y => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) P B K hK hP hB
    hnormU hsumU hSupP hSup1 v hvzero hveq
  simpa [v, F', P, B, K] using hprofile

end Critical2DKPZ.MomentBounds

end
