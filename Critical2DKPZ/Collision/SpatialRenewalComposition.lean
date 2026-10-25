/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewal
public import Critical2DKPZ.RandomWalk.Port.Walk.SRWDecomp
public import Critical2DKPZ.RandomWalk.Port.Walk.SRWOneDim
public import Critical2DKPZ.Polymer.PathComposition
public import Critical2DKPZ.WalkTails.LogConcavity
public import Critical2DKPZ.Collision.SquaredBinomialLocalGaussian
public import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic

/-! # Composition formula for the spatial renewal profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open LatticeProb
open Critical2DKPZ.WalkTails

private def rotatedU (x : Site) : ℤ := x 0 + x 1

private def rotatedV (x : Site) : ℤ := x 0 - x 1

private theorem srwHeat_two_rotated_product (n : ℕ) (x : Site) :
    LatticeProb.srwHeat 2 n x =
      LatticeProb.S1 n (rotatedU x) * LatticeProb.S1 n (rotatedV x) := by
  induction n generalizing x with
  | zero =>
      rw [LatticeProb.srwHeat_zero, LatticeProb.S1_zero, LatticeProb.S1_zero]
      by_cases hx : x = 0
      · subst x
        simp [rotatedU, rotatedV]
      · have hUV : rotatedU x ≠ 0 ∨ rotatedV x ≠ 0 := by
          by_cases hU : rotatedU x = 0
          · by_cases hV : rotatedV x = 0
            · exfalso
              apply hx
              ext i
              fin_cases i <;> simp_all [rotatedU, rotatedV] <;> omega
            · exact Or.inr hV
          · exact Or.inl hU
        rcases hUV with hU | hV
        · simp [hU, hx]
        · simp [hV, hx]
  | succ n ih =>
      rw [LatticeProb.srwHeat_succ_eq_sum_dir]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
      simp_rw [ih]
      simp [rotatedU, rotatedV, LatticeProb.dirVec]
      rw [LatticeProb.S1_succ, LatticeProb.S1_succ]
      ring_nf

private theorem S1_eq_binomZ_of_double (k : ℕ) (u j : ℤ)
    (h : 2 * j = (k : ℤ) + u) :
    LatticeProb.S1 k u = LatticeProb.binomZ k j / (2 : ℝ) ^ k := by
  by_cases hjneg : j < 0
  · have huneg : u < 0 := by omega
    have huabs : (k : ℤ) < (u.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_neg huneg]
      omega
    have hnorm : k < LatticeProb.graphNorm (![u] : LatticeProb.Site 1) := by
      rw [LatticeProb.graphNorm_one]
      exact_mod_cast huabs
    have hkernel : LatticeProb.S1 k u = 0 := by
      rw [LatticeProb.S1, LatticeProb.srwHeat_eq_zero_of_lt hnorm]
    rw [hkernel, LatticeProb.binomZ_of_neg hjneg]
    simp
  · have hjnonneg : 0 ≤ j := by omega
    by_cases hjk : j ≤ (k : ℤ)
    · let a : ℕ := j.toNat
      have haj : (a : ℤ) = j := by
        dsimp [a]
        exact Int.toNat_of_nonneg hjnonneg
      have hakZ : (a : ℤ) ≤ (k : ℤ) := by
        rw [haj]
        exact hjk
      have hak : a ≤ k := by exact_mod_cast hakZ
      let b : ℕ := k - a
      have hab : a + b = k := by
        dsimp [b]
        exact Nat.add_sub_of_le hak
      have hu : u = (a : ℤ) - (b : ℤ) := by
        have h' : 2 * (a : ℤ) = (k : ℤ) + u := by simpa [haj] using h
        have hab' : (a : ℤ) + (b : ℤ) = (k : ℤ) := by exact_mod_cast hab
        omega
      have hbinom : LatticeProb.binomZ k j = (Nat.choose k a : ℝ) := by
        rw [show j = (a : ℤ) by exact haj.symm, LatticeProb.binomZ_natCast]
      rw [LatticeProb.S1, hu, LatticeProb.srwHeat_one_binom k a b hab, hbinom]
    · have hklej : (k : ℤ) < j := by omega
      have huPos : 0 < u := by omega
      have huabs : (k : ℤ) < (u.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_pos huPos]
        omega
      have hnorm : k < LatticeProb.graphNorm (![u] : LatticeProb.Site 1) := by
        rw [LatticeProb.graphNorm_one]
        exact_mod_cast huabs
      have hkernel : LatticeProb.S1 k u = 0 := by
        rw [LatticeProb.S1, LatticeProb.srwHeat_eq_zero_of_lt hnorm]
      rw [hkernel, LatticeProb.binomZ_of_lt hklej]
      simp

/-- Rotated coordinates: the planar walk is a product of two independent
`±1` walks in `x₀ + x₁` and `x₀ − x₁`. -/
theorem srwKernel_eq_binomZ_mul (k : ℕ) (x : Site) (j₁ j₂ : ℤ)
    (h₁ : 2 * j₁ = k + x 0 + x 1) (h₂ : 2 * j₂ = k + x 0 - x 1) :
    srwKernel k x = LatticeProb.binomZ k j₁ * LatticeProb.binomZ k j₂ / 4 ^ k := by
  have hrot := srwHeat_two_rotated_product k x
  have hu : 2 * j₁ = (k : ℤ) + rotatedU x := by
    simpa [rotatedU, add_assoc] using h₁
  have hv : 2 * j₂ = (k : ℤ) + rotatedV x := by
    calc
      2 * j₂ = ((k : ℤ) + x 0) - x 1 := h₂
      _ = (k : ℤ) + (x 0 - x 1) := by abel
  rw [srwKernel_eq_srwHeat, hrot,
    S1_eq_binomZ_of_double k (rotatedU x) j₁ hu,
    S1_eq_binomZ_of_double k (rotatedV x) j₂ hv]
  have hden : (2 : ℝ) ^ k * 2 ^ k = (4 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  calc
    (LatticeProb.binomZ k j₁ / (2 : ℝ) ^ k) *
        (LatticeProb.binomZ k j₂ / (2 : ℝ) ^ k) =
        LatticeProb.binomZ k j₁ * LatticeProb.binomZ k j₂ /
          ((2 : ℝ) ^ k * 2 ^ k) := by ring
    _ = LatticeProb.binomZ k j₁ * LatticeProb.binomZ k j₂ / 4 ^ k := by rw [hden]


/-- Iterated spatial convolution of the squared one-step-block kernels of a
composition. -/
def squareConvolution : List ℕ → Site → ℝ
  | [] => fun x => if x = 0 then 1 else 0
  | k :: ks => fun x => ∑' z, srwKernel k z ^ 2 * squareConvolution ks (x - z)

/-- Prepend the block determined by the total size of the remaining composition. -/
def compositionPrependFirstBlock (n : ℕ)
    (p : Σ m : Fin (n + 1), Composition m.val) : Composition (n + 1) where
  blocks := (n + 1 - p.1.val) :: p.2.blocks
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact Nat.sub_pos_of_lt p.1.isLt
    · exact p.2.blocks_pos hi
  blocks_sum := by
    simp only [List.sum_cons]
    rw [p.2.blocks_sum]
    exact Nat.sub_add_cancel (Nat.le_of_lt p.1.isLt)

/-- Split a positive composition into its first block and its tail total. -/
noncomputable def compositionSplitFirstBlock (n : ℕ) (c : Composition (n + 1)) :
    Σ m : Fin (n + 1), Composition m.val := by
  classical
  have hne : c.blocks ≠ [] := by
    intro h
    have hz : n + 1 = 0 := (Composition.blocks_eq_nil c).mp h
    omega
  have hsplit : c.blocks.head! :: c.blocks.tail = c.blocks := List.cons_head!_tail hne
  have hsum : c.blocks.head! + c.blocks.tail.sum = n + 1 := by
    calc
      c.blocks.head! + c.blocks.tail.sum = (c.blocks.head! :: c.blocks.tail).sum := by simp
      _ = c.blocks.sum := by rw [hsplit]
      _ = n + 1 := c.blocks_sum
  have hhead : 0 < c.blocks.head! := c.blocks_pos (List.head!_mem_self hne)
  have htail : c.blocks.tail.sum < n + 1 := by omega
  refine ⟨⟨c.blocks.tail.sum, htail⟩, ⟨c.blocks.tail, ?_, rfl⟩⟩
  intro i hi
  apply c.blocks_pos
  rw [← hsplit]
  simp [hi]

/-- Decompose a positive composition into its first block and the remaining
composition, with the remainder parameterized by its total size. -/
def compositionFirstBlockEquiv (n : ℕ) :
    (Σ m : Fin (n + 1), Composition m.val) ≃ Composition (n + 1) where
  toFun := compositionPrependFirstBlock n
  invFun := compositionSplitFirstBlock n
  left_inv := by
    rintro ⟨m, c⟩
    have hm : (compositionSplitFirstBlock n
        (compositionPrependFirstBlock n ⟨m, c⟩)).1 = m := by
      apply Fin.ext
      simp [compositionPrependFirstBlock, compositionSplitFirstBlock]
    have hc : (compositionSplitFirstBlock n
        (compositionPrependFirstBlock n ⟨m, c⟩)).2 =
        c.cast c.blocks_sum.symm := by
      apply Composition.ext
      simp [compositionPrependFirstBlock, compositionSplitFirstBlock,
        Composition.cast_blocks]
    exact Sigma.ext hm
      (HEq.trans (heq_of_eq hc) (Composition.cast_heq c c.blocks_sum.symm))
  right_inv := by
    intro c
    have hne : c.blocks ≠ [] := by
      intro h
      have hz : n + 1 = 0 := (Composition.blocks_eq_nil c).mp h
      omega
    have hsplit : c.blocks.head! :: c.blocks.tail = c.blocks := List.cons_head!_tail hne
    have hsum : c.blocks.head! + c.blocks.tail.sum = n + 1 := by
      calc
        c.blocks.head! + c.blocks.tail.sum = (c.blocks.head! :: c.blocks.tail).sum := by simp
        _ = c.blocks.sum := by rw [hsplit]
        _ = n + 1 := c.blocks_sum
    have hfirst : n + 1 - c.blocks.tail.sum = c.blocks.head! := by omega
    apply Composition.ext
    change (n + 1 - c.blocks.tail.sum) :: c.blocks.tail = c.blocks
    rw [hfirst, hsplit]

private theorem tsum_kernelConv_sum (k : ℕ) (x : Site) (F : Site → ℝ) :
    ∑' z, srwKernel k z ^ 2 * F (x - z) =
      ∑ z ∈ Polymer.endpoints 0 k, srwKernel k z ^ 2 * F (x - z) := by
  apply tsum_eq_sum
  intro z hz
  have hkernel := Polymer.srwKernel_eq_zero_of_not_mem k 0 z hz
  simp [sub_zero] at hkernel
  simp [hkernel]

private theorem squareConvolution_cons_sum (k : ℕ) (ks : List ℕ) (x : Site) :
    squareConvolution (k :: ks) x =
      ∑ z ∈ Polymer.endpoints 0 k,
        srwKernel k z ^ 2 * squareConvolution ks (x - z) := by
  exact tsum_kernelConv_sum k x (squareConvolution ks)

private def siteFromCounts (k : ℕ) (a b : ℤ) : Site :=
  ![a + b - (k : ℤ), a - b]

private def countsFromSite (k : ℕ) (z : Site) : ℤ × ℤ :=
  (((k : ℤ) + z 0 + z 1) / 2, ((k : ℤ) + z 0 - z 1) / 2)

private theorem srwStep_rotatedU (s : Fin 4) :
    srwStep s 0 + srwStep s 1 = 1 ∨ srwStep s 0 + srwStep s 1 = -1 := by
  fin_cases s <;> decide

private theorem srwStep_rotatedV (s : Fin 4) :
    srwStep s 0 - srwStep s 1 = 1 ∨ srwStep s 0 - srwStep s 1 = -1 := by
  fin_cases s <;> decide

private theorem countsFromSite_two_mul (k : ℕ) (z : Site)
    (ha : Even ((k : ℤ) + z 0 + z 1))
    (hb : Even ((k : ℤ) + z 0 - z 1)) :
    2 * (countsFromSite k z).1 = (k : ℤ) + z 0 + z 1 ∧
      2 * (countsFromSite k z).2 = (k : ℤ) + z 0 - z 1 := by
  constructor <;> exact Int.two_mul_ediv_two_of_even (by assumption)

private theorem siteFromCounts_countsFromSite (k : ℕ) (z : Site)
    (ha : Even ((k : ℤ) + z 0 + z 1))
    (hb : Even ((k : ℤ) + z 0 - z 1)) :
    siteFromCounts k (countsFromSite k z).1 (countsFromSite k z).2 = z := by
  obtain ⟨h₁, h₂⟩ := countsFromSite_two_mul k z ha hb
  ext i
  fin_cases i <;> simp [siteFromCounts, countsFromSite] at * <;> omega

private theorem countsFromSite_siteFromCounts (k : ℕ) (a b : ℤ) :
    countsFromSite k (siteFromCounts k a b) = (a, b) := by
  apply Prod.ext
  · change ((k : ℤ) + (siteFromCounts k a b) 0 +
      (siteFromCounts k a b) 1) / 2 = a
    rw [show (k : ℤ) + (siteFromCounts k a b) 0 +
      (siteFromCounts k a b) 1 = 2 * a by simp [siteFromCounts]; ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  · change ((k : ℤ) + (siteFromCounts k a b) 0 -
      (siteFromCounts k a b) 1) / 2 = b
    rw [show (k : ℤ) + (siteFromCounts k a b) 0 -
      (siteFromCounts k a b) 1 = 2 * b by simp [siteFromCounts]; ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

private theorem endpoint_rotated_even (k : ℕ) {z : Site}
    (hz : z ∈ Polymer.endpoints 0 k) :
    Even ((k : ℤ) + z 0 + z 1) ∧ Even ((k : ℤ) + z 0 - z 1) := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff 0 z k).mp hz
  have hpar := Polymer.walkPosition_parity (0 : Site) s
  have hparU : Int.ModEq 2 (z 0 + z 1) (k : ℤ) := by
    simpa [hs] using hpar
  have hparV : Int.ModEq 2 (z 0 - z 1) (k : ℤ) := by
    dsimp [Int.ModEq] at hparU ⊢
    omega
  have hevenU : Even ((k : ℤ) + z 0 + z 1) := by
    apply Int.even_iff.mpr
    have hmod : Int.ModEq 2 ((z 0 + z 1) + (k : ℤ)) 0 := by
      calc
        _ ≡ (k : ℤ) + k [ZMOD 2] := hparU.add_right k
        _ ≡ 0 [ZMOD 2] := by dsimp [Int.ModEq]; omega
    simpa [Int.ModEq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmod
  have hevenV : Even ((k : ℤ) + z 0 - z 1) := by
    apply Int.even_iff.mpr
    have hmod : Int.ModEq 2 ((z 0 - z 1) + (k : ℤ)) 0 := by
      calc
        _ ≡ (k : ℤ) + k [ZMOD 2] := hparV.add_right k
        _ ≡ 0 [ZMOD 2] := by dsimp [Int.ModEq]; omega
    simpa [Int.ModEq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmod
  exact ⟨hevenU, hevenV⟩

private theorem endpoint_counts_mem (k : ℕ) {z : Site}
    (hz : z ∈ Polymer.endpoints 0 k) :
    (countsFromSite k z).1 ∈ Finset.Icc (0 : ℤ) k ∧
      (countsFromSite k z).2 ∈ Finset.Icc (0 : ℤ) k := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff 0 z k).mp hz
  obtain ⟨hevenU, hevenV⟩ := endpoint_rotated_even k hz
  obtain ⟨hU, hV⟩ := countsFromSite_two_mul k z hevenU hevenV
  have hsumU : z 0 + z 1 =
      ∑ i : Fin k, (srwStep (s i) 0 + srwStep (s i) 1) := by
    rw [← hs, Polymer.walkPosition_end]
    simp only [Pi.zero_apply, zero_add, Pi.add_apply, Finset.sum_apply]
    rw [Finset.sum_add_distrib]
  have hsumV : z 0 - z 1 =
      ∑ i : Fin k, (srwStep (s i) 0 - srwStep (s i) 1) := by
    rw [← hs, Polymer.walkPosition_end]
    simp only [zero_add, Finset.sum_apply]
    rw [Finset.sum_sub_distrib]
  have huStep (i : Fin k) :
      -1 ≤ srwStep (s i) 0 + srwStep (s i) 1 ∧
        srwStep (s i) 0 + srwStep (s i) 1 ≤ 1 := by
    rcases (srwStep_rotatedU (s i)) with h | h <;> omega
  have hvStep (i : Fin k) :
      -1 ≤ srwStep (s i) 0 - srwStep (s i) 1 ∧
        srwStep (s i) 0 - srwStep (s i) 1 ≤ 1 := by
    rcases (srwStep_rotatedV (s i)) with h | h <;> omega
  have huBounds : -(k : ℤ) ≤ z 0 + z 1 ∧ z 0 + z 1 ≤ k := by
    constructor
    · calc
        -(k : ℤ) = ∑ i : Fin k, (-1 : ℤ) := by simp
        _ ≤ ∑ i : Fin k, (srwStep (s i) 0 + srwStep (s i) 1) :=
          Finset.sum_le_sum fun i _ => (huStep i).1
        _ = z 0 + z 1 := hsumU.symm
    · calc
        z 0 + z 1 = ∑ i : Fin k, (srwStep (s i) 0 + srwStep (s i) 1) := hsumU
        _ ≤ ∑ i : Fin k, (1 : ℤ) := Finset.sum_le_sum fun i _ => (huStep i).2
        _ = k := by simp
  have hvBounds : -(k : ℤ) ≤ z 0 - z 1 ∧ z 0 - z 1 ≤ k := by
    constructor
    · calc
        -(k : ℤ) = ∑ i : Fin k, (-1 : ℤ) := by simp
        _ ≤ ∑ i : Fin k, (srwStep (s i) 0 - srwStep (s i) 1) :=
          Finset.sum_le_sum fun i _ => (hvStep i).1
        _ = z 0 - z 1 := hsumV.symm
    · calc
        z 0 - z 1 = ∑ i : Fin k, (srwStep (s i) 0 - srwStep (s i) 1) := hsumV
        _ ≤ ∑ i : Fin k, (1 : ℤ) := Finset.sum_le_sum fun i _ => (hvStep i).2
        _ = k := by simp
  constructor <;> simp only [Finset.mem_Icc] <;> omega

private theorem siteFromCounts_mem_endpoints (k : ℕ) {a b : ℤ}
    (ha : a ∈ Finset.Icc (0 : ℤ) k) (hb : b ∈ Finset.Icc (0 : ℤ) k) :
    siteFromCounts k a b ∈ Polymer.endpoints 0 k := by
  have h₁ : 2 * a = (k : ℤ) + (siteFromCounts k a b) 0 +
      (siteFromCounts k a b) 1 := by simp [siteFromCounts]; ring
  have h₂ : 2 * b = (k : ℤ) + (siteFromCounts k a b) 0 -
      (siteFromCounts k a b) 1 := by simp [siteFromCounts]; ring
  have hchooseA : 0 < LatticeProb.binomZ k a := by
    rcases Int.eq_ofNat_of_zero_le (Finset.mem_Icc.mp ha).1 with ⟨aN, rfl⟩
    rw [LatticeProb.binomZ_natCast]
    exact_mod_cast Nat.choose_pos (by exact_mod_cast (Finset.mem_Icc.mp ha).2)
  have hchooseB : 0 < LatticeProb.binomZ k b := by
    rcases Int.eq_ofNat_of_zero_le (Finset.mem_Icc.mp hb).1 with ⟨bN, rfl⟩
    rw [LatticeProb.binomZ_natCast]
    exact_mod_cast Nat.choose_pos (by exact_mod_cast (Finset.mem_Icc.mp hb).2)
  have hq : 0 < srwKernel k (siteFromCounts k a b) := by
    rw [srwKernel_eq_binomZ_mul k _ a b h₁ h₂]
    positivity
  by_contra hz
  have hzero : srwKernel k (siteFromCounts k a b) = 0 := by
    simpa using Polymer.srwKernel_eq_zero_of_not_mem k 0
      (siteFromCounts k a b) hz
  linarith

private theorem sum_endpoints_eq_sum_counts (k : ℕ) (f : Site → ℝ) :
    (∑ z ∈ Polymer.endpoints 0 k, f z) =
      ∑ a ∈ Finset.Icc (0 : ℤ) k, ∑ b ∈ Finset.Icc (0 : ℤ) k,
        f (siteFromCounts k a b) := by
  classical
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun z hz => countsFromSite k z)
  · intro z hz
    exact Finset.mem_product.mpr ⟨(endpoint_counts_mem k hz).1,
      (endpoint_counts_mem k hz).2⟩
  · intro z hz z' hz' hcounts
    have heven := endpoint_rotated_even k hz
    have heven' := endpoint_rotated_even k hz'
    have hinv := siteFromCounts_countsFromSite k z heven.1 heven.2
    have hinv' := siteFromCounts_countsFromSite k z' heven'.1 heven'.2
    calc
      z = siteFromCounts k (countsFromSite k z).1 (countsFromSite k z).2 := hinv.symm
      _ = siteFromCounts k (countsFromSite k z').1 (countsFromSite k z').2 := by rw [hcounts]
      _ = z' := hinv'
  · intro p hp
    refine ⟨siteFromCounts k p.1 p.2,
      siteFromCounts_mem_endpoints k (Finset.mem_product.mp hp).1
        (Finset.mem_product.mp hp).2, ?_⟩
    exact countsFromSite_siteFromCounts k p.1 p.2
  · intro z hz
    exact congrArg f (siteFromCounts_countsFromSite k z
      (endpoint_rotated_even k hz).1 (endpoint_rotated_even k hz).2).symm

private theorem srwKernel_even_origin (k : ℕ) :
    srwKernel (2 * k) 0 =
      ((Nat.choose (2 * k) k : ℝ) / 4 ^ k) ^ 2 := by
  have h : 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) + 0 + 0 := by push_cast; ring
  rw [srwKernel_eq_binomZ_mul (2 * k) 0 k k h h]
  simp_rw [LatticeProb.binomZ_natCast]
  have hpow : (4 : ℝ) ^ (2 * k) = ((4 : ℝ) ^ k) ^ 2 := by
    rw [show 2 * k = k * 2 by omega, pow_mul]
  rw [hpow]
  ring

private theorem srwKernel_sq_counts (k : ℕ) (z : Site) (a b : ℤ)
    (h₁ : 2 * a = (k : ℤ) + z 0 + z 1)
    (h₂ : 2 * b = (k : ℤ) + z 0 - z 1) :
    srwKernel k z ^ 2 = srwKernel (2 * k) 0 *
      WalkTails.hypergeometricIntWeight k a *
        WalkTails.hypergeometricIntWeight k b := by
  rw [srwKernel_eq_binomZ_mul k z a b h₁ h₂, srwKernel_even_origin]
  unfold WalkTails.hypergeometricIntWeight
  have hchoosePos : 0 < Nat.choose (2 * k) k := Nat.choose_pos (by omega)
  have hchoose : (Nat.choose (2 * k) k : ℝ) ≠ 0 := by exact_mod_cast hchoosePos.ne'
  field_simp [hchoose]

private theorem sum_product_factor (A : Finset ℤ) (c : ℝ)
    (f g : ℤ → ℝ) :
    (∑ a ∈ A, ∑ b ∈ A, c * (f a * g b)) =
      c * (∑ a ∈ A, f a) * (∑ b ∈ A, g b) := by
  calc
    _ = ∑ a ∈ A, c * (f a * ∑ b ∈ A, g b) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ b ∈ A, (c * f a) * g b := by
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = (c * f a) * ∑ b ∈ A, g b := by rw [Finset.mul_sum]
        _ = c * (f a * ∑ b ∈ A, g b) := by ring
    _ = c * (∑ a ∈ A, f a) * (∑ b ∈ A, g b) := by
      calc
        _ = ∑ a ∈ A, (c * f a) * (∑ b ∈ A, g b) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = (∑ a ∈ A, c * f a) * (∑ b ∈ A, g b) := by rw [Finset.sum_mul]
        _ = (c * ∑ a ∈ A, f a) * (∑ b ∈ A, g b) := by rw [← Finset.mul_sum]
        _ = _ := by ring

private theorem squareConvolution_eq_aux (ks : List ℕ) :
    ∀ (x : Site) (j₁ j₂ : ℤ),
      2 * j₁ = (ks.sum : ℤ) + x 0 + x 1 →
      2 * j₂ = (ks.sum : ℤ) + x 0 - x 1 →
      squareConvolution ks x =
        (ks.map fun k => srwKernel (2 * k) 0).prod *
          WalkTails.squaredBinomialConvolution ks j₁ *
            WalkTails.squaredBinomialConvolution ks j₂ := by
  induction ks with
  | nil =>
      intro x j₁ j₂ h₁ h₂
      simp only [List.sum_nil, Nat.cast_zero, zero_add] at h₁ h₂
      by_cases hx : x = 0
      · subst x
        simp only [Pi.zero_apply, zero_add] at h₁ h₂
        have hj₁ : j₁ = 0 := by omega
        have hj₂ : j₂ = 0 := by omega
        simp [squareConvolution, WalkTails.squaredBinomialConvolution,
          WalkTails.deltaCoeff, hj₁, hj₂]
      · have hnonzero : j₁ ≠ 0 ∨ j₂ ≠ 0 := by
          by_contra h
          push Not at h
          apply hx
          have hx₀ : x 0 = 0 := by omega
          have hx₁ : x 1 = 0 := by omega
          ext i
          fin_cases i <;> simp [hx₀, hx₁]
        rcases hnonzero with hj₁ | hj₂
        · simp [squareConvolution, WalkTails.squaredBinomialConvolution,
            WalkTails.deltaCoeff, hx, hj₁]
        · simp [squareConvolution, WalkTails.squaredBinomialConvolution,
            WalkTails.deltaCoeff, hx, hj₂]
  | cons k ks ih =>
      intro x j₁ j₂ h₁ h₂
      simp only [List.sum_cons, Nat.cast_add] at h₁ h₂
      have hkernel (a b : ℤ) :
          srwKernel k (siteFromCounts k a b) ^ 2 =
            srwKernel (2 * k) 0 * WalkTails.hypergeometricIntWeight k a *
              WalkTails.hypergeometricIntWeight k b := by
        apply srwKernel_sq_counts
        · simp [siteFromCounts]; ring
        · simp [siteFromCounts]; ring
      have htail₁ (a b : ℤ) :
          2 * (j₁ - a) = (ks.sum : ℤ) +
            (x - siteFromCounts k a b) 0 + (x - siteFromCounts k a b) 1 := by
        have hz : (siteFromCounts k a b) 0 + (siteFromCounts k a b) 1 =
            2 * a - k := by simp [siteFromCounts]; ring
        simp only [Pi.sub_apply]
        have hz' : 2 * a - k = (siteFromCounts k a b) 0 +
            (siteFromCounts k a b) 1 := by simpa [siteFromCounts] using hz.symm
        linear_combination h₁ - hz'
      have htail₂ (a b : ℤ) :
          2 * (j₂ - b) = (ks.sum : ℤ) +
            (x - siteFromCounts k a b) 0 - (x - siteFromCounts k a b) 1 := by
        have hz : (siteFromCounts k a b) 0 - (siteFromCounts k a b) 1 =
            2 * b - k := by simp [siteFromCounts]; ring
        simp only [Pi.sub_apply]
        have hz' : 2 * b - k = (siteFromCounts k a b) 0 -
            (siteFromCounts k a b) 1 := by simpa [siteFromCounts] using hz.symm
        linear_combination h₂ - hz'
      have hsum :
          squareConvolution (k :: ks) x =
            ∑ a ∈ Finset.Icc (0 : ℤ) k, ∑ b ∈ Finset.Icc (0 : ℤ) k,
              srwKernel k (siteFromCounts k a b) ^ 2 *
                squareConvolution ks (x - siteFromCounts k a b) := by
        rw [squareConvolution_cons_sum, sum_endpoints_eq_sum_counts]
      rw [hsum]
      simp_rw [hkernel]
      have hsumTail :
          (∑ a ∈ Finset.Icc (0 : ℤ) k, ∑ b ∈ Finset.Icc (0 : ℤ) k,
            (srwKernel (2 * k) 0 *
                WalkTails.hypergeometricIntWeight k a *
                WalkTails.hypergeometricIntWeight k b) *
              squareConvolution ks (x - siteFromCounts k a b)) =
          srwKernel (2 * k) 0 *
            (ks.map fun m => srwKernel (2 * m) 0).prod *
              (∑ a ∈ Finset.Icc (0 : ℤ) k,
                WalkTails.hypergeometricIntWeight k a *
                  WalkTails.squaredBinomialConvolution ks (j₁ - a)) *
              (∑ b ∈ Finset.Icc (0 : ℤ) k,
                WalkTails.hypergeometricIntWeight k b *
                  WalkTails.squaredBinomialConvolution ks (j₂ - b)) := by
        calc
          _ = ∑ a ∈ Finset.Icc (0 : ℤ) k, ∑ b ∈ Finset.Icc (0 : ℤ) k,
              (srwKernel (2 * k) 0 *
                  (ks.map fun m => srwKernel (2 * m) 0).prod) *
                ((WalkTails.hypergeometricIntWeight k a *
                    WalkTails.squaredBinomialConvolution ks (j₁ - a)) *
                  (WalkTails.hypergeometricIntWeight k b *
                    WalkTails.squaredBinomialConvolution ks (j₂ - b))) := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            rw [ih (x - siteFromCounts k a b) (j₁ - a) (j₂ - b)
              (htail₁ a b) (htail₂ a b)]
            ring
          _ = _ := by
            rw [sum_product_factor]
      rw [hsumTail]
      simp only [WalkTails.squaredBinomialConvolution, WalkTails.finiteConvolution]
      simp only [List.map_cons, List.prod_cons]

/-- A planar convolution of squared kernels factors into the product of the
two rotated squared-binomial convolutions. -/
theorem squareConvolution_eq (ks : List ℕ) (x : Site) (j₁ j₂ : ℤ)
    (h₁ : 2 * j₁ = (ks.sum : ℤ) + x 0 + x 1)
    (h₂ : 2 * j₂ = (ks.sum : ℤ) + x 0 - x 1) :
    squareConvolution ks x =
      (ks.map fun k => srwKernel (2 * k) 0).prod *
        WalkTails.squaredBinomialConvolution ks j₁ *
          WalkTails.squaredBinomialConvolution ks j₂ :=
  squareConvolution_eq_aux ks x j₁ j₂ h₁ h₂

/-- Squared planar kernels retain the parity class of their total duration. -/
theorem squareConvolution_eq_zero_of_odd (ks : List ℕ) (x : Site)
    (h : ¬ Even ((ks.sum : ℤ) + x 0 + x 1)) : squareConvolution ks x = 0 := by
  induction ks generalizing x with
  | nil =>
      simp only [List.sum_nil, Nat.cast_zero, zero_add] at h
      have hx : x ≠ 0 := by
        intro hx
        subst x
        exact h (by simp)
      simp [squareConvolution, hx]
  | cons k ks ih =>
      simp only [List.sum_cons, Nat.cast_add] at h
      rw [squareConvolution_cons_sum, sum_endpoints_eq_sum_counts]
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro b hb
      let z := siteFromCounts k a b
      have hz : z 0 + z 1 = 2 * a - k := by simp [z, siteFromCounts]; ring
      have htotal : (k : ℤ) + (ks.sum : ℤ) + x 0 + x 1 =
          (ks.sum : ℤ) + (x - z) 0 + (x - z) 1 + 2 * a := by
        simp only [Pi.sub_apply]
        push_cast
        linear_combination hz
      have htail : ¬ Even ((ks.sum : ℤ) + (x - z) 0 + (x - z) 1) := by
        intro heven
        have hsumEven : Even ((ks.sum : ℤ) + (x - z) 0 + (x - z) 1 + 2 * a) := by
          apply Int.even_iff.mpr
          have hmod := Int.even_iff.mp heven
          omega
        have htotalEven : Even ((k : ℤ) + (ks.sum : ℤ) + x 0 + x 1) := by
          rw [htotal]
          exact hsumEven
        exact h htotalEven
      rw [ih (x - z) htail]
      simp

private theorem endpoint_translate (n : ℕ) (z y : Site)
    (hy : y ∈ Polymer.endpoints 0 n) : z + y ∈ Polymer.endpoints z n := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff 0 y n).mp hy
  apply (Polymer.mem_endpoints_iff z (z + y) n).2
  refine ⟨s, ?_⟩
  calc
    walkPosition z s n = z + walkPosition 0 s n := by
      simpa using Polymer.walkPosition_add_start z 0 s n
    _ = z + y := by rw [hs]

private theorem endpoints_add {n m : ℕ} {z x : Site}
    (hz : z ∈ Polymer.endpoints 0 n) (hx : x ∈ Polymer.endpoints z m) :
    x ∈ Polymer.endpoints 0 (n + m) := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff 0 z n).mp hz
  obtain ⟨t, ht⟩ := (Polymer.mem_endpoints_iff z x m).mp hx
  apply (Polymer.mem_endpoints_iff 0 x (n + m)).2
  refine ⟨Fin.append s t, ?_⟩
  rw [Polymer.walkPosition_append_end, hs]
  exact ht

private theorem squareConvolution_eq_zero_of_not_mem {ks : List ℕ} {x : Site}
    (hx : x ∉ Polymer.endpoints 0 ks.sum) : squareConvolution ks x = 0 := by
  induction ks generalizing x with
  | nil =>
      have hreachable : (0 : Site) ∈ Polymer.endpoints 0 0 := by
        apply (Polymer.mem_endpoints_iff 0 0 0).2
        exact ⟨Fin.elim0, by simp⟩
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        exact hx hreachable
      simp [squareConvolution, hx0]
  | cons k ks ih =>
      simp only [List.sum_cons] at hx
      rw [squareConvolution_cons_sum]
      apply Finset.sum_eq_zero
      intro z hz
      have htail : x - z ∉ Polymer.endpoints 0 ks.sum := by
        intro hreach
        apply hx
        have htranslate : x ∈ Polymer.endpoints z ks.sum := by
          have h := endpoint_translate ks.sum z (x - z) hreach
          convert h using 1
          ext i
          simp
        exact endpoints_add hz htranslate
      rw [ih htail]
      simp

/-- A squared-kernel composition is supported on the endpoints reachable in its total time. -/
theorem squareConvolution_eq_zero_of_not_mem_endpoints {ks : List ℕ} {x : Site}
    (hx : x ∉ Polymer.endpoints 0 ks.sum) : squareConvolution ks x = 0 :=
  squareConvolution_eq_zero_of_not_mem hx

/-- The total mass of the planar squared convolution is the product of the
central two-step return masses. -/
theorem tsum_squareConvolution (ks : List ℕ) :
    ∑' x, squareConvolution ks x = (ks.map fun k => srwKernel (2 * k) 0).prod := by
  rw [tsum_eq_sum]
  · rw [sum_endpoints_eq_sum_counts]
    calc
      _ = ∑ a ∈ Finset.Icc (0 : ℤ) ks.sum,
            ∑ b ∈ Finset.Icc (0 : ℤ) ks.sum,
              (ks.map fun k => srwKernel (2 * k) 0).prod *
                (WalkTails.squaredBinomialConvolution ks a *
                  WalkTails.squaredBinomialConvolution ks b) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [squareConvolution_eq ks (siteFromCounts ks.sum a b) a b]
        · ring
        · simp [siteFromCounts]; ring
        · simp [siteFromCounts]; ring
      _ = (ks.map fun k => srwKernel (2 * k) 0).prod := by
        rw [sum_product_factor, WalkTails.squaredBinomialConvolution_sum_one ks]
        ring
  · intro x hx
    exact squareConvolution_eq_zero_of_not_mem hx

private def siteReflection (x : Site) : Site ≃ Site where
  toFun y := x - y
  invFun y := x - y
  left_inv y := by
    ext i
    simp only [Pi.sub_apply]
    omega
  right_inv y := by
    ext i
    simp only [Pi.sub_apply]
    omega

private theorem tsum_reflect_kernel (k : ℕ) (x : Site) (F : Site → ℝ) :
    ∑' z, srwKernel k z ^ 2 * F (x - z) =
      ∑' z, F z * srwKernel k (x - z) ^ 2 := by
  let e := siteReflection x
  calc
    _ = ∑' z, srwKernel k (e z) ^ 2 * F (x - e z) :=
      (e.tsum_eq (fun z => srwKernel k z ^ 2 * F (x - z))).symm
    _ = _ := by
      apply tsum_congr
      intro z
      simp only [e, siteReflection, Equiv.coe_fn_mk]
      have hz : x - (x - z) = z := by
        ext i
        simp only [Pi.sub_apply]
        omega
      rw [hz]
      ring

private theorem sum_firstBlock_convolution (σ : ℝ) {m : ℕ} (x : Site)
    (E : Finset Site) (q : Site → ℝ) (F : Composition m → Site → ℝ) :
    (∑ c : Composition m, σ ^ (c.length + 1) *
        ∑ z ∈ E, q z ^ 2 * F c (x - z)) =
      σ * ∑ z ∈ E, q z ^ 2 *
        (∑ c : Composition m, σ ^ c.length * F c (x - z)) := by
  classical
  calc
    _ = ∑ c : Composition m, ∑ z ∈ E,
          σ ^ (c.length + 1) * (q z ^ 2 * F c (x - z)) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = ∑ z ∈ E, ∑ c : Composition m,
          σ ^ (c.length + 1) * (q z ^ 2 * F c (x - z)) := by
      rw [Finset.sum_comm]
    _ = σ * ∑ z ∈ E, q z ^ 2 *
          (∑ c : Composition m, σ ^ c.length * F c (x - z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      calc
        (∑ c : Composition m,
            σ ^ (c.length + 1) * (q z ^ 2 * F c (x - z))) =
            ∑ c : Composition m,
              σ * (q z ^ 2 * (σ ^ c.length * F c (x - z))) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [pow_succ]
          ring
        _ = σ * (q z ^ 2 *
            (∑ c : Composition m, σ ^ c.length * F c (x - z))) := by
          calc
            _ = ∑ c : Composition m,
                  (σ * q z ^ 2) * (σ ^ c.length * F c (x - z)) := by
                apply Finset.sum_congr rfl
                intro c hc
                ring
            _ = (σ * q z ^ 2) *
                  (∑ c : Composition m, σ ^ c.length * F c (x - z)) := by
                rw [Finset.mul_sum]
            _ = _ := by ring

private theorem compositionSum_succ (σ : ℝ) (n : ℕ) (x : Site) :
    (∑ c : Composition (n + 1), σ ^ c.length * squareConvolution c.blocks x) =
      ∑ m : Fin (n + 1), σ * ∑' z,
        (∑ c : Composition m.val, σ ^ c.length * squareConvolution c.blocks z) *
          srwKernel (n + 1 - m.val) (x - z) ^ 2 := by
  classical
  let f : Composition (n + 1) → ℝ := fun c =>
    σ ^ c.length * squareConvolution c.blocks x
  calc
    (∑ c : Composition (n + 1), σ ^ c.length * squareConvolution c.blocks x) =
        ∑ p : Σ m : Fin (n + 1), Composition m.val,
          f (compositionPrependFirstBlock n p) :=
      (compositionFirstBlockEquiv n).sum_comp f |>.symm
    _ = ∑ m : Fin (n + 1), ∑ c : Composition m.val,
          σ ^ (c.length + 1) *
            ∑ z ∈ Polymer.endpoints 0 (n + 1 - m.val),
              srwKernel (n + 1 - m.val) z ^ 2 * squareConvolution c.blocks (x - z) := by
      calc
        _ = ∑ p : Σ m : Fin (n + 1), Composition m.val,
              (fun m c => f (compositionPrependFirstBlock n ⟨m, c⟩)) p.1 p.2 := by
          apply Finset.sum_congr rfl
          intro p hp
          rfl
        _ = ∑ m : Fin (n + 1), ∑ c : Composition m.val,
              f (compositionPrependFirstBlock n ⟨m, c⟩) :=
          Fintype.sum_sigma' (fun m c => f (compositionPrependFirstBlock n ⟨m, c⟩))
        _ = _ := by
          simp only [f, compositionPrependFirstBlock, Composition.length, List.length_cons,
            squareConvolution_cons_sum]
    _ = ∑ m : Fin (n + 1), σ *
          ∑ z ∈ Polymer.endpoints 0 (n + 1 - m.val),
            srwKernel (n + 1 - m.val) z ^ 2 *
              (∑ c : Composition m.val, σ ^ c.length * squareConvolution c.blocks (x - z)) := by
      apply Finset.sum_congr rfl
      intro m hm
      simpa [Composition.length] using
        (sum_firstBlock_convolution σ x
          (Polymer.endpoints 0 (n + 1 - m.val))
          (fun z => srwKernel (n + 1 - m.val) z)
          (fun c y => squareConvolution c.blocks y))
    _ = ∑ m : Fin (n + 1), σ * ∑' z,
          (∑ c : Composition m.val, σ ^ c.length * squareConvolution c.blocks z) *
            srwKernel (n + 1 - m.val) (x - z) ^ 2 := by
      apply Finset.sum_congr rfl
      intro m hm
      let G : Site → ℝ := fun y =>
        ∑ c : Composition m.val, σ ^ c.length * squareConvolution c.blocks y
      change σ * (∑ z ∈ Polymer.endpoints 0 (n + 1 - m.val),
          srwKernel (n + 1 - m.val) z ^ 2 * G (x - z)) =
        σ * ∑' z, G z * srwKernel (n + 1 - m.val) (x - z) ^ 2
      have hfinite :
          ∑ z ∈ Polymer.endpoints 0 (n + 1 - m.val),
            srwKernel (n + 1 - m.val) z ^ 2 * G (x - z) =
          ∑' z, srwKernel (n + 1 - m.val) z ^ 2 * G (x - z) :=
        (tsum_kernelConv_sum (n + 1 - m.val) x G).symm
      calc
        σ * (∑ z ∈ Polymer.endpoints 0 (n + 1 - m.val),
            srwKernel (n + 1 - m.val) z ^ 2 * G (x - z)) =
          σ * ∑' z, srwKernel (n + 1 - m.val) z ^ 2 * G (x - z) :=
            congrArg (fun r : ℝ => σ * r) hfinite
        _ = σ * ∑' z, G z * srwKernel (n + 1 - m.val) (x - z) ^ 2 :=
          congrArg (fun r : ℝ => σ * r)
            (tsum_reflect_kernel (n + 1 - m.val) x G)

private theorem composition_zero_eq_ones (c : Composition 0) :
    c = Composition.ones 0 := by
  apply Composition.ext
  have hc : c.length = 0 := Nat.eq_zero_of_le_zero c.length_le
  have hl : c.blocks.length = 0 := by simp [hc]
  have hblocks : c.blocks = [] := List.length_eq_zero_iff.mp hl
  simp [Composition.ones_blocks, hblocks]

private instance compositionZeroUnique : Unique (Composition 0) where
  default := Composition.ones 0
  uniq := composition_zero_eq_ones

private theorem spatialRenewal_eq_sum_compositions_all (σ : ℝ) (n : ℕ) (x : Site) :
    spatialRenewal σ n x =
      ∑ c : Composition n, σ ^ c.length * squareConvolution c.blocks x := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        rw [spatialRenewal_zero, Fintype.sum_unique]
        change (if x = 0 then 1 else 0) =
          σ ^ (Composition.ones 0).length *
            squareConvolution (Composition.ones 0).blocks x
        simp [squareConvolution, Composition.ones_blocks]
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        rw [spatialRenewal_succ, compositionSum_succ]
        apply Finset.sum_congr rfl
        intro m' hm'
        calc
          ∑' z, spatialRenewal σ m'.val z * σ *
              srwKernel (m + 1 - m'.val) (x - z) ^ 2 =
            ∑' z, (∑ c : Composition m'.val,
              σ ^ c.length * squareConvolution c.blocks z) * σ *
                srwKernel (m + 1 - m'.val) (x - z) ^ 2 := by
            apply tsum_congr
            intro z
            rw [ih m'.val (by omega) z]
          _ = ∑' z, σ *
                ((∑ c : Composition m'.val,
                  σ ^ c.length * squareConvolution c.blocks z) *
                  srwKernel (m + 1 - m'.val) (x - z) ^ 2) := by
            apply tsum_congr
            intro z
            ring
          _ = σ * ∑' z,
                (∑ c : Composition m'.val,
                  σ ^ c.length * squareConvolution c.blocks z) *
                srwKernel (m + 1 - m'.val) (x - z) ^ 2 := tsum_mul_left

/-- Expand the last-renewal recursion as a finite sum over compositions of
the total time. -/
theorem spatialRenewal_eq_sum_compositions (σ2 : ℝ) {n : ℕ} (hn : 1 ≤ n) (x : Site) :
    spatialRenewal σ2 n x =
      ∑ c : Composition n, σ2 ^ c.length * squareConvolution c.blocks x := by
  cases n with
  | zero => omega
  | succ n => exact spatialRenewal_eq_sum_compositions_all σ2 (n + 1) x

end Critical2DKPZ.Collision

end
