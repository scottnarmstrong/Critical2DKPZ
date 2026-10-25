/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockSpatialMixedLimit
public import Critical2DKPZ.SHF.Moments.PairBlockCompositionLocalLimit
public import Critical2DKPZ.SHF.Moments.PairBlockCompositionTail
public import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
public import Critical2DKPZ.SHF.DeltaBose.ScalarBounds
import Mathlib.Tactic

/-! # Spatial local limit for the critical pair-block renewal -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

private theorem natCube_mul_exp_neg_four_log_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 3 *
      Real.exp (-4 * Real.log (N : ℝ))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have heq : (fun N : ℕ => (N : ℝ) ^ 3 *
      Real.exp (-4 * Real.log (N : ℝ))) =ᶠ[atTop]
      fun N : ℕ => (N : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hexp : Real.exp (-4 * Real.log (N : ℝ)) =
        (Real.exp (-Real.log (N : ℝ))) ^ 4 := by
      calc
        _ = Real.exp ((4 : ℕ) * (-Real.log (N : ℝ))) := by congr 1; norm_num
        _ = _ := Real.exp_nat_mul _ _
    rw [hexp, Real.exp_neg, Real.exp_log hNreal]
    field_simp [hNreal.ne']
  exact hinv.congr' heq.symm

private theorem hypergeometricBlockListLaw_le_one
    (ms : List ℕ) (j : ℕ) (hj : j ≤ ms.sum) :
    hypergeometricBlockListLaw ms j ≤ 1 := by
  have hjmem : j ∈ Finset.range (ms.sum + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsingle := Finset.single_le_sum
    (fun k hk => hypergeometricBlockListLaw_nonneg ms k) hjmem
  rw [hypergeometricBlockListLaw_sum_one] at hsingle
  exact hsingle

private theorem hypergeometricBlockListPairLaw_le_one
    (ms : List ℕ) (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ ms.sum) (hj₂ : j₂ ≤ ms.sum) :
    hypergeometricBlockListPairLaw ms j₁ j₂ ≤ 1 := by
  have h₁ := hypergeometricBlockListLaw_le_one ms j₁ hj₁
  have h₂ := hypergeometricBlockListLaw_le_one ms j₂ hj₂
  have hn₁ := hypergeometricBlockListLaw_nonneg ms j₁
  have hn₂ := hypergeometricBlockListLaw_nonneg ms j₂
  unfold hypergeometricBlockListPairLaw
  calc
    _ ≤ 1 * hypergeometricBlockListLaw ms j₂ :=
      mul_le_mul_of_nonneg_right h₁ hn₂
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = 1 := by ring

private theorem heatKernel_le_t0_inverse {t₀ u : ℝ} (ht₀ : 0 < t₀)
    (hu : t₀ / 2 ≤ u) (y : Plane) :
    heatKernel u y ≤ (Real.pi * t₀)⁻¹ := by
  have huPos : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hden : Real.pi * t₀ ≤ 2 * Real.pi * u := by
    calc
      Real.pi * t₀ = (2 * Real.pi) * (t₀ / 2) := by ring
      _ ≤ (2 * Real.pi) * u :=
        mul_le_mul_of_nonneg_left hu (by positivity)
  have hdenPos : 0 < Real.pi * t₀ := mul_pos Real.pi_pos ht₀
  calc
    heatKernel u y ≤ (2 * Real.pi * u)⁻¹ := heatKernel_le_at_zero huPos.le y
    _ ≤ (Real.pi * t₀)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hdenPos hden

private theorem sum_short_long_split {α : Type*} [Fintype α]
    (len : α → ℕ) (K : ℕ) (f : α → ℝ) :
    (∑ x : α, f x) =
      (∑ x : α, if len x < K then f x else 0) +
      (∑ x : α, if K ≤ len x then f x else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : len x < K
  · simp [h, Nat.not_le_of_gt h]
  · have h' : K ≤ len x := Nat.le_of_not_gt h
    simp [h, h']

private theorem abs_sum_short_weight_error {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (w f : α → ℝ) (H η : ℝ)
    (hw : ∀ x, 0 ≤ w x) (herr : ∀ x, P x → |f x - H| ≤ η) :
    |(∑ x : α, if P x then w x * f x else 0) -
      H * (∑ x : α, if P x then w x else 0)| ≤
      η * (∑ x : α, if P x then w x else 0) := by
  classical
  have hfactor : H * (∑ x : α, if P x then w x else 0) =
      ∑ x : α, if P x then w x * H else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hP : P x
    · simp [hP]
      ring
    · simp [hP]
  have hdiff :
      (∑ x : α, if P x then w x * f x else 0) -
        H * (∑ x : α, if P x then w x else 0) =
      ∑ x : α, if P x then w x * (f x - H) else 0 := by
    rw [hfactor, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hP : P x
    · simp [hP]
      ring
    · simp [hP]
  rw [hdiff]
  calc
    _ ≤ ∑ x : α, |if P x then w x * (f x - H) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : α, if P x then w x * η else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hP : P x
      · simp [hP]
        rw [abs_of_nonneg (hw x)]
        exact mul_le_mul_of_nonneg_left (herr x hP) (hw x)
      · simp [hP]
    _ = η * (∑ x : α, if P x then w x else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hP : P x
      · simp [hP]
        ring
      · simp [hP]

/-- The scalar weight of a collision composition, before summing its spatial mark. -/
def compositionScalarWeight (σ : ℝ) {n : ℕ}
    (c : Composition n) : ℝ :=
  σ ^ c.length * (c.blocks.map Renewal.returnWeight).prod

/-- Collision compositions have nonnegative scalar weights for nonnegative activity. -/
theorem compositionScalarWeight_nonneg (σ : ℝ) (hσ : 0 ≤ σ) {n : ℕ}
    (c : Composition n) : 0 ≤ compositionScalarWeight σ c := by
  unfold compositionScalarWeight
  apply mul_nonneg (pow_nonneg hσ _)
  apply List.prod_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
  exact srwKernel_nonneg (2 * r) 0

/-- The scalar coefficient in the exact pair-law expansion is the scalar
composition weight. -/
theorem compositionScalarWeight_eq_pairCoefficient (σ : ℝ) {n : ℕ}
    (c : Composition n) :
    compositionScalarWeight σ c =
      σ ^ c.length * (c.blocks.map fun k => srwKernel (2 * k) 0).prod := by
  change σ ^ c.length * (c.blocks.map Renewal.returnWeight).prod = _
  rfl

private theorem compositionScalarWeight_prepend (σ : ℝ) (n : ℕ)
    (m : Fin (n + 1)) (c : Composition m.val) :
    compositionScalarWeight σ (Critical2DKPZ.Collision.compositionPrependFirstBlock
      n ⟨m, c⟩) =
      (σ * Renewal.returnWeight (n + 1 - m.val)) * compositionScalarWeight σ c := by
  simp [compositionScalarWeight,
    Critical2DKPZ.Collision.compositionPrependFirstBlock,
    Composition.length, List.length_cons, List.map_cons, List.prod_cons,
    pow_succ]
  ring

private theorem compositionScalarWeight_lengthSum_succ (σ : ℝ) (n k : ℕ) :
    (∑ c : Composition (n + 1),
      if c.length = k + 1 then compositionScalarWeight σ c else 0) =
      ∑ m : Fin (n + 1), (σ * Renewal.returnWeight (n + 1 - m.val)) *
        (∑ c : Composition m.val,
          if c.length = k then compositionScalarWeight σ c else 0) := by
  classical
  let f : Composition (n + 1) → ℝ := fun c =>
    if c.length = k + 1 then compositionScalarWeight σ c else 0
  calc
    _ = ∑ p : Σ m : Fin (n + 1), Composition m.val,
        f (Critical2DKPZ.Collision.compositionPrependFirstBlock n p) :=
      (Critical2DKPZ.Collision.compositionFirstBlockEquiv n).sum_comp f |>.symm
    _ = ∑ m : Fin (n + 1), ∑ c : Composition m.val,
        f (Critical2DKPZ.Collision.compositionPrependFirstBlock n ⟨m, c⟩) :=
      Fintype.sum_sigma' (fun m c =>
        f (Critical2DKPZ.Collision.compositionPrependFirstBlock n ⟨m, c⟩))
    _ = ∑ m : Fin (n + 1), ∑ c : Composition m.val,
        (if c.length = k then
          (σ * Renewal.returnWeight (n + 1 - m.val)) * compositionScalarWeight σ c
         else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hk : c.length = k
      · have hlen : (Critical2DKPZ.Collision.compositionPrependFirstBlock
            n ⟨m, c⟩).length = c.length + 1 := by
          simp [Critical2DKPZ.Collision.compositionPrependFirstBlock,
            Composition.length]
        simp [f, hlen, hk, compositionScalarWeight_prepend]
      · have hlen : (Critical2DKPZ.Collision.compositionPrependFirstBlock
            n ⟨m, c⟩).length = c.length + 1 := by
          simp [Critical2DKPZ.Collision.compositionPrependFirstBlock,
            Composition.length]
        simp [f, hlen, hk]
    _ = ∑ m : Fin (n + 1),
        (σ * Renewal.returnWeight (n + 1 - m.val)) *
          (∑ c : Composition m.val,
            if c.length = k then compositionScalarWeight σ c else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      calc
        _ = ∑ c : Composition m.val,
            (σ * Renewal.returnWeight (n + 1 - m.val)) *
              (if c.length = k then compositionScalarWeight σ c else 0) := by
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hk : c.length = k <;> simp [hk]
        _ = _ := by rw [Finset.mul_sum]

private theorem sum_Icc_one_succ_eq_reversed_sum_fin {n : ℕ} (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 (n + 1), f r =
      ∑ m : Fin (n + 1), f (n + 1 - m.val) := by
  classical
  refine Finset.sum_bij (fun r hr => ⟨n + 1 - r, ?_⟩) ?_ ?_ ?_ ?_
  · have hr := Finset.mem_Icc.mp hr
    omega
  · intro r hr
    simp
  · intro r₁ hr₁ r₂ hr₂ heq
    have hr₁' : r₁ ≤ n + 1 := (Finset.mem_Icc.mp hr₁).2
    have hr₂' : r₂ ≤ n + 1 := (Finset.mem_Icc.mp hr₂).2
    have hval : n + 1 - r₁ = n + 1 - r₂ := congrArg Fin.val heq
    exact (tsub_right_inj hr₁' hr₂').mp hval
  · intro m hm
    refine ⟨n + 1 - m.val, ?_, ?_⟩
    · have hm' := m.isLt
      simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      change n + 1 - (n + 1 - m.val) = m.val
      exact Nat.sub_sub_self (Nat.le_of_lt m.isLt)
  · intro r hr
    have hrle : r ≤ n + 1 := (Finset.mem_Icc.mp hr).2
    change f r = f (n + 1 - (n + 1 - r))
    congr 1
    exact (Nat.sub_sub_self hrle).symm

/-- The sum of composition weights at a fixed number of blocks is the
corresponding scalar renewal convolution power. -/
theorem compositionScalarWeight_length_sum_eq_convolutionPower (σ : ℝ) :
    ∀ n k : ℕ,
      (∑ c : Composition n,
        if c.length = k then compositionScalarWeight σ c else 0) =
        Renewal.convolutionPower (fun r => σ * Renewal.returnWeight r) k n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro k
      cases n with
      | zero =>
          classical
          have huniq (c : Composition 0) : c = Composition.ones 0 := by
            apply Composition.ext
            have hblocks : c.blocks = [] := by
              have hlen : c.length = 0 := by simp
              change c.blocks.length = 0 at hlen
              exact List.length_eq_zero_iff.mp hlen
            simp [Composition.ones_blocks, hblocks]
          have huniv : (Finset.univ : Finset (Composition 0)) =
              {Composition.ones 0} := by
            ext c
            simp [huniq]
          have hlen : (Composition.ones 0).length = 0 := by simp
          have hweight : compositionScalarWeight σ (Composition.ones 0) = 1 := by
            simp [compositionScalarWeight]
          cases k <;> simp [huniv, hlen, hweight, Renewal.convolutionPower]
      | succ n =>
          cases k with
          | zero =>
              classical
              have hpos (c : Composition (n + 1)) : c.length ≠ 0 := by
                intro hc
                have hnil : c.blocks = [] := by
                  change c.blocks.length = 0 at hc
                  exact List.length_eq_zero_iff.mp hc
                have hsum : c.blocks.sum = 0 := by simp [hnil]
                rw [c.blocks_sum] at hsum
                omega
              have hleft :
                  (∑ c : Composition (n + 1),
                    if c.length = 0 then compositionScalarWeight σ c else 0) = 0 := by
                apply Finset.sum_eq_zero
                intro c hc
                simp [hpos c]
              rw [hleft]
              simp [Renewal.convolutionPower]
          | succ k =>
              rw [compositionScalarWeight_lengthSum_succ]
              calc
                _ = ∑ m : Fin (n + 1), (σ * Renewal.returnWeight (n + 1 - m.val)) *
                    Renewal.convolutionPower (fun r => σ * Renewal.returnWeight r) k m.val := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  rw [ih m.val (by have hm' := m.isLt; omega) k]
                _ = Renewal.convolutionPower
                    (fun r => σ * Renewal.returnWeight r) (k + 1) (n + 1) := by
                  rw [Renewal.convolutionPower_succ]
                  let w : ℕ → ℝ := fun r => σ * Renewal.returnWeight r
                  let f : ℕ → ℝ := fun r => w r *
                    Renewal.convolutionPower w k (n + 1 - r)
                  have hindex := sum_Icc_one_succ_eq_reversed_sum_fin (n := n) f
                  rw [hindex]
                  apply Finset.sum_congr rfl
                  intro m hm
                  simp [f, w, Nat.sub_sub_self (Nat.le_of_lt m.isLt)]

/-- Composition weights with at least `K` blocks are exactly the scalar
renewal tail over convolution orders `K` and above. -/
theorem compositionScalarWeight_longLength_sum_eq_convolutionPower_tail
    (σ : ℝ) (n K : ℕ) :
    (∑ c : Composition n,
      if K ≤ c.length then compositionScalarWeight σ c else 0) =
      ∑ k ∈ Finset.Icc K n,
        Renewal.convolutionPower (fun r => σ * Renewal.returnWeight r) k n := by
  classical
  let T := Finset.Icc K n
  have hsingle (c : Composition n) :
      (if K ≤ c.length then compositionScalarWeight σ c else 0) =
        ∑ k ∈ T, if c.length = k then compositionScalarWeight σ c else 0 := by
    by_cases hc : K ≤ c.length
    · have hmem : c.length ∈ T := by
        simp [T, hc, c.length_le]
      rw [Finset.sum_eq_single c.length]
      · simp [hc]
      · intro k hk hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hmem).elim
    · have hmem : c.length ∉ T := by
        simp [T, hc]
      have hzero :
          (∑ k ∈ T, if c.length = k then compositionScalarWeight σ c else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hne : c.length ≠ k := by
          intro heq
          exact hmem (heq ▸ hk)
        simp [hne]
      simp [hc, hzero]
  calc
    _ = ∑ c : Composition n, ∑ k ∈ T,
        if c.length = k then compositionScalarWeight σ c else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hsingle c
    _ = ∑ k ∈ T, ∑ c : Composition n,
        if c.length = k then compositionScalarWeight σ c else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact compositionScalarWeight_length_sum_eq_convolutionPower σ n k

/-- Below the time horizon `N`, the long composition tail agrees exactly with
the clipped critical-window convolution tail. -/
theorem compositionScalarWeight_longLength_sum_eq_criticalWindowTail
    (σ : ℝ) (N n K : ℕ) (hn : n ≤ N) :
    (∑ c : Composition n,
      if K ≤ c.length then compositionScalarWeight σ c else 0) =
      ∑ k ∈ Finset.Icc K n,
        Renewal.convolutionPower
          (fun r => if r ≤ N then σ * Renewal.returnWeight r else 0) k n := by
  rw [compositionScalarWeight_longLength_sum_eq_convolutionPower_tail]
  apply Finset.sum_congr rfl
  intro k hk
  apply Renewal.convolutionPower_congr
  intro r hr1 hrn
  simp [Nat.le_trans hrn hn]

/-- The exact spatial renewal expansion factors through the scalar composition
weight and the two-coordinate block law. -/
theorem spatialRenewal_eq_compositionScalarWeight_pairLaw
    (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) (z : Site) (j₁ j₂ : ℕ)
    (h₁ : 2 * (j₁ : ℤ) = (n : ℤ) + z 0 + z 1)
    (h₂ : 2 * (j₂ : ℤ) = (n : ℤ) + z 0 - z 1) :
    Collision.spatialRenewal σ n z =
      ∑ c : Composition n,
        compositionScalarWeight σ c *
          hypergeometricBlockListPairLaw c.blocks j₁ j₂ := by
  rw [spatialRenewal_eq_compositionPairLaw σ hn z j₁ j₂ h₁ h₂]
  apply Finset.sum_congr rfl
  intro c hc
  rw [compositionScalarWeight_eq_pairCoefficient]

private theorem exists_rotatedPairIndices {n : ℕ} (z : Site)
    (hEven : Even ((n : ℤ) + z 0 + z 1))
    (hplus : |(z 0 : ℝ) + z 1| ≤ n)
    (hminus : |(z 0 : ℝ) - z 1| ≤ n) :
    ∃ j₁ j₂ : ℕ, j₁ ≤ n ∧ j₂ ≤ n ∧
      2 * (j₁ : ℤ) = (n : ℤ) + z 0 + z 1 ∧
      2 * (j₂ : ℤ) = (n : ℤ) + z 0 - z 1 := by
  have hEven₂ : Even ((n : ℤ) + z 0 - z 1) := by
    have hzEven : Even (2 * (z 1 : ℤ)) :=
      even_iff_exists_two_mul.mpr ⟨z 1, by ring⟩
    have hrewrite : (n : ℤ) + z 0 - z 1 =
        ((n : ℤ) + z 0 + z 1) - 2 * z 1 := by ring
    rw [hrewrite]
    exact Even.sub hEven hzEven
  have hplusIlo : -(n : ℤ) ≤ z 0 + z 1 := by
    have h := (abs_le.mp hplus).1
    exact_mod_cast h
  have hplusIhi : z 0 + z 1 ≤ (n : ℤ) := by
    have h := (abs_le.mp hplus).2
    exact_mod_cast h
  have hminusIlo : -(n : ℤ) ≤ z 0 - z 1 := by
    have h := (abs_le.mp hminus).1
    exact_mod_cast h
  have hminusIhi : z 0 - z 1 ≤ (n : ℤ) := by
    have h := (abs_le.mp hminus).2
    exact_mod_cast h
  obtain ⟨p₁, hp₁⟩ := even_iff_exists_two_mul.mp hEven
  obtain ⟨p₂, hp₂⟩ := even_iff_exists_two_mul.mp hEven₂
  have hp₁lo : 0 ≤ p₁ := by omega
  have hp₁hi : p₁ ≤ n := by omega
  have hp₂lo : 0 ≤ p₂ := by omega
  have hp₂hi : p₂ ≤ n := by omega
  refine ⟨p₁.toNat, p₂.toNat, ?_, ?_, ?_, ?_⟩
  · have hcast := Int.toNat_of_nonneg hp₁lo
    have hle : (p₁.toNat : ℤ) ≤ n := by rw [hcast]; exact hp₁hi
    exact_mod_cast hle
  · have hcast := Int.toNat_of_nonneg hp₂lo
    have hle : (p₂.toNat : ℤ) ≤ n := by rw [hcast]; exact hp₂hi
    exact_mod_cast hle
  · have hcast := Int.toNat_of_nonneg hp₁lo
    rw [← hcast]
    omega
  · have hcast := Int.toNat_of_nonneg hp₂lo
    rw [← hcast]
    omega

private theorem eventually_exists_rotatedPairIndices
    (t₀ R : ℝ) (ht₀ : 0 < t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, t₀ * N ≤ n → n ≤ N →
      ∀ z : Site, Even ((n : ℤ) + z 0 + z 1) →
        ‖siteToPlane z‖ ≤ R * Real.sqrt N →
        ∃ j₁ j₂ : ℕ, j₁ ∈ Finset.range (n + 1) ∧
          j₂ ∈ Finset.range (n + 1) ∧
          2 * (j₁ : ℤ) = (n : ℤ) + z 0 + z 1 ∧
          2 * (j₂ : ℤ) = (n : ℤ) + z 0 - z 1 := by
  have hrootT : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hrootT.eventually_gt_atTop (2 * R / t₀)
  filter_upwards [hlarge, eventually_ge_atTop 1] with N hlargeN hN
  intro n hnLower hnUpper z hEven hz
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hRnonneg : 0 ≤ R := by
    by_contra hR
    have hRneg : R < 0 := lt_of_not_ge hR
    have hprod : R * Real.sqrt (N : ℝ) < 0 := mul_neg_of_neg_of_pos hRneg hsqrt
    have hnorm : 0 ≤ ‖siteToPlane z‖ := norm_nonneg _
    linarith
  have hcoeff : 2 * R < t₀ * Real.sqrt (N : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ ht₀).mp hlargeN
  have hscale : 2 * (R * Real.sqrt (N : ℝ)) ≤ t₀ * (N : ℝ) := by
    calc
      _ = (2 * R) * Real.sqrt (N : ℝ) := by ring
      _ ≤ (t₀ * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff.le hsqrt.le
      _ = t₀ * (Real.sqrt (N : ℝ)) ^ 2 := by ring
      _ = t₀ * (N : ℝ) := by rw [Real.sq_sqrt hNreal.le]
  have hcoordinates := siteToPlane_sum_difference_norm_bound z
  have hplus : |(z 0 : ℝ) + z 1| ≤ (n : ℝ) := by
    calc
      _ ≤ 2 * ‖siteToPlane z‖ := hcoordinates.1
      _ ≤ 2 * (R * Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left hz (by norm_num)
      _ ≤ t₀ * (N : ℝ) := hscale
      _ ≤ (n : ℝ) := by exact_mod_cast hnLower
  have hminus : |(z 0 : ℝ) - z 1| ≤ (n : ℝ) := by
    calc
      _ ≤ 2 * ‖siteToPlane z‖ := hcoordinates.2
      _ ≤ 2 * (R * Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left hz (by norm_num)
      _ ≤ t₀ * (N : ℝ) := hscale
      _ ≤ (n : ℝ) := by exact_mod_cast hnLower
  obtain ⟨j₁, j₂, hj₁, hj₂, h₁, h₂⟩ :=
    exists_rotatedPairIndices z hEven hplus hminus
  exact ⟨j₁, j₂, Finset.mem_range.mpr (Nat.lt_succ_of_le hj₁),
    Finset.mem_range.mpr (Nat.lt_succ_of_le hj₂), h₁, h₂⟩

/-- Short composition pair laws have the Gaussian heat profile, uniformly in
their block list and accessible spatial indices. -/
theorem eventually_hypergeometricBlockListPairLaw_heat_error_shortComposition
    (δ R ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ms : List ℕ, ms ≠ [] →
      ms.length ≤ spatialLogCutoff N ^ 2 → (∀ m ∈ ms, 0 < m) →
      δ * (N : ℝ) ≤ (ms.sum : ℝ) → (ms.sum : ℝ) ≤ N → ∀ z : Site,
      ∀ j₁ j₂ : ℕ, j₁ ∈ Finset.range (ms.sum + 1) →
        j₂ ∈ Finset.range (ms.sum + 1) →
        2 * (j₁ : ℤ) = (ms.sum : ℤ) + z 0 + z 1 →
        2 * (j₂ : ℤ) = (ms.sum : ℤ) + z 0 - z 1 →
        ‖siteToPlane z‖ ≤ R * Real.sqrt N →
        |(N / 4 : ℝ) * hypergeometricBlockListPairLaw ms j₁ j₂ -
          heatKernel ((ms.sum : ℝ) / (2 * N))
            ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| < ε := by
  have hhybrid := eventually_hypergeometricBlockListPairLaw_scaled_error_longBlockCutoff
    δ (ε / 3) hδ (by positivity)
  have hmixed := eventually_largeBlockGaussianListPairLaw_heat_error_mixedBlocks
    δ R (ε / 3) hδ (by positivity)
  filter_upwards [hhybrid, hmixed] with N hhybridN hmixedN
  intro ms hne hlen hpositive hsumLower hsumUpper z j₁ j₂ hj₁ hj₂ h₁ h₂ hz
  have hlenCeil : ms.length ≤ ⌈Real.log (N : ℝ)⌉₊ ^ 2 := by
    simpa only [spatialLogCutoff] using hlen
  have hpair := hhybridN ms hne hpositive hsumLower hlenCeil j₁ j₂ hj₁ hj₂
  let Q := largeBlockGaussianListPairLaw (spatialLogCutoff N ^ 10) ms j₁ j₂
  let H := heatKernel ((ms.sum : ℝ) / (2 * N))
    ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)
  have hpair' : (N : ℝ) *
      |hypergeometricBlockListPairLaw ms j₁ j₂ - Q| < ε / 3 := by
    simpa [Q, spatialLogCutoff] using hpair
  have hmix := hmixedN ms hne hlen hpositive hsumLower hsumUpper z j₁ j₂
    hj₁ hj₂ h₁ h₂ hz
  have hscaled :
      |(N / 4 : ℝ) * hypergeometricBlockListPairLaw ms j₁ j₂ -
        (N / 4 : ℝ) * Q| < ε / 12 := by
    rw [show (N / 4 : ℝ) * hypergeometricBlockListPairLaw ms j₁ j₂ -
        (N / 4 : ℝ) * Q = ((N : ℝ) / 4) *
          (hypergeometricBlockListPairLaw ms j₁ j₂ - Q) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 4)]
    calc
      _ = ((N : ℝ) *
          |hypergeometricBlockListPairLaw ms j₁ j₂ - Q|) / 4 := by ring
      _ < (ε / 3) / 4 := div_lt_div_of_pos_right hpair' (by norm_num)
      _ = ε / 12 := by ring
  calc
    |(N / 4 : ℝ) * hypergeometricBlockListPairLaw ms j₁ j₂ - H|
        ≤ |(N / 4 : ℝ) * hypergeometricBlockListPairLaw ms j₁ j₂ -
            (N / 4 : ℝ) * Q| + |(N / 4 : ℝ) * Q - H| := abs_sub_le _ _ _
    _ < ε / 12 + ε / 3 := add_lt_add hscaled hmix
    _ < ε := by linarith

/-- Summing all composition weights gives the scalar renewal mass. -/
theorem compositionScalarWeight_sum_eq_renewalMass (σ : ℝ) (n : ℕ) :
    (∑ c : Composition n, compositionScalarWeight σ c) =
      Renewal.renewalMass (fun r => σ * Renewal.returnWeight r) n := by
  have h := compositionScalarWeight_longLength_sum_eq_convolutionPower_tail σ n 0
  have hrange : Finset.range (n + 1) = Finset.Icc 0 n := by
    ext k
    simp
  simpa only [Renewal.renewalMass, ← hrange, Nat.zero_le, ite_true] using h

/-- The normalized total composition weight at integer time `n` is the scalar
renewal profile evaluated at `n / N`. -/
theorem compositionScalarWeight_scaled_sum_eq_criticalRenewalMassProfile
    (ϑ : ℝ) (N n : ℕ) (hN : 0 < N) :
    (N / Real.log N) *
        (∑ c : Composition n, compositionScalarWeight
          (criticalSigmaSq ϑ N) c) =
      Renewal.criticalRenewalMassProfile N (ϑ, (n : ℝ) / N) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod : (N : ℝ) * ((n : ℝ) / N) = n := by
    field_simp [hNreal.ne']
  rw [Renewal.criticalRenewalMassProfile]
  rw [hprod, Nat.floor_natCast, Renewal.criticalRenewalMass,
    compositionScalarWeight_sum_eq_renewalMass]

/-- The critical clock estimate controls the normalized tail of long
composition weights. -/
theorem exists_eventually_scaled_compositionScalarWeight_long_tail_le
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ n : ℕ, n ≤ N →
        (N / Real.log N) *
          (∑ c : Composition n,
            if ⌈Real.log (N : ℝ)⌉₊ ^ 2 ≤ c.length then
              compositionScalarWeight (criticalSigmaSq ϑ N) c else 0) ≤
          (N / Real.log N) * ((n : ℝ) + 1) * C *
            Real.exp (-4 * Real.log N) := by
  obtain ⟨C, hC, N₀, htail⟩ :=
    exists_eventually_scaled_criticalWindow_longComposition_tail_le
      A 1 hA (by norm_num)
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN ϑ hϑ n hn
  have hn' : n ≤ ⌊(1 : ℝ) * N⌋₊ := by simpa using hn
  have htail' := htail N hN ϑ hϑ n hn'
  rw [compositionScalarWeight_longLength_sum_eq_criticalWindowTail
    (criticalSigmaSq ϑ N) N n (⌈Real.log (N : ℝ)⌉₊ ^ 2) hn]
  simpa using htail'

/-- The scalar mass profile converges uniformly on the parameter and positive-time
box used by the spatial renewal limit. -/
private theorem eventually_criticalRenewalMassProfile_error_box
    (A t₀ ε : ℝ) (ht₀ : 0 < t₀) (ht₀1 : t₀ ≤ 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ t ∈ Set.Icc t₀ 1,
      |Renewal.criticalRenewalMassProfile N (ϑ, t) -
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t| < ε := by
  let δ := min t₀ 1
  have hδeq : δ = t₀ := min_eq_left ht₀1
  have hδ : 0 < δ := by rw [hδeq]; exact ht₀
  have hprofile := Renewal.tendstoUniformlyOn_criticalRenewalMassProfile_box
    (a := -A) (b := A) hδ
  have hclose := (Metric.tendstoUniformlyOn_iff.mp hprofile) ε hε
  filter_upwards [hclose] with N hN
  intro ϑ hϑ t ht
  have ht' : t ∈ Set.Icc δ 1 := by rw [hδeq]; exact ht
  have hpoint := hN (ϑ, t) ⟨hϑ, ht'⟩
  simpa [Real.dist_eq, abs_sub_comm] using hpoint

/-- The spatial renewal has the scalar renewal density times the planar heat
profile, uniformly on compact critical-parameter, positive-time, and diffusive
space windows. -/
theorem spatialRenewal_localLimit (A t₀ R : ℝ) (ht₀ : 0 < t₀) (ht₀1 : t₀ ≤ 1) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ n : ℕ,
      t₀ * N ≤ n → n ≤ N → ∀ z : Site,
      Even ((n : ℤ) + z 0 + z 1) → ‖siteToPlane z‖ ≤ R * Real.sqrt N →
        |(N / 4 : ℝ) * (N / Real.log N) *
            Collision.spatialRenewal (criticalSigmaSq ϑ N) n z -
          DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (n / N) *
            heatKernel (n / (2 * N))
              ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| ≤ ε := by
  intro ε hε
  by_cases hA : 0 ≤ A
  · obtain ⟨Ctail, hCtail, Ntail, htail⟩ :=
      exists_eventually_scaled_compositionScalarWeight_long_tail_le A hA
    let B : ℝ := A + |Real.eulerMascheroniConstant|
    let D : ℝ := Real.exp 1 / t₀ * Real.exp (Real.exp (B + 1))
    let H₀ : ℝ := (Real.pi * t₀)⁻¹
    let η : ℝ := ε / (8 * (D + 1))
    let ηp : ℝ := min 1 (ε / (8 * (H₀ + 1)))
    let Clong : ℝ := 2 * Ctail * (1 / 4 + H₀)
    have hD : 0 < D := by dsimp [D]; positivity
    have hH₀ : 0 < H₀ := by dsimp [H₀]; positivity
    have hη : 0 < η := by dsimp [η]; positivity
    have hηp : 0 < ηp := by
      dsimp [ηp]
      exact lt_min (by norm_num) (by positivity)
    have hηpOne : ηp ≤ 1 := by exact min_le_left _ _
    have hηpH₀ : ηp * H₀ ≤ ε / 8 := by
      have hratio : H₀ / (H₀ + 1) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith)
      calc
        ηp * H₀ ≤ (ε / (8 * (H₀ + 1))) * H₀ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hH₀.le
        _ = (ε / 8) * (H₀ / (H₀ + 1)) := by field_simp
        _ ≤ (ε / 8) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = ε / 8 := by ring
    have hηmass : η * (D + 1) = ε / 8 := by
      dsimp [η]
      have hden : 8 * (D + 1) ≠ 0 := by positivity
      field_simp [hden]
    have hClong : 0 < Clong := by dsimp [Clong]; positivity
    have hlogEvent : ∀ᶠ N : ℕ in atTop, 1 < Real.log (N : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 1
    have hdecayEvent : ∀ᶠ N : ℕ in atTop,
        Clong * (N : ℝ) ^ 3 * Real.exp (-4 * Real.log (N : ℝ)) < ε / 8 := by
      have hdecay := natCube_mul_exp_neg_four_log_tendsto_zero.const_mul Clong
      have hlim : Clong * 0 < ε / 8 := by simp; positivity
      filter_upwards [hdecay.eventually (Iio_mem_nhds hlim)]
        with N hN
      simpa [mul_comm, mul_left_comm, mul_assoc] using hN
    have hindicesEvent := eventually_exists_rotatedPairIndices t₀ R ht₀
    have hpairEvent := eventually_hypergeometricBlockListPairLaw_heat_error_shortComposition
      t₀ R η ht₀ hη
    have hprofileEvent := eventually_criticalRenewalMassProfile_error_box
      A t₀ ηp ht₀ ht₀1 hηp
    have hσEvent := Renewal.criticalSigmaSq_eventually_pos (-A)
    filter_upwards [hindicesEvent, hpairEvent, hprofileEvent, hσEvent,
        hlogEvent, hdecayEvent, eventually_ge_atTop Ntail,
        eventually_ge_atTop 2] with N hindicesN hpairN hprofileN hσN hlogN
          hdecayN hNtail hNtwo
    intro ϑ hϑ n hnLower hnUpper z hEven hz
    have hNreal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN2 : 2 ≤ N := hNtwo
    have hNcast : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hlog : 0 < Real.log (N : ℝ) := by linarith
    have hlogOne : 1 ≤ Real.log (N : ℝ) := le_of_lt hlogN
    have hα : 0 < (N : ℝ) / Real.log N := div_pos hNreal hlog
    have hαle : (N : ℝ) / Real.log N ≤ N := by
      apply (div_le_iff₀ hlog).2
      nlinarith
    have hnLowerR : t₀ * (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnLower
    have hnUpperR : (n : ℝ) ≤ N := by exact_mod_cast hnUpper
    have htimeLower : t₀ ≤ (n : ℝ) / N :=
      (le_div_iff₀ hNreal).2 hnLowerR
    have htimeUpper : (n : ℝ) / N ≤ 1 := (div_le_one hNreal).2 hnUpperR
    have htime : (n : ℝ) / N ∈ Set.Icc t₀ 1 := ⟨htimeLower, htimeUpper⟩
    have hσbase : 0 < criticalSigmaSq (-A) N := hσN
    have hσ : 0 ≤ criticalSigmaSq ϑ N := by
      exact hσbase.le.trans (Renewal.criticalSigmaSq_mono_parameter hN2 hϑ.1)
    have hnPosR : 0 < (n : ℝ) := (mul_pos ht₀ hNreal).trans_le hnLowerR
    have hnPos : 1 ≤ n := by
      have hnNat : 0 < n := by exact_mod_cast hnPosR
      omega
    obtain ⟨j₁, j₂, hj₁, hj₂, h₁, h₂⟩ :=
      hindicesN n hnLower hnUpper z hEven hz
    have hj₁n : j₁ ≤ n := by simp only [Finset.mem_range] at hj₁; omega
    have hj₂n : j₂ ≤ n := by simp only [Finset.mem_range] at hj₂; omega
    let K : ℕ := spatialLogCutoff N ^ 2
    let σ : ℝ := criticalSigmaSq ϑ N
    let α : ℝ := (N : ℝ) / Real.log N
    let β : ℝ := (N : ℝ) / 4
    let H : ℝ := heatKernel ((n : ℝ) / (2 * N))
      ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)
    let S : ℝ := DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant)
      ((n : ℝ) / N)
    let Wtotal : ℝ := ∑ c : Composition n, compositionScalarWeight σ c
    let Wshort : ℝ := ∑ c : Composition n,
      if c.length < K then compositionScalarWeight σ c else 0
    let Wlong : ℝ := ∑ c : Composition n,
      if K ≤ c.length then compositionScalarWeight σ c else 0
    let f : Composition n → ℝ := fun c =>
      β * hypergeometricBlockListPairLaw c.blocks j₁ j₂
    let Q : Composition n → ℝ := fun c => compositionScalarWeight σ c * f c
    let Tshort : ℝ := ∑ c : Composition n, if c.length < K then Q c else 0
    let Tlong : ℝ := ∑ c : Composition n, if K ≤ c.length then Q c else 0
    have hBparam : ϑ - Real.eulerMascheroniConstant ≤ B := by
      dsimp [B]
      linarith [neg_le_abs Real.eulerMascheroniConstant, hϑ.2]
    have hscalar : S ≤ D := by
      dsimp [S, D]
      calc
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N)
            ≤ Real.exp 1 / ((n : ℝ) / N) *
                Real.exp (Real.exp (B + 1) * ((n : ℝ) / N)) :=
              DeltaBose.scalarDensity_le_exp hBparam (lt_of_lt_of_le ht₀ htimeLower)
        _ ≤ Real.exp 1 / t₀ * Real.exp (Real.exp (B + 1)) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_left (Real.exp_nonneg _) ht₀ htimeLower
          · exact Real.exp_le_exp.mpr
              (mul_le_of_le_one_right (by positivity) htimeUpper)
          · positivity
          · positivity
    have hhalfTime : t₀ / 2 ≤ (n : ℝ) / (2 * N) := by
      calc
        t₀ / 2 ≤ ((n : ℝ) / N) / 2 := by linarith [htimeLower]
        _ = (n : ℝ) / (2 * N) := by field_simp [hNreal.ne']
    have hHnonneg : 0 ≤ H := by
      dsimp [H]
      exact heatKernel_nonneg (by positivity : 0 ≤ (n : ℝ) / (2 * N)) _
    have hHbound : H ≤ H₀ := by
      dsimp [H, H₀]
      exact heatKernel_le_t0_inverse ht₀ hhalfTime _
    have hweight : ∀ c : Composition n, 0 ≤ compositionScalarWeight σ c :=
      fun c => compositionScalarWeight_nonneg σ hσ c
    have hpairLe : ∀ c : Composition n,
        hypergeometricBlockListPairLaw c.blocks j₁ j₂ ≤ 1 := by
      intro c
      have hj₁c : j₁ ≤ c.blocks.sum := by rw [c.blocks_sum]; exact hj₁n
      have hj₂c : j₂ ≤ c.blocks.sum := by rw [c.blocks_sum]; exact hj₂n
      exact hypergeometricBlockListPairLaw_le_one c.blocks j₁ j₂ hj₁c hj₂c
    have hpairNonneg : ∀ c : Composition n,
        0 ≤ hypergeometricBlockListPairLaw c.blocks j₁ j₂ := by
      intro c
      exact mul_nonneg
        (hypergeometricBlockListLaw_nonneg c.blocks j₁)
        (hypergeometricBlockListLaw_nonneg c.blocks j₂)
    have hβ : 0 ≤ β := by dsimp [β]; positivity
    have hflong : ∀ c : Composition n, |f c - H| ≤ β + H₀ := by
      intro c
      have hfn : 0 ≤ f c := by
        dsimp [f]
        exact mul_nonneg hβ (hpairNonneg c)
      have hfupper : f c ≤ β := by
        dsimp [f]
        calc
          _ ≤ β * 1 := mul_le_mul_of_nonneg_left (hpairLe c) hβ
          _ = β := by ring
      calc
        |f c - H| = |f c + -H| := by rw [sub_eq_add_neg]
        _ ≤ |f c| + |-H| := abs_add_le _ _
        _ = f c + H := by rw [abs_of_nonneg hfn, abs_neg, abs_of_nonneg hHnonneg]
        _ ≤ β + H₀ := add_le_add hfupper hHbound
    have hshortPoint : ∀ c : Composition n, c.length < K → |f c - H| ≤ η := by
      intro c hcshort
      have hlen : c.blocks.length ≤ spatialLogCutoff N ^ 2 := by
        simpa [Composition.length, K] using (Nat.le_of_lt hcshort)
      have hsumLower : t₀ * (N : ℝ) ≤ (c.blocks.sum : ℝ) := by
        simpa only [c.blocks_sum] using hnLowerR
      have hsumUpper : (c.blocks.sum : ℝ) ≤ N := by
        simpa only [c.blocks_sum] using hnUpperR
      have hj₁c : j₁ ∈ Finset.range (c.blocks.sum + 1) := by
        simpa only [c.blocks_sum] using hj₁
      have hj₂c : j₂ ∈ Finset.range (c.blocks.sum + 1) := by
        simpa only [c.blocks_sum] using hj₂
      have h₁c : 2 * (j₁ : ℤ) = (c.blocks.sum : ℤ) + z 0 + z 1 := by
        simpa only [c.blocks_sum] using h₁
      have h₂c : 2 * (j₂ : ℤ) = (c.blocks.sum : ℤ) + z 0 - z 1 := by
        simpa only [c.blocks_sum] using h₂
      have hcne : c.blocks ≠ [] := by
        intro hc
        have hs := c.blocks_sum
        simp [hc] at hs
        omega
      have hpos : ∀ m ∈ c.blocks, 0 < m := by
        intro m hm
        exact c.blocks_pos hm
      have hlocal := hpairN c.blocks hcne hlen hpos hsumLower hsumUpper
        z j₁ j₂ hj₁c hj₂c h₁c h₂c hz
      simpa [f, β, H] using (le_of_lt hlocal)
    have hshortErr := abs_sum_short_weight_error
      (P := fun c : Composition n => c.length < K)
      (w := fun c => compositionScalarWeight σ c) (f := f) (H := H) (η := η)
      hweight hshortPoint
    have hlongErr := abs_sum_short_weight_error
      (P := fun c : Composition n => K ≤ c.length)
      (w := fun c => compositionScalarWeight σ c) (f := f) (H := H)
      (η := β + H₀) hweight (fun c _ => hflong c)
    have hWtotalProfile : α * Wtotal = Renewal.criticalRenewalMassProfile N
        (ϑ, (n : ℝ) / N) := by
      simpa [α, Wtotal, σ] using
        compositionScalarWeight_scaled_sum_eq_criticalRenewalMassProfile
          ϑ N n (by omega)
    have hprofileGap : |α * Wtotal - S| < ηp := by
      rw [hWtotalProfile]
      exact hprofileN ϑ hϑ ((n : ℝ) / N) htime
    have hmassUpper : α * Wtotal ≤ D + 1 := by
      have hgap := (abs_lt.mp hprofileGap).2
      have hηp := hηpOne
      dsimp [S] at hscalar
      linarith
    have hWsplit := sum_short_long_split
      (fun c : Composition n => c.length) K
      (fun c => compositionScalarWeight σ c)
    have hWtotalSplit : Wtotal = Wshort + Wlong := by
      simpa [Wtotal, Wshort, Wlong, K] using hWsplit
    have hWshortNonneg : 0 ≤ Wshort := by
      dsimp [Wshort]
      apply Finset.sum_nonneg
      intro c hc
      split_ifs
      · exact hweight c
      · exact le_rfl
    have hWlongNonneg : 0 ≤ Wlong := by
      dsimp [Wlong]
      apply Finset.sum_nonneg
      intro c hc
      split_ifs
      · exact hweight c
      · exact le_rfl
    have hWshortLe : α * Wshort ≤ α * Wtotal := by
      rw [hWtotalSplit]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hWlongNonneg) hα.le
    have hηshortMass : η * (α * Wshort) ≤ ε / 8 := by
      calc
        η * (α * Wshort) ≤ η * (α * Wtotal) :=
          mul_le_mul_of_nonneg_left hWshortLe hη.le
        _ ≤ η * (D + 1) := mul_le_mul_of_nonneg_left hmassUpper hη.le
        _ = ε / 8 := hηmass
    have hshortErrScaled :
        |α * Tshort - H * (α * Wshort)| ≤ ε / 8 := by
      have hfactor :
          |α * Tshort - H * (α * Wshort)| = α * |Tshort - H * Wshort| := by
        rw [show α * Tshort - H * (α * Wshort) = α * (Tshort - H * Wshort) by ring,
          abs_mul, abs_of_nonneg hα.le]
      calc
        _ = α * |Tshort - H * Wshort| := hfactor
        _ ≤ α * (η * Wshort) := mul_le_mul_of_nonneg_left hshortErr hα.le
        _ = η * (α * Wshort) := by ring
        _ ≤ ε / 8 := hηshortMass
    have htailN' := htail N hNtail ϑ hϑ n hnUpper
    have hWlongTail :
        α * Wlong ≤ α * ((n : ℝ) + 1) * Ctail *
          Real.exp (-4 * Real.log (N : ℝ)) :=
      htail N hNtail ϑ hϑ n hnUpper
    have hnplus : (n : ℝ) + 1 ≤ 2 * (N : ℝ) := by nlinarith
    have hH₀leN : H₀ ≤ (N : ℝ) * H₀ := by
      calc
        H₀ = 1 * H₀ := by ring
        _ ≤ (N : ℝ) * H₀ := mul_le_mul_of_nonneg_right hNcast hH₀.le
    have hbetaH : β + H₀ ≤ (N : ℝ) * (1 / 4 + H₀) := by
      calc
        β + H₀ = H₀ + β := by ring
        _ ≤ (N : ℝ) * H₀ + β := add_le_add hH₀leN le_rfl
        _ = (N : ℝ) * (1 / 4 + H₀) := by dsimp [β]; ring
    have hLongProd :
        (β + H₀) * (α * Wlong) ≤
          Clong * (N : ℝ) ^ 3 * Real.exp (-4 * Real.log (N : ℝ)) := by
      have hsecond :
          α * ((n : ℝ) + 1) * Ctail * Real.exp (-4 * Real.log (N : ℝ)) ≤
            (N : ℝ) * (2 * (N : ℝ)) * Ctail *
              Real.exp (-4 * Real.log (N : ℝ)) := by
        calc
          _ = ((α * ((n : ℝ) + 1)) *
              (Ctail * Real.exp (-4 * Real.log (N : ℝ)))) := by ring
          _ ≤ (((N : ℝ) * ((n : ℝ) + 1)) *
              (Ctail * Real.exp (-4 * Real.log (N : ℝ)))) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hαle (by positivity)) (by positivity)
          _ ≤ (((N : ℝ) * (2 * (N : ℝ))) *
              (Ctail * Real.exp (-4 * Real.log (N : ℝ)))) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hnplus hNreal.le) (by positivity)
          _ = (N : ℝ) * (2 * (N : ℝ)) * Ctail *
              Real.exp (-4 * Real.log (N : ℝ)) := by ring
      calc
        _ ≤ (β + H₀) *
            (α * ((n : ℝ) + 1) * Ctail *
              Real.exp (-4 * Real.log (N : ℝ))) :=
              mul_le_mul_of_nonneg_left hWlongTail (by positivity)
        _ ≤ ((N : ℝ) * (1 / 4 + H₀)) *
            ((N : ℝ) * (2 * (N : ℝ)) * Ctail *
              Real.exp (-4 * Real.log (N : ℝ))) := by
              exact mul_le_mul hbetaH hsecond (by positivity) (by positivity)
        _ = Clong * (N : ℝ) ^ 3 * Real.exp (-4 * Real.log (N : ℝ)) := by
              dsimp [Clong]
              ring
    have hlongErrScaled :
        |α * Tlong - H * (α * Wlong)| < ε / 8 := by
      have hfactor :
          |α * Tlong - H * (α * Wlong)| = α * |Tlong - H * Wlong| := by
        rw [show α * Tlong - H * (α * Wlong) = α * (Tlong - H * Wlong) by ring,
          abs_mul, abs_of_nonneg hα.le]
      calc
        _ = α * |Tlong - H * Wlong| := hfactor
        _ ≤ α * ((β + H₀) * Wlong) := mul_le_mul_of_nonneg_left hlongErr hα.le
        _ = (β + H₀) * (α * Wlong) := by ring
        _ ≤ Clong * (N : ℝ) ^ 3 * Real.exp (-4 * Real.log (N : ℝ)) := hLongProd
        _ < ε / 8 := hdecayN
    have hTsplit := sum_short_long_split
      (fun c : Composition n => c.length) K Q
    have hTsplit' :
        (∑ c : Composition n, Q c) = Tshort + Tlong := by
      simpa [Tshort, Tlong] using hTsplit
    have hβrenewal :
        β * Collision.spatialRenewal σ n z = ∑ c : Composition n, Q c := by
      rw [spatialRenewal_eq_compositionScalarWeight_pairLaw σ hnPos z j₁ j₂ h₁ h₂]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      dsimp [Q, f]
      ring
    have hactual :
        β * α * Collision.spatialRenewal σ n z = α * (Tshort + Tlong) := by
      calc
        _ = α * (β * Collision.spatialRenewal σ n z) := by ring
        _ = α * (∑ c : Composition n, Q c) := by rw [hβrenewal]
        _ = α * (Tshort + Tlong) := by rw [hTsplit']
    have hdecomp :
        α * (Tshort + Tlong) - H * (α * Wtotal) =
          (α * Tshort - H * (α * Wshort)) +
            (α * Tlong - H * (α * Wlong)) := by
      rw [hWtotalSplit]
      ring
    have happrox :
        |α * (Tshort + Tlong) - H * (α * Wtotal)| ≤ ε / 4 := by
      rw [hdecomp]
      calc
        _ ≤ |α * Tshort - H * (α * Wshort)| +
              |α * Tlong - H * (α * Wlong)| := abs_add_le _ _
        _ ≤ ε / 8 + ε / 8 := add_le_add hshortErrScaled hlongErrScaled.le
        _ = ε / 4 := by ring
    have hprofileErr : |H * (α * Wtotal) - S * H| ≤ ε / 8 := by
      rw [show H * (α * Wtotal) - S * H = H * (α * Wtotal - S) by ring,
        abs_mul, abs_of_nonneg hHnonneg]
      calc
        H * |α * Wtotal - S| ≤ H₀ * ηp :=
          mul_le_mul hHbound hprofileGap.le (abs_nonneg _) hH₀.le
        _ ≤ ε / 8 := by simpa [mul_comm] using hηpH₀
    have hfinal :
        |α * (Tshort + Tlong) - S * H| ≤ ε := by
      calc
        _ ≤ |α * (Tshort + Tlong) - H * (α * Wtotal)| +
              |H * (α * Wtotal) - S * H| := abs_sub_le _ _ _
        _ ≤ ε / 4 + ε / 8 := add_le_add happrox hprofileErr
        _ ≤ ε := by linarith
    simpa [α, β, σ, H, S, hactual, mul_assoc, mul_left_comm, mul_comm] using hfinal
  · filter_upwards [Filter.Eventually.of_forall (fun _ : ℕ => True.intro)] with N _
    intro ϑ hϑ n hnLower hnUpper z hEven hz
    have hcontra : -A ≤ A := hϑ.1.trans hϑ.2
    linarith


end Critical2DKPZ.SHF.Moments

end
