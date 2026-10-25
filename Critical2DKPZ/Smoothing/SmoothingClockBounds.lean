/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # Clock comparisons for the lattice approximation estimate rescaling -/

@[expose] public section

open Filter
open scoped Topology

namespace Critical2DKPZ.Smoothing

/-- A difference of comparable even ceilings is even. -/
theorem evenCeil_sub_even {s t : ℝ} (hst : s ≤ t) :
    Even (evenCeil t - evenCeil s) := by
  have hmono : evenCeil s ≤ evenCeil t := evenCeil_mono hst
  obtain ⟨a, ha⟩ := evenCeil_even t
  obtain ⟨b, hb⟩ := evenCeil_even s
  refine ⟨a - b, ?_⟩
  omega

/-- After diffusive rescaling, the even-ceiling horizon is comparable to `N (T - t)`. -/
theorem c11_horizon_rescale_bounds {t T a b : ℝ} (ht : 0 ≤ t) (ha : 0 < a)
    (hab : a ≤ b) (hgap : T - t ∈ Set.Icc a b) :
    ∀ᶠ N : ℕ in atTop,
      let M := evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t)
      a / 2 * (N : ℝ) ≤ (M : ℝ) ∧ (M : ℝ) ≤ 2 * b * (N : ℝ) := by
  let N₀ : ℕ := max ⌈4 / a⌉₊ ⌈2 / b⌉₊
  filter_upwards [eventually_ge_atTop N₀] with N hN
  dsimp only
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hNlower : 4 / a ≤ (N : ℝ) := by
    calc
      4 / a ≤ (⌈4 / a⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (N₀ : ℝ) := by
        exact_mod_cast (le_max_left ⌈4 / a⌉₊ ⌈2 / b⌉₊)
      _ ≤ N := by exact_mod_cast hN
  have hNupper : 2 / b ≤ (N : ℝ) := by
    calc
      2 / b ≤ (⌈2 / b⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (N₀ : ℝ) := by
        exact_mod_cast (le_max_right ⌈4 / a⌉₊ ⌈2 / b⌉₊)
      _ ≤ N := by exact_mod_cast hN
  have hT : 0 ≤ T := by
    rcases hgap with ⟨hgap, _⟩
    linarith
  have htime : (N : ℝ) * t ≤ (N : ℝ) * T :=
    mul_le_mul_of_nonneg_left (by linarith [hgap.1]) (Nat.cast_nonneg N)
  have hceil : evenCeil ((N : ℝ) * t) ≤ evenCeil ((N : ℝ) * T) :=
    evenCeil_mono htime
  have hMcast :
      ((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) =
        evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) := by
    simp [Nat.cast_sub hceil]
  have hMerror :
      |((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) -
          (N : ℝ) * (T - t)| < 2 := by
    have hround := evenCeil_duration_error (s := (N : ℝ) * t)
      (t := (N : ℝ) * T) (mul_nonneg (Nat.cast_nonneg N) ht)
      (mul_nonneg (Nat.cast_nonneg N) hT)
    rw [hMcast]
    convert hround using 1; ring_nf
  have hMlo : (N : ℝ) * (T - t) - 2 <
      ((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) := by
    have h := (abs_lt.mp hMerror).1
    linarith
  have hMhi :
      ((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) <
        (N : ℝ) * (T - t) + 2 := by
    have h := (abs_lt.mp hMerror).2
    linarith
  constructor
  · have hNapos : 4 ≤ a * (N : ℝ) := by
      apply (div_le_iff₀ ha).mp at hNlower
      nlinarith only [hNlower]
    have hgaplo := hgap.1
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [hMlo]
  · have hNbpos : 2 ≤ b * (N : ℝ) := by
      apply (div_le_iff₀ hb).mp at hNupper
      nlinarith only [hNupper]
    have hgaphigh := hgap.2
    nlinarith [hMhi]

/-- The original and rescaled smoothing clocks differ by at most six integer time steps. -/
theorem c11_widths_within_six (N : ℕ) {t T δ a : ℝ}
    (ht : 0 ≤ t) (ha : 0 < a) (hgap : a ≤ T - t)
    (hδ : 0 < δ) (hδa : δ ≤ a) :
    let M : ℕ := evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t)
    let δ' : ℝ := δ / (T - t)
    ((evenCeil (δ * (N : ℝ)) : ℤ) ≤ (evenCeil (δ' * M) : ℤ) + 6) ∧
      ((evenCeil (δ' * M) : ℤ) ≤ (evenCeil (δ * (N : ℝ)) : ℤ) + 6) ∧
      ((evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t) : ℤ) ≤
        (evenCeil (δ' * M) : ℤ) + 6) ∧
      ((evenCeil (δ' * M) : ℤ) ≤
        (evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t) : ℤ) + 6) := by
  dsimp only
  let M : ℕ := evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t)
  let δ' : ℝ := δ / (T - t)
  have hT : 0 ≤ T := by linarith
  have htime : (N : ℝ) * t ≤ (N : ℝ) * T :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)
  have hceil : evenCeil ((N : ℝ) * t) ≤ evenCeil ((N : ℝ) * T) :=
    evenCeil_mono htime
  have hMcast : (M : ℝ) =
      (evenCeil ((N : ℝ) * T) : ℝ) - evenCeil ((N : ℝ) * t) := by
    simp [M, Nat.cast_sub hceil]
  have hMerror : |(M : ℝ) - (N : ℝ) * (T - t)| < 2 := by
    have hround := evenCeil_duration_error (s := (N : ℝ) * t)
      (t := (N : ℝ) * T) (mul_nonneg (Nat.cast_nonneg N) ht)
      (mul_nonneg (Nat.cast_nonneg N) hT)
    rw [hMcast]
    convert hround using 1; ring_nf
  have hgappos : 0 < T - t := lt_of_lt_of_le ha hgap
  have hδ'pos : 0 < δ' := div_pos hδ hgappos
  have hδ'le : δ' ≤ 1 := (div_le_one hgappos).2 (hδa.trans hgap)
  have hδ'Mnonneg : 0 ≤ δ' * (M : ℝ) := mul_nonneg hδ'pos.le (Nat.cast_nonneg M)
  have hδNnonneg : 0 ≤ δ * (N : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg N)
  have hδ'Mclose : |δ' * (M : ℝ) - δ * (N : ℝ)| < 2 := by
    have hfactor : δ' * (T - t) = δ := by
      dsimp [δ']
      field_simp
    have hrewrite : δ' * (M : ℝ) - δ * (N : ℝ) =
        δ' * ((M : ℝ) - (N : ℝ) * (T - t)) := by
      rw [mul_sub, ← hfactor]
      ring_nf
    rw [hrewrite, abs_mul, abs_of_nonneg hδ'pos.le]
    nlinarith [hMerror, hδ'le]
  have hceilδ'M := evenCeil_error hδ'Mnonneg
  have hceilδN := evenCeil_error hδNnonneg
  have hceilδMclose :
      |(evenCeil (δ' * (M : ℝ)) : ℝ) - evenCeil (δ * (N : ℝ))| < 6 := by
    let A : ℝ := evenCeil (δ' * (M : ℝ))
    let B : ℝ := δ' * (M : ℝ)
    let C : ℝ := δ * (N : ℝ)
    let D : ℝ := evenCeil (δ * (N : ℝ))
    have hleft :
        |A - B| < 2 := by
      dsimp [A, B]
      rw [abs_of_nonneg hceilδ'M.1]
      exact hceilδ'M.2
    have hright :
        |D - C| < 2 := by
      dsimp [D, C]
      rw [abs_of_nonneg hceilδN.1]
      exact hceilδN.2
    have htriAC : |A - D| ≤ |A - B| + |B - D| := abs_sub_le A B D
    have htriBD : |B - D| ≤ |B - C| + |C - D| := abs_sub_le B C D
    have hright' : |C - D| < 2 := by simpa [abs_sub_comm] using hright
    calc
      _ = |A - D| := by rfl
      _ ≤ |A - B| + (|B - C| + |C - D|) := by
            calc
              |A - D| ≤ |A - B| + |B - D| := htriAC
              _ ≤ |A - B| + (|B - C| + |C - D|) := by linarith [htriBD]
      _ < 6 := by nlinarith [hleft, hδ'Mclose, hright']
  have hceilstep : |(evenCeil (δ' * (M : ℝ)) : ℤ) - evenCeil (δ * (N : ℝ))| < 6 := by
    exact_mod_cast hceilδMclose
  have hfinebase :
      |((evenCeil ((N : ℝ) * (t + δ)) : ℝ) - evenCeil ((N : ℝ) * t)) -
          δ * (N : ℝ)| < 2 := by
    have hround := evenCeil_duration_error (s := (N : ℝ) * t)
      (t := (N : ℝ) * (t + δ)) (mul_nonneg (Nat.cast_nonneg N) ht)
      (mul_nonneg (Nat.cast_nonneg N) (by linarith))
    convert hround using 1; ring_nf
  have hfine :
      |(evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t) : ℝ) -
          evenCeil (δ' * (M : ℝ))| < 6 := by
    let A : ℝ := evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t)
    let B : ℝ := δ * (N : ℝ)
    let C : ℝ := δ' * (M : ℝ)
    let D : ℝ := evenCeil (δ' * (M : ℝ))
    have hceilδ' : |evenCeil (δ' * (M : ℝ)) - δ' * (M : ℝ)| < 2 := by
      rw [abs_of_nonneg hceilδ'M.1]
      exact hceilδ'M.2
    have hbase : |A - B| < 2 := by simpa [A, B] using hfinebase
    have hclose : |B - C| < 2 := by simpa [B, C, abs_sub_comm] using hδ'Mclose
    have hceil' : |C - D| < 2 := by simpa [C, D, abs_sub_comm] using hceilδ'
    have htriAC : |A - D| ≤ |A - B| + |B - D| := abs_sub_le A B D
    have htriBD : |B - D| ≤ |B - C| + |C - D| := abs_sub_le B C D
    calc
      _ = |A - D| := by rfl
      _ ≤ |A - B| + (|B - C| + |C - D|) := by
            calc
              |A - D| ≤ |A - B| + |B - D| := htriAC
              _ ≤ |A - B| + (|B - C| + |C - D|) := by linarith [htriBD]
      _ < 6 := by nlinarith [hbase, hclose, hceil']
  have hfinestep :
      |(evenCeil (δ' * (M : ℝ)) : ℤ) -
        (evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t) : ℤ)| < 6 := by
    have hwidthCast :
        ((evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t) : ℤ) : ℝ) =
          (evenCeil ((N : ℝ) * (t + δ)) : ℝ) - evenCeil ((N : ℝ) * t) := by
      norm_cast
    have hreal :
        |(evenCeil (δ' * (M : ℝ)) : ℝ) -
          (((evenCeil ((N : ℝ) * (t + δ)) - evenCeil ((N : ℝ) * t) : ℤ) : ℝ))| < 6 := by
      rw [hwidthCast]
      simpa only [abs_sub_comm] using hfine
    exact_mod_cast hreal
  have hceilBounds := abs_lt.mp hceilstep
  have hfineBounds := abs_lt.mp hfinestep
  constructor
  · change (evenCeil (δ * (N : ℝ)) : ℤ) ≤
      (evenCeil (δ' * (M : ℝ)) : ℤ) + 6
    omega
  constructor
  · change (evenCeil (δ' * (M : ℝ)) : ℤ) ≤
      (evenCeil (δ * (N : ℝ)) : ℤ) + 6
    omega
  constructor
  · change (evenCeil ((N : ℝ) * (t + δ)) : ℤ) -
      evenCeil ((N : ℝ) * t) ≤ (evenCeil (δ' * (M : ℝ)) : ℤ) + 6
    omega
  · change (evenCeil (δ' * (M : ℝ)) : ℤ) ≤
      (evenCeil ((N : ℝ) * (t + δ)) : ℤ) - evenCeil ((N : ℝ) * t) + 6
    omega

end Critical2DKPZ.Smoothing

end
