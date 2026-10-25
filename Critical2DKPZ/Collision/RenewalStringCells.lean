/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.RenewalStringBase
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.Tactic

/-!
# Renewal pair cells and finite-string comparisons

Shifted cells compare discrete renewal strings with scalar-density integrals.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Collision

/-- The subcell used for a pair of renewal indices. Equal indices use a triangle
to capture the zero-gap logarithmic mass; distinct indices use two half-cells. -/
def renewalStringPairCell (N a b : ℕ) : Set (ℝ × ℝ) :=
  if a = b then
    {p | ((a : ℝ) - 1 / 2) / N < p.1 ∧ p.1 < ((a : ℝ) - 1 / 4) / N ∧
      p.1 < p.2 ∧ p.2 < p.1 + (1 : ℝ) / (4 * (N : ℝ))}
  else
    {p | ((a : ℝ) - 1 / 2) / N < p.1 ∧ p.1 < (a : ℝ) / N ∧
      (b : ℝ) / N < p.2 ∧ p.2 < ((b : ℝ) + 1 / 2) / N}

/-- Product cell for a finite string of renewal pairs. -/
def renewalStringPairBox (N m : ℕ) (a b : Fin (m + 1) → ℕ) :
    Set (Fin (m + 1) → ℝ × ℝ) :=
  Set.univ.pi (fun j => renewalStringPairCell N (a j) (b j))

/-- The continuum rational factor attached to a renewal string. -/
def renewalStringPairBoxRational (m : ℕ) (p : Fin (m + 1) → ℝ × ℝ) : ℝ :=
  (p 0).1⁻¹ * ∏ j : Fin m,
    (p j.castSucc).2 / ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))

/-- The product of scalar collision densities along a renewal string. -/
def renewalStringPairBoxDensity (θ : ℝ) (m : ℕ)
    (p : Fin (m + 1) → ℝ × ℝ) : ℝ :=
  ∏ j : Fin (m + 1), DeltaBose.scalarDensity θ ((p j).2 - (p j).1)

/-- Each renewal string pair cell is measurable. -/
theorem measurableSet_renewalStringPairCell (N a b : ℕ) :
    MeasurableSet (renewalStringPairCell N a b) := by
  by_cases hab : a = b <;> simp [renewalStringPairCell, hab] <;> measurability

/-- Each finite renewal string pair box is measurable. -/
theorem measurableSet_renewalStringPairBox (N m : ℕ)
    (a b : Fin (m + 1) → ℕ) :
    MeasurableSet (renewalStringPairBox N m a b) := by
  exact MeasurableSet.univ_pi fun j => measurableSet_renewalStringPairCell N (a j) (b j)

/-- A valid product cell lies in the half-shifted domain for its occupied blocks. -/
theorem renewalStringPairBox_subset_target (N m : ℕ)
    (lo hi a b : Fin (m + 1) → ℕ) (hN : 0 < N)
    (hlo : ∀ j, lo j < a j) (hhi : ∀ j, b j ≤ hi j)
    (hab : ∀ j, a j ≤ b j) :
    renewalStringPairBox N m a b ⊆
      {p : Fin (m + 1) → ℝ × ℝ | ∀ j,
        ((lo j : ℝ) + 1 / 2) / N < (p j).1 ∧
        (p j).1 < (p j).2 ∧ (p j).2 ≤ ((hi j : ℝ) + 1 / 2) / N} := by
  intro p hp
  simp only [renewalStringPairBox, Set.mem_univ_pi] at hp
  simp only [Set.mem_ofPred_eq]
  intro j
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlo' : (lo j : ℝ) + 1 ≤ a j := by exact_mod_cast Nat.succ_le_of_lt (hlo j)
  have hhi' : (b j : ℝ) ≤ hi j := by exact_mod_cast hhi j
  have hpj : p j ∈ renewalStringPairCell N (a j) (b j) := hp j
  by_cases habj : a j = b j
  · simp only [renewalStringPairCell, ite_eq_left habj, Set.mem_ofPred_eq] at hpj
    rcases hpj with ⟨hslo, hsup, hst, htup⟩
    have hleft : ((lo j : ℝ) + 1 / 2) / N ≤ ((a j : ℝ) - 1 / 2) / N := by
      apply div_le_div_of_nonneg_right _ hN'.le
      linarith
    have hright : (a j : ℝ) / N ≤ ((hi j : ℝ) + 1 / 2) / N := by
      apply div_le_div_of_nonneg_right _ hN'.le
      rw [habj]
      linarith
    have hshift : (1 : ℝ) / (4 * (N : ℝ)) = (1 / 4) / N := by
      field_simp
    have htupper : (p j).2 < (a j : ℝ) / N := by
      rw [hshift] at htup
      have hsum : ((a j : ℝ) - 1 / 4) / N + (1 / 4) / N = (a j : ℝ) / N := by
        field_simp
        ring
      linarith
    exact ⟨hleft.trans_lt hslo, hst, (htupper.le.trans hright)⟩
  · simp only [renewalStringPairCell, ite_eq_right habj, Set.mem_ofPred_eq] at hpj
    rcases hpj with ⟨hslo, hsup, hblower, hbupper⟩
    have hleft : ((lo j : ℝ) + 1 / 2) / N ≤ ((a j : ℝ) - 1 / 2) / N := by
      apply div_le_div_of_nonneg_right _ hN'.le
      linarith
    have ha_lt_b : a j < b j := lt_of_le_of_ne (hab j) habj
    have hmiddle : (a j : ℝ) / N < (b j : ℝ) / N :=
      div_lt_div_of_pos_right (by exact_mod_cast ha_lt_b) hN'
    have hright : ((b j : ℝ) + 1 / 2) / N ≤ ((hi j : ℝ) + 1 / 2) / N := by
      apply div_le_div_of_nonneg_right _ hN'.le
      linarith
    exact ⟨hleft.trans_lt hslo, (hsup.trans hmiddle).trans hblower,
      (hbupper.le.trans hright)⟩

/-- Coordinate bounds for a pair-cell whose renewal indices are ordered. -/
theorem renewalStringPairCell_bounds (N a b : ℕ) (hN : 0 < N) (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ renewalStringPairCell N a b) :
    ((a : ℝ) - 1 / 2) / N < p.1 ∧ p.1 < (a : ℝ) / N ∧ p.1 < p.2 ∧
      p.2 < ((b : ℝ) + 1 / 2) / N ∧
      (b = a → p.2 < (a : ℝ) / N) ∧ (a < b → (b : ℝ) / N < p.2) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  by_cases hab' : a = b
  · simp only [renewalStringPairCell, ite_eq_left hab', Set.mem_ofPred_eq] at hp
    rcases hp with ⟨hslo, hsup, hst, htup⟩
    have hsup' : p.1 < (a : ℝ) / N := by
      have hle : ((a : ℝ) - 1 / 4) / N ≤ (a : ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hN'.le
        linarith
      exact hsup.trans_le hle
    have hshift : (1 : ℝ) / (4 * (N : ℝ)) = (1 / 4) / N := by
      field_simp
    have htup' : p.2 < (a : ℝ) / N := by
      rw [hshift] at htup
      have hsum : ((a : ℝ) - 1 / 4) / N + (1 / 4) / N = (a : ℝ) / N := by
        field_simp
        ring
      linarith
    have hbt : ((b : ℝ) + 1 / 2) / N = ((a : ℝ) + 1 / 2) / N := by rw [hab']
    have hupper : (a : ℝ) / N ≤ ((b : ℝ) + 1 / 2) / N := by
      rw [hbt]
      apply div_le_div_of_nonneg_right _ hN'.le
      linarith
    refine ⟨hslo, hsup', hst, ?_, ?_, ?_⟩
    · exact htup'.trans_le hupper
    · intro _
      exact htup'
    · intro hablt
      exact False.elim ((Nat.ne_of_lt hablt) hab')
  · simp only [renewalStringPairCell, ite_eq_right hab', Set.mem_ofPred_eq] at hp
    rcases hp with ⟨hslo, hsup, hblower, hbupper⟩
    have hlt : a < b := lt_of_le_of_ne hab hab'
    have hmiddle : (a : ℝ) / N ≤ (b : ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hab) hN'.le
    exact ⟨hslo, hsup, (lt_of_lt_of_le hsup hmiddle).trans hblower, hbupper,
      (fun hEq => False.elim (hab' hEq.symm)), (fun _ => hblower)⟩

/-- The second coordinate stays at least a half-cell below its integer index. -/
theorem renewalStringPairCell_second_lower (N a b : ℕ) (hN : 0 < N)
    (hab : a ≤ b) {p : ℝ × ℝ} (hp : p ∈ renewalStringPairCell N a b) :
    ((b : ℝ) - 1 / 2) / N < p.2 := by
  obtain ⟨hlo, _, hst, _, _, hgap⟩ := renewalStringPairCell_bounds N a b hN hab hp
  by_cases hEq : a = b
  · rw [hEq] at hlo
    exact hlo.trans hst
  · have hgap' := hgap (lt_of_le_of_ne hab hEq)
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hstep : ((b : ℝ) - 1 / 2) / N < (b : ℝ) / N := by
      apply div_lt_div_of_pos_right _ hN'
      linarith
    exact hstep.trans hgap'

/-- Geometry of two consecutive pair-cells when their integer indices are strictly
ordered. -/
theorem renewalStringPairCell_cross_geometry (N a b c d : ℕ) (hN : 0 < N)
    (hab : a ≤ b) (hcd : c ≤ d) (hbc : b < c)
    {p q : ℝ × ℝ} (hp : p ∈ renewalStringPairCell N a b)
    (hq : q ∈ renewalStringPairCell N c d) :
    ((b : ℝ) - 1 / 2) / N < p.2 ∧ p.2 < q.1 ∧ q.1 < (c : ℝ) / N := by
  have hpBounds := renewalStringPairCell_bounds N a b hN hab hp
  have hqBounds := renewalStringPairCell_bounds N c d hN hcd hq
  have hplower := renewalStringPairCell_second_lower N a b hN hab hp
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsep : ((b : ℝ) + 1 / 2) / N ≤ ((c : ℝ) - 1 / 2) / N := by
    apply div_le_div_of_nonneg_right _ hN'.le
    have hNat : b + 1 ≤ c := Nat.succ_le_of_lt hbc
    have hcast : (b : ℝ) + 1 ≤ c := by exact_mod_cast hNat
    linarith
  exact ⟨hplower, (hpBounds.2.2.2.1.trans_le hsep).trans hqBounds.1,
    hqBounds.2.1⟩

/-- The rational factor between successive occupied blocks is controlled by the
continuum factor on the pair-cell, with a uniform mesh loss. -/
theorem renewalStringPairCell_cross_ratio (N a b c d : ℕ) (hN : 0 < N)
    (hb : 1 ≤ b) (hab : a ≤ b) (hcd : c ≤ d) (hbc : b < c)
    {p q : ℝ × ℝ} (hp : p ∈ renewalStringPairCell N a b)
    (hq : q ∈ renewalStringPairCell N c d) :
    (b : ℝ) / ((c : ℝ) * ((c : ℝ) - b)) ≤
      (4 / (N : ℝ)) * p.2 / (q.1 * (q.1 - p.2)) := by
  obtain ⟨hplower, horder, hqupper⟩ :=
    renewalStringPairCell_cross_geometry N a b c d hN hab hcd hbc hp hq
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbc' : (b : ℝ) + 1 ≤ c := by exact_mod_cast (Nat.succ_le_of_lt hbc)
  have hc' : (0 : ℝ) < (c : ℝ) := by
    have : (1 : ℝ) ≤ c := by exact_mod_cast (by omega : 1 ≤ c)
    linarith
  have hdiff' : (0 : ℝ) < (c : ℝ) - b := by linarith
  have htprefix : 0 < ((b : ℝ) - 1 / 2) / N := by
    apply div_pos _ hN'
    linarith
  have htp : 0 < p.2 := lt_trans htprefix hplower
  have hspos : 0 < q.1 := lt_trans htp horder
  have hgapPos : 0 < q.1 - p.2 := sub_pos.mpr horder
  have hnumR : 0 < (N : ℝ) * q.1 * (q.1 - p.2) := by positivity
  have hdenL : 0 < (c : ℝ) * ((c : ℝ) - b) := mul_pos hc' hdiff'
  have hNs : (N : ℝ) * q.1 ≤ c := by
    have hmul := mul_le_mul_of_nonneg_left hqupper.le hN'.le
    have heq : (N : ℝ) * ((c : ℝ) / N) = c := by field_simp
    rw [heq] at hmul
    exact hmul
  have hGap : q.1 - p.2 ≤ (3 / 2) * ((c : ℝ) - b) / N := by
    have hcoef : ((c : ℝ) - b) + 1 / 2 ≤ (3 / 2) * ((c : ℝ) - b) := by
      linarith [hbc']
    have hcoefdiv : (((c : ℝ) - b) + 1 / 2) / N ≤
        (3 / 2) * ((c : ℝ) - b) / N := by
      calc
        _ ≤ ((3 / 2) * ((c : ℝ) - b)) / N :=
          div_le_div_of_nonneg_right hcoef hN'.le
        _ = (3 / 2) * ((c : ℝ) - b) / N := rfl
    have hdiff : (c : ℝ) / N - ((b : ℝ) - 1 / 2) / N =
        (((c : ℝ) - b) + 1 / 2) / N := by
      field_simp
      ring
    have hsum : q.1 - p.2 < (((c : ℝ) - b) + 1 / 2) / N := by
      linarith
    exact hsum.le.trans hcoefdiv
  have hT : (b : ℝ) / (2 * N) ≤ p.2 := by
    have hnum : (b : ℝ) / 2 ≤ (b : ℝ) - 1 / 2 := by linarith
    have hdiv : ((b : ℝ) / 2) / N ≤ ((b : ℝ) - 1 / 2) / N :=
      div_le_div_of_nonneg_right hnum hN'.le
    have heq : ((b : ℝ) / 2) / N = (b : ℝ) / (2 * N) := by ring
    rw [← heq]
    exact hdiv.trans hplower.le
  have hleft : (b : ℝ) * (((N : ℝ) * q.1) * (q.1 - p.2)) ≤
      (b : ℝ) * c * ((3 / 2) * ((c : ℝ) - b) / N) := by
    have hinner : ((N : ℝ) * q.1) * (q.1 - p.2) ≤
        c * ((3 / 2) * ((c : ℝ) - b) / N) :=
      mul_le_mul hNs hGap hgapPos.le hc'.le
    calc
      _ ≤ (b : ℝ) * (c * ((3 / 2) * ((c : ℝ) - b) / N)) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (b : ℝ) * c * ((3 / 2) * ((c : ℝ) - b) / N) := by ring
  have hmid : (b : ℝ) * c * ((3 / 2) * ((c : ℝ) - b) / N) ≤
      (4 : ℝ) * p.2 * c * ((c : ℝ) - b) := by
    calc
      _ = (3 / 2 : ℝ) * ((b : ℝ) * c * ((c : ℝ) - b)) / N := by ring
      _ ≤ 2 * ((b : ℝ) * c * ((c : ℝ) - b)) / N := by
        apply div_le_div_of_nonneg_right _ hN'.le
        have hprod : 0 ≤ (b : ℝ) * c * ((c : ℝ) - b) := by positivity
        nlinarith
      _ = ((b : ℝ) / (2 * N)) * (4 * c * ((c : ℝ) - b)) := by ring
      _ ≤ p.2 * (4 * c * ((c : ℝ) - b)) :=
        mul_le_mul_of_nonneg_right hT (by positivity)
      _ = (4 : ℝ) * p.2 * c * ((c : ℝ) - b) := by ring
  have hcross : (b : ℝ) * (((N : ℝ) * q.1) * (q.1 - p.2)) ≤
      (4 : ℝ) * p.2 * c * ((c : ℝ) - b) := hleft.trans hmid
  have hdiv : (b : ℝ) / ((c : ℝ) * ((c : ℝ) - b)) ≤
      (4 : ℝ) * p.2 / ((N : ℝ) * q.1 * (q.1 - p.2)) :=
    (div_le_div_iff₀ hdenL hnumR).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcross)
  have heq : (4 / (N : ℝ)) * p.2 / (q.1 * (q.1 - p.2)) =
      (4 : ℝ) * p.2 / ((N : ℝ) * q.1 * (q.1 - p.2)) := by
    field_simp
  rw [heq]
  exact hdiv

/-- The first half-shifted coordinate controls the discrete initial reciprocal. -/
theorem renewalStringPairCell_initial_inv (N a b : ℕ) (hN : 0 < N)
    (ha : 1 ≤ a) (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ renewalStringPairCell N a b) :
    (a : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ * p.1⁻¹ := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hbounds := renewalStringPairCell_bounds N a b hN hab hp
  have hpa : 0 < p.1 := by
    have hnum : (0 : ℝ) < (a : ℝ) - 1 / 2 := by
      have ha'' : (1 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
    exact lt_trans (div_pos hnum hN') hbounds.1
  have hNs : (N : ℝ) * p.1 ≤ a := by
    have hmul := mul_le_mul_of_nonneg_left hbounds.2.1.le hN'.le
    have heq : (N : ℝ) * ((a : ℝ) / N) = a := by field_simp
    rw [heq] at hmul
    exact hmul
  have hrightpos : 0 < (N : ℝ) * p.1 := mul_pos hN' hpa
  have hdiv : (1 : ℝ) / a ≤ 1 / ((N : ℝ) * p.1) := by
    apply (div_le_div_iff₀ ha' hrightpos).2
    simpa using hNs
  simpa [one_div, mul_comm] using hdiv

/-- Pointwise comparison of the discrete rational prefactor with its value on a
valid product cell. -/
theorem renewalStringPairBox_rational_le (N m : ℕ) (lo hi a b : Fin (m + 1) → ℕ)
    (hN : 0 < N) (hlo : ∀ j, lo j < a j) (hhi : ∀ j, b j ≤ hi j)
    (hsep : ∀ j : Fin m, hi j.castSucc ≤ lo j.succ)
    (hab : ∀ j, a j ≤ b j) {p : Fin (m + 1) → ℝ × ℝ}
    (hp : p ∈ renewalStringPairBox N m a b) :
    (a 0 : ℝ)⁻¹ *
        ∏ j : Fin m, (b j.castSucc : ℝ) /
          ((a j.succ : ℝ) * ((a j.succ : ℝ) - b j.castSucc)) ≤
      (1 / (N : ℝ)) * (4 / (N : ℝ)) ^ m *
        ((p 0).1⁻¹ * ∏ j : Fin m,
          (p j.castSucc).2 /
            ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))) := by
  classical
  have hpCell : ∀ j, p j ∈ renewalStringPairCell N (a j) (b j) := by
    simpa only [renewalStringPairBox, Set.mem_univ_pi] using hp
  have hfirst : 1 ≤ a 0 := by
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (hlo (0 : Fin (m + 1))))
  have hfirstInv := renewalStringPairCell_initial_inv N (a 0) (b 0) hN hfirst
    (hab 0) (hpCell 0)
  let f : Fin m → ℝ := fun j => (b j.castSucc : ℝ) /
    ((a j.succ : ℝ) * ((a j.succ : ℝ) - b j.castSucc))
  let g : Fin m → ℝ := fun j => (p j.castSucc).2 /
    ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))
  have hfnn : ∀ j, 0 ≤ f j := by
    intro j
    dsimp [f]
    have hbc : b j.castSucc < a j.succ := by
      exact lt_of_le_of_lt (hhi j.castSucc) (lt_of_le_of_lt (hsep j) (hlo j.succ))
    have hbpos : 0 < (b j.castSucc : ℝ) := by
      have hNat : 0 < b j.castSucc := by
        have hidx := hlo j.castSucc
        have habidx := hab j.castSucc
        omega
      exact_mod_cast hNat
    have hdiff : 0 < (a j.succ : ℝ) - b j.castSucc := by
      have hcast : (b j.castSucc : ℝ) + 1 ≤ a j.succ := by
        exact_mod_cast (Nat.succ_le_of_lt hbc)
      linarith
    positivity
  have hgnn : ∀ j, 0 ≤ g j := by
    intro j
    dsimp [g]
    have hbc : b j.castSucc < a j.succ := by
      exact lt_of_le_of_lt (hhi j.castSucc) (lt_of_le_of_lt (hsep j) (hlo j.succ))
    have hpj : p j.castSucc ∈ renewalStringPairCell N (a j.castSucc) (b j.castSucc) :=
      hpCell j.castSucc
    have hqj : p j.succ ∈ renewalStringPairCell N (a j.succ) (b j.succ) := hpCell j.succ
    obtain ⟨hplower, horder, hqupper⟩ := renewalStringPairCell_cross_geometry
      N (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ) hN
      (hab j.castSucc) (hab j.succ) hbc hpj hqj
    have htpos : 0 < (p j.castSucc).2 := by
      have hbpos : (1 : ℝ) ≤ b j.castSucc := by
        have hidx := hlo j.castSucc
        have habidx := hab j.castSucc
        have hNat : 1 ≤ b j.castSucc := by omega
        exact_mod_cast hNat
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hbase : 0 < ((b j.castSucc : ℝ) - 1 / 2) / N := by
        apply div_pos _ hN'
        linarith
      exact lt_trans hbase hplower
    have hspos : 0 < (p j.succ).1 := lt_trans htpos horder
    have hgap : 0 < (p j.succ).1 - (p j.castSucc).2 := sub_pos.mpr horder
    positivity
  have hfg : ∀ j, f j ≤ (4 / (N : ℝ)) * g j := by
    intro j
    dsimp [f, g]
    have hbc : b j.castSucc < a j.succ := by
      exact lt_of_le_of_lt (hhi j.castSucc) (lt_of_le_of_lt (hsep j) (hlo j.succ))
    have hpj : p j.castSucc ∈ renewalStringPairCell N (a j.castSucc) (b j.castSucc) :=
      hpCell j.castSucc
    have hqj : p j.succ ∈ renewalStringPairCell N (a j.succ) (b j.succ) := hpCell j.succ
    have hbp : 1 ≤ b j.castSucc := by
      have hidx := hlo j.castSucc
      have habidx := hab j.castSucc
      omega
    have hratio := renewalStringPairCell_cross_ratio N (a j.castSucc) (b j.castSucc)
      (a j.succ) (b j.succ) hN hbp (hab j.castSucc) (hab j.succ) hbc hpj hqj
    exact hratio.trans_eq (by ring)
  have hconst : (∏ j : Fin m, (4 / (N : ℝ))) = (4 / (N : ℝ)) ^ m := by
    rw [Fin.prod_const, div_pow]
  have hprod : (∏ j : Fin m, f j) ≤ (4 / (N : ℝ)) ^ m * ∏ j : Fin m, g j := by
    calc
      (∏ j : Fin m, f j) ≤ ∏ j : Fin m, (4 / (N : ℝ)) * g j :=
        Finset.prod_le_prod₀ (fun j _ => hfnn j) (fun j _ => hfg j)
      _ = (∏ j : Fin m, (4 / (N : ℝ))) * ∏ j : Fin m, g j := by
        rw [Finset.prod_mul_distrib]
      _ = (4 / (N : ℝ)) ^ m * ∏ j : Fin m, g j := by rw [hconst]
  have hprodn : 0 ≤ ∏ j : Fin m, f j :=
    Finset.prod_nonneg (fun j hj => hfnn j)
  have h0 : 0 < (p 0).1 := by
    have h0' := renewalStringPairCell_bounds N (a 0) (b 0) hN (hab 0) (hpCell 0)
    have ha0 : (1 : ℝ) ≤ a 0 := by exact_mod_cast hfirst
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    apply lt_trans _ h0'.1
    apply div_pos _ hN'
    linarith
  have htargetn : 0 ≤ (p 0).1⁻¹ * ∏ j : Fin m, g j :=
    mul_nonneg (inv_nonneg.mpr h0.le) (Finset.prod_nonneg (fun j hj => hgnn j))
  have hcoefnonneg : 0 ≤ (1 / (N : ℝ)) * (p 0).1⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr h0.le)
  calc
    _ ≤ (1 / (N : ℝ) * (p 0).1⁻¹) * ∏ j : Fin m, f j :=
      mul_le_mul_of_nonneg_right (by simpa [one_div] using hfirstInv) hprodn
    _ ≤ (1 / (N : ℝ) * (p 0).1⁻¹) *
        ((4 / (N : ℝ)) ^ m * ∏ j : Fin m, g j) :=
      mul_le_mul_of_nonneg_left hprod hcoefnonneg
    _ = (1 / (N : ℝ)) * (4 / (N : ℝ)) ^ m *
        ((p 0).1⁻¹ * ∏ j : Fin m, g j) := by ring

/-- Distinct ordered pair cells are disjoint. -/
theorem renewalStringPairCell_disjoint (N : ℕ) (hN : 0 < N)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (hne : a ≠ c ∨ b ≠ d) :
    Disjoint (renewalStringPairCell N a b) (renewalStringPairCell N c d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  obtain ⟨haslo, hasup, _, _, hadiag, hablower⟩ :=
    renewalStringPairCell_bounds N a b hN hab hp
  obtain ⟨hcslo, hcsup, _, hdupper, hcdiag, hclower⟩ :=
    renewalStringPairCell_bounds N c d hN hcd hq
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rcases hne with hac | hbd
  · rcases lt_or_gt_of_ne hac with hac | hca
    · have hsep : (a : ℝ) / N ≤ ((c : ℝ) - 1 / 2) / N := by
        apply div_le_div_of_nonneg_right _ hN'.le
        have hNat : a + 1 ≤ c := Nat.succ_le_of_lt hac
        have hcast : (a : ℝ) + 1 ≤ c := by exact_mod_cast hNat
        linarith
      linarith
    · have hsep : (c : ℝ) / N ≤ ((a : ℝ) - 1 / 2) / N := by
        apply div_le_div_of_nonneg_right _ hN'.le
        have hNat : c + 1 ≤ a := Nat.succ_le_of_lt hca
        have hcast : (c : ℝ) + 1 ≤ a := by exact_mod_cast hNat
        linarith
      linarith
  · have hac : a = c := by
      by_contra h
      rcases lt_or_gt_of_ne h with hlt | hgt
      · have hsep : (a : ℝ) / N ≤ ((c : ℝ) - 1 / 2) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          have hNat : a + 1 ≤ c := Nat.succ_le_of_lt hlt
          have hcast : (a : ℝ) + 1 ≤ c := by exact_mod_cast hNat
          linarith
        linarith
      · have hsep : (c : ℝ) / N ≤ ((a : ℝ) - 1 / 2) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          have hNat : c + 1 ≤ a := Nat.succ_le_of_lt hgt
          have hcast : (c : ℝ) + 1 ≤ a := by exact_mod_cast hNat
          linarith
        linarith
    subst c
    have hbd' : b ≠ d := hbd
    rcases lt_or_gt_of_ne hbd' with hbdlt | hdb
    · have hdlower : (d : ℝ) / N < p.2 := by
        have hda : a < d := lt_of_le_of_lt hab hbdlt
        exact (hclower hda)
      by_cases hba : b = a
      · have hup := hadiag hba
        have hsep : (a : ℝ) / N ≤ (d : ℝ) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          exact_mod_cast (show a ≤ d by omega)
        linarith
      · have hba' : a < b := lt_of_le_of_ne hab (Ne.symm hba)
        have hsep : ((b : ℝ) + 1 / 2) / N ≤ (d : ℝ) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          have hNat : b + 1 ≤ d := by omega
          have hcast : (b : ℝ) + 1 ≤ d := by exact_mod_cast hNat
          linarith
        linarith
    · have hblower' : (b : ℝ) / N < p.2 := by
        have hba : a < b := lt_of_le_of_lt hcd hdb
        exact hablower hba
      by_cases hda : d = a
      · have hup := hcdiag hda
        have hsep : (a : ℝ) / N ≤ (b : ℝ) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          exact_mod_cast (show a ≤ b by omega)
        linarith
      · have hdb' : a < d := lt_of_le_of_ne hcd (Ne.symm hda)
        have hsep : ((d : ℝ) + 1 / 2) / N ≤ (b : ℝ) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          have hNat : d + 1 ≤ b := by omega
          have hcast : (d : ℝ) + 1 ≤ b := by exact_mod_cast hNat
          linarith
        linarith [hdupper]

/-- Product boxes indexed by distinct ordered strings are disjoint. -/
theorem renewalStringPairBox_disjoint (N m : ℕ) (hN : 0 < N)
    (a b c d : Fin (m + 1) → ℕ)
    (hab : ∀ j, a j ≤ b j) (hcd : ∀ j, c j ≤ d j)
    (hne : a ≠ c ∨ b ≠ d) :
    Disjoint (renewalStringPairBox N m a b) (renewalStringPairBox N m c d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hcoords : ∃ j, a j ≠ c j ∨ b j ≠ d j := by
    rcases hne with hne | hne
    · by_contra hnot
      push Not at hnot
      exact hne (funext fun j => (hnot j).1)
    · by_contra hnot
      push Not at hnot
      exact hne (funext fun j => (hnot j).2)
  obtain ⟨j, hj⟩ := hcoords
  have hpj : p j ∈ renewalStringPairCell N (a j) (b j) := by
    have h := hp
    simp only [renewalStringPairBox, Set.mem_univ_pi] at h
    exact h j
  have hqj : p j ∈ renewalStringPairCell N (c j) (d j) := by
    have h := hq
    simp only [renewalStringPairBox, Set.mem_univ_pi] at h
    exact h j
  have hcell := renewalStringPairCell_disjoint N hN (hab j) (hcd j) hj
  rw [Set.disjoint_left] at hcell
  exact hcell hpj hqj

/-- Tonelli factorization for a finite product of one-coordinate nonnegative
functions. -/
theorem lintegral_fin_nat_prod_eq_prod_collision {n : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Fin n → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → α, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hMP := measurePreserving_piFinSuccAbove μ 0
      rw [← hMP.symm.lintegral_comp (by fun_prop)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      have hg : Measurable (fun x : Fin n → α => ∏ i, f i.succ (x i)) := by
        apply Finset.measurable_fun_prod Finset.univ
        intro i hi
        exact (hf i.succ).comp (measurable_pi_apply i)
      rw [lintegral_prod_mul (f := f 0)
        (g := fun x : Fin n → α => ∏ i, f i.succ (x i))
        (μ := μ 0) (ν := Measure.pi fun i => μ i.succ)
        (hf 0).aemeasurable hg.aemeasurable]
      rw [ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ)]

/-- The scalar-density product integral over a product pair-cell factors into the
one-pair cell integrals. -/
theorem lintegral_renewalStringPairBox_scalar_prod (N m : ℕ)
    (a b : Fin (m + 1) → ℕ) (θ : ℝ) :
    (∫⁻ p in renewalStringPairBox N m a b,
      ∏ j, ENNReal.ofReal (DeltaBose.scalarDensity θ ((p j).2 - (p j).1))) =
        ∏ j, ∫⁻ q in renewalStringPairCell N (a j) (b j),
          ENNReal.ofReal (DeltaBose.scalarDensity θ (q.2 - q.1)) := by
  change (∫⁻ p, ∏ j, ENNReal.ofReal
      (DeltaBose.scalarDensity θ ((p j).2 - (p j).1)) ∂
        ((volume : Measure (Fin (m + 1) → ℝ × ℝ)).restrict
          (Set.univ.pi fun j => renewalStringPairCell N (a j) (b j)))) = _
  rw [volume_pi, Measure.restrict_pi_pi]
  exact lintegral_fin_nat_prod_eq_prod_collision
    (fun j => volume.restrict (renewalStringPairCell N (a j) (b j)))
    (fun j q => ENNReal.ofReal (DeltaBose.scalarDensity θ (q.2 - q.1)))
    (fun j => (DeltaBose.measurable_scalarDensity.comp
      (measurable_const.prodMk (measurable_snd.sub measurable_fst))).ennreal_ofReal)

/-- A lower bound on the rational factor can be pulled through the pair-box
integral, leaving the tensorized scalar-density mass. -/
theorem lintegral_renewalStringPairBox_rational_density_lower (N m : ℕ)
    (a b : Fin (m + 1) → ℕ) (θ R₀ : ℝ) (hN : 0 < N) (hR₀ : 0 ≤ R₀)
    (hab : ∀ j, a j ≤ b j)
    (hR : ∀ p ∈ renewalStringPairBox N m a b,
      R₀ ≤ renewalStringPairBoxRational m p) :
    ENNReal.ofReal R₀ *
        ∏ j : Fin (m + 1), ∫⁻ q in renewalStringPairCell N (a j) (b j),
          ENNReal.ofReal (DeltaBose.scalarDensity θ (q.2 - q.1)) ≤
      ∫⁻ p in renewalStringPairBox N m a b,
        ENNReal.ofReal (renewalStringPairBoxRational m p *
          renewalStringPairBoxDensity θ m p) := by
  let f : (Fin (m + 1) → ℝ × ℝ) → ℝ≥0∞ := fun p =>
    ∏ j : Fin (m + 1), ENNReal.ofReal
      (DeltaBose.scalarDensity θ ((p j).2 - (p j).1))
  have hf : Measurable f := by
    apply Finset.measurable_fun_prod Finset.univ
    intro j hj
    have hpair : Measurable (fun p : Fin (m + 1) → ℝ × ℝ =>
        (θ, (p j).2 - (p j).1)) :=
      measurable_const.prodMk
        ((measurable_snd.sub measurable_fst).comp (measurable_pi_apply j))
    exact (DeltaBose.measurable_scalarDensity.comp hpair).ennreal_ofReal
  have hbox : MeasurableSet (renewalStringPairBox N m a b) :=
    measurableSet_renewalStringPairBox N m a b
  have hpoint : ∀ p ∈ renewalStringPairBox N m a b,
      ENNReal.ofReal R₀ * f p ≤ ENNReal.ofReal
        (renewalStringPairBoxRational m p * renewalStringPairBoxDensity θ m p) := by
    intro p hp
    have hpCell : ∀ j, p j ∈ renewalStringPairCell N (a j) (b j) := by
      simpa only [renewalStringPairBox, Set.mem_univ_pi] using hp
    have hDnonneg : 0 ≤ renewalStringPairBoxDensity θ m p := by
      unfold renewalStringPairBoxDensity
      apply Finset.prod_nonneg
      intro j hj
      have hbound := renewalStringPairCell_bounds N (a j) (b j) hN (hab j) (hpCell j)
      exact (DeltaBose.scalarDensity_pos θ (sub_pos.mpr hbound.2.2.1)).le
    have hRp : 0 ≤ renewalStringPairBoxRational m p := hR₀.trans (hR p hp)
    have hmul : R₀ * renewalStringPairBoxDensity θ m p ≤
        renewalStringPairBoxRational m p * renewalStringPairBoxDensity θ m p :=
      mul_le_mul_of_nonneg_right (hR p hp) hDnonneg
    have hENN := ENNReal.ofReal_le_ofReal hmul
    rw [ENNReal.ofReal_mul hR₀, ENNReal.ofReal_mul hRp] at hENN
    have hDof : ENNReal.ofReal (renewalStringPairBoxDensity θ m p) = f p := by
      unfold renewalStringPairBoxDensity f
      exact ENNReal.ofReal_prod_of_nonneg (fun j hj =>
        (DeltaBose.scalarDensity_pos θ (sub_pos.mpr
          (renewalStringPairCell_bounds N (a j) (b j) hN (hab j) (hpCell j)).2.2.1)).le)
    rw [hDof] at hENN
    rw [ENNReal.ofReal_mul hRp, hDof]
    exact hENN
  have hfactor := lintegral_renewalStringPairBox_scalar_prod N m a b θ
  change ENNReal.ofReal R₀ *
      (∏ j : Fin (m + 1), ∫⁻ q in renewalStringPairCell N (a j) (b j),
        ENNReal.ofReal (DeltaBose.scalarDensity θ (q.2 - q.1))) ≤
    ∫⁻ p, ENNReal.ofReal
      (renewalStringPairBoxRational m p * renewalStringPairBoxDensity θ m p) ∂
        (volume.restrict (renewalStringPairBox N m a b))
  rw [← hfactor]
  rw [← lintegral_const_mul (μ := volume.restrict (renewalStringPairBox N m a b))
    (r := ENNReal.ofReal R₀) hf]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hbox] with p hp
  exact hpoint p hp



/-- Uniform lower mass of each selected renewal-pair subcell.  The diagonal
triangle captures the zero-gap logarithmic mass; off the diagonal, a rectangle
and the squared-log renewal bound give the comparison. -/
theorem exists_renewalStringPairCell_lower (A : ℝ) (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ ϑ : ℝ, ϑ ∈ Set.Icc (-A) A → ∀ a : ℕ, ∀ b : ℕ,
        1 ≤ a → a ≤ b → b ≤ N →
        ENNReal.ofReal (c / (N : ℝ) *
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a))) ≤
          ∫⁻ p in renewalStringPairCell N a b,
            ENNReal.ofReal (DeltaBose.scalarDensity
              (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) := by
  obtain ⟨cMass, hcMass, hMass⟩ :=
    eventually_criticalRenewalMass_scaled_log_sq_bound A hA
  obtain ⟨cDensity, hcDensity, hDensity⟩ :=
    exists_scalarDensity_lower_log (A + |Real.eulerMascheroniConstant|) (by positivity)
  obtain ⟨cIntegral, hcIntegral, hIntegral⟩ :=
    exists_lintegral_scalarDensity_lower_log
      (A + |Real.eulerMascheroniConstant|) (by positivity)
  let M : ℝ := 1 + (Real.log 2)⁻¹
  let Q : ℝ := 1 + (1 + Real.log 4) / Real.log 2
  let cGap : ℝ := cDensity / (8 * M ^ 2 * cMass)
  let cDiag : ℝ := cIntegral / (4 * Q * (Real.pi + 1))
  let c : ℝ := min cGap cDiag
  have hM : 0 < M := by dsimp [M]; positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hcGap : 0 < cGap := by dsimp [cGap]; positivity
  have hcDiag : 0 < cDiag := by
    dsimp [cDiag]
    have hpi : 0 < Real.pi + 1 := by positivity
    positivity
  have hc : 0 < c := lt_min hcGap hcDiag
  refine ⟨c, hc, ?_⟩
  filter_upwards [hMass, eventually_criticalSigmaSq_uniform_log_bound A hA,
    Filter.eventually_ge_atTop 2] with N hMassN hSigmaN hN
  intro ϑ hϑ a b ha hab hbN
  have hσ : 0 < criticalSigmaSq ϑ N := (hSigmaN ϑ hϑ).1
  have hσupper : criticalSigmaSq ϑ N ≤ (Real.pi + 1) / Real.log N :=
    (hSigmaN ϑ hϑ).2
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hθshift : ϑ - Real.eulerMascheroniConstant ∈
      Set.Icc (-(A + |Real.eulerMascheroniConstant|))
        (A + |Real.eulerMascheroniConstant|) := by
    constructor
    · change -(A + |Real.eulerMascheroniConstant|) ≤
        ϑ - Real.eulerMascheroniConstant
      have hg := neg_le_neg (le_abs_self Real.eulerMascheroniConstant)
      linarith [hϑ.1]
    · change ϑ - Real.eulerMascheroniConstant ≤
        A + |Real.eulerMascheroniConstant|
      have hg := neg_le_abs Real.eulerMascheroniConstant
      linarith [hϑ.2]
  by_cases habEq : a = b
  · subst b
    have hmass0 : Renewal.criticalRenewalMass ϑ N 0 = 1 := by
      simp [Renewal.criticalRenewalMass]
    have hcell : renewalStringPairCell N a a =
        {p | ((a : ℝ) - 1 / 2) / N < p.1 ∧
          p.1 < ((a : ℝ) - 1 / 4) / N ∧ p.1 < p.2 ∧
          p.2 < p.1 + (1 : ℝ) / (4 * (N : ℝ))} := by
      ext p
      simp [renewalStringPairCell, div_eq_mul_inv]
    let θ : ℝ := ϑ - Real.eulerMascheroniConstant
    let width : ℝ := 1 / (4 * N)
    let h : ℝ := width
    let l : ℝ := ((a : ℝ) - 1 / 2) / N
    let r : ℝ := ((a : ℝ) - 1 / 4) / N
    have hwidth : 0 < width := by
      dsimp [width]
      positivity
    have hwidth_le : width ≤ 1 := by
      dsimp [width]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      apply (div_le_one (by positivity : (0 : ℝ) < 4 * N)).2
      have hNlower : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      nlinarith
    have hF : Measurable (fun u : ℝ =>
        ENNReal.ofReal (DeltaBose.scalarDensity θ u)) := by
      exact (DeltaBose.measurable_scalarDensity.comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal
    have htriangle := lintegral_renewalPair_triangle_eq
      (l := l) (r := r) (h := h) (F := fun u : ℝ =>
        ENNReal.ofReal (DeltaBose.scalarDensity θ u)) hF
    have htriangle' :
        (∫⁻ p : ℝ × ℝ in renewalStringPairCell N a a,
          ENNReal.ofReal (DeltaBose.scalarDensity θ (p.2 - p.1))) =
        ENNReal.ofReal width *
          (∫⁻ u in Ioo (0 : ℝ) h,
            ENNReal.ofReal (DeltaBose.scalarDensity θ u)) := by
      rw [hcell]
      convert htriangle using 1
      dsimp [l, r, h, width]
      congr 1
      ring_nf
    have hsmall := hIntegral θ h hθshift hwidth hwidth_le
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog2N : Real.log 2 ≤ Real.log (N : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast (by omega : 2 ≤ N)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 * 2) := by norm_num
        _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
        _ = 2 * Real.log 2 := by ring
    have hQbound : 1 + Real.log 4 + Real.log (N : ℝ) ≤
        Q * Real.log (N : ℝ) := by
      dsimp [Q]
      rw [div_eq_mul_inv]
      have hratio : 1 ≤ Real.log (N : ℝ) / Real.log 2 :=
        (le_div_iff₀ hlog2pos).2 (by simpa using hlog2N)
      have hterms : 1 + Real.log 4 ≤
          ((1 + Real.log 4) / Real.log 2) * Real.log (N : ℝ) := by
        rw [div_eq_mul_inv]
        calc
          1 + Real.log 4 =
              (1 + Real.log 4) * 1 := by ring
          _ ≤ (1 + Real.log 4) *
              (Real.log (N : ℝ) / Real.log 2) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = _ := by ring
      calc
        1 + Real.log 4 + Real.log (N : ℝ) ≤
            ((1 + Real.log 4) / Real.log 2) * Real.log (N : ℝ) +
              Real.log (N : ℝ) := by linarith
        _ = Q * Real.log (N : ℝ) := by dsimp [Q]; ring
    have hden : 1 - Real.log h = 1 + Real.log 4 + Real.log (N : ℝ) := by
      dsimp [h, width]
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by positivity : (4 : ℝ) * N ≠ 0)]
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (by positivity : (N : ℝ) ≠ 0)]
      simp
      ring
    have hdenpos : 0 < 1 - Real.log h := by
      have hloghle : Real.log h ≤ 0 :=
        Real.log_nonpos (by positivity) (by linarith [hwidth_le])
      linarith
    have hdenbound : 1 - Real.log h ≤ Q * Real.log (N : ℝ) := by
      rw [hden]
      exact hQbound
    have hrecip : (Q * Real.log (N : ℝ))⁻¹ ≤ (1 - Real.log h)⁻¹ :=
      (inv_le_inv₀ (mul_pos hQ hlogN) hdenpos).2 hdenbound
    have hcompare : c / (N : ℝ) * criticalSigmaSq ϑ N ≤
        width * (cIntegral / (1 - Real.log h)) := by
      have hcDiagBound : c ≤ cDiag := by
        dsimp [c]
        exact min_le_right cGap cDiag
      have hcoeff : c / (N : ℝ) ≤ cDiag / (N : ℝ) :=
        div_le_div_of_nonneg_right hcDiagBound (by positivity)
      have hσle : criticalSigmaSq ϑ N ≤ (Real.pi + 1) / Real.log N := hσupper
      calc
        c / (N : ℝ) * criticalSigmaSq ϑ N ≤
            cDiag / (N : ℝ) * ((Real.pi + 1) / Real.log N) := by
          calc
            _ ≤ cDiag / (N : ℝ) * criticalSigmaSq ϑ N :=
              mul_le_mul_of_nonneg_right hcoeff hσ.le
            _ ≤ _ := mul_le_mul_of_nonneg_left hσle (by positivity)
        _ ≤ width * (cIntegral / (1 - Real.log h)) := by
          calc
            cDiag / (N : ℝ) * ((Real.pi + 1) / Real.log N) =
                (cIntegral / (4 * N)) * (Q * Real.log N)⁻¹ := by
              dsimp [cDiag]
              field_simp [ne_of_gt hlogN, ne_of_gt hQ]
            _ ≤ (cIntegral / (4 * N)) * (1 - Real.log h)⁻¹ :=
              mul_le_mul_of_nonneg_left hrecip (by positivity)
            _ = width * (cIntegral / (1 - Real.log h)) := by
              dsimp [width]
              field_simp [ne_of_gt hdenpos, ne_of_gt (show (0 : ℝ) < N by positivity)]
    have hsmall' : ENNReal.ofReal (cIntegral / (1 - Real.log h)) ≤
        ∫⁻ u in Ioo (0 : ℝ) h,
          ENNReal.ofReal (DeltaBose.scalarDensity θ u) := hsmall
    have hmul : ENNReal.ofReal width * ENNReal.ofReal (cIntegral / (1 - Real.log h)) ≤
        ENNReal.ofReal width *
          (∫⁻ u in Ioo (0 : ℝ) h,
            ENNReal.ofReal (DeltaBose.scalarDensity θ u)) :=
      mul_le_mul_of_nonneg_left hsmall' zero_le
    have hrealENN : ENNReal.ofReal (c / (N : ℝ) *
        (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (a - a))) ≤
          ENNReal.ofReal width * ENNReal.ofReal (cIntegral / (1 - Real.log h)) := by
      have hleft := ENNReal.ofReal_le_ofReal hcompare
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ width)] at hleft
      simpa [Nat.sub_self, hmass0, width, h] using hleft
    calc
      ENNReal.ofReal (c / (N : ℝ) *
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (a - a))) ≤
        ENNReal.ofReal width * ENNReal.ofReal (cIntegral / (1 - Real.log h)) := by
          exact hrealENN
      _ ≤ _ := hmul
      _ = _ := htriangle'.symm
  · have hablt : a < b := by omega
    let d : ℕ := b - a
    have hd : 1 ≤ d := by dsimp [d]; omega
    have hdPlus : d + 1 ≤ N := by dsimp [d]; omega
    have hθ : ϑ - Real.eulerMascheroniConstant ∈
        Set.Icc (-(A + |Real.eulerMascheroniConstant|))
          (A + |Real.eulerMascheroniConstant|) := hθshift
    let L : ℝ := Real.log (1 + (N : ℝ) / d)
    have hL : 0 < L := by
      dsimp [L]
      apply Real.log_pos
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hquot : 0 < (N : ℝ) / d := div_pos hNpos hdpos
      linarith
    have hpoint := scalarDensity_lower_on_scaled_gap hcDensity hDensity N d
      (by omega) hd hdPlus hθ
    have hcell : renewalStringPairCell N a b =
        Ioo (((a : ℝ) - 1 / 2) / N) ((a : ℝ) / N) ×ˢ
          Ioo ((b : ℝ) / N) (((b : ℝ) + 1 / 2) / N) := by
      ext p
      simp [renewalStringPairCell, ne_of_lt hablt, Set.mem_Ioo, and_assoc]
    let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
      (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1))
    have hF : Measurable F := by
      have hpair : Measurable (fun p : ℝ × ℝ =>
          (ϑ - Real.eulerMascheroniConstant, p.2 - p.1)) :=
        measurable_const.prodMk (measurable_snd.sub measurable_fst)
      have hdensity := DeltaBose.measurable_scalarDensity.comp hpair
      change Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)))
      simpa only [Function.comp_apply] using hdensity.ennreal_ofReal
    let pointBound : ℝ := cDensity * N /
      (2 * d * (1 + (Real.log 2)⁻¹) ^ 2 * L ^ 2)
    have hpointBound : 0 < pointBound := by
      dsimp [pointBound]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hMpos : 0 < 1 + (Real.log 2)⁻¹ := by
        have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        positivity
      exact div_pos (mul_pos hcDensity hNpos)
        (mul_pos (mul_pos (mul_pos (by norm_num) hdpos)
          (sq_pos_of_pos hMpos)) (sq_pos_of_pos hL))
    have hpointwise : ∀ p ∈
        Ioo (((a : ℝ) - 1 / 2) / N) ((a : ℝ) / N) ×ˢ
          Ioo ((b : ℝ) / N) (((b : ℝ) + 1 / 2) / N),
        ENNReal.ofReal pointBound ≤ F p := by
      intro p hp
      have hs := hp.1
      have ht := hp.2
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hdlo : (d : ℝ) / N ≤ p.2 - p.1 := by
        have hdcast : (d : ℝ) = (b : ℝ) - (a : ℝ) := by
          dsimp [d]
          exact Nat.cast_sub hab
        have hbase : (b : ℝ) / N - (a : ℝ) / N = (d : ℝ) / N := by
          rw [← sub_div, show (b : ℝ) - (a : ℝ) = (d : ℝ) by linarith]
        have hdiff : (b : ℝ) / N - (a : ℝ) / N < p.2 - p.1 := by
          linarith [ht.1, hs.2]
        rw [hbase] at hdiff
        exact hdiff.le
      have hdupper : p.2 - p.1 ≤ ((d + 1 : ℕ) : ℝ) / N := by
        have hleft : p.2 - p.1 <
            (((b : ℝ) + 1 / 2) / N) - (((a : ℝ) - 1 / 2) / N) := by
          linarith [ht.2, hs.1]
        have hdiff : (((b : ℝ) + 1 / 2) / N) -
            (((a : ℝ) - 1 / 2) / N) =
              ((d + 1 : ℕ) : ℝ) / N := by
          have hdcast : (d : ℝ) = (b : ℝ) - (a : ℝ) := by
            dsimp [d]
            exact Nat.cast_sub hab
          rw [← sub_div]
          rw [show ((b : ℝ) + 1 / 2) - ((a : ℝ) - 1 / 2) =
            ((b : ℝ) - (a : ℝ)) + 1 by ring]
          rw [Nat.cast_add, Nat.cast_one, hdcast]
        exact hleft.le.trans_eq hdiff
      have hpt := hpoint (p.2 - p.1) hdlo hdupper
      have heq : pointBound = cDensity * N /
          (2 * d * (1 + (Real.log 2)⁻¹) ^ 2 *
            (Real.log (1 + (N : ℝ) / d)) ^ 2) := by
        dsimp [pointBound, L]
      change ENNReal.ofReal pointBound ≤
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1))
      rw [heq]
      exact ENNReal.ofReal_le_ofReal hpt
    have hrect := lintegral_Ioo_prod_lower F (ENNReal.ofReal pointBound) hpointwise
    have hcellIntegral :
        ∫⁻ p in renewalStringPairCell N a b, F p =
          ∫⁻ p in Ioo (((a : ℝ) - 1 / 2) / N) ((a : ℝ) / N) ×ˢ
            Ioo ((b : ℝ) / N) (((b : ℝ) + 1 / 2) / N), F p := by rw [hcell]
    have hwidthA : (a : ℝ) / N - ((a : ℝ) - 1 / 2) / N = 1 / (2 * N) := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      field_simp
      ring
    have hwidthB : ((b : ℝ) + 1 / 2) / N - (b : ℝ) / N = 1 / (2 * N) := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      field_simp
      ring
    have hrect' : ENNReal.ofReal pointBound * ENNReal.ofReal (1 / (2 * N)) *
        ENNReal.ofReal (1 / (2 * N)) ≤
          ∫⁻ p in renewalStringPairCell N a b, F p := by
      rw [hwidthA, hwidthB] at hrect
      rw [hcellIntegral]
      exact hrect
    have hMassN' := hMassN ϑ hϑ d hd (by dsimp [d]; omega)
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hscaledNonneg : 0 ≤
        criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d := by
      apply mul_nonneg hσ.le
      change 0 ≤ Renewal.renewalMass
        (fun r => criticalSigmaSq ϑ N * Renewal.returnWeight r) d
      apply Renewal.renewalMass_nonneg
      intro r
      exact mul_nonneg hσ.le (srwKernel_nonneg (2 * r) 0)
    have hratio : criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d ≤
        cMass / (d * L ^ 2) := by
      apply (le_div_iff₀ (mul_pos hdpos (sq_pos_of_pos hL))).2
      have hbase : (d : ℝ) *
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d) ≤
            cMass / L ^ 2 := by simpa [L] using hMassN'
      have hmul := (le_div_iff₀ (sq_pos_of_pos hL)).1 hbase
      calc
        (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d) *
            ((d : ℝ) * L ^ 2) =
          (d : ℝ) * (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d) * L ^ 2 := by ring
        _ ≤ cMass := hmul
    have hrealBound : c / (N : ℝ) *
        (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d) ≤
          pointBound / (4 * (N : ℝ) ^ 2) := by
      have hcoeff : c / (N : ℝ) ≤ cGap / (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        dsimp [c]
        exact min_le_left cGap cDiag
      calc
        c / (N : ℝ) * (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d) ≤
            cGap / (N : ℝ) * (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d) :=
          mul_le_mul_of_nonneg_right hcoeff hscaledNonneg
        _ ≤ cGap / (N : ℝ) * (cMass / (d * L ^ 2)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = pointBound / (4 * (N : ℝ) ^ 2) := by
          dsimp [cGap, pointBound, M, L]
          have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          field_simp [ne_of_gt hL, ne_of_gt hNpos]
          ring
    have hrealENN : ENNReal.ofReal (c / (N : ℝ) *
        (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d)) ≤
          ENNReal.ofReal pointBound * ENNReal.ofReal (1 / (2 * N)) *
            ENNReal.ofReal (1 / (2 * N)) := by
      have hle := ENNReal.ofReal_le_ofReal hrealBound
      have hprod : ENNReal.ofReal (pointBound / (4 * (N : ℝ) ^ 2)) =
          ENNReal.ofReal pointBound * ENNReal.ofReal (1 / (2 * N)) *
            ENNReal.ofReal (1 / (2 * N)) := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        rw [← ENNReal.ofReal_mul (le_of_lt hpointBound)]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ pointBound * (1 / (2 * N)))]
        congr 1
        field_simp [ne_of_gt hNpos]
        ring
      rw [hprod] at hle
      exact hle
    calc
      ENNReal.ofReal (c / (N : ℝ) *
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a))) =
        ENNReal.ofReal (c / (N : ℝ) *
          (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d)) := by
            simp [d]
      _ ≤ ENNReal.ofReal pointBound * ENNReal.ofReal (1 / (2 * N)) *
            ENNReal.ofReal (1 / (2 * N)) := hrealENN
      _ ≤ ∫⁻ p in renewalStringPairCell N a b, F p := hrect'
      _ = ∫⁻ p in renewalStringPairCell N a b,
          ENNReal.ofReal (DeltaBose.scalarDensity
            (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) := rfl

end Critical2DKPZ.Collision

end
