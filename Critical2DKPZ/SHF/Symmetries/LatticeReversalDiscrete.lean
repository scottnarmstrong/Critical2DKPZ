/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.KernelReversal
public import Critical2DKPZ.PolymerCalculus.TimeReversal
public import Critical2DKPZ.Polymer.Moments
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Critical2DKPZ.SHF.Moments.CriticalBoundary
public import Critical2DKPZ.SHF.Moments.TimeRounding
public import Critical2DKPZ.SHF.Positivity.CompactConvergence
public import Critical2DKPZ.SHF.Tsai.ConvergenceApproximation
public import Critical2DKPZ.SHF.Tsai.SecondMomentApproximation
public import Critical2DKPZ.SHF.Flow.SlabProductsIdentities
public import Critical2DKPZ.SHF.Moments.WordDominationFlatPairMoment
import Mathlib.Tactic
import Critical2DKPZ.SHF.Moments.WordDominationPositivity

/-! # Finite-scale lattice reversal and the SHF reversed finite-dimensional laws -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Moments Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Symmetries

private theorem evenCeil_reflected_gap_cases {N : ℕ} {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    evenCeil ((N : ℝ) * (x + y)) - evenCeil ((N : ℝ) * x) =
      evenCeil ((N : ℝ) * y) ∨
    evenCeil ((N : ℝ) * (x + y)) - evenCeil ((N : ℝ) * x) + 2 =
      evenCeil ((N : ℝ) * y) := by
  let a := evenCeil ((N : ℝ) * x)
  let b := evenCeil ((N : ℝ) * y)
  let c := evenCeil ((N : ℝ) * (x + y))
  have hsum : c ≤ a + b := by
    dsimp [a, b, c, Critical2DKPZ.evenCeil]
    rw [show (N : ℝ) * (x + y) / 2 =
      ((N : ℝ) * x) / 2 + ((N : ℝ) * y) / 2 by ring]
    simpa only [Nat.mul_add] using Nat.mul_le_mul_left 2
      (Nat.ceil_add_le (((N : ℝ) * x) / 2) (((N : ℝ) * y) / 2))
  have hmono : a ≤ c := by
    dsimp [a, c]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hy) (Nat.cast_nonneg N))
  have hgapCast : (((a + b : ℕ) - c : ℕ) : ℝ) < 4 := by
    have ha : (a : ℝ) < (N : ℝ) * x + 2 := by
      dsimp [a]
      exact Critical2DKPZ.evenCeil_lt_add_two (mul_nonneg (Nat.cast_nonneg N) hx)
    have hb : (b : ℝ) < (N : ℝ) * y + 2 := by
      dsimp [b]
      exact Critical2DKPZ.evenCeil_lt_add_two (mul_nonneg (Nat.cast_nonneg N) hy)
    have hc : (c : ℝ) ≥ (N : ℝ) * (x + y) := by
      dsimp [c]
      exact Critical2DKPZ.le_evenCeil _
    rw [Nat.cast_sub hsum, Nat.cast_add]
    norm_num at *
    nlinarith
  have hEven : Even ((a + b : ℕ) - c) := by
    rcases Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * x) with ⟨u, hu⟩
    rcases Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * y) with ⟨v, hv⟩
    rcases Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * (x + y)) with ⟨w, hw⟩
    refine ⟨u + v - w, ?_⟩
    dsimp [a, b, c] at hu hv hw ⊢
    omega
  have hgap : (a + b : ℕ) - c = 0 ∨ (a + b : ℕ) - c = 2 := by
    have hltNat : (a + b : ℕ) - c < 4 := by exact_mod_cast hgapCast
    rcases hEven with ⟨m, hm⟩
    omega
  rcases hgap with hzero | htwo
  · left
    omega
  · right
    omega

/-- Even rounding fixes a natural number cast from an even clock. -/
theorem evenCeil_natCast_of_even {m : ℕ} (hm : Even m) :
    Critical2DKPZ.evenCeil (m : ℝ) = m := by
  rcases hm with ⟨q, hq⟩
  rw [hq]
  simp [Critical2DKPZ.evenCeil]
  ring

/-- Scaling an even natural clock by `1 / N` and rounding recovers that clock. -/
theorem evenCeil_scaled_nat_div {N m : ℕ} (hN : 0 < N) (hm : Even m) :
    Critical2DKPZ.evenCeil ((N : ℝ) * ((m : ℝ) / N)) = m := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  rw [show (N : ℝ) * ((m : ℝ) / N) = (m : ℝ) by field_simp]
  exact evenCeil_natCast_of_even hm

/-- Complementary even-rounded clocks differ from exact reflection by at most two steps. -/
theorem evenCeil_reflected_clock_cases {N : ℕ} {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    evenCeil ((N : ℝ) * (T - t)) =
        evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) ∨
      evenCeil ((N : ℝ) * (T - t)) =
        evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) + 2 := by
  have h := evenCeil_reflected_gap_cases (N := N) (x := T - t) (y := t)
    (sub_nonneg.mpr htT) ht
  rw [show T - t + t = T by ring] at h
  have hmono : evenCeil ((N : ℝ) * t) ≤ evenCeil ((N : ℝ) * T) :=
    Critical2DKPZ.evenCeil_mono (mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg N))
  have hRmono : evenCeil ((N : ℝ) * (T - t)) ≤ evenCeil ((N : ℝ) * T) :=
    Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (sub_le_self T ht) (Nat.cast_nonneg N))
  rcases h with h | h
  · left
    omega
  · right
    omega


/-- Swap the two coordinates of a compactly supported test function. -/
def swapPairTest (φ : C_c(Plane × Plane, ℝ)) : C_c(Plane × Plane, ℝ) where
  toFun p := φ p.swap
  continuous_toFun := φ.continuous.comp continuous_swap
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    (Homeomorph.prodComm Plane Plane)

private theorem cellTestWeight_swapPairTest (N : ℕ) (φ : C_c(Plane × Plane, ℝ))
    (x y : Site) :
    cellTestWeight N (swapPairTest φ) x y = cellTestWeight N φ y x := by
  unfold cellTestWeight
  change (N / 4 : ℝ) *
      (∫ p in cell N x ×ˢ cell N y, φ p.swap) =
    (N / 4 : ℝ) * (∫ p in cell N y ×ˢ cell N x, φ p)
  rw [Measure.volume_eq_prod Plane Plane,
    MeasureTheory.setIntegral_prod_swap (μ := volume) (ν := volume)
    (s := cell N y) (t := cell N x)]

private theorem pointToPoint_endpoint_time_reversal (β : ℝ) {a b L : ℕ}
    (hab : a ≤ b) (hbL : b ≤ L) (x y : Site) (ω : Disorder) :
    Real.exp (β * ω (a, x)) * pointToPoint β a (b - a) x y ω =
      Real.exp (β * ω (b, y)) * pointToPoint β (L - b) (b - a) y x
        (PolymerCalculus.reversedDisorder L ω) := by
  have h := PolymerCalculus.pointToPoint_time_reversal β L a (b - a)
    (by omega) x y ω
  have htime : a + (b - a) = b := by omega
  rw [htime] at h
  exact h

private theorem cellWeight_sum_pointToPoint_endpoint_time_reversal
    (ϑ : ℝ) (N a b L : ℕ) (hab : a ≤ b) (hbL : b ≤ L)
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
      (Real.exp (criticalBeta ϑ N * ω (a, q.1)) *
        pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω)) =
    (∑' q : Site × Site, cellTestWeight N (swapPairTest φ) q.1 q.2 *
      (Real.exp (criticalBeta ϑ N * ω (b, q.1)) *
        pointToPoint (criticalBeta ϑ N) (L - b) (b - a) q.1 q.2
          (PolymerCalculus.reversedDisorder L ω))) := by
  let F : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2 *
    (Real.exp (criticalBeta ϑ N * ω (b, q.2)) *
      pointToPoint (criticalBeta ϑ N) (L - b) (b - a) q.2 q.1
        (PolymerCalculus.reversedDisorder L ω))
  let G : Site × Site → ℝ := fun q => cellTestWeight N (swapPairTest φ) q.1 q.2 *
    (Real.exp (criticalBeta ϑ N * ω (b, q.1)) *
      pointToPoint (criticalBeta ϑ N) (L - b) (b - a) q.1 q.2
        (PolymerCalculus.reversedDisorder L ω))
  have hrev (q : Site × Site) := pointToPoint_endpoint_time_reversal
    (criticalBeta ϑ N) hab hbL q.1 q.2 ω
  have hswap : (∑' q : Site × Site, G q) =
      ∑' q : Site × Site, G q.swap :=
    (Equiv.prodComm Site Site).tsum_eq G |>.symm
  calc
    _ = ∑' q, F q := by
      apply tsum_congr
      intro q
      dsimp [F]
      rw [hrev q]
    _ = ∑' q : Site × Site, G q.swap := by
      apply tsum_congr
      intro q
      dsimp [F, G]
      rw [cellTestWeight_swapPairTest]
    _ = _ := by
      change (∑' q : Site × Site, G q.swap) = ∑' q : Site × Site, G q
      exact hswap.symm

/-- Express a tested rescaled polymer kernel as the sum of its cell-pair weights. -/
theorem pairing_cellTestWeight_eq_tsum_pointToPoint (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p * rescaledP2P ϑ N s t p ω) =
      ∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω := by
  rw [← Critical2DKPZ.SHF.Limit.integral_polymerMeasure ϑ N s t ω φ,
    Critical2DKPZ.SHF.Flow.integral_polymerMeasure_cellTsum]
  apply tsum_congr
  intro q
  unfold cellTestWeight
  ring

/-- A cell-pair test weight vanishes outside the finite support set of the test. -/
theorem cellTestWeight_eq_zero_of_not_mem (N : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) (q : Site × Site)
    (hq : q ∉ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset) :
    cellTestWeight N φ q.1 q.2 = 0 := by
  by_contra hne
  have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, φ p) ≠ 0 := by
    intro hz
    apply hne
    simp [cellTestWeight, hz]
  exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).mem_toFinset.mpr hcell)


/-- The compact pairing at an even integer clock is the corresponding cell-weighted
point-to-point lattice sum. -/
theorem pairing_latticeClock_eq_tsum_pointToPoint (ϑ : ℝ) {N a b : ℕ}
    (hN : 0 < N) (ha : Even a) (hb : Even b)
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) =
      ∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω := by
  have hsa : evenCeil ((N : ℝ) * ((a : ℝ) / N)) = a :=
    evenCeil_scaled_nat_div hN ha
  have hsb : evenCeil ((N : ℝ) * ((b : ℝ) / N)) = b :=
    evenCeil_scaled_nat_div hN hb
  rw [pairing_cellTestWeight_eq_tsum_pointToPoint, hsa, hsb]

/-- A compact pairing with an initial endpoint Boltzmann factor is a finite-support lattice sum. -/
theorem pairing_endpointWeight_eq_tsum_pointToPoint (ϑ : ℝ) (N a : ℕ)
    (s t : ℝ) (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p *
      (Real.exp (criticalBeta ϑ N * ω (a, latticePoint N p.1)) *
        rescaledP2P ϑ N s t p ω)) =
      ∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        (Real.exp (criticalBeta ϑ N * ω (a, q.1)) *
          pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω) := by
  let G : Site → Site → ℝ := fun x y =>
    Real.exp (criticalBeta ϑ N * ω (a, x)) *
      pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) x y ω
  calc
    _ = ∫ p : Plane × Plane, (N / 4 : ℝ) *
        (φ p * G (latticePoint N p.1) (latticePoint N p.2)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [G]
      change φ p * (Real.exp _ * ((N / 4 : ℝ) * _)) = _ * (φ p * _)
      ring
    _ = (N / 4 : ℝ) *
        (∫ p : Plane × Plane, φ p *
          G (latticePoint N p.1) (latticePoint N p.2)) := by
      rw [integral_const_mul]
    _ = (N / 4 : ℝ) *
        (∑' q : Site × Site,
          (∫ p in cell N q.1 ×ˢ cell N q.2, φ p) * G q.1 q.2) := by
      rw [Critical2DKPZ.SHF.Flow.integral_latticePairing_eq_cellTsum]
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro q
      unfold cellTestWeight G
      ring

/-- Express the tested initial-endpoint factor error as a weighted point-to-point sum. -/
theorem pairing_startEndpoint_error_eq_tsum (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p *
      ((Real.exp (criticalBeta ϑ N * ω
          (evenCeil ((N : ℝ) * s), latticePoint N p.1)) - 1) *
        rescaledP2P ϑ N s t p ω)) =
      ∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        ((Real.exp (criticalBeta ϑ N * ω
            (evenCeil ((N : ℝ) * s), q.1)) - 1) *
          pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω) := by
  let a := evenCeil ((N : ℝ) * s)
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let G : Site → Site → ℝ := fun x y =>
    (Real.exp (criticalBeta ϑ N * ω (a, x)) - 1) *
      pointToPoint (criticalBeta ϑ N) a n x y ω
  calc
    _ = ∫ p : Plane × Plane, (N / 4 : ℝ) *
        (φ p * G (latticePoint N p.1) (latticePoint N p.2)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp [G, a, n]
      simp only [rescaledP2P]
      ring
    _ = (N / 4 : ℝ) *
        (∫ p : Plane × Plane, φ p *
          G (latticePoint N p.1) (latticePoint N p.2)) := by
      rw [integral_const_mul]
    _ = (N / 4 : ℝ) *
        (∑' q : Site × Site,
          (∫ p in cell N q.1 ×ˢ cell N q.2, φ p) * G q.1 q.2) := by
      rw [Critical2DKPZ.SHF.Flow.integral_latticePairing_eq_cellTsum]
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro q
      unfold cellTestWeight G
      ring

/-- Reverse the discrete tested pairing while retaining the initial endpoint factor. -/
theorem integral_pairing_endpoint_time_reversal_discrete
    (ϑ : ℝ) {N a b L : ℕ} (hN : 0 < N) (ha : Even a) (hb : Even b)
    (hL : Even L) (hab : a ≤ b) (hbL : b ≤ L)
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p *
      (Real.exp (criticalBeta ϑ N * ω (a, latticePoint N p.1)) *
        rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω)) =
    (∫ p, swapPairTest φ p *
      (Real.exp (criticalBeta ϑ N *
          PolymerCalculus.reversedDisorder L ω (L - b, latticePoint N p.1)) *
        rescaledP2P ϑ N ((L - b : ℝ) / N) ((L - a : ℝ) / N) p
          (PolymerCalculus.reversedDisorder L ω))) := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hsa : evenCeil ((N : ℝ) * ((a : ℝ) / N)) = a := by
    rw [show (N : ℝ) * ((a : ℝ) / N) = (a : ℝ) by field_simp]
    exact evenCeil_natCast_of_even ha
  have hsb : evenCeil ((N : ℝ) * ((b : ℝ) / N)) = b := by
    rw [show (N : ℝ) * ((b : ℝ) / N) = (b : ℝ) by field_simp]
    exact evenCeil_natCast_of_even hb
  have hL_b : evenCeil ((N : ℝ) * ((L - b : ℝ) / N)) = L - b := by
    have hsub : (L : ℝ) - b = ((L - b : ℕ) : ℝ) := by
      rw [Nat.cast_sub hbL]
    rw [show (N : ℝ) * (((L : ℝ) - b) / N) = ((L - b : ℕ) : ℝ) by
      rw [hsub]; field_simp]
    exact evenCeil_natCast_of_even (by
      rcases hL with ⟨l, hl⟩
      rcases hb with ⟨q, hq⟩
      refine ⟨l - q, ?_⟩
      omega)
  have hL_a : evenCeil ((N : ℝ) * ((L - a : ℝ) / N)) = L - a := by
    have hsub : (L : ℝ) - a = ((L - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub (le_trans hab hbL)]
    rw [show (N : ℝ) * (((L : ℝ) - a) / N) = ((L - a : ℕ) : ℝ) by
      rw [hsub]; field_simp]
    exact evenCeil_natCast_of_even (by
      rcases hL with ⟨l, hl⟩
      rcases ha with ⟨q, hq⟩
      refine ⟨l - q, ?_⟩
      omega)
  have hleft := pairing_endpointWeight_eq_tsum_pointToPoint ϑ N a
    ((a : ℝ) / N) ((b : ℝ) / N) φ ω
  have hright := pairing_endpointWeight_eq_tsum_pointToPoint ϑ N (L - b)
      ((L - b : ℝ) / N) ((L - a : ℝ) / N) (swapPairTest φ)
      (PolymerCalculus.reversedDisorder L ω)
  rw [hleft, hright, hsa, hsb, hL_b, hL_a]
  have hduration : L - a - (L - b) = b - a := by omega
  rw [hduration]
  have hnoise (z : Site) :
      PolymerCalculus.reversedDisorder L ω (L - b, z) = ω (b, z) := by
    simp [PolymerCalculus.reversedDisorder, Gaussian.reindexDisorder,
      PolymerCalculus.timeReversalIndex, PolymerCalculus.reflectedTime,
      Nat.sub_sub_self hbL]
  simp_rw [hnoise]
  exact cellWeight_sum_pointToPoint_endpoint_time_reversal ϑ N a b L hab hbL φ ω


end Critical2DKPZ.SHF.Symmetries

end
