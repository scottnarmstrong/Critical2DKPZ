/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WalkScaling
public import Critical2DKPZ.SHF.Moments.CollisionEntrance
public import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Tactic

/-! # The local-CLT error for a two-walk collision density -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Polymer

/-- The scaled collision slice is the even-cell area times the product of its
two scaled one-walk densities. -/
theorem scaled_collisionSlice_eq_cellSum (N n : ℕ) (hN : 0 < N)
    (a b : Site) (F : Site → ℝ) :
    ((N : ℝ) / 4) * collisionSlice n a b F =
      (4 / (N : ℝ)) *
        ∑ z ∈ endpoints a n,
          (((N : ℝ) / 4) * srwKernel n (z - a)) *
            (((N : ℝ) / 4) * srwKernel n (z - b)) * F z := by
  unfold collisionSlice
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp [ne_of_gt hNr]

/-- Away from time zero, the product of two period-correct walk densities has a uniform `O(1/N)` local central limit error. -/
theorem srwKernel_scaled_collisionProduct_error_away_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N n : ℕ, 0 < N → 1 ≤ n → ε * N ≤ n →
      ∀ x y : Site, Even (x 0 + x 1 + n) → Even (y 0 + y 1 + n) →
        |(((N : ℝ) / 4) * srwKernel n x) * (((N : ℝ) / 4) * srwKernel n y) -
          heatKernel ((n : ℝ) / N) (latticeRepresentative N x) *
            heatKernel ((n : ℝ) / N) (latticeRepresentative N y)| ≤ C / N := by
  obtain ⟨C₀, hC₀, hlocal⟩ := srwKernel_scaled_localCLT_away_zero hε
  let K : ℝ := (2 * Real.pi * ε)⁻¹
  let C : ℝ := C₀ * (2 * K + C₀)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, by dsimp [C]; positivity, fun N n hN hn hgap x y hx hy => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgap' : ε * (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hgap
  have htime : ε ≤ (n : ℝ) / N := (le_div_iff₀ hNr).2 (by simpa using hgap')
  have htimepos : 0 < (n : ℝ) / N := div_pos hnr hNr
  let A : ℝ := ((N : ℝ) / 4) * srwKernel n x
  let B : ℝ := ((N : ℝ) / 4) * srwKernel n y
  let P : ℝ := heatKernel ((n : ℝ) / N) (latticeRepresentative N x)
  let Q : ℝ := heatKernel ((n : ℝ) / N) (latticeRepresentative N y)
  have hAerr : |A - P| ≤ C₀ / N := by
    simpa only [A, P] using hlocal N n hN hn hgap x hx
  have hBerr : |B - Q| ≤ C₀ / N := by
    simpa only [B, Q] using hlocal N n hN hn hgap y hy
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) (Critical2DKPZ.srwKernel_nonneg _ _)
  have hPnonneg : 0 ≤ P := heatKernel_nonneg htimepos.le _
  have hQnonneg : 0 ≤ Q := heatKernel_nonneg htimepos.le _
  have hdenle : 2 * Real.pi * ε ≤ 2 * Real.pi * ((n : ℝ) / N) := by
    exact mul_le_mul_of_nonneg_left htime (by positivity)
  have hdenpos : 0 < 2 * Real.pi * ε := by positivity
  have hdenpos' : 0 < 2 * Real.pi * ((n : ℝ) / N) := by positivity
  have hkernelBound : (2 * Real.pi * ((n : ℝ) / N))⁻¹ ≤ K := by
    exact (inv_le_inv₀ hdenpos' hdenpos).2 hdenle
  have hPbound : P ≤ K := (heatKernel_le_at_zero htimepos.le _).trans hkernelBound
  have hQbound : Q ≤ K := (heatKernel_le_at_zero htimepos.le _).trans hkernelBound
  have hBbound : B ≤ K + C₀ := by
    have hstep : B - Q ≤ C₀ / N := (abs_le.mp hBerr).2
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hdiv : C₀ / N ≤ C₀ := (div_le_iff₀ hNr).2 (by nlinarith [hC₀, hNreal])
    calc
      B = (B - Q) + Q := by ring
      _ ≤ C₀ / N + K := add_le_add hstep hQbound
      _ ≤ C₀ + K := add_le_add hdiv le_rfl
      _ = K + C₀ := add_comm _ _
  have hBabs : |B| ≤ K + C₀ := by rw [abs_of_nonneg hBnonneg]; exact hBbound
  have hPabs : |P| ≤ K := by rw [abs_of_nonneg hPnonneg]; exact hPbound
  have hdecomp : A * B - P * Q = (A - P) * B + P * (B - Q) := by ring
  calc
    |A * B - P * Q| = |(A - P) * B + P * (B - Q)| := by rw [hdecomp]
    _ ≤ |A - P| * |B| + |P| * |B - Q| := by
      simpa only [abs_mul] using abs_add_le ((A - P) * B) (P * (B - Q))
    _ ≤ (C₀ / N) * (K + C₀) + K * (C₀ / N) := by
      apply add_le_add
      · exact mul_le_mul hAerr hBabs
          (abs_nonneg _) (by positivity)
      · exact mul_le_mul hPabs hBerr
          (abs_nonneg _) (by positivity)
    _ = C / N := by dsimp [C]; ring

/-- Summing a pointwise two-kernel error over a finite phase-correct test. -/
theorem scaled_collisionProduct_finiteSum_error_of_pointwise
    (N n : ℕ) (hN : 0 < N) (a b : Site) (J : Finset Site) (F : Site → ℝ)
    (C : ℝ)
    (hpointwise : ∀ x y : Site, Even (x 0 + x 1 + n) → Even (y 0 + y 1 + n) →
      |(((N : ℝ) / 4) * srwKernel n x) * (((N : ℝ) / 4) * srwKernel n y) -
        heatKernel ((n : ℝ) / N) (latticeRepresentative N x) *
          heatKernel ((n : ℝ) / N) (latticeRepresentative N y)| ≤ C / N)
    (hphaseA : ∀ z ∈ J, Even ((z - a) 0 + (z - a) 1 + n))
    (hphaseB : ∀ z ∈ J, Even ((z - b) 0 + (z - b) 1 + n)) :
    |(4 / (N : ℝ)) *
        ∑ z ∈ J,
          (((N : ℝ) / 4) * srwKernel n (z - a)) *
            (((N : ℝ) / 4) * srwKernel n (z - b)) * F z -
      (4 / (N : ℝ)) *
        ∑ z ∈ J,
          heatKernel ((n : ℝ) / N) (latticeRepresentative N (z - a)) *
            heatKernel ((n : ℝ) / N) (latticeRepresentative N (z - b)) * F z| ≤
      (4 * C / N ^ 2) * ∑ z ∈ J, |F z| := by
  let A : Site → ℝ := fun z => ((N : ℝ) / 4) * srwKernel n (z - a)
  let B : Site → ℝ := fun z => ((N : ℝ) / 4) * srwKernel n (z - b)
  let P : Site → ℝ := fun z => heatKernel ((n : ℝ) / N) (latticeRepresentative N (z - a))
  let Q : Site → ℝ := fun z => heatKernel ((n : ℝ) / N) (latticeRepresentative N (z - b))
  have hsumSub :
      Finset.sum J (fun z => A z * B z * F z) -
          Finset.sum J (fun z => P z * Q z * F z) =
        Finset.sum J (fun z => (A z * B z * F z) - (P z * Q z * F z)) := by
    symm
    exact Finset.sum_sub_distrib (s := J)
      (f := fun z => A z * B z * F z) (g := fun z => P z * Q z * F z)
  have hsumEq :
      (4 / (N : ℝ)) * (∑ z ∈ J, A z * B z * F z) -
        (4 / (N : ℝ)) * (∑ z ∈ J, P z * Q z * F z) =
        (4 / (N : ℝ)) *
          Finset.sum J (fun z => (A z * B z - P z * Q z) * F z) := by
    calc
      _ = (4 / (N : ℝ)) *
          ((∑ z ∈ J, A z * B z * F z) - (∑ z ∈ J, P z * Q z * F z)) := by ring
      _ = (4 / (N : ℝ)) *
          Finset.sum J (fun z => (A z * B z * F z) - (P z * Q z * F z)) := by
        rw [hsumSub]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro z hz
        ring
  have hterm : ∀ z ∈ J, |(A z * B z - P z * Q z) * F z| ≤
      (C / N) * |F z| := by
    intro z hz
    have hpoint := hpointwise (z - a) (z - b) (hphaseA z hz) (hphaseB z hz)
    have hpoint' : |A z * B z - P z * Q z| ≤ C / N := by
      simpa only [A, B, P, Q] using hpoint
    calc
      |(A z * B z - P z * Q z) * F z| =
          |A z * B z - P z * Q z| * |F z| := abs_mul _ _
      _ ≤ (C / N) * |F z| :=
        mul_le_mul_of_nonneg_right hpoint' (abs_nonneg (F z))
  have hsumBound :
      |∑ z ∈ J, (A z * B z - P z * Q z) * F z| ≤
        ∑ z ∈ J, (C / N) * |F z| := by
    calc
      _ ≤ ∑ z ∈ J, |(A z * B z - P z * Q z) * F z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun z hz => hterm z hz
  have hcoef : 0 ≤ 4 / (N : ℝ) := by positivity
  calc
    _ = |(4 / (N : ℝ)) *
          (∑ z ∈ J, (A z * B z - P z * Q z) * F z)| := by rw [hsumEq]
    _ = (4 / (N : ℝ)) *
          |∑ z ∈ J, (A z * B z - P z * Q z) * F z| := by
      rw [abs_mul, abs_of_nonneg hcoef]
    _ ≤ (4 / (N : ℝ)) * ∑ z ∈ J, (C / N) * |F z| :=
      mul_le_mul_of_nonneg_left hsumBound hcoef
    _ = (4 / (N : ℝ)) * ((C / N) * ∑ z ∈ J, |F z|) := by
      rw [← Finset.mul_sum]
    _ = (4 * C / N ^ 2) * ∑ z ∈ J, |F z| := by ring


/-- The heat-kernel discretization of the collision entrance after the spatial
cell factor and the microscopic time-step factor are both included. -/
def collisionEntrance_heatDiscrete (N lo hi : ℕ) (a b : Site)
    (F : ℝ × Plane → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc lo hi,
    (4 / (N : ℝ)) * ((4 / (N : ℝ)) *
      ∑ z ∈ Polymer.endpoints a r,
        heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
          heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
          F ((r : ℝ) / N, latticeRepresentative N z))

/-- Every endpoint of an `r`-step walk has the corresponding time-space parity. -/
theorem endpoints_accessible_phase (r : ℕ) (a z : Site)
    (hz : z ∈ Polymer.endpoints a r) :
    Even ((z - a) 0 + (z - a) 1 + r) := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff a z r).mp hz
  have hpar := Polymer.walkPosition_parity a s
  rw [hs] at hpar
  have hdisp : Int.ModEq 2 ((z - a) 0 + (z - a) 1) (r : ℤ) := by
    have hsub := Int.ModEq.sub_right (a 0 + a 1) hpar
    have hleft : (z - a) 0 + (z - a) 1 =
        (z 0 + z 1) - (a 0 + a 1) := by
      simp only [Pi.sub_apply]
      ring
    have hright : (a 0 + a 1 + (r : ℤ)) - (a 0 + a 1) = (r : ℤ) := by ring
    rw [hleft, ← hright]
    exact hsub
  have hsum := hdisp.add_right (r : ℤ)
  have htwor : Int.ModEq 2 ((r : ℤ) + r) 0 := by
    dsimp [Int.ModEq]
    omega
  have hzero := hsum.trans htwor
  apply Int.even_iff.mpr
  simpa [Int.ModEq] using hzero

/-- If two starting sites have the same even-lattice parity, a common endpoint
has the correct phase for both walk kernels. -/
theorem endpoints_common_accessible_phase (r : ℕ) (a b z : Site)
    (ha : Even (a 0 + a 1)) (hb : Even (b 0 + b 1))
    (hz : z ∈ Polymer.endpoints a r) :
    Even ((z - b) 0 + (z - b) 1 + r) := by
  have hphase := endpoints_accessible_phase r a z hz
  have hstart : Even ((a - b) 0 + (a - b) 1) := by
    have hsum : (a - b) 0 + (a - b) 1 = (a 0 + a 1) - (b 0 + b 1) := by
      simp only [Pi.sub_apply]
      ring
    rw [hsum]
    exact Even.sub ha hb
  have hrewrite :
      (z - b) 0 + (z - b) 1 + r =
        ((z - a) 0 + (z - a) 1 + r) + ((a - b) 0 + (a - b) 1) := by
    simp only [Pi.sub_apply]
    ring
  rw [hrewrite]
  exact Even.add hphase hstart

/-- Away from time zero, the discrete collision entrance differs from its
heat-kernel spatial cell sum by the accumulated local-CLT error. -/
theorem collisionEntrance_heatDiscrete_error_away_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N lo hi : ℕ, 0 < N →
      ∀ a b : Site, ∀ F : ℝ × Plane → ℝ,
      (∀ r ∈ Finset.Icc lo hi, ε * N ≤ r) →
      (∀ r ∈ Finset.Icc lo hi, ∀ z ∈ Polymer.endpoints a r,
        Even ((z - a) 0 + (z - a) 1 + r)) →
      (∀ r ∈ Finset.Icc lo hi, ∀ z ∈ Polymer.endpoints a r,
        Even ((z - b) 0 + (z - b) 1 + r)) →
      |collisionEntrance N lo hi a b F - collisionEntrance_heatDiscrete N lo hi a b F| ≤
        (16 * C / N ^ 3) *
          ∑ r ∈ Finset.Icc lo hi,
            ∑ z ∈ Polymer.endpoints a r,
              |F ((r : ℝ) / N, latticeRepresentative N z)| := by
  obtain ⟨C, hC, hpointwise⟩ := srwKernel_scaled_collisionProduct_error_away_zero hε
  refine ⟨C, hC, ?_⟩
  intro N lo hi hN a b F hgap hphaseA hphaseB
  have hcoef : 0 ≤ 4 / (N : ℝ) := by positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hper : ∀ r ∈ Finset.Icc lo hi,
      |collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
        (4 / (N : ℝ)) * ((4 / (N : ℝ)) *
          ∑ z ∈ Polymer.endpoints a r,
            heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
              heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
              F ((r : ℝ) / N, latticeRepresentative N z))| ≤
        (16 * C / N ^ 3) *
          ∑ z ∈ Polymer.endpoints a r,
            |F ((r : ℝ) / N, latticeRepresentative N z)| := by
    intro r hr
    have hgap' : ε * (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast hgap r hr
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (mul_pos hε hNreal) hgap'
    have hrone : 1 ≤ r := by exact_mod_cast hrpos
    have hlocal : ∀ x y : Site, Even (x 0 + x 1 + r) → Even (y 0 + y 1 + r) →
        |(((N : ℝ) / 4) * srwKernel r x) * (((N : ℝ) / 4) * srwKernel r y) -
          heatKernel ((r : ℝ) / N) (latticeRepresentative N x) *
            heatKernel ((r : ℝ) / N) (latticeRepresentative N y)| ≤ C / N := by
      intro x y hx hy
      exact hpointwise N r hN hrone hgap' x y hx hy
    have hphaseB' : ∀ z ∈ Polymer.endpoints a r,
        Even ((z - b) 0 + (z - b) 1 + r) := by
      intro z hz
      exact hphaseB r hr z hz
    have hsum := scaled_collisionProduct_finiteSum_error_of_pointwise
      N r hN a b (Polymer.endpoints a r)
      (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) C hlocal
      (fun z hz => hphaseA r hr z hz) hphaseB'
    have hslice := scaled_collisionSlice_eq_cellSum N r hN a b
      (fun z => F ((r : ℝ) / N, latticeRepresentative N z))
    have hsum' :
        |((N : ℝ) / 4) * collisionSlice r a b
              (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
          (4 / (N : ℝ)) *
            ∑ z ∈ Polymer.endpoints a r,
              heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                F ((r : ℝ) / N, latticeRepresentative N z)| ≤
          (4 * C / N ^ 2) *
            ∑ z ∈ Polymer.endpoints a r,
              |F ((r : ℝ) / N, latticeRepresentative N z)| := by
      simpa only [hslice] using hsum
    have hidentity :
        collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
            (4 / (N : ℝ)) * ((4 / (N : ℝ)) *
              ∑ z ∈ Polymer.endpoints a r,
                heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                  heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                  F ((r : ℝ) / N, latticeRepresentative N z)) =
          (4 / (N : ℝ)) *
            (((N : ℝ) / 4) * collisionSlice r a b
                (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
              (4 / (N : ℝ)) *
                ∑ z ∈ Polymer.endpoints a r,
                  heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                    heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                    F ((r : ℝ) / N, latticeRepresentative N z)) := by
      field_simp [hNreal.ne']
    calc
      _ = |(4 / (N : ℝ)) *
          (((N : ℝ) / 4) * collisionSlice r a b
              (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
            (4 / (N : ℝ)) *
              ∑ z ∈ Polymer.endpoints a r,
                heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                  heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                  F ((r : ℝ) / N, latticeRepresentative N z))| := by rw [hidentity]
      _ = (4 / (N : ℝ)) *
          |((N : ℝ) / 4) * collisionSlice r a b
              (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
            (4 / (N : ℝ)) *
              ∑ z ∈ Polymer.endpoints a r,
                heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                  heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                  F ((r : ℝ) / N, latticeRepresentative N z)| := by
        rw [abs_mul, abs_of_nonneg hcoef]
      _ ≤ (4 / (N : ℝ)) * ((4 * C / N ^ 2) *
          ∑ z ∈ Polymer.endpoints a r,
            |F ((r : ℝ) / N, latticeRepresentative N z)|) :=
        mul_le_mul_of_nonneg_left hsum' hcoef
      _ = (16 * C / N ^ 3) *
          ∑ z ∈ Polymer.endpoints a r,
            |F ((r : ℝ) / N, latticeRepresentative N z)| := by ring
  have hsumSub :
      (∑ r ∈ Finset.Icc lo hi,
          collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z))) -
        collisionEntrance_heatDiscrete N lo hi a b F =
      ∑ r ∈ Finset.Icc lo hi,
        (collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
          (4 / (N : ℝ)) * ((4 / (N : ℝ)) *
            ∑ z ∈ Polymer.endpoints a r,
              heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                F ((r : ℝ) / N, latticeRepresentative N z))) := by
    simp only [collisionEntrance_heatDiscrete]
    symm
    exact Finset.sum_sub_distrib (s := Finset.Icc lo hi)
      (f := fun r => collisionSlice r a b
        (fun z => F ((r : ℝ) / N, latticeRepresentative N z)))
      (g := fun r => (4 / (N : ℝ)) * ((4 / (N : ℝ)) *
        ∑ z ∈ Polymer.endpoints a r,
          heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
            heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
            F ((r : ℝ) / N, latticeRepresentative N z)))
  have hsumBound :
      |∑ r ∈ Finset.Icc lo hi,
          (collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
            (4 / (N : ℝ)) * ((4 / (N : ℝ)) *
              ∑ z ∈ Polymer.endpoints a r,
                heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                  heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                  F ((r : ℝ) / N, latticeRepresentative N z)))| ≤
        ∑ r ∈ Finset.Icc lo hi,
          (16 * C / N ^ 3) *
            ∑ z ∈ Polymer.endpoints a r,
              |F ((r : ℝ) / N, latticeRepresentative N z)| := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc lo hi,
          |collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) -
            (4 / (N : ℝ)) * ((4 / (N : ℝ)) *
              ∑ z ∈ Polymer.endpoints a r,
                heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - a)) *
                  heatKernel ((r : ℝ) / N) (latticeRepresentative N (z - b)) *
                  F ((r : ℝ) / N, latticeRepresentative N z))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun r hr => hper r hr
  have hfinal :
      ∑ r ∈ Finset.Icc lo hi,
          (16 * C / N ^ 3) *
            ∑ z ∈ Polymer.endpoints a r,
              |F ((r : ℝ) / N, latticeRepresentative N z)| =
        (16 * C / N ^ 3) *
          ∑ r ∈ Finset.Icc lo hi,
            ∑ z ∈ Polymer.endpoints a r,
              |F ((r : ℝ) / N, latticeRepresentative N z)| := by
    rw [← Finset.mul_sum]
  simpa only [collisionEntrance, hsumSub, hfinal] using hsumBound

/-- The time-slab heat comparison applies directly when both starts lie in the
even sublattice, which makes every common reachable endpoint phase-correct. -/
theorem collisionEntrance_heatDiscrete_error_away_zero_evenStarts {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N lo hi : ℕ, 0 < N → ∀ a b : Site,
      Even (a 0 + a 1) → Even (b 0 + b 1) → ∀ F : ℝ × Plane → ℝ,
      (∀ r ∈ Finset.Icc lo hi, ε * N ≤ r) →
      |collisionEntrance N lo hi a b F - collisionEntrance_heatDiscrete N lo hi a b F| ≤
        (16 * C / N ^ 3) *
          ∑ r ∈ Finset.Icc lo hi,
            ∑ z ∈ Polymer.endpoints a r,
              |F ((r : ℝ) / N, latticeRepresentative N z)| := by
  obtain ⟨C, hC, hgeneral⟩ := collisionEntrance_heatDiscrete_error_away_zero hε
  refine ⟨C, hC, ?_⟩
  intro N lo hi hN a b ha hb F hgap
  apply hgeneral N lo hi hN a b F hgap
  · intro r hr z hz
    exact endpoints_accessible_phase r a z hz
  · intro r hr z hz
    exact endpoints_common_accessible_phase r a b z ha hb hz

end Critical2DKPZ.SHF.Moments

end
