/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.PathComposition
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Definitions.EndpointDist
import Mathlib.Tactic

/-! Finite-horizon polymer partition functions satisfy the Chapman–Kolmogorov composition identities. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- Terminal-profile partition functions compose across an intermediate time slice. -/
theorem terminalProfile_chapmanKolmogorov (β : ℝ) (a n m : ℕ)
    (w : Site) (f : Site → ℝ) (ω : Disorder) :
    ∑' z, pointToPoint β a (n + m) w z ω * f z =
      ∑' y, pointToPoint β a n w y ω *
        (∑' z, pointToPoint β (a + n) m y z ω * f z) := by
  simp_rw [tsum_pointToPoint_mul]
  rw [← (Fin.appendEquiv n m).sum_comp
    (fun r : Fin (n + m) → Fin 4 =>
      (4 : ℝ)⁻¹ ^ (n + m) * pathWeight β a w r ω * f (walkPosition w r (n + m)))]
  rw [Fintype.sum_prod_type]
  simp only [pow_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.appendEquiv, Equiv.coe_fn_mk]
  rw [pathWeight_append, walkPosition_append_end]
  ring

/-- Point-to-point partition functions satisfy the finite Chapman–Kolmogorov identity. -/
theorem pointToPoint_chapmanKolmogorov (β : ℝ) (a n m : ℕ)
    (w z : Site) (ω : Disorder) :
    pointToPoint β a (n + m) w z ω =
      ∑' y, pointToPoint β a n w y ω * pointToPoint β (a + n) m y z ω := by
  have h := terminalProfile_chapmanKolmogorov β a n m w
    (fun x => if x = z then 1 else 0) ω
  simpa only [mul_ite, mul_one, mul_zero, tsum_ite_eq] using h

/-- Point-to-plane partition functions factor through the intermediate endpoint kernel. -/
theorem pointToPlane_chapmanKolmogorov (β : ℝ) (a n m : ℕ)
    (w : Site) (ω : Disorder) :
    pointToPlane β a (n + m) w ω =
      ∑' y, pointToPoint β a n w y ω * pointToPlane β (a + n) m y ω := by
  have h := terminalProfile_chapmanKolmogorov β a n m w (fun _ => 1) ω
  simpa only [mul_one, tsum_pointToPoint] using h

/-- The polymer endpoint distribution is nonnegative. -/
theorem endpointDist_nonneg (β : ℝ) (n : ℕ) (w z : Site) (ω : Disorder) :
    0 ≤ endpointDist β n w ω z :=
  div_nonneg (pointToPoint_nonneg β 0 n w z ω) (pointToPlane_pos β 0 n w ω).le

/-- The polymer endpoint distribution vanishes outside the reachable endpoint set. -/
theorem endpointDist_eq_zero_of_not_mem (β : ℝ) (n : ℕ) (w z : Site)
    (ω : Disorder) (hz : z ∉ endpoints w n) :
    endpointDist β n w ω z = 0 := by
  unfold endpointDist
  rw [pointToPoint_eq_zero_of_not_mem β 0 n w z ω hz, zero_div]

/-- The polymer endpoint distribution has total mass one. -/
theorem tsum_endpointDist (β : ℝ) (n : ℕ) (w : Site) (ω : Disorder) :
    ∑' z, endpointDist β n w ω z = 1 := by
  unfold endpointDist
  rw [tsum_div_const, tsum_pointToPoint, div_self (ne_of_gt (pointToPlane_pos β 0 n w ω))]

/-- Dividing out the earlier partition function leaves the endpoint-distribution average of the later one. -/
theorem pointToPlane_endpoint_factorization (β : ℝ) (m N : ℕ) (hm : m ≤ N)
    (w : Site) (ω : Disorder) :
    pointToPlane β 0 N w ω = pointToPlane β 0 m w ω *
      profileP2Fun β m N (endpointDist β m w ω) (fun _ => 1) ω := by
  rw [profileP2Fun]
  simp only [mul_one, tsum_pointToPoint]
  rw [← tsum_mul_left]
  have h := pointToPlane_chapmanKolmogorov β 0 m (N - m) w ω
  rw [Nat.add_sub_of_le hm, Nat.zero_add] at h
  rw [h]
  apply tsum_congr
  intro y
  unfold endpointDist
  field_simp [ne_of_gt (pointToPlane_pos β 0 m w ω)]

end Critical2DKPZ.Polymer
