/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.FinitePathGaussian
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # Gaussian comparison for finite initial polymer profiles -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

/-- A polymer mass with finitely supported initial weights and constant terminal profile one is a finite weighted path sum. -/
theorem profileP2Fun_eq_finitePathMass (β : ℝ) (a b : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (ω : Disorder) :
    profileP2Fun β a b ν (fun _ => 1) ω =
      PolymerCalculus.finitePathMass β a (b - a)
        (fun w : {y // y ∈ A} => w.1)
        (fun p : {y // y ∈ A} × (Fin (b - a) → Fin 4) =>
          ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a))) ω := by
  classical
  let Starts := {y // y ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a))
  have hprofile : profileP2Fun β a b ν (fun _ => 1) ω =
      ∑ y ∈ A, ν y * pointToPlane β a (b - a) y ω := by
    rw [Polymer.profileP2Fun_eq_sum β a b ν (fun _ => 1) A hνA]
    simp only [mul_one]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Polymer.tsum_pointToPoint]
  rw [hprofile]
  change ∑ y ∈ A, ν y * pointToPlane β a (b - a) y ω =
    ∑ p : Starts × (Fin (b - a) → Fin 4),
      c p * Real.exp (PolymerCalculus.pathEnergy β a (w p.1) p.2 ω)
  have hStart : (Finset.univ : Finset Starts) = A.attach := by
    ext y
    simp [Starts]
  calc
    ∑ y ∈ A, ν y * pointToPlane β a (b - a) y ω =
        ∑ y ∈ A.attach, ν y.1 * pointToPlane β a (b - a) y.1 ω := by
          exact (Finset.sum_attach A (fun y => ν y * pointToPlane β a (b - a) y ω)).symm
    _ = ∑ y : Starts, ν y.1 * pointToPlane β a (b - a) y.1 ω := by
          rw [← hStart]
    _ = ∑ y : Starts, ν y.1 *
          ∑ s : Fin (b - a) → Fin 4,
            ((4 : ℝ)⁻¹ ^ (b - a)) *
              Real.exp (PolymerCalculus.pathEnergy β a y.1 s ω) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Polymer.pointToPlane_eq_sum]
          rfl
    _ = ∑ y : Starts, ∑ s : Fin (b - a) → Fin 4,
          c (y, s) * Real.exp (PolymerCalculus.pathEnergy β a (w y) s ω) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          dsimp [c, w]
          ring
    _ = ∑ p : Starts × (Fin (b - a) → Fin 4),
          c p * Real.exp (PolymerCalculus.pathEnergy β a (w p.1) p.2 ω) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]


/-- A polymer mass with a normalized nonnegative finite initial profile satisfies logarithmic Gaussian moment bounds. -/
theorem profileP2Fun_log_moment_bounds (β : ℝ) (a b : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hν1 : ∑ w ∈ A, ν w = 1) :
    let F := fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)
    0 ≤ gaussianityDefect disorderLaw F ∧
      Var[F; disorderLaw] ≤ -2 * (∫ ω, F ω ∂disorderLaw) ∧
      -2 * (∫ ω, F ω ∂disorderLaw) ≤ Real.log (mgf F disorderLaw 2) ∧
      (∀ p : ℝ, 0 ≤ p → Real.log (mgf F disorderLaw (-p)) ≤
        -p * (∫ ω, F ω ∂disorderLaw) + p ^ 2 / 2 * Var[F; disorderLaw]) ∧
      gaussianityDefect disorderLaw F ≤
        Real.log (mgf F disorderLaw 2 / mgf F disorderLaw (-1)) := by
  classical
  let Starts := {y // y ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a))
  have hνpos : ∃ y ∈ A, 0 < ν y := by
    have hsum : 0 < ∑ y ∈ A, ν y := by rw [hν1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun y hy => hν0 y)).mp hsum
  have hc : ∀ p, 0 ≤ c p := by
    intro p
    dsimp [c]
    exact mul_nonneg (hν0 p.1.1) (by positivity)
  have hpos : ∃ p, 0 < c p := by
    obtain ⟨y, hyA, hy⟩ := hνpos
    refine ⟨(⟨y, hyA⟩, fun _ => 0), ?_⟩
    dsimp [c]
    exact mul_pos hy (by positivity)
  have hnorm : ∑ p, c p = 1 := by
    have hStart : (Finset.univ : Finset Starts) = A.attach := by
      ext y
      simp [Starts]
    have hstartMass : ∑ y : Starts, ν y.1 = 1 := by
      calc
        ∑ y : Starts, ν y.1 = ∑ y ∈ A, ν y := by
          rw [hStart, Finset.sum_attach]
        _ = 1 := hν1
    calc
      (∑ p : Starts × (Fin (b - a) → Fin 4), c p) =
          ∑ y : Starts, ∑ s : Fin (b - a) → Fin 4, c (y, s) := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ =
          ∑ y : Starts, ν y.1 *
            ∑ s : Fin (b - a) → Fin 4, ((4 : ℝ)⁻¹ ^ (b - a)) := by
              apply Finset.sum_congr rfl
              intro y hy
              dsimp [c]
              rw [← Finset.mul_sum]
      _ = ∑ y : Starts, ν y.1 * 1 := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Polymer.sum_walkProbability]
      _ = 1 := by simpa only [mul_one] using hstartMass
  have hEq (ω : Disorder) : profileP2Fun β a b ν (fun _ => 1) ω =
      PolymerCalculus.finitePathMass β a (b - a) w c ω := by
    simpa only [w, c, Starts] using
      profileP2Fun_eq_finitePathMass β a b ν A hνA ω
  have hlogEq :
      (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) =
        (fun ω => Real.log (PolymerCalculus.finitePathMass β a (b - a) w c ω)) := by
    funext ω
    rw [hEq]
  have hconv := logMGFRatio_finitePathMass_convex β a (b - a) w hc hpos
  have hbounds := PolymerCalculus.finitePathMass_bounds_of_logMGFRatio_convex
    β a (b - a) w hc hpos hnorm hconv
  simpa only [hlogEq] using hbounds

/-- The polymer mass with normalized nonnegative finite initial profile and terminal profile one is strictly positive for every disorder realization. -/
theorem profileP2Fun_pos_of_normalized (β : ℝ) (a b : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hν1 : ∑ w ∈ A, ν w = 1) (ω : Disorder) :
    0 < profileP2Fun β a b ν (fun _ => 1) ω := by
  have hνpos : ∃ y ∈ A, 0 < ν y := by
    have hsum : 0 < ∑ y ∈ A, ν y := by rw [hν1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun y hy => hν0 y)).mp hsum
  obtain ⟨y, hyA, hy⟩ := hνpos
  rw [Polymer.profileP2Fun_eq_sum β a b ν (fun _ => 1) A hνA]
  simp only [mul_one]
  have hsum :
      (∑ z ∈ A, ν z * ∑' y, pointToPoint β a (b - a) z y ω) =
        ∑ z ∈ A, ν z * pointToPlane β a (b - a) z ω := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [Polymer.tsum_pointToPoint]
  rw [hsum]
  apply (Finset.sum_pos_iff_of_nonneg (fun z hz =>
    mul_nonneg (hν0 z) (Polymer.pointToPlane_pos β a (b - a) z ω).le)).2
  exact ⟨y, hyA, mul_pos hy (Polymer.pointToPlane_pos β a (b - a) y ω)⟩

/-- The logarithm of the polymer mass with normalized nonnegative finite initial profile has all real exponential moments. -/
theorem integrableExpSet_log_profileP2Fun_eq_univ (β : ℝ) (a b : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hν1 : ∑ w ∈ A, ν w = 1) :
    integrableExpSet
      (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) disorderLaw = univ := by
  classical
  let Starts := {y // y ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a))
  have hνpos : ∃ y ∈ A, 0 < ν y := by
    have hsum : 0 < ∑ y ∈ A, ν y := by rw [hν1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun y hy => hν0 y)).mp hsum
  have hc : ∀ p, 0 ≤ c p := by
    intro p
    dsimp [c]
    exact mul_nonneg (hν0 p.1.1) (by positivity)
  have hpos : ∃ p, 0 < c p := by
    obtain ⟨y, hyA, hy⟩ := hνpos
    refine ⟨(⟨y, hyA⟩, fun _ => 0), ?_⟩
    dsimp [c]
    exact mul_pos hy (by positivity)
  have hEq (ω : Disorder) : profileP2Fun β a b ν (fun _ => 1) ω =
      PolymerCalculus.finitePathMass β a (b - a) w c ω := by
    simpa only [w, c, Starts] using
      profileP2Fun_eq_finitePathMass β a b ν A hνA ω
  have hlogEq :
      (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) =
        (fun ω => Real.log (PolymerCalculus.finitePathMass β a (b - a) w c ω)) := by
    funext ω
    rw [hEq]
  rw [hlogEq]
  exact PolymerCalculus.integrableExpSet_log_finitePathMass β a (b - a) w hc hpos

/-- The polymer mass with normalized nonnegative finite initial profile has integrable real powers. -/
theorem integrable_rpow_profileP2Fun (β : ℝ) (a b : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hν1 : ∑ w ∈ A, ν w = 1) (p : ℝ) :
    Integrable (fun ω => profileP2Fun β a b ν (fun _ => 1) ω ^ p) disorderLaw := by
  let F := fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)
  have hdom : integrableExpSet F disorderLaw = univ := by
    simpa only [F] using
      integrableExpSet_log_profileP2Fun_eq_univ β a b ν A hνA hν0 hν1
  have hExp : Integrable (fun ω => Real.exp (p * F ω)) disorderLaw := by
    apply integrable_of_mem_integrableExpSet
    rw [hdom]
    exact Set.mem_univ p
  have hpos := profileP2Fun_pos_of_normalized β a b ν A hνA hν0 hν1
  have hEq : (fun ω => profileP2Fun β a b ν (fun _ => 1) ω ^ p) =
      fun ω => Real.exp (p * F ω) := by
    funext ω
    rw [Real.rpow_def_of_pos (hpos ω)]
    simp only [F, mul_comm]
  rw [hEq]
  exact hExp

/-- Every real power of a smoothed one-point function is integrable, by its normalized
finite-support walk profile. -/
theorem integrable_rpow_smoothedP2Plane (β : ℝ) (s n : ℕ) (x : Site) (p : ℝ) :
    Integrable (fun ω => smoothedP2Plane β s n x ω ^ p) disorderLaw := by
  let ν : Site → ℝ := fun y => srwKernel s (y - x)
  let A : Finset Site := Polymer.endpoints x s
  have hνA : ∀ y ∉ A, ν y = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem s x y (by simpa [A] using hy)
  have hν0 : ∀ y, 0 ≤ ν y := fun y => Polymer.kernel_nonneg s (y - x)
  have hν1 : ∑ y ∈ A, ν y = 1 := Polymer.sum_srwKernel_endpoints s x
  have h := integrable_rpow_profileP2Fun β s n ν A hνA hν0 hν1 p
  have hEq : (fun ω => profileP2Fun β s n ν (fun _ => 1) ω ^ p) =
      fun ω => smoothedP2Plane β s n x ω ^ p := by
    funext ω
    exact congrArg (fun z : ℝ => z ^ p) (Polymer.profileP2Fun_srw_flat β s n x ω)
  rw [← hEq]
  exact h

/-- The MGF of a positive random variable's logarithm is its real-power moment. -/
theorem mgf_log_eq_integral_rpow {f : Disorder → ℝ} (hf : ∀ ω, 0 < f ω) (q : ℝ) :
    mgf (fun ω => Real.log (f ω)) disorderLaw q = ∫ ω, f ω ^ q ∂disorderLaw := by
  rw [ProbabilityTheory.mgf]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [Real.rpow_def_of_pos (hf ω), mul_comm]

/-- Gaussian convexity yields the polymer Gaussian-defect estimate for every smoothed one-point function. -/
theorem gaussianityDefect_log_smoothedP2Plane_bounds {β : ℝ} (hβ : 0 ≤ β)
    (s n : ℕ) (x : Site) :
    0 ≤ gaussianityDefect disorderLaw
      (fun ω => Real.log (smoothedP2Plane β s n x ω)) ∧
    gaussianityDefect disorderLaw
      (fun ω => Real.log (smoothedP2Plane β s n x ω)) ≤
      Real.log ((∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw) /
        ∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw) := by
  have _ : 0 ≤ β := hβ
  let ν : Site → ℝ := fun y => srwKernel s (y - x)
  let A : Finset Site := Polymer.endpoints x s
  have hνA : ∀ y ∉ A, ν y = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem s x y (by simpa [A] using hy)
  have hν0 : ∀ y, 0 ≤ ν y := fun y => by
    exact Polymer.kernel_nonneg s (y - x)
  have hν1 : ∑ y ∈ A, ν y = 1 := by
    exact Polymer.sum_srwKernel_endpoints s x
  have hbounds := profileP2Fun_log_moment_bounds β s n ν A hνA hν0 hν1
  have hF :
      (fun ω => Real.log (profileP2Fun β s n ν (fun _ => 1) ω)) =
        (fun ω => Real.log (smoothedP2Plane β s n x ω)) := by
    funext ω
    dsimp [ν]
    exact congrArg Real.log (Polymer.profileP2Fun_srw_flat β s n x ω)
  have hbounds' :
      0 ≤ gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β s n x ω)) ∧
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β s n x ω)) ≤
        Real.log (mgf (fun ω => Real.log (smoothedP2Plane β s n x ω)) disorderLaw 2 /
          mgf (fun ω => Real.log (smoothedP2Plane β s n x ω)) disorderLaw (-1)) := by
    rw [← hF]
    exact ⟨hbounds.1, hbounds.2.2.2.2⟩
  have hpositive : ∀ ω, 0 < smoothedP2Plane β s n x ω :=
    fun ω => Polymer.smoothedP2Plane_pos β s n x ω
  have htwo :
      mgf (fun ω => Real.log (smoothedP2Plane β s n x ω)) disorderLaw 2 =
        ∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, smoothedP2Plane β s n x ω ^ (2 : ℝ) ∂disorderLaw :=
        mgf_log_eq_integral_rpow hpositive 2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Real.rpow_natCast _ 2
  have hone :
      mgf (fun ω => Real.log (smoothedP2Plane β s n x ω)) disorderLaw (-1) =
        ∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw := by
    calc
      _ = ∫ ω, smoothedP2Plane β s n x ω ^ (-1 : ℝ) ∂disorderLaw :=
        mgf_log_eq_integral_rpow hpositive (-1)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Real.rpow_neg_one _
  simpa only [htwo, hone] using hbounds'

/-- Negative moments of a normalized finite profile obey the one-point comparison bound. Their
integrability is supplied by `integrable_rpow_profileP2Fun`. -/
theorem integral_rpow_neg_profileP2Fun_le {β : ℝ} (hβ : 0 ≤ β) (a b : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hν1 : ∑ w ∈ A, ν w = 1) {p : ℝ} (hp : 0 ≤ p) :
    ∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ (-p) ∂disorderLaw ≤
      (∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ 2 ∂disorderLaw) ^ (p * (p + 1) / 2) := by
  have _ : 0 ≤ β := hβ
  let F := fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)
  have hbounds := profileP2Fun_log_moment_bounds β a b ν A hνA hν0 hν1
  have hdom : integrableExpSet F disorderLaw = univ := by
    simpa only [F] using
      integrableExpSet_log_profileP2Fun_eq_univ β a b ν A hνA hν0 hν1
  have hmem (q : ℝ) : q ∈ integrableExpSet F disorderLaw := by
    rw [hdom]
    exact Set.mem_univ q
  have hpos := profileP2Fun_pos_of_normalized β a b ν A hνA hν0 hν1
  have hneg : Real.log (mgf F disorderLaw (-p)) ≤
      -p * (∫ ω, F ω ∂disorderLaw) + p ^ 2 / 2 * Var[F; disorderLaw] :=
    hbounds.2.2.2.1 p hp
  have hvar := hbounds.2.1
  have hmean := hbounds.2.2.1
  have hfactor : 0 ≤ p * (p + 1) / 2 := by positivity
  have hquad : -p * (∫ ω, F ω ∂disorderLaw) + p ^ 2 / 2 * Var[F; disorderLaw] ≤
      (p * (p + 1) / 2) * Real.log (mgf F disorderLaw 2) := by
    calc
      _ ≤ -p * (∫ ω, F ω ∂disorderLaw) + p ^ 2 / 2 *
          (-2 * (∫ ω, F ω ∂disorderLaw)) := by
            have hvarMul : p ^ 2 / 2 * Var[F; disorderLaw] ≤
                p ^ 2 / 2 * (-2 * (∫ ω, F ω ∂disorderLaw)) :=
              mul_le_mul_of_nonneg_left hvar (by positivity)
            linarith only [hvarMul]
      _ = (p * (p + 1) / 2) * (-2 * (∫ ω, F ω ∂disorderLaw)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean hfactor
  have hlog : Real.log (mgf F disorderLaw (-p)) ≤
      (p * (p + 1) / 2) * Real.log (mgf F disorderLaw 2) := hneg.trans hquad
  have hmgfnegpos := ProbabilityTheory.mgf_pos (hmem (-p))
  have hmgf2pos := ProbabilityTheory.mgf_pos (hmem 2)
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hmgfnegpos] at hexp
  have hpow : Real.exp ((p * (p + 1) / 2) * Real.log (mgf F disorderLaw 2)) =
      (mgf F disorderLaw 2) ^ (p * (p + 1) / 2) := by
    rw [Real.rpow_def_of_pos hmgf2pos]
    congr 1
    ring
  rw [hpow] at hexp
  have htwo :
      mgf F disorderLaw 2 =
        ∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ (2 : ℝ) ∂disorderLaw :=
        mgf_log_eq_integral_rpow hpos 2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Real.rpow_natCast _ 2
  have hnegative :
      mgf F disorderLaw (-p) =
        ∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ (-p) ∂disorderLaw :=
    mgf_log_eq_integral_rpow hpos (-p)
  rw [hnegative, htwo] at hexp
  exact hexp

end Critical2DKPZ.OnePoint

end
