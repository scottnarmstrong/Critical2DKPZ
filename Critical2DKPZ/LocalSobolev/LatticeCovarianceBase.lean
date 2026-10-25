/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeMass
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.Collision.ConditionalFlat
public import Critical2DKPZ.RandomWalk.Estimates
public import Critical2DKPZ.MomentBounds.CSZ25Green
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Covariance bounds for the flat lattice field -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Filter

namespace Critical2DKPZ.LocalSobolev

/-- At zero smoothing time the smoothed polymer mass is the point-to-plane mass. -/
theorem smoothedP2Plane_zero_eq_pointToPlane (β : ℝ) (n : ℕ) (x : Site) (ω : Disorder) :
    smoothedP2Plane β 0 n x ω = pointToPlane β 0 n x ω := by
  rw [Polymer.smoothedP2Plane_eq_sum]
  simp [Polymer.endpoints]

/-- The logarithm of a point-to-plane partition function is square-integrable. -/
theorem memLp_log_pointToPlane (β : ℝ) (a n : ℕ) (x : Site) :
    MemLp (fun ω => Real.log (pointToPlane β a n x ω)) 2 disorderLaw := by
  let ν : Site → ℝ := fun z => if z = x then 1 else 0
  let A : Finset Site := {x}
  have hνA : ∀ z ∉ A, ν z = 0 := by
    intro z hz
    have hz' : z ≠ x := by simpa [A] using hz
    simp [ν, hz']
  have hν0 (z : Site) : 0 ≤ ν z := by by_cases hz : z = x <;> simp [ν, hz]
  have hν1 : ∑ z ∈ A, ν z = 1 := by simp [A, ν]
  have hprofile (ω : Disorder) :
      profileP2Fun β a (a + n) ν (fun _ => 1) ω = pointToPlane β a n x ω := by
    rw [Polymer.profileP2Fun_eq_sum β a (a + n) ν (fun _ => 1) A hνA]
    simp only [Nat.add_sub_cancel_left]
    simpa [A, ν] using (Polymer.tsum_pointToPoint β a n x ω)
  have hdom := OnePoint.integrableExpSet_log_profileP2Fun_eq_univ β a (a + n)
    ν A hνA hν0 hν1
  have hprofileMem : MemLp
      (fun ω => Real.log (profileP2Fun β a (a + n) ν (fun _ => 1) ω))
      2 disorderLaw := by
    apply memLp_of_mem_interior_integrableExpSet
    rw [hdom, interior_univ]
    simp
  have heq : (fun ω => Real.log (profileP2Fun β a (a + n) ν (fun _ => 1) ω)) =
      fun ω => Real.log (pointToPlane β a n x ω) := by
    funext ω
    rw [hprofile]
  rw [← heq]
  exact hprofileMem

/-- Finite-polymer Gaussian calculus bounds the variance of a point-to-plane logarithm by the logarithm of its second moment. -/
theorem variance_log_pointToPlane_le_log_secondMoment (β : ℝ) (a n : ℕ) (x : Site) :
    Var[fun ω => Real.log (pointToPlane β a n x ω); disorderLaw] ≤
      Real.log (∫ ω, pointToPlane β a n x ω ^ 2 ∂disorderLaw) := by
  let ν : Site → ℝ := fun z => if z = x then 1 else 0
  let A : Finset Site := {x}
  have hνA : ∀ z ∉ A, ν z = 0 := by
    intro z hz
    have hz' : z ≠ x := by simpa [A] using hz
    simp [ν, hz']
  have hν0 (z : Site) : 0 ≤ ν z := by by_cases hz : z = x <;> simp [ν, hz]
  have hν1 : ∑ z ∈ A, ν z = 1 := by simp [A, ν]
  have hprofile (ω : Disorder) :
      profileP2Fun β a (a + n) ν (fun _ => 1) ω = pointToPlane β a n x ω := by
    rw [Polymer.profileP2Fun_eq_sum β a (a + n) ν (fun _ => 1) A hνA]
    simp only [Nat.add_sub_cancel_left]
    simpa [A, ν] using (Polymer.tsum_pointToPoint β a n x ω)
  let F : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β a (a + n) ν (fun _ => 1) ω)
  have hProfileInverseMomentInput := OnePoint.profileP2Fun_log_moment_bounds β a (a + n) ν A hνA hν0 hν1
  have hpos : ∀ ω, 0 < profileP2Fun β a (a + n) ν (fun _ => 1) ω :=
    OnePoint.profileP2Fun_pos_of_normalized β a (a + n) ν A hνA hν0 hν1
  have hmgf : mgf F disorderLaw 2 =
      ∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω ^ (2 : ℝ) ∂disorderLaw :=
        OnePoint.mgf_log_eq_integral_rpow hpos 2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Real.rpow_natCast _ 2
  have hprofileEq :
      (fun ω => Real.log (profileP2Fun β a (a + n) ν (fun _ => 1) ω)) =
        fun ω => Real.log (pointToPlane β a n x ω) := by
    funext ω
    rw [hprofile]
  have hmomentEq :
      (∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω ^ 2 ∂disorderLaw) =
        ∫ ω, pointToPlane β a n x ω ^ 2 ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hprofile]
  calc
    _ = Var[F; disorderLaw] :=
      congrArg (fun H : Disorder → ℝ => Var[H; disorderLaw]) hprofileEq.symm
    _ ≤ -2 * (∫ ω, F ω ∂disorderLaw) := hProfileInverseMomentInput.2.1
    _ ≤ Real.log (mgf F disorderLaw 2) := hProfileInverseMomentInput.2.2.1
    _ = Real.log (∫ ω, pointToPlane β a n x ω ^ 2 ∂disorderLaw) := by
      rw [hmgf, hmomentEq]

/-- A point-to-plane partition function has a strictly positive second moment. -/
theorem integral_sq_pointToPlane_pos (β : ℝ) (a n : ℕ) (x : Site) :
    0 < ∫ ω, pointToPlane β a n x ω ^ 2 ∂disorderLaw := by
  let ν : Site → ℝ := fun z => if z = x then 1 else 0
  let A : Finset Site := {x}
  have hνA : ∀ z ∉ A, ν z = 0 := by
    intro z hz
    have hz' : z ≠ x := by simpa [A] using hz
    simp [ν, hz']
  have hν0 (z : Site) : 0 ≤ ν z := by by_cases hz : z = x <;> simp [ν, hz]
  have hν1 : ∑ z ∈ A, ν z = 1 := by simp [A, ν]
  have hprofile (ω : Disorder) :
      profileP2Fun β a (a + n) ν (fun _ => 1) ω = pointToPlane β a n x ω := by
    rw [Polymer.profileP2Fun_eq_sum β a (a + n) ν (fun _ => 1) A hνA]
    simp only [Nat.add_sub_cancel_left]
    simpa [A, ν] using (Polymer.tsum_pointToPoint β a n x ω)
  let F : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β a (a + n) ν (fun _ => 1) ω)
  have hpos : ∀ ω, 0 < profileP2Fun β a (a + n) ν (fun _ => 1) ω :=
    OnePoint.profileP2Fun_pos_of_normalized β a (a + n) ν A hνA hν0 hν1
  have hdom := OnePoint.integrableExpSet_log_profileP2Fun_eq_univ β a (a + n)
    ν A hνA hν0 hν1
  have hmem2 : 2 ∈ integrableExpSet F disorderLaw := by
    dsimp [F]
    rw [hdom]
    simp
  have hmgfpos : 0 < mgf F disorderLaw 2 := ProbabilityTheory.mgf_pos hmem2
  have hmgf : mgf F disorderLaw 2 =
      ∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω ^ (2 : ℝ) ∂disorderLaw :=
        OnePoint.mgf_log_eq_integral_rpow hpos 2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Real.rpow_natCast _ 2
  have hmomentEq :
      (∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω ^ 2 ∂disorderLaw) =
        ∫ ω, pointToPlane β a n x ω ^ 2 ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hprofile]
  rw [← hmomentEq, ← hmgf]
  exact hmgfpos

/-- Spatial stationarity of the second moment of a point-to-plane mass. -/
theorem integral_sq_pointToPlane_eq_zero (β : ℝ) (n : ℕ) (x : Site) :
    (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) =
      ∫ ω, pointToPlane β 0 n 0 ω ^ 2 ∂disorderLaw := by
  let e := Gaussian.spatialTranslation x
  have hmp := Gaussian.measurePreserving_reindexDisorder e
  let eD : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ) e.symm
  have hefun : Gaussian.reindexDisorder e = eD := by
    funext ω p
    change ω (e p) = eD ω p
    symm
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
      (β := fun _ : ℕ × Site => ℝ) ω (e p)
    simpa [eD] using h
  have hshift (ω : Disorder) :
      (fun p : ℕ × Site => ω (p.1, p.2 + x)) = eD ω := by
    funext p
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
      (β := fun _ : ℕ × Site => ℝ) ω (e p)
    simpa [eD, e, Gaussian.spatialTranslation] using h.symm
  have hrewrite (ω : Disorder) :
      pointToPlane β 0 n x ω = pointToPlane β 0 n 0 (eD ω) := by
    have h := Polymer.pointToPlane_translate β 0 n 0 x ω
    simpa only [zero_add, hshift] using h
  have hmpD : MeasurePreserving eD disorderLaw disorderLaw := by
    rw [← hefun]
    exact hmp
  calc
    _ = ∫ ω, pointToPlane β 0 n 0 (Gaussian.reindexDisorder e ω) ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [hrewrite ω, ← hefun]
    _ = _ := by
      rw [hefun]
      exact hmpD.integral_comp' (fun ω : Disorder => pointToPlane β 0 n 0 ω ^ 2)

/-- A one-step normalized profile has a logarithmic second moment controlled by the size of
the Gaussian layer, uniformly over its finite initial profile. The squared logarithm is integrable
by `OnePoint.integrableExpSet_log_profileP2Fun_eq_univ`, as in the proof. -/
theorem integral_sq_log_profileP2Fun_oneStep_le (β : ℝ) (a : ℕ)
    (ν : Site → ℝ) (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0)
    (hν0 : ∀ w, 0 ≤ ν w) (hν1 : ∑ w ∈ A, ν w = 1) :
    (∫ ω, Real.log (profileP2Fun β a (a + 1) ν (fun _ => 1) ω) ^ 2 ∂disorderLaw) ≤
      β ^ 2 + β ^ 4 / 4 := by
  let F : Disorder → ℝ := fun ω => Real.log (profileP2Fun β a (a + 1) ν (fun _ => 1) ω)
  have hProfileInverseMomentInput := OnePoint.profileP2Fun_log_moment_bounds β a (a + 1) ν A hνA hν0 hν1
  have hpos : ∀ ω, 0 < profileP2Fun β a (a + 1) ν (fun _ => 1) ω :=
    OnePoint.profileP2Fun_pos_of_normalized β a (a + 1) ν A hνA hν0 hν1
  have hFmem : MemLp F 2 disorderLaw := by
    have hdom := OnePoint.integrableExpSet_log_profileP2Fun_eq_univ β a (a + 1)
      ν A hνA hν0 hν1
    apply memLp_of_mem_interior_integrableExpSet
    dsimp [F]
    rw [hdom, interior_univ]
    simp
  have hpair (w v : Site) : Polymer.pairMoment β 1 w v ≤ Real.exp (β ^ 2) := by
    rw [Polymer.pairMoment_firstCollision]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, Polymer.pairMoment_zero]
    have hk1 : srwKernel 2 (v - w) ≤ 1 := Polymer.srwKernel_le_one 2 (v - w)
    have he : 1 ≤ Real.exp (β ^ 2) := Real.one_le_exp (sq_nonneg β)
    have hprod : (Real.exp (β ^ 2) - 1) * srwKernel 2 (v - w) ≤
        Real.exp (β ^ 2) - 1 :=
      (mul_le_mul_of_nonneg_left hk1 (sub_nonneg.mpr he)).trans_eq (by ring)
    unfold Polymer.sigmaSq
    nlinarith [hprod]
  have hsecond :
      (∫ ω, profileP2Fun β a (a + 1) ν (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤
        Real.exp (β ^ 2) := by
    calc
      _ = ∫ ω, profileP2Fun β a (a + 1) ν (fun _ => 1) ω *
          profileP2Fun β a (a + 1) ν (fun _ => 1) ω ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [] with ω
            ring
      _ = ∑ w ∈ A, ∑ v ∈ A, ν w * ν v * Polymer.pairMoment β 1 w v :=
        Polymer.integral_profile_product_finset β a 1 ν ν A A hνA hνA
      _ ≤ ∑ w ∈ A, ∑ v ∈ A, ν w * ν v * Real.exp (β ^ 2) := by
        apply Finset.sum_le_sum
        intro w hw
        apply Finset.sum_le_sum
        intro v hv
        exact mul_le_mul_of_nonneg_left (hpair w v)
          (mul_nonneg (hν0 w) (hν0 v))
      _ = Real.exp (β ^ 2) := by
        have hinner (w : Site) :
            ∑ v ∈ A, ν w * ν v * Real.exp (β ^ 2) = ν w * Real.exp (β ^ 2) := by
          calc
            _ = ∑ v ∈ A, (ν w * ν v) * Real.exp (β ^ 2) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
            _ = (∑ v ∈ A, ν w * ν v) * Real.exp (β ^ 2) := by
              rw [← Finset.sum_mul]
            _ = (ν w * ∑ v ∈ A, ν v) * Real.exp (β ^ 2) := by
              rw [← Finset.mul_sum]
            _ = ν w * Real.exp (β ^ 2) := by rw [hν1]; ring
        calc
          _ = ∑ w ∈ A, ν w * Real.exp (β ^ 2) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact hinner w
          _ = Real.exp (β ^ 2) := by
            rw [← Finset.sum_mul, hν1]
            ring
  have hmgf : mgf F disorderLaw 2 =
      ∫ ω, profileP2Fun β a (a + 1) ν (fun _ => 1) ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, profileP2Fun β a (a + 1) ν (fun _ => 1) ω ^ (2 : ℝ) ∂disorderLaw :=
        OnePoint.mgf_log_eq_integral_rpow hpos 2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Real.rpow_natCast _ 2
  have hdom := OnePoint.integrableExpSet_log_profileP2Fun_eq_univ β a (a + 1)
    ν A hνA hν0 hν1
  have hmem2 : 2 ∈ integrableExpSet F disorderLaw := by
    dsimp [F]
    rw [hdom]
    simp
  have hmgfpos : 0 < mgf F disorderLaw 2 := ProbabilityTheory.mgf_pos hmem2
  have hlogmgf : Real.log (mgf F disorderLaw 2) ≤ β ^ 2 := by
    calc
      Real.log (mgf F disorderLaw 2) ≤ Real.log (Real.exp (β ^ 2)) :=
        Real.log_le_log hmgfpos (hmgf ▸ hsecond)
      _ = β ^ 2 := Real.log_exp _
  have hmean : -2 * (∫ ω, F ω ∂disorderLaw) ≤ β ^ 2 := by
    exact (hProfileInverseMomentInput.2.2.1).trans hlogmgf
  have hvar : Var[F; disorderLaw] ≤ β ^ 2 := hProfileInverseMomentInput.2.1.trans hmean
  have hmeanNonpos : ∫ ω, F ω ∂disorderLaw ≤ 0 := by
    unfold gaussianityDefect at hProfileInverseMomentInput
    have hdef := hProfileInverseMomentInput.1
    have hvar0 : 0 ≤ Var[F; disorderLaw] := variance_nonneg F disorderLaw
    linarith
  have hmeanAbs : |∫ ω, F ω ∂disorderLaw| ≤ β ^ 2 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hF2 :
      (∫ ω, F ω ^ 2 ∂disorderLaw) = Var[F; disorderLaw] +
        (∫ ω, F ω ∂disorderLaw) ^ 2 := by
    have h := variance_eq_sub hFmem
    have h' : Var[F; disorderLaw] =
        (∫ ω, F ω ^ 2 ∂disorderLaw) - (∫ ω, F ω ∂disorderLaw) ^ 2 := by
      simpa only [Pi.pow_apply] using h
    linarith
  have hmeanSq : (∫ ω, F ω ∂disorderLaw) ^ 2 ≤ (β ^ 2 / 2) ^ 2 := by
    nlinarith [abs_le.mp hmeanAbs]
  change (∫ ω, F ω ^ 2 ∂disorderLaw) ≤ _
  rw [hF2]
  nlinarith [hvar, hmeanSq, sq_nonneg (β ^ 2)]

/-- The logarithmic increment from a point-to-plane mass to the next layer has a second moment
of order the Gaussian variance, even when its endpoint profile is random and measurable with respect to the past.
Both logarithms are in `L²` by `memLp_log_pointToPlane`, so the integrand is integrable. -/
theorem integral_sq_log_pointToPlane_succ_increment_le (β : ℝ) (n : ℕ) (x : Site) :
    (∫ ω, (Real.log (pointToPlane β 0 (n + 1) x ω) -
      Real.log (pointToPlane β 0 n x ω)) ^ 2 ∂disorderLaw) ≤ β ^ 2 + β ^ 4 / 4 := by
  let A : Finset Site := Polymer.endpoints x n
  let η : Disorder → Site → ℝ := fun ω z => endpointDist β n x ω z
  let F : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β n (n + 1) (η ω) (fun _ => 1) ω)
  have hsupp (ω : Disorder) (z : Site) (hz : z ∉ A) : η ω z = 0 :=
    (Smoothing.endpointDist_probability β n x ω).1 z (by simpa [A] using hz)
  have hnonneg (ω : Disorder) (z : Site) : 0 ≤ η ω z :=
    (Smoothing.endpointDist_probability β n x ω).2.1 z
  have hnorm (ω : Disorder) : ∑ z ∈ A, η ω z = 1 :=
    (Smoothing.endpointDist_probability β n x ω).2.2
  have hprofilePos (ω : Disorder) :
      0 < profileP2Fun β n (n + 1) (η ω) (fun _ => 1) ω :=
    OnePoint.profileP2Fun_pos_of_normalized β n (n + 1) (η ω) A
      (hsupp ω) (hnonneg ω) (hnorm ω) ω
  have hfactor (ω : Disorder) :=
    pointToPlane_succ_eq_mul_endpointProfile β n x ω
  have hF_eq : F = (fun ω => Real.log (pointToPlane β 0 (n + 1) x ω)) -
      (fun ω => Real.log (pointToPlane β 0 n x ω)) := by
    funext ω
    dsimp [F]
    rw [hfactor ω, Real.log_mul
      (ne_of_gt (Polymer.pointToPlane_pos β 0 n x ω)) (ne_of_gt (hprofilePos ω))]
    ring
  have hFmem : MemLp F 2 disorderLaw := by
    rw [hF_eq]
    exact (memLp_log_pointToPlane β 0 (n + 1) x).sub
      (memLp_log_pointToPlane β 0 n x)
  have hFmeas : Measurable F := by
    rw [hF_eq]
    exact (Real.measurable_log.comp (Polymer.measurable_pointToPlane β 0 (n + 1) x)).sub
      (Real.measurable_log.comp (Polymer.measurable_pointToPlane β 0 n x))
  have hF2int : Integrable (fun ω => F ω ^ 2) disorderLaw := hFmem.integrable_sq
  have hF2meas : Measurable (fun ω => F ω ^ 2) := hFmeas.pow_const 2
  have hηmeas (z : Site) : Measurable[disorderPast n] (η · z) := by
    exact Polymer.measurable_endpointDist_past β n x z
  have hresample (ω ξ : Disorder) :
      F (Gaussian.resample (Gaussian.timeBlock 0 n) ω ξ) =
        Real.log (profileP2Fun β n (n + 1) (η ω) (fun _ => 1) ξ) := by
    dsimp [F]
    rw [Collision.profileP2Fun_resamplePast β n (n + 1) A η hsupp hηmeas ω ξ]
    rw [show n + 1 - n = 1 by omega]
    have hsum :
        (∑ z ∈ A, η ω z * pointToPlane β n 1 z ξ) =
          profileP2Fun β n (n + 1) (η ω) (fun _ => 1) ξ := by
      rw [Polymer.profileP2Fun_eq_sum β n (n + 1) (η ω) (fun _ => 1) A (hsupp ω)]
      rw [show n + 1 - n = 1 by omega]
      simp only [mul_one]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Polymer.tsum_pointToPoint]
    rw [hsum]
  have hce := Gaussian.condExp_disorderBlock_ae_eq 0 n hF2meas hF2int
  rw [Gaussian.disorderBlock_zero] at hce
  have hcondBound :
      disorderLaw[(fun ω => F ω ^ 2) | disorderPast n] ≤ᵐ[disorderLaw]
        fun _ => β ^ 2 + β ^ 4 / 4 := by
    filter_upwards [hce] with ω hω
    rw [hω]
    calc
      _ = ∫ ξ, Real.log (profileP2Fun β n (n + 1) (η ω) (fun _ => 1) ξ) ^ 2
          ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            rw [← hresample ω ξ]
      _ ≤ β ^ 2 + β ^ 4 / 4 :=
        integral_sq_log_profileP2Fun_oneStep_le β n (η ω) A (hsupp ω)
          (hnonneg ω) (hnorm ω)
  calc
    _ = ∫ ω, F ω ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [hF_eq]
      simp only [Pi.sub_apply]
    _ = ∫ ω, disorderLaw[(fun ω => F ω ^ 2) | disorderPast n] ω ∂disorderLaw := by
      symm
      have hpastle : disorderPast n ≤ (inferInstance : MeasurableSpace Disorder) := by
        rw [← Gaussian.disorderBlock_zero n]
        exact Gaussian.disorderBlock_le 0 n
      exact integral_condExp hpastle
    _ ≤ ∫ _ω, β ^ 2 + β ^ 4 / 4 ∂disorderLaw :=
      integral_mono_ae integrable_condExp (integrable_const _) hcondBound
    _ = β ^ 2 + β ^ 4 / 4 := by simp

/-- Cauchy--Schwarz for covariance, in the variance normalization. -/
theorem abs_covariance_le_sqrt_variances {X Y : Disorder → ℝ}
    (hX : MemLp X 2 disorderLaw) (hY : MemLp Y 2 disorderLaw) :
    |covariance X Y disorderLaw| ≤
      Real.sqrt (Var[X; disorderLaw] * Var[Y; disorderLaw]) := by
  let vx := Var[X; disorderLaw]
  let vy := Var[Y; disorderLaw]
  let c := covariance X Y disorderLaw
  have hvx : 0 ≤ vx := by dsimp [vx]; exact variance_nonneg X disorderLaw
  have hvy : 0 ≤ vy := by dsimp [vy]; exact variance_nonneg Y disorderLaw
  have hquad (t : ℝ) : 0 ≤ vx + 2 * t * c + t ^ 2 * vy := by
    have h := variance_nonneg (X + fun ω => t * Y ω) disorderLaw
    rw [variance_add hX (hY.const_mul t), variance_const_mul,
      covariance_const_mul_right] at h
    dsimp [vx, vy, c]
    nlinarith [h]
  have hcv : c ^ 2 ≤ vx * vy := by
    by_cases hpos : 0 < vy
    · have h := hquad (-c / vy)
      have h' : 0 ≤ vx * vy - c ^ 2 := by
        field_simp [ne_of_gt hpos] at h
        nlinarith [h, hpos]
      nlinarith
    · have hy0 : vy = 0 := le_antisymm (not_lt.mp hpos) hvy
      by_contra hnot
      have hcne : c ≠ 0 := by
        intro hc
        apply hnot
        rw [hc, hy0]
        norm_num
      have h := hquad (-(vx + 1) / (2 * c))
      rw [hy0] at h
      have hden : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hcne
      have hcancel : 2 * (-(vx + 1) / (2 * c)) * c = -(vx + 1) := by
        field_simp [hden]
      rw [hcancel] at h
      nlinarith [h]
  have hprod : Real.sqrt (vx * vy) ^ 2 = vx * vy := by
    rw [Real.sq_sqrt (mul_nonneg hvx hvy)]
  have habs : 0 ≤ |c| := abs_nonneg _
  have hsqrt : 0 ≤ Real.sqrt (vx * vy) := Real.sqrt_nonneg _
  have habs_sq : |c| ^ 2 = c ^ 2 := sq_abs c
  have hmain : |c| ≤ Real.sqrt (vx * vy) := by
    nlinarith [hcv, sq_nonneg (|c| - Real.sqrt (vx * vy))]
  simpa [vx, vy, c] using hmain

/-- Adding two square-integrable error terms changes a covariance by at most the three
variance Cauchy--Schwarz bounds. -/
theorem covariance_add_add_le_of {X Y D E : Disorder → ℝ}
    (hX : MemLp X 2 disorderLaw) (hY : MemLp Y 2 disorderLaw)
    (hD : MemLp D 2 disorderLaw) (hE : MemLp E 2 disorderLaw) :
    covariance (X + D) (Y + E) disorderLaw ≤
      covariance X Y disorderLaw +
        Real.sqrt (Var[D; disorderLaw] * Var[Y; disorderLaw]) +
        Real.sqrt (Var[X; disorderLaw] * Var[E; disorderLaw]) +
        Real.sqrt (Var[D; disorderLaw] * Var[E; disorderLaw]) := by
  rw [covariance_add_left hX hD (hY.add hE), covariance_add_right hX hY hE,
    covariance_add_right hD hY hE]
  have hDY : covariance D Y disorderLaw ≤
      Real.sqrt (Var[D; disorderLaw] * Var[Y; disorderLaw]) :=
    (le_abs_self _).trans (abs_covariance_le_sqrt_variances hD hY)
  have hXE : covariance X E disorderLaw ≤
      Real.sqrt (Var[X; disorderLaw] * Var[E; disorderLaw]) :=
    (le_abs_self _).trans (abs_covariance_le_sqrt_variances hX hE)
  have hDE : covariance D E disorderLaw ≤
      Real.sqrt (Var[D; disorderLaw] * Var[E; disorderLaw]) :=
    (le_abs_self _).trans (abs_covariance_le_sqrt_variances hD hE)
  linarith

/-- A bounded Gaussianity defect transfers across an additive error, with the covariance cost
controlled by the two variances. -/
theorem gaussianityDefect_le_add_of {F D : Disorder → ℝ}
    (hF : MemLp F 2 disorderLaw) (hD : MemLp D 2 disorderLaw)
    (C : ℝ) (hDdef : |gaussianityDefect disorderLaw D| ≤ C) :
    gaussianityDefect disorderLaw F ≤
      gaussianityDefect disorderLaw (F + D) + C +
        Real.sqrt (Var[F; disorderLaw] * Var[D; disorderLaw]) := by
  have hidentity : gaussianityDefect disorderLaw (F + D) =
      gaussianityDefect disorderLaw F + gaussianityDefect disorderLaw D -
        covariance F D disorderLaw := by
    unfold gaussianityDefect
    change -(∫ ω, F ω + D ω ∂disorderLaw) - Var[F + D; disorderLaw] / 2 = _
    rw [integral_add (hF.integrable (by norm_num)) (hD.integrable (by norm_num)),
      variance_add hF hD]
    ring
  have hcov := abs_covariance_le_sqrt_variances hF hD
  rw [hidentity]
  have hleft : -gaussianityDefect disorderLaw D ≤ C := by
    calc
      _ ≤ |gaussianityDefect disorderLaw D| := neg_le_abs _
      _ ≤ C := hDdef
  have hcov' : covariance F D disorderLaw ≤
      Real.sqrt (Var[F; disorderLaw] * Var[D; disorderLaw]) :=
    (le_abs_self _).trans hcov
  linarith

/-- A bounded defect at the next point-to-plane horizon transfers to the preceding horizon;
the cost is controlled by the next-layer logarithmic moment. -/
theorem gaussianityDefect_pointToPlane_le_of_succ (β : ℝ) (n : ℕ) (x : Site)
    (E : ℝ) (hM : 0 < ∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw)
    (hEven : gaussianityDefect disorderLaw
      (fun ω => Real.log (pointToPlane β 0 (n + 1) x ω)) ≤ E) :
    gaussianityDefect disorderLaw
      (fun ω => Real.log (pointToPlane β 0 n x ω)) ≤
        E + 1 + (3 / 2) * (β ^ 2 + β ^ 4 / 4) +
          Real.sqrt (2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) *
            (β ^ 2 + β ^ 4 / 4)) := by
  let F : Disorder → ℝ := fun ω => Real.log (pointToPlane β 0 n x ω)
  let G : Disorder → ℝ := fun ω => Real.log (pointToPlane β 0 (n + 1) x ω)
  let D : Disorder → ℝ := G - F
  let q : ℝ := β ^ 2 + β ^ 4 / 4
  change gaussianityDefect disorderLaw F ≤
    E + 1 + (3 / 2) * q +
      Real.sqrt (2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) * q)
  have hFmem : MemLp F 2 disorderLaw := memLp_log_pointToPlane β 0 n x
  have hGmem : MemLp G 2 disorderLaw := memLp_log_pointToPlane β 0 (n + 1) x
  have hDmem : MemLp D 2 disorderLaw := by
    dsimp [D]
    exact hGmem.sub hFmem
  have hD2 : (∫ ω, D ω ^ 2 ∂disorderLaw) ≤ q := by
    dsimp [D, G, F, q]
    exact integral_sq_log_pointToPlane_succ_increment_le β n x
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hDvar : Var[D; disorderLaw] ≤ q := by
    calc
      _ ≤ ∫ ω, D ω ^ 2 ∂disorderLaw :=
        variance_le_expectation_sq hDmem.aestronglyMeasurable
      _ ≤ q := hD2
  have hDmeanSq : (∫ ω, D ω ∂disorderLaw) ^ 2 ≤ q := by
    have hvar := variance_eq_sub hDmem
    have hnonneg := variance_nonneg D disorderLaw
    calc
      _ ≤ ∫ ω, D ω ^ 2 ∂disorderLaw := by
        have hvar' : Var[D; disorderLaw] =
            (∫ ω, D ω ^ 2 ∂disorderLaw) - (∫ ω, D ω ∂disorderLaw) ^ 2 := by
          simpa only [Pi.pow_apply] using hvar
        linarith
      _ ≤ q := hD2
  have hDmeanAbs : |∫ ω, D ω ∂disorderLaw| ≤ 1 + q := by
    rw [abs_le]
    constructor <;> nlinarith [hDmeanSq, hq, sq_nonneg q]
  have hDdef : |gaussianityDefect disorderLaw D| ≤ 1 + (3 / 2) * q := by
    unfold gaussianityDefect
    rw [abs_le]
    have hmean := abs_le.mp hDmeanAbs
    have hDvar0 : 0 ≤ Var[D; disorderLaw] := variance_nonneg D disorderLaw
    constructor <;> linarith [hmean.1, hmean.2, hDvar0, hDvar, hq]
  have hFvar : Var[F; disorderLaw] ≤
      2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) := by
    have hv := variance_log_pointToPlane_le_log_secondMoment β 0 n x
    have hlog := Real.log_le_sub_one_of_pos hM
    dsimp [F]
    linarith
  have hprod : Var[F; disorderLaw] * Var[D; disorderLaw] ≤
      2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) * q := by
    have hF0 : 0 ≤ Var[F; disorderLaw] := variance_nonneg F disorderLaw
    have hD0 : 0 ≤ Var[D; disorderLaw] := variance_nonneg D disorderLaw
    have hM0 : 0 ≤ 2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) := by positivity
    exact (mul_le_mul hFvar hDvar hD0 hM0).trans_eq (by ring)
  have hroot : Real.sqrt (Var[F; disorderLaw] * Var[D; disorderLaw]) ≤
      Real.sqrt (2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) * q) :=
    Real.sqrt_le_sqrt hprod
  have hsum : F + D = G := by
    funext ω
    simp [F, G, D]
  have htransfer := gaussianityDefect_le_add_of hFmem hDmem (1 + (3 / 2) * q) hDdef
  rw [hsum] at htransfer
  calc
    gaussianityDefect disorderLaw F ≤
        gaussianityDefect disorderLaw G + (1 + (3 / 2) * q) +
          Real.sqrt (Var[F; disorderLaw] * Var[D; disorderLaw]) := htransfer
    _ ≤ E + (1 + (3 / 2) * q) +
          Real.sqrt (2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) * q) := by
      gcongr
    _ = E + 1 + (3 / 2) * q +
          Real.sqrt (2 * (∫ ω, pointToPlane β 0 n x ω ^ 2 ∂disorderLaw) * q) := by ring

private theorem sum_inv_add_le_log (n : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    (∑ r ∈ Finset.Icc 1 n, ((r : ℝ) + q)⁻¹) ≤
      1 + Real.log (1 + (n : ℝ) / (1 + q)) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hsplit : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hshift :
      (∑ r ∈ Finset.Icc 2 n, ((r : ℝ) + q)⁻¹) =
        ∑ i ∈ Finset.Ico 1 n, ((i : ℝ) + 1 + q)⁻¹ := by
    classical
    refine Finset.sum_bij (fun r _ => r - 1) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      simp only [Finset.mem_Ico]
      omega
    · intro r₁ hr₁ r₂ hr₂ h
      simp only [Finset.mem_Icc] at hr₁ hr₂
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      refine ⟨i + 1, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · exact Nat.add_sub_cancel i 1
    · intro r hr
      have hr1' : 1 ≤ r := le_trans (by norm_num) (Finset.mem_Icc.mp hr).1
      have hcast : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by
        rw [Nat.cast_sub hr1']
        simp
      rw [← hcast]
  rw [hshift]
  have hanti : AntitoneOn (fun x : ℝ => (x + q)⁻¹) (Set.Icc 1 (n : ℝ)) := by
    intro x hx y hy hxy
    apply inv_anti₀ (by linarith [hq, hx.1])
    linarith
  have hanti' : AntitoneOn (fun x : ℝ => (x + q)⁻¹)
      (Set.Icc (↑(1 : ℕ) : ℝ) (n : ℝ)) := by simpa using hanti
  have hsumInt := AntitoneOn.sum_le_integral_Ico hn1 hanti'
  have hsumInt' :
      ∑ i ∈ Finset.Ico 1 n, ((i : ℝ) + 1 + q)⁻¹ ≤
        ∫ x in (1 : ℝ)..(n : ℝ), (x + q)⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsumInt
  have hint :
      (∫ x in (1 : ℝ)..(n : ℝ), (x + q)⁻¹) =
        Real.log (((n : ℝ) + q) / (1 + q)) := by
    rw [intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => x⁻¹) q]
    exact integral_inv_of_pos (by positivity) (by positivity)
  have hlog : Real.log (((n : ℝ) + q) / (1 + q)) ≤
      Real.log (1 + (n : ℝ) / (1 + q)) := by
    apply Real.log_le_log (by positivity)
    calc
      ((n : ℝ) + q) / (1 + q) ≤ ((n : ℝ) + q + 1) / (1 + q) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 1 + (n : ℝ) / (1 + q) := by
        field_simp [ne_of_gt (by positivity : 0 < 1 + q)]
        ring
  have hfirst : ((1 : ℝ) + q)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    linarith
  calc
    ((↑(1 : ℕ) : ℝ) + q)⁻¹ +
        ∑ i ∈ Finset.Ico 1 n, ((i : ℝ) + 1 + q)⁻¹
        ≤ 1 + ∫ x in (1 : ℝ)..(n : ℝ), (x + q)⁻¹ := by
      simpa only [Nat.cast_one] using add_le_add hfirst hsumInt'
    _ ≤ 1 + Real.log (1 + (n : ℝ) / (1 + q)) := by rw [hint]; linarith

/-- The truncated Green function is at most a constant times `1 + log (1 + n / (1 + ‖z‖ ^ 2))`,
uniformly in the horizon `n` and the site `z`. -/
theorem truncatedGreen_le_log_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, ∀ z : Site,
      MomentBounds.truncatedGreen n z ≤
        B * (1 + Real.log (1 + (n : ℝ) / (1 + ‖siteToPlane z‖ ^ 2))) := by
  obtain ⟨A, c, hc, hgauss⟩ := srwKernel_gaussianBound
  have hA : 0 < A := by
    have h := hgauss 2 (by omega) (0 : Site)
    have hp := srwKernel_two_zero_pos
    have hsite : siteToPlane (0 : Site) = 0 := by
      ext i
      simp [siteToPlane]
    have h' : srwKernel 2 0 ≤ A / 2 := by simpa [hsite] using h
    linarith
  let a : ℝ := c / 2
  let K : ℝ := 1 + a⁻¹
  let B : ℝ := A * K / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hB0 : 0 ≤ B := le_of_lt (by dsimp [B]; positivity)
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    positivity
  intro n z
  by_cases hn : n = 0
  · simpa [hn, MomentBounds.truncatedGreen] using hB0
  have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 n) :
      srwKernel (2 * r) z ≤ B / ((r : ℝ) + ‖siteToPlane z‖ ^ 2) := by
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr1)
    have hkernel := hgauss (2 * r) (by omega) z
    have hExp :
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / (2 * r)) ≤
          K / (1 + ‖siteToPlane z‖ ^ 2 / r) := by
      have hu : 0 ≤ ‖siteToPlane z‖ ^ 2 / r := by positivity
      have hden : 0 < 1 + a * (‖siteToPlane z‖ ^ 2 / r) := by positivity
      have hexp :
          Real.exp (-(a * (‖siteToPlane z‖ ^ 2 / r))) ≤
            1 / (1 + a * (‖siteToPlane z‖ ^ 2 / r)) := by
        rw [Real.exp_neg]
        have hInv : (Real.exp (a * (‖siteToPlane z‖ ^ 2 / r)))⁻¹ ≤
            (1 + a * (‖siteToPlane z‖ ^ 2 / r))⁻¹ :=
          (inv_le_inv₀ (Real.exp_pos _) hden).2 (by
            have h := Real.add_one_le_exp (a * (‖siteToPlane z‖ ^ 2 / r))
            linarith)
        simpa only [one_div] using hInv
      have hratio :
          1 / (1 + a * (‖siteToPlane z‖ ^ 2 / r)) ≤
            K / (1 + ‖siteToPlane z‖ ^ 2 / r) := by
        apply (div_le_div_iff₀ hden (by positivity)).2
        dsimp [K]
        rw [one_mul]
        have hu' : a⁻¹ * (a * (‖siteToPlane z‖ ^ 2 / r)) =
            ‖siteToPlane z‖ ^ 2 / r := by
          rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
        have haInv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
        have hau : 0 ≤ a * (‖siteToPlane z‖ ^ 2 / r) := mul_nonneg ha.le hu
        calc
          1 + ‖siteToPlane z‖ ^ 2 / r ≤
              1 + ‖siteToPlane z‖ ^ 2 / r + a⁻¹ +
                a * (‖siteToPlane z‖ ^ 2 / r) := by linarith
          _ = (1 + a⁻¹) *
              (1 + a * (‖siteToPlane z‖ ^ 2 / r)) := by
                simp only [mul_add, add_mul, one_mul, mul_one, hu']
                ring
      have harg :
          -c * ‖siteToPlane z‖ ^ 2 / (2 * r) =
            -(a * (‖siteToPlane z‖ ^ 2 / r)) := by
        dsimp [a]
        field_simp
      rw [harg]
      exact hexp.trans hratio
    have hkernel' : srwKernel (2 * r) z ≤
        A / (2 * (r : ℝ)) * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / (2 * (r : ℝ))) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hkernel
    have hscale := mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ A / (2 * (r : ℝ)))
    have heq :
        A / (2 * (r : ℝ)) * (K / (1 + ‖siteToPlane z‖ ^ 2 / r)) =
          B / ((r : ℝ) + ‖siteToPlane z‖ ^ 2) := by
      dsimp [B]
      field_simp [ne_of_gt hrR]
    calc
      srwKernel (2 * r) z ≤
          A / (2 * (r : ℝ)) * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / (2 * (r : ℝ))) := hkernel'
      _ ≤ A / (2 * (r : ℝ)) *
          (K / (1 + ‖siteToPlane z‖ ^ 2 / r)) := hscale
      _ = B / ((r : ℝ) + ‖siteToPlane z‖ ^ 2) := heq
  rw [MomentBounds.truncatedGreen]
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 n, B / ((r : ℝ) + ‖siteToPlane z‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r hr
    _ = ∑ r ∈ Finset.Icc 1 n,
          B * ((r : ℝ) + ‖siteToPlane z‖ ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [div_eq_mul_inv]
    _ = B * ∑ r ∈ Finset.Icc 1 n,
          ((r : ℝ) + ‖siteToPlane z‖ ^ 2)⁻¹ := by
      rw [← Finset.mul_sum]
    _ ≤ B * (1 + Real.log (1 + (n : ℝ) /
          (1 + ‖siteToPlane z‖ ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_inv_add_le_log n _ (sq_nonneg _)) (le_of_lt (by dsimp [B]; positivity))


end Critical2DKPZ.LocalSobolev

end
