/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Assembly.LatticeCentring
public import Critical2DKPZ.LocalSobolev.LatticeProfileMass
public import Critical2DKPZ.LocalSobolev.LatticeReversalProfileIdentity
public import Critical2DKPZ.Gaussian.DisorderLaws
import Mathlib.Tactic

/-! # Exact-clock forward/reversed lattice profile identity -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

private theorem profileP2Fun_point_flat_eq_pointToPlane (β : ℝ) (m : ℕ)
    (x : Site) (ω : Disorder) :
    profileP2Fun β 0 m (fun z => if z = x then 1 else 0) (fun _ => 1) ω =
      pointToPlane β 0 m x ω := by
  classical
  unfold profileP2Fun
  simp only [Nat.sub_zero, ite_mul, one_mul, zero_mul, tsum_ite_eq]
  simpa using Polymer.tsum_pointToPoint β 0 m x ω

/-- The flat exact-clock reversed profile has mean log equal to the mean log point-to-plane
mass over the corresponding forward duration. -/
theorem integral_log_exactReverse_flatProfile_eq_pointToPlane (β : ℝ)
    {L m : ℕ} (hmL : m ≤ L) (x : Site) :
    Integrable (fun ω => Real.log (profileP2Fun β (L - m) L
      (fun z => if z = x then 1 else 0) (fun _ => 1) ω)) disorderLaw ∧
    (∫ ω, Real.log (profileP2Fun β (L - m) L
      (fun z => if z = x then 1 else 0) (fun _ => 1) ω) ∂disorderLaw) =
      ∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw := by
  let ν : Site → ℝ := fun z => if z = x then 1 else 0
  let q := L - m
  have hqm : L - q = m := by dsimp [q]; omega
  have hqL : q ≤ L := by dsimp [q]; omega
  have hpoint (ω : Disorder) : profileP2Fun β q L ν (fun _ => 1) ω =
      pointToPlane β 0 m x (Smoothing.shiftEnvironment q ω) := by
    have hshift := Smoothing.profileP2Fun_timeShift_sub β (d := q) (a := q) (b := L)
      (le_rfl) hqL ν
      (fun _ => 1) ω
    calc
      _ = profileP2Fun β 0 (L - q) ν (fun _ => 1)
          (Smoothing.shiftEnvironment q ω) := by simpa [q] using hshift
      _ = pointToPlane β 0 m x (Smoothing.shiftEnvironment q ω) := by
        rw [hqm]
        exact profileP2Fun_point_flat_eq_pointToPlane β m x _
  have hlogmeas (z : Site) : Measurable (fun ω => Real.log (pointToPlane β 0 m z ω)) :=
    (Polymer.measurable_pointToPlane β 0 m z).log
  have hlogint (z : Site) : Integrable
      (fun ω => Real.log (pointToPlane β 0 m z ω)) disorderLaw :=
    (LocalSobolev.memLp_log_pointToPlane β 0 m z).integrable (by norm_num)
  have hcenter : Integrable (fun ω => Real.log (profileP2Fun β q L ν
      (fun _ => 1) ω)) disorderLaw := by
    have heq : (fun ω => Real.log (profileP2Fun β q L ν (fun _ => 1) ω)) =
        fun ω => Real.log (pointToPlane β 0 m x (Smoothing.shiftEnvironment q ω)) := by
      funext ω
      rw [hpoint ω]
    rw [heq]
    exact (Smoothing.measurePreserving_shiftEnvironment q).integrable_comp_of_integrable
      (hlogint x)
  refine ⟨hcenter, ?_⟩
  have htime :
      (∫ ω, Real.log (pointToPlane β 0 m x (Smoothing.shiftEnvironment q ω))
          ∂disorderLaw) =
        ∫ ω, Real.log (pointToPlane β 0 m x ω) ∂disorderLaw :=
    Smoothing.integral_shiftEnvironment q (hlogmeas x)
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x)
  have hspaceFun :
      (fun ω => Real.log (pointToPlane β 0 m x ω)) =
        fun ω => Real.log (pointToPlane β 0 m 0 (τ ω)) := by
    funext ω
    have htranslate : pointToPlane β 0 m x ω =
        pointToPlane β 0 m 0 (fun p => ω (p.1, p.2 + x)) := by
      simpa only [zero_add] using Polymer.pointToPlane_translate β 0 m 0 x ω
    rw [htranslate]
  let e := Gaussian.spatialTranslation x
  let eD : MeasurableEquiv Disorder Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ) e.symm
  have hefun : Gaussian.reindexDisorder e = eD := by
    funext ω p
    change ω (e p) = eD ω p
    symm
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
      (β := fun _ : ℕ × Site => ℝ) ω (e p)
    simpa [eD] using h
  have hτeq : τ = eD := by
    funext ω p
    change ω (e p) = eD ω p
    symm
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
      (β := fun _ : ℕ × Site => ℝ) ω (e p)
    simpa [τ, eD, e, Gaussian.spatialTranslation] using h
  have hmpD : MeasurePreserving eD disorderLaw disorderLaw := by
    rw [← hefun]
    exact Gaussian.measurePreserving_reindexDisorder e
  have hspace :
      (∫ ω, Real.log (pointToPlane β 0 m x ω) ∂disorderLaw) =
        ∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw := by
    rw [hspaceFun, hτeq]
    exact hmpD.integral_comp' (fun ω : Disorder => Real.log (pointToPlane β 0 m 0 ω))
  calc
    _ = ∫ ω, Real.log (pointToPlane β 0 m x
        (Smoothing.shiftEnvironment q ω)) ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            simpa [q, ν] using congrArg Real.log (hpoint ω)
    _ = ∫ ω, Real.log (pointToPlane β 0 m x ω) ∂disorderLaw := htime
    _ = _ := hspace

/-- The forward lattice logarithm is the exact-clock reversed profile logarithm plus the
explicit initial-slice and terminal-profile corrections. The centering remains displayed. -/
theorem kpzLattice_exactReverseProfile_log_identity (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) (t T : ℝ) (htT : t ≤ T) (h0 : Plane →ᵇ ℝ)
    (x : Plane) (ω : Disorder) (hm : 1 ≤ evenCeil ((N : ℝ) * t)) :
    let m := evenCeil ((N : ℝ) * t)
    let L := evenCeil ((N : ℝ) * T)
    let x0 := latticePoint N x
    let β := criticalBeta ϑ N
    let f := cellAverage N (fun y => Real.exp (h0 y))
    let ω' := Smoothing.shiftEnvironment (L - m)
      (PolymerCalculus.reversedDisorder L ω)
    let η := endpointDist β (m - 1) x0 ω'
    kpzLattice ϑ N t h0 x ω =
      Real.log (profileP2Fun β (L - m) L (fun z => if z = x0 then 1 else 0)
        f (PolymerCalculus.reversedDisorder L ω)) +
        (β * ω (m, x0) - β ^ 2 / 2 +
          (Real.log (profileP2Fun 0 (m - 1) m η f ω') -
            Real.log (profileP2Fun β (m - 1) m η f ω'))) -
        kpzLatticeCentring ϑ N t := by
  dsimp only
  let m := evenCeil ((N : ℝ) * t)
  let L := evenCeil ((N : ℝ) * T)
  let x0 := latticePoint N x
  let β := criticalBeta ϑ N
  let f := cellAverage N (fun y => Real.exp (h0 y))
  have hmEven : Even m := by simpa [m] using evenCeil_even ((N : ℝ) * t)
  have hmL : m ≤ L := by
    dsimp [m, L]
    exact evenCeil_mono
      (mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg N))
  have hxEven : Even (x0 0 + x0 1) := by
    have hx := latticePoint_mem_evenLattice N x
    simpa [x0, evenLattice] using hx
  have hfEven (z : Site) (hz : Even (z 0 + z 1)) : 0 < f z := by
    exact (Smoothing.cellAverage_exp_bounds_of_even N hN h0 hz).1
  have hmass := integral_rescaledP2P_profile_eq_tsum ϑ hN t x h0 ω (by simpa [m] using hmEven)
  have hidentity := log_tsum_pointToPoint_time_reversal_sub_profile_of_even
    β hmL hm hmEven x0 hxEven f hfEven ω
  unfold kpzLattice
  rw [hmass]
  change Real.log (∑' z : Site, f z * pointToPoint β 0 m z x0 ω) -
      kpzLatticeCentring ϑ N t = _
  rw [← sub_add_cancel (Real.log (∑' z : Site, f z * pointToPoint β 0 m z x0 ω))
    (kpzLatticeCentring ϑ N t)]
  linarith [hidentity]

end Critical2DKPZ.LocalSobolev

end
