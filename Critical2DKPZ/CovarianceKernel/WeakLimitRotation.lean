/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakCovarianceLimit

/-! # Rotation invariance of weak `L²` limits -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Critical2DKPZ.CovarianceKernel

private noncomputable def pullbackL2 (R : Plane ≃ₗᵢ[ℝ] Plane)
    (f : Lp ℝ 2 (volume : Measure Plane)) : Lp ℝ 2 (volume : Measure Plane) :=
  Lp.compMeasurePreserving R (LinearIsometryEquiv.measurePreserving R) f

private theorem inner_pullbackL2 (R : Plane ≃ₗᵢ[ℝ] Plane)
    (f g : Lp ℝ 2 (volume : Measure Plane)) :
    inner ℝ (pullbackL2 R f) g = inner ℝ f (pullbackL2 R.symm g) := by
  have hleft : inner ℝ (pullbackL2 R f) g = ∫ z : Plane, f (R z) * g z := by
    change inner ℝ (Lp.compMeasurePreserving R
      (LinearIsometryEquiv.measurePreserving R) f) g = _
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving f
      (LinearIsometryEquiv.measurePreserving R)] with z hz
    rw [hz]
    rfl
  have hright : inner ℝ f (pullbackL2 R.symm g) =
      ∫ z : Plane, f z * g (R.symm z) := by
    change inner ℝ f (Lp.compMeasurePreserving R.symm
      (LinearIsometryEquiv.measurePreserving R.symm) g) = _
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving g
      (LinearIsometryEquiv.measurePreserving R.symm)] with z hz
    rw [hz]
    rfl
  have hchange : (∫ z : Plane, f (R z) * g z) =
      ∫ z : Plane, f z * g (R.symm z) := by
    have h := (LinearIsometryEquiv.measurePreserving R).integral_comp'
      (f := R.toMeasurableEquiv) (fun z : Plane => f z * g (R.symm z))
    calc
      (∫ z : Plane, f (R z) * g z) =
          ∫ z : Plane, f (R.toMeasurableEquiv z) *
            g (R.symm (R.toMeasurableEquiv z)) := by
              apply integral_congr_ae
              filter_upwards [] with z
              simp
      _ = ∫ z : Plane, f z * g (R.symm z) := h
  exact hleft.trans (hchange.trans hright.symm)

/-- A weak `L²` limit of functions invariant under a linear isometry is invariant under that
isometry almost everywhere. -/
theorem weakLimitL2_invariant_of_invariant_seq
    (R : Plane ≃ₗᵢ[ℝ] Plane) (s : ℕ → ℕ)
    (v : Lp ℝ 2 (volume : Measure Plane)) (F : ℕ → Plane → ℝ)
    (hmem : ∀ n, MemLp (F n) 2 volume)
    (hweak : ∀ g : Lp ℝ 2 (volume : Measure Plane),
      Tendsto (fun n => inner ℝ ((hmem (s n)).toLp (F (s n))) g)
        atTop (𝓝 (inner ℝ v g)))
    (hinv : ∀ n z, F n (R z) = F n z) :
    (fun z : Plane => v (R z)) =ᵐ[volume] v := by
  let U : ℕ → Lp ℝ 2 (volume : Measure Plane) :=
    fun n => (hmem (s n)).toLp (F (s n))
  have hUAE (n : ℕ) : ∀ᵐ z : Plane ∂volume, U n z = F (s n) z := by
    dsimp [U]
    exact (hmem (s n)).coeFn_toLp
  have hUinv (n : ℕ) : pullbackL2 R (U n) = U n := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (U n)
        (LinearIsometryEquiv.measurePreserving R),
      (LinearIsometryEquiv.measurePreserving R).quasiMeasurePreserving.ae (hUAE n),
      hUAE n] with z hcomp hUmap hU
    calc
      pullbackL2 R (U n) z = U n (R z) := by simpa [pullbackL2] using hcomp
      _ = F (s n) (R z) := hUmap
      _ = F (s n) z := hinv (s n) z
      _ = U n z := hU.symm
  have hinnerInvariant (g : Lp ℝ 2 (volume : Measure Plane)) :
      inner ℝ v g = inner ℝ v (pullbackL2 R.symm g) := by
    have hlim₁ := hweak g
    have hlim₂ := hweak (pullbackL2 R.symm g)
    have hlim₁' : Tendsto (fun n => inner ℝ (U n) (pullbackL2 R.symm g)) atTop
        (𝓝 (inner ℝ v g)) := by
      apply hlim₁.congr'
      filter_upwards [] with n
      calc
        inner ℝ (U n) g = inner ℝ (pullbackL2 R (U n)) g := by rw [hUinv n]
        _ = inner ℝ (U n) (pullbackL2 R.symm g) := inner_pullbackL2 R (U n) g
    exact tendsto_nhds_unique hlim₁' hlim₂
  have hinnerEq (g : Lp ℝ 2 (volume : Measure Plane)) :
      inner ℝ (pullbackL2 R v) g = inner ℝ v g := by
    calc
      inner ℝ (pullbackL2 R v) g = inner ℝ v (pullbackL2 R.symm g) :=
        inner_pullbackL2 R v g
      _ = inner ℝ v g := (hinnerInvariant g).symm
  let d : Lp ℝ 2 (volume : Measure Plane) := pullbackL2 R v - v
  have hself : inner ℝ d d = 0 := by
    have hEq := hinnerEq d
    calc
      inner ℝ d d = inner ℝ (pullbackL2 R v - v) d := by rfl
      _ = inner ℝ (pullbackL2 R v) d - inner ℝ v d := by rw [inner_sub_left]
      _ = 0 := by rw [hEq]; ring
  have hnormsq : ‖d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hself
  have hd0 : d = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖d‖]
  have hpullbackEq : pullbackL2 R v = v := by
    have h := congrArg (fun x : Lp ℝ 2 (volume : Measure Plane) => x + v) hd0
    simpa [d] using h
  filter_upwards [Lp.coeFn_compMeasurePreserving v
      (LinearIsometryEquiv.measurePreserving R), Lp.ext_iff.mp hpullbackEq] with z hz heq
  exact hz.symm.trans heq

end Critical2DKPZ.CovarianceKernel

end
