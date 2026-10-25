/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.TranslatedPairingDerivative

/-! Differentiating a compact smooth kernel gives the directional derivatives of its translated distribution pairing. -/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped ContDiff Distributions

namespace Critical2DKPZ.Analysis.Sobolev

/-- The derivative of a smooth compactly supported kernel in a fixed direction, as a test
function. -/
def directionalDerivativeKernel (ρ : TestFn) (v : Plane) : TestFn := {
  toFun := fun z => fderiv ℝ ρ z v
  contDiff' := (ρ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Plane => v))
  hasCompactSupport' := ρ.hasCompactSupport.fderiv_apply ℝ v
  tsupport_subset' := fun _ _ => trivial }


/-- Pairing against the derivative test family is the translated pairing with the differentiated
kernel. -/
theorem translatedDistributionPairingDirectionalDerivative_eq_kernel
    (T : Distr) (φ ρ : TestFn) (y v : Plane) :
    translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) =
      translatedDistributionPairing T φ (directionalDerivativeKernel ρ v) y := by
  rw [translatedDistributionPairing_apply]
  unfold translatedDistributionPairingDirectionalDerivative
  apply congrArg T
  apply TestFunction.ext
  intro x
  change φ x * fderiv ℝ ρ (y - x) v =
    φ x * directionalDerivativeKernel ρ v (y - x)
  rfl

/-- At a fixed direction, the distributional derivative pairing is continuously differentiable in
the translation point. -/
theorem contDiffOne_translatedDistributionPairingDirectionalDerivative
    (T : Distr) (φ ρ : TestFn) (v : Plane) :
    ContDiff ℝ 1
      (fun y => translatedDistributionPairingDirectionalDerivative T φ ρ (y, v)) := by
  have hfun : (fun y => translatedDistributionPairingDirectionalDerivative T φ ρ (y, v)) =
      translatedDistributionPairing T φ (directionalDerivativeKernel ρ v) := by
    funext y
    exact translatedDistributionPairingDirectionalDerivative_eq_kernel T φ ρ y v
  rw [hfun]
  exact contDiffOne_translatedDistributionPairing T φ (directionalDerivativeKernel ρ v)

/-- The derivative in the base point of a fixed-direction pairing is given by the translated
pairing derivative for the differentiated kernel. -/
theorem hasFDerivAt_translatedDistributionPairingDirectionalDerivative
    (T : Distr) (φ ρ : TestFn) (y v : Plane) :
    HasFDerivAt
      (fun z => translatedDistributionPairingDirectionalDerivative T φ ρ (z, v))
      (translatedDistributionPairingFDeriv T φ (directionalDerivativeKernel ρ v) y) y := by
  have hfun :
      (fun z => translatedDistributionPairingDirectionalDerivative T φ ρ (z, v)) =
        translatedDistributionPairing T φ (directionalDerivativeKernel ρ v) := by
    funext z
    exact translatedDistributionPairingDirectionalDerivative_eq_kernel T φ ρ z v
  rw [hfun]
  exact hasFDerivAt_translatedDistributionPairing T φ (directionalDerivativeKernel ρ v) y

/-- A continuous linear functional on the plane is the sum of its coordinate values times the coordinate projections. -/
theorem translatedDistributionPairingFDeriv_eq_basisSum
    (T : Distr) (φ ρ : TestFn) (y : Plane) :
    translatedDistributionPairingFDeriv T φ ρ y =
      ∑ i : Fin 2,
        translatedDistributionPairingDirectionalDerivative T φ ρ
          (y, EuclideanSpace.single i (1 : ℝ)) • EuclideanSpace.proj i := by
  let e (i : Fin 2) : Plane := EuclideanSpace.single i (1 : ℝ)
  let a (i : Fin 2) := translatedDistributionPairingDirectionalDerivative T φ ρ (y, e i)
  let P (i : Fin 2) : Plane →L[ℝ] ℝ := EuclideanSpace.proj i
  let A : Plane →L[ℝ] ℝ := ∑ i : Fin 2, a i • P i
  have hAe : A = translatedDistributionPairingFDeriv T φ ρ y := by
    ext v
    have hv : v = ∑ i : Fin 2, v i • e i := by
      simpa [e] using (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v |>.symm
    change (∑ i : Fin 2, a i * v i) =
      translatedDistributionPairingDirectionalDerivative T φ ρ (y, v)
    calc
      (∑ i : Fin 2, a i * v i) =
          ∑ i : Fin 2, translatedDistributionPairingFDeriv T φ ρ y (v i • e i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [a, e, translatedDistributionPairingFDeriv_apply]
            ring
      _ = translatedDistributionPairingFDeriv T φ ρ y (∑ i : Fin 2, v i • e i) := by
            rw [map_sum]
      _ = translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) := by
            rw [translatedDistributionPairingFDeriv_apply]
            conv_rhs => rw [hv]
  simpa [A, a, e, P] using hAe.symm

/-- The bundled first derivative varies continuously differentiably with its base point. -/
theorem contDiffOne_translatedDistributionPairingFDeriv
    (T : Distr) (φ ρ : TestFn) :
    ContDiff ℝ 1 (translatedDistributionPairingFDeriv T φ ρ) := by
  let e (i : Fin 2) : Plane := EuclideanSpace.single i (1 : ℝ)
  let a (i : Fin 2) (y : Plane) :=
    translatedDistributionPairingDirectionalDerivative T φ ρ (y, e i)
  let P (i : Fin 2) : Plane →L[ℝ] ℝ := EuclideanSpace.proj i
  have ha (i : Fin 2) : ContDiff ℝ 1 (a i) := by
    change ContDiff ℝ 1
      (fun y => translatedDistributionPairingDirectionalDerivative T φ ρ (y, e i))
    exact contDiffOne_translatedDistributionPairingDirectionalDerivative T φ ρ (e i)
  have hA : ContDiff ℝ 1 (fun y : Plane => ∑ i : Fin 2, a i y • P i) := by
    exact ContDiff.sum (s := Finset.univ) fun i _ => (ha i).smul_const (P i)
  have hfun : (fun y => translatedDistributionPairingFDeriv T φ ρ y) =
      fun y => ∑ i : Fin 2, a i y • P i := by
    funext y
    simpa [a, e, P] using translatedDistributionPairingFDeriv_eq_basisSum T φ ρ y
  change ContDiff ℝ 1
    (fun y => translatedDistributionPairingFDeriv T φ ρ y)
  rw [hfun]
  exact hA

/-- The translated pairing has every finite order of continuous differentiability. -/
theorem contDiffNat_translatedDistributionPairing (n : ℕ) :
    ∀ (T : Distr) (φ ρ : TestFn),
      ContDiff ℝ n (translatedDistributionPairing T φ ρ) := by
  induction n with
  | zero =>
      intro T φ ρ
      exact contDiff_zero.mpr (continuous_translatedDistributionPairing T φ ρ)
  | succ n ih =>
      intro T φ ρ
      rw [Nat.cast_add, Nat.cast_one]
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨translatedDistributionPairingFDeriv T φ ρ, ?_,
        fun y => hasFDerivAt_translatedDistributionPairing T φ ρ y⟩
      let e (i : Fin 2) : Plane := EuclideanSpace.single i (1 : ℝ)
      let a (i : Fin 2) (y : Plane) :=
        translatedDistributionPairingDirectionalDerivative T φ ρ (y, e i)
      let P (i : Fin 2) : Plane →L[ℝ] ℝ := EuclideanSpace.proj i
      have ha (i : Fin 2) : ContDiff ℝ n (a i) := by
        change ContDiff ℝ n
          (fun y => translatedDistributionPairingDirectionalDerivative T φ ρ (y, e i))
        have hkernel :
            (fun y => translatedDistributionPairingDirectionalDerivative T φ ρ (y, e i)) =
              translatedDistributionPairing T φ (directionalDerivativeKernel ρ (e i)) := by
          funext y
          exact translatedDistributionPairingDirectionalDerivative_eq_kernel T φ ρ y (e i)
        rw [hkernel]
        exact ih T φ (directionalDerivativeKernel ρ (e i))
      have hsum : ContDiff ℝ n
          (fun y : Plane => ∑ i : Fin 2, a i y • P i) :=
        ContDiff.sum (s := Finset.univ) fun i _ => (ha i).smul_const (P i)
      have hrepr :
          (fun y => translatedDistributionPairingFDeriv T φ ρ y) =
            fun y => ∑ i : Fin 2, a i y • P i := by
        funext y
        simpa [a, e, P] using translatedDistributionPairingFDeriv_eq_basisSum T φ ρ y
      change ContDiff ℝ n
        (fun y => translatedDistributionPairingFDeriv T φ ρ y)
      rw [hrepr]
      exact hsum

/-- The translated pairing is twice continuously differentiable, as a finite-order instance. -/
theorem contDiffTwo_translatedDistributionPairing (T : Distr) (φ ρ : TestFn) :
    ContDiff ℝ 2 (translatedDistributionPairing T φ ρ) :=
  contDiffNat_translatedDistributionPairing 2 T φ ρ

/-- Every translated pairing with a compact smooth kernel is smooth. -/
theorem contDiff_translatedDistributionPairing (T : Distr) (φ ρ : TestFn) :
    ContDiff ℝ ∞ (translatedDistributionPairing T φ ρ) := by
  rw [contDiff_infty]
  intro n
  exact contDiffNat_translatedDistributionPairing n T φ ρ

/-- The translated pairing with compact smooth data is itself a test function. -/
noncomputable def translatedDistributionPairingTestFn (T : Distr) (φ ρ : TestFn) : TestFn := {
  toFun := translatedDistributionPairing T φ ρ
  contDiff' := contDiff_translatedDistributionPairing T φ ρ
  hasCompactSupport' := hasCompactSupport_translatedDistributionPairing T φ ρ
  tsupport_subset' := fun _ _ => trivial }


end Critical2DKPZ.Analysis.Sobolev

end
