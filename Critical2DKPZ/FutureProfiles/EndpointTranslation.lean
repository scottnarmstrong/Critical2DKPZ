/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.Basic
public import Critical2DKPZ.Polymer.Locality
public import Critical2DKPZ.Gaussian.DisorderLaws
import Mathlib.Tactic

/-! # Endpoint profiles and spatial translation -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Polymer


/-- The point-started endpoint law is the zero-time smoothed endpoint law. -/
theorem endpointDist_eq_smoothedEndpointDist_zero (β : ℝ) (n : ℕ) (x : Site)
    (ω : Disorder) :
    endpointDist β n x ω = smoothedEndpointDist β 0 n x ω := by
  have hnum (w : Site) :
      (∑' y, srwKernel 0 (y - x) * pointToPoint β 0 (n - 0) y w ω) =
        pointToPoint β 0 n x w ω := by
    rw [tsum_eq_single x]
    · simp
    · intro y hy
      have hne : y - x ≠ 0 := by
        intro h
        apply hy
        exact sub_eq_zero.mp h
      simp [hne]
  have hden : smoothedP2Plane β 0 n x ω = pointToPlane β 0 n x ω := by
    unfold smoothedP2Plane
    rw [tsum_eq_single x]
    · simp
    · intro y hy
      have hne : y - x ≠ 0 := by
        intro h
        apply hy
        exact sub_eq_zero.mp h
      simp [hne]
  funext w
  simp only [endpointDist, smoothedEndpointDist, Nat.sub_zero]
  rw [← hnum, ← hden]
  simp only [Nat.sub_zero]

/-- Spatial translation of the disorder preserves its product Gaussian law. -/
theorem measurePreserving_disorderShift (x : Site) :
    MeasurePreserving (fun (ω : Disorder) (p : ℕ × Site) => ω (p.1, p.2 + x))
      disorderLaw disorderLaw :=
  Gaussian.measurePreserving_disorder_translation x

/-- Translation acts measurably on every past sigma-field. -/
theorem measurable_disorderShift_past (n : ℕ) (x : Site) :
    Measurable[disorderPast n, disorderPast n]
      (fun (ω : Disorder) (p : ℕ × Site) => ω (p.1, p.2 + x)) := by
  let I := {p : ℕ × Site // 0 < p.1 ∧ p.1 ≤ n}
  let restrict : Disorder → (I → ℝ) := fun ω j => ω j
  let shiftIndex : I → I := fun j =>
    ⟨(j.1.1, j.1.2 + x), ⟨j.2.1, j.2.2⟩⟩
  let shiftCoordinates : (I → ℝ) → (I → ℝ) := fun f j => f (shiftIndex j)
  have hshift : Measurable shiftCoordinates := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (shiftIndex j)
  have hcomp : restrict ∘
      (fun ω : Disorder => fun p : ℕ × Site => ω (p.1, p.2 + x)) =
        shiftCoordinates ∘ restrict := by
    funext ω j
    rfl
  apply Measurable.of_comap_le
  change (MeasurableSpace.comap restrict inferInstance).comap
      (fun ω : Disorder => fun p : ℕ × Site => ω (p.1, p.2 + x)) ≤
    MeasurableSpace.comap restrict inferInstance
  rw [MeasurableSpace.comap_comp, hcomp]
  exact MeasurableSpace.comap_le_comap_of_eq_comp shiftCoordinates hshift rfl

/-- Reindexing a profile and its terminal observable commutes with spatial translation. -/
theorem profileP2Fun_translate (β : ℝ) (a b : ℕ) (x : Site) (ν f : Site → ℝ)
    (ω : Disorder) :
    profileP2Fun β a b (fun w => ν (w - x)) f ω =
      profileP2Fun β a b ν (fun z => f (z + x)) (fun p => ω (p.1, p.2 + x)) := by
  unfold profileP2Fun
  calc
    _ = ∑' w, ν ((w + x) - x) *
          (∑' z, pointToPoint β a (b - a) (w + x) z ω * f z) := by
      symm
      exact Equiv.tsum_eq (Equiv.addRight x)
        (fun w => ν (w - x) *
          (∑' z, pointToPoint β a (b - a) w z ω * f z))
    _ = ∑' w, ν w *
          (∑' z, pointToPoint β a (b - a) w z
            (fun p => ω (p.1, p.2 + x)) * f (z + x)) := by
      apply tsum_congr
      intro w
      have hinner :
          (∑' z, pointToPoint β a (b - a) (w + x) z ω * f z) =
            ∑' z, pointToPoint β a (b - a) w z
              (fun p => ω (p.1, p.2 + x)) * f (z + x) := by
        calc
          _ = ∑' z, pointToPoint β a (b - a) (w + x) (z + x) ω * f (z + x) :=
            (Equiv.addRight x).tsum_eq
              (fun z => pointToPoint β a (b - a) (w + x) z ω * f z) |>.symm
          _ = _ := by
            apply tsum_congr
            intro z
            rw [pointToPoint_translate]
      rw [hinner]
      congr 1
      simp

/-- The endpoint distribution translates together with the disorder. -/
theorem endpointDist_translate (β : ℝ) (n : ℕ) (x : Site) (ω : Disorder) (w : Site) :
    endpointDist β n x ω (w + x) =
      endpointDist β n 0 (fun p => ω (p.1, p.2 + x)) w := by
  unfold endpointDist
  rw [show pointToPoint β 0 n x (w + x) ω =
        pointToPoint β 0 n 0 w (fun p => ω (p.1, p.2 + x)) by
        simpa only [zero_add] using
          Polymer.pointToPoint_translate β 0 n 0 w x ω,
      show pointToPlane β 0 n x ω =
        pointToPlane β 0 n 0 (fun p => ω (p.1, p.2 + x)) by
        simpa only [zero_add] using Polymer.pointToPlane_translate β 0 n 0 x ω]

/-- The smoothed endpoint distribution translates together with the disorder. -/
theorem smoothedEndpointDist_translate (β : ℝ) (m n : ℕ) (x : Site)
    (ω : Disorder) (w : Site) :
    smoothedEndpointDist β m n x ω (w + x) =
      smoothedEndpointDist β m n 0 (fun p => ω (p.1, p.2 + x)) w := by
  have hnum :
      (∑' y, srwKernel m (y - x) * pointToPoint β m (n - m) y (w + x) ω) =
        ∑' y, srwKernel m y * pointToPoint β m (n - m) y w
          (fun p => ω (p.1, p.2 + x)) := by
    calc
      _ = ∑' y, srwKernel m ((y + x) - x) *
          pointToPoint β m (n - m) (y + x) (w + x) ω := by
        symm
        exact Equiv.tsum_eq (Equiv.addRight x)
          (fun y => srwKernel m (y - x) * pointToPoint β m (n - m) y (w + x) ω)
      _ = _ := by
        apply tsum_congr
        intro y
        rw [pointToPoint_translate]
        simp
  have hden : smoothedP2Plane β m n x ω =
      smoothedP2Plane β m n 0 (fun p => ω (p.1, p.2 + x)) := by
    unfold smoothedP2Plane
    calc
      _ = ∑' y, srwKernel m ((y + x) - x) *
          pointToPlane β m (n - m) (y + x) ω := by
        symm
        exact Equiv.tsum_eq (Equiv.addRight x)
          (fun y => srwKernel m (y - x) * pointToPlane β m (n - m) y ω)
      _ = _ := by
        apply tsum_congr
        intro y
        rw [pointToPlane_translate]
        simp
  unfold smoothedEndpointDist
  rw [hnum, hden]
  simp

/-- Translation of an endpoint profile through a later polymer segment. -/
theorem profileP2Fun_endpointDist_translate (β : ℝ) (n N : ℕ) (x : Site)
    (f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β n N (endpointDist β n x ω) f ω =
      profileP2Fun β n N (endpointDist β n 0
        (fun p => ω (p.1, p.2 + x))) (fun z => f (z + x))
        (fun p => ω (p.1, p.2 + x)) := by
  have hν : endpointDist β n x ω = fun w =>
      endpointDist β n 0 (fun p => ω (p.1, p.2 + x)) (w - x) := by
    funext w
    have h := endpointDist_translate β n x ω (w - x)
    simpa using h
  rw [hν]
  exact profileP2Fun_translate β n N x
    (endpointDist β n 0 (fun p => ω (p.1, p.2 + x))) f ω

/-- Translation of a smoothed endpoint profile through a later polymer segment. -/
theorem profileP2Fun_smoothedEndpointDist_translate (β : ℝ) (m n N : ℕ) (x : Site)
    (f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β n N (smoothedEndpointDist β m n x ω) f ω =
      profileP2Fun β n N (smoothedEndpointDist β m n 0
        (fun p => ω (p.1, p.2 + x))) (fun z => f (z + x))
        (fun p => ω (p.1, p.2 + x)) := by
  have hν : smoothedEndpointDist β m n x ω = fun w =>
      smoothedEndpointDist β m n 0 (fun p => ω (p.1, p.2 + x)) (w - x) := by
    funext w
    have h := smoothedEndpointDist_translate β m n x ω (w - x)
    simpa using h
  rw [hν]
  exact profileP2Fun_translate β n N x
    (smoothedEndpointDist β m n 0 (fun p => ω (p.1, p.2 + x))) f ω

end Critical2DKPZ.FutureProfiles

end
