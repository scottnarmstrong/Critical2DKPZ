/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ChapmanKolmogorov
public import Critical2DKPZ.Smoothing.Decomposition
public import Critical2DKPZ.Smoothing.WidthLogInverseMoment
import Mathlib.Tactic

/-! # Exact factorization for short changes of the smoothing clock -/

@[expose] public section

open Filter MeasureTheory

namespace Critical2DKPZ.Smoothing

/-- The logarithm of a smoothed polymer mass splits into the short initial log mass and the future log mass tested against its normalized endpoint law. -/
theorem log_profileP2Fun_srwKernel_shortClock_decomp (β : ℝ) {d k M : ℕ}
    (hdk : d ≤ k) (hkM : k ≤ M) (x : Site) (f : Site → ℝ)
    (hf : ∀ z, 0 < f z) (ω : Disorder) :
    Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) f ω) =
      Real.log (smoothedP2Plane β d k x ω) +
        Real.log (profileP2Fun β k M (smoothedEndpointDist β d k x ω) f ω) := by
  classical
  let ν : Site → ℝ := fun w => srwKernel d (w - x)
  let A : Finset Site := Polymer.endpoints x d
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem d x w (by simpa [A] using hw)
  have hν0 : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg d (w - x)
  have hνsum : ∑ w ∈ A, ν w = 1 := by
    exact Polymer.sum_srwKernel_endpoints d x
  have hνpos : ∃ w ∈ A, 0 < ν w := by
    have hsum : 0 < ∑ w ∈ A, ν w := by rw [hνsum]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hν0 w)).mp hsum
  have hηA : ∀ w ∉ (Polymer.endpoints x d).biUnion
      (fun y => Polymer.endpoints y (k - d)),
      smoothedEndpointDist β d k x ω w = 0 :=
    (smoothedEndpointDist_probability β hdk x ω).1
  have hη0 (w : Site) : 0 ≤ smoothedEndpointDist β d k x ω w :=
    (smoothedEndpointDist_probability β hdk x ω).2.1 w
  have hηsum : ∑ w ∈ (Polymer.endpoints x d).biUnion
      (fun y => Polymer.endpoints y (k - d)), smoothedEndpointDist β d k x ω w = 1 :=
    (smoothedEndpointDist_probability β hdk x ω).2.2
  have hηpos : ∃ w ∈ (Polymer.endpoints x d).biUnion
      (fun y => Polymer.endpoints y (k - d)),
      0 < smoothedEndpointDist β d k x ω w := by
    have hsum : 0 < ∑ w ∈ (Polymer.endpoints x d).biUnion
        (fun y => Polymer.endpoints y (k - d)), smoothedEndpointDist β d k x ω w := by
      rw [hηsum]
      norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hη0 w)).mp hsum
  have hηprofile : 0 < profileP2Fun β k M
      (smoothedEndpointDist β d k x ω) f ω :=
    profileP2Fun_pos_terminal β k M (smoothedEndpointDist β d k x ω) f
      ((Polymer.endpoints x d).biUnion (fun y => Polymer.endpoints y (k - d)))
      hηA hη0 hηpos hf ω
  have hshort : 0 < smoothedP2Plane β d k x ω :=
    Polymer.smoothedP2Plane_pos β d k x ω
  calc
    _ = Real.log (smoothedP2Plane β d k x ω *
        profileP2Fun β k M (smoothedEndpointDist β d k x ω) f ω) := by
          rw [profileP2Fun_srwKernel_eq_mul β hdk hkM x f ω]
    _ = _ := Real.log_mul hshort.ne' hηprofile.ne'

/-- The collision estimate for centered logarithms, with the initial walk-kernel variation
replaced by its uniform even-clock bound. The resulting right side no longer depends on the
spatial center `x`. -/
theorem eLpNorm_centered_log_walkKernel_profile_difference_le_collision_uniform_variation
    (A H F : ℝ) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ f : Site → ℝ,
        (∀ z, |f z| ≤ F) → (∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) →
        ∀ a T p q : ℕ, a + T ≤ M → ∀ x : Site,
        eLpNorm (fun ω =>
          (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
              (fun w => srwKernel (2 * q) (w - x)) f ω) -
            Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
              (fun w => srwKernel (2 * p) (w - x)) f ω)) -
            (∫ ω', (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω') -
              Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω'))
              ∂disorderLaw)) 2 disorderLaw ≤
          (ENNReal.ofReal logHolderConstant *
            ENNReal.ofReal (Real.sqrt (F ^ 2 *
              (2 * (((max p q - min p q : ℕ) : ℝ)) /
                Real.sqrt ((min p q : ℝ) + 1)) ^ 2 *
              ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
            (2 * (ENNReal.ofReal (Real.exp H * C * (1 + Real.log ((M : ℝ) + 1))) ^
              ((1 : ℝ) / 3))) +
          ENNReal.ofReal logHolderConstant *
            ENNReal.ofReal (Real.sqrt (
              (2 * (((max p q - min p q : ℕ) : ℝ)) /
                Real.sqrt ((min p q : ℝ) + 1)) ^ 2 *
              ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
            (2 * (ENNReal.ofReal (C * (1 + Real.log ((M : ℝ) + 1))) ^
              ((1 : ℝ) / 3)))) := by
  obtain ⟨C, hC, hraw⟩ :=
    eLpNorm_centered_log_walkKernel_profile_difference_le_collision_uniform
      A H F hH hF
  refine ⟨C, hC, ?_⟩
  filter_upwards [hraw] with M hM
  intro ϑ hϑ f hfb hf a T p q hTM x
  have hraw' := hM ϑ hϑ f hfb hf a T p q hTM x
  let S : ℝ := ∑ w ∈ (Polymer.endpoints x (2 * p) ∪
      Polymer.endpoints x (2 * q)),
      |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|
  let V : ℝ := 2 * (((max p q - min p q : ℕ) : ℝ)) /
      Real.sqrt ((min p q : ℝ) + 1)
  have hSV : S ≤ V := by
    rcases le_total p q with hpq | hqp
    · have h := walkKernel_initialVariation_le hpq x
      have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
      have hwidth : max p q - min p q = q - p := by
        simp [max_eq_right hpq, min_eq_left hpq]
      simpa [S, V, hwidth, Nat.cast_min, min_eq_left hpqR] using h
    · have h := walkKernel_initialVariation_le hqp x
      have hqpR : (q : ℝ) ≤ p := by exact_mod_cast hqp
      have hswap : S =
          ∑ w ∈ (Polymer.endpoints x (2 * q) ∪
            Polymer.endpoints x (2 * p)),
            |srwKernel (2 * p) (w - x) - srwKernel (2 * q) (w - x)| := by
        dsimp [S]
        apply Finset.sum_congr
        · exact Finset.union_comm _ _
        · intro w hw
          exact abs_sub_comm _ _
      have h' : S ≤ 2 * (((p - q : ℕ) : ℝ)) /
          Real.sqrt ((q : ℝ) + 1) := by
        rw [hswap]
        exact h
      have hwidth : max p q - min p q = p - q := by
        simp [max_eq_left hqp, min_eq_right hqp]
      simpa [V, hwidth, Nat.cast_min, min_eq_right hqpR] using h'
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hSsq : S ^ 2 ≤ V ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hSV) (add_nonneg hVnonneg hSnonneg)]
  have hlognonneg : 0 ≤ Real.log ((M : ℝ) + 1) := by
    apply Real.log_nonneg
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    linarith
  have hscale : 0 ≤ (C + 1) * (1 + Real.log ((M : ℝ) + 1)) := by
    positivity
  have hscaleF : 0 ≤ F ^ 2 * S ^ 2 *
      ((C + 1) * (1 + Real.log ((M : ℝ) + 1))) := by positivity
  have hscaleV : 0 ≤ F ^ 2 * V ^ 2 *
      ((C + 1) * (1 + Real.log ((M : ℝ) + 1))) := by positivity
  calc
    _ ≤ (ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (Real.sqrt (F ^ 2 * S ^ 2 *
            ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
          (2 * (ENNReal.ofReal (Real.exp H * C * (1 + Real.log ((M : ℝ) + 1))) ^
            ((1 : ℝ) / 3))) +
        ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (Real.sqrt (S ^ 2 *
            ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
          (2 * (ENNReal.ofReal (C * (1 + Real.log ((M : ℝ) + 1))) ^
            ((1 : ℝ) / 3)))) := hraw'
    _ ≤ _ := by
      apply add_le_add <;> gcongr

end Critical2DKPZ.Smoothing

end
