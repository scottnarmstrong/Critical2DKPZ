/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeCovarianceBounds
public import Critical2DKPZ.Collision.HeatStart
public import Critical2DKPZ.Collision.ConditionalFlat
public import Critical2DKPZ.JointConvergence.HeatStartLogTails
public import Critical2DKPZ.Smoothing.LocalErrorBounds
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
import Mathlib.Tactic

/-! # Covariance bounds for lattice heat starts -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

private theorem profile_heatStart_flat_terminal_eq (β : ℝ) (N a b m : ℕ)
    (hN : 0 < N) (hm : Even m) (hab : Even (b - a)) (x : Site)
    (hx : x ∈ evenLattice) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m (w - x))
        (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω =
      profileP2Fun β a b (fun w => srwKernel m (w - x)) (fun _ => 1) ω := by
  let A : Finset Site := Polymer.endpoints x m
  let ν : Site → ℝ := fun w => srwKernel m (w - x)
  let f : Site → ℝ := fun z => cellAverage N (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) z
  let g : Site → ℝ := fun _ => 1
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem m x w hw
  have hν0 : ∀ w, 0 ≤ ν w := fun w => by
    dsimp [ν]
    exact Polymer.kernel_nonneg m (w - x)
  have hterminal (w : Site) (hw : w ∈ A) (z : Site)
      (hz : z ∈ Polymer.endpoints w (b - a)) : f z = g z := by
    dsimp [f, g]
    simp only [Real.exp_zero]
    rw [cellAverage_const hN
      (JointConvergence.evenLattice_of_even_duration
        (JointConvergence.evenLattice_of_even_duration hx hm hw) hab hz) 1]
  apply le_antisymm
  · exact JointConvergence.profileP2Fun_le_of_reachable (β := β) a b ν f g A hνA hν0
      (fun w hw z hz => le_of_eq (hterminal w hw z hz)) ω
  · exact JointConvergence.profileP2Fun_le_of_reachable (β := β) a b ν g f A hνA hν0
      (fun w hw z hz => le_of_eq (hterminal w hw z hz).symm) ω

private theorem profile_heatStart_eq_smoothed_shift (β : ℝ) (N a b m : ℕ)
    (hN : 0 < N) (hma : m ≤ a) (hab : a ≤ b) (hm : Even m)
    (hba : Even (b - a)) (x : Site) (hx : x ∈ evenLattice) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m (w - x))
        (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω =
      smoothedP2Plane β m (m + (b - a)) x
        (Smoothing.shiftEnvironment (a - m) ω) := by
  have hda : a - m ≤ a := Nat.sub_le _ _
  have hdb : a - m ≤ b := (Nat.sub_le _ _).trans hab
  have hstart : a - (a - m) = m := Nat.sub_sub_self hma
  have hend : b - (a - m) = m + (b - a) := by omega
  calc
    _ = profileP2Fun β (a - (a - m)) (b - (a - m))
          (fun w => srwKernel m (w - x))
          (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y))
          (Smoothing.shiftEnvironment (a - m) ω) :=
        Smoothing.profileP2Fun_timeShift_sub β hda hdb _ _ _
    _ = profileP2Fun β m (m + (b - a))
          (fun w => srwKernel m (w - x)) (fun _ => 1)
          (Smoothing.shiftEnvironment (a - m) ω) := by
        rw [hstart, hend]
        exact profile_heatStart_flat_terminal_eq β N m (m + (b - a)) m hN hm
          (by simpa using hba) x hx _
    _ = smoothedP2Plane β m (m + (b - a)) x
          (Smoothing.shiftEnvironment (a - m) ω) := by
        exact Polymer.profileP2Fun_srw_flat β m (m + (b - a)) x _

private theorem covariance_log_profile_le_joint (β : ℝ)
    (a b c d : ℕ) (ν μ : Site → ℝ) (A B : Finset Site)
    (hνA : ∀ w ∉ A, ν w = 0) (hμB : ∀ w ∉ B, μ w = 0)
    (hν0 : ∀ w, 0 ≤ ν w) (hμ0 : ∀ w, 0 ≤ μ w)
    (hνpos : ∃ w ∈ A, 0 < ν w) (hμpos : ∃ w ∈ B, 0 < μ w) :
    covariance (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω))
      (fun ω => Real.log (profileP2Fun β c d μ (fun _ => 1) ω)) disorderLaw ≤
      Real.log (∫ ω, profileP2Fun β a b ν (fun _ => 1) ω *
        profileP2Fun β c d μ (fun _ => 1) ω ∂disorderLaw) +
      gaussianityDefect disorderLaw
        (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) +
      gaussianityDefect disorderLaw
        (fun ω => Real.log (profileP2Fun β c d μ (fun _ => 1) ω)) := by
  classical
  let Ix := {w : Site // w ∈ A}
  let Iy := {w : Site // w ∈ B}
  let wx : Ix → Site := fun z => z.1
  let wy : Iy → Site := fun z => z.1
  let cx : Ix × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a))
  let cy : Iy × (Fin (d - c) → Fin 4) → ℝ := fun p =>
    μ p.1.1 * ((4 : ℝ)⁻¹ ^ (d - c))
  have hcx : ∀ p, 0 ≤ cx p := by
    intro p
    exact mul_nonneg (hν0 p.1.1) (by positivity)
  have hcy : ∀ p, 0 ≤ cy p := by
    intro p
    exact mul_nonneg (hμ0 p.1.1) (by positivity)
  have hcxpos : ∃ p, 0 < cx p := by
    rcases hνpos with ⟨w, hw, hwpos⟩
    refine ⟨(⟨w, hw⟩, fun _ => 0), ?_⟩
    exact mul_pos hwpos (by positivity)
  have hcypos : ∃ p, 0 < cy p := by
    rcases hμpos with ⟨w, hw, hwpos⟩
    refine ⟨(⟨w, hw⟩, fun _ => 0), ?_⟩
    exact mul_pos hwpos (by positivity)
  have hX (ω : Disorder) : profileP2Fun β a b ν (fun _ => 1) ω =
      PolymerCalculus.finitePathMass β a (b - a) wx cx ω :=
    OnePoint.profileP2Fun_eq_finitePathMass β a b ν A hνA ω
  have hY (ω : Disorder) : profileP2Fun β c d μ (fun _ => 1) ω =
      PolymerCalculus.finitePathMass β c (d - c) wy cy ω :=
    OnePoint.profileP2Fun_eq_finitePathMass β c d μ B hμB ω
  let F : Disorder → ℝ := fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)
  let G : Disorder → ℝ := fun ω => Real.log (profileP2Fun β c d μ (fun _ => 1) ω)
  have hmemF : MemLp F 2 disorderLaw := by
    dsimp [F]
    rw [show (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) =
      fun ω => Real.log (PolymerCalculus.finitePathMass β a (b - a) wx cx ω) from
        funext fun ω => congrArg Real.log (hX ω)]
    exact PolymerCalculus.memLp_log_finitePathMass β a (b - a) wx hcx hcxpos 2
  have hmemG : MemLp G 2 disorderLaw := by
    dsimp [G]
    rw [show (fun ω => Real.log (profileP2Fun β c d μ (fun _ => 1) ω)) =
      fun ω => Real.log (PolymerCalculus.finitePathMass β c (d - c) wy cy ω) from
        funext fun ω => congrArg Real.log (hY ω)]
    exact PolymerCalculus.memLp_log_finitePathMass β c (d - c) wy hcy hcypos 2
  have hjoint := Smoothing.logMGFRatio_add_finitePathMass_convex
    β β a (b - a) c (d - c) wx wy hcx hcxpos hcy hcypos
  have hsumEq : F + G =
      (fun ω => Real.log (PolymerCalculus.finitePathMass β a (b - a) wx cx ω)) +
        (fun ω => Real.log (PolymerCalculus.finitePathMass β c (d - c) wy cy ω)) := by
    funext ω
    simp only [Pi.add_apply, F, G]
    rw [hX ω, hY ω]
  have hdom : integrableExpSet (F + G) disorderLaw = Set.univ := by
    simpa only [← hsumEq] using hjoint.1
  have hconv : ConvexOn ℝ (integrableExpSet (F + G) disorderLaw)
      (logMGFRatio disorderLaw (F + G)) := by
    simpa only [← hsumEq] using hjoint.2
  have h0 : 0 ∈ interior (integrableExpSet (F + G) disorderLaw) := by
    rw [hdom]
    simp
  have h1 : 1 ∈ integrableExpSet (F + G) disorderLaw := by
    rw [hdom]
    simp
  have hupper := PolymerCalculus.covariance_le_log_joint_moment_add_defects_of_convex
    hmemF hmemG hconv h0 h1
  have hmgf : mgf (F + G) disorderLaw 1 =
      ∫ ω, profileP2Fun β a b ν (fun _ => 1) ω *
        profileP2Fun β c d μ (fun _ => 1) ω ∂disorderLaw := by
    rw [mgf]
    apply integral_congr_ae
    filter_upwards [] with ω
    have hpX : 0 < profileP2Fun β a b ν (fun _ => 1) ω := by
      rw [hX ω]
      exact PolymerCalculus.finitePathMass_pos β a (b - a) wx hcx hcxpos ω
    have hpY : 0 < profileP2Fun β c d μ (fun _ => 1) ω := by
      rw [hY ω]
      exact PolymerCalculus.finitePathMass_pos β c (d - c) wy hcy hcypos ω
    change Real.exp (1 * ((F + G) ω)) = _
    rw [one_mul]
    change Real.exp (F ω + G ω) = _
    dsimp [F, G]
    rw [Real.exp_add, Real.exp_log hpX, Real.exp_log hpY]
  rw [hmgf] at hupper
  exact hupper

private theorem profileP2Fun_evolve_start (β : ℝ) (a c b : ℕ)
    (hac : a ≤ c) (hcb : c ≤ b) (ν : Site → ℝ) (A : Finset Site)
    (hνA : ∀ u ∉ A, ν u = 0) (ω : Disorder) :
    profileP2Fun β a b ν (fun _ => 1) ω =
      profileP2Fun β c b
        (fun z => ∑ u ∈ A, ν u * pointToPoint β a (c - a) u z ω)
        (fun _ => 1) ω := by
  classical
  let C : Finset Site := A.biUnion (fun u => Polymer.endpoints u (c - a))
  let η : Site → ℝ := fun z =>
    ∑ u ∈ A, ν u * pointToPoint β a (c - a) u z ω
  have hηC : ∀ z ∉ C, η z = 0 := by
    intro z hz
    simp only [η]
    apply Finset.sum_eq_zero
    intro u hu
    have hnot : z ∉ Polymer.endpoints u (c - a) := by
      intro hreach
      exact hz (Finset.mem_biUnion.mpr ⟨u, hu, hreach⟩)
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β a (c - a) u z ω hnot, mul_zero]
  have hsub (u : Site) (hu : u ∈ A) :
      Polymer.endpoints u (c - a) ⊆ C := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨u, hu, hz⟩
  have hCK (u : Site) (hu : u ∈ A) :
      pointToPlane β a (b - a) u ω =
        ∑ z ∈ C, pointToPoint β a (c - a) u z ω *
          pointToPlane β c (b - c) z ω := by
    have hsplit : (c - a) + (b - c) = b - a := by omega
    calc
      pointToPlane β a (b - a) u ω =
          ∑' z, pointToPoint β a (c - a) u z ω *
            pointToPlane β (a + (c - a)) (b - c) z ω := by
        rw [← hsplit, Polymer.pointToPlane_chapmanKolmogorov]
      _ = ∑ z ∈ Polymer.endpoints u (c - a),
          pointToPoint β a (c - a) u z ω * pointToPlane β c (b - c) z ω := by
        rw [show a + (c - a) = c by omega,
          Polymer.tsum_pointToPoint_mul_eq_sum]
      _ = ∑ z ∈ C, pointToPoint β a (c - a) u z ω *
          pointToPlane β c (b - c) z ω := by
        apply Finset.sum_subset (hsub u hu)
        intro z hzC hzNot
        rw [Polymer.pointToPoint_eq_zero_of_not_mem β a (c - a) u z ω hzNot, zero_mul]
  rw [Polymer.profileP2Fun_eq_sum β a b ν (fun _ => 1) A hνA ω,
    Polymer.profileP2Fun_eq_sum β c b η (fun _ => 1) C hηC ω]
  simp only [mul_one, Polymer.tsum_pointToPoint]
  dsimp [η]
  calc
    (∑ u ∈ A, ν u * pointToPlane β a (b - a) u ω) =
        ∑ u ∈ A, ∑ z ∈ C,
          ν u * pointToPoint β a (c - a) u z ω *
            pointToPlane β c (b - c) z ω := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hCK u hu]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = ∑ z ∈ C, ∑ u ∈ A,
          ν u * pointToPoint β a (c - a) u z ω *
            pointToPlane β c (b - c) z ω := Finset.sum_comm
    _ = ∑ z ∈ C,
          (∑ u ∈ A, ν u * pointToPoint β a (c - a) u z ω) *
            pointToPlane β c (b - c) z ω := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]

private theorem condExp_randomFlatProfileProduct (β : ℝ) (a b : ℕ)
    (A B : Finset Site) (η ζ : Disorder → Site → ℝ)
    (hsuppη : ∀ ω w, w ∉ A → η ω w = 0)
    (hsuppζ : ∀ ω w, w ∉ B → ζ ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hmeasζ : ∀ w, Measurable[disorderPast a] (ζ · w))
    (hXmeas : Measurable (fun ω =>
      Collision.randomFlatProfilePolymer β a b η ω *
        Collision.randomFlatProfilePolymer β a b ζ ω))
    (hXint : Integrable (fun ω =>
      Collision.randomFlatProfilePolymer β a b η ω *
        Collision.randomFlatProfilePolymer β a b ζ ω) disorderLaw) :
    disorderLaw[(fun ω => Collision.randomFlatProfilePolymer β a b η ω *
      Collision.randomFlatProfilePolymer β a b ζ ω) | disorderPast a] =ᵐ[disorderLaw]
      fun ω => ∑ w ∈ A, ∑ v ∈ B,
        η ω w * ζ ω v * Polymer.pairMoment β (b - a) w v := by
  have hce := Gaussian.condExp_disorderBlock_ae_eq 0 a hXmeas hXint
  rw [Gaussian.disorderBlock_zero] at hce
  filter_upwards [hce] with ω hω
  rw [hω]
  have hevalη (ξ : Disorder) :
      Collision.randomFlatProfilePolymer β a b η
          (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
        ∑ w ∈ A, η ω w * pointToPlane β a (b - a) w ξ :=
    Collision.profileP2Fun_resamplePast β a b A η hsuppη hmeasη ω ξ
  have hevalζ (ξ : Disorder) :
      Collision.randomFlatProfilePolymer β a b ζ
          (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
        ∑ v ∈ B, ζ ω v * pointToPlane β a (b - a) v ξ :=
    Collision.profileP2Fun_resamplePast β a b B ζ hsuppζ hmeasζ ω ξ
  simp_rw [hevalη, hevalζ]
  have hfun (ξ : Disorder) :
      (∑ w ∈ A, η ω w * pointToPlane β a (b - a) w ξ) *
        (∑ v ∈ B, ζ ω v * pointToPlane β a (b - a) v ξ) =
      ∑ w ∈ A, ∑ v ∈ B, (η ω w * ζ ω v) *
        (pointToPlane β a (b - a) w ξ * pointToPlane β a (b - a) v ξ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
  rw [integral_finsetSum _ fun w _ =>
    integrable_finsetSum _ fun v _ =>
      (Polymer.integrable_pairProduct β a (b - a) w v).const_mul _]
  apply Finset.sum_congr rfl
  intro w hw
  rw [integral_finsetSum _ fun v _ =>
    (Polymer.integrable_pairProduct β a (b - a) w v).const_mul _]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul, Polymer.integral_pairMoment]

private theorem integral_randomFlatProfileProduct (β : ℝ) (a b : ℕ)
    (A B : Finset Site) (η : Disorder → Site → ℝ) (μ : Site → ℝ)
    (hsuppη : ∀ ω w, w ∉ A → η ω w = 0)
    (hsuppμ : ∀ v ∉ B, μ v = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hηint : ∀ w, Integrable (η · w) disorderLaw)
    (hXmeas : Measurable (fun ω =>
      Collision.randomFlatProfilePolymer β a b η ω *
        profileP2Fun β a b μ (fun _ => 1) ω))
    (hXint : Integrable (fun ω =>
      Collision.randomFlatProfilePolymer β a b η ω *
        profileP2Fun β a b μ (fun _ => 1) ω) disorderLaw) :
    (∫ ω, Collision.randomFlatProfilePolymer β a b η ω *
      profileP2Fun β a b μ (fun _ => 1) ω ∂disorderLaw) =
      ∑ w ∈ A, ∑ v ∈ B, (∫ ω, η ω w ∂disorderLaw) * μ v *
        Polymer.pairMoment β (b - a) w v := by
  have hmeasμ : ∀ v, Measurable[disorderPast a] (fun _ : Disorder => μ v) :=
    fun _ => measurable_const
  have hce := condExp_randomFlatProfileProduct β a b A B η
    (fun _ w => μ w) hsuppη (fun _ w hw => hsuppμ w hw)
    hmeasη hmeasμ hXmeas hXint
  have hpastle : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero a]
    exact Gaussian.disorderBlock_le 0 a
  calc
    _ = ∫ ω, disorderLaw[(fun ω =>
          Collision.randomFlatProfilePolymer β a b η ω *
            profileP2Fun β a b μ (fun _ => 1) ω) | disorderPast a] ω
          ∂disorderLaw := by
      symm
      exact integral_condExp hpastle
    _ = ∫ ω, ∑ w ∈ A, ∑ v ∈ B,
          η ω w * μ v * Polymer.pairMoment β (b - a) w v ∂disorderLaw :=
      integral_congr_ae hce
    _ = ∑ w ∈ A, ∑ v ∈ B,
          (∫ ω, η ω w ∂disorderLaw) * μ v *
            Polymer.pairMoment β (b - a) w v := by
      have htermInt (w v : Site) : Integrable
          (fun ω => η ω w * (μ v * Polymer.pairMoment β (b - a) w v)) disorderLaw :=
        (hηint w).mul_const _
      have hterm (w v : Site) :
          (∫ ω, η ω w * μ v * Polymer.pairMoment β (b - a) w v ∂disorderLaw) =
            (∫ ω, η ω w ∂disorderLaw) * μ v *
              Polymer.pairMoment β (b - a) w v := by
        have heq : (fun ω => η ω w * μ v * Polymer.pairMoment β (b - a) w v) =
            fun ω => η ω w * (μ v * Polymer.pairMoment β (b - a) w v) := by
          funext ω
          ring
        rw [heq, integral_mul_const]
        ring
      rw [integral_finsetSum _ fun w _ =>
        integrable_finsetSum _ fun v _ => by simpa only [mul_assoc] using htermInt w v]
      apply Finset.sum_congr rfl
      intro w hw
      rw [integral_finsetSum _ fun v _ => by
        simpa only [mul_assoc] using htermInt w v]
      apply Finset.sum_congr rfl
      intro v hv
      exact hterm w v

private theorem heatStart_product_mixedTimes (β : ℝ) (a c b m l : ℕ)
    (hac : a ≤ c) (hcb : c ≤ b) (x y : Site) :
    (∫ ω, profileP2Fun β a b (fun u => srwKernel m (u - x)) (fun _ => 1) ω *
      profileP2Fun β c b (fun v => srwKernel l (v - y)) (fun _ => 1) ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 (b - c),
        srwKernel (m + (c - a) + l + 2 * r) (y - x) * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (b - c - r) 0 ω ^ 2 ∂disorderLaw) := by
  classical
  let A := Polymer.endpoints x m
  let B := Polymer.endpoints y l
  let C := A.biUnion (fun u => Polymer.endpoints u (c - a))
  let ν : Site → ℝ := fun u => srwKernel m (u - x)
  let μ : Site → ℝ := fun v => srwKernel l (v - y)
  let η : Disorder → Site → ℝ := fun ω z =>
    ∑ u ∈ A, ν u * pointToPoint β a (c - a) u z ω
  have hνA : ∀ u ∉ A, ν u = 0 := by
    intro u hu
    exact Polymer.srwKernel_eq_zero_of_not_mem m x u hu
  have hμB : ∀ v ∉ B, μ v = 0 := by
    intro v hv
    exact Polymer.srwKernel_eq_zero_of_not_mem l y v hv
  have hν0 : ∀ u, 0 ≤ ν u := fun u => Polymer.kernel_nonneg m (u - x)
  have hμ0 : ∀ v, 0 ≤ μ v := fun v => Polymer.kernel_nonneg l (v - y)
  have hsumν : ∑ u ∈ A, ν u = 1 := by
    dsimp [ν, A]
    exact Polymer.sum_srwKernel_endpoints m x
  have hsumμ : ∑ v ∈ B, μ v = 1 := by
    dsimp [μ, B]
    exact Polymer.sum_srwKernel_endpoints l y
  have hηC : ∀ ω z, z ∉ C → η ω z = 0 := by
    intro ω z hz
    simp only [η]
    apply Finset.sum_eq_zero
    intro u hu
    have hnot : z ∉ Polymer.endpoints u (c - a) := by
      intro hreach
      exact hz (Finset.mem_biUnion.mpr ⟨u, hu, hreach⟩)
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β a (c - a) u z ω hnot, mul_zero]
  have hηmeas : ∀ z, Measurable[disorderPast c] (η · z) := by
    intro z
    dsimp [η]
    have hblock : Gaussian.disorderBlock a c ≤ disorderPast c := by
      rw [← Gaussian.disorderBlock_zero c]
      exact Gaussian.disorderBlock_mono (Nat.zero_le a) le_rfl
    apply Finset.measurable_sum
    intro u hu
    exact measurable_const.mul
      ((Polymer.measurable_pointToPoint_block β a (c - a) u z).mono
        (by rw [show a + (c - a) = c by omega]; exact hblock) le_rfl)
  have hηint : ∀ z, Integrable (η · z) disorderLaw := by
    intro z
    dsimp [η]
    apply integrable_finsetSum
    intro u hu
    exact (Polymer.integrable_pointToPoint β a (c - a) u z).const_mul _
  have hηavg (z : Site) :
      (∫ ω, η ω z ∂disorderLaw) = srwKernel (m + (c - a)) (z - x) := by
    have hsum : (∫ ω, η ω z ∂disorderLaw) =
        ∑ u ∈ A, ν u * srwKernel (c - a) (z - u) := by
      dsimp [η]
      rw [integral_finsetSum _ fun u _ =>
        (Polymer.integrable_pointToPoint β a (c - a) u z).const_mul _]
      simp_rw [integral_const_mul, Polymer.integral_pointToPoint]
    rw [hsum]
    dsimp [ν, A]
    exact Polymer.kernel_convolution_finset m (c - a) x z
  have hν'C : ∀ z ∉ C, srwKernel (m + (c - a)) (z - x) = 0 := by
    intro z hz
    rw [← hηavg z]
    have hsum : (∫ ω, η ω z ∂disorderLaw) =
        ∑ u ∈ A, ν u * srwKernel (c - a) (z - u) := by
      dsimp [η]
      rw [integral_finsetSum _ fun u _ =>
        (Polymer.integrable_pointToPoint β a (c - a) u z).const_mul _]
      simp_rw [integral_const_mul, Polymer.integral_pointToPoint]
    rw [hsum]
    apply Finset.sum_eq_zero
    intro u hu
    have hnot : z ∉ Polymer.endpoints u (c - a) := by
      intro hreach
      exact hz (Finset.mem_biUnion.mpr ⟨u, hu, hreach⟩)
    rw [Polymer.srwKernel_eq_zero_of_not_mem (c - a) u z hnot, mul_zero]
  have hXmem : MemLp
      (fun ω => profileP2Fun β a b ν (fun _ => 1) ω) 2 disorderLaw :=
    Polymer.memLp_profileP2Fun_finset β a b ν (fun _ => 1) A hνA 2 (by norm_num)
  have hYmem : MemLp
      (fun ω => profileP2Fun β c b μ (fun _ => 1) ω) 2 disorderLaw :=
    Polymer.memLp_profileP2Fun_finset β c b μ (fun _ => 1) B hμB 2 (by norm_num)
  have hprodEq : (fun ω => Collision.randomFlatProfilePolymer β c b η ω *
      profileP2Fun β c b μ (fun _ => 1) ω) =
      fun ω => profileP2Fun β a b ν (fun _ => 1) ω *
        profileP2Fun β c b μ (fun _ => 1) ω := by
    funext ω
    rw [Collision.randomFlatProfilePolymer]
    change profileP2Fun β c b
        (fun z => ∑ u ∈ A, ν u * pointToPoint β a (c - a) u z ω)
        (fun _ => 1) ω * _ = _
    exact congrArg (fun q => q * profileP2Fun β c b μ (fun _ => 1) ω)
      (profileP2Fun_evolve_start β a c b hac hcb ν A hνA ω).symm
  have hprodMeas : Measurable (fun ω =>
      Collision.randomFlatProfilePolymer β c b η ω *
        profileP2Fun β c b μ (fun _ => 1) ω) := by
    rw [hprodEq]
    exact (Polymer.measurable_profileP2Fun β a b ν (fun _ => 1)).mul
      (Polymer.measurable_profileP2Fun β c b μ (fun _ => 1))
  have hprodInt : Integrable (fun ω =>
      Collision.randomFlatProfilePolymer β c b η ω *
        profileP2Fun β c b μ (fun _ => 1) ω) disorderLaw := by
    rw [hprodEq]
    exact hXmem.integrable_mul hYmem
  have hproduct := integral_randomFlatProfileProduct β c b C B η μ
    hηC hμB hηmeas hηint hprodMeas hprodInt
  have hcommon :
      (∫ ω, profileP2Fun β a b ν (fun _ => 1) ω *
        profileP2Fun β c b μ (fun _ => 1) ω ∂disorderLaw) =
      ∫ ω, profileP2Fun β c b
        (fun z => srwKernel (m + (c - a)) (z - x)) (fun _ => 1) ω *
        profileP2Fun β c b μ (fun _ => 1) ω ∂disorderLaw := by
    calc
      _ = ∫ ω, Collision.randomFlatProfilePolymer β c b η ω *
          profileP2Fun β c b μ (fun _ => 1) ω ∂disorderLaw := by
        congr 1
        funext ω
        exact (congrFun hprodEq ω).symm
      _ = ∑ z ∈ C, ∑ v ∈ B,
          (∫ ω, η ω z ∂disorderLaw) * μ v * Polymer.pairMoment β (b - c) z v :=
        hproduct
      _ = ∑ z ∈ C, ∑ v ∈ B,
          srwKernel (m + (c - a)) (z - x) * μ v *
            Polymer.pairMoment β (b - c) z v := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro v hv
        rw [hηavg z]
      _ = ∫ ω, profileP2Fun β c b
          (fun z => srwKernel (m + (c - a)) (z - x)) (fun _ => 1) ω *
          profileP2Fun β c b μ (fun _ => 1) ω ∂disorderLaw := by
        simpa only [Nat.add_sub_cancel' hcb] using
          (Polymer.integral_profile_product_finset β c (b - c)
            (fun z => srwKernel (m + (c - a)) (z - x)) μ C B hν'C hμB).symm
  have hmix := Collision.heatStart_mixed_firstCollision β c (b - c)
    (m + (c - a)) l x y
  rw [hcommon]
  simpa only [Nat.add_sub_cancel' hcb] using hmix

private theorem covariance_log_profile_nonneg (β γ : ℝ)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (a b c d : ℕ)
    (ν μ : Site → ℝ) (A B : Finset Site)
    (hνA : ∀ w ∉ A, ν w = 0) (hμB : ∀ w ∉ B, μ w = 0)
    (hν0 : ∀ w, 0 ≤ ν w) (hμ0 : ∀ w, 0 ≤ μ w)
    (hνpos : ∃ w ∈ A, 0 < ν w) (hμpos : ∃ w ∈ B, 0 < μ w) :
    0 ≤ covariance (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω))
      (fun ω => Real.log (profileP2Fun γ c d μ (fun _ => 1) ω)) disorderLaw := by
  classical
  let Ix := {w : Site // w ∈ A}
  let Iy := {w : Site // w ∈ B}
  let wx : Ix → Site := fun z => z.1
  let wy : Iy → Site := fun z => z.1
  let cx : Ix × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a))
  let cy : Iy × (Fin (d - c) → Fin 4) → ℝ := fun p =>
    μ p.1.1 * ((4 : ℝ)⁻¹ ^ (d - c))
  have hcx : ∀ p, 0 ≤ cx p := fun p => mul_nonneg (hν0 p.1.1) (by positivity)
  have hcy : ∀ p, 0 ≤ cy p := fun p => mul_nonneg (hμ0 p.1.1) (by positivity)
  have hcxpos : ∃ p, 0 < cx p := by
    rcases hνpos with ⟨w, hw, hwpos⟩
    refine ⟨(⟨w, hw⟩, fun _ => 0), ?_⟩
    exact mul_pos hwpos (by positivity)
  have hcypos : ∃ p, 0 < cy p := by
    rcases hμpos with ⟨w, hw, hwpos⟩
    refine ⟨(⟨w, hw⟩, fun _ => 0), ?_⟩
    exact mul_pos hwpos (by positivity)
  have hX (ω : Disorder) : profileP2Fun β a b ν (fun _ => 1) ω =
      PolymerCalculus.finitePathMass β a (b - a) wx cx ω :=
    OnePoint.profileP2Fun_eq_finitePathMass β a b ν A hνA ω
  have hY (ω : Disorder) : profileP2Fun γ c d μ (fun _ => 1) ω =
      PolymerCalculus.finitePathMass γ c (d - c) wy cy ω :=
    OnePoint.profileP2Fun_eq_finitePathMass γ c d μ B hμB ω
  have hXfun : (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) =
      fun ω => Real.log (PolymerCalculus.finitePathMass β a (b - a) wx cx ω) :=
    funext fun ω => congrArg Real.log (hX ω)
  have hYfun : (fun ω => Real.log (profileP2Fun γ c d μ (fun _ => 1) ω)) =
      fun ω => Real.log (PolymerCalculus.finitePathMass γ c (d - c) wy cy ω) :=
    funext fun ω => congrArg Real.log (hY ω)
  rw [hXfun, hYfun]
  exact PolymerCalculus.covariance_log_finitePathMass_nonneg hβ hγ
    a (b - a) c (d - c) wx wy hcx hcxpos hcy hcypos

private theorem heatStart_product_mixedTimes_symm (β : ℝ)
    (a a' b m l : ℕ) (hab : a ≤ b) (ha'b : a' ≤ b) (x y : Site) :
    (∫ ω, profileP2Fun β a b (fun u => srwKernel m (u - x)) (fun _ => 1) ω *
      profileP2Fun β a' b (fun v => srwKernel l (v - y)) (fun _ => 1) ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 (b - max a a'),
        srwKernel (m + l + (max a a' - min a a') + 2 * r) (y - x) *
          Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (b - max a a' - r) 0 ω ^ 2 ∂disorderLaw) := by
  by_cases haa' : a ≤ a'
  · have h := heatStart_product_mixedTimes β a a' b m l haa' ha'b x y
    simpa only [max_eq_right haa', min_eq_left haa', Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using h
  · have ha'a : a' ≤ a := le_of_not_ge haa'
    have hcomm : (∫ ω, profileP2Fun β a b
        (fun u => srwKernel m (u - x)) (fun _ => 1) ω *
        profileP2Fun β a' b (fun v => srwKernel l (v - y)) (fun _ => 1) ω
        ∂disorderLaw) =
      ∫ ω, profileP2Fun β a' b
        (fun v => srwKernel l (v - y)) (fun _ => 1) ω *
        profileP2Fun β a b (fun u => srwKernel m (u - x)) (fun _ => 1) ω
        ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    rw [hcomm]
    have h := heatStart_product_mixedTimes β a' a b l m ha'a hab y x
    simpa only [max_eq_left ha'a, min_eq_right ha'a,
      Polymer.srwKernel_sub_swap, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

private theorem heatStart_collision_sum_le_green (ϑ : ℝ) (N : ℕ)
    (T₁ S β : ℝ) (hS : 0 ≤ S)
    (hspec : Real.exp (β ^ 2) - 1 = criticalSigmaSq ϑ N)
    (hSigma : ∀ L : ℕ, (L : ℝ) ≤ T₁ * N →
      criticalSigmaSq ϑ N *
        (∫ ω, pointToPlane β 0 L 0 ω ^ 2 ∂disorderLaw) ≤ S)
    (a a' b m l k : ℕ) (ha : a ≤ b) (ha' : a' ≤ b)
    (hk : m + l + (max a a' - min a a') = 2 * k)
    (hH₁ : ((m + (b - a) : ℕ) : ℝ) ≤ T₁ * N)
    (hH₂ : ((l + (b - a' : ℕ) : ℕ) : ℝ) ≤ T₁ * N)
    (z : Site) :
    (∑ r ∈ Finset.Icc 1 (b - max a a'),
      srwKernel (m + l + (max a a' - min a a') + 2 * r) z *
        Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (b - max a a' - r) 0 ω ^ 2 ∂disorderLaw)) ≤
      S * MomentBounds.truncatedGreen (k + (b - max a a')) z := by
  classical
  let n := b - max a a'
  let H := k + n
  have hmaxmin : max a a' + min a a' = a + a' := by omega
  have htwoH : 2 * H = (m + (b - a)) + (l + (b - a')) := by
    dsimp [H, n]
    omega
  have hH₁le : m + (b - a) ≤ max (m + (b - a)) (l + (b - a')) := Nat.le_max_left _ _
  have hH₂le : l + (b - a') ≤ max (m + (b - a)) (l + (b - a')) := Nat.le_max_right _ _
  have hHnat : H ≤ max (m + (b - a)) (l + (b - a')) := by omega
  have hHmax : ((max (m + (b - a)) (l + (b - a')) : ℕ) : ℝ) ≤ T₁ * N := by
    rw [Nat.cast_max]
    exact max_le_iff.mpr ⟨hH₁, hH₂⟩
  have hHreal : (H : ℝ) ≤ T₁ * N := by
    exact (Nat.cast_le.mpr hHnat).trans hHmax
  have hkr : ∀ r, m + l + (max a a' - min a a') + 2 * r = 2 * (k + r) := by
    intro r
    omega
  have hcoeff : ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) ≤ S := by
    intro r hr
    have hLnat : n - r ≤ H := by dsimp [H, n]; omega
    have hLreal : ((n - r : ℕ) : ℝ) ≤ T₁ * N :=
      (Nat.cast_le.mpr hLnat).trans hHreal
    simpa [Polymer.sigmaSq, hspec] using hSigma (n - r) hLreal
  have hshift := Polymer.sum_Icc_shift k n
    (fun q => srwKernel (2 * q) z)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 n, srwKernel (2 * (k + r)) z * S := by
      apply Finset.sum_le_sum
      intro r hr
      rw [hkr r]
      have hkern : 0 ≤ srwKernel (2 * (k + r)) z :=
        Polymer.kernel_nonneg _ _
      calc
        srwKernel (2 * (k + r)) z * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) =
          srwKernel (2 * (k + r)) z *
            (Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw)) := by ring
        _ ≤ srwKernel (2 * (k + r)) z * S :=
          mul_le_mul_of_nonneg_left (hcoeff r hr) hkern
    _ = S * ∑ r ∈ Finset.Icc 1 n, srwKernel (2 * (k + r)) z := by
      rw [← Finset.sum_mul]
      ring
    _ = S * ∑ q ∈ Finset.Icc (k + 1) H, srwKernel (2 * q) z := by
      rw [hshift]
    _ ≤ S * ∑ q ∈ Finset.Icc 1 H, srwKernel (2 * q) z := by
      apply mul_le_mul_of_nonneg_left _ hS
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have hq' : k + 1 ≤ q ∧ q ≤ H := Finset.mem_Icc.mp hq
        exact Finset.mem_Icc.mpr ⟨by omega, hq'.2⟩
      · intro q hq _
        exact Polymer.kernel_nonneg (2 * q) z
    _ = S * MomentBounds.truncatedGreen H z := by
      simp [MomentBounds.truncatedGreen]

private theorem heatStart_horizon_bounds {N : ℕ} (hN4 : 4 ≤ N)
    {t₀ t₁ T t δ : ℝ} (ht₀ : 0 < t₀) (ht : t ∈ Set.Icc t₀ t₁)
    (hT : t ≤ T) (hδ : 0 < δ) (hδt : δ < t / 2)
    (hN₀ : 4 / t₀ ≤ (N : ℝ)) :
    (t₀ / 2) * N ≤
        ((evenCeil ((N : ℝ) * δ) +
          (evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * (T - t + δ))) : ℕ) : ℝ) ∧
      ((evenCeil ((N : ℝ) * δ) +
          (evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * (T - t + δ))) : ℕ) : ℝ) ≤
        max (t₀ / 2 + 1) (t₁ + 1) * N := by
  let a := evenCeil ((N : ℝ) * (T - t + δ))
  let b := evenCeil ((N : ℝ) * T)
  let m := evenCeil ((N : ℝ) * δ)
  have hδle : δ ≤ T - t + δ := by linarith [hT]
  have hArgA0 : 0 ≤ (N : ℝ) * (T - t + δ) := by
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have htd : 0 ≤ T - t := sub_nonneg.mpr hT
    exact mul_nonneg hNnonneg (by linarith)
  have hArgB0 : 0 ≤ (N : ℝ) * T := by
    apply mul_nonneg (Nat.cast_nonneg N)
    linarith [hT, ht.1]
  have hArgM0 : 0 ≤ (N : ℝ) * δ := mul_nonneg (Nat.cast_nonneg N) hδ.le
  have hA : (N : ℝ) * (T - t + δ) ≤ (a : ℝ) := by
    dsimp [a]
    exact le_evenCeil _
  have hB : (N : ℝ) * T ≤ (b : ℝ) := by
    dsimp [b]
    exact le_evenCeil _
  have hM : (N : ℝ) * δ ≤ (m : ℝ) := by
    dsimp [m]
    exact le_evenCeil _
  have hAupp : (a : ℝ) < (N : ℝ) * (T - t + δ) + 2 := by
    dsimp [a]
    exact evenCeil_lt_add_two hArgA0
  have hBupp : (b : ℝ) < (N : ℝ) * T + 2 := by
    dsimp [b]
    exact evenCeil_lt_add_two hArgB0
  have hMupp : (m : ℝ) < (N : ℝ) * δ + 2 := by
    dsimp [m]
    exact evenCeil_lt_add_two hArgM0
  have hab : a ≤ b := by
    dsimp [a, b]
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left (by linarith [hδt]) (Nat.cast_nonneg N)
  have hHcast : ((m + (b - a) : ℕ) : ℝ) = (m : ℝ) + (b : ℝ) - (a : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hab]
    ring
  have hHlower : (N : ℝ) * t - 2 <
      ((m + (b - a) : ℕ) : ℝ) := by
    rw [hHcast]
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith [hM, hB, hAupp]
  have hHupper : ((m + (b - a) : ℕ) : ℝ) < (N : ℝ) * t + 4 := by
    rw [hHcast]
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith [hMupp, hBupp, hA]
  constructor
  · have htN : (N : ℝ) * t₀ ≤ (N : ℝ) * t :=
      mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg N)
    have hN0' : 2 ≤ (N : ℝ) * (t₀ / 2) := by
      have hNt₀ : 4 ≤ (N : ℝ) * t₀ := (div_le_iff₀ ht₀).mp hN₀
      nlinarith
    nlinarith
  · have htN : (N : ℝ) * t ≤ (N : ℝ) * t₁ :=
      mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg N)
    have hfour : 4 ≤ (N : ℝ) := by exact_mod_cast hN4
    have hT₁ : t₁ + 1 ≤ max (t₀ / 2 + 1) (t₁ + 1) := le_max_right _ _
    nlinarith

private theorem gaussianityDefect_shiftEnvironment (d : ℕ) (F : Disorder → ℝ)
    (hFmeas : Measurable F) :
    gaussianityDefect disorderLaw (fun ω => F (Smoothing.shiftEnvironment d ω)) =
      gaussianityDefect disorderLaw F := by
  unfold gaussianityDefect
  rw [Smoothing.integral_shiftEnvironment d hFmeas]
  rw [(Smoothing.measurePreserving_shiftEnvironment d).variance_fun_comp
    hFmeas.aemeasurable]

/-- Heat-start lattice log masses have a uniform logarithmic spatial covariance bound.
The logarithms are in `L²` by `Smoothing.memLp_log_profileP2Fun_of_bounded_terminal`;
the covariance estimate itself uses the defect bound and the mixed-time collision identity. -/
theorem heatStart_lattice_covariance_le_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ T t : ℝ, t ∈ Set.Icc t₀ t₁ → t ≤ T →
      ∀ δ δ' : ℝ, 0 < δ → δ < t / 2 → 0 < δ' → δ' < t / 2 →
        ∀ x y : Plane, x ≠ y →
          0 ≤ covariance
            (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (N * (T - t + δ))) (evenCeil (N * T))
              (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
              (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω))
            (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (N * (T - t + δ'))) (evenCeil (N * T))
              (fun w => srwKernel (evenCeil (N * δ')) (w - latticePoint N y))
              (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)) disorderLaw ∧
          covariance
            (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (N * (T - t + δ))) (evenCeil (N * T))
              (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
              (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω))
            (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (N * (T - t + δ'))) (evenCeil (N * T))
              (fun w => srwKernel (evenCeil (N * δ')) (w - latticePoint N y))
              (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)) disorderLaw ≤
            C * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) := by
  let Aθ := |ϑ| + 1
  let T₀ := t₀ / 2
  let T₁ := max (t₀ / 2 + 1) (t₁ + 1)
  let d₀ := Real.log (1 + 1 / (T₁ + 1))
  have hθrange : ϑ ∈ Set.Icc (-Aθ) Aθ := by
    constructor <;> dsimp [Aθ] <;> linarith [neg_abs_le ϑ, le_abs_self ϑ]
  have hT₀pos : 0 < T₀ := by dsimp [T₀]; linarith
  have hT₁pos : 0 < T₁ := by
    dsimp [T₁]
    have hleft : 0 < t₀ / 2 + 1 := by linarith
    exact lt_of_lt_of_le hleft (le_max_left _ _)
  have hT₀T₁ : T₀ < T₁ := by
    dsimp [T₀, T₁]
    linarith [le_max_left (t₀ / 2 + 1) (t₁ + 1)]
  have hT₁ge : t₁ + 1 ≤ T₁ := le_max_right _ _
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    apply Real.log_pos
    have hfrac : 0 < 1 / (T₁ + 1) := by positivity
    linarith
  obtain ⟨hVDfirst, _⟩ := hVD Aθ
  obtain ⟨CVD, hVDlarge⟩ := hVDfirst T₀ T₁ hT₀pos hT₀T₁
  obtain ⟨Csm, hCsmpos, hsmLarge⟩ := Renewal.secondMoment_log_bound_horizon ϑ T₁
  obtain ⟨B, hBpos, hgreenBound⟩ := truncatedGreen_le_log_bound
  let S := Csm / d₀
  have hSpos : 0 < S := by dsimp [S]; exact div_pos hCsmpos hd₀
  let D₀ := greenAbsorbConstant S B T₁
  let Cfinal := Real.log D₀ + 2 * |CVD| + 1
  have hD₀ : 1 ≤ D₀ := by
    have hlog1 : 0 ≤ Real.log (1 + 16 * T₁) :=
      Real.log_nonneg (by nlinarith [hT₁pos])
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hSB : 0 ≤ S * B := mul_nonneg hSpos.le hBpos.le
    dsimp [D₀, greenAbsorbConstant]
    nlinarith [mul_nonneg hSB (show 0 ≤ 1 + Real.log (1 + 16 * T₁) +
      2 * Real.log 2 by linarith)]
  have hCfinalge1 : 1 ≤ Cfinal := by
    have hlogD : 0 ≤ Real.log D₀ := Real.log_nonneg hD₀
    dsimp [Cfinal]
    nlinarith [abs_nonneg CVD]
  have hN₀ : ∀ᶠ N : ℕ in atTop, 4 / t₀ ≤ (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (⌈4 / t₀⌉₊)] with N hN
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
  have hN₄ : ∀ᶠ N : ℕ in atTop, 4 ≤ N := eventually_ge_atTop 4
  have hsigmaSmall : ∀ᶠ N : ℕ in atTop, criticalSigmaSq ϑ N < 1 :=
    (Renewal.tendsto_sigma_zero ϑ).eventually (Iio_mem_nhds (by norm_num))
  have hsigmaPos : ∀ᶠ N : ℕ in atTop, 0 < criticalSigmaSq ϑ N :=
    Renewal.criticalSigmaSq_eventually_pos ϑ
  have hSigmaMoment (N L : ℕ) (hN : 0 < N) (hL : (L : ℝ) ≤ T₁ * N)
      (hsmN : ∀ L : ℕ, (L : ℝ) ≤ T₁ * N →
        criticalSigmaSq ϑ N *
          ∫ ω, pointToPlane (criticalBeta ϑ N) 0 L 0 ω ^ 2 ∂disorderLaw ≤
            Csm / Real.log (1 + (N : ℝ) / (L + 1))) :
      criticalSigmaSq ϑ N *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 L 0 ω ^ 2 ∂disorderLaw ≤ S := by
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hdenom : (L : ℝ) + 1 ≤ (T₁ + 1) * N := by nlinarith [hL, hNreal]
    have hratio : 1 / (T₁ + 1) ≤ (N : ℝ) / (L + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hdenom]
    have hlogdenom : d₀ ≤ Real.log (1 + (N : ℝ) / (L + 1)) := by
      dsimp [d₀]
      apply Real.log_le_log (by positivity)
      linarith
    calc
      _ ≤ Csm / Real.log (1 + (N : ℝ) / (L + 1)) := hsmN L hL
      _ ≤ Csm / d₀ := div_le_div_of_nonneg_left hCsmpos.le hd₀ hlogdenom
      _ = S := by rfl
  refine ⟨Cfinal, ?_⟩
  filter_upwards [hN₀, hN₄, hVDlarge, hsmLarge, criticalBeta_spec ϑ,
      hsigmaSmall, hsigmaPos] with N hN₀ hN₄ hVDN hsmN hspec hsigmaSmallN hsigmaPosN
  have hNpos : 0 < N := by omega
  have hSigma (L : ℕ) (hL : (L : ℝ) ≤ T₁ * N) :
      criticalSigmaSq ϑ N *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 L 0 ω ^ 2 ∂disorderLaw ≤ S :=
    hSigmaMoment N L hNpos hL hsmN
  have hβpos : 0 ≤ criticalBeta ϑ N := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hT₁pos' : 0 < T₁ := hT₁pos
  intro T t ht hT δ δ' hδ hδt hδ' hδ't x y hxy
  let a := evenCeil ((N : ℝ) * (T - t + δ))
  let a' := evenCeil ((N : ℝ) * (T - t + δ'))
  let b := evenCeil ((N : ℝ) * T)
  let m := evenCeil ((N : ℝ) * δ)
  let l := evenCeil ((N : ℝ) * δ')
  let β := criticalBeta ϑ N
  let sx := latticePoint N x
  let sy := latticePoint N y
  let ν : Site → ℝ := fun w => srwKernel m (w - sx)
  let μ : Site → ℝ := fun w => srwKernel l (w - sy)
  let A := Polymer.endpoints sx m
  let Bset := Polymer.endpoints sy l
  let profX : Disorder → ℝ := fun ω =>
    profileP2Fun β a b ν (fun _ => 1) ω
  let profY : Disorder → ℝ := fun ω =>
    profileP2Fun β a' b μ (fun _ => 1) ω
  have hTminus : 0 ≤ T - t := sub_nonneg.mpr hT
  have hδa : δ ≤ T - t + δ := by linarith
  have hδ'a : δ' ≤ T - t + δ' := by linarith
  have hδt' : δ < t := by linarith
  have hδ't' : δ' < t := by linarith
  have hargA : (N : ℝ) * (T - t + δ) ≤ (N : ℝ) * T :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)
  have hargA' : (N : ℝ) * (T - t + δ') ≤ (N : ℝ) * T :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)
  have hargM : (N : ℝ) * δ ≤ (N : ℝ) * (T - t + δ) :=
    mul_le_mul_of_nonneg_left hδa (Nat.cast_nonneg N)
  have hargL : (N : ℝ) * δ' ≤ (N : ℝ) * (T - t + δ') :=
    mul_le_mul_of_nonneg_left hδ'a (Nat.cast_nonneg N)
  have hma : m ≤ a := by dsimp [m, a]; exact evenCeil_mono hargM
  have hla : l ≤ a' := by dsimp [l, a']; exact evenCeil_mono hargL
  have hab : a ≤ b := by dsimp [a, b]; exact evenCeil_mono hargA
  have ha'b : a' ≤ b := by dsimp [a', b]; exact evenCeil_mono hargA'
  have hmEven : Even m := by dsimp [m]; exact evenCeil_even _
  have hlEven : Even l := by dsimp [l]; exact evenCeil_even _
  have hbaEven : Even (b - a) := by
    dsimp [a, b]
    exact Critical2DKPZ.SHF.Moments.even_evenCeil_sub _ _
  have hba'Even : Even (b - a') := by
    dsimp [a', b]
    exact Critical2DKPZ.SHF.Moments.even_evenCeil_sub _ _
  have hNtimeEven : Even (m + (b - a)) := Even.add hmEven hbaEven
  have hNtime'Even : Even (l + (b - a')) := Even.add hlEven hba'Even
  have hboundX := heatStart_horizon_bounds hN₄ ht₀ ht hT hδ hδt hN₀
  have hboundY := heatStart_horizon_bounds hN₄ ht₀ ht hT hδ' hδ't hN₀
  have hsiteX : sx ∈ evenLattice := by dsimp [sx]; exact latticePoint_mem_evenLattice N x
  have hsiteY : sy ∈ evenLattice := by dsimp [sy]; exact latticePoint_mem_evenLattice N y
  have hprofileX (ω : Disorder) : profX ω =
      smoothedP2Plane β m (m + (b - a)) sx
        (Smoothing.shiftEnvironment (a - m) ω) := by
    calc
      profX ω = profileP2Fun β a b ν
          (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω := by
        dsimp [profX]
        exact (profile_heatStart_flat_terminal_eq β N a b m hNpos hmEven hbaEven
          sx hsiteX ω).symm
      _ = smoothedP2Plane β m (m + (b - a)) sx
          (Smoothing.shiftEnvironment (a - m) ω) := by
        dsimp [ν]
        exact profile_heatStart_eq_smoothed_shift β N a b m hNpos hma hab hmEven
          hbaEven sx hsiteX ω
  have hprofileY (ω : Disorder) : profY ω =
      smoothedP2Plane β l (l + (b - a')) sy
        (Smoothing.shiftEnvironment (a' - l) ω) := by
    calc
      profY ω = profileP2Fun β a' b μ
          (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω := by
        dsimp [profY]
        exact (profile_heatStart_flat_terminal_eq β N a' b l hNpos hlEven hba'Even
          sy hsiteY ω).symm
      _ = smoothedP2Plane β l (l + (b - a')) sy
          (Smoothing.shiftEnvironment (a' - l) ω) := by
        dsimp [μ]
        exact profile_heatStart_eq_smoothed_shift β N a' b l hNpos hla ha'b hlEven
          hba'Even sy hsiteY ω
  have hmeasSmoothedX : Measurable (fun ω =>
      Real.log (smoothedP2Plane β m (m + (b - a)) sx ω)) :=
    Real.measurable_log.comp (Polymer.measurable_smoothedP2Plane β m (m + (b - a)) sx)
  have hmeasSmoothedY : Measurable (fun ω =>
      Real.log (smoothedP2Plane β l (l + (b - a')) sy ω)) :=
    Real.measurable_log.comp (Polymer.measurable_smoothedP2Plane β l (l + (b - a')) sy)
  have hVDx := hVDN ϑ hθrange sx m (m + (b - a)) hmEven hNtimeEven
    (by omega) hboundX.1 hboundX.2
  have hVDy := hVDN ϑ hθrange sy l (l + (b - a')) hlEven hNtime'Even
    (by omega) hboundY.1 hboundY.2
  have hdefX : gaussianityDefect disorderLaw (fun ω => Real.log (profX ω)) ≤ CVD := by
    calc
      _ = gaussianityDefect disorderLaw (fun ω =>
          Real.log (smoothedP2Plane β m (m + (b - a)) sx
            (Smoothing.shiftEnvironment (a - m) ω))) := by
          congr 1
          funext ω
          exact congrArg Real.log (hprofileX ω)
      _ = gaussianityDefect disorderLaw
          (fun ω => Real.log (smoothedP2Plane β m (m + (b - a)) sx ω)) :=
          gaussianityDefect_shiftEnvironment (a - m) _ hmeasSmoothedX
      _ ≤ CVD := (hVDx.2.1.trans hVDx.2.2)
  have hdefY : gaussianityDefect disorderLaw (fun ω => Real.log (profY ω)) ≤ CVD := by
    calc
      _ = gaussianityDefect disorderLaw (fun ω =>
          Real.log (smoothedP2Plane β l (l + (b - a')) sy
            (Smoothing.shiftEnvironment (a' - l) ω))) := by
          congr 1
          funext ω
          exact congrArg Real.log (hprofileY ω)
      _ = gaussianityDefect disorderLaw
          (fun ω => Real.log (smoothedP2Plane β l (l + (b - a')) sy ω)) :=
          gaussianityDefect_shiftEnvironment (a' - l) _ hmeasSmoothedY
      _ ≤ CVD := (hVDy.2.1.trans hVDy.2.2)
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem m sx w hw
  have hμB : ∀ w ∉ Bset, μ w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem l sy w hw
  have hν0 : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg m (w - sx)
  have hμ0 : ∀ w, 0 ≤ μ w := fun w => Polymer.kernel_nonneg l (w - sy)
  have hνsum : ∑ w ∈ A, ν w = 1 := by
    dsimp [A, ν]
    exact Polymer.sum_srwKernel_endpoints m sx
  have hμsum : ∑ w ∈ Bset, μ w = 1 := by
    dsimp [Bset, μ]
    exact Polymer.sum_srwKernel_endpoints l sy
  have hνpos : ∃ w ∈ A, 0 < ν w := by
    apply (Finset.sum_pos_iff_of_nonneg (fun w _ => hν0 w)).1
    simp [hνsum]
  have hμpos : ∃ w ∈ Bset, 0 < μ w := by
    apply (Finset.sum_pos_iff_of_nonneg (fun w _ => hμ0 w)).1
    simp [hμsum]
  have hcovNonneg : 0 ≤ covariance (fun ω => Real.log (profX ω))
      (fun ω => Real.log (profY ω)) disorderLaw := by
    have hXlog : (fun ω => Real.log (profX ω)) =
        fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω) := rfl
    have hYlog : (fun ω => Real.log (profY ω)) =
        fun ω => Real.log (profileP2Fun β a' b μ (fun _ => 1) ω) := rfl
    rw [hXlog, hYlog]
    exact covariance_log_profile_nonneg β β hβpos hβpos a b a' b ν μ A Bset
      hνA hμB hν0 hμ0 hνpos hμpos
  have hjoint := covariance_log_profile_le_joint β a b a' b ν μ A Bset
    hνA hμB hν0 hμ0 hνpos hμpos
  let gap := max a a' - min a a'
  have hgapEven : Even gap := by
    by_cases haa' : a ≤ a'
    · dsimp [gap]
      simpa [max_eq_right haa', min_eq_left haa'] using
        (Critical2DKPZ.SHF.Moments.even_evenCeil_sub
          ((N : ℝ) * (T - t + δ)) ((N : ℝ) * (T - t + δ')))
    · have ha'a : a' ≤ a := le_of_not_ge haa'
      dsimp [gap]
      simpa [max_eq_left ha'a, min_eq_right ha'a] using
        (Critical2DKPZ.SHF.Moments.even_evenCeil_sub
          ((N : ℝ) * (T - t + δ')) ((N : ℝ) * (T - t + δ)))
  have hdoubleEven : Even (m + l + gap) := Even.add (Even.add hmEven hlEven) hgapEven
  obtain ⟨k, hk⟩ := hdoubleEven
  have hk' : m + l + (max a a' - min a a') = 2 * k := by
    dsimp [gap] at hk
    simpa [two_mul, add_assoc] using hk
  have hH1 : ((m + (b - a) : ℕ) : ℝ) ≤ T₁ * N := hboundX.2
  have hH2 : ((l + (b - a') : ℕ) : ℝ) ≤ T₁ * N := hboundY.2
  have hHindex : k + (b - max a a') ≤ max (m + (b - a)) (l + (b - a')) := by
    omega
  have hHmax : ((max (m + (b - a)) (l + (b - a') : ℕ) : ℕ) : ℝ) ≤ T₁ * N := by
    rw [Nat.cast_max]
    exact max_le_iff.mpr ⟨hH1, hH2⟩
  have hHreal : ((k + (b - max a a') : ℕ) : ℝ) ≤ T₁ * N :=
    (Nat.cast_le.mpr hHindex).trans hHmax
  have hSigmaBound : ∀ L : ℕ, (L : ℝ) ≤ T₁ * N →
      criticalSigmaSq ϑ N *
        ∫ ω, pointToPlane β 0 L 0 ω ^ 2 ∂disorderLaw ≤ S := by
    intro L hL
    simpa only [β] using hSigma L hL
  have hcollision := heatStart_product_mixedTimes_symm β a a' b m l hab ha'b sx sy
  have hcollisionBound := heatStart_collision_sum_le_green ϑ N T₁ S β hSpos.le hspec
    hSigmaBound a a' b m l k hab ha'b hk' hH1 hH2 (sy - sx)
  let collisionSum := ∑ r ∈ Finset.Icc 1 (b - max a a'),
    srwKernel (m + l + (max a a' - min a a') + 2 * r) (sy - sx) *
      Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (b - max a a' - r) 0 ω ^ 2 ∂disorderLaw)
  have hcollisionEq : (∫ ω, profX ω * profY ω ∂disorderLaw) - 1 = collisionSum := by
    dsimp [profX, profY, ν, μ, sx, sy, a, a', b, m, l, β, collisionSum]
    exact hcollision
  have hcollisionNonneg : 0 ≤ collisionSum := by
    dsimp [collisionSum]
    apply Finset.sum_nonneg
    intro r hr
    have hσ : 0 ≤ Polymer.sigmaSq β := by
      unfold Polymer.sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
    exact mul_nonneg (mul_nonneg (Polymer.kernel_nonneg _ _) hσ)
      (integral_nonneg fun ω => sq_nonneg _)
  have hJlower : 1 ≤ ∫ ω, profX ω * profY ω ∂disorderLaw := by
    linarith [hcollisionEq, hcollisionNonneg]
  have hgreenNonneg : 0 ≤ MomentBounds.truncatedGreen
      (k + (b - max a a')) (sy - sx) := by
    simp only [MomentBounds.truncatedGreen]
    apply Finset.sum_nonneg
    intro r hr
    exact Polymer.kernel_nonneg (2 * r) (sy - sx)
  have hlogJ : Real.log (∫ ω, profX ω * profY ω ∂disorderLaw) ≤
      Real.log (1 + S * MomentBounds.truncatedGreen
        (k + (b - max a a')) (sy - sx)) := by
    rw [show (∫ ω, profX ω * profY ω ∂disorderLaw) = 1 + collisionSum by
      linarith [hcollisionEq]]
    apply Real.log_le_log (by linarith [hcollisionNonneg])
    dsimp [collisionSum] at hcollisionBound ⊢
    linarith [hcollisionBound]
  have hgreenPlane := hgreenBound (k + (b - max a a')) (sy - sx)
  obtain ⟨_, hlogGreen⟩ := log_green_to_plane_bound S B T₁ hSpos.le hBpos
    hT₁pos' hNpos hHreal hxy hgreenPlane
  have hLnonneg : 0 ≤ Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
    apply Real.log_nonneg
    linarith [le_max_left (0 : ℝ) (Real.log ‖x - y‖⁻¹)]
  have hcovUpper : covariance (fun ω => Real.log (profX ω))
      (fun ω => Real.log (profY ω)) disorderLaw ≤
        Cfinal * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) := by
    have hdefect : gaussianityDefect disorderLaw (fun ω => Real.log (profX ω)) +
        gaussianityDefect disorderLaw (fun ω => Real.log (profY ω)) ≤ 2 * CVD := by
      linarith [hdefX, hdefY]
    have hcore : covariance (fun ω => Real.log (profX ω))
        (fun ω => Real.log (profY ω)) disorderLaw ≤
          Real.log (1 + S * MomentBounds.truncatedGreen
            (k + (b - max a a')) (sy - sx)) + 2 * CVD := by
      calc
        _ ≤ Real.log (∫ ω, profX ω * profY ω ∂disorderLaw) +
            (gaussianityDefect disorderLaw (fun ω => Real.log (profX ω)) +
              gaussianityDefect disorderLaw (fun ω => Real.log (profY ω))) := by
          simpa [add_assoc] using hjoint
        _ ≤ _ := add_le_add hlogJ hdefect
    have hdistBound : covariance (fun ω => Real.log (profX ω))
        (fun ω => Real.log (profY ω)) disorderLaw ≤
          (Real.log D₀ + 2 * |CVD|) + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
      calc
        _ ≤ Real.log (1 + S * MomentBounds.truncatedGreen
            (k + (b - max a a')) (sy - sx)) + 2 * CVD := hcore
        _ ≤ (Real.log D₀ + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) +
              2 * CVD := by
                have h := hlogGreen
                dsimp [sy, sx, D₀] at h ⊢
                linarith only [h]
        _ ≤ (Real.log D₀ + 2 * |CVD|) +
              Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
          have hCVD : 2 * CVD ≤ 2 * |CVD| :=
            mul_le_mul_of_nonneg_left (le_abs_self CVD) (by norm_num : (0 : ℝ) ≤ 2)
          linarith only [hCVD]
    have hbase : Real.log D₀ + 2 * |CVD| ≤ Cfinal := by
      change Real.log D₀ + 2 * |CVD| ≤ (Real.log D₀ + 2 * |CVD|) + 1
      exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
    calc
      _ ≤ (Real.log D₀ + 2 * |CVD|) +
          Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := hdistBound
      _ ≤ Cfinal + Cfinal * Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)) := by
        apply add_le_add hbase
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hCfinalge1 hLnonneg
      _ = _ := by ring
  have htargetX : (fun ω => Real.log (profileP2Fun β a b ν
      (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)) =
      fun ω => Real.log (profX ω) := by
    funext ω
    exact congrArg Real.log (profile_heatStart_flat_terminal_eq β N a b m hNpos
      hmEven hbaEven sx hsiteX ω)
  have htargetY : (fun ω => Real.log (profileP2Fun β a' b μ
      (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)) =
      fun ω => Real.log (profY ω) := by
    funext ω
    exact congrArg Real.log (profile_heatStart_flat_terminal_eq β N a' b l hNpos
      hlEven hba'Even sy hsiteY ω)
  rw [htargetX, htargetY]
  exact ⟨hcovNonneg, hcovUpper⟩

end Critical2DKPZ.LocalSobolev

end
