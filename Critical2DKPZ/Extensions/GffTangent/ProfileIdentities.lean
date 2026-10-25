/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.FutureProfiles.SmoothedEndpointProfile
public import Critical2DKPZ.Blocks.Expansion
public import Critical2DKPZ.FutureProfiles.Basic
public import Critical2DKPZ.FutureProfiles.OpenCorrectorEnergy
import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
import Critical2DKPZ.FutureProfiles.FreezingPast
import Critical2DKPZ.FutureProfiles.EndpointTranslation
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Critical2DKPZ.Analysis.Heat.Semigroup
import Critical2DKPZ.Assembly.RegularizedInvariance
public import Critical2DKPZ.Provider.ShfSymmetries

/-!
# Endpoint-profile mass identities

At the flow, the profile mass is the ratio of the two heat-started masses.
At the lattice, the Chapman--Kolmogorov theorem identifies this ratio with
the future mass of the normalized endpoint profile.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped BoundedContinuousFunction BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

open Blocks FutureProfiles Collision Polymer

/-- Future mass of the endpoint profile observed at time `n`, expressed as a
ratio of heat-started masses. Its measurability under a critical SHF is proved
in `aemeasurable_profileMass`. -/
def profileMass {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (a n T : ℝ) (x : Plane) (ω : Ω) : ℝ :=
  shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω /
    shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1) ω

/-- The ratio description at the flow is the definition, with no filtration
or continuum conditional expectation assumption. -/
theorem profileMass_flow_ratio {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (a n T : ℝ) (x : Plane) (ω : Ω) :
    profileMass Z a n T x ω =
      shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω /
        shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1) ω := rfl

/-- A positive-time heat-start mass is almost everywhere measurable. -/
theorem aemeasurable_profileHeatMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ϑ : ℝ}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    AEMeasurable (fun ω => shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω) P := by
  have h := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
    a T a x (0 : Plane →ᵇ ℝ) ha.le haT ha
  have hzero : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) = fun _ => 1 := by
    funext y
    change Real.exp (0 : ℝ) = 1
    exact Real.exp_zero
  rw [hzero] at h
  apply h.2.1.exp.congr
  filter_upwards [h.1] with ω hω
  exact Real.exp_log hω

/-- Explicit measurability of the profile ratio under a critical SHF. -/
theorem aemeasurable_profileMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ϑ : ℝ}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a n T : ℝ} (ha : 0 < a) (han : a < n) (haT : a < T) (x : Plane) :
    AEMeasurable (profileMass Z a n T x) P :=
  (aemeasurable_profileHeatMass P Z hZ ha haT x).div
    (aemeasurable_profileHeatMass P Z hZ ha han x)

/-- The normalized endpoint law has the claimed future mass at the lattice. -/
theorem profileMass_lattice_ratio (β : ℝ) {a n T : ℕ} (han : a ≤ n) (hnT : n ≤ T)
    (x : Site) (ω : Disorder) :
    profileP2Fun β n T (smoothedEndpointDist β a n x ω) (fun _ => 1) ω =
      smoothedP2Plane β a T x ω / smoothedP2Plane β a n x ω :=
  FutureProfiles.profileP2Fun_smoothedEndpointDist_eq_div β han hnT x ω

/-- Heat-start lattice pairing is the smoothed point-to-plane mass. -/
theorem profileHeatMass_lattice (β : ℝ) (a T : ℕ) (x : Site) (ω : Disorder) :
    profileP2Fun β a T (fun y => srwKernel a (y - x)) (fun _ => 1) ω =
      smoothedP2Plane β a T x ω := by
  simp only [profileP2Fun, smoothedP2Plane, mul_one, Polymer.tsum_pointToPoint]


/-- The heat-start density transforms with the inverse Jacobian under the
same spatial scaling as the flow. -/
theorem profileHeatKernel_scaled_eq {a : ℝ} (ha : 0 < a) (b : ℝ) (x y : Plane) :
    heatKernel (b / a) ((Real.sqrt a)⁻¹ • y - (Real.sqrt a)⁻¹ • x) =
      a * heatKernel b (y - x) := by
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hscale : ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ := by
    rw [inv_pow, Real.sq_sqrt ha.le]
  have h := heatKernel_scaling (a := (Real.sqrt a)⁻¹) (u := b) (inv_pos.mpr hsqrt) (y - x)
  rw [hscale, inv_inv, smul_sub] at h
  convert h using 1
  congr 1
  ring

/-- Heat-start pairings are invariant pathwise under the horizon scaling.
No stochastic flow property is needed for this transport identity. -/
theorem shfPairing_scaled_eq {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {a : ℝ} (ha : 0 < a)
    (b T : ℝ) (x : Plane) (ω : Ω) :
    shfPairing (fun s t ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map
        (fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)))
      (b / a) (T / a)
      (fun y => heatKernel (b / a) (y - (Real.sqrt a)⁻¹ • x)) (fun _ => 1) ω =
      shfPairing Z b T (fun y => heatKernel b (y - x)) (fun _ => 1) ω := by
  rw [Assembly.shfPairing_scaleTransport Z a (Real.sqrt a)
    (ne_of_gt (Real.sqrt_pos.mpr ha)) (ENNReal.ofReal a⁻¹)]
  have hb : a * (b / a) = b := by field_simp
  have hT : a * (T / a) = T := by field_simp
  rw [hb, hT, ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)]
  simp only [profileHeatKernel_scaled_eq ha, shfPairing, mul_one,
    MeasureTheory.integral_const_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ha), one_mul]

/-- The future profile mass is invariant under horizon scaling. -/
theorem profileMass_scaled_eq {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {a : ℝ} (ha : 0 < a)
    (b n T : ℝ) (x : Plane) (ω : Ω) :
    profileMass (fun s t ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map
        (fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)))
      (b / a) (n / a) (T / a) ((Real.sqrt a)⁻¹ • x) ω = profileMass Z b n T x ω := by
  unfold profileMass
  rw [shfPairing_scaled_eq Z ha b T x ω, shfPairing_scaled_eq Z ha b n x ω]

/-- Scaling the exponential horizon to one changes parameter `-l` into the
fixed parameter `log c`, independently of `l`. -/
theorem isCriticalSHF_profile_horizon_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {c l : ℝ} (hc : 0 < c)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z) :
    IsCriticalSHF (Real.log c) P (fun s t ω =>
      ENNReal.ofReal (c * Real.exp l)⁻¹ •
        (Z ((c * Real.exp l) * s) ((c * Real.exp l) * t) ω).map
          (fun p => ((Real.sqrt (c * Real.exp l))⁻¹ • p.1,
            (Real.sqrt (c * Real.exp l))⁻¹ • p.2))) := by
  have h := (Provider.shf_symmetries (-l) P Z hZ).2.2.2.1
    (c * Real.exp l) (mul_pos hc (Real.exp_pos l))
  have hparam : -l + Real.log (c * Real.exp l) = Real.log c := by
    rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos l)), Real.log_exp]
    ring
  rwa [hparam] at h

/-- Finite-support, boundedness and past measurability data for the
difference of two heat-started endpoint profiles. -/
theorem profile_endpoint_difference_data (β : ℝ) {a b n : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) :
    ∃ S : Finset Site,
      (∀ ω y, y ∉ S → smoothedEndpointDist β a n 0 ω y = 0) ∧
      (∀ ω y, y ∉ S → smoothedEndpointDist β b n 0 ω y = 0) ∧
      (∀ ω y, |smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y| ≤ 2) ∧
      (∀ y, Measurable[disorderPast n] (fun ω =>
        smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y)) := by
  classical
  let S (m : ℕ) := (Polymer.endpoints 0 m).biUnion (fun y => Polymer.endpoints y (n - m))
  have hsupp (m : ℕ) (ω : Disorder) (y : Site) (hy : y ∉ S m) :
      smoothedEndpointDist β m n 0 ω y = 0 :=
    Smoothing.smoothedEndpointDist_eq_zero_of_not_mem β 0 y ω hy
  have hbound (m : ℕ) (hm : m ≤ n) (ω : Disorder) (y : Site) :
      |smoothedEndpointDist β m n 0 ω y| ≤ 1 := by
    have hdata := Smoothing.smoothedEndpointDist_probability β hm 0 ω
    by_cases hy : y ∈ S m
    · rw [abs_of_nonneg (hdata.2.1 y)]
      exact (Finset.single_le_sum (fun z _ => hdata.2.1 z) hy).trans_eq hdata.2.2
    · rw [hsupp m ω y hy]
      norm_num
  refine ⟨S a ∪ S b, ?_, ?_, ?_, ?_⟩
  · intro ω y hy
    exact hsupp a ω y (fun h => hy (Finset.mem_union_left _ h))
  · intro ω y hy
    exact hsupp b ω y (fun h => hy (Finset.mem_union_right _ h))
  · intro ω y
    exact (abs_sub _ _).trans (by linarith only [hbound a ha ω y, hbound b hb ω y])
  · intro y
    rw [← Gaussian.disorderBlock_zero n]
    exact ((Polymer.measurable_smoothedEndpointDist_block β a n ha 0 y).mono
      (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl).sub
      ((Polymer.measurable_smoothedEndpointDist_block β b n hb 0 y).mono
        (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl)

/-- The expected absolute difference of future masses is bounded by the
expected future seminorm of the difference of their endpoint profiles. -/
theorem profile_future_mass_comparison_le (β : ℝ) {a b n N : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hn : n ≤ N) (G : Set Disorder)
    (hG : MeasurableSet[disorderPast n] G) :
    (∫ ω in G, |profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) 1 ω -
      profileP2Fun β n N (smoothedEndpointDist β b n 0 ω) 1 ω| ∂disorderLaw) ≤
    ∫ ω in G, Real.sqrt (FutureProfiles.futureEnergy β n N (fun y =>
      smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y)) ∂disorderLaw := by
  obtain ⟨S, hSa, hSb, hbound, hmeas⟩ := profile_endpoint_difference_data β ha hb
  have hsub (ω : Disorder) (y : Site) (hy : y ∉ S) :
      smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y = 0 := by
    rw [hSa ω y hy, hSb ω y hy, sub_self]
  have heq (ω : Disorder) : profileP2Fun β n N
      (fun y => smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y) 1 ω =
      profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) 1 ω -
        profileP2Fun β n N (smoothedEndpointDist β b n 0 ω) 1 ω := by
    rw [Polymer.profileP2Fun_eq_sum β n N _ _ S (hsub ω),
      Polymer.profileP2Fun_eq_sum β n N _ _ S (hSa ω),
      Polymer.profileP2Fun_eq_sum β n N _ _ S (hSb ω), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    exact sub_mul _ _ _
  have h := FutureProfiles.setIntegral_abs_profileP2Fun_le β hn
    (fun ω y => smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y)
    S hsub ⟨2, hbound⟩ hmeas G hG
  calc
    _ = ∫ ω in G, |profileP2Fun β n N (fun y =>
        smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y) 1 ω| ∂disorderLaw :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => congrArg abs (heq ω).symm)
    _ ≤ _ := h

/-- Propagation of a finitely supported random initial profile to an
intermediate time, before its normalization. -/
def profileTransport (β : ℝ) (n S : ℕ) (A : Finset Site)
    (η : Disorder → Site → ℝ) (ω : Disorder) (y : Site) : ℝ :=
  ∑ x ∈ A, η ω x * pointToPoint β n (S - n) x y ω

/-- The propagated profile has a deterministic finite support. -/
theorem profileTransport_support (β : ℝ) (n S : ℕ) (A : Finset Site)
    (η : Disorder → Site → ℝ) (ω : Disorder) (y : Site)
    (hy : y ∉ A.biUnion (fun x => Polymer.endpoints x (S - n))) :
    profileTransport β n S A η ω y = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [Polymer.pointToPoint_eq_zero_of_not_mem β n (S - n) x y ω (by
    intro h; exact hy (Finset.mem_biUnion.mpr ⟨x, hx, h⟩)), mul_zero]

/-- Chapman–Kolmogorov for a finitely supported initial profile propagated
through an intermediate observation time. -/
theorem profileP2Fun_profileTransport (β : ℝ) {n S N : ℕ} (hnS : n ≤ S) (hSN : S ≤ N)
    (A : Finset Site) (η : Disorder → Site → ℝ)
    (hη : ∀ ω y, y ∉ A → η ω y = 0) (ω : Disorder) :
    profileP2Fun β S N (profileTransport β n S A η ω) 1 ω =
      profileP2Fun β n N (η ω) 1 ω := by
  classical
  let B := A.biUnion (fun x => Polymer.endpoints x (S - n))
  have hsum (a b : ℕ) (w : Site) : (∑' z, pointToPoint β a b w z ω * (1 : Site → ℝ) z) =
      pointToPlane β a b w ω := by
    simp only [Pi.one_apply, mul_one, Polymer.tsum_pointToPoint]
  rw [Polymer.profileP2Fun_eq_sum β S N _ _ B
    (profileTransport_support β n S A η ω),
    Polymer.profileP2Fun_eq_sum β n N _ _ A (hη ω)]
  simp only [hsum, profileTransport]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hCK := Polymer.pointToPlane_chapmanKolmogorov β n (S - n) (N - S) x ω
  rw [Nat.add_sub_of_le hnS, show S - n + (N - S) = N - n by omega] at hCK
  rw [hCK]
  symm
  exact tsum_eq_sum fun y hy => by
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β n (S - n) x y ω (by
      intro h; exact hy (Finset.mem_biUnion.mpr ⟨x, hx, h⟩)), zero_mul]

/-- The total mass of the propagated profile is the mass at the
intermediate horizon. -/
theorem profileTransport_sum (β : ℝ) {n S : ℕ} (hnS : n ≤ S)
    (A : Finset Site) (η : Disorder → Site → ℝ)
    (hη : ∀ ω y, y ∉ A → η ω y = 0) (ω : Disorder) :
    (∑ y ∈ A.biUnion (fun x => Polymer.endpoints x (S - n)), profileTransport β n S A η ω y) =
      profileP2Fun β n S (η ω) 1 ω := by
  have h := profileP2Fun_profileTransport β hnS (le_refl S) A η hη ω
  rw [Polymer.profileP2Fun_eq_sum β S S _ _
    (A.biUnion (fun x => Polymer.endpoints x (S - n)))
    (profileTransport_support β n S A η ω)] at h
  simpa only [Nat.sub_self, Pi.one_apply, mul_one, Polymer.tsum_pointToPoint,
    Polymer.pointToPlane_zero] using h

/-- Conditional expectation of a finite-profile polymer at an intermediate
horizon. No continuum filtration is needed. -/
theorem condExp_profileP2Fun_horizon (β : ℝ) {n S N : ℕ}
    (hnS : n ≤ S) (hSN : S ≤ N) (A : Finset Site) (η : Disorder → Site → ℝ)
    (hη : ∀ ω y, y ∉ A → η ω y = 0)
    (hbounded : ∃ M : ℝ, ∀ ω y, |η ω y| ≤ M)
    (hmeas : ∀ y, Measurable[disorderPast n] (η · y)) :
    disorderLaw[(fun ω => profileP2Fun β n N (η ω) 1 ω) | disorderPast S] =ᵐ[disorderLaw]
      fun ω => profileP2Fun β n S (η ω) 1 ω := by
  classical
  let B := A.biUnion (fun x => Polymer.endpoints x (S - n))
  let ξ := profileTransport β n S A η
  let X := fun ω => profileP2Fun β n N (η ω) 1 ω
  have hξsupp : ∀ ω y, y ∉ B → ξ ω y = 0 := profileTransport_support β n S A η
  have hpast : disorderPast n ≤ disorderPast S := by
    rw [← Gaussian.disorderBlock_zero n, ← Gaussian.disorderBlock_zero S]
    exact Gaussian.disorderBlock_mono le_rfl hnS
  have hξmeas (y : Site) : Measurable[disorderPast S] (ξ · y) := by
    apply Finset.measurable_sum
    intro x _
    apply ((hmeas x).mono hpast le_rfl).mul
    rw [← Gaussian.disorderBlock_zero S]
    have hm := Polymer.measurable_pointToPoint_block β n (S - n) x y
    rw [Nat.add_sub_of_le hnS] at hm
    exact hm.mono (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl
  have heq : Collision.randomFlatProfilePolymer β S N ξ = X := by
    funext ω
    exact profileP2Fun_profileTransport β hnS hSN A η hη ω
  have hXm : Measurable X := FutureProfiles.measurable_randomTerminalProfilePolymer
    β n N A η 1 hη hmeas
  have hXi : Integrable X disorderLaw := FutureProfiles.integrable_randomTerminalProfilePolymer
    β n N A η 1 hη hbounded hmeas 1 (by intro y; simp)
  have hc := Collision.condExp_randomFlatProfilePolymer β S N hSN B ξ hξsupp hξmeas
    (heq.symm ▸ hXm) (heq.symm ▸ hXi)
  rw [heq] at hc
  filter_upwards [hc] with ω hω
  exact hω.trans (profileTransport_sum β hnS A η hη ω)

/-- Conditioning a future mass back to a shorter horizon decreases its
expected absolute value on every event already observable at that horizon. -/
theorem profileP2Fun_horizon_abs_integral_le (β : ℝ) {n S N : ℕ}
    (hnS : n ≤ S) (hSN : S ≤ N) (A : Finset Site) (η : Disorder → Site → ℝ)
    (hη : ∀ ω y, y ∉ A → η ω y = 0)
    (hbounded : ∃ M : ℝ, ∀ ω y, |η ω y| ≤ M)
    (hmeas : ∀ y, Measurable[disorderPast n] (η · y))
    (G : Set Disorder) (hG : MeasurableSet[disorderPast S] G) :
    (∫ ω in G, |profileP2Fun β n S (η ω) 1 ω| ∂disorderLaw) ≤
      ∫ ω in G, |profileP2Fun β n N (η ω) 1 ω| ∂disorderLaw := by
  have hc := condExp_profileP2Fun_horizon β hnS hSN A η hη hbounded hmeas
  calc
    _ = ∫ ω in G, |disorderLaw[(fun ω => profileP2Fun β n N (η ω) 1 ω) | disorderPast S] ω|
        ∂disorderLaw := integral_congr_ae ((ae_restrict_of_ae hc).mono
          fun ω h => congrArg abs h.symm)
    _ ≤ _ := setIntegral_abs_condExp_le hG _

/-- Linearity in a difference of finitely supported initial profiles. -/
theorem profileP2Fun_sub_of_support (β : ℝ) (a b : ℕ) (ν ξ f : Site → ℝ)
    (A : Finset Site) (hν : ∀ y ∉ A, ν y = 0) (hξ : ∀ y ∉ A, ξ y = 0) (ω : Disorder) :
    profileP2Fun β a b (ν - ξ) f ω = profileP2Fun β a b ν f ω - profileP2Fun β a b ξ f ω := by
  rw [Polymer.profileP2Fun_eq_sum β a b _ _ A
    (by intro y hy; simp only [Pi.sub_apply, hν y hy, hξ y hy, sub_self]),
    Polymer.profileP2Fun_eq_sum β a b _ _ A hν,
    Polymer.profileP2Fun_eq_sum β a b _ _ A hξ, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => sub_mul _ _ _

/-- The lattice two-profile absolute comparison transfers to every shorter
future horizon on a good event measurable at the observation time. -/
theorem profile_future_mass_horizon_comparison (β : ℝ) {a b n S N : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hnS : n ≤ S) (hSN : S ≤ N)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast n] G) :
    (∫ ω in G, |profileP2Fun β n S (smoothedEndpointDist β a n 0 ω) 1 ω -
      profileP2Fun β n S (smoothedEndpointDist β b n 0 ω) 1 ω| ∂disorderLaw) ≤
    (∫ ω in G, |profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) 1 ω -
      profileP2Fun β n N (smoothedEndpointDist β b n 0 ω) 1 ω| ∂disorderLaw) := by
  obtain ⟨A, hA, hB, hbounded, hmeas⟩ := profile_endpoint_difference_data β ha hb
  have hη (ω : Disorder) (y : Site) (hy : y ∉ A) :
      smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y = 0 := by
    rw [hA ω y hy, hB ω y hy, sub_self]
  have hpast : disorderPast n ≤ disorderPast S := by
    rw [← Gaussian.disorderBlock_zero n, ← Gaussian.disorderBlock_zero S]
    exact Gaussian.disorderBlock_mono le_rfl hnS
  have h := profileP2Fun_horizon_abs_integral_le β hnS hSN A
    (fun ω => smoothedEndpointDist β a n 0 ω - smoothedEndpointDist β b n 0 ω)
    hη ⟨2, hbounded⟩ hmeas G (hpast G hG)
  simpa only [profileP2Fun_sub_of_support β n S _ _ 1 A (hA _) (hB _),
    profileP2Fun_sub_of_support β n N _ _ 1 A (hA _) (hB _)] using h

/-- Splitting off a bad event converts an absolute comparison into the
bounded continuous quantity used in the lattice-to-flow passage. -/
theorem profile_integral_min_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) {G : Set Ω} (hG : MeasurableSet G) (M : ℝ) :
    (∫ ω, min |X ω| M ∂P) ≤ (∫ ω in G, |X ω| ∂P) + M * (P Gᶜ).toReal := by
  have hmin := hX.abs.inf (integrable_const M)
  have hleft := hX.abs.integrableOn.integrable_indicator hG
  have hright := (integrable_const (μ := P) M).integrableOn.integrable_indicator hG.compl
  calc
    _ ≤ ∫ ω, (G.indicator (fun ω => |X ω|) ω + Gᶜ.indicator (fun _ => M) ω) ∂P := by
      apply integral_mono_ae hmin (hleft.add hright)
      filter_upwards [] with ω
      change min |X ω| M ≤ G.indicator (fun ω => |X ω|) ω + Gᶜ.indicator (fun _ => M) ω
      by_cases hω : ω ∈ G
      · simpa only [Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω),
          add_zero] using min_le_left |X ω| M
      · simpa only [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω),
          zero_add] using min_le_right |X ω| M
    _ = _ := by
      rw [integral_add hleft hright, integral_indicator hG, integral_indicator hG.compl,
        setIntegral_const]
      simp only [smul_eq_mul, mul_comm]
      rfl

/-- The bounded two-profile comparison at a shorter horizon follows from
the full-horizon comparison and the exceptional probability of a past event. -/
theorem profile_future_mass_truncated_horizon_le (β : ℝ) {a b n S N : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hnS : n ≤ S) (hSN : S ≤ N)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast n] G) (M : ℝ) :
    (∫ ω, min |profileP2Fun β n S (smoothedEndpointDist β a n 0 ω) 1 ω -
      profileP2Fun β n S (smoothedEndpointDist β b n 0 ω) 1 ω| M ∂disorderLaw) ≤
    (∫ ω in G, |profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) 1 ω -
      profileP2Fun β n N (smoothedEndpointDist β b n 0 ω) 1 ω| ∂disorderLaw) +
      M * (disorderLaw Gᶜ).toReal := by
  obtain ⟨A, hA, hB, hbounded, hmeas⟩ := profile_endpoint_difference_data β ha hb
  let η := fun ω => smoothedEndpointDist β a n 0 ω - smoothedEndpointDist β b n 0 ω
  have hη (ω : Disorder) (y : Site) (hy : y ∉ A) : η ω y = 0 := by
    dsimp only [η, Pi.sub_apply]
    rw [hA ω y hy, hB ω y hy, sub_self]
  have hi : Integrable (fun ω => profileP2Fun β n S (η ω) 1 ω) disorderLaw :=
    FutureProfiles.integrable_randomTerminalProfilePolymer β n S A η 1 hη
      ⟨2, hbounded⟩ hmeas 1 (by intro y; simp)
  have hpast : disorderPast n ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero n]
    exact Gaussian.disorderBlock_le _ _
  have hsplit := profile_integral_min_abs_le disorderLaw hi (hpast G hG) M
  have heq (T : ℕ) : (fun ω => profileP2Fun β n T (η ω) 1 ω) =
      fun ω => profileP2Fun β n T (smoothedEndpointDist β a n 0 ω) 1 ω -
        profileP2Fun β n T (smoothedEndpointDist β b n 0 ω) 1 ω := by
    funext ω
    exact profileP2Fun_sub_of_support β n T _ _ 1 A (hA ω) (hB ω) ω
  have heqS (ω : Disorder) := congrFun (heq S) ω
  simp_rw [heqS] at hsplit
  exact hsplit.trans (add_le_add
    (profile_future_mass_horizon_comparison β ha hb hnS hSN G hG) le_rfl)

/-- Heat-started lattice masses translate with the disorder. -/
theorem profile_lattice_heatMass_translate (β : ℝ) (a T : ℕ) (x : Site) (ω : Disorder) :
    smoothedP2Plane β a T x ω =
      smoothedP2Plane β a T 0 (fun p => ω (p.1, p.2 + x)) := by
  rw [← profileHeatMass_lattice β a T x ω, ← profileHeatMass_lattice β a T 0]
  simpa only [sub_zero, Pi.one_apply] using
    FutureProfiles.profileP2Fun_translate β a T x (srwKernel a) (fun _ => 1) ω

/-- The capped comparison of two heat-started lattice mass ratios has a
spatially invariant expectation. -/
theorem profile_lattice_ratio_cap_spatial (β : ℝ) (a b n T : ℕ) (x : Site) (M : ℝ) :
    (∫ ω, min |smoothedP2Plane β a T x ω / smoothedP2Plane β a n x ω -
      smoothedP2Plane β b T x ω / smoothedP2Plane β b n x ω| M ∂disorderLaw) =
    (∫ ω, min |smoothedP2Plane β a T 0 ω / smoothedP2Plane β a n 0 ω -
      smoothedP2Plane β b T 0 ω / smoothedP2Plane β b n 0 ω| M ∂disorderLaw) := by
  let F (ω : Disorder) := min |smoothedP2Plane β a T 0 ω / smoothedP2Plane β a n 0 ω -
    smoothedP2Plane β b T 0 ω / smoothedP2Plane β b n 0 ω| M
  have hF : Measurable F :=
    (((Polymer.measurable_smoothedP2Plane β a T 0).div
      (Polymer.measurable_smoothedP2Plane β a n 0)).sub
      ((Polymer.measurable_smoothedP2Plane β b T 0).div
        (Polymer.measurable_smoothedP2Plane β b n 0))).abs.min measurable_const
  have hm := FutureProfiles.measurePreserving_disorderShift x
  calc
    _ = ∫ ω, F (fun p => ω (p.1, p.2 + x)) ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [F, profile_lattice_heatMass_translate β _ _ x ω]
    _ = _ := by
      rw [← integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable, hm.map_eq]

/-- The past sigma-field is a sub-sigma-field of the full disorder space. -/
theorem profile_disorderPast_le (a : ℕ) :
    disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
  rw [← Gaussian.disorderBlock_zero a]
  exact Gaussian.disorderBlock_le 0 a

/-- Conditional annealing identifies the integrated future energy with the
squared future polymer on a past-measurable event. -/
theorem profile_setIntegral_polymer_sq_eq_energy (β : ℝ) {a b : ℕ}
    (hab : a ≤ b) (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2))
    (hXint : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast a] G) :
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw =
      ∫ ω in G, futureEnergy β a b (η ω) ∂disorderLaw := by
  have hCE := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
    hXmeas hXint
  have hCEeq : disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
      disorderPast a] =ᵐ[disorderLaw] fun ω => futureEnergy β a b (η ω) := by
    filter_upwards [hCE] with ω hω
    rw [hω, futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)]
  calc
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw =
        ∫ ω in G, disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
          disorderPast a] ω ∂disorderLaw := by
            simpa only [randomFlatProfilePolymer] using
              (setIntegral_condExp (profile_disorderPast_le a) hXint hG).symm
    _ = ∫ ω in G, futureEnergy β a b (η ω) ∂disorderLaw :=
      setIntegral_congr_ae ((profile_disorderPast_le a) G hG)
        (hCEeq.mono fun _ h _ => h)

/-- The open-corrector energy bound with decay strictly below one half.
The larger threshold on the geometric block ratio preserves every lattice
input while supplying the padding convention of the extension note. -/
theorem profile_openCorrector_energy_bound (A : ℝ) :
    ∃ ρ₀ θ : ℝ, 1 < ρ₀ ∧ 0 < θ ∧ θ < 1 / 2 ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁,
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ u s : ℕ, 1 ≤ u → u ≤ s → s + 2 ≤ blockCount N ρ →
        ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) u s,
            futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
              (openCorrector (criticalBeta ϑ N) (blockTime N ρ) u s ω) ∂disorderLaw ≤
          C * θ ^ (2 * (s - u)) / ((blockCount N ρ : ℝ) - u) := by
  obtain ⟨C₀K, ε, hε, hDiscrepancyStringInputA⟩ := Blocks.openDiscrepancyMass_sq_integral_le A
  let ρ₀ : ℝ := Real.exp (16 * ε ^ 2) + 2
  let θ : ℝ := 2 * ε / Real.sqrt (Real.log ρ₀)
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    nlinarith [Real.exp_pos (16 * ε ^ 2)]
  have hlogρ₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < 1 / 2 := by
    have hlog : 16 * ε ^ 2 < Real.log ρ₀ := by
      apply (Real.lt_log_iff_exp_lt (by dsimp [ρ₀]; positivity)).2
      dsimp only [ρ₀]
      linarith
    have hsq : (4 * ε) ^ 2 < (Real.sqrt (Real.log ρ₀)) ^ 2 := by
      rw [Real.sq_sqrt hlogρ₀.le]
      nlinarith only [hlog]
    have hroot : 4 * ε < Real.sqrt (Real.log ρ₀) := by
      nlinarith only [hsq, Real.sqrt_nonneg (Real.log ρ₀), hε]
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr hlogρ₀)).mpr
    change 2 * ε < (1 / 2 : ℝ) * Real.sqrt (Real.log ρ₀)
    linarith only [hroot]
  refine ⟨ρ₀, θ, hρ₀, hθpos, hθlt, ?_⟩
  intro ρ₁
  refine ⟨4 * C₀K ^ 2, ?_⟩
  intro ρ hρmem
  have hρ : Real.exp (ε ^ 2) < ρ := by
    have hexpMono : Real.exp (ε ^ 2) ≤ Real.exp (16 * ε ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ε])
    have hexpAdd : Real.exp (16 * ε ^ 2) < ρ₀ := by
      dsimp [ρ₀]
      exact lt_add_of_pos_right _ (by norm_num)
    exact (hexpMono.trans_lt hexpAdd).trans_le hρmem.1
  have hρpos : 0 < ρ := by linarith [hρmem.1]
  have hlogρ : Real.log ρ₀ ≤ Real.log ρ := Real.log_le_log (by linarith) hρmem.1
  have hθρ : 2 * (ε / Real.sqrt (Real.log ρ)) ≤ θ := by
    dsimp [θ]
    have hroot : Real.sqrt (Real.log ρ₀) ≤ Real.sqrt (Real.log ρ) :=
      Real.sqrt_le_sqrt hlogρ
    have hroot0 : 0 < Real.sqrt (Real.log ρ₀) := Real.sqrt_pos.2 hlogρ₀
    have hrootρ : 0 < Real.sqrt (Real.log ρ) :=
      Real.sqrt_pos.2 (lt_of_lt_of_le hlogρ₀ hlogρ)
    have hfrac : ε / Real.sqrt (Real.log ρ) ≤ ε / Real.sqrt (Real.log ρ₀) :=
      div_le_div_of_nonneg_left hε.le hroot0 hroot
    calc
      2 * (ε / Real.sqrt (Real.log ρ)) ≤ 2 * (ε / Real.sqrt (Real.log ρ₀)) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = 2 * ε / Real.sqrt (Real.log ρ₀) := by ring
  have hKevent := hDiscrepancyStringInputA ρ hρ
  have hρstrict : 1 < ρ := lt_of_lt_of_le hρ₀ hρmem.1
  filter_upwards [hKevent, blockTime_monotone hρstrict,
      eventually_ge_atTop 1] with N hKN hmono hKpos
  classical
  intro ϑ hϑ u s hu hus hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let G := blockGoodSet β t u s
  let η : Disorder → Site → ℝ := fun ω y => if ω ∈ G then openCorrector β t u s ω y else 0
  let S := openCorrectorNumeratorSupport t u s
  have hKnat : 1 ≤ blockCount N ρ := by unfold blockCount; omega
  have hmonoUS : Monotone t := hmono
  have htS : t s ≤ N := by
    have hle := hmonoUS (show s ≤ s + 2 by omega)
    have hleK := hmonoUS hsK
    have hterminal : t (blockCount N ρ) = N := by
      simp [t, blockTime, Nat.ne_of_gt (by omega : 0 < blockCount N ρ)]
    rw [hterminal] at hleK
    exact hle.trans hleK
  have htStart : t (u - 1) ≤ t s := hmonoUS (by omega)
  have htU : t (u - 1) ≤ t s := htStart
  have hGmeas : MeasurableSet[disorderPast (t s)] G := by
    let : MeasurableSpace Disorder := disorderPast (t s)
    have hblock (i : ℕ) (hi : i ∈ Finset.Icc u s) :
        Measurable[disorderPast (t s)] (blockMass β t i) := by
      have hti : t i ≤ t s := hmonoUS (Finset.mem_Icc.mp hi).2
      exact (measurable_blockMass β t i).mono
        (Gaussian.disorderBlock_mono (Nat.zero_le _) hti) le_rfl
    have h : MeasurableSet[disorderPast (t s)]
        (⋂ i ∈ Finset.Icc u s, {ω | |blockMass β t i ω - 1| ≤ 1 / 2}) := by
      apply Finset.measurableSet_biInter
      intro i hi
      have habs : Measurable[disorderPast (t s)]
          (fun ω => |blockMass β t i ω - 1|) :=
        (hblock i hi).sub measurable_const |>.abs
      exact MeasurableSet.preimage measurableSet_Iic habs
    convert h using 1
    ext ω
    simp [G, blockGoodSet]
  have hGmeas' : MeasurableSet[disorderPast (t s)] G := hGmeas
  have hηsupport : ∀ ω y, y ∉ S → η ω y = 0 := by
    intro ω y hy
    by_cases hω : ω ∈ G
    · simp only [η, hω, ite_true]
      unfold openCorrector
      rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hy, zero_div]
    · simp [η, hω]
  have hOpenMeas (y : Site) : Measurable[disorderPast (t s)]
      (fun ω => openCorrector β t u s ω y) :=
    measurable_openCorrector_on_past β t hmonoUS u s hu hus y
  have hηMeas (y : Site) : Measurable[disorderPast (t s)] (η · y) := by
    change Measurable[disorderPast (t s)]
      (fun ω => if ω ∈ G then openCorrector β t u s ω y else 0)
    exact Measurable.ite hGmeas (hOpenMeas y) measurable_const
  have hXmeas : Measurable (fun ω => randomFlatProfilePolymer β (t s) N η ω ^ 2) := by
    have hprofile := measurable_randomTerminalProfilePolymer β (t s) N S η (fun _ => 1)
      hηsupport hηMeas
    simpa only [randomFlatProfilePolymer, randomTerminalProfilePolymer] using hprofile.pow_const 2
  have hprofileEq (ω : Disorder) : randomFlatProfilePolymer β (t s) N η ω =
      if ω ∈ G then openDiscrepancyMass β t N u (s + 1) ω /
          ∏ i ∈ Finset.Icc u s, blockMass β t i ω else 0 := by
    by_cases hω : ω ∈ G
    · have heta : η ω = openCorrector β t u s ω := by
        funext y
        simp [η, hω]
      rw [randomFlatProfilePolymer, heta]
      rw [ite_eq_left hω]
      exact profileP2Fun_openCorrector_eq β hmonoUS N hu hus htS ω
    · simp [randomFlatProfilePolymer, η, hω, profileP2Fun]
  have hdenlower (ω : Disorder) (hω : ω ∈ G) :
      (1 / 2 : ℝ) ^ (s - u + 1) ≤ ∏ i ∈ Finset.Icc u s, blockMass β t i ω := by
    have hfactor (i : ℕ) (hi : i ∈ Finset.Icc u s) :
        (1 / 2 : ℝ) ≤ blockMass β t i ω := by
      have hGprop : ∀ i ∈ Finset.Icc u s, |blockMass β t i ω - 1| ≤ 1 / 2 := by
        simpa [G, blockGoodSet] using hω
      have hiω := hGprop i hi
      have := (abs_le.mp hiω).1
      linarith
    calc
      (1 / 2 : ℝ) ^ (s - u + 1) = ∏ _i ∈ Finset.Icc u s, (1 / 2 : ℝ) := by
        rw [Finset.prod_const]
        have hcard : (Finset.Icc u s).card = s - u + 1 := by
          simp [Nat.card_Icc]
          omega
        rw [hcard]
      _ ≤ ∏ i ∈ Finset.Icc u s, blockMass β t i ω := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        · intro i hi
          exact hfactor i hi
  have hproductpos (ω : Disorder) : 0 < ∏ i ∈ Finset.Icc u s, blockMass β t i ω :=
    Finset.prod_pos fun i hi => blockMass_pos β t i ω
  have hratioBound (ω : Disorder) (hω : ω ∈ G) :
      |openDiscrepancyMass β t N u (s + 1) ω /
        ∏ i ∈ Finset.Icc u s, blockMass β t i ω| ^ 2 ≤
          (4 : ℝ) ^ (s - u + 1) * openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
    have hprod := hdenlower ω hω
    have hprodpos := hproductpos ω
    have hinv : (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ≤
        (2 : ℝ) ^ (s - u + 1) := by
      have hbasepos : 0 < (1 / 2 : ℝ) ^ (s - u + 1) := pow_pos (by norm_num) _
      have hrecip := (inv_le_inv₀ hprodpos hbasepos).2 hprod
      have hbaseinv : ((1 / 2 : ℝ) ^ (s - u + 1))⁻¹ =
          (2 : ℝ) ^ (s - u + 1) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
      simpa [hbaseinv] using hrecip
    have hsq : |openDiscrepancyMass β t N u (s + 1) ω /
        ∏ i ∈ Finset.Icc u s, blockMass β t i ω| ^ 2 =
          openDiscrepancyMass β t N u (s + 1) ω ^ 2 *
            (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ^ 2 := by
      rw [sq_abs, div_eq_mul_inv, mul_pow]
    rw [hsq]
    have hinvnonneg : 0 ≤ (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ := inv_nonneg.mpr hprodpos.le
    have hsquare : (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ^ 2 ≤
        ((2 : ℝ) ^ (s - u + 1)) ^ 2 :=
      (sq_le_sq₀ hinvnonneg (by positivity)).2 hinv
    calc
      _ ≤ openDiscrepancyMass β t N u (s + 1) ω ^ 2 *
          ((2 : ℝ) ^ (s - u + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = (4 : ℝ) ^ (s - u + 1) * openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
            have hp : ((2 : ℝ) ^ (s - u + 1)) ^ 2 =
                (4 : ℝ) ^ (s - u + 1) := by
              calc
                _ = (2 : ℝ) ^ ((s - u + 1) * 2) := by rw [← pow_mul]
                _ = (2 : ℝ) ^ (2 * (s - u + 1)) := by congr 1; omega
                _ = ((2 : ℝ) ^ 2) ^ (s - u + 1) := by rw [pow_mul]
                _ = _ := by norm_num
            rw [hp, mul_comm]
  have hXbound (ω : Disorder) :
      ‖randomFlatProfilePolymer β (t s) N η ω ^ 2‖ ≤
        (4 : ℝ) ^ (s - u + 1) *
          openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
    by_cases hω : ω ∈ G
    · rw [hprofileEq ω, ite_eq_left hω]
      have hbound := hratioBound ω hω
      have hnormX : ‖(openDiscrepancyMass β t N u (s + 1) ω /
          ∏ i ∈ Finset.Icc u s, blockMass β t i ω) ^ 2‖ =
          |openDiscrepancyMass β t N u (s + 1) ω /
            ∏ i ∈ Finset.Icc u s, blockMass β t i ω| ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (sq_abs _).symm
      rw [hnormX]
      exact hbound
    · rw [hprofileEq ω, ite_eq_right hω]
      have hnonneg : 0 ≤ (4 : ℝ) ^ (s - u + 1) *
          openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by positivity
      have hmassnonneg : 0 ≤ openDiscrepancyMass β t N u (s + 1) ω ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hmassnonneg]
  have hOpenInt : Integrable
      (fun ω => openDiscrepancyMass β t N u (s + 1) ω ^ 2) disorderLaw := by
    rw [show (fun ω => openDiscrepancyMass β t N u (s + 1) ω ^ 2) =
        (fun ω => closedDiscrepancy β (Function.update t (s + 1) N) u (s + 1) ω ^ 2) by
      funext ω
      exact congrArg (fun z : ℝ => z ^ 2)
        (openDiscrepancyMass_eq_closedDiscrepancy_update β t N hu
          (by omega : u ≤ s + 1) ω)]
    exact integrable_sq_closedDiscrepancy β (Function.update t (s + 1) N) u (s + 1)
  have hXint : Integrable
      (fun ω => randomFlatProfilePolymer β (t s) N η ω ^ 2) disorderLaw :=
    (hOpenInt.const_mul ((4 : ℝ) ^ (s - u + 1))).mono' hXmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hXbound ω)
  have henergyEq := profile_setIntegral_polymer_sq_eq_energy β
    (by omega) η S hηsupport hηMeas hXmeas hXint G hGmeas'
  have hDiscrepancyStringInputN := hKN ϑ hϑ u (s + 1) hu (by omega) (by omega)
  have hDiscrepancyStringInputN' : ∫ ω, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw ≤
      (C₀K * (ε / Real.sqrt (Real.log ρ)) ^ (s - u)) ^ 2 /
        ((blockCount N ρ : ℝ) - u) := by
    have hexp : s + 1 - u - 1 = s - u := by omega
    simpa only [β, t, hexp] using hDiscrepancyStringInputN
  have hdenom := by
    have hKlower : 0 < (blockCount N ρ : ℝ) - u := by
      have hnat : u < blockCount N ρ := by omega
      rw [← Nat.cast_sub (Nat.le_of_lt hnat)]
      exact_mod_cast Nat.sub_pos_of_lt hnat
    have hθpow : (2 * (ε / Real.sqrt (Real.log ρ))) ^ (2 * (s - u)) ≤
        θ ^ (2 * (s - u)) := by
      exact pow_le_pow_left₀ (by positivity) hθρ (2 * (s - u))
    have hGmeasGlobal := profile_disorderPast_le (t s) G hGmeas'
    calc
      ∫ ω in G, futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw
          = ∫ ω in G, futureEnergy β (t s) N (η ω) ∂disorderLaw := by
              apply setIntegral_congr_ae hGmeasGlobal
              filter_upwards [] with ω hω
              have heta : η ω = openCorrector β t u s ω := by
                funext y
                simp [η, hω]
              rw [heta]
      _ = ∫ ω in G, profileP2Fun β (t s) N (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw :=
            henergyEq.symm
      _ = ∫ ω in G, randomFlatProfilePolymer β (t s) N η ω ^ 2 ∂disorderLaw := by
            simp only [randomFlatProfilePolymer]
      _ ≤ (4 : ℝ) ^ (s - u + 1) *
            ∫ ω in G, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
              calc
                _ ≤ ∫ ω in G,
                    (4 : ℝ) ^ (s - u + 1) *
                      openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
                    apply setIntegral_mono_on hXint.integrableOn
                      (hOpenInt.const_mul ((4 : ℝ) ^ (s - u + 1))).integrableOn
                      hGmeasGlobal
                    intro ω hω
                    have h := hratioBound ω hω
                    rw [hprofileEq ω, ite_eq_left hω]
                    simpa [Real.norm_eq_abs, sq_abs] using h
                _ = (4 : ℝ) ^ (s - u + 1) *
                    ∫ ω in G, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
                      rw [integral_const_mul]
      _ ≤ (4 : ℝ) ^ (s - u + 1) *
            ∫ ω, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
              exact mul_le_mul_of_nonneg_left
                (setIntegral_le_integral hOpenInt
                  (Filter.Eventually.of_forall fun ω => sq_nonneg _)) (by positivity)
      _ ≤ (4 : ℝ) ^ (s - u + 1) *
            ((C₀K * (ε / Real.sqrt (Real.log ρ)) ^ (s - u)) ^ 2 /
              ((blockCount N ρ : ℝ) - u)) := by
              exact mul_le_mul_of_nonneg_left hDiscrepancyStringInputN' (by positivity)
      _ = 4 * C₀K ^ 2 *
            (2 * (ε / Real.sqrt (Real.log ρ))) ^ (2 * (s - u)) /
              ((blockCount N ρ : ℝ) - u) := by
              let d : ℕ := s - u
              let e : ℝ := ε / Real.sqrt (Real.log ρ)
              have hd : d = s - u := rfl
              have he : e = ε / Real.sqrt (Real.log ρ) := rfl
              have hpow : (C₀K * e ^ d) ^ 2 = C₀K ^ 2 * e ^ (2 * d) := by
                rw [mul_pow, ← pow_mul, Nat.mul_comm]
              have hdouble : (2 * e) ^ (2 * d) = 4 ^ d * e ^ (2 * d) := by
                rw [mul_pow, pow_mul]
                norm_num
              rw [show s - u + 1 = d + 1 by simp [d]]
              rw [pow_succ, hpow, hdouble]
              rw [he]
              ring
      _ ≤ 4 * C₀K ^ 2 * θ ^ (2 * (s - u)) /
            ((blockCount N ρ : ℝ) - u) := by
              apply div_le_div_of_nonneg_right _ hKlower.le
              apply mul_le_mul_of_nonneg_left hθpow
              positivity
  exact hdenom


/-- A block-ratio increment only involves closed intervals ending at that block. -/
theorem blockRatio_increment_eq (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {r v : ℕ} (hr : 1 ≤ r) (hrv : r ≤ v) (ω : Disorder) :
    blockRatio β t r v ω - blockRatio β t r (v - 1) ω =
      ∑ u ∈ Finset.Ico r v, blockRatio β t r (u - 1) ω *
        (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω) := by
  rcases hrv.eq_or_lt with h | h
  · subst v
    rw [blockRatio_self, blockRatio_empty β t r hr, Finset.Ico_self, Finset.sum_empty, sub_self]
  · have hset : Finset.Icc r (v - 1) = Finset.Ico r v := by
      ext u
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [blockRatio_recurrence β t ht r v hr h ω, hset, add_sub_cancel_left]

/-- Telescoping form of the ratio difference. Unlike a bound on `R - 1`,
this isolates only the observation blocks and is uniform in the earlier prefix. -/
theorem blockRatio_sub_eq_sum_increments (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {r l j : ℕ} (hr : 1 ≤ r) (hrl : r ≤ l) (hlj : l ≤ j) (ω : Disorder) :
    blockRatio β t r j ω - blockRatio β t r (l - 1) ω =
      ∑ v ∈ Finset.Icc l j, ∑ u ∈ Finset.Ico r v, blockRatio β t r (u - 1) ω *
        (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω) := by
  have htel : (∑ v ∈ Finset.Icc l j,
      (blockRatio β t r v ω - blockRatio β t r (v - 1) ω)) =
      blockRatio β t r j ω - blockRatio β t r (l - 1) ω := by
    simpa only [Nat.add_sub_cancel] using
      (Finset.sum_Icc_sub hlj (fun v => blockRatio β t r (v - 1) ω))
  rw [← htel]
  apply Finset.sum_congr rfl
  intro v hv
  exact blockRatio_increment_eq β t ht hr (hrl.trans (Finset.mem_Icc.mp hv).1) ω





end Critical2DKPZ.Extensions.GffTangent

end
