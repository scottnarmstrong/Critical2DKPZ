/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Provider.EhrhardTypeCharacterization
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
public import Critical2DKPZ.RandomMeasure.GeneralRandom
public import Critical2DKPZ.SHF.Symmetries.LatticeReversal
public import Critical2DKPZ.PolymerCalculus.LogSumExp
public import Critical2DKPZ.PolymerCalculus.BoundarySliceDisorder
public import Critical2DKPZ.Analysis.Lattice.Basic
public import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
import Mathlib.Tactic

/-! # Ehrhard type of the regularized critical KPZ field -/

@[expose] public section

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.Assembly

open Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Limit

/-- The weight of the path pair `r = (u, s)` in the finite-sum form of the lattice profile. -/
private def latWeight (β : ℝ) (a b m : ℕ) (x0 : Site) (f : Site → ℝ)
    (r : (Fin m → Fin 4) × (Fin (b - a) → Fin 4)) : ℝ :=
  (4 : ℝ)⁻¹ ^ m * (4 : ℝ)⁻¹ ^ (b - a) * Real.exp (-(((b - a : ℕ) : ℝ) * β ^ 2 / 2)) *
    f (walkPosition (x0 + walkPosition 0 r.1 m) r.2 (b - a))

/-- The coordinates visited by the path pair `r` at times `a + 1, …, b`. -/
private def latCoord (a b m : ℕ) (x0 : Site) (r : (Fin m → Fin 4) × (Fin (b - a) → Fin 4))
    (j : ℕ) : ℕ × Site :=
  (a + j, walkPosition (x0 + walkPosition 0 r.1 m) r.2 j)

/-- The linear form of the disorder attached to the path pair `r`. -/
private def latLin (β : ℝ) (a b m : ℕ) (x0 : Site)
    (r : (Fin m → Fin 4) × (Fin (b - a) → Fin 4)) (ω : Disorder) : ℝ :=
  β * ∑ j ∈ Finset.Icc 1 (b - a), ω (latCoord a b m x0 r j)

/-- The lattice profile is a finite weighted sum of exponentials of linear forms of the
disorder. -/
private theorem profile_eq_sum (β : ℝ) (a b m : ℕ) (x0 : Site) (f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m (w - x0)) f ω =
      ∑ r : (Fin m → Fin 4) × (Fin (b - a) → Fin 4),
        latWeight β a b m x0 f r * Real.exp (latLin β a b m x0 r ω) := by
  classical
  unfold profileP2Fun
  have hin : ∀ w : Site, (∑' z : Site, pointToPoint β a (b - a) w z ω * f z) =
      ∑ s : Fin (b - a) → Fin 4, (4 : ℝ)⁻¹ ^ (b - a) *
        Real.exp (∑ j ∈ Finset.Icc 1 (b - a), (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2)) *
          f (walkPosition w s (b - a)) := by
    intro w
    unfold pointToPoint
    simp_rw [Finset.sum_mul]
    rw [Summable.tsum_finsetSum]
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [tsum_eq_single (walkPosition w s (b - a))]
      · simp
      · intro z hz
        simp [Ne.symm hz]
    · intro s _
      refine summable_of_ne_finset_zero (s := {walkPosition w s (b - a)}) fun z hz => ?_
      have : walkPosition w s (b - a) ≠ z := fun h => hz (by simp [h])
      simp [this]
  simp_rw [hin]
  unfold srwKernel
  simp_rw [Finset.sum_mul]
  rw [Summable.tsum_finsetSum]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tsum_eq_single (x0 + walkPosition 0 u m)]
    · have hc : walkPosition 0 u m = x0 + walkPosition 0 u m - x0 := by abel
      have h1 : (if walkPosition 0 u m = x0 + walkPosition 0 u m - x0 then (1 : ℝ) else 0) = 1 :=
        by
          split_ifs
          rfl
      rw [h1, mul_one]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hexp : Real.exp (∑ j ∈ Finset.Icc 1 (b - a), (β * ω (a + j, walkPosition
          (x0 + walkPosition 0 u m) s j) - β ^ 2 / 2)) =
          Real.exp (-(((b - a : ℕ) : ℝ) * β ^ 2 / 2)) * Real.exp (latLin β a b m x0 (u, s) ω) := by
        rw [← Real.exp_add, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
        unfold latLin latCoord
        rw [← Finset.mul_sum]
        congr 1
        simp only [Nat.add_sub_cancel, nsmul_eq_mul]
        ring
      unfold latWeight
      simp only [hexp]
      ring
    · intro w hw
      have : walkPosition 0 u m ≠ w - x0 := fun h => hw (by rw [h]; abel)
      simp [this]
  · intro u _
    refine summable_of_ne_finset_zero (s := {x0 + walkPosition 0 u m}) fun w hw => ?_
    have : walkPosition 0 u m ≠ w - x0 := fun h => hw (by rw [Finset.mem_singleton, h]; abel)
    simp [this]

/-- The weights of the lattice profile are nonnegative when the final profile is. -/
private theorem latWeight_nonneg (β : ℝ) (a b m : ℕ) (x0 : Site) {f : Site → ℝ}
    (hf : ∀ z, 0 ≤ f z) (r : (Fin m → Fin 4) × (Fin (b - a) → Fin 4)) :
    0 ≤ latWeight β a b m x0 f r := by
  unfold latWeight
  exact mul_nonneg (by positivity) (hf _)

/-- The linear form attached to a path pair is convex (indeed linear) in the disorder. -/
private theorem convexOn_latLin (β : ℝ) (a b m : ℕ) (x0 : Site)
    (r : (Fin m → Fin 4) × (Fin (b - a) → Fin 4)) :
    ConvexOn ℝ Set.univ (fun ω : Disorder => latLin β a b m x0 r ω) := by
  refine ⟨convex_univ, fun ω _ ω' _ s t _ _ _ => le_of_eq ?_⟩
  simp only [latLin, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- The logarithm of the lattice profile is a convex function of the disorder. -/
private theorem convexOn_log_profile (β : ℝ) (a b m : ℕ) (x0 : Site) {f : Site → ℝ}
    (hf : ∀ z, 0 ≤ f z) :
    ConvexOn ℝ Set.univ (fun ω : Disorder =>
      Real.log (profileP2Fun β a b (fun w => srwKernel m (w - x0)) f ω)) := by
  have heq : (fun ω : Disorder =>
      Real.log (profileP2Fun β a b (fun w => srwKernel m (w - x0)) f ω)) = fun ω =>
      Real.log (∑ r : (Fin m → Fin 4) × (Fin (b - a) → Fin 4),
        latWeight β a b m x0 f r * Real.exp (latLin β a b m x0 r ω)) :=
    funext fun ω => by rw [profile_eq_sum]
  rw [heq]
  by_cases hpos : ∃ r, 0 < latWeight β a b m x0 f r
  · exact PolymerCalculus.convexOn_log_weighted_exp_sum convex_univ
      (latWeight_nonneg β a b m x0 hf) hpos (convexOn_latLin β a b m x0)
  · push Not at hpos
    have h0 : ∀ r, latWeight β a b m x0 f r = 0 := fun r =>
      le_antisymm (hpos r) (latWeight_nonneg β a b m x0 hf r)
    simp only [h0, zero_mul, Finset.sum_const_zero, Real.log_zero]
    exact convexOn_const 0 convex_univ

/-- Lattice points of a bounded set of the plane lie in a finite box of sites. -/
private theorem latticePoint_mem_box (N : ℕ) {R : ℝ} {x : Plane} (hx : ‖x‖ ≤ R) :
    latticePoint N x ∈ Set.pi Set.univ
      (fun _ : Fin 2 => Set.Icc (-⌈Real.sqrt (N / 2) * R + 1⌉) ⌈Real.sqrt (N / 2) * R + 1⌉) := by
  intro i _
  set y : Plane := Real.sqrt (N / 2) • x with hy
  have hyn : ‖y‖ ≤ Real.sqrt (N / 2) * R := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)
  have h1 := norm_sub_nearestEven_le_one y
  have hc1 : |y i - (latticePoint N x i : ℝ)| ≤ 1 := by
    have : |(y - siteToPlane (nearestEven y)) i| ≤ ‖y - siteToPlane (nearestEven y)‖ := by
      simpa using PiLp.norm_apply_le (y - siteToPlane (nearestEven y)) i
    simpa [siteToPlane, latticePoint, hy] using this.trans h1
  have hc2 : |y i| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y i
  have h3 : |(latticePoint N x i : ℝ)| ≤ ⌈Real.sqrt (N / 2) * R + 1⌉ := by
    have : |(latticePoint N x i : ℝ)| ≤ |y i| + |y i - (latticePoint N x i : ℝ)| := by
      calc |(latticePoint N x i : ℝ)| = |y i - (y i - (latticePoint N x i : ℝ))| := by ring_nf
        _ ≤ _ := abs_sub _ _
    exact (this.trans (by linarith)).trans (Int.le_ceil _)
  rw [abs_le] at h3
  constructor
  · exact_mod_cast h3.1
  · exact_mod_cast h3.2

/-- A finite set of coordinates containing every coordinate visited from a finite set of
starting sites. -/
private theorem exists_coordFinset (a b m : ℕ) {Λ : Set Site} (hΛ : Λ.Finite) :
    ∃ S : Finset (ℕ × Site), ∀ x0 ∈ Λ, ∀ r, ∀ j ∈ Finset.Icc 1 (b - a),
      latCoord a b m x0 r j ∈ S := by
  have hfin : Set.Finite ((fun p : Site × ((Fin m → Fin 4) × (Fin (b - a) → Fin 4)) × ℕ =>
      latCoord a b m p.1 p.2.1 p.2.2) ''
        (Λ ×ˢ (Set.univ ×ˢ (Finset.Icc 1 (b - a) : Set ℕ)))) :=
    (hΛ.prod (Set.finite_univ.prod (Finset.finite_toSet _))).image _
  refine ⟨hfin.toFinset, fun x0 hx0 r j hj => ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨(x0, r, j), ⟨hx0, Set.mem_univ _, by simpa using hj⟩, rfl⟩

/-- A compactly supported test function times a function of the lattice point is integrable,
when the lattice points of the support lie in a finite set. -/
private theorem integrable_mul_latticePoint (N : ℕ) (φ : TestFn) {Λ : Set Site}
    (hΛ : Λ.Finite) (hsupp : ∀ x, φ x ≠ 0 → latticePoint N x ∈ Λ) (g : Site → ℝ) :
    Integrable (fun x => φ x * g (latticePoint N x)) := by
  set M : ℝ := ∑ z ∈ hΛ.toFinset, |g z| with hM
  have hφ : Integrable (fun x => |φ x| * M) :=
    (φ.continuous.abs.integrable_of_hasCompactSupport φ.hasCompactSupport.abs).mul_const M
  refine hφ.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (φ.continuous.measurable.mul
      ((measurable_of_countable g).comp (measurable_latticePoint N))).aestronglyMeasurable
  · by_cases h : φ x = 0
    · simp [h, hM]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact Finset.single_le_sum (f := fun z => |g z|) (fun _ _ => abs_nonneg _)
        ((hΛ.mem_toFinset).2 (hsupp x h))

/-- The tested lattice log-field `∫ φ · log Z` of the polymer with a nonnegative
terminal profile and a nonnegative test function, shifted by a constant, has Ehrhard-type law:
it is a convex function of finitely many Gaussian disorder coordinates. -/
private theorem lattice_field_ehrhard (β : ℝ) (a b m N : ℕ) (f : Site → ℝ)
    (hf : ∀ z, 0 ≤ f z) (φ : TestFn) (hφ : ∀ x, 0 ≤ φ x) (c : ℝ) :
    IsEhrhardType (disorderLaw.map (fun ω : Disorder =>
      (∫ x, φ x * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - latticePoint N x)) f ω)) - c)) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x, φ x ≠ 0 → ‖x‖ ≤ R := by
    obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun x hx => by simpa using hR (subset_tsupport _ (Function.mem_support.2 hx))⟩
  set Λ : Set Site := Set.pi Set.univ
    (fun _ : Fin 2 => Set.Icc (-⌈Real.sqrt (N / 2) * R + 1⌉) ⌈Real.sqrt (N / 2) * R + 1⌉)
    with hΛdef
  have hΛ : Λ.Finite := Set.Finite.pi fun _ => Set.finite_Icc _ _
  have hsupp : ∀ x, φ x ≠ 0 → latticePoint N x ∈ Λ := fun x hx =>
    latticePoint_mem_box N (hR x hx)
  obtain ⟨S, hS⟩ := exists_coordFinset a b m hΛ
  let e : Fin S.card → ℕ × Site := fun i => (S.equivFin.symm i).1
  have he : Function.Injective e := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  let ext : EuclideanSpace ℝ (Fin S.card) → Disorder := fun y q =>
    if h : q ∈ S then y (S.equivFin ⟨q, h⟩) else 0
  have hext : ∀ ω q, q ∈ S → ext (PolymerCalculus.disorderSliceCoordinates e ω) q = ω q := by
    intro ω q hq
    simp [ext, hq, PolymerCalculus.disorderSliceCoordinates, e]
  have hext_lin : ∀ (y z : EuclideanSpace ℝ (Fin S.card)) (s t : ℝ),
      ext (s • y + t • z) = s • ext y + t • ext z := by
    intro y z s t
    funext q
    by_cases hq : q ∈ S <;> simp [ext, hq]
  have hKcong : ∀ x0 ∈ Λ, ∀ ω ω' : Disorder, (∀ q ∈ S, ω q = ω' q) →
      profileP2Fun β a b (fun w => srwKernel m (w - x0)) f ω =
        profileP2Fun β a b (fun w => srwKernel m (w - x0)) f ω' := by
    intro x0 hx0 ω ω' h
    rw [profile_eq_sum, profile_eq_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold latLin
    congr 3
    exact Finset.sum_congr rfl fun j hj => h _ (hS x0 hx0 r j hj)
  have hint : ∀ y : EuclideanSpace ℝ (Fin S.card), Integrable (fun x => φ x * Real.log
      (profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x)) f (ext y))) :=
    fun y => integrable_mul_latticePoint N φ hΛ hsupp
      (fun z => Real.log (profileP2Fun β a b (fun w => srwKernel m (w - z)) f (ext y)))
  let F : EuclideanSpace ℝ (Fin S.card) → ℝ := fun y =>
    (∫ x, φ x * Real.log (profileP2Fun β a b
      (fun w => srwKernel m (w - latticePoint N x)) f (ext y))) - c
  have hFconv : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, fun y _ z _ s t hs ht hst => ?_⟩
    simp only [smul_eq_mul, F]
    have hle : ∫ x, φ x * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - latticePoint N x)) f (ext (s • y + t • z))) ≤
        ∫ x, (s * (φ x * Real.log (profileP2Fun β a b
            (fun w => srwKernel m (w - latticePoint N x)) f (ext y))) +
          t * (φ x * Real.log (profileP2Fun β a b
            (fun w => srwKernel m (w - latticePoint N x)) f (ext z)))) := by
      refine integral_mono (hint _) (((hint y).const_mul s).add ((hint z).const_mul t))
        (fun x => ?_)
      have h := (convexOn_log_profile β a b m (latticePoint N x) hf).2 (Set.mem_univ (ext y))
        (Set.mem_univ (ext z)) hs ht hst
      simp only [smul_eq_mul] at h
      rw [hext_lin]
      calc _ ≤ φ x * (s * Real.log (profileP2Fun β a b
              (fun w => srwKernel m (w - latticePoint N x)) f (ext y)) +
            t * Real.log (profileP2Fun β a b
              (fun w => srwKernel m (w - latticePoint N x)) f (ext z))) :=
            mul_le_mul_of_nonneg_left h (hφ x)
        _ = _ := by ring
    rw [integral_add ((hint y).const_mul s) ((hint z).const_mul t), integral_const_mul,
      integral_const_mul] at hle
    have hc : (s + t) * c = c := by rw [hst, one_mul]
    nlinarith [hle, hc]
  have hFmeas : Measurable F := (continuousOn_univ.1 (hFconv.continuousOn isOpen_univ)).measurable
  have hfun : (fun ω : Disorder => (∫ x, φ x * Real.log (profileP2Fun β a b
      (fun w => srwKernel m (w - latticePoint N x)) f ω)) - c) =
      F ∘ PolymerCalculus.disorderSliceCoordinates e := by
    funext ω
    simp only [Function.comp, F]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : φ x = 0
    · simp [hx]
    · dsimp only
      rw [hKcong _ (hsupp x hx) _ _ (fun q hq => (hext ω q hq).symm)]
  have hlaw := PolymerCalculus.hasLaw_disorderSliceCoordinates e he
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable hFmeas.aemeasurable hlaw.aemeasurable,
    hlaw.map_eq]
  exact Provider.ehrhardType_convexGaussianImage _ F hFconv

/-- The flat centring constant `E log 𝒵_{t-δ}(1, g_δ)` of the regularized field. -/
private def ehrCen {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) : ℝ :=
  ∫ ω, Real.log (shfPairing Z 0 (t - δ) (fun _ => 1) (fun y => heatKernel δ y) ω) ∂P

/-- The tested log-field `∫ φ (log ∫ g_δ(p₁ - x) dμ - c)` of a measure on the plane pair,
with the heat kernel on the first coordinate. -/
private def ehrG (δ c : ℝ) (φ : TestFn) (μ : Measure (Plane × Plane)) : ℝ :=
  ∫ x, φ x * (Real.log (∫ p, heatKernel δ (p.1 - x) * 1 ∂μ) - c)

/-- The tested regularized field is `ehrG` of the swapped measure `Z 0 (t - δ) ω`. -/
private theorem regField_eq' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (φ : TestFn) (ω : Ω) :
    ∫ x, φ x * kpzRegularized P Z t δ 0 x ω =
      ehrG δ (ehrCen P Z t δ) φ ((Z 0 (t - δ) ω).map Prod.swap) := by
  unfold ehrG kpzRegularized ehrCen
  congr 1
  funext x
  congr 2
  have hm : Measurable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * 1) :=
    ((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul measurable_const
  rw [integral_map measurable_swap.aemeasurable hm.aestronglyMeasurable]
  congr 2
  simp [shfPairing]

/-- Almost sure local finiteness of a random measure passes to its law. -/
private theorem ae_locallyFinite_map' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure (Plane × Plane)) (hM : Measurable M)
    (h : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω)) :
    ∀ᵐ μ ∂(P.map M), IsLocallyFiniteMeasure μ := by
  have hS := RandomMeasure.measurableSet_isLocallyFiniteMeasure
    (CompactExhaustion.choice (Plane × Plane)) (id : Measure (Plane × Plane) → _) measurable_id
  exact (ae_map_iff hM.aemeasurable hS).2 h

/-- The tested regularized field is a.e. measurable. -/
private theorem aemeasurable_regField' (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzRegularized P Z t δ 0 x ω) P := by
  have hT : 0 < t - δ := sub_pos.2 hδt
  have hm : Measurable (Z 0 (t - δ)) := hZ.1 0 (t - δ) le_rfl hT
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure ((Z 0 (t - δ) ω).map Prod.swap) :=
    (hZ.2.1 0 (t - δ) le_rfl hT).mono fun ω h =>
      CovarianceKernel.locallyFinite_map_homeomorph (Homeomorph.prodComm Plane Plane) _ h.1
  have h := JointConvergence.aemeasurable_integral_log_heatPairing P
    (fun ω => (Z 0 (t - δ) ω).map Prod.swap)
    ((Measure.measurable_map _ measurable_swap).comp hm) hloc δ (ehrCen P Z t δ) hδ
    (fun _ => 1) φ measurable_const (fun _ => zero_le_one) φ.continuous.measurable
  exact h.congr (Eventually.of_forall fun ω => (regField_eq' P Z t δ φ ω).symm)

/-- The swapped measure `Z 0 T` has the same law as `Z 0 T` (reversal of a critical SHF). -/
private theorem law_swap_eq (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {T : ℝ} (hT : 0 < T) :
    P.map (fun ω => (Z 0 T ω).map Prod.swap) = P.map (Z 0 T) := by
  have h := SHF.Symmetries.isCriticalSHF_reverse_fdd ϑ P Z hZ T 1 (fun _ => 0) (fun _ => T)
    (fun _ => ⟨le_rfl, hT, le_rfl⟩)
  simp only [sub_self, sub_zero] at h
  have h1 := congrArg (fun ν => ν.map (fun m : Fin 1 → Measure (Plane × Plane) => m 0)) h
  have hm : Measurable (Z 0 T) := hZ.1 0 T le_rfl hT
  have hm' : Measurable (fun ω => (Z 0 T ω).map Prod.swap) :=
    (Measure.measurable_map _ measurable_swap).comp hm
  rw [Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval fun _ => hm'),
    Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval fun _ => hm)] at h1
  exact h1

/-- Pointwise comparison of a shifted heat kernel with the heat kernel at doubled time. -/
private theorem heat_shift_le {δ : ℝ} (hδ : 0 < δ) (x y : Plane) {R : ℝ} (hR : ‖x‖ ≤ R) :
    heatKernel δ (y - x) ≤ 2 * Real.exp (R ^ 2 / (2 * δ)) * heatKernel (2 * δ) y := by
  have hn : ‖y‖ ^ 2 ≤ 2 * ‖y - x‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
    have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
    have h2 : ‖y‖ ^ 2 ≤ (‖y - x‖ + ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖y - x‖ - ‖x‖)]
  have hR2 : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hexp : Real.exp (-‖y - x‖ ^ 2 / (2 * δ)) ≤
      Real.exp (R ^ 2 / (2 * δ)) * Real.exp (-‖y‖ ^ 2 / (2 * (2 * δ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e1 : -‖y - x‖ ^ 2 / (2 * δ) = -(‖y - x‖ ^ 2) * (1 / (2 * δ)) := by ring
    have e2 : R ^ 2 / (2 * δ) + -‖y‖ ^ 2 / (2 * (2 * δ)) =
        (R ^ 2 - ‖y‖ ^ 2 / 2) * (1 / (2 * δ)) := by field_simp; ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  have hc : (2 * Real.pi * δ)⁻¹ = 2 * (2 * Real.pi * (2 * δ))⁻¹ := by
    field_simp
  unfold heatKernel
  calc (2 * Real.pi * δ)⁻¹ * Real.exp (-‖y - x‖ ^ 2 / (2 * δ))
      ≤ (2 * Real.pi * δ)⁻¹ *
        (Real.exp (R ^ 2 / (2 * δ)) * Real.exp (-‖y‖ ^ 2 / (2 * (2 * δ)))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by rw [hc]; ring

/-- Integrability of the doubled heat pairing gives integrability of every shift. -/
private theorem integrable_heat_shift {μ : Measure (Plane × Plane)} {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * δ) p.1) μ) (x : Plane) :
    Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ := by
  refine (hint.const_mul (2 * Real.exp (‖x‖ ^ 2 / (2 * δ)))).mono'
    (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (heatKernel_nonneg hδ.le _)]
  exact heat_shift_le hδ x p.1 le_rfl

/-- The heat pairing with the first marginal is continuous in the centre. -/
private theorem continuous_heat_pairing {μ : Measure (Plane × Plane)} {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * δ) p.1) μ) :
    Continuous (fun x : Plane => ∫ p, heatKernel δ (p.1 - x) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hc : ContinuousOn (fun x : Plane => ∫ p, heatKernel δ (p.1 - x) ∂μ)
      (Metric.closedBall 0 (‖x0‖ + 1)) := by
    refine continuousOn_of_dominated
      (bound := fun p => 2 * Real.exp ((‖x0‖ + 1) ^ 2 / (2 * δ)) * heatKernel (2 * δ) p.1)
      ?_ ?_ ?_ ?_
    · intro x _
      exact ((continuous_heatKernel δ).comp
        (continuous_fst.sub continuous_const)).aestronglyMeasurable
    · intro x hx
      refine Eventually.of_forall fun p => ?_
      have hx' : ‖x‖ ≤ ‖x0‖ + 1 := by simpa using hx
      rw [Real.norm_of_nonneg (heatKernel_nonneg hδ.le _)]
      exact heat_shift_le hδ x p.1 hx'
    · exact hint.const_mul _
    · exact Eventually.of_forall fun p => ((continuous_heatKernel δ).comp
        (continuous_const.sub continuous_id)).continuousOn
  refine hc.continuousAt (Filter.mem_of_superset (Metric.ball_mem_nhds x0 one_pos) ?_)
  intro y hy
  have : ‖y - x0‖ < 1 := by simpa [dist_eq_norm] using hy
  have h1 : ‖y‖ ≤ ‖y - x0‖ + ‖x0‖ := by simpa using norm_add_le (y - x0) x0
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith

/-- A nonzero measure with integrable doubled heat pairing has positive heat pairings. -/
private theorem heat_pairing_pos {μ : Measure (Plane × Plane)} {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * δ) p.1) μ) (hμ : μ ≠ 0)
    (x : Plane) : 0 < ∫ p, heatKernel δ (p.1 - x) ∂μ := by
  have hi := integrable_heat_shift hδ hint x
  have hnn : 0 ≤ fun p : Plane × Plane => heatKernel δ (p.1 - x) :=
    fun p => heatKernel_nonneg hδ.le _
  rw [integral_pos_iff_support_of_nonneg hnn hi]
  have hs : Function.support (fun p : Plane × Plane => heatKernel δ (p.1 - x)) = Set.univ := by
    ext p
    simp [Function.mem_support, (heatKernel_pos hδ _).ne']
  rw [hs]
  exact Measure.measure_univ_pos.2 hμ

/-- On a good measure the tested log-field splits: `∫ φ (log A - c) = ∫ φ log A - c ∫ φ`. -/
private theorem ehrG_eq_of_good {μ : Measure (Plane × Plane)} {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * δ) p.1) μ) (hμ : μ ≠ 0)
    (c : ℝ) (φ : TestFn) :
    ehrG δ c φ μ = (∫ x, φ x * Real.log (∫ p, heatKernel δ (p.1 - x) ∂μ)) - c * ∫ x, φ x := by
  have hcont := continuous_heat_pairing hδ hint
  have hI : Integrable (fun x => φ x * Real.log (∫ p, heatKernel δ (p.1 - x) ∂μ)) :=
    (φ.continuous.mul (hcont.log fun x => (heat_pairing_pos hδ hint hμ x).ne')
      ).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hφ : Integrable (fun x => φ x) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  unfold ehrG
  simp only [mul_one, mul_sub]
  rw [integral_sub hI (hφ.mul_const c), integral_mul_const]
  ring

/-- Almost surely the doubled first-marginal heat pairing is integrable and the measure is
nonzero (the seventh conjunct: positivity of heat pairings). -/
private theorem good_event (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hsym : ShfSymmetriesAt ϑ P Z) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel (2 * δ) p.1) (Z 0 T ω) ∧
      Z 0 T ω ≠ 0 := by
  filter_upwards [(hsym.2.2.2.2.2.2 0 T (2 * δ) 0 0 le_rfl hT (by linarith)).1] with ω hω
  have hω' : 0 < ∫ p : Plane × Plane, heatKernel (2 * δ) p.1 ∂(Z 0 T ω) := by
    simpa [shfPairing] using hω
  refine ⟨?_, fun h => ?_⟩
  · by_contra hni
    rw [integral_undef hni] at hω'
    exact lt_irrefl _ hω'
  · rw [h, integral_zero_measure] at hω'
    exact lt_irrefl _ hω'

/-- Cell averages of a nonnegative function are nonnegative. -/
private theorem cellAverage_nonneg (N : ℕ) {u : Plane → ℝ} (hu : ∀ y, 0 ≤ u y) (z : Site) :
    0 ≤ cellAverage N u z :=
  mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (integral_nonneg fun y => hu y)

/-- The grid `δₙ = t / (n + 2)` lies in `(0, t)` and tends to `0⁺`. -/
private theorem grid_tendsto' (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => t / ((n : ℝ) + 2)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  · exact div_pos ht (by positivity)

/-- At a fixed positive width, the tested field `∫ φ · ℋ^{(δ)}_t(0, ·)` is
a.e. measurable and has Ehrhard-type law, for nonnegative `φ`. -/
theorem isEhrhardType_regularized_field_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (φ : TestFn) (hφ : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzRegularized P Z t δ 0 x ω) P ∧
      IsEhrhardType (P.map fun ω => ∫ x, φ x * kpzRegularized P Z t δ 0 x ω) := by
  have hT : 0 < t - δ := sub_pos.2 hδt
  refine ⟨aemeasurable_regField' ϑ P Z hZ hδ hδt φ, ?_⟩
  set c := ehrCen P Z t δ with hc
  set c' : ℝ := c * ∫ x, φ x with hc'
  have hm : Measurable (Z 0 (t - δ)) := hZ.1 0 (t - δ) le_rfl hT
  have hlocZ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z 0 (t - δ) ω) :=
    (hZ.2.1 0 (t - δ) le_rfl hT).mono fun ω h => h.1
  -- the lattice fields converge in law to the (unswapped) heat-start field.
  have hlim := hHeatStartLogFieldInput (t - δ) 1 (fun _ => 0) (fun _ => 0) (fun _ => δ) (fun _ => φ)
    (fun _ => ⟨le_rfl, hT, hδ⟩)
  have hlim' := hlim.continuous_comp (g := fun v : Fin 1 → ℝ => v 0 - c') (by fun_prop)
  have hE := Provider.ehrhardType_weakClosure _ _
    (hlim'.tendsto.comp (tendsto_add_atTop_nat 1)) (fun k =>
      lattice_field_ehrhard (criticalBeta ϑ (k + 1)) _ _ _ (k + 1) _
        (cellAverage_nonneg (k + 1) fun y => (Real.exp_pos _).le) φ hφ c')
  -- the limit field is `ehrG` of `Z 0 (t - δ)`, up to the centring.
  have hae : ∀ᵐ ω ∂P, ((fun v : Fin 1 → ℝ => v 0 - c') ∘ (fun ω (i : Fin 1) =>
      ∫ x, φ x * Real.log (shfPairing Z 0 (t - δ) (fun y => heatKernel δ (y - x))
        (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω))) ω =
      ehrG δ c φ (Z 0 (t - δ) ω) := by
    filter_upwards [good_event ϑ P Z hsym hT hδ] with ω hω
    rw [ehrG_eq_of_good hδ hω.1 hω.2]
    simp [shfPairing, hc']
  -- reversal of the law of the random measure.
  have hν := law_swap_eq ϑ P Z hZ hT
  have hGν : AEMeasurable (ehrG δ c φ) (P.map (Z 0 (t - δ))) :=
    JointConvergence.aemeasurable_integral_log_heatPairing (P.map (Z 0 (t - δ))) id
      measurable_id (ae_locallyFinite_map' P _ hm hlocZ) δ c hδ (fun _ => 1) φ
      measurable_const (fun _ => zero_le_one) φ.continuous.measurable
  have hsw : Measurable (fun ω => (Z 0 (t - δ) ω).map Prod.swap) :=
    (Measure.measurable_map _ measurable_swap).comp hm
  have hfwd : (fun ω => ∫ x, φ x * kpzRegularized P Z t δ 0 x ω) =
      ehrG δ c φ ∘ fun ω => (Z 0 (t - δ) ω).map Prod.swap :=
    funext fun ω => regField_eq' P Z t δ φ ω
  have hlaw : P.map (fun ω => ∫ x, φ x * kpzRegularized P Z t δ 0 x ω) =
      P.map ((fun v : Fin 1 → ℝ => v 0 - c') ∘ (fun ω (i : Fin 1) =>
        ∫ x, φ x * Real.log (shfPairing Z 0 (t - δ) (fun y => heatKernel δ (y - x))
          (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω))) := by
    rw [hfwd, ← AEMeasurable.map_map_of_aemeasurable (hν ▸ hGν) hsw.aemeasurable, hν,
      AEMeasurable.map_map_of_aemeasurable hGν hm.aemeasurable]
    exact Measure.map_congr (hae.mono fun ω h => h.symm)
  rw [hlaw]
  exact hE

/-- For flat initial data and a nonnegative smooth compact test, the KPZ pairing is
a.e. measurable and has an Ehrhard-type law, under heat-start convergence and SHF symmetries. -/
theorem criticalKPZ_isEhrhardType_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) (t : ℝ) (ht : 0 < t)
    (φ : TestFn) (hφ : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun ω => H t 0 ω φ) P ∧ IsEhrhardType (P.map (fun ω => H t 0 ω φ)) := by
  set u : ℕ → ℝ := fun n => t / ((n : ℝ) + 2) with hu
  have hu0 : ∀ n, 0 < u n := fun n => div_pos ht (by positivity)
  have hut : ∀ n, u n < t := fun n => by
    rw [hu]
    exact div_lt_self ht (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hseq : TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, φ x * kpzRegularized P Z t (u n) 0 x ω) atTop
      (fun ω => H t 0 ω φ) := fun ε hε => (hH t ht 0 φ ε hε).comp (grid_tendsto' t ht)
  have hmeas : ∀ n, AEMeasurable
      (fun ω => ∫ x, φ x * kpzRegularized P Z t (u n) 0 x ω) P := fun n =>
    aemeasurable_regField' ϑ P Z hZ (hu0 n) (hut n) φ
  refine ⟨hseq.aemeasurable hmeas, ?_⟩
  have hd := hseq.tendstoInDistribution hmeas
  exact Provider.ehrhardType_weakClosure _ _ hd.tendsto fun n =>
    (isEhrhardType_regularized_field_of ϑ P Z hZ hHeatStartLogFieldInput hsym (hu0 n) (hut n) φ hφ).2

end Critical2DKPZ.Assembly

end

end
