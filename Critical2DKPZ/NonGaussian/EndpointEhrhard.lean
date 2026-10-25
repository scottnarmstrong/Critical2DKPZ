/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointOne
public import Critical2DKPZ.NonGaussian.EndpointMeans
public import Critical2DKPZ.NonGaussian.EhrhardNormalization
public import Critical2DKPZ.Provider.EhrhardTypeCharacterization
public import Critical2DKPZ.SHF.Positivity.FinitePathEhrhard
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Ehrhard type for positive lattice averaged logarithmic fields -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.JointConvergence Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Limit
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.NonGaussian

private def endpointPathCoordinateSet {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) : Finset (ℕ × Site) :=
  PolymerCalculus.finitePathCoordinates a n w

private def endpointPathCoordinateMap {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) : Fin (endpointPathCoordinateSet a n w).card → ℕ × Site :=
  fun i => ((endpointPathCoordinateSet a n w).equivFin.symm i).val

private def endpointPathCoordinateVector {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) (ω : Disorder) :
    EuclideanSpace ℝ (Fin (endpointPathCoordinateSet a n w).card) :=
  PolymerCalculus.disorderSliceCoordinates (endpointPathCoordinateMap a n w) ω

private def endpointPathCoordinateExtension {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) :
    EuclideanSpace ℝ (Fin (endpointPathCoordinateSet a n w).card) →ₗ[ℝ] Disorder where
  toFun x := fun p => if hp : p ∈ endpointPathCoordinateSet a n w then
    x ((endpointPathCoordinateSet a n w).equivFin ⟨p, hp⟩) else 0
  map_add' x y := by
    funext p
    by_cases hp : p ∈ endpointPathCoordinateSet a n w <;> simp [hp, Pi.add_apply]
  map_smul' c x := by
    funext p
    by_cases hp : p ∈ endpointPathCoordinateSet a n w <;> simp [hp, smul_eq_mul]

private theorem endpointPathCoordinateExtension_vector_eq {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) (ω : Disorder) (p : ℕ × Site)
    (hp : p ∈ endpointPathCoordinateSet a n w) :
    endpointPathCoordinateExtension a n w (endpointPathCoordinateVector a n w ω) p = ω p := by
  change (if h : p ∈ endpointPathCoordinateSet a n w then
    endpointPathCoordinateVector a n w ω ((endpointPathCoordinateSet a n w).equivFin ⟨p, h⟩)
      else 0) = ω p
  simp [hp, endpointPathCoordinateVector, PolymerCalculus.disorderSliceCoordinates,
    endpointPathCoordinateMap]

/-- A nonnegative finite weighted sum of logarithmic path partition functions is a convex function
of a finite Gaussian vector and has an Ehrhard-type law. -/
theorem isEhrhardType_weighted_sum_log_finitePathMass
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (β : ℝ) (a n : ℕ) (w : ι → Site)
    {c : κ → ι × (Fin n → Fin 4) → ℝ} (weight : κ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hc : ∀ i p, 0 ≤ c i p)
    (hpos : ∀ i, ∃ p, 0 < c i p) :
    IsEhrhardType (disorderLaw.map fun ω =>
      ∑ i : κ, weight i * Real.log (PolymerCalculus.finitePathMass β a n w (c i) ω)) := by
  classical
  let S := endpointPathCoordinateSet a n w
  let π := endpointPathCoordinateVector a n w
  let L := endpointPathCoordinateExtension a n w
  let F : κ → Disorder → ℝ := fun i ω =>
    Real.log (PolymerCalculus.finitePathMass β a n w (c i) ω)
  let Fv : κ → EuclideanSpace ℝ (Fin S.card) → ℝ := fun i x => F i (L x)
  let H : EuclideanSpace ℝ (Fin S.card) → ℝ := fun x =>
    ∑ i : κ, weight i * Fv i x
  have he : Function.Injective (endpointPathCoordinateMap a n w) := by
    intro i j hij
    have hsub : S.equivFin.symm i = S.equivFin.symm j := Subtype.ext hij
    exact S.equivFin.symm.injective hsub
  have hπlaw : HasLaw π (stdGaussian (EuclideanSpace ℝ (Fin S.card))) disorderLaw := by
    change HasLaw (PolymerCalculus.disorderSliceCoordinates
      (endpointPathCoordinateMap a n w))
      (stdGaussian (EuclideanSpace ℝ (Fin S.card))) disorderLaw
    exact PolymerCalculus.hasLaw_disorderSliceCoordinates (endpointPathCoordinateMap a n w) he
  have hπmeas : Measurable π := by
    change Measurable (fun ω : Disorder =>
      WithLp.toLp 2 (fun i => ω (endpointPathCoordinateMap a n w i)))
    have hraw : Measurable (fun ω : Disorder =>
        fun i : Fin S.card => ω (endpointPathCoordinateMap a n w i)) :=
      measurable_pi_iff.mpr (fun i => Gaussian.measurable_disorder_eval
        (endpointPathCoordinateMap a n w i))
    have hto : Measurable (fun x : (Fin S.card → ℝ) => WithLp.toLp 2 x) := by fun_prop
    exact hto.comp hraw
  have hcoordEq (ω : Disorder) (p : ℕ × Site) (hp : p ∈ S) : L (π ω) p = ω p := by
    simpa only [L, π, S] using endpointPathCoordinateExtension_vector_eq a n w ω p hp
  have hmassEq (i : κ) (ω : Disorder) :
      PolymerCalculus.finitePathMass β a n w (c i) (L (π ω)) =
        PolymerCalculus.finitePathMass β a n w (c i) ω := by
    apply PolymerCalculus.dependsOn_finitePathMass β a n w (c i)
    intro p hp
    exact hcoordEq ω p hp
  have hFcomp (i : κ) : F i = fun ω => Fv i (π ω) := by
    funext ω
    dsimp [Fv, F]
    exact congrArg Real.log (hmassEq i ω).symm
  have hconvF (i : κ) : ConvexOn ℝ Set.univ (F i) := by
    simpa only [F] using PolymerCalculus.convexOn_log_finitePathMass
      β a n w (hc i) (hpos i)
  have hLlin : ∀ x y (u v : ℝ), L (u • x + v • y) = u • L x + v • L y := by
    intro x y u v
    simp
  have hconvFv (i : κ) : ConvexOn ℝ Set.univ (Fv i) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ u v hu hv huv
    change F i (L (u • x + v • y)) ≤ u * F i (L x) + v * F i (L y)
    rw [hLlin]
    exact (hconvF i).2 (Set.mem_univ _) (Set.mem_univ _) hu hv huv
  have hconvH : ConvexOn ℝ Set.univ H := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ u v hu hv huv
    change (∑ i : κ, weight i * Fv i (u • x + v • y)) ≤
      u * (∑ i : κ, weight i * Fv i x) + v * (∑ i : κ, weight i * Fv i y)
    calc
      _ ≤ ∑ i : κ, weight i * (u * Fv i x + v * Fv i y) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          ((hconvFv i).2 (Set.mem_univ _) (Set.mem_univ _) hu hv huv) (hweight i)
      _ = ∑ i : κ, (u * (weight i * Fv i x) + v * (weight i * Fv i y)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hLmeas : Measurable L := by
    apply measurable_pi_iff.mpr
    intro p
    dsimp [L, endpointPathCoordinateExtension, S]
    split_ifs <;> fun_prop
  have hFmeas (i : κ) : Measurable (F i) := by
    simpa only [F] using PolymerCalculus.measurable_log_finitePathMass β a n w (c i)
  have hFvmeas (i : κ) : Measurable (Fv i) := (hFmeas i).comp hLmeas
  have hHmeas : Measurable H := by
    dsimp [H]
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_const.mul (hFvmeas i))
  have hsumComp : (fun ω => ∑ i : κ, weight i * F i ω) = fun ω => H (π ω) := by
    funext ω
    change (∑ i : κ, weight i * F i ω) =
      ∑ i : κ, weight i * Fv i (π ω)
    apply Finset.sum_congr rfl
    intro i hi
    rw [hFcomp i]
  have hmeasure : disorderLaw.map (fun ω => ∑ i : κ, weight i * F i ω) =
      (stdGaussian (EuclideanSpace ℝ (Fin S.card))).map H := by
    rw [hsumComp]
    calc
      disorderLaw.map (fun ω => H (π ω)) = (disorderLaw.map π).map H :=
        (Measure.map_map hHmeas hπmeas).symm
      _ = (stdGaussian (EuclideanSpace ℝ (Fin S.card))).map H := by rw [hπlaw.map_eq]
  change IsEhrhardType (disorderLaw.map fun ω => ∑ i : κ, weight i * F i ω)
  rw [hmeasure]
  exact Provider.ehrhardType_convexGaussianImage _ H hconvH

/-- A finite nonnegative average of logarithmic polymer profiles with simple random walk initial
profiles has an Ehrhard-type law. -/
private theorem isEhrhardType_sum_log_srwProfile
    (β : ℝ) (a b m : ℕ) (S : Finset Site) (weight : Site → ℝ)
    (hweight : ∀ z ∈ S, 0 ≤ weight z) :
    IsEhrhardType (disorderLaw.map fun ω =>
      ∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z)) (fun _ => 1) ω)) := by
  classical
  let A : Finset Site := S.biUnion fun z => Polymer.endpoints z m
  let Starts := {w : Site // w ∈ A}
  let I := {z : Site // z ∈ S}
  let start : Starts → Site := fun w => w.1
  let coeff : I → Starts × (Fin (b - a) → Fin 4) → ℝ := fun z p =>
    srwKernel m (p.1.1 - z.1) * ((4 : ℝ)⁻¹ ^ (b - a))
  let wt : I → ℝ := fun z => weight z.1
  have hStart : (Finset.univ : Finset Starts) = A.attach := by
    ext w
    simp [Starts]
  have hI : (Finset.univ : Finset I) = S.attach := by
    ext z
    simp [I]
  have hA (z : I) (w : Site) (hw : w ∈ Polymer.endpoints z.1 m) : w ∈ A := by
    exact Finset.mem_biUnion.mpr ⟨z.1, z.2, hw⟩
  have hνA (z : I) (w : Site) (hw : w ∉ A) : srwKernel m (w - z.1) = 0 := by
    apply Polymer.srwKernel_eq_zero_of_not_mem m z.1 w
    intro hmem
    exact hw (hA z w hmem)
  have hνEnd (z : I) (w : Site) (hw : w ∉ Polymer.endpoints z.1 m) :
      srwKernel m (w - z.1) = 0 :=
    Polymer.srwKernel_eq_zero_of_not_mem m z.1 w hw
  have hνsum (z : I) :
      (∑ w ∈ A, srwKernel m (w - z.1)) = 1 := by
    calc
      (∑ w ∈ A, srwKernel m (w - z.1)) =
          ∑' w : Site, srwKernel m (w - z.1) := (tsum_eq_sum (hνA z)).symm
      _ = ∑ w ∈ Polymer.endpoints z.1 m, srwKernel m (w - z.1) :=
          tsum_eq_sum (hνEnd z)
      _ = 1 := Polymer.sum_srwKernel_endpoints m z.1
  have hcoeff (z : I) (p : Starts × (Fin (b - a) → Fin 4)) : 0 ≤ coeff z p := by
    dsimp [coeff]
    exact mul_nonneg (srwKernel_nonneg _ _) (by positivity)
  have hcoeffPos (z : I) : ∃ p, 0 < coeff z p := by
    have hnonneg : ∀ w, 0 ≤ srwKernel m (w - z.1) := fun w => srwKernel_nonneg _ _
    have hsumPos : 0 < ∑ w ∈ A, srwKernel m (w - z.1) := by rw [hνsum z]; norm_num
    obtain ⟨w, hwA, hwp⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun w hw => hnonneg w)).mp hsumPos
    refine ⟨(⟨w, hwA⟩, fun _ => 0), ?_⟩
    dsimp [coeff]
    exact mul_pos hwp (by positivity)
  have hcoeffEq (z : I) (ω : Disorder) :
      profileP2Fun β a b (fun w => srwKernel m (w - z.1)) (fun _ => 1) ω =
        PolymerCalculus.finitePathMass β a (b - a) start (coeff z) ω := by
    simpa only [start, coeff, Starts] using
      OnePoint.profileP2Fun_eq_finitePathMass β a b
        (fun w => srwKernel m (w - z.1)) A (hνA z) ω
  have hsumEq (ω : Disorder) :
      (∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z)) (fun _ => 1) ω)) =
      ∑ z : I, wt z * Real.log
        (PolymerCalculus.finitePathMass β a (b - a) start (coeff z) ω) := by
    have hattach := Finset.sum_attach S (fun z => weight z * Real.log
      (profileP2Fun β a b (fun w => srwKernel m (w - z)) (fun _ => 1) ω))
    calc
      _ = ∑ z ∈ S.attach, weight z.1 * Real.log (profileP2Fun β a b
          (fun w => srwKernel m (w - z.1)) (fun _ => 1) ω) := hattach.symm
      _ = ∑ z : I, weight z.1 * Real.log (profileP2Fun β a b
          (fun w => srwKernel m (w - z.1)) (fun _ => 1) ω) := by rw [← hI]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hcoeffEq z ω]
  have h := isEhrhardType_weighted_sum_log_finitePathMass β a (b - a) start wt
    (fun z => hweight z.1 z.2) hcoeff hcoeffPos
  rw [show (fun ω => ∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
      (fun w => srwKernel m (w - z)) (fun _ => 1) ω)) =
      fun ω => ∑ z : I, wt z * Real.log
        (PolymerCalculus.finitePathMass β a (b - a) start (coeff z) ω) from
    funext hsumEq]
  exact h

private theorem profileP2Fun_heatStart_one_eq (β : ℝ) (N a b m : ℕ)
    (hN : 0 < N) (hm : Even m) (hab : Even (b - a)) (x : Plane) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x))
        (cellAverage N fun _ => (1 : ℝ)) ω =
      profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x))
        (fun _ => 1) ω := by
  let A : Finset Site := Polymer.endpoints (latticePoint N x) m
  let ν : Site → ℝ := fun w => srwKernel m (w - latticePoint N x)
  let f : Site → ℝ := fun z => cellAverage N (fun _ => (1 : ℝ)) z
  let g : Site → ℝ := fun _ => 1
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    dsimp [ν, A]
    exact Polymer.srwKernel_eq_zero_of_not_mem m (latticePoint N x) w hw
  have hν0 : ∀ w, 0 ≤ ν w := fun w => by
    dsimp [ν]
    exact srwKernel_nonneg _ _
  have hxEven : latticePoint N x ∈ evenLattice := latticePoint_mem_evenLattice N x
  have hterminal (w : Site) (hw : w ∈ A) (z : Site)
      (hz : z ∈ Polymer.endpoints w (b - a)) : f z = g z := by
    dsimp [f, g]
    have hwEven : w ∈ evenLattice := evenLattice_of_even_duration hxEven hm hw
    have hzEven : z ∈ evenLattice := evenLattice_of_even_duration hwEven hab hz
    exact cellAverage_const hN hzEven 1
  have hterminalLe (w : Site) (hw : w ∈ A) (z : Site)
      (hz : z ∈ Polymer.endpoints w (b - a)) : f z ≤ g z :=
    (hterminal w hw z hz).le
  have hle := profileP2Fun_le_of_reachable (β := β) (a := a) (b := b)
    ν f g A hνA hν0 hterminalLe ω
  have hge := profileP2Fun_le_of_reachable (β := β) (a := a) (b := b)
    ν g f A hνA hν0 (by
      intro w hw z hz
      exact (hterminal w hw z hz).symm.le) ω
  exact le_antisymm hle hge

private theorem isEhrhardType_sum_log_srwProfile_exp (β : ℝ) {N : ℕ}
    (hN : 0 < N) (a b m : ℕ) (hm : Even m) (hab : Even (b - a))
    (h₀ : Plane →ᵇ ℝ) (S : Finset Site) (weight : Site → ℝ)
    (hS_even : ∀ z ∈ S, z ∈ evenLattice)
    (hweight : ∀ z ∈ S, 0 ≤ weight z) :
    IsEhrhardType (disorderLaw.map fun ω =>
      ∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z))
        (cellAverage N fun y => Real.exp (h₀ y)) ω)) := by
  classical
  let A : Finset Site := S.biUnion fun z => Polymer.endpoints z m
  let Starts := {w : Site // w ∈ A}
  let I := {z : Site // z ∈ S}
  let start : Starts → Site := fun w => w.1
  let terminal : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  let coeff : I → Starts × (Fin (b - a) → Fin 4) → ℝ := fun z p =>
    srwKernel m (p.1.1 - z.1) * terminal (walkPosition p.1.1 p.2 (b - a)) *
      ((4 : ℝ)⁻¹ ^ (b - a))
  let wt : I → ℝ := fun z => weight z.1
  have hStart : (Finset.univ : Finset Starts) = A.attach := by
    ext w
    simp [Starts]
  have hI : (Finset.univ : Finset I) = S.attach := by
    ext z
    simp [I]
  have hA (z : I) (w : Site) (hw : w ∈ Polymer.endpoints z.1 m) : w ∈ A :=
    Finset.mem_biUnion.mpr ⟨z.1, z.2, hw⟩
  have hνA (z : I) (w : Site) (hw : w ∉ A) : srwKernel m (w - z.1) = 0 := by
    apply Polymer.srwKernel_eq_zero_of_not_mem m z.1 w
    intro hmem
    exact hw (hA z w hmem)
  have hνEnd (z : I) (w : Site) (hw : w ∉ Polymer.endpoints z.1 m) :
      srwKernel m (w - z.1) = 0 :=
    Polymer.srwKernel_eq_zero_of_not_mem m z.1 w hw
  have hνsum (z : I) :
      (∑ w ∈ A, srwKernel m (w - z.1)) = 1 := by
    calc
      (∑ w ∈ A, srwKernel m (w - z.1)) =
          ∑' w : Site, srwKernel m (w - z.1) := (tsum_eq_sum (hνA z)).symm
      _ = ∑ w ∈ Polymer.endpoints z.1 m, srwKernel m (w - z.1) :=
          tsum_eq_sum (hνEnd z)
      _ = 1 := Polymer.sum_srwKernel_endpoints m z.1
  have htermNonneg (v : Site) : 0 ≤ terminal v := by
    by_cases hv : v ∈ evenLattice
    · exact (Smoothing.cellAverage_exp_bounds_of_even N (by omega) h₀ hv).1.le
    · dsimp [terminal, cellAverage]
      rw [cell_eq_empty_of_not_even hv]
      simp
  have hcoeff (z : I) (p : Starts × (Fin (b - a) → Fin 4)) : 0 ≤ coeff z p := by
    dsimp [coeff]
    exact mul_nonneg (mul_nonneg (srwKernel_nonneg _ _) (htermNonneg _)) (by positivity)
  have hcoeffPos (z : I) : ∃ p, 0 < coeff z p := by
    have hnonneg : ∀ w, 0 ≤ srwKernel m (w - z.1) := fun w => srwKernel_nonneg _ _
    have hsumPos : 0 < ∑ w ∈ A, srwKernel m (w - z.1) := by rw [hνsum z]; norm_num
    obtain ⟨w, hwA, hwp⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun w hw => hnonneg w)).mp hsumPos
    obtain ⟨z₀, hz₀S, hwreach⟩ := Finset.mem_biUnion.mp hwA
    have hwEven : w ∈ evenLattice := evenLattice_of_even_duration
      (hS_even z₀ hz₀S) hm hwreach
    let path : Fin (b - a) → Fin 4 := fun _ => 0
    let v := walkPosition w path (b - a)
    have hvReach : v ∈ Polymer.endpoints w (b - a) :=
      (Polymer.mem_endpoints_iff w v (b - a)).2 ⟨path, rfl⟩
    have hvEven : v ∈ evenLattice := evenLattice_of_even_duration hwEven hab hvReach
    have htermPos : 0 < terminal v := by
      dsimp [terminal]
      exact (Smoothing.cellAverage_exp_bounds_of_even N (by omega) h₀ hvEven).1
    refine ⟨(⟨w, hwA⟩, path), ?_⟩
    dsimp [coeff, path, v]
    exact mul_pos (mul_pos hwp htermPos) (by positivity)
  have hcoeffEq (z : I) (ω : Disorder) :
      profileP2Fun β a b (fun w => srwKernel m (w - z.1)) terminal ω =
        PolymerCalculus.finitePathMass β a (b - a) start (coeff z) ω := by
    simpa only [start, coeff, terminal, Starts] using
      profileP2Fun_eq_finitePathMass_terminal β a b
        (fun w => srwKernel m (w - z.1)) terminal A (hνA z) ω
  have hsumEq (ω : Disorder) :
      (∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z)) terminal ω)) =
      ∑ z : I, wt z * Real.log
        (PolymerCalculus.finitePathMass β a (b - a) start (coeff z) ω) := by
    have hattach := Finset.sum_attach S (fun z => weight z * Real.log
      (profileP2Fun β a b (fun w => srwKernel m (w - z)) terminal ω))
    calc
      _ = ∑ z ∈ S.attach, weight z.1 * Real.log (profileP2Fun β a b
          (fun w => srwKernel m (w - z.1)) terminal ω) := hattach.symm
      _ = ∑ z : I, weight z.1 * Real.log (profileP2Fun β a b
          (fun w => srwKernel m (w - z.1)) terminal ω) := by rw [← hI]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hcoeffEq z ω]
  have h := isEhrhardType_weighted_sum_log_finitePathMass β a (b - a) start wt
    (fun z => hweight z.1 z.2) hcoeff hcoeffPos
  rw [show (fun ω => ∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
      (fun w => srwKernel m (w - z)) terminal ω)) =
      fun ω => ∑ z : I, wt z * Real.log
        (PolymerCalculus.finitePathMass β a (b - a) start (coeff z) ω) from
    funext hsumEq]
  exact h

/-- At every finite lattice scale, the spatial integral of the heat-start logarithmic field
has an Ehrhard-type law. -/
private theorem isEhrhardType_integral_heatStartLogProfile (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {r t : ℝ} (_hrt : r < t) (ψ : TestFn)
    (hψ : ∀ x, 0 ≤ ψ x) :
    IsEhrhardType (disorderLaw.map fun ω =>
      ∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) := by
  classical
  let a := evenCeil (N * r)
  let b := evenCeil (N * t)
  let m := evenCeil (N * r)
  let β := criticalBeta ϑ N
  obtain ⟨S, hS⟩ := exists_finite_heatStartCells (fun _ : Fin 1 => ψ) N
  have hS' : ∀ x, ψ x ≠ 0 → latticePoint N x ∈ S := by
    intro x hx
    exact hS 0 x hx
  let G : Site → Disorder → ℝ := fun z ω => Real.log
    (profileP2Fun β a b (fun w => srwKernel m (w - z)) (fun _ => 1) ω)
  let weight : Site → ℝ := fun z => ∫ x in cell N z, ψ x
  have hhm : Even m := by dsimp [m]; exact evenCeil_even (N * r)
  have hhab : Even (b - a) := by
    dsimp [a, b]
    exact (evenCeil_even (N * t)).tsub (evenCeil_even (N * r))
  have hpoint (x : Plane) (ω : Disorder) :
      heatStartLogProfile ϑ N r t r x 0 ω = G (latticePoint N x) ω := by
    dsimp [heatStartLogProfile, G, a, b, m, β]
    rw [Real.exp_zero]
    exact congrArg Real.log (profileP2Fun_heatStart_one_eq
      (criticalBeta ϑ N) N (evenCeil (N * r)) (evenCeil (N * t))
      (evenCeil (N * r)) hN hhm hhab x ω)
  have hpiece (ω : Disorder) :
      (∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) =
      ∑ z ∈ S, weight z * G z ω := by
    rw [show (fun x => ψ x * heatStartLogProfile ϑ N r t r x 0 ω) =
      fun x => ψ x * G (latticePoint N x) ω from funext fun x => by rw [hpoint]]
    exact integral_mul_latticePoint_piecewise ψ.continuous ψ.hasCompactSupport N
      (fun z => G z ω) S hS'
  have hweight : ∀ z ∈ S, 0 ≤ weight z := by
    intro z hz
    dsimp [weight]
    exact setIntegral_nonneg (measurableSet_cell N z) (fun x hx => hψ x)
  have hE : IsEhrhardType (disorderLaw.map fun ω => ∑ z ∈ S,
      weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z)) (fun _ => 1) ω)) := by
    exact isEhrhardType_sum_log_srwProfile β a b m S weight hweight
  have hEq : (fun ω => ∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) =
      fun ω => ∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z)) (fun _ => 1) ω) := by
    funext ω
    simpa [G, weight] using hpiece ω
  rw [show (fun ω => ∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) = _ from hEq]
  exact hE

private theorem isEhrhardType_integral_heatStartLogProfile_general (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {r t : ℝ} (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (h₀ : Plane →ᵇ ℝ) :
    IsEhrhardType (disorderLaw.map fun ω =>
      ∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω) := by
  classical
  let a := evenCeil (N * r)
  let b := evenCeil (N * t)
  let m := evenCeil (N * r)
  let β := criticalBeta ϑ N
  obtain ⟨Sraw, hSraw⟩ := exists_finite_heatStartCells (fun _ : Fin 1 => ψ) N
  let S := Sraw.filter fun z => z ∈ evenLattice
  have hS : ∀ x, ψ x ≠ 0 → latticePoint N x ∈ S := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨hSraw 0 x hx, latticePoint_mem_evenLattice N x⟩
  let G : Site → Disorder → ℝ := fun z ω => Real.log
    (profileP2Fun β a b (fun w => srwKernel m (w - z))
      (cellAverage N fun y => Real.exp (h₀ y)) ω)
  let weight : Site → ℝ := fun z => ∫ x in cell N z, ψ x
  have hhm : Even m := by dsimp [m]; exact evenCeil_even (N * r)
  have hhab : Even (b - a) := by
    dsimp [a, b]
    exact (evenCeil_even (N * t)).tsub (evenCeil_even (N * r))
  have hpoint (x : Plane) (ω : Disorder) :
      heatStartLogProfile ϑ N r t r x h₀ ω = G (latticePoint N x) ω := by
    rfl
  have hpiece (ω : Disorder) :
      (∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω) =
      ∑ z ∈ S, weight z * G z ω := by
    rw [show (fun x => ψ x * heatStartLogProfile ϑ N r t r x h₀ ω) =
      fun x => ψ x * G (latticePoint N x) ω from funext fun x => by rw [hpoint]]
    exact integral_mul_latticePoint_piecewise ψ.continuous ψ.hasCompactSupport N
      (fun z => G z ω) S hS
  have hweight : ∀ z ∈ S, 0 ≤ weight z := by
    intro z hz
    dsimp [weight]
    exact setIntegral_nonneg (measurableSet_cell N z) (fun x hx => hψ x)
  have hE : IsEhrhardType (disorderLaw.map fun ω => ∑ z ∈ S,
      weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z))
        (cellAverage N fun y => Real.exp (h₀ y)) ω)) := by
    exact isEhrhardType_sum_log_srwProfile_exp β hN a b m hhm hhab h₀ S weight
      (fun z hz => (Finset.mem_filter.mp hz).2) hweight
  have hEq : (fun ω => ∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω) =
      fun ω => ∑ z ∈ S, weight z * Real.log (profileP2Fun β a b
        (fun w => srwKernel m (w - z))
        (cellAverage N fun y => Real.exp (h₀ y)) ω) := by
    funext ω
    simpa [G, weight] using hpiece ω
  rw [show (fun ω => ∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω) = _ from hEq]
  exact hE

/-- At every finite lattice scale, the sum of the flat and perturbed spatial logarithmic fields
has an Ehrhard-type law. -/
private theorem isEhrhardType_integral_heatStartLogProfile_pair (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {r t : ℝ} (_hrt : r < t) (ψ : TestFn)
    (hψ : ∀ x, 0 ≤ ψ x) (h₀ : Plane →ᵇ ℝ) :
    IsEhrhardType (disorderLaw.map fun ω =>
      (∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) +
      (∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω)) := by
  classical
  let a := evenCeil (N * r)
  let b := evenCeil (N * t)
  let m := evenCeil (N * r)
  let β := criticalBeta ϑ N
  obtain ⟨Sraw, hSraw⟩ := exists_finite_heatStartCells (fun _ : Fin 1 => ψ) N
  let S := Sraw.filter fun z => z ∈ evenLattice
  have hS : ∀ x, ψ x ≠ 0 → latticePoint N x ∈ S := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSraw 0 x hx, latticePoint_mem_evenLattice N x⟩
  let A : Finset Site := S.biUnion fun z => Polymer.endpoints z m
  let Starts := {w : Site // w ∈ A}
  let I := {z : Site // z ∈ S}
  let start : Starts → Site := fun w => w.1
  let terminal : Fin 2 → Site → ℝ := fun j z =>
    cellAverage N (fun y => Real.exp ((if j = 0 then (0 : Plane →ᵇ ℝ) else h₀) y)) z
  let ψWeight : Site → ℝ := fun z => ∫ x in cell N z, ψ x
  let coeff : I × Fin 2 → Starts × (Fin (b - a) → Fin 4) → ℝ := fun q p =>
    srwKernel m (p.1.1 - q.1.1) * terminal q.2
      (walkPosition p.1.1 p.2 (b - a)) * ((4 : ℝ)⁻¹ ^ (b - a))
  let wt : I × Fin 2 → ℝ := fun q => ψWeight q.1.1
  have hhm : Even m := by dsimp [m]; exact evenCeil_even (N * r)
  have hhab : Even (b - a) := by
    dsimp [a, b]
    exact (evenCeil_even (N * t)).tsub (evenCeil_even (N * r))
  have hI : (Finset.univ : Finset I) = S.attach := by
    ext z
    simp [I]
  have hA (z : I) (w : Site) (hw : w ∈ Polymer.endpoints z.1 m) : w ∈ A :=
    Finset.mem_biUnion.mpr ⟨z.1, z.2, hw⟩
  have hνA (z : I) (w : Site) (hw : w ∉ A) : srwKernel m (w - z.1) = 0 := by
    apply Polymer.srwKernel_eq_zero_of_not_mem m z.1 w
    intro hmem
    exact hw (hA z w hmem)
  have hνEnd (z : I) (w : Site) (hw : w ∉ Polymer.endpoints z.1 m) :
      srwKernel m (w - z.1) = 0 := Polymer.srwKernel_eq_zero_of_not_mem m z.1 w hw
  have hνsum (z : I) : (∑ w ∈ A, srwKernel m (w - z.1)) = 1 := by
    calc
      (∑ w ∈ A, srwKernel m (w - z.1)) = ∑' w : Site, srwKernel m (w - z.1) :=
        (tsum_eq_sum (hνA z)).symm
      _ = ∑ w ∈ Polymer.endpoints z.1 m, srwKernel m (w - z.1) := tsum_eq_sum (hνEnd z)
      _ = 1 := Polymer.sum_srwKernel_endpoints m z.1
  have hterminalNonneg (j : Fin 2) (z : Site) : 0 ≤ terminal j z := by
    by_cases hz : z ∈ evenLattice
    · exact (Smoothing.cellAverage_exp_bounds_of_even N (by omega)
        (if j = 0 then (0 : Plane →ᵇ ℝ) else h₀) hz).1.le
    · simp [terminal, cellAverage, cell_eq_empty_of_not_even hz]
  have hcoeff (q : I × Fin 2) (p : Starts × (Fin (b - a) → Fin 4)) : 0 ≤ coeff q p := by
    dsimp [coeff]
    exact mul_nonneg (mul_nonneg (srwKernel_nonneg _ _) (hterminalNonneg _ _)) (by positivity)
  have hcoeffPos (q : I × Fin 2) : ∃ p, 0 < coeff q p := by
    have hnonneg : ∀ w, 0 ≤ srwKernel m (w - q.1.1) := fun w => srwKernel_nonneg _ _
    have hsumPos : 0 < ∑ w ∈ A, srwKernel m (w - q.1.1) := by
      rw [hνsum q.1]
      norm_num
    obtain ⟨w, hwA, hwp⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun w hw => hnonneg w)).mp hsumPos
    obtain ⟨z₀, hz₀S, hwreach⟩ := Finset.mem_biUnion.mp hwA
    have hwEven : w ∈ evenLattice := evenLattice_of_even_duration
      (Finset.mem_filter.mp hz₀S).2 hhm hwreach
    let path : Fin (b - a) → Fin 4 := fun _ => 0
    let v := walkPosition w path (b - a)
    have hvReach : v ∈ Polymer.endpoints w (b - a) :=
      (Polymer.mem_endpoints_iff w v (b - a)).2 ⟨path, rfl⟩
    have hvEven : v ∈ evenLattice := evenLattice_of_even_duration hwEven hhab hvReach
    have htermPos : 0 < terminal q.2 v := by
      exact (Smoothing.cellAverage_exp_bounds_of_even N (by omega)
        (if q.2 = 0 then (0 : Plane →ᵇ ℝ) else h₀) hvEven).1
    refine ⟨(⟨w, hwA⟩, path), ?_⟩
    dsimp [coeff, path, v]
    exact mul_pos (mul_pos hwp htermPos) (by positivity)
  have hcoeffEq (z : I) (j : Fin 2) (ω : Disorder) :
      profileP2Fun β a b (fun w => srwKernel m (w - z.1)) (terminal j) ω =
        PolymerCalculus.finitePathMass β a (b - a) start (coeff (z, j)) ω := by
    simpa only [start, coeff, terminal, Starts] using
      profileP2Fun_eq_finitePathMass_terminal β a b
        (fun w => srwKernel m (w - z.1)) (terminal j) A (hνA z) ω
  have hweight : ∀ z ∈ S, 0 ≤ ψWeight z := by
    intro z hz
    dsimp [ψWeight]
    exact setIntegral_nonneg (measurableSet_cell N z) (fun x hx => hψ x)
  let G : Fin 2 → Site → Disorder → ℝ := fun j z ω => Real.log
    (profileP2Fun β a b (fun w => srwKernel m (w - z)) (terminal j) ω)
  have hpoint (x : Plane) (ω : Disorder) :
      heatStartLogProfile ϑ N r t r x 0 ω = G 0 (latticePoint N x) ω ∧
      heatStartLogProfile ϑ N r t r x h₀ ω = G 1 (latticePoint N x) ω := by
    constructor <;> rfl
  have hpiece (j : Fin 2) (ω : Disorder) :
      ∫ x, ψ x * heatStartLogProfile ϑ N r t r x
        (if j = 0 then (0 : Plane →ᵇ ℝ) else h₀) ω =
      ∑ z ∈ S, ψWeight z * G j z ω := by
    rw [show (fun x => ψ x * heatStartLogProfile ϑ N r t r x
        (if j = 0 then (0 : Plane →ᵇ ℝ) else h₀) ω) =
      fun x => ψ x * G j (latticePoint N x) ω from funext fun x => by
        by_cases hj : j = 0
        · subst j
          exact congrArg (fun u => ψ x * u) (hpoint x ω).1
        · have hj1 : j = 1 := Fin.ext (by omega)
          subst j
          exact congrArg (fun u => ψ x * u) (hpoint x ω).2]
    exact integral_mul_latticePoint_piecewise ψ.continuous ψ.hasCompactSupport N
      (fun z => G j z ω) S (by
        intro x hx
        exact hS x hx)
  have hsourceEq (ω : Disorder) :
      (∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) +
        (∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω) =
      ∑ q : I × Fin 2, wt q * Real.log
        (PolymerCalculus.finitePathMass β a (b - a) start (coeff q) ω) := by
    have hleft := hpiece 0 ω
    have hright := hpiece 1 ω
    have hattach0 := Finset.sum_attach S (fun z => ψWeight z * G 0 z ω)
    have hattach1 := Finset.sum_attach S (fun z => ψWeight z * G 1 z ω)
    rw [show (∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) =
      ∑ z ∈ S, ψWeight z * G 0 z ω from by simpa using hleft,
      show (∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω) =
      ∑ z ∈ S, ψWeight z * G 1 z ω from by simpa using hright]
    calc
      _ = (∑ z ∈ S.attach, ψWeight z.1 * G 0 z.1 ω) +
          (∑ z ∈ S.attach, ψWeight z.1 * G 1 z.1 ω) := by
        rw [hattach0.symm, hattach1.symm]
      _ = ∑ z : I, (ψWeight z.1 * G 0 z.1 ω + ψWeight z.1 * G 1 z.1 ω) := by
        rw [← hI]
        simp only [Finset.sum_add_distrib]
        rfl
      _ = ∑ q : I × Fin 2, wt q * Real.log
          (PolymerCalculus.finitePathMass β a (b - a) start (coeff q) ω) := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two, wt, G]
        simp_rw [hcoeffEq]
  have hE := isEhrhardType_weighted_sum_log_finitePathMass β a (b - a) start wt
    (fun q => hweight q.1.1 q.1.2) hcoeff hcoeffPos
  rw [show (fun ω => (∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω) +
      (∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω)) =
      fun ω => ∑ q : I × Fin 2, wt q * Real.log
        (PolymerCalculus.finitePathMass β a (b - a) start (coeff q) ω) from funext hsourceEq]
  exact hE

private theorem avgLogField_eq_uncentered_sub_mean_integral (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → Plane →ᵇ ℝ),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (ψ : TestFn) (h₀ : Plane →ᵇ ℝ) :
    ∃ d : ℝ, d = ∫ x, ψ x * ∫ ω, Real.log (shfPairing Z r t
        (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω) ∂P ∧
      AEMeasurable (avgLogField P Z r t ψ
        (fun y => Real.exp (h₀ y))) P ∧
      (∀ᵐ ω ∂P, avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) ω =
        (∫ x, ψ x * Real.log (shfPairing Z r t
          (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω)) - d) ∧
      Integrable (avgLogField P Z r t ψ (fun y => Real.exp (h₀ y))) P ∧
      (∫ ω, avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) ω ∂P) = 0 := by
  let G : Plane × Ω → ℝ := fun q => Real.log
    (shfPairing Z r t (fun y => heatKernel r (y - q.1))
      (fun y => Real.exp (h₀ y)) q.2)
  let F : Plane × Ω → ℝ := fun q => ψ q.1 * G q
  let m : Plane → ℝ := fun x => ∫ ω, G (x, ω) ∂P
  let J : Plane → ℝ := fun x => ∫ ω, F (x, ω) ∂P
  let U : Ω → ℝ := fun ω => ∫ x, F (x, ω) ∂volume
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z r t ω) := by
    filter_upwards [(hZ.2.1 r t hr.le hrt).mono (fun ω hω => hω.1)] with ω hω
    exact hω
  have hG : AEMeasurable G (volume.prod P) := by
    exact aemeasurable_log_heatPairing_joint P (Z r t) (hZ.1 r t hr.le hrt)
      hlocal r hr (fun y => Real.exp (h₀ y))
      (Real.continuous_exp.measurable.comp h₀.continuous.measurable)
      (fun y => (Real.exp_nonneg _))
  have hsec (x : Plane) : AEStronglyMeasurable (fun ω => G (x, ω)) P := by
    have h := hsym.2.2.2.2.2.2 r t r x h₀ hr.le hrt hr
    simpa [G] using h.2.1.aestronglyMeasurable
  obtain ⟨M, hM, hSq⟩ := shf_heatStartLogField_square_bound
    ϑ P Z hZ hpair hjoint hpos t h₀ hr.le hrt hr
  have hSqG (x : Plane) : Integrable (fun ω => |G (x, ω)| ^ 2) P ∧
      ∫ ω, |G (x, ω)| ^ 2 ∂P ≤ M := by simpa [G] using hSq x
  have hprod : Integrable F (volume.prod P) := by
    exact integrable_test_mul_joint P hG hsec hM hSqG ψ
  have hSectionsX : ∀ᵐ ω ∂P, Integrable (fun x => F (x, ω)) volume :=
    (integrable_prod_iff' hprod.aestronglyMeasurable).1 hprod |>.1
  have hGmem (x : Plane) : MemLp (fun ω => G (x, ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq (hsec x)).2
    simpa [sq_abs] using (hSqG x).1
  have hGint (x : Plane) : Integrable (fun ω => G (x, ω)) P :=
    (hGmem x).integrable (by norm_num)
  have hJmeas : AEMeasurable J volume := by
    exact hprod.aestronglyMeasurable.integral_prod_right'.aemeasurable.congr
      (Filter.Eventually.of_forall fun x => rfl)
  have hJmajor : Integrable (fun x => ∫ ω, ‖F (x, ω)‖ ∂P) volume :=
    (integrable_prod_iff hprod.aestronglyMeasurable).1 hprod |>.2
  have hCenterInt : Integrable J volume := by
    apply hJmajor.mono' hJmeas.aestronglyMeasurable
    filter_upwards [] with x
    dsimp [J]
    exact norm_integral_le_integral_norm (fun ω => F (x, ω))
  have hJ (x : Plane) : J x = ψ x * m x := by
    dsimp [J, m, F, G]
    rw [integral_const_mul]
  have hUmeas : AEMeasurable U P := by
    exact (aemeasurable_integral_shfLogField ϑ P Z hZ r t r hr.le hrt hr h₀ ψ).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have hEq : ∀ᵐ ω ∂P, avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) ω = U ω - ∫ x, J x ∂volume := by
    filter_upwards [hSectionsX] with ω hω
    have hpoint (x : Plane) :
        ψ x * (G (x, ω) - m x) = F (x, ω) - J x := by
      rw [hJ x]
      dsimp [F]
      ring
    have hAvg : avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) ω =
        ∫ x, (F (x, ω) - J x) ∂volume := by
      unfold avgLogField
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => hpoint x
    rw [hAvg, integral_sub hω hCenterInt]
  have hUInt : Integrable U P := by
    simpa [U, F] using hprod.swap.integral_prod_left
  have hEqFun : (fun ω => U ω - ∫ x, J x ∂volume) =ᵐ[P]
      avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) := by
    filter_upwards [hEq] with ω hω
    exact hω.symm
  have hAveMeas : AEMeasurable
      (avgLogField P Z r t ψ (fun y => Real.exp (h₀ y))) P := by
    have hDmeas : AEMeasurable (fun _ : Ω => ∫ x, J x ∂volume) P := aemeasurable_const
    exact (hUmeas.sub hDmeas).congr hEqFun
  have hd : (∫ x, J x ∂volume) = ∫ x, ψ x * ∫ ω,
      Real.log (shfPairing Z r t (fun y => heatKernel r (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => hJ x
  have hUmean : (∫ ω, U ω ∂P) = ∫ x, J x ∂volume := by
    calc
      (∫ ω, U ω ∂P) = ∫ ω, ∫ x, F (x, ω) ∂volume ∂P := rfl
      _ = ∫ x, ∫ ω, F (x, ω) ∂P ∂volume := integral_integral_swap hprod.swap
      _ = ∫ x, J x ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp [J, F, G, integral_const_mul]
  have hAvgInt : Integrable (avgLogField P Z r t ψ (fun y => Real.exp (h₀ y))) P :=
    (hUInt.sub (integrable_const (∫ x, J x ∂volume))).congr hEqFun
  have hAvgMean : (∫ ω, avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) ω ∂P) = 0 := by
    calc
      _ = ∫ ω, U ω - ∫ x, J x ∂volume ∂P := integral_congr_ae hEq
      _ = (∫ ω, U ω ∂P) - ∫ ω, (∫ x, J x ∂volume) ∂P :=
        integral_sub hUInt (integrable_const _)
      _ = 0 := by simp [hUmean]
  exact ⟨∫ x, J x ∂volume, hd, hAveMeas, hEq, hAvgInt, hAvgMean⟩

/-- The spatially averaged centered logarithmic field with a bounded exponential terminal
is integrable and has mean zero. -/
theorem avgLogField_integral_eq_zero_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (ψ : TestFn) (h₀ : Plane →ᵇ ℝ) :
    Integrable (avgLogField P Z r t ψ (fun y => Real.exp (h₀ y))) P ∧
      (∫ ω, avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) ω ∂P) = 0 := by
  have hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane)
      (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P := by
    intro s t δ hs hst hδ x g
    exact isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hjoint := isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
  have hpos : ∀ (s t δ : ℝ) (x : Plane) (g : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (g y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (g y)) ω)) P := by
    intro s t δ x g hs hst hδ
    rcases hsym.2.2.2.2.2.2 s t δ x g hs hst hδ with ⟨hp, hm, _⟩
    exact ⟨hp, hm⟩
  obtain ⟨_, _, _, _, hint, hmean⟩ := avgLogField_eq_uncentered_sub_mean_integral
    ϑ P Z hZ hsym hpair hjoint hpos hr hrt ψ h₀
  exact ⟨hint, hmean⟩

private theorem integral_abs_le_sqrt_integral_sq_disorder (f : Disorder → ℝ)
    (hfmeas : Measurable f) (hf : Integrable (fun ω => f ω ^ 2) disorderLaw) :
    ∫ ω, |f ω| ∂disorderLaw ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) := by
  have hfmem : MemLp f (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    have hfmem' : MemLp f 2 disorderLaw :=
      (memLp_two_iff_integrable_sq hfmeas.aestronglyMeasurable).2 (by
        simpa only [Real.norm_eq_abs, sq_abs] using hf)
    simpa using hfmem'
  have hAbsMem : MemLp (fun ω => |f ω|) (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    have h := hfmem.norm
    simpa only [Real.norm_eq_abs] using h
  have honeMem : MemLp (fun _ : Disorder => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) disorderLaw := memLp_const 1
  have honeNonneg : 0 ≤ᵐ[disorderLaw] (fun _ : Disorder => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun _ => by norm_num
  have hAbsNonneg : 0 ≤ᵐ[disorderLaw] (fun ω => |f ω|) :=
    Filter.Eventually.of_forall fun ω => abs_nonneg _
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := disorderLaw) (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two honeNonneg hAbsNonneg honeMem hAbsMem
  have hOne : ∫ ω, (1 : ℝ) ^ 2 ∂disorderLaw = 1 := by simp
  have hSq : ∫ ω, |f ω| ^ 2 ∂disorderLaw = ∫ ω, f ω ^ 2 ∂disorderLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Pi.pow_apply] using (sq_abs (f ω))
  calc
    _ = ∫ ω, (1 : ℝ) * |f ω| ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by ring
    _ ≤ (∫ ω, (1 : ℝ) ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) *
        (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by
      simpa only [Real.rpow_two] using hHolder
    _ = Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) := by
      calc
        _ = 1 ^ (1 / 2 : ℝ) * (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by
          exact congrArg (fun q : ℝ => q ^ (1 / 2 : ℝ) *
            (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ)) hOne
        _ = (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by simp
        _ = (∫ ω, f ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) :=
          congrArg (fun q : ℝ => q ^ (1 / 2 : ℝ)) hSq
        _ = Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) := by
          exact (Real.sqrt_eq_rpow _).symm

private theorem integral_heatStartLogProfile_mean_shift_tendsto (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → Plane →ᵇ ℝ),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (ψ : TestFn) (h₀ : Plane →ᵇ ℝ) :
    ∃ N₀ : ℕ, Tendsto (fun N => ∫ x, ψ x * ∫ ω,
      heatStartLogProfile ϑ (N + N₀) r t r x h₀ ω ∂disorderLaw) atTop
      (𝓝 (∫ x, ψ x * ∫ ω, Real.log (shfPairing Z r t
        (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω) ∂P)) := by
  classical
  let mN : ℕ → Plane → ℝ := fun N x => ∫ ω,
    heatStartLogProfile ϑ N r t r x h₀ ω ∂disorderLaw
  let mLimit : Plane → ℝ := fun x => ∫ ω, Real.log (shfPairing Z r t
    (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω) ∂P
  obtain ⟨C, hC, hCN⟩ := heatStartLogProfile_square_bound ϑ hr.le hrt hr h₀
  let M : ℝ := C * 2 * Real.Gamma 2
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg hC (by norm_num))
      (Real.Gamma_pos_of_pos (by norm_num)).le
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hCN
  have hprofMeas (N : ℕ) (x : Plane) :
      Measurable (heatStartLogProfile ϑ N r t r x h₀) := by
    unfold heatStartLogProfile
    exact Real.measurable_log.comp (Polymer.measurable_profileP2Fun _ _ _ _ _)
  have hmNMeas (N : ℕ) : Measurable (mN N) := by
    let A : Site → ℝ := fun z => ∫ ω, Real.log
      (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * r)) (evenCeil (N * t))
        (fun w => srwKernel (evenCeil (N * r)) (w - z))
        (cellAverage N fun y => Real.exp (h₀ y)) ω) ∂disorderLaw
    have hA : Measurable A := measurable_of_countable A
    have hEq : mN N = A ∘ latticePoint N := by
      funext x
      rfl
    rw [hEq]
    exact hA.comp (measurable_latticePoint N)
  have hmean (x : Plane) : Tendsto (mN · x) atTop (𝓝 (mLimit x)) := by
    simpa [mN, mLimit] using tendsto_heatStartLogProfile_mean ϑ P Z hZ hpair hjoint hpos
      t r r h₀ x hr.le hrt hr
  have hdom : Integrable (fun x : Plane => (Real.sqrt M) * |ψ x|) volume := by
    exact (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).norm.const_mul _
  have hbound (N : ℕ) (hN : N₀ ≤ N) (x : Plane) :
      ‖ψ x * mN N x‖ ≤ Real.sqrt M * |ψ x| := by
    have hSq := hN₀ N hN x
    have hInt : Integrable (fun ω => heatStartLogProfile ϑ N r t r x h₀ ω ^ 2)
        disorderLaw := by
      have h := hSq.1
      apply h.congr
      filter_upwards [] with ω
      simp [sq_abs]
    have hmeanAbs := integral_abs_le_sqrt_integral_sq_disorder
      (heatStartLogProfile ϑ N r t r x h₀) (hprofMeas N x) hInt
    have hmBound : |mN N x| ≤ Real.sqrt M := by
      dsimp [mN]
      calc
        |∫ ω, heatStartLogProfile ϑ N r t r x h₀ ω ∂disorderLaw| ≤
            ∫ ω, |heatStartLogProfile ϑ N r t r x h₀ ω| ∂disorderLaw :=
          abs_integral_le_integral_abs
        _ ≤ Real.sqrt (∫ ω, heatStartLogProfile ϑ N r t r x h₀ ω ^ 2 ∂disorderLaw) :=
          hmeanAbs
        _ ≤ Real.sqrt M := by
          apply Real.sqrt_le_sqrt
          dsimp [M]
          calc
            ∫ ω, heatStartLogProfile ϑ N r t r x h₀ ω ^ 2 ∂disorderLaw =
                ∫ ω, |heatStartLogProfile ϑ N r t r x h₀ ω| ^ 2 ∂disorderLaw := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => by simp [sq_abs]
            _ ≤ C * 2 * Real.Gamma 2 := hSq.2
    rw [Real.norm_eq_abs, abs_mul]
    rw [mul_comm (|ψ x|) (|mN N x|)]
    exact mul_le_mul_of_nonneg_right hmBound (abs_nonneg (ψ x))
  refine ⟨N₀, ?_⟩
  let D : ℕ → ℝ := fun N => ∫ x, ψ x * mN (N + N₀) x
  have hDmeas (N : ℕ) : AEStronglyMeasurable
      (fun x : Plane => ψ x * mN (N + N₀) x) volume := by
    exact ((ψ.continuous.measurable.mul (hmNMeas (N + N₀))).aestronglyMeasurable)
  have hDdom (N : ℕ) : ∀ᵐ x ∂volume,
      ‖ψ x * mN (N + N₀) x‖ ≤ Real.sqrt M * |ψ x| := by
    exact Filter.Eventually.of_forall fun x => hbound (N + N₀) (by omega) x
  have hDlim (x : Plane) : Tendsto
      (fun N => ψ x * mN (N + N₀) x) atTop (𝓝 (ψ x * mLimit x)) := by
    exact tendsto_const_nhds.mul ((hmean x).comp (tendsto_add_atTop_nat N₀))
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun x : Plane => Real.sqrt M * |ψ x|) hDmeas hdom hDdom
    (Filter.Eventually.of_forall hDlim)
  simpa [D, mN, mLimit] using hDCT

private theorem tendsto_of_shifted_nat {f : ℕ → ℝ} {L : ℝ} (N₀ : ℕ)
    (h : Tendsto (fun N => f (N + N₀)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hclose := (Metric.tendsto_nhds.mp h) ε hε
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hclose
  filter_upwards [eventually_ge_atTop (N₀ + k)] with N hN
  let n := N - N₀
  have hn : k ≤ n := by dsimp [n]; omega
  have hrepr : n + N₀ = N := by dsimp [n]; omega
  have h := hk n hn
  simpa [n, hrepr] using h

private theorem integral_heatStartLogProfile_mean_tendsto (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → Plane →ᵇ ℝ),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (ψ : TestFn) (h₀ : Plane →ᵇ ℝ) :
    Tendsto (fun N => ∫ x, ψ x * ∫ ω,
      heatStartLogProfile ϑ N r t r x h₀ ω ∂disorderLaw) atTop
      (𝓝 (∫ x, ψ x * ∫ ω, Real.log (shfPairing Z r t
        (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω) ∂P)) := by
  obtain ⟨N₀, hshift⟩ := integral_heatStartLogProfile_mean_shift_tendsto
    ϑ P Z hZ hpair hjoint hpos hr hrt ψ h₀
  apply tendsto_of_shifted_nat N₀
  simpa [Nat.add_comm] using hshift

/-- The centered log field with a positive bounded continuous terminal, and its sum with
the centered flat-terminal log field, have Ehrhard-type laws; see KPZ Lemma 9.2. -/
theorem avgLogField_isEhrhardType_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (_hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (f : Plane →ᵇ ℝ) {c : ℝ} (hc : 0 < c) (hf : ∀ y, c ≤ f y) :
    AEMeasurable (avgLogField P Z r t ψ f) P ∧
      IsEhrhardType (P.map (avgLogField P Z r t ψ f)) ∧
      IsEhrhardType (P.map fun ω => avgLogField P Z r t ψ (fun _ => 1) ω +
        avgLogField P Z r t ψ f ω) := by
  classical
  let h₀ : Plane →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.log (f y), by
      apply continuous_iff_continuousAt.mpr
      intro y
      exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hc (hf y)))).comp
        f.continuous.continuousAt⟩
    (2 * max |Real.log c| |Real.log ‖f‖|) (by
      intro x y
      rw [Real.dist_eq]
      let B : ℝ := max |Real.log c| |Real.log ‖f‖|
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hbound (z : Plane) : |Real.log (f z)| ≤ B := by
        have hlow : Real.log c ≤ Real.log (f z) := Real.log_le_log hc (hf z)
        have hnorm : f z ≤ ‖f‖ := le_trans (le_abs_self (f z)) (f.norm_coe_le_norm z)
        have hupper : Real.log (f z) ≤ Real.log ‖f‖ :=
          Real.log_le_log (lt_of_lt_of_le hc (hf z)) hnorm
        apply abs_le.mpr
        constructor
        · calc
            -B ≤ -|Real.log c| := by dsimp [B]; exact neg_le_neg (le_max_left _ _)
            _ ≤ Real.log c := neg_abs_le _
            _ ≤ Real.log (f z) := hlow
        · exact hupper.trans ((le_abs_self _).trans (le_max_right _ _))
      calc
        |Real.log (f x) - Real.log (f y)| ≤
            |Real.log (f x)| + |Real.log (f y)| := abs_sub _ _
        _ ≤ B + B := add_le_add (hbound x) (hbound y)
        _ = 2 * B := by ring)
  have h₀eq (y : Plane) : h₀ y = Real.log (f y) := by
    simp [h₀, BoundedContinuousFunction.mkOfBound_coe]
  have hexp₀ (y : Plane) : Real.exp (h₀ y) = f y := by
    rw [h₀eq]
    exact Real.exp_log (lt_of_lt_of_le hc (hf y))
  have hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane)
      (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P := by
    intro s t δ hs hst hδ x g
    exact isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hjoint := isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
  have hpos : ∀ (s t δ : ℝ) (x : Plane) (g : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (g y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (g y)) ω)) P := by
    intro s t δ x g hs hst hδ
    rcases hsym.2.2.2.2.2.2 s t δ x g hs hst hδ with ⟨hp, hm, _⟩
    exact ⟨hp, hm⟩
  obtain ⟨d₀, hd₀, hmeas₀, hcenter₀, _hInt₀, _hMean₀⟩ := avgLogField_eq_uncentered_sub_mean_integral
    ϑ P Z hZ hsym hpair hjoint hpos hr hrt ψ (0 : Plane →ᵇ ℝ)
  obtain ⟨d₁, hd₁, hmeas₁, hcenter₁, _hInt₁, _hMean₁⟩ := avgLogField_eq_uncentered_sub_mean_integral
    ϑ P Z hZ hsym hpair hjoint hpos hr hrt ψ h₀
  let hTerminal : Fin 2 → Plane →ᵇ ℝ := fun i => if i = 0 then 0 else h₀
  let X : ℕ → Disorder → Fin 2 → ℝ := fun N ω i =>
    ∫ x, ψ x * heatStartLogProfile ϑ N r t r x (hTerminal i) ω
  let L : Ω → Fin 2 → ℝ := fun ω i =>
    ∫ x, ψ x * Real.log (shfPairing Z r t
      (fun y => heatKernel r (y - x)) (fun y => Real.exp (hTerminal i y)) ω)
  have hparams : ∀ i : Fin 2, 0 ≤ r ∧ r < t ∧ 0 < r := fun _ => ⟨hr.le, hrt, hr⟩
  have hraw : TendstoInDistribution X atTop L (fun _ => disorderLaw) P := by
    simpa [X, L, heatStartLogProfile, hTerminal] using
      hHeatStartLogFieldInput t 2 hTerminal (fun _ => r) (fun _ => r) (fun _ => ψ) hparams
  let d₀N : ℕ → ℝ := fun N => ∫ x, ψ x * ∫ ω,
    heatStartLogProfile ϑ N r t r x 0 ω ∂disorderLaw
  let d₁N : ℕ → ℝ := fun N => ∫ x, ψ x * ∫ ω,
    heatStartLogProfile ϑ N r t r x h₀ ω ∂disorderLaw
  have hmean₀ := integral_heatStartLogProfile_mean_tendsto
    ϑ P Z hZ hpair hjoint hpos hr hrt ψ (0 : Plane →ᵇ ℝ)
  have hmean₁ := integral_heatStartLogProfile_mean_tendsto
    ϑ P Z hZ hpair hjoint hpos hr hrt ψ h₀
  have hmean₀' : Tendsto d₀N atTop (𝓝 (∫ x, ψ x * ∫ ω,
      Real.log (shfPairing Z r t (fun y => heatKernel r (y - x))
        (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω) ∂P)) := by
    simpa [d₀N] using hmean₀
  have hmean₁' : Tendsto d₁N atTop (𝓝 (∫ x, ψ x * ∫ ω,
      Real.log (shfPairing Z r t (fun y => heatKernel r (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∂P)) := by
    simpa [d₁N] using hmean₁
  have hd₀N : Tendsto d₀N atTop (𝓝 d₀) := by
    rw [hd₀]
    simpa [Real.exp_zero] using hmean₀'
  have hd₁N : Tendsto d₁N atTop (𝓝 d₁) := by
    rw [hd₁]
    exact hmean₁'
  have hXzero (N : ℕ) (ω : Disorder) : X N ω 0 =
      ∫ x, ψ x * heatStartLogProfile ϑ N r t r x 0 ω := by
    simp [X, hTerminal]
  have hXpert (N : ℕ) (ω : Disorder) : X N ω 1 =
      ∫ x, ψ x * heatStartLogProfile ϑ N r t r x h₀ ω := by
    simp [X, hTerminal]
  have hLzero (ω : Ω) : L ω 0 =
      ∫ x, ψ x * Real.log (shfPairing Z r t
        (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω) := by
    simp [L, hTerminal, Real.exp_zero]
  have hLpert (ω : Ω) : L ω 1 =
      ∫ x, ψ x * Real.log (shfPairing Z r t
        (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω) := by
    simp [L, hTerminal]
  have hcenter₀' : avgLogField P Z r t ψ (fun _ => (1 : ℝ)) =ᵐ[P]
      fun ω => L ω 0 - d₀ := by
    filter_upwards [hcenter₀] with ω hω
    simpa [hLzero] using hω
  have hcenter₁' : avgLogField P Z r t ψ f =ᵐ[P]
      fun ω => L ω 1 - d₁ := by
    filter_upwards [hcenter₁] with ω hω
    simpa [hLpert, hexp₀] using hω
  have hfieldEq : avgLogField P Z r t ψ f =
      avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) := by
    congr 1
    funext y
    exact (hexp₀ y).symm
  let Xone : ℕ → Disorder → Fin 1 → ℝ := fun N ω _ => X N ω 0
  let Lone : Ω → Fin 1 → ℝ := fun ω _ => L ω 0
  let Done : ℕ → Fin 1 → ℝ := fun N _ => d₀N N
  let DoneLim : Fin 1 → ℝ := fun _ => d₀
  have hrawOne : TendstoInDistribution Xone atTop Lone (fun _ => disorderLaw) P := by
    have h := hraw.continuous_comp
      (g := fun v : Fin 2 → ℝ => fun _ : Fin 1 => v 0) (by fun_prop)
    simpa [Xone, Lone, Function.comp_def] using h
  have hDone : Tendsto Done atTop (𝓝 DoneLim) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa [Done, DoneLim] using hd₀N
  have hshiftOne := tendstoInDistribution_sub_tendsto Xone Lone Done DoneLim hrawOne hDone
  have hTIDzero : TendstoInDistribution
      (fun N ω => X N ω 0 - d₀N N) atTop (fun ω => L ω 0 - d₀) (fun _ => disorderLaw) P := by
    have h := hshiftOne.continuous_comp (continuous_apply (0 : Fin 1))
    simpa [Xone, Lone, Done, DoneLim, Function.comp_def] using h
  let Xsum : ℕ → Disorder → Fin 1 → ℝ := fun N ω _ => X N ω 0 + X N ω 1
  let Lsum : Ω → Fin 1 → ℝ := fun ω _ => L ω 0 + L ω 1
  let Dsum : ℕ → Fin 1 → ℝ := fun N _ => d₀N N + d₁N N
  let DsumLim : Fin 1 → ℝ := fun _ => d₀ + d₁
  have hrawSum : TendstoInDistribution Xsum atTop Lsum (fun _ => disorderLaw) P := by
    have h := hraw.continuous_comp
      (g := fun v : Fin 2 → ℝ => fun _ : Fin 1 => v 0 + v 1) (by fun_prop)
    simpa [Xsum, Lsum, Function.comp_def] using h
  have hDsum : Tendsto Dsum atTop (𝓝 DsumLim) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa [Dsum, DsumLim] using hd₀N.add hd₁N
  have hshiftSum := tendstoInDistribution_sub_tendsto
    Xsum Lsum Dsum DsumLim hrawSum hDsum
  have hTIDsum : TendstoInDistribution
      (fun N ω => X N ω 0 + X N ω 1 - (d₀N N + d₁N N)) atTop
      (fun ω => L ω 0 + L ω 1 - (d₀ + d₁)) (fun _ => disorderLaw) P := by
    have h := hshiftSum.continuous_comp (continuous_apply (0 : Fin 1))
    simpa [Xsum, Lsum, Dsum, DsumLim, Function.comp_def] using h
  have hmeasXzero (N : ℕ) : AEMeasurable (fun ω => X N ω 0) disorderLaw := by
    simpa [X, hTerminal] using
      aemeasurable_integral_heatStartLogProfile ϑ N r t r (0 : Plane →ᵇ ℝ) ψ
  have hmeasXpert (N : ℕ) : AEMeasurable (fun ω => X N ω 1) disorderLaw := by
    simpa [X, hTerminal] using aemeasurable_integral_heatStartLogProfile ϑ N r t r h₀ ψ
  have hmeasXsum (N : ℕ) : AEMeasurable (fun ω => X N ω 0 + X N ω 1) disorderLaw :=
    (hmeasXzero N).add (hmeasXpert N)
  have hmapShiftZero (N : ℕ) :
      disorderLaw.map (fun ω => X N ω 0 - d₀N N) =
        (disorderLaw.map fun ω => X N ω 0).map (fun y => y + -d₀N N) := by
    have hm : Measurable (fun y : ℝ => y + -d₀N N) := by fun_prop
    rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable (hmeasXzero N)]
    rfl
  have hmapShiftPert (N : ℕ) :
      disorderLaw.map (fun ω => X N ω 1 - d₁N N) =
        (disorderLaw.map fun ω => X N ω 1).map (fun y => y + -d₁N N) := by
    have hm : Measurable (fun y : ℝ => y + -d₁N N) := by fun_prop
    rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable (hmeasXpert N)]
    rfl
  have hmapShiftSum (N : ℕ) :
      disorderLaw.map (fun ω => X N ω 0 + X N ω 1 - (d₀N N + d₁N N)) =
        (disorderLaw.map fun ω => X N ω 0 + X N ω 1).map
          (fun y => y + -(d₀N N + d₁N N)) := by
    have hm : Measurable (fun y : ℝ => y + -(d₀N N + d₁N N)) := by fun_prop
    rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable (hmeasXsum N)]
    rfl
  have hfiniteZero (N : ℕ) (hN : 0 < N) :
      IsEhrhardType (disorderLaw.map fun ω => X N ω 0) := by
    simpa [X, hTerminal] using
      isEhrhardType_integral_heatStartLogProfile ϑ hN hrt ψ hψ
  have hfinitePert (N : ℕ) (hN : 0 < N) :
      IsEhrhardType (disorderLaw.map fun ω => X N ω 1) := by
    simpa [X, hTerminal] using
      isEhrhardType_integral_heatStartLogProfile_general ϑ hN ψ hψ h₀
  have hfiniteSum (N : ℕ) (hN : 0 < N) :
      IsEhrhardType (disorderLaw.map fun ω => X N ω 0 + X N ω 1) := by
    simpa [X, hTerminal] using
      isEhrhardType_integral_heatStartLogProfile_pair ϑ hN hrt ψ hψ h₀
  have hfiniteZeroShift (N : ℕ) (hN : 0 < N) :
      IsEhrhardType (disorderLaw.map fun ω => X N ω 0 - d₀N N) := by
    rw [hmapShiftZero N]
    exact isEhrhardType_map_add_const (hfiniteZero N hN) (-d₀N N)
  have hfinitePertShift (N : ℕ) (hN : 0 < N) :
      IsEhrhardType (disorderLaw.map fun ω => X N ω 1 - d₁N N) := by
    rw [hmapShiftPert N]
    exact isEhrhardType_map_add_const (hfinitePert N hN) (-d₁N N)
  have hfiniteSumShift (N : ℕ) (hN : 0 < N) :
      IsEhrhardType (disorderLaw.map fun ω => X N ω 0 + X N ω 1 - (d₀N N + d₁N N)) := by
    rw [hmapShiftSum N]
    exact isEhrhardType_map_add_const (hfiniteSum N hN) (-(d₀N N + d₁N N))
  let ν₀ : ℕ → ProbabilityMeasure ℝ := fun k =>
    ⟨disorderLaw.map (fun ω => X (k + 1) ω 0 - d₀N (k + 1)), inferInstance⟩
  let ν₀' : ProbabilityMeasure ℝ := ⟨P.map (fun ω => L ω 0 - d₀), inferInstance⟩
  have hweak₀ : Tendsto ν₀ atTop (𝓝 ν₀') := by
    have h := hTIDzero.tendsto.comp (tendsto_add_atTop_nat 1)
    apply Tendsto.congr' (Filter.Eventually.of_forall fun k => ?_) h
    apply Subtype.ext
    rfl
  have hEhrhard₀ (k : ℕ) : IsEhrhardType (ν₀ k : Measure ℝ) := by
    simpa [ν₀, ProbabilityMeasure.coe_mk] using hfiniteZeroShift (k + 1) (by omega)
  have hlimit₀ := Provider.ehrhardType_weakClosure ν₀ ν₀' hweak₀ hEhrhard₀
  have hmapLimit₀ : P.map (avgLogField P Z r t ψ (fun _ => (1 : ℝ))) =
      P.map (fun ω => L ω 0 - d₀) := by
    apply Measure.map_congr
    exact hcenter₀'
  have hEzero : IsEhrhardType
      (P.map (avgLogField P Z r t ψ (fun _ => (1 : ℝ)))) := by
    rw [hmapLimit₀]
    simpa [ν₀', ProbabilityMeasure.coe_mk] using hlimit₀
  let XpertOne : ℕ → Disorder → Fin 1 → ℝ := fun N ω _ => X N ω 1
  let LpertOne : Ω → Fin 1 → ℝ := fun ω _ => L ω 1
  let Dpert : ℕ → Fin 1 → ℝ := fun N _ => d₁N N
  let DpertLim : Fin 1 → ℝ := fun _ => d₁
  have hrawPert : TendstoInDistribution XpertOne atTop LpertOne
      (fun _ => disorderLaw) P := by
    have h := hraw.continuous_comp
      (g := fun v : Fin 2 → ℝ => fun _ : Fin 1 => v 1) (by fun_prop)
    simpa [XpertOne, LpertOne, Function.comp_def] using h
  have hDpert : Tendsto Dpert atTop (𝓝 DpertLim) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa [Dpert, DpertLim] using hd₁N
  have hshiftPert := tendstoInDistribution_sub_tendsto
    XpertOne LpertOne Dpert DpertLim hrawPert hDpert
  have hTIDpert : TendstoInDistribution
      (fun N ω => X N ω 1 - d₁N N) atTop (fun ω => L ω 1 - d₁)
      (fun _ => disorderLaw) P := by
    have h := hshiftPert.continuous_comp (continuous_apply (0 : Fin 1))
    simpa [XpertOne, LpertOne, Dpert, DpertLim, Function.comp_def] using h
  let ν₁ : ℕ → ProbabilityMeasure ℝ := fun k =>
    ⟨disorderLaw.map (fun ω => X (k + 1) ω 1 - d₁N (k + 1)), inferInstance⟩
  let ν₁' : ProbabilityMeasure ℝ := ⟨P.map (fun ω => L ω 1 - d₁), inferInstance⟩
  have hweak₁ : Tendsto ν₁ atTop (𝓝 ν₁') := by
    have h := hTIDpert.tendsto.comp (tendsto_add_atTop_nat 1)
    apply Tendsto.congr' (Filter.Eventually.of_forall fun k => ?_) h
    apply Subtype.ext
    rfl
  have hEhrhard₁ (k : ℕ) : IsEhrhardType (ν₁ k : Measure ℝ) := by
    simpa [ν₁, ProbabilityMeasure.coe_mk] using hfinitePertShift (k + 1) (by omega)
  have hlimit₁ := Provider.ehrhardType_weakClosure ν₁ ν₁' hweak₁ hEhrhard₁
  have hmapLimit₁ : P.map (avgLogField P Z r t ψ f) =
      P.map (fun ω => L ω 1 - d₁) := by
    apply Measure.map_congr
    exact hcenter₁'
  have hEpert : IsEhrhardType (P.map (avgLogField P Z r t ψ f)) := by
    rw [hmapLimit₁]
    simpa [ν₁', ProbabilityMeasure.coe_mk] using hlimit₁
  let νsum : ℕ → ProbabilityMeasure ℝ := fun k =>
    ⟨disorderLaw.map (fun ω => X (k + 1) ω 0 + X (k + 1) ω 1 -
      (d₀N (k + 1) + d₁N (k + 1))), inferInstance⟩
  let νsum' : ProbabilityMeasure ℝ :=
    ⟨P.map (fun ω => L ω 0 + L ω 1 - (d₀ + d₁)), inferInstance⟩
  have hweakSum : Tendsto νsum atTop (𝓝 νsum') := by
    have h := hTIDsum.tendsto.comp (tendsto_add_atTop_nat 1)
    apply Tendsto.congr' (Filter.Eventually.of_forall fun k => ?_) h
    apply Subtype.ext
    rfl
  have hEhrhardSum (k : ℕ) : IsEhrhardType (νsum k : Measure ℝ) := by
    simpa [νsum, ProbabilityMeasure.coe_mk] using
      hfiniteSumShift (k + 1) (by omega)
  have hlimitSum := Provider.ehrhardType_weakClosure νsum νsum' hweakSum hEhrhardSum
  have hmapLimitSum :
      P.map (fun ω => avgLogField P Z r t ψ (fun _ => (1 : ℝ)) ω +
        avgLogField P Z r t ψ f ω) =
      P.map (fun ω => L ω 0 + L ω 1 - (d₀ + d₁)) := by
    apply Measure.map_congr
    filter_upwards [hcenter₀', hcenter₁'] with ω hω₀ hω₁
    rw [hω₀, hω₁]
    ring
  have hEsum : IsEhrhardType
      (P.map fun ω => avgLogField P Z r t ψ (fun _ => (1 : ℝ)) ω +
        avgLogField P Z r t ψ f ω) := by
    rw [hmapLimitSum]
    simpa [νsum', ProbabilityMeasure.coe_mk] using hlimitSum
  have hmeasF : AEMeasurable (avgLogField P Z r t ψ f) P := by
    rw [hfieldEq]
    exact hmeas₁
  exact ⟨hmeasF, hEpert, hEsum⟩

end Critical2DKPZ.NonGaussian

end
