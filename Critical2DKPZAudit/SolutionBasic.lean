/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! Gaussian polymers, critical stochastic heat flows and local negative Sobolev spaces provide the definitions for Theorem 1.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZAudit

/-- The square lattice. -/
@[reducible] def Site := Fin 2 → ℤ

/-- The four signed coordinate steps of the planar simple symmetric walk. -/
def srwStep : Fin 4 → Site :=
  ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]]

/-- The position of a planar walk after a specified initial segment of its steps. -/
def walkPosition (w : Site) {n : ℕ} (s : Fin n → Fin 4) (j : ℕ) : Site :=
  w + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), srwStep (s i)

/-- The transition probability of the planar simple symmetric walk. -/
def srwKernel (n : ℕ) (z : Site) : ℝ :=
  ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * if walkPosition 0 s n = z then 1 else 0

/-- The expected overlap of two planar simple walks up to the lattice horizon. -/
def replicaOverlap (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, srwKernel (2 * n) 0

/-- The critical-window disorder variance determined by the replica overlap and parameter. -/
def criticalSigmaSq (ϑ : ℝ) (N : ℕ) : ℝ :=
  (1 + ϑ / Real.log N) / replicaOverlap N

/-- The nonnegative critical disorder strength, defined from the critical-window variance. -/
def criticalBeta (ϑ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (1 + criticalSigmaSq ϑ N))

/-- The real disorder field indexed by nonnegative lattice times and planar lattice sites. -/
@[reducible] def Disorder := ℕ × Site → ℝ

/-- The product law of independent standard Gaussian disorder coordinates. -/
def disorderLaw : Measure Disorder :=
  Measure.infinitePi fun _ : ℕ × Site => gaussianReal 0 1

set_option linter.defProp false in
/-- The Gaussian disorder product law is a probability measure. -/
@[reducible, instance] def disorderLaw_isProbabilityMeasure : IsProbabilityMeasure disorderLaw :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun _ : ℕ × Site => gaussianReal 0 1))

/-- The Euclidean plane. -/
@[reducible] def Plane := EuclideanSpace ℝ (Fin 2)

/-- Real distributions on the Euclidean plane. -/
@[reducible] def Distr := Distribution (⊤ : Opens Plane) ℝ ⊤

/-- The even upper approximation to a nonnegative lattice time. -/
def evenCeil (t : ℝ) : ℕ :=
  2 * ⌈t / 2⌉₊

/-- The planar heat density with covariance equal to its positive time. -/
def heatKernel (u : ℝ) (z : Plane) : ℝ :=
  (2 * Real.pi * u)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * u))

/-- The SHF measure paired against separate initial and terminal functions. -/
def shfPairing {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (s t : ℝ)
    (f g : Plane → ℝ) (ω : Ω) : ℝ :=
  ∫ p, f p.1 * g p.2 ∂(Z s t ω)

/-- The centered temporal regularization of the log-SHF with initial height. -/
def kpzRegularized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) :
    ℝ :=
  Real.log (shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y)) (fun y => heatKernel δ (y - x)) ω) -
    ∫ ω', Real.log (shfPairing Z 0 (t - δ) (fun _ => 1) (fun y => heatKernel δ y) ω') ∂P

/-- Real smooth compactly supported functions on the plane. -/
@[reducible] def TestFn := TestFunction (⊤ : Opens Plane) ℝ ⊤

/-- The KPZ field characterized by convergence in probability of regularized test pairings. -/
def IsCriticalKPZ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn),
    TendstoInMeasure P (fun δ ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) (nhdsWithin 0 (Set.Ioi 0))
      (fun ω => H t h₀ ω φ)

/-- A nearest even lattice point, with rounding ties chosen towards positive infinity. -/
def nearestEven (x : Plane) : Site :=
  let a := round ((x 0 + x 1) / 2)
  let b := round ((x 0 - x 1) / 2)
  ![a + b, a - b]

/-- The nearest even lattice representative of a diffusively rescaled planar point. -/
def latticePoint (N : ℕ) (x : Plane) : Site :=
  nearestEven (Real.sqrt (N / 2) • x)

/-- The lattice polymer partition function with specified initial and terminal sites. -/
def pointToPoint (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) : ℝ :=
  ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
    Real.exp (∑ j ∈ Finset.Icc 1 n, (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2)) *
    if walkPosition w s n = z then 1 else 0

/-- The diffusively rescaled point-to-point polymer density. -/
def rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ) (p : Plane × Plane) (ω : Disorder) : ℝ :=
  (N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t) - evenCeil (N * s))
    (latticePoint N p.1) (latticePoint N p.2) ω

/-- The lattice polymer partition function with free terminal site. -/
def pointToPlane (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) : ℝ :=
  ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
    Real.exp (∑ j ∈ Finset.Icc 1 n, (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2))

/-- The diffusively rescaled polymer partition function with free terminal site. -/
def rescaledP2Plane (ϑ : ℝ) (N : ℕ) (s t : ℝ) (x : Plane) (ω : Disorder) : ℝ :=
  pointToPlane (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t) - evenCeil (N * s))
    (latticePoint N x) ω

/-- The critical SHF characterized by joint polymer pairing limits and locally finite marginals. -/
def IsCriticalSHF (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  (∀ s t, 0 ≤ s → s < t → Measurable (Z s t)) ∧
  (∀ s t, 0 ≤ s → s < t → ∀ᵐ ω ∂P,
    IsLocallyFiniteMeasure (Z s t ω) ∧ IsLocallyFiniteMeasure ((Z s t ω).map Prod.fst)) ∧
  ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i) →
    ∀ (φ : Fin k → C_c(Plane × Plane, ℝ)) (ψ : Fin k → C_c(Plane, ℝ)),
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ((∫ p, φ i p * rescaledP2P ϑ N (s i) (t i) p ω),
           (∫ x, ψ i x * rescaledP2Plane ϑ N (s i) (t i) x ω)))
        atTop
        (fun ω i => ((∫ p, φ i p ∂(Z (s i) (t i) ω)),
                     (∫ x, ψ i x ∂((Z (s i) (t i) ω).map Prod.fst))))
        (fun _ => disorderLaw) P

/-- The mean flat-initial lattice log-partition function at the spatial origin. -/
def kpzLatticeCentring (ϑ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Real.log (∫ y, rescaledP2P ϑ N 0 t (y, 0) ω) ∂disorderLaw

/-- The centered rescaled lattice log-partition field with bounded continuous initial height. -/
def kpzLattice (ϑ : ℝ) (N : ℕ) (t : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) : ℝ :=
  Real.log (∫ y, Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) - kpzLatticeCentring ϑ N t

/-- Distributions regarded as a carrier for the local negative Sobolev topology. -/
def LocNegSobolevTop (_s : ℝ) : Type := Distr

/-- The underlying distribution of a point in the local negative Sobolev carrier. -/
def LocNegSobolevTop.toDistr {s : ℝ} (S : LocNegSobolevTop s) : Distr := S

namespace TestFn

/-- A test function multiplied by the cosine of a Fourier phase. -/


def mulCos (χ : TestFn) (ξ : Plane) : TestFn where
  toFun x := χ x * Real.cos (inner ℝ ξ x)
  contDiff' := χ.contDiff.mul (Real.contDiff_cos.comp (innerSL ℝ ξ).contDiff)
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := fun _ _ => trivial

end TestFn

namespace TestFn

/-- A test function multiplied by the sine of a Fourier phase. -/


def mulSin (χ : TestFn) (ξ : Plane) : TestFn where
  toFun x := χ x * Real.sin (inner ℝ ξ x)
  contDiff' := χ.contDiff.mul (Real.contDiff_sin.comp (innerSL ℝ ξ).contDiff)
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := fun _ _ => trivial

end TestFn

/-- The squared localized negative Sobolev seminorm given by the Fourier integral. -/
def localNegSobolevSq (s : ℝ) (T : Distr) (χ : TestFn) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
    ∫⁻ ξ : Plane, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-s) *
      ((T (χ.mulCos ξ)) ^ 2 + (T (χ.mulSin ξ)) ^ 2))

/-- The topology generated by localized negative Sobolev balls. -/
@[reducible, instance] def LocNegSobolevTop.topologicalSpace (s : ℝ) : TopologicalSpace (LocNegSobolevTop s) :=
  TopologicalSpace.generateFrom
    {U | ∃ (T : Distr) (χ : TestFn) (ε : ℝ≥0∞), 0 < ε ∧
      U = {S : LocNegSobolevTop s | localNegSobolevSq s (S.toDistr - T) χ < ε}}

/-- Finite tuples of distributions with their product local negative Sobolev topology. -/
def LocNegSobolevTuple (s : ℝ) (k : ℕ) : Type := Fin k → LocNegSobolevTop s

/-- The product of the localized negative Sobolev topologies. -/
@[reducible, instance] def LocNegSobolevTuple.topologicalSpace (s : ℝ) (k : ℕ) : TopologicalSpace (LocNegSobolevTuple s k) := Pi.topologicalSpace

/-- The Borel sigma-algebra of the tuple local negative Sobolev topology. -/
@[reducible, instance] def LocNegSobolevTuple.measurableSpace (s : ℝ) (k : ℕ) : MeasurableSpace (LocNegSobolevTuple s k) := borel _

set_option linter.defProp false in
/-- The tuple measurable space is the Borel sigma-algebra of its topology. -/
@[reducible, instance] def LocNegSobolevTuple.borelSpace (s : ℝ) (k : ℕ) : BorelSpace (LocNegSobolevTuple s k) := ⟨rfl⟩

/-- A distribution has finite localized negative Sobolev energy for every smooth test. -/
def MemLocalNegSobolev (s : ℝ) (T : Distr) : Prop :=
  ∀ χ : TestFn, localNegSobolevSq s T χ < ⊤

/-- The sigma-algebra generated by all nonnegative-time SHF coordinates. -/
@[reducible] def shfSigma {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : MeasurableSpace Ω :=
  ⨆ (s : ℝ) (t : ℝ) (_ : 0 ≤ s ∧ s < t), MeasurableSpace.comap (Z s t) inferInstance

/-- A finite tuple of distributions viewed in the local negative Sobolev topology. -/
def toLocNegSobolevTuple (s : ℝ) {k : ℕ} (T : Fin k → Distr) : LocNegSobolevTuple s k := T

end Critical2DKPZAudit

end
