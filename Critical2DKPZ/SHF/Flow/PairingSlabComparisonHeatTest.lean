/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.PairingSlabReplicaCoordinates
public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedCompactMomentLimit
public import Critical2DKPZ.SHF.Flow.SlabMeanKernelLimit
public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.Tsai.Cutoff

/-! Compact connector tests describe the second moments of slab pairings. -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Moments
open Critical2DKPZ.DeltaBose
open Critical2DKPZ.SHF.Tsai
open scoped Topology
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- A compact heat-connector test with cutoffs in the two middle coordinates. -/
def slabHeatCutoffConnectorTest (Φ : C_c(Plane × Plane, ℝ)) (v R : ℝ) :
    C_c(((Plane × Plane) × (Plane × Plane)), ℝ) := by
  let χ : C_c(Plane, ℝ) := ⟨⟨ballCutoff R, continuous_ballCutoff R⟩,
    hasCompactSupport_ballCutoff R⟩
  let f (q : (Plane × Plane) × (Plane × Plane)) : ℝ :=
    Φ (q.1.1, q.2.2) * heatKernel v (q.2.1 - q.1.2) * χ q.1.2 * χ q.2.1
  have hf : Continuous f := by
    dsimp [f]
    have hEndpoint : Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
        (q.1.1, q.2.2)) := by fun_prop
    have hMiddle : Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
        q.2.1 - q.1.2) := by fun_prop
    have hHeat : Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
        heatKernel v (q.2.1 - q.1.2)) :=
      (Critical2DKPZ.continuous_heatKernel v).comp hMiddle
    have hCutLeft : Continuous (fun q : (Plane × Plane) × (Plane × Plane) => χ q.1.2) :=
      χ.continuous.comp (continuous_snd.comp continuous_fst)
    have hCutRight : Continuous (fun q : (Plane × Plane) × (Plane × Plane) => χ q.2.1) :=
      χ.continuous.comp (continuous_fst.comp continuous_snd)
    exact (Φ.continuous.comp hEndpoint).mul hHeat |>.mul hCutLeft |>.mul hCutRight
  let A : Set Plane := Prod.fst '' tsupport (Φ : (Plane × Plane) → ℝ)
  let B : Set Plane := Prod.snd '' tsupport (Φ : (Plane × Plane) → ℝ)
  let C : Set Plane := tsupport (χ : Plane → ℝ)
  let K : Set ((Plane × Plane) × (Plane × Plane)) :=
    (A ×ˢ C) ×ˢ (C ×ˢ B)
  have hA : IsCompact A := Φ.hasCompactSupport.image continuous_fst
  have hB : IsCompact B := Φ.hasCompactSupport.image continuous_snd
  have hC : IsCompact C := χ.hasCompactSupport
  have hK : IsCompact K := (hA.prod hC).prod (hC.prod hB)
  refine ⟨⟨f, hf⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro q hq
  have hΦ : Φ (q.1.1, q.2.2) ≠ 0 := by
    intro hz
    apply hq
    simp [f, hz]
  have hχ₁ : χ q.1.2 ≠ 0 := by
    intro hz
    apply hq
    simp [f, hz]
  have hχ₂ : χ q.2.1 ≠ 0 := by
    intro hz
    apply hq
    simp [f, hz]
  change (q.1.1 ∈ A ∧ q.1.2 ∈ C) ∧ (q.2.1 ∈ C ∧ q.2.2 ∈ B)
  exact ⟨⟨⟨(q.1.1, q.2.2), subset_tsupport _ hΦ, rfl⟩,
      subset_tsupport _ hχ₁⟩,
    ⟨subset_tsupport _ hχ₂,
      ⟨(q.1.1, q.2.2), subset_tsupport _ hΦ, rfl⟩⟩⟩


/-- The heat-connector replica moment on separated polymer blocks converges to its kernel integral, with eventual integrability supplied by `eventually_slabSeparatedTensorMass_sq_bound`. -/
theorem tendsto_slabHeatCutoffConnectorMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {v : ℝ} (hv : 0 < v) (hvu : t + v < u)
    (Φ : C_c(Plane × Plane, ℝ)) (R : ℝ) :
    Tendsto
      (fun N => ∫ ω, ∫ q,
        slabReplicaSourceTest (slabHeatCutoffConnectorTest Φ v R) q ∂
          slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
            (polymerMeasure ϑ N (t + v) u ω) ∂disorderLaw)
      atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
        (t - s) (u - (t + v)) (slabReplicaSourceTest
          (slabHeatCutoffConnectorTest Φ v R)))) := by
  simpa [slabTwoBlockPiMeasure] using
    tendsto_slabSeparatedCompactIntegral ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst
      (by linarith : t < t + v) hvu
      (slabReplicaSourceTest (slabHeatCutoffConnectorTest Φ v R))

/-- The finite slab connector with compact middle cutoffs, before replica expansion. -/
def slabCutoffConnectorValue (ϑ : ℝ) (N : ℕ) (t v R : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (a b : Plane × Plane) : ℝ :=
  Φ (a.1, b.2) * slabMeanKernel ϑ N t (t + v) a.2 b.1 *
    ballCutoff R a.2 * ballCutoff R b.1

/-- The limiting heat connector with the same compact middle cutoffs. -/
def slabHeatCutoffConnectorValue (v R : ℝ) (Φ : C_c(Plane × Plane, ℝ))
    (a b : Plane × Plane) : ℝ :=
  Φ (a.1, b.2) * heatKernel v (b.1 - a.2) * ballCutoff R a.2 * ballCutoff R b.1

/-- The finite slab replica integrand, with the two connectors paired across the replicas. -/
def slabCutoffReplicaValue (ϑ : ℝ) (N : ℕ) (t v R : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (q : Fin 4 → Plane × Plane) : ℝ :=
  slabCutoffConnectorValue ϑ N t v R Φ (q 0) (q 2) *
    slabCutoffConnectorValue ϑ N t v R Φ (q 1) (q 3)

/-- The heat replica integrand equals its compact endpoint test. -/
def slabHeatCutoffReplicaTest (v R : ℝ) (Φ : C_c(Plane × Plane, ℝ)) :
    C_c((Fin 4 → Plane × Plane), ℝ) :=
  slabReplicaSourceTest (slabHeatCutoffConnectorTest Φ v R)

/-- The heat replica test is the product of its two connector values. -/
theorem slabHeatCutoffReplicaTest_apply (v R : ℝ) (Φ : C_c(Plane × Plane, ℝ))
    (q : Fin 4 → Plane × Plane) :
    slabHeatCutoffReplicaTest v R Φ q =
      slabHeatCutoffConnectorValue v R Φ (q 0) (q 2) *
        slabHeatCutoffConnectorValue v R Φ (q 1) (q 3) := by
  simp [slabHeatCutoffReplicaTest, slabReplicaSourceTest,
    slabReplicaTensorTest, slabReplicaArrayHomeomorph, slabReplicaArrayEquiv,
    slabHeatCutoffConnectorTest, slabHeatCutoffConnectorValue]

/-- The slab connector converges uniformly on its compactly cut middle coordinates, with any
compact endpoint test as a multiplier. -/
theorem eventually_slabCutoffConnector_uniform (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {v : ℝ} (hv : 0 < v) (R : ℝ) (Φ : C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ a b : Plane × Plane,
      |slabCutoffConnectorValue ϑ N t v R Φ a b -
        slabHeatCutoffConnectorValue v R Φ a b| < ε := by
  intro ε hε
  let χ : C_c(Plane, ℝ) := ⟨⟨ballCutoff R, continuous_ballCutoff R⟩,
    hasCompactSupport_ballCutoff R⟩
  let K : Set (Plane × Plane) := tsupport χ ×ˢ tsupport χ
  have hK : IsCompact K := χ.hasCompactSupport.prod χ.hasCompactSupport
  obtain ⟨M₀, hM₀⟩ := Φ.hasCompactSupport.exists_bound_of_continuousOn
    Φ.continuous.continuousOn
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦbound (x y : Plane) : |Φ (x, y)| ≤ M := by
    by_cases hxy : (x, y) ∈ tsupport (Φ : (Plane × Plane) → ℝ)
    · have hnorm : ‖Φ (x, y)‖ ≤ M₀ := hM₀ (x, y) hxy
      rw [Real.norm_eq_abs] at hnorm
      exact hnorm.trans (le_max_left _ _)
    · have hz : Φ (x, y) = 0 := image_eq_zero_of_notMem_tsupport hxy
      simp [hz, M]
  let δ := ε / (1 + M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδM : M * δ < ε := by
    have hden : 0 < 1 + M := by positivity
    have hMlt : M < 1 + M := by linarith
    calc
      M * δ < (1 + M) * δ := mul_lt_mul_of_pos_right hMlt hδ
      _ = ε := by dsimp [δ]; field_simp
  obtain hkernel := tendsto_slabMeanKernel_uniformOn_compact ϑ ht hv K hK δ hδ
  filter_upwards [hkernel] with N hN
  intro a b
  by_cases hleft : ballCutoff R a.2 = 0
  · simpa [slabCutoffConnectorValue, slabHeatCutoffConnectorValue, hleft] using hε
  by_cases hright : ballCutoff R b.1 = 0
  · simpa [slabCutoffConnectorValue, slabHeatCutoffConnectorValue, hright] using hε
  have ha : a.2 ∈ tsupport χ := by
    apply subset_tsupport χ
    simpa [χ] using hleft
  have hb : b.1 ∈ tsupport χ := by
    apply subset_tsupport χ
    simpa [χ] using hright
  have hkernel' := hN a.2 b.1 ⟨ha, hb⟩
  have hleft₀ : 0 ≤ ballCutoff R a.2 := (ballCutoff_mem_Icc R a.2).1
  have hleft₁ : ballCutoff R a.2 ≤ 1 := (ballCutoff_mem_Icc R a.2).2
  have hright₀ : 0 ≤ ballCutoff R b.1 := (ballCutoff_mem_Icc R b.1).1
  have hright₁ : ballCutoff R b.1 ≤ 1 := (ballCutoff_mem_Icc R b.1).2
  have hcuts : |ballCutoff R a.2 * ballCutoff R b.1| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hleft₀ hright₀)]
    calc
      ballCutoff R a.2 * ballCutoff R b.1 ≤ ballCutoff R a.2 * 1 :=
        mul_le_mul_of_nonneg_left hright₁ hleft₀
      _ = ballCutoff R a.2 := by ring
      _ ≤ 1 := hleft₁
  have hfactor :
      slabCutoffConnectorValue ϑ N t v R Φ a b -
        slabHeatCutoffConnectorValue v R Φ a b =
      Φ (a.1, b.2) *
        (slabMeanKernel ϑ N t (t + v) a.2 b.1 - heatKernel v (b.1 - a.2)) *
          (ballCutoff R a.2 * ballCutoff R b.1) := by
    simp [slabCutoffConnectorValue, slabHeatCutoffConnectorValue]
    ring
  rw [hfactor, abs_mul, abs_mul]
  calc
    |Φ (a.1, b.2)| *
        |slabMeanKernel ϑ N t (t + v) a.2 b.1 - heatKernel v (b.1 - a.2)| *
          |ballCutoff R a.2 * ballCutoff R b.1|
      ≤ M * δ * 1 := by
        apply mul_le_mul
        · exact mul_le_mul (hΦbound _ _) (le_of_lt hkernel') (abs_nonneg _) hM
        · exact hcuts
        · positivity
        · positivity
    _ < ε := by simpa using hδM

/-- The four-replica slab integrand converges uniformly to its compact heat test. -/
theorem eventually_slabCutoffReplica_uniform (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {v : ℝ} (hv : 0 < v) (R : ℝ) (Φ : C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ q : Fin 4 → Plane × Plane,
      |slabCutoffReplicaValue ϑ N t v R Φ q - slabHeatCutoffReplicaTest v R Φ q| < ε := by
  intro ε hε
  let χ : C_c(Plane, ℝ) := ⟨⟨ballCutoff R, continuous_ballCutoff R⟩,
    hasCompactSupport_ballCutoff R⟩
  let K : Set (Plane × Plane) := tsupport χ ×ˢ tsupport χ
  have hK : IsCompact K := χ.hasCompactSupport.prod χ.hasCompactSupport
  let D : Set Plane := (fun p : Plane × Plane => p.2 - p.1) '' K
  have hD : IsCompact D := hK.image (by fun_prop)
  obtain ⟨C₀, hC₀⟩ := hD.exists_bound_of_continuousOn
    (Critical2DKPZ.continuous_heatKernel v).continuousOn
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  obtain ⟨M₀, hM₀⟩ := Φ.hasCompactSupport.exists_bound_of_continuousOn
    Φ.continuous.continuousOn
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦbound (x y : Plane) : |Φ (x, y)| ≤ M := by
    by_cases hxy : (x, y) ∈ tsupport (Φ : (Plane × Plane) → ℝ)
    · have hnorm : ‖Φ (x, y)‖ ≤ M₀ := hM₀ (x, y) hxy
      rw [Real.norm_eq_abs] at hnorm
      exact hnorm.trans (le_max_left _ _)
    · have hz : Φ (x, y) = 0 := image_eq_zero_of_notMem_tsupport hxy
      simp [hz, M]
  have hHeatBound (a b : Plane × Plane) :
      |slabHeatCutoffConnectorValue v R Φ a b| ≤ M * C := by
    by_cases hleft : ballCutoff R a.2 = 0
    · simpa [slabHeatCutoffConnectorValue, hleft] using mul_nonneg hM hC
    by_cases hright : ballCutoff R b.1 = 0
    · simpa [slabHeatCutoffConnectorValue, hright] using mul_nonneg hM hC
    have ha : a.2 ∈ tsupport χ := by
      apply subset_tsupport χ
      simpa [χ] using hleft
    have hb : b.1 ∈ tsupport χ := by
      apply subset_tsupport χ
      simpa [χ] using hright
    have hdiff : b.1 - a.2 ∈ D := ⟨(a.2, b.1), ⟨ha, hb⟩, rfl⟩
    have hkernel : |heatKernel v (b.1 - a.2)| ≤ C := by
      have hnorm := hC₀ (b.1 - a.2) hdiff
      rw [Real.norm_eq_abs] at hnorm
      exact hnorm.trans (le_max_left _ _)
    have hcut₀ : 0 ≤ ballCutoff R a.2 := (ballCutoff_mem_Icc R a.2).1
    have hcut₁ : ballCutoff R a.2 ≤ 1 := (ballCutoff_mem_Icc R a.2).2
    have hcut'₀ : 0 ≤ ballCutoff R b.1 := (ballCutoff_mem_Icc R b.1).1
    have hcut'₁ : ballCutoff R b.1 ≤ 1 := (ballCutoff_mem_Icc R b.1).2
    have hcutAbs : |ballCutoff R a.2| ≤ 1 := by
      rw [abs_of_nonneg hcut₀]
      exact hcut₁
    have hcut'Abs : |ballCutoff R b.1| ≤ 1 := by
      rw [abs_of_nonneg hcut'₀]
      exact hcut'₁
    have hbase : |Φ (a.1, b.2)| * |heatKernel v (b.1 - a.2)| ≤ M * C :=
      mul_le_mul (hΦbound _ _) hkernel (abs_nonneg _) hM
    rw [slabHeatCutoffConnectorValue]
    calc
      |Φ (a.1, b.2) * heatKernel v (b.1 - a.2) * ballCutoff R a.2 * ballCutoff R b.1|
          = |Φ (a.1, b.2)| * |heatKernel v (b.1 - a.2)| *
            |ballCutoff R a.2| * |ballCutoff R b.1| := by
              simp only [abs_mul]
      _ ≤ M * C * 1 * 1 := by gcongr
      _ = M * C := by ring
  let B := M * C + 1
  let δ := ε / (1 + B + M * C)
  have hδ : 0 < δ := by dsimp [δ, B]; positivity
  have hfac : δ * (B + M * C) < ε := by
    change (ε / (1 + B + M * C)) * (B + M * C) < ε
    have hden : 0 < 1 + B + M * C := by positivity
    have hnum : B + M * C < 1 + B + M * C := by linarith
    calc
      (ε / (1 + B + M * C)) * (B + M * C) <
          (ε / (1 + B + M * C)) * (1 + B + M * C) :=
        mul_lt_mul_of_pos_left hnum (div_pos hε hden)
      _ = ε := by field_simp
  obtain hclose := eventually_slabCutoffConnector_uniform ϑ ht hv R Φ δ hδ
  obtain hone := eventually_slabCutoffConnector_uniform ϑ ht hv R Φ 1 (by norm_num)
  filter_upwards [hclose, hone] with N hclose hone q
  rw [slabHeatCutoffReplicaTest_apply]
  let a₀ := slabCutoffConnectorValue ϑ N t v R Φ (q 0) (q 2)
  let a₁ := slabCutoffConnectorValue ϑ N t v R Φ (q 1) (q 3)
  let b₀ := slabHeatCutoffConnectorValue v R Φ (q 0) (q 2)
  let b₁ := slabHeatCutoffConnectorValue v R Φ (q 1) (q 3)
  have hdiff₀ : |a₀ - b₀| < δ := hclose _ _
  have hdiff₁ : |a₁ - b₁| < δ := hclose _ _
  have hone₁ : |a₁ - b₁| < 1 := hone _ _
  have hbound₁ : |a₁| ≤ B := by
    have h := abs_add_le (a₁ - b₁) b₁
    have hEq : a₁ = (a₁ - b₁) + b₁ := by ring
    rw [hEq]
    calc
      |(a₁ - b₁) + b₁| ≤ |a₁ - b₁| + |b₁| := abs_add_le _ _
      _ ≤ 1 + M * C := add_le_add (le_of_lt hone₁) (hHeatBound _ _)
      _ = B := by dsimp [B]; ring
  have hbound₀ : |b₀| ≤ M * C := hHeatBound _ _
  have hproduct : a₀ * a₁ - b₀ * b₁ = (a₀ - b₀) * a₁ + b₀ * (a₁ - b₁) := by ring
  rw [show slabCutoffReplicaValue ϑ N t v R Φ q = a₀ * a₁ by rfl,
    hproduct]
  calc
    |(a₀ - b₀) * a₁ + b₀ * (a₁ - b₁)| ≤
        |a₀ - b₀| * |a₁| + |b₀| * |a₁ - b₁| := by
          calc
            _ ≤ |(a₀ - b₀) * a₁| + |b₀ * (a₁ - b₁)| := abs_add_le _ _
            _ = _ := by simp [abs_mul]
    _ ≤ δ * B + M * C * δ := by
      apply add_le_add
      · exact mul_le_mul (le_of_lt hdiff₀) hbound₁ (abs_nonneg _) (le_of_lt hδ)
      · exact mul_le_mul hbound₀ (le_of_lt hdiff₁) (abs_nonneg _)
          (mul_nonneg hM hC)
    _ = δ * (B + M * C) := by ring
    _ < ε := hfac

end Critical2DKPZ.SHF.Flow

end
