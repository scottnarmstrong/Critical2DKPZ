/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.LatticeReversalTerminalClockError
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.SHF.Symmetries.DenseTransportHelpers
public import Critical2DKPZ.SHF.Tsai.FiniteVectorConvergence
public import Critical2DKPZ.PolymerCalculus.TimeReversal
import Mathlib.Tactic

/-! # Lattice reversal for critical stochastic heat flows -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open Critical2DKPZ.SHF.Moments
open scoped CompactlySupported ENNReal Topology

namespace Critical2DKPZ.SHF.Symmetries

private def clockPairing (ϑ : ℝ) (N a b : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) : ℝ :=
  ∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω

private def clockStartEndpointError (ϑ : ℝ) (N a b : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) : ℝ :=
  ∫ p, φ p * ((Real.exp (criticalBeta ϑ N * ω (a, latticePoint N p.1)) - 1) *
    rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω)

private theorem tendstoInMeasure_add_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0))
    (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun N ω => f N ω + g N ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro δ hδ
  have hf' := (tendstoInMeasure_iff_measureReal_dist).mp hf
  have hg' := (tendstoInMeasure_iff_measureReal_dist).mp hg
  have hA := hf' (δ / 2) (by positivity)
  have hB := hg' (δ / 2) (by positivity)
  let A (N : ℕ) := {ω | δ / 2 ≤ dist (f N ω) (0 : ℝ)}
  let B (N : ℕ) := {ω | δ / 2 ≤ dist (g N ω) (0 : ℝ)}
  have hsubset (N : ℕ) :
      {ω | δ ≤ dist (f N ω + g N ω) (0 : ℝ)} ⊆ A N ∪ B N := by
    intro ω hω
    by_contra hnot
    have hnotA : ¬ δ / 2 ≤ dist (f N ω) (0 : ℝ) := by
      intro h
      exact hnot (Or.inl h)
    have hnotB : ¬ δ / 2 ≤ dist (g N ω) (0 : ℝ) := by
      intro h
      exact hnot (Or.inr h)
    have hfa : |f N ω| < δ / 2 := by
      have h := lt_of_not_ge hnotA
      simpa [Real.dist_eq] using h
    have hgb : |g N ω| < δ / 2 := by
      have h := lt_of_not_ge hnotB
      simpa [Real.dist_eq] using h
    have hsum : δ ≤ |f N ω + g N ω| := by simpa [Real.dist_eq] using hω
    have htriangle := abs_add_le (f N ω) (g N ω)
    linarith
  have hbound (N : ℕ) :
      μ.real {ω | δ ≤ dist (f N ω + g N ω) (0 : ℝ)} ≤
        μ.real (A N) + μ.real (B N) :=
    (measureReal_mono (hsubset N)).trans (measureReal_union_le _ _)
  have hsum : Tendsto (fun N => μ.real (A N) + μ.real (B N)) atTop (𝓝 0) := by
    simpa [A, B] using hA.add hB
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun N => measureReal_nonneg)
    (Filter.Eventually.of_forall hbound)

private theorem tendstoInMeasure_neg_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun N ω => -f N ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hf ⊢
  intro δ hδ
  have hevent (N : ℕ) :
      μ.real {ω | δ ≤ dist (-f N ω) (0 : ℝ)} =
        μ.real {ω | δ ≤ dist (f N ω) (0 : ℝ)} := by
    congr 1
    ext ω
    simp
  exact (hf δ hδ).congr fun N => (hevent N).symm

private def reversalDisorderEquiv (L : ℕ) : Disorder ≃ᵐ Disorder :=
  MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
    (PolymerCalculus.timeReversalIndex L).symm

private theorem reversalDisorderEquiv_eq (L : ℕ) :
    Gaussian.reindexDisorder (PolymerCalculus.timeReversalIndex L) =
      reversalDisorderEquiv L := by
  funext ω p
  change ω (PolymerCalculus.timeReversalIndex L p) = reversalDisorderEquiv L ω p
  symm
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (PolymerCalculus.timeReversalIndex L).symm (β := fun _ : ℕ × Site => ℝ)
    ω (PolymerCalculus.timeReversalIndex L p)
  simpa [reversalDisorderEquiv] using h

private theorem measurePreserving_reversalDisorderEquiv (L : ℕ) :
    MeasurePreserving (reversalDisorderEquiv L) disorderLaw disorderLaw := by
  rw [← reversalDisorderEquiv_eq L]
  exact PolymerCalculus.measurePreserving_reversedDisorder L


/-- Reversing disorder samples preserves the in-measure convergence of endpoint errors,
including when the reflection clock changes with the scale. -/
private theorem tendstoInMeasure_reversedClockStartEndpointError
    (ϑ ε : ℝ) (hε : 0 < ε) (a b L : ℕ → ℕ)
    (ha : ∀ N, Even (a N)) (hb : ∀ N, Even (b N))
    (hgap : ∀ᶠ N : ℕ in atTop,
      ε * (N : ℝ) ≤ ((b N - a N : ℕ) : ℝ))
    (φ : C_c(Plane × Plane, ℝ)) :
    TendstoInMeasure disorderLaw
      (fun N ω => clockStartEndpointError ϑ N (a N) (b N) φ
        (PolymerCalculus.reversedDisorder (L N) ω))
      atTop (fun _ => 0) := by
  classical
  obtain ⟨C, hC, hkernelMass⟩ :=
    Critical2DKPZ.SHF.Symmetries.exists_tsum_compactAbs_cellKernel_bound hε φ
  let mass : ℝ := ∫ p, compactAbs φ p
  let root (N : ℕ) := Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
    2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1)
  let upper (N : ℕ) := root N * (C * mass)
  let err (N : ℕ) (ω : Disorder) :=
    clockStartEndpointError ϑ N (a N) (b N) φ ω
  have hbase (N : ℕ) (hN : 0 < N)
      (hgapN : ε * (N : ℝ) ≤ ((b N - a N : ℕ) : ℝ)) :
      Integrable (err N) disorderLaw ∧
        (∫ ω, |err N ω| ∂disorderLaw) ≤ upper N := by
    have hba : a N ≤ b N := by
      by_contra h
      have hlt : b N < a N := Nat.lt_of_not_ge h
      have hzero : b N - a N = 0 := Nat.sub_eq_zero_of_le hlt.le
      rw [hzero] at hgapN
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hpos : 0 < ε * (N : ℝ) := mul_pos hε hNreal
      have hgapZero : ε * (N : ℝ) ≤ 0 := by simpa using hgapN
      exact (not_le_of_gt hpos) hgapZero
    have hclockA := evenCeil_scaled_nat_div hN (ha N)
    have hclockB := evenCeil_scaled_nat_div hN (hb N)
    have hkernel := hkernelMass N (b N - a N) hgapN
    have hkernel' : (∑' q : Site × Site, cellTestWeight N (compactAbs φ) q.1 q.2 *
        srwKernel (evenCeil ((N : ℝ) * ((b N : ℝ) / N)) -
          evenCeil ((N : ℝ) * ((a N : ℝ) / N))) (q.2 - q.1)) ≤ C * mass := by
      simpa only [hclockA, hclockB, sub_zero, mass] using hkernel
    have hbound := integral_abs_pairing_startEndpoint_error_le ϑ φ C hkernel'
    have hmain : Integrable (fun ω => clockStartEndpointError ϑ N (a N) (b N) φ ω)
        disorderLaw := by
      simpa [clockStartEndpointError, hclockA, hclockB] using hbound.1
    have hmainBound :
        (∫ ω, |clockStartEndpointError ϑ N (a N) (b N) φ ω| ∂disorderLaw) ≤ upper N := by
      simpa [clockStartEndpointError, hclockA, hclockB, upper, root, mass,
        ← mul_assoc] using hbound.2
    exact ⟨by simpa [err] using hmain, by simpa [err] using hmainBound⟩
  have hroot : Tendsto root atTop (𝓝 0) := tendsto_expPairingError_root ϑ
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hroot.mul_const (C * mass)
  have hbound : ∀ᶠ N : ℕ in atTop, (∫ ω, |err N ω| ∂disorderLaw) ≤ upper N := by
    filter_upwards [eventually_gt_atTop 0, hgap] with N hN hgapN
    exact (hbase N hN hgapN).2
  let revErr (N : ℕ) (ω : Disorder) :=
    err N (PolymerCalculus.reversedDisorder (L N) ω)
  have hrevInt : ∀ᶠ N : ℕ in atTop, Integrable (fun ω => |revErr N ω|) disorderLaw := by
    filter_upwards [eventually_gt_atTop 0, hgap] with N hN hgapN
    let e := reversalDisorderEquiv (L N)
    have hMP := measurePreserving_reversalDisorderEquiv (L N)
    have heq : (e : Disorder → Disorder) =
        PolymerCalculus.reversedDisorder (L N) := by
      change (reversalDisorderEquiv (L N) : Disorder → Disorder) =
        Gaussian.reindexDisorder (PolymerCalculus.timeReversalIndex (L N))
      exact (reversalDisorderEquiv_eq (L N)).symm
    have heq' : (reversalDisorderEquiv (L N) : Disorder → Disorder) =
        PolymerCalculus.reversedDisorder (L N) := heq
    have h := hMP.integrable_comp_of_integrable ((hbase N hN hgapN).1.norm)
    change Integrable (fun ω => ‖err N (reversalDisorderEquiv (L N) ω)‖)
      disorderLaw at h
    simpa only [Real.norm_eq_abs, heq', revErr] using h
  have hrevBound : ∀ᶠ N : ℕ in atTop,
      (∫ ω, |revErr N ω| ∂disorderLaw) ≤ upper N := by
    filter_upwards [eventually_gt_atTop 0, hgap] with N hN hgapN
    let e := reversalDisorderEquiv (L N)
    have hMP := measurePreserving_reversalDisorderEquiv (L N)
    have heq : (e : Disorder → Disorder) =
        PolymerCalculus.reversedDisorder (L N) := by
      change (reversalDisorderEquiv (L N) : Disorder → Disorder) =
        Gaussian.reindexDisorder (PolymerCalculus.timeReversalIndex (L N))
      exact (reversalDisorderEquiv_eq (L N)).symm
    have hIntEq :
        (∫ ω, |err N (e ω)| ∂disorderLaw) =
          ∫ ω, |err N ω| ∂disorderLaw := by
      simpa only [Function.comp_apply] using
        (hMP.integral_comp' (fun ω => |err N ω|))
    have hrewrite :
        (fun ω => |revErr N ω|) = fun ω => |err N (e ω)| := by
      funext ω
      simp [revErr, ← heq]
    rw [hrewrite, hIntEq]
    exact (hbase N hN hgapN).2
  have hL1 : Tendsto (fun N => ∫ ω, |revErr N ω| ∂disorderLaw) atTop (𝓝 0) := by
    have hnonneg (N : ℕ) : 0 ≤ ∫ ω, |revErr N ω| ∂disorderLaw :=
      integral_nonneg fun ω => abs_nonneg (revErr N ω)
    exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hrevBound hupper
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro δ hδ
  have hmarkov : ∀ᶠ N : ℕ in atTop,
      disorderLaw.real {ω | δ ≤ dist (revErr N ω) (0 : ℝ)} ≤
        (∫ ω, |revErr N ω| ∂disorderLaw) / δ := by
    filter_upwards [eventually_gt_atTop 0, hgap, hrevInt] with N hN hgapN hInt
    exact measureReal_dist_le_integral_abs disorderLaw (revErr N) hInt hδ
  have hdiv : Tendsto (fun N => (∫ ω, |revErr N ω| ∂disorderLaw) / δ)
      atTop (𝓝 0) := by simpa using hL1.div_const δ
  have hres : Tendsto (fun N : ℕ => disorderLaw.real
      {ω | δ ≤ dist (revErr N ω) (0 : ℝ)}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [zero_div] using hdiv)
      (Filter.Eventually.of_forall fun N => measureReal_nonneg)
    exact hmarkov
  exact hres

private theorem aemeasurable_clockPairing (ϑ : ℝ) (N a b : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) :
    AEMeasurable (fun ω => clockPairing ϑ N a b φ ω) disorderLaw := by
  have hprod := Critical2DKPZ.SHF.Moments.integrable_pairing_rescaledP2P
    ϑ N ((a : ℝ) / N) ((b : ℝ) / N) φ.continuous φ.hasCompactSupport
  have hswap := hprod.swap
  have hI := hswap.integral_prod_left
  change Integrable (fun ω : Disorder => ∫ p : Plane × Plane,
      (φ : Plane × Plane → ℝ) p *
        rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω) disorderLaw at hI
  exact hI.aemeasurable

private theorem tendstoInMeasure_reversal_comp
    (L : ℕ → ℕ) {f : ℕ → Disorder → ℝ}
    (hf : ∀ N, AEMeasurable (f N) disorderLaw)
    (hlim : TendstoInMeasure disorderLaw f atTop (fun _ => 0)) :
    TendstoInMeasure disorderLaw
      (fun N ω => f N (PolymerCalculus.reversedDisorder (L N) ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hlim ⊢
  intro δ hδ
  have hmeasure (N : ℕ) :
      disorderLaw.real {ω | δ ≤ dist
        (f N (PolymerCalculus.reversedDisorder (L N) ω)) (0 : ℝ)} =
      disorderLaw.real {ω | δ ≤ dist (f N ω) (0 : ℝ)} := by
    let e := reversalDisorderEquiv (L N)
    let A : Set Disorder := {ω | δ ≤ dist (f N ω) (0 : ℝ)}
    have hdist : AEMeasurable (fun ω => dist (f N ω) (0 : ℝ)) disorderLaw :=
      (measurable_id.dist measurable_const).comp_aemeasurable (hf N)
    have hA : NullMeasurableSet A disorderLaw := by
      exact hdist.nullMeasurableSet_preimage measurableSet_Ici
    have hMP := measurePreserving_reversalDisorderEquiv (L N)
    have heq : (e : Disorder → Disorder) =
        PolymerCalculus.reversedDisorder (L N) := by
      change (reversalDisorderEquiv (L N) : Disorder → Disorder) =
        Gaussian.reindexDisorder (PolymerCalculus.timeReversalIndex (L N))
      exact (reversalDisorderEquiv_eq (L N)).symm
    have hA' : NullMeasurableSet A (disorderLaw.map e) := by
      exact hMP.map_eq.symm ▸ hA
    have hpre : disorderLaw (e ⁻¹' A) = disorderLaw A := by
      rw [← Measure.map_apply₀ hMP.aemeasurable hA', hMP.map_eq]
    have hEvent :
        {ω | δ ≤ dist (f N (PolymerCalculus.reversedDisorder (L N) ω)) (0 : ℝ)} =
          e ⁻¹' A := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, A]
      rw [← heq]
    calc
      disorderLaw.real {ω | δ ≤ dist
          (f N (PolymerCalculus.reversedDisorder (L N) ω)) (0 : ℝ)} =
          disorderLaw.real (e ⁻¹' A) := by rw [hEvent]
      _ = disorderLaw.real A := congrArg ENNReal.toReal hpre
      _ = disorderLaw.real {ω | δ ≤ dist (f N ω) (0 : ℝ)} := rfl
  have hlim' := hlim δ hδ
  exact hlim'.congr fun N => (hmeasure N).symm

private theorem tendstoInMeasure_of_eventually_zero_or
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0))
    (hcase : ∀ N ω, g N ω = 0 ∨ g N ω = f N ω) :
    TendstoInMeasure μ g atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hf ⊢
  intro δ hδ
  have hle (N : ℕ) :
      μ.real {ω | δ ≤ dist (g N ω) (0 : ℝ)} ≤
        μ.real {ω | δ ≤ dist (f N ω) (0 : ℝ)} := by
    apply measureReal_mono
    · intro ω hω
      rcases hcase N ω with hzero | heq
      · have : δ ≤ (0 : ℝ) := by simpa [hzero] using hω
        linarith
      · simpa [heq] using hω
    · exact measure_ne_top μ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hf δ hδ) (Filter.Eventually.of_forall fun N => measureReal_nonneg)
    (Filter.Eventually.of_forall hle)

private theorem summable_cellTestWeight_mul (N : ℕ)
    (φ : C_c(Plane × Plane, ℝ)) (g : Site × Site → ℝ) :
    Summable (fun q : Site × Site => cellTestWeight N φ q.1 q.2 * g q) := by
  classical
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro q hq
  rw [cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
  simp

private theorem clockPairing_endpointWeight_decomposition
    (ϑ : ℝ) {N a b : ℕ} (hN : 0 < N) (ha : Even a) (hb : Even b)
    (φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    (∫ p, φ p *
      (Real.exp (criticalBeta ϑ N * ω (a, latticePoint N p.1)) *
        rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω)) =
      clockPairing ϑ N a b φ ω + clockStartEndpointError ϑ N a b φ ω := by
  classical
  let W : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2
  let P : Site × Site → ℝ := fun q =>
    pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω
  let E : Site × Site → ℝ := fun q => Real.exp (criticalBeta ϑ N * ω (a, q.1))
  have hA := pairing_endpointWeight_eq_tsum_pointToPoint ϑ N a
    ((a : ℝ) / N) ((b : ℝ) / N) φ ω
  have hF := pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hb φ ω
  have hR := pairing_startEndpoint_error_eq_tsum ϑ N
    ((a : ℝ) / N) ((b : ℝ) / N) φ ω
  have hsa : evenCeil ((N : ℝ) * ((a : ℝ) / N)) = a :=
    evenCeil_scaled_nat_div hN ha
  have hsb : evenCeil ((N : ℝ) * ((b : ℝ) / N)) = b :=
    evenCeil_scaled_nat_div hN hb
  have hAsum :
      (∫ p, φ p *
        (Real.exp (criticalBeta ϑ N * ω (a, latticePoint N p.1)) *
          rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω)) =
        ∑' q : Site × Site, W q * (E q * P q) := by
    simpa only [W, E, P, hsa, hsb] using hA
  have hFsum : clockPairing ϑ N a b φ ω =
      ∑' q : Site × Site, W q * P q := by
    simpa only [clockPairing, W, P] using hF
  have hRsum : clockStartEndpointError ϑ N a b φ ω =
      ∑' q : Site × Site, W q * ((E q - 1) * P q) := by
    simpa only [clockStartEndpointError, W, P, E, hsa, hsb] using hR
  have hsumF := summable_cellTestWeight_mul N φ (fun q => P q)
  have hsumR := summable_cellTestWeight_mul N φ (fun q => (E q - 1) * P q)
  calc
    _ = ∑' q : Site × Site, W q * (E q * P q) := hAsum
    _ = ∑' q : Site × Site, (W q * P q + W q * ((E q - 1) * P q)) := by
      apply tsum_congr
      intro q
      dsimp [W, E, P]
      ring
    _ = (∑' q : Site × Site, W q * P q) +
        (∑' q : Site × Site, W q * ((E q - 1) * P q)) := hsumF.tsum_add hsumR
    _ = clockPairing ϑ N a b φ ω + clockStartEndpointError ϑ N a b φ ω := by
      rw [hFsum, hRsum]

/-- A compact rescaled polymer pairing and its time-reversed, endpoint-swapped counterpart differ by a term tending to zero in probability, including the endpoint Boltzmann factors and at most two-step clock rounding. -/
theorem tendstoInMeasure_rescaledP2P_pairing_sub_reversed (ϑ T : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (htT : t ≤ T)
    (φ : C_c(Plane × Plane, ℝ)) :
    TendstoInMeasure disorderLaw
      (fun (N : ℕ) ω =>
        (∫ p, φ p * rescaledP2P ϑ N s t p ω) -
          ∫ p, φ (p.2, p.1) * rescaledP2P ϑ N (T - t) (T - s) p
            (PolymerCalculus.reversedDisorder (evenCeil (N * T)) ω))
      atTop (fun _ => 0) := by
  classical
  let Δ : ℝ := t - s
  let ε : ℝ := Δ / 8
  let a : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * s)
  let b : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  let L : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * T)
  let c : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * (T - t))
  let d : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * (T - s))
  let ra : ℕ → ℕ := fun N => L N - b N
  let rb : ℕ → ℕ := fun N => L N - a N
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ha : ∀ N, Even (a N) := by
    intro N
    exact Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * s)
  have hb : ∀ N, Even (b N) := by
    intro N
    exact Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * t)
  have hL : ∀ N, Even (L N) := by
    intro N
    exact Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * T)
  have hc : ∀ N, Even (c N) := by
    intro N
    exact Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * (T - t))
  have hd : ∀ N, Even (d N) := by
    intro N
    exact Critical2DKPZ.SHF.Moments.even_evenCeil ((N : ℝ) * (T - s))
  have hab : ∀ N, a N ≤ b N := by
    intro N
    dsimp [a, b]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  have hbL : ∀ N, b N ≤ L N := by
    intro N
    dsimp [b, L]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg N))
  have haL : ∀ N, a N ≤ L N := fun N => (hab N).trans (hbL N)
  have hra : ∀ N, Even (ra N) := by
    intro N
    rcases hL N with ⟨l, hl⟩
    rcases hb N with ⟨q, hq⟩
    refine ⟨l - q, ?_⟩
    dsimp [ra]
    omega
  have hrb : ∀ N, Even (rb N) := by
    intro N
    rcases hL N with ⟨l, hl⟩
    rcases ha N with ⟨q, hq⟩
    refine ⟨l - q, ?_⟩
    dsimp [rb]
    omega
  have hra_le_hrb : ∀ N, ra N ≤ rb N := by
    intro N
    have habN := hab N
    have hbLN := hbL N
    have haLN := haL N
    dsimp [ra, rb]
    omega
  have hclockGap (N : ℕ) : rb N - ra N = b N - a N := by
    have habN := hab N
    have hbLN := hbL N
    have haLN := haL N
    dsimp [ra, rb]
    omega
  have hcCases (N : ℕ) : c N = ra N ∨ c N = ra N + 2 := by
    have ht : 0 ≤ t := hs.trans hst.le
    simpa [c, ra, L, b] using
      (evenCeil_reflected_clock_cases (N := N) (t := t) (T := T) ht htT)
  have hdCases (N : ℕ) : d N = rb N ∨ d N = rb N + 2 := by
    have hsT : s ≤ T := hst.le.trans htT
    simpa [d, rb, L, a] using
      (evenCeil_reflected_clock_cases (N := N) (t := s) (T := T) hs hsT)
  have hgapRatio : Tendsto
      (fun N : ℕ => ((b N - a N : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 Δ) := by
    simpa [a, b, Δ] using
      (Critical2DKPZ.SHF.Moments.tendsto_evenCeil_gap_div hs hst.le)
  have hratioEvent : ∀ᶠ N : ℕ in atTop,
      Δ / 2 < ((b N - a N : ℕ) : ℝ) / (N : ℝ) :=
    hgapRatio.eventually (Ioi_mem_nhds (by linarith [hΔ]))
  have hscale : Tendsto (fun N : ℕ => (Δ / 4) * (N : ℝ)) atTop atTop := by
    exact (tendsto_const_mul_atTop_of_pos (by positivity : 0 < Δ / 4)).2
      tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (Δ / 4) * (N : ℝ) :=
    hscale.eventually_ge_atTop 4
  have hgapStrong : ∀ᶠ N : ℕ in atTop,
      (2 * ε) * (N : ℝ) + 4 ≤ ((b N - a N : ℕ) : ℝ) := by
    filter_upwards [hratioEvent, hlarge] with N hratio hlargeN
    have hNreal : 0 < (N : ℝ) := by
      by_contra hnot
      have hzero : (N : ℝ) = 0 := le_antisymm (le_of_not_gt hnot) (Nat.cast_nonneg N)
      rw [hzero, mul_zero] at hlargeN
      norm_num at hlargeN
    have hdiff : (Δ / 2) * (N : ℝ) < ((b N - a N : ℕ) : ℝ) :=
      (lt_div_iff₀ hNreal).mp hratio
    have hεeq : 2 * ε = Δ / 4 := by dsimp [ε]; ring
    rw [hεeq]
    linarith
  have hgapOrig : ∀ᶠ N : ℕ in atTop,
      ε * (N : ℝ) ≤ ((b N - a N : ℕ) : ℝ) := by
    filter_upwards [hgapStrong] with N hN
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hmul : ε * (N : ℝ) ≤ (2 * ε) * (N : ℝ) := by
      nlinarith [hε, hNnonneg]
    linarith
  have hgapOrigReal : ∀ᶠ N : ℕ in atTop,
      ε * (N : ℝ) ≤ (b N : ℝ) - (a N : ℝ) := by
    filter_upwards [hgapOrig] with N hN
    rw [← Nat.cast_sub (hab N)]
    exact hN
  have hgapRef : ∀ᶠ N : ℕ in atTop,
      ε * (N : ℝ) ≤ ((rb N - ra N : ℕ) : ℝ) := by
    filter_upwards [hgapOrig] with N hN
    rw [hclockGap]
    exact hN
  have hgapTwoStep : ∀ᶠ N : ℕ in atTop,
      (2 * ε) * (N : ℝ) + 2 ≤ ((rb N - ra N : ℕ) : ℝ) := by
    filter_upwards [hgapStrong] with N hN
    rw [hclockGap]
    linarith
  have hgapTerminal : ∀ᶠ N : ℕ in atTop,
      (2 * ε) * (N : ℝ) + 2 ≤ ((rb N - c N : ℕ) : ℝ) := by
    filter_upwards [hgapStrong, Filter.Eventually.of_forall hcCases] with N hN hcN
    have hdiff4Real : (4 : ℝ) ≤ ((b N - a N : ℕ) : ℝ) := by
      have hnonneg : 0 ≤ (2 * ε) * (N : ℝ) := by positivity
      linarith
    have hdiff4 : 4 ≤ b N - a N := by exact_mod_cast hdiff4Real
    have hsubOrder : ra N + 2 ≤ rb N := by
      have hgap := hclockGap N
      omega
    have hEq := hclockGap N
    have hNat : b N - a N ≤ rb N - c N + 2 := by
      rcases hcN with hcEq | hcEq
      · rw [hcEq]
        omega
      · rw [hcEq]
        omega
    have hCast : ((b N - a N : ℕ) : ℝ) ≤
        ((rb N - c N : ℕ) : ℝ) + 2 := by exact_mod_cast hNat
    linarith
  let forwardPair (N : ℕ) (ω : Disorder) : ℝ :=
    ∫ p, φ p * rescaledP2P ϑ N s t p ω
  let targetPair (N : ℕ) (ω : Disorder) : ℝ :=
    ∫ p, φ (p.2, p.1) * rescaledP2P ϑ N (T - t) (T - s) p
      (PolymerCalculus.reversedDisorder (L N) ω)
  let forwardClock (N : ℕ) (ω : Disorder) : ℝ :=
    clockPairing ϑ N (a N) (b N) φ ω
  let reflectedClock (N : ℕ) (ω : Disorder) : ℝ :=
    clockPairing ϑ N (ra N) (rb N) (swapPairTest φ)
      (PolymerCalculus.reversedDisorder (L N) ω)
  let roundedStart (N : ℕ) (ω : Disorder) : ℝ :=
    clockPairing ϑ N (ra N) (rb N) (swapPairTest φ)
        (PolymerCalculus.reversedDisorder (L N) ω) -
      clockPairing ϑ N (c N) (rb N) (swapPairTest φ)
        (PolymerCalculus.reversedDisorder (L N) ω)
  let roundedTerminal (N : ℕ) (ω : Disorder) : ℝ :=
    clockPairing ϑ N (c N) (rb N) (swapPairTest φ)
        (PolymerCalculus.reversedDisorder (L N) ω) -
      clockPairing ϑ N (c N) (d N) (swapPairTest φ)
        (PolymerCalculus.reversedDisorder (L N) ω)
  let forwardEndpointError (N : ℕ) (ω : Disorder) : ℝ :=
    clockStartEndpointError ϑ N (a N) (b N) φ ω
  let reversedEndpointError (N : ℕ) (ω : Disorder) : ℝ :=
    clockStartEndpointError ϑ N (ra N) (rb N) (swapPairTest φ)
      (PolymerCalculus.reversedDisorder (L N) ω)
  have hforwardClock (N : ℕ) (hN : 0 < N) (ω : Disorder) :
      forwardPair N ω = forwardClock N ω := by
    have haClock := evenCeil_scaled_nat_div hN (ha N)
    have hbClock := evenCeil_scaled_nat_div hN (hb N)
    dsimp [forwardPair, forwardClock, clockPairing]
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [rescaledP2P, haClock, hbClock]
    simp [a, b]
  have htargetClock (N : ℕ) (hN : 0 < N) (ω : Disorder) :
      targetPair N ω =
        clockPairing ϑ N (c N) (d N) (swapPairTest φ)
          (PolymerCalculus.reversedDisorder (L N) ω) := by
    have hcClock := evenCeil_scaled_nat_div hN (hc N)
    have hdClock := evenCeil_scaled_nat_div hN (hd N)
    dsimp [targetPair, clockPairing]
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [rescaledP2P, hcClock, hdClock]
    simp [c, d, swapPairTest, Prod.swap]
  have hforwardEndpoint : TendstoInMeasure disorderLaw forwardEndpointError
      atTop (fun _ => 0) := by
    simpa [forwardEndpointError, clockStartEndpointError] using
      (tendstoInMeasure_startEndpointPairingError_evenClock ϑ hε a b ha hb
        hgapOrigReal φ)
  have hreversedEndpoint : TendstoInMeasure disorderLaw reversedEndpointError
      atTop (fun _ => 0) := by
    exact tendstoInMeasure_reversedClockStartEndpointError ϑ ε hε ra rb L hra hrb
      hgapRef (swapPairTest φ)
  let startStep (N : ℕ) (ω : Disorder) : ℝ :=
    clockPairing ϑ N (ra N) (rb N) (swapPairTest φ) ω -
      clockPairing ϑ N (ra N + 2) (rb N) (swapPairTest φ) ω
  have hstartStep : TendstoInMeasure disorderLaw startStep atTop (fun _ => 0) := by
    simpa [startStep, clockPairing] using
      (tendstoInMeasure_startTwoStepPairingError ϑ ε hε ra rb hra hrb hgapTwoStep
        (swapPairTest φ))
  have hstartStepMeas : ∀ N, AEMeasurable (startStep N) disorderLaw := by
    intro N
    dsimp [startStep]
    exact (aemeasurable_clockPairing ϑ N (ra N) (rb N) (swapPairTest φ)).sub
      (aemeasurable_clockPairing ϑ N (ra N + 2) (rb N) (swapPairTest φ))
  have hstartStepReversed : TendstoInMeasure disorderLaw
      (fun N ω => startStep N (PolymerCalculus.reversedDisorder (L N) ω))
      atTop (fun _ => 0) :=
    tendstoInMeasure_reversal_comp L hstartStepMeas hstartStep
  have hroundedStart : TendstoInMeasure disorderLaw roundedStart
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_eventually_zero_or disorderLaw hstartStepReversed
    intro N ω
    rcases hcCases N with hcase | hcase
    · left
      simp [roundedStart, hcase]
    · right
      simp [roundedStart, startStep, hcase]
  let terminalStep (N : ℕ) (ω : Disorder) : ℝ :=
    clockPairing ϑ N (c N) (rb N + 2) (swapPairTest φ) ω -
      clockPairing ϑ N (c N) (rb N) (swapPairTest φ) ω
  have hterminalStep : TendstoInMeasure disorderLaw terminalStep atTop (fun _ => 0) := by
    simpa [terminalStep, clockPairing] using
      (tendstoInMeasure_terminalTwoStepPairingError ϑ ε hε c rb hc hrb hgapTerminal
        (swapPairTest φ))
  have hterminalStepMeas : ∀ N, AEMeasurable (terminalStep N) disorderLaw := by
    intro N
    dsimp [terminalStep]
    exact (aemeasurable_clockPairing ϑ N (c N) (rb N + 2) (swapPairTest φ)).sub
      (aemeasurable_clockPairing ϑ N (c N) (rb N) (swapPairTest φ))
  have hterminalStepReversed := tendstoInMeasure_reversal_comp L
    hterminalStepMeas hterminalStep
  have hnegativeTerminal := tendstoInMeasure_neg_zero disorderLaw hterminalStepReversed
  have hroundedTerminal : TendstoInMeasure disorderLaw roundedTerminal
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_eventually_zero_or disorderLaw hnegativeTerminal
    intro N ω
    rcases hdCases N with hcase | hcase
    · left
      simp [roundedTerminal, hcase]
    · right
      simp [roundedTerminal, terminalStep, hcase]
  let weightedForward (N : ℕ) (ω : Disorder) : ℝ :=
    ∫ p, φ p *
      (Real.exp (criticalBeta ϑ N * ω (a N, latticePoint N p.1)) *
        rescaledP2P ϑ N ((a N : ℝ) / N) ((b N : ℝ) / N) p ω)
  let weightedReversed (N : ℕ) (ω : Disorder) : ℝ :=
    ∫ p, (swapPairTest φ) p *
      (Real.exp (criticalBeta ϑ N *
          PolymerCalculus.reversedDisorder (L N) ω (ra N, latticePoint N p.1)) *
        rescaledP2P ϑ N ((ra N : ℝ) / N) ((rb N : ℝ) / N) p
          (PolymerCalculus.reversedDisorder (L N) ω))
  have hclockDifference (N : ℕ) (hN : 0 < N) (ω : Disorder) :
      forwardClock N ω - reflectedClock N ω =
        reversedEndpointError N ω - forwardEndpointError N ω := by
    have hdiscrete : weightedForward N ω = weightedReversed N ω := by
      simpa [weightedForward, weightedReversed, ra, rb,
        Nat.cast_sub (hbL N), Nat.cast_sub (haL N)] using
        (integral_pairing_endpoint_time_reversal_discrete ϑ hN (ha N) (hb N) (hL N)
          (hab N) (hbL N) φ ω)
    have hdecompF := clockPairing_endpointWeight_decomposition ϑ hN (ha N) (hb N)
      φ ω
    have hdecompR := clockPairing_endpointWeight_decomposition ϑ hN (hra N) (hrb N)
      (swapPairTest φ) (PolymerCalculus.reversedDisorder (L N) ω)
    change weightedForward N ω = forwardClock N ω + forwardEndpointError N ω at hdecompF
    change weightedReversed N ω = reflectedClock N ω + reversedEndpointError N ω at hdecompR
    linarith
  let totalError (N : ℕ) (ω : Disorder) : ℝ :=
    reversedEndpointError N ω - forwardEndpointError N ω +
      roundedStart N ω + roundedTerminal N ω
  have htotalError : TendstoInMeasure disorderLaw totalError atTop (fun _ => 0) := by
    have hnegForward := tendstoInMeasure_neg_zero disorderLaw hforwardEndpoint
    have hendpointSum := tendstoInMeasure_add_zero disorderLaw hreversedEndpoint hnegForward
    have hroundSum := tendstoInMeasure_add_zero disorderLaw hroundedStart hroundedTerminal
    simpa [totalError, sub_eq_add_neg, add_assoc] using
      tendstoInMeasure_add_zero disorderLaw hendpointSum hroundSum
  have hpointwise (N : ℕ) (hN : 0 < N) (ω : Disorder) :
      forwardPair N ω - targetPair N ω = totalError N ω := by
    have hF := hforwardClock N hN ω
    have hT := htargetClock N hN ω
    have hExact := hclockDifference N hN ω
    dsimp [totalError, reflectedClock, roundedStart, roundedTerminal,
      forwardClock] at hExact ⊢
    rw [hF, hT]
    linarith
  have hEq : ∀ᶠ N : ℕ in atTop,
      (fun ω => forwardPair N ω - targetPair N ω) =ᵐ[disorderLaw]
        fun ω => totalError N ω := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact Filter.Eventually.of_forall fun ω => hpointwise N hN ω
  have hEq' : ∀ᶠ N : ℕ in atTop,
      (fun ω => totalError N ω) =ᵐ[disorderLaw]
        fun ω => forwardPair N ω - targetPair N ω := by
    filter_upwards [hEq] with N hN
    exact hN.symm
  exact TendstoInMeasure.congr' hEq'
    (Filter.Eventually.of_forall fun ω => rfl) htotalError

/-- A critical SHF has the same finite-dimensional law after reversing all
time intervals and swapping the two spatial endpoints. -/
theorem isCriticalSHF_reverse_fdd (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (T : ℝ) (k : ℕ) (s t : Fin k → ℝ) (hst : ∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) :
    P.map (fun ω i => (Z (T - t i) (T - s i) ω).map Prod.swap) =
      P.map (fun ω i => Z (s i) (t i) ω) := by
  classical
  let Zrev : Fin k → Ω → Measure (Plane × Plane) := fun i ω =>
    (Z (T - t i) (T - s i) ω).map Prod.swap
  let Zfor : Fin k → Ω → Measure (Plane × Plane) := fun i ω => Z (s i) (t i) ω
  have hrevOrder (i : Fin k) : 0 ≤ T - t i ∧ T - t i < T - s i := by
    rcases hst i with ⟨hs, hst', ht⟩
    constructor <;> linarith
  have hforMeas (i : Fin k) : Measurable (Zfor i) :=
    hZ.1 (s i) (t i) (hst i).1 (hst i).2.1
  have hrevMeas (i : Fin k) : Measurable (Zrev i) := by
    dsimp [Zrev]
    exact Measure.measurable_map Prod.swap measurable_swap |>.comp
      (hZ.1 (T - t i) (T - s i) (hrevOrder i).1 (hrevOrder i).2)
  have hforLF : ∀ᵐ ω ∂P, ∀ i, IsLocallyFiniteMeasure (Zfor i ω) := by
    apply ae_all_iff.2
    intro i
    exact (hZ.2.1 (s i) (t i) (hst i).1 (hst i).2.1).mono fun ω hω => hω.1
  have hrevLF : ∀ᵐ ω ∂P, ∀ i, IsLocallyFiniteMeasure (Zrev i ω) := by
    apply ae_all_iff.2
    intro i
    filter_upwards [hZ.2.1 (T - t i) (T - s i)
      (hrevOrder i).1 (hrevOrder i).2] with ω hω
    have hmap := @locallyFinite_map_homeomorph _ _ _ _ _ _ _ _ _ pairSwap
      (Z (T - t i) (T - s i) ω) hω.1
    simpa [Zrev, pairSwapMeas, pairSwap, Prod.swap] using hmap
  have hPairLaws : ∀ (m : ℕ) (f : Fin m → Fin k × C_c(Plane × Plane, ℝ)),
      P.map (fun ω j => ∫ p, (f j).2 p ∂(Zrev (f j).1 ω)) =
        P.map (fun ω j => ∫ p, (f j).2 p ∂(Zfor (f j).1 ω)) := by
    intro m f
    let sr : Fin m → ℝ := fun j => T - t ((f j).1)
    let tr : Fin m → ℝ := fun j => T - s ((f j).1)
    let φr : Fin m → C_c(Plane × Plane, ℝ) := fun j => pairSwapTest (f j).2
    let ψr : Fin m → C_c(Plane, ℝ) := fun _ => 0
    let φf : Fin m → C_c(Plane × Plane, ℝ) := fun j => (f j).2
    let ψf : Fin m → C_c(Plane, ℝ) := fun _ => 0
    have horderR (j : Fin m) : 0 ≤ sr j ∧ sr j < tr j := by
      exact hrevOrder (f j).1
    have horderF (j : Fin m) : 0 ≤ s ((f j).1) ∧ s ((f j).1) < t ((f j).1) := by
      exact ⟨(hst ((f j).1)).1, (hst ((f j).1)).2.1⟩
    let XR : ℕ → Disorder → Fin m → ℝ := fun N ω j =>
      ∫ p, φr j p * rescaledP2P ϑ N (sr j) (tr j) p ω
    let XF : ℕ → Disorder → Fin m → ℝ := fun N ω j =>
      ∫ p, φf j p * rescaledP2P ϑ N (s ((f j).1)) (t ((f j).1)) p ω
    let LR : Ω → Fin m → ℝ := fun ω j =>
      ∫ p, φr j p ∂(Z (sr j) (tr j) ω)
    let LF : Ω → Fin m → ℝ := fun ω j =>
      ∫ p, φf j p ∂(Z (s ((f j).1)) (t ((f j).1)) ω)
    let project : (Fin m → ℝ × ℝ) → Fin m → ℝ := fun x j => (x j).1
    have hproject : Continuous project := by fun_prop
    have hRpair := hZ.2.2 m sr tr horderR φr ψr
    have hR : TendstoInDistribution XR atTop LR (fun _ => disorderLaw) P := by
      have h := hRpair.continuous_comp hproject
      refine ⟨h.forall_aemeasurable, h.aemeasurable_limit, ?_⟩
      exact h.tendsto.comp tendsto_id
    have hFpair := hZ.2.2 m (fun j => s ((f j).1))
      (fun j => t ((f j).1)) horderF φf ψf
    have hF : TendstoInDistribution XF atTop LF (fun _ => disorderLaw) P := by
      have h := hFpair.continuous_comp hproject
      refine ⟨h.forall_aemeasurable, h.aemeasurable_limit, ?_⟩
      exact h.tendsto.comp tendsto_id
    have hswapLimit (j : Fin m) : ∀ᵐ ω ∂P,
        ∫ p, (f j).2 p ∂(Zrev (f j).1 ω) = LR ω j := by
      filter_upwards [hZ.2.1 (T - t ((f j).1)) (T - s ((f j).1))
        (horderR j).1 (horderR j).2] with ω hω
      dsimp [Zrev, LR, sr, φr]
      have hs := @integral_pairSwapTest_map (Z (T - t ((f j).1))
        (T - s ((f j).1)) ω) hω.1 ((f j).2)
      simpa [pairSwapMeas, pairSwap, Prod.swap, pairSwapTest] using hs.2
    have hswapLimitVec : (fun ω j => LR ω j) =ᵐ[P]
        (fun ω j => ∫ p, (f j).2 p ∂(Zrev (f j).1 ω)) := by
      have hswapLimitRev (j : Fin m) : ∀ᵐ ω ∂P,
          LR ω j = ∫ p, (f j).2 p ∂(Zrev (f j).1 ω) :=
        (hswapLimit j).mono fun _ h => h.symm
      filter_upwards [ae_all_iff.2 hswapLimitRev] with ω hω
      funext j
      exact hω j
    have hR' : TendstoInDistribution XR atTop
        (fun ω j => ∫ p, (f j).2 p ∂(Zrev (f j).1 ω))
        (fun _ => disorderLaw) P := by
      exact hR.congr (fun _ => Filter.Eventually.of_forall fun ω => rfl) hswapLimitVec
    let XRev : ℕ → Disorder → Fin m → ℝ := fun N ω j =>
      XR N (PolymerCalculus.reversedDisorder (evenCeil (N * T)) ω) j
    have hErrCoord (j : Fin m) :
        TendstoInMeasure disorderLaw (fun N ω => XF N ω j - XRev N ω j)
          atTop (fun _ => 0) := by
      simpa [XF, XRev, XR, sr, tr, φf, φr, pairSwapTest_apply] using
        tendstoInMeasure_rescaledP2P_pairing_sub_reversed ϑ T
          (hst ((f j).1)).1 (hst ((f j).1)).2.1 (hst ((f j).1)).2.2 ((f j).2)
    have hErr : TendstoInMeasure disorderLaw (fun N ω j => XF N ω j - XRev N ω j)
        atTop (fun _ => 0) := by
      exact Critical2DKPZ.SHF.Tsai.tendstoInMeasure_fintype_pi disorderLaw
        (fun N ω j => XF N ω j - XRev N ω j) (fun _ _ => 0) hErrCoord
    have hXRevAEM : ∀ N, AEMeasurable (XRev N) disorderLaw := by
      intro N
      let L := evenCeil (N * T)
      let rev := PolymerCalculus.reversedDisorder L
      let hMP := PolymerCalculus.measurePreserving_reversedDisorder L
      have houter : AEMeasurable (XR N) (disorderLaw.map rev) := by
        rw [hMP.map_eq]
        exact hR.forall_aemeasurable N
      exact houter.comp_aemeasurable hMP.measurable.aemeasurable
    have hRrev : TendstoInDistribution XRev atTop
        (fun ω j => ∫ p, (f j).2 p ∂(Zrev (f j).1 ω)) (fun _ => disorderLaw) P := by
      refine ⟨hXRevAEM, hR'.aemeasurable_limit, ?_⟩
      apply hR'.tendsto.congr'
      filter_upwards with N
      apply Subtype.ext
      let rev := PolymerCalculus.reversedDisorder (evenCeil (N * T))
      let hMP := PolymerCalculus.measurePreserving_reversedDisorder (evenCeil (N * T))
      have houter : AEMeasurable (XR N) (disorderLaw.map rev) := by
        rw [hMP.map_eq]
        exact hR.forall_aemeasurable N
      calc
        disorderLaw.map (XR N) = (disorderLaw.map rev).map (XR N) := by
          rw [hMP.map_eq]
        _ = disorderLaw.map (XRev N) := by
          simpa [XRev, Function.comp_def] using
            AEMeasurable.map_map_of_aemeasurable houter hMP.measurable.aemeasurable
    have hXF_AEM : ∀ N, AEMeasurable (XF N) disorderLaw := hF.forall_aemeasurable
    have hFtoR : TendstoInDistribution XF atTop
        (fun ω j => ∫ p, (f j).2 p ∂(Zrev (f j).1 ω))
        (fun _ => disorderLaw) P := by
      exact MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub
        (fun N ω => XF N ω)
        (fun ω j => ∫ p, (f j).2 p ∂(Zrev (f j).1 ω)) hRrev hErr hXF_AEM
    have huniq := MeasureTheory.tendstoInDistribution_unique _ hF hFtoR
    simpa [Function.comp_def] using huniq.symm
  exact RandomMeasure.map_eq_of_pairing_laws P P k Zrev Zfor
    hrevMeas hforMeas hrevLF hforLF hPairLaws

end Critical2DKPZ.SHF.Symmetries

end
