/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.TimeContinuity.SlabDifference
public import Critical2DKPZ.SHF.TimeContinuity.SlabDifferenceEnd
import Mathlib.Tactic

/-! # Uniform discrete L² continuity -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped CompactlySupported Topology
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Flow

namespace Critical2DKPZ.SHF.TimeContinuity

private structure PolymerBadDatum where
  N : ℕ
  s : ℝ
  t : ℝ
  s' : ℝ
  t' : ℝ

/-- Moving-time polymer-moment convergence and the two slab projection identities imply a uniform discrete L² modulus. -/
theorem polymerMeasure_L2_modulus_of (ϑ : ℝ) (hPolymerMovingMomentInput : PolymerMovingMomentLimit ϑ)
    (Φ : C_c(Plane × Plane, ℝ)) {τ T : ℝ} (hτ : 0 < τ) :
    PolymerL2Modulus ϑ Φ τ T := by
  intro ε hε
  by_contra hmod
  let Bad (η : ℝ) (N : ℕ) : Prop :=
    ∃ s t s' t' : ℝ,
      (0 ≤ s ∧ τ ≤ t - s ∧ t ≤ T ∧
        0 ≤ s' ∧ τ ≤ t' - s' ∧ t' ≤ T) ∧
      |s - s'| + |t - t'| ≤ η ∧
      ε < ∫ ω,
        (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω) -
          ∫ p, Φ p ∂(polymerMeasure ϑ N s' t' ω)) ^ 2 ∂disorderLaw
  have hbadOften (η : ℝ) (hη : 0 < η) : ∃ᶠ N : ℕ in atTop, Bad η N := by
    by_contra hnever
    have hnotbad : ∀ᶠ N : ℕ in atTop, ¬ Bad η N := by
      simpa only [Filter.Frequently, not_not] using hnever
    have hbound : ∀ᶠ N : ℕ in atTop, ∀ s t s' t' : ℝ,
        0 ≤ s → τ ≤ t - s → t ≤ T → 0 ≤ s' → τ ≤ t' - s' → t' ≤ T →
        |s - s'| + |t - t'| ≤ η →
          ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω) -
            ∫ p, Φ p ∂(polymerMeasure ϑ N s' t' ω)) ^ 2 ∂disorderLaw ≤ ε := by
      filter_upwards [hnotbad] with N hN
      intro s t s' t' hs hst ht hs' hs't ht' hclose
      by_contra hle
      exact hN ⟨s, t, s', t', ⟨hs, hst, ht, hs', hs't, ht'⟩, hclose, lt_of_not_ge hle⟩
    exact hmod ⟨η, hη, by simpa only [Bad] using hbound⟩
  have hselect (k M : ℕ) :
      ∃ d : PolymerBadDatum, M ≤ d.N ∧
        (0 ≤ d.s ∧ τ ≤ d.t - d.s ∧ d.t ≤ T ∧
          0 ≤ d.s' ∧ τ ≤ d.t' - d.s' ∧ d.t' ≤ T) ∧
        |d.s - d.s'| + |d.t - d.t'| ≤ 1 / ((k : ℝ) + 1) ∧
        ε < ∫ ω,
          (∫ p, Φ p ∂(polymerMeasure ϑ d.N d.s d.t ω) -
            ∫ p, Φ p ∂(polymerMeasure ϑ d.N d.s' d.t' ω)) ^ 2 ∂disorderLaw := by
    have hη : 0 < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨N, hMN, hBad⟩ := (hbadOften _ hη).forall_exists_of_atTop M
    obtain ⟨s, t, s', t', hlegal, hclose, hlarge⟩ := hBad
    exact ⟨⟨N, s, t, s', t'⟩, hMN, hlegal, hclose, hlarge⟩
  let select (k M : ℕ) : PolymerBadDatum := Classical.choose (hselect k M)
  let data : ℕ → PolymerBadDatum :=
    Nat.rec (select 0 0) (fun k d => select (k + 1) (d.N + 1))
  let Nseq : ℕ → ℕ := fun k => (data k).N
  let sN : ℕ → ℝ := fun k => (data k).s
  let tN : ℕ → ℝ := fun k => (data k).t
  let s'N : ℕ → ℝ := fun k => (data k).s'
  let t'N : ℕ → ℝ := fun k => (data k).t'
  have hdataProps (k : ℕ) :
      (0 ≤ (data k).s ∧ τ ≤ (data k).t - (data k).s ∧ (data k).t ≤ T ∧
        0 ≤ (data k).s' ∧ τ ≤ (data k).t' - (data k).s' ∧ (data k).t' ≤ T) ∧
      |(data k).s - (data k).s'| + |(data k).t - (data k).t'| ≤
        1 / ((k : ℝ) + 1) ∧
      ε < ∫ ω,
        (∫ p, Φ p ∂(polymerMeasure ϑ (data k).N (data k).s (data k).t ω) -
          ∫ p, Φ p ∂(polymerMeasure ϑ (data k).N (data k).s' (data k).t' ω)) ^ 2
          ∂disorderLaw := by
    induction k with
    | zero =>
        simpa [data, select] using (Classical.choose_spec (hselect 0 0)).2
    | succ k _ =>
        simpa [data, select] using
          (Classical.choose_spec (hselect (k + 1) ((data k).N + 1))).2
  have hNinc (k : ℕ) : Nseq k < Nseq (k + 1) := by
    have h := (Classical.choose_spec (hselect (k + 1) (Nseq k + 1))).1
    simpa [data, select, Nseq] using h
  have hNseq : StrictMono Nseq := strictMono_nat_of_lt_succ hNinc
  have hlegal (k : ℕ) :
      0 ≤ sN k ∧ τ ≤ tN k - sN k ∧ tN k ≤ T ∧
      0 ≤ s'N k ∧ τ ≤ t'N k - s'N k ∧ t'N k ≤ T := by
    simpa [sN, tN, s'N, t'N] using (hdataProps k).1
  have hclose (k : ℕ) : |sN k - s'N k| + |tN k - t'N k| ≤
      1 / ((k : ℝ) + 1) := by
    simpa [sN, tN, s'N, t'N] using (hdataProps k).2.1
  have hbadValue (k : ℕ) : ε <
      ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω) -
        ∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (s'N k) (t'N k) ω)) ^ 2 ∂disorderLaw := by
    simpa [Nseq, sN, tN, s'N, t'N] using (hdataProps k).2.2

  let pseq : ℕ → (ℝ × ℝ) × (ℝ × ℝ) := fun k =>
    Prod.mk (sN k, tN k) (s'N k, t'N k)
  have hpseq (k : ℕ) :
      pseq k ∈ (Icc 0 T ×ˢ Icc 0 T) ×ˢ (Icc 0 T ×ˢ Icc 0 T) := by
    have hl := hlegal k
    have hsLt : sN k < tN k := by linarith [hτ]
    have hs'Lt' : s'N k < t'N k := by linarith [hτ]
    have hsT : sN k ≤ T := le_trans hsLt.le hl.2.2.1
    have hs'T : s'N k ≤ T := le_trans hs'Lt'.le hl.2.2.2.2.2
    exact ⟨⟨⟨hl.1, hsT⟩, ⟨by linarith [hl.1, hτ, hl.2.1], hl.2.2.1⟩⟩,
      ⟨⟨hl.2.2.2.1, hs'T⟩,
        ⟨by linarith [hl.2.2.2.1, hτ, hl.2.2.2.2.1], hl.2.2.2.2.2⟩⟩⟩
  have hcompact : IsCompact ((Icc 0 T ×ˢ Icc 0 T) ×ˢ (Icc 0 T ×ˢ Icc 0 T)) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨plim, hplim, φ, hφ, hφlim⟩ := hcompact.tendsto_subseq hpseq
  have hsSub : Tendsto (fun k => sN (φ k)) atTop (𝓝 plim.1.1) := by
    simpa [pseq, Function.comp_def] using
      ((continuous_fst.comp continuous_fst).tendsto plim).comp hφlim
  have htSub : Tendsto (fun k => tN (φ k)) atTop (𝓝 plim.1.2) := by
    simpa [pseq, Function.comp_def] using
      ((continuous_snd.comp continuous_fst).tendsto plim).comp hφlim
  have hs'Sub : Tendsto (fun k => s'N (φ k)) atTop (𝓝 plim.2.1) := by
    simpa [pseq, Function.comp_def] using
      ((continuous_fst.comp continuous_snd).tendsto plim).comp hφlim
  have ht'Sub : Tendsto (fun k => t'N (φ k)) atTop (𝓝 plim.2.2) := by
    simpa [pseq, Function.comp_def] using
      ((continuous_snd.comp continuous_snd).tendsto plim).comp hφlim
  have hsmall : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hcloseSub : Tendsto
      (fun k => |sN (φ k) - s'N (φ k)| + |tN (φ k) - t'N (φ k)|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (fun k => (hclose (φ k))) hsmall
  have hsDiff0 : Tendsto (fun k => sN (φ k) - s'N (φ k)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have habs : Tendsto (fun k => |sN (φ k) - s'N (φ k)|) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => abs_nonneg _)
        (fun k => by nlinarith [abs_nonneg (tN (φ k) - t'N (φ k)), hclose (φ k)]) hsmall
    simpa only [Real.norm_eq_abs, sub_zero] using habs
  have htDiff0 : Tendsto (fun k => tN (φ k) - t'N (φ k)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have habs : Tendsto (fun k => |tN (φ k) - t'N (φ k)|) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => abs_nonneg _)
        (fun k => by nlinarith [abs_nonneg (sN (φ k) - s'N (φ k)), hclose (φ k)]) hsmall
    simpa only [Real.norm_eq_abs, sub_zero] using habs
  have hsEq : plim.1.1 = plim.2.1 := by
    have hdiff := hsSub.sub hs'Sub
    have heq := tendsto_nhds_unique hdiff hsDiff0
    exact sub_eq_zero.mp heq
  have htEq : plim.1.2 = plim.2.2 := by
    have hdiff := htSub.sub ht'Sub
    have heq := tendsto_nhds_unique hdiff htDiff0
    exact sub_eq_zero.mp heq
  have hsLimit : 0 ≤ plim.1.1 := hplim.1.1.1
  have htLimitGap : τ ≤ plim.1.2 - plim.1.1 := by
    have hdur := htSub.sub hsSub
    exact ge_of_tendsto' hdur (fun k => (hlegal (φ k)).2.1)
  have hstLimit : plim.1.1 < plim.1.2 := by linarith [hτ]
  have hcloseCross : ∀ᶠ k : ℕ in atTop, s'N (φ k) < tN (φ k) := by
    have hevent := (Metric.tendsto_nhds.mp hsmall) (τ / 2) (by linarith)
    filter_upwards [hevent] with k hk
    have hsmallk : 1 / ((φ k : ℝ) + 1) < τ / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / ((φ k : ℝ) + 1))] using hk
    have htk : |tN (φ k) - t'N (φ k)| < τ / 2 := by
      have := hclose (φ k)
      nlinarith [abs_nonneg (sN (φ k) - s'N (φ k)), abs_nonneg (tN (φ k) - t'N (φ k)), hsmallk]
    have hcross : 0 < tN (φ k) - s'N (φ k) := by
      have := (hlegal (φ k)).2.2.2.2.1
      nlinarith [abs_le.mp (le_of_lt htk)]
    exact sub_pos.mp hcross
  obtain ⟨K, hK⟩ := eventually_atTop.1 hcloseCross
  let sh : ℕ → ℕ := fun k => k + K
  have hsh : StrictMono sh := strictMono_nat_of_lt_succ (fun _ => by simp [sh])
  have hNfinal : StrictMono (fun k => Nseq (φ (sh k))) :=
    (hNseq.comp hφ).comp hsh
  let Nfinal : ℕ → ℕ := fun k => Nseq (φ (sh k))
  let sBase : ℕ → ℝ := fun k => sN (φ (sh k))
  let tBase : ℕ → ℝ := fun k => tN (φ (sh k))
  let s'Base : ℕ → ℝ := fun k => s'N (φ (sh k))
  let t'Base : ℕ → ℝ := fun k => t'N (φ (sh k))
  have hshift : Tendsto sh atTop atTop := hsh.tendsto_atTop
  have hsBase : Tendsto sBase atTop (𝓝 plim.1.1) := hsSub.comp hshift
  have htBase : Tendsto tBase atTop (𝓝 plim.1.2) := htSub.comp hshift
  have hs'Base : Tendsto s'Base atTop (𝓝 plim.2.1) := hs'Sub.comp hshift
  have ht'Base : Tendsto t'Base atTop (𝓝 plim.2.2) := ht'Sub.comp hshift
  have hN0 : ∀ k, 0 ≤ sBase k := fun k => (hlegal (φ (sh k))).1
  have hs'0 : ∀ k, 0 ≤ s'Base k := fun k => (hlegal (φ (sh k))).2.2.2.1
  have htBaseLe : ∀ k, tBase k ≤ T := fun k => (hlegal (φ (sh k))).2.2.1
  have ht'BaseLe : ∀ k, t'Base k ≤ T := fun k => (hlegal (φ (sh k))).2.2.2.2.2
  have hsLt : ∀ k, sBase k < tBase k := fun k => by
    have h := (hlegal (φ (sh k))).2.1
    linarith [hτ]
  have hs'Lt : ∀ k, s'Base k < t'Base k := fun k => by
    have h := (hlegal (φ (sh k))).2.2.2.2.1
    linarith [hτ]
  have hs'LtBase : ∀ k, s'Base k < tBase k := by
    intro k
    exact hK (sh k) (by simp [sh])
  let sLo : ℕ → ℝ := fun k => min (sBase k) (s'Base k)
  let sHi : ℕ → ℝ := fun k => max (sBase k) (s'Base k)
  let tLo : ℕ → ℝ := fun k => min (tBase k) (t'Base k)
  let tHi : ℕ → ℝ := fun k => max (tBase k) (t'Base k)
  have hs'LtLo : ∀ k, s'Base k < tLo k := by
    intro k
    exact lt_min (hs'LtBase k) (hs'Lt k)
  have hsLoLimit : Tendsto sLo atTop (𝓝 plim.1.1) := by
    simpa [sLo, hsEq] using hsBase.min hs'Base
  have hsHiLimit : Tendsto sHi atTop (𝓝 plim.1.1) := by
    simpa [sHi, hsEq] using hsBase.max hs'Base
  have htLoLimit : Tendsto tLo atTop (𝓝 plim.1.2) := by
    simpa [tLo, htEq] using htBase.min ht'Base
  have htHiLimit : Tendsto tHi atTop (𝓝 plim.1.2) := by
    simpa [tHi, htEq] using htBase.max ht'Base
  have hsLo0 : ∀ k, 0 ≤ sLo k := by
    intro k
    exact le_min (hN0 k) (hs'0 k)
  have hsStart : ∀ k, sLo k ≤ sHi k ∧ sHi k < tBase k := by
    intro k
    constructor
    · exact min_le_max
    · exact max_lt (hsLt k) (hs'LtBase k)
  have htEnd : ∀ k, tLo k ≤ tHi k ∧ tHi k ≤ T := by
    intro k
    constructor
    · exact min_le_max
    · exact max_le (htBaseLe k) (ht'BaseLe k)
  let pairing (a b : ℕ → ℝ) : ℕ → Disorder → ℝ := fun k ω =>
    ∫ p, Φ p ∂(polymerMeasure ϑ (Nfinal k) (a k) (b k) ω)
  let startDiff : ℕ → Disorder → ℝ := fun k ω =>
    pairing sBase tBase k ω - pairing s'Base tBase k ω
  let endDiff : ℕ → Disorder → ℝ := fun k ω =>
    pairing s'Base tBase k ω - pairing s'Base t'Base k ω
  let fullDiff : ℕ → Disorder → ℝ := fun k ω =>
    pairing sBase tBase k ω - pairing s'Base t'Base k ω
  have hstartLimit := polymerPairing_startSlab_sq_tendsto_zero ϑ hPolymerMovingMomentInput
    (hsLimit) hstLimit T Nfinal hNfinal sLo sHi tBase hsLoLimit hsHiLimit htBase
    hsLo0 hsStart (fun k => htBaseLe k) Φ
  have hs'Limit : Tendsto s'Base atTop (𝓝 plim.1.1) := by
    simpa [hsEq] using hs'Base
  have hendLimit := polymerPairing_endSlab_sq_tendsto_zero ϑ hPolymerMovingMomentInput
    hsLimit hstLimit T Nfinal hNfinal s'Base tLo tHi hs'Limit htLoLimit htHiLimit
    hs'0 (fun k => ⟨hs'LtLo k, (htEnd k).1⟩) (fun k => (htEnd k).2) Φ
  have hendLim : Tendsto (fun k => ∫ ω, endDiff k ω ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
    apply hendLimit.congr'
    filter_upwards [] with k
    by_cases h : tBase k ≤ t'Base k
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simp [endDiff, pairing, tLo, tHi, min_eq_left h, max_eq_right h]
        ring
    · have h' : t'Base k ≤ tBase k := le_of_not_ge h
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simp [endDiff, pairing, tLo, tHi, min_eq_right h', max_eq_left h']
  have hstartSorted : Tendsto
      (fun k => ∫ ω,
        (pairing sLo tBase k ω - pairing sHi tBase k ω) ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
    simpa [pairing] using hstartLimit
  have hstartActual : Tendsto (fun k => ∫ ω, startDiff k ω ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
    apply hstartSorted.congr'
    filter_upwards [] with k
    by_cases h : sBase k ≤ s'Base k
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simp [startDiff, pairing, sLo, sHi, min_eq_left h, max_eq_right h]
    · have h' : s'Base k ≤ sBase k := le_of_not_ge h
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simp [startDiff, pairing, sLo, sHi, min_eq_right h', max_eq_left h']
        ring
  have hendActual : Tendsto (fun k => ∫ ω, endDiff k ω ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := hendLim
  have hupperLimit : Tendsto
      (fun k => 2 * ((∫ ω, startDiff k ω ^ 2 ∂disorderLaw) +
        ∫ ω, endDiff k ω ^ 2 ∂disorderLaw)) atTop (𝓝 0) := by
    simpa using (hstartActual.add hendActual).const_mul 2
  have hfullLimit : Tendsto (fun k => ∫ ω, fullDiff k ω ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
    apply squeeze_zero
      (fun k => integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg (fullDiff k ω)))
      (fun k => ?_) hupperLimit
    let f₁ : Disorder → ℝ := pairing sBase tBase k
    let f₂ : Disorder → ℝ := pairing s'Base tBase k
    let f₃ : Disorder → ℝ := pairing s'Base t'Base k
    have h₁ := Critical2DKPZ.SHF.Flow.memLp_polymerPairing_two
      ϑ (Nfinal k) (sBase k) (tBase k) Φ
    have h₂ := Critical2DKPZ.SHF.Flow.memLp_polymerPairing_two
      ϑ (Nfinal k) (s'Base k) (tBase k) Φ
    have h₃ := Critical2DKPZ.SHF.Flow.memLp_polymerPairing_two
      ϑ (Nfinal k) (s'Base k) (t'Base k) Φ
    have hstart : MemLp (fun ω => startDiff k ω) 2 disorderLaw := by
      convert h₁.sub h₂ using 1
    have hend : MemLp (fun ω => endDiff k ω) 2 disorderLaw := by
      convert h₂.sub h₃ using 1
    have hfull : MemLp (fun ω => fullDiff k ω) 2 disorderLaw := by
      have hsum := hstart.add hend
      have heq : (fun ω => startDiff k ω + endDiff k ω) = fun ω => fullDiff k ω := by
        funext ω
        dsimp [startDiff, endDiff, fullDiff]
        ring
      rw [← heq]
      exact hsum
    have hfullInt : Integrable (fun ω => fullDiff k ω ^ 2) disorderLaw := by
      simpa [Real.norm_eq_abs, sq_abs] using hfull.integrable_sq
    have hstartInt : Integrable (fun ω => startDiff k ω ^ 2) disorderLaw := by
      simpa [Real.norm_eq_abs, sq_abs] using hstart.integrable_sq
    have hendInt : Integrable (fun ω => endDiff k ω ^ 2) disorderLaw := by
      simpa [Real.norm_eq_abs, sq_abs] using hend.integrable_sq
    have hRHS : Integrable (fun ω =>
        2 * (startDiff k ω ^ 2) + 2 * (endDiff k ω ^ 2)) disorderLaw :=
      (hstartInt.const_mul 2).add (hendInt.const_mul 2)
    have hpoint (ω : Disorder) : fullDiff k ω ^ 2 ≤
        2 * (startDiff k ω ^ 2) + 2 * (endDiff k ω ^ 2) := by
      have heq : fullDiff k ω = startDiff k ω + endDiff k ω := by
        dsimp [startDiff, endDiff, fullDiff]
        ring
      rw [heq]
      nlinarith [sq_nonneg (startDiff k ω - endDiff k ω)]
    calc
      _ = ∫ ω, fullDiff k ω ^ 2 ∂disorderLaw := rfl
      _ ≤ ∫ ω, (2 * (startDiff k ω ^ 2) + 2 * (endDiff k ω ^ 2)) ∂disorderLaw :=
        integral_mono hfullInt hRHS hpoint
      _ = 2 * ((∫ ω, startDiff k ω ^ 2 ∂disorderLaw) +
          ∫ ω, endDiff k ω ^ 2 ∂disorderLaw) := by
        rw [integral_add (hstartInt.const_mul 2) (hendInt.const_mul 2),
          integral_const_mul, integral_const_mul]
        ring
  have hbadFinal (k : ℕ) : ε ≤ ∫ ω, fullDiff k ω ^ 2 ∂disorderLaw := by
    have h := hbadValue (φ (sh k))
    simpa [fullDiff, pairing, Nfinal, sBase, tBase, s'Base, t'Base] using h.le
  have hεle0 : ε ≤ 0 := ge_of_tendsto' hfullLimit hbadFinal
  linarith

end Critical2DKPZ.SHF.TimeContinuity

end
