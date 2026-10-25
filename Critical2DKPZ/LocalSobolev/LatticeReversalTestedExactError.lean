/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeReversalPointwiseL1
public import Critical2DKPZ.LocalSobolev.LatticeReversalPointwiseL1
public import Critical2DKPZ.PolymerCalculus.Clocks
public import Mathlib.Tactic
public import Critical2DKPZ.Definitions.TestFn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Tested lattice reversal error at the exact reflected clock -/

@[expose] public noncomputable section
namespace Critical2DKPZ.LocalSobolev
open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology

private theorem tested_eLpNorm_one_le (E : Plane → Disorder → ℝ) (φ : TestFn) (B : ℝ)
    (hm : Measurable (Function.uncurry E))
    (hi : ∀ x, Integrable (E x) disorderLaw)
    (hb : ∀ x, (∫ ω, |E x ω| ∂disorderLaw) ≤ B) :
    eLpNorm (fun ω => ∫ x, φ x * E x ω) 1 disorderLaw ≤
      ENNReal.ofReal ((∫ x, |φ x|) * B) := by
  let F : Plane × Disorder → ℝ := fun p => φ p.1 * E p.1 p.2
  have hF : Measurable F := (φ.continuous.measurable.comp measurable_fst).mul hm
  have hφ : Integrable (fun x => |φ x|) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).abs
  have hs (x : Plane) : Integrable (fun ω => F (x, ω)) disorderLaw :=
    (hi x).const_mul (φ x)
  have hmean (x : Plane) : (∫ ω, ‖F (x, ω)‖ ∂disorderLaw) =
      |φ x| * ∫ ω, |E x ω| ∂disorderLaw := by
    simp only [F, Real.norm_eq_abs, abs_mul, integral_const_mul]
  have hmajor (x : Plane) : ‖∫ ω, ‖F (x, ω)‖ ∂disorderLaw‖ ≤ |φ x| * B := by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hmean]
    exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  have hmarg : Integrable (fun x => ∫ ω, ‖F (x, ω)‖ ∂disorderLaw) :=
    (hφ.mul_const B).mono'
      hF.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
      (Eventually.of_forall hmajor)
  have hprod : Integrable F (volume.prod disorderLaw) :=
    (integrable_prod_iff hF.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall hs, hmarg⟩
  have htested : Integrable (fun ω => ∫ x, φ x * E x ω) disorderLaw :=
    hprod.integral_prod_right
  have habsInt : Integrable (fun ω => ∫ x, ‖F (x, ω)‖) disorderLaw :=
    hprod.norm.integral_prod_right
  have hnorm : (∫ ω, ‖∫ x, φ x * E x ω‖ ∂disorderLaw) ≤
      (∫ x, |φ x|) * B := by
    calc
      _ ≤ ∫ ω, (∫ x, ‖F (x, ω)‖) ∂disorderLaw :=
        integral_mono_ae htested.norm habsInt (Eventually.of_forall fun _ => norm_integral_le_integral_norm _)
      _ = ∫ x, ∫ ω, ‖F (x, ω)‖ ∂disorderLaw :=
        (integral_integral_swap hprod.norm).symm
      _ ≤ ∫ x, |φ x| * B := integral_mono_ae hmarg (hφ.mul_const B)
        (Eventually.of_forall fun x => by
          change (∫ ω, ‖F (x, ω)‖ ∂disorderLaw) ≤ |φ x| * B
          rw [hmean]
          exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _))
      _ = _ := integral_mul_const _ _
  rw [eLpNorm_one_eq_lintegral_enorm htested.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm htested]
  exact ENNReal.ofReal_le_ofReal hnorm

private theorem measurable_exact_error (ϑ : ℝ) {N m L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmEven : Even m) (hLEven : Even L) (hmL : m ≤ L)
    (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun p : Plane × Disorder => kpzLattice ϑ N ((m : ℝ) / N) h₀ p.1 p.2 -
      kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ p.1
        (PolymerCalculus.reversedDisorder L p.2)) := by
  let β := criticalBeta ϑ N
  let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  let ξ : Disorder → Disorder := fun ω =>
    Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)
  let A : Site → Disorder → ℝ := fun z ω =>
    β * ω (m, z) - β ^ 2 / 2 +
      (Real.log (profileP2Fun 0 (m - 1) m (endpointDist β (m - 1) z (ξ ω)) f (ξ ω)) -
       Real.log (profileP2Fun β (m - 1) m (endpointDist β (m - 1) z (ξ ω)) f (ξ ω))) +
      ((∫ ζ, Real.log (pointToPlane β 0 m 0 ζ) ∂disorderLaw) - kpzLatticeCentring ϑ N ((m : ℝ) / N))
  have hξ : Measurable ξ := (Smoothing.measurable_shiftEnvironment _).comp
    (PolymerCalculus.measurePreserving_reversedDisorder L).measurable
  have hA (z : Site) : Measurable (A z) := by
    have hη (w : Site) : Measurable (fun ω => endpointDist β (m - 1) z (ξ ω) w) :=
      (Polymer.measurable_endpointDist β (m - 1) z w).comp hξ
    have hprof (γ : ℝ) := Smoothing.measurable_profileP2Fun_param γ (m - 1) m f hη hξ
    exact (((measurable_pi_apply (m, z)).const_mul β).sub_const _).add
      ((hprof 0).log.sub (hprof β).log) |>.add_const _
  have hsite : Measurable (fun p : Site × Disorder => A p.1 p.2) :=
    measurable_from_prod_countable_right hA
  have hmap : Measurable (fun p : Plane × Disorder => (latticePoint N p.1, p.2)) :=
    ((measurable_latticePoint N).comp measurable_fst).prodMk measurable_snd
  convert hsite.comp hmap using 1
  funext p
  exact kpzLattice_sub_exactReverseField_eq ϑ hN hm hmEven hLEven hmL h₀ p.1 p.2

private theorem kpzLattice_eq_of_clock_eq (ϑ : ℝ) (N : ℕ) (a b : ℝ)
    (h : evenCeil (N * a) = evenCeil (N * b)) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    kpzLattice ϑ N a h₀ x ω = kpzLattice ϑ N b h₀ x ω := by
  simp only [kpzLattice, kpzLatticeCentring, rescaledP2P, h]

private theorem eventually_exact_error_control (ϑ t T : ℝ)
    (ht : 0 < t) (htT : t ≤ T) (h₀ : Plane →ᵇ ℝ) :
    ∀ᶠ N : ℕ in atTop,
      let m := evenCeil ((N : ℝ) * t)
      let L := evenCeil ((N : ℝ) * T)
      let E : Plane → Disorder → ℝ := fun x ω => kpzLattice ϑ N t h₀ x ω -
        kpzLatticeReversed ϑ N (((L - m : ℕ) : ℝ) / N) ((L : ℝ) / N) h₀ x
          (PolymerCalculus.reversedDisorder L ω)
      Measurable (Function.uncurry E) ∧ ∀ x,
        Integrable (fun ω => |E x ω|) disorderLaw ∧
        (∫ ω, |E x ω| ∂disorderLaw) ≤
          |criticalBeta ϑ N| + (criticalBeta ϑ N) ^ 2 +
            Real.sqrt ((criticalBeta ϑ N) ^ 2 + (criticalBeta ϑ N) ^ 4 / 4) := by
  have hcent := Critical2DKPZ.Assembly.kpzLatticeCentring_sub_logPointToPlane_le ϑ t ht
  filter_upwards [eventually_ge_atTop 1, hcent] with N hN hcentN
  dsimp only
  let m := evenCeil ((N : ℝ) * t)
  let L := evenCeil ((N : ℝ) * T)
  have hNpos : 0 < N := by omega
  have hmEven : Even m := evenCeil_even _
  have hLEven : Even L := evenCeil_even _
  have hmL : m ≤ L := evenCeil_mono (mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg N))
  have hm : 1 ≤ m := by
    have hpos : 0 < (N : ℝ) * t := mul_pos (by exact_mod_cast hNpos) ht
    have hle := le_evenCeil ((N : ℝ) * t)
    have hcast : (0 : ℝ) < m := lt_of_lt_of_le hpos hle
    exact_mod_cast hcast
  have hclock : evenCeil ((N : ℝ) * ((m : ℝ) / N)) = m :=
    Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hNpos hmEven
  have hfield (x : Plane) (ω : Disorder) :
      kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω = kpzLattice ϑ N t h₀ x ω :=
    kpzLattice_eq_of_clock_eq ϑ N _ t hclock h₀ x ω
  have hcenterEq : kpzLatticeCentring ϑ N ((m : ℝ) / N) = kpzLatticeCentring ϑ N t := by
    simp only [kpzLatticeCentring, rescaledP2P, hclock]
    rfl
  have hc : |kpzLatticeCentring ϑ N ((m : ℝ) / N) -
      ∫ ζ, Real.log (pointToPlane (criticalBeta ϑ N) 0 m 0 ζ) ∂disorderLaw| ≤
        (criticalBeta ϑ N) ^ 2 / 2 := by
    rw [hcenterEq]
    exact hcentN
  refine ⟨?_, fun x => ?_⟩
  · convert measurable_exact_error ϑ hNpos hm hmEven hLEven hmL h₀ using 1
    funext p
    dsimp only [Function.uncurry]
    rw [hfield]
  · simpa only [hfield] using
      integral_abs_kpzLattice_sub_exactReverseField_le ϑ hNpos hm hmEven hLEven hmL h₀ x hc

/-- Testing the exact reflected-clock lattice reversal error against a compact smooth
function gives an L¹ error tending to zero. Integrability is supplied by the
pointwise error bound and the product-integrability argument in `tested_eLpNorm_one_le`. -/
theorem tendsto_eLpNorm_tested_exactReverseField_error (ϑ t T : ℝ)
    (ht : 0 < t) (htT : t ≤ T) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    Tendsto (fun N : ℕ => eLpNorm (fun ω : Disorder =>
      ∫ x, φ x * (kpzLattice ϑ N t h₀ x ω -
        kpzLatticeReversed ϑ N
          (((evenCeil ((N : ℝ) * T) - evenCeil ((N : ℝ) * t) : ℕ) : ℝ) /
            (N : ℝ))
          (((evenCeil ((N : ℝ) * T) : ℕ) : ℝ) / (N : ℝ)) h₀ x
          (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * T)) ω)))
      1 disorderLaw) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun N => |criticalBeta ϑ N| + (criticalBeta ϑ N) ^ 2 +
    Real.sqrt ((criticalBeta ϑ N) ^ 2 + (criticalBeta ϑ N) ^ 4 / 4)
  have hR : Tendsto R atTop (𝓝 0) := by
    have hc : Continuous (fun b : ℝ => |b| + b ^ 2 + Real.sqrt (b ^ 2 + b ^ 4 / 4)) := by
      fun_prop
    have hh := hc.continuousAt.tendsto.comp
      (Critical2DKPZ.SHF.Moments.tendsto_criticalBeta_zero ϑ)
    convert hh using 1
    · rfl
    · norm_num
  have hbound := eventually_exact_error_control ϑ t T ht htT h₀
  have hlim : Tendsto (fun N => ENNReal.ofReal ((∫ x, |φ x|) * R N)) atTop (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hR.const_mul (∫ x, |φ x|))
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [hbound] with N hN
  have hsec (x : Plane) := hN.1.comp
    (show Measurable (fun ω : Disorder => (x, ω)) from measurable_const.prodMk measurable_id)
  exact tested_eLpNorm_one_le _ φ (R N) hN.1
    (fun x => (integrable_norm_iff (hsec x).aestronglyMeasurable).mp (by
      simpa only [Function.comp_def, Function.uncurry, Real.norm_eq_abs] using (hN.2 x).1))
    (fun x => (hN.2 x).2)

end Critical2DKPZ.LocalSobolev
