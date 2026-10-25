/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Critical2DKPZ.RandomWalk.Port.Walk.Character
public import Critical2DKPZ.RandomWalk.Port.Walk.Basic
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Critical2DKPZ.RandomWalk.Port.Walk.Fourier
public import Critical2DKPZ.RandomWalk.Port.Site

/-! # Fourier representation of the simple random walk kernel

Orthogonality of torus characters and the nearest-neighbour recursion give the Fourier
representation; the cosine Taylor bound controls the characteristic function near zero. -/

@[expose] public section

namespace LatticeProb.LocalCLT

open MeasureTheory

noncomputable section

/-- The coordinate box representing the Fourier torus. -/
def torusBox (d : ℕ) : Set (Fin d → ℝ) := Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi)
/-- Splitting off the first coordinate maps the torus box onto an interval times the lower-dimensional box. -/
theorem torusBox_image_piFinSuccAbove (d : ℕ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0) '' torusBox (d + 1)
      = Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hp' : (x 0, Fin.removeNth 0 x) = p := by
      simpa [MeasurableEquiv.piFinSuccAbove] using hp
    rw [← hp']
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨hx.1 0, hx.2 0⟩, ?_⟩
    refine Set.mem_Icc.mpr ⟨fun j => hx.1 j.succ, fun j => hx.2 j.succ⟩
  · rintro ⟨h1, h2⟩
    simp only [Set.mem_Icc, torusBox] at h1 h2
    refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
    · constructor
      · intro i; induction i using Fin.cases with
        | zero => simpa using h1.1
        | succ j => simpa using h2.1 j
      · intro i; induction i using Fin.cases with
        | zero => simpa using h1.2
        | succ j => simpa using h2.2 j
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]
/-- The Fourier torus box is measurable. -/
theorem torusBox_measurable (d : ℕ) : MeasurableSet (torusBox d) := measurableSet_Icc

/-- A measurable equivalence transports a restricted measure to the corresponding restricted image measure. -/
theorem map_restrict_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Measure.map e (μ.restrict s) = (Measure.map e μ).restrict (e '' s) := by
  ext t ht
  have hL : Measure.map e (μ.restrict s) t = μ (s ∩ e ⁻¹' t) := by
    rw [Measure.map_apply e.measurable ht, Measure.restrict_apply (e.measurable ht)]
    exact congrArg μ (Set.inter_comm _ _)
  have hpre : e ⁻¹' (t ∩ e '' s) = s ∩ e ⁻¹' t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨h1, y, hy, heq⟩
      exact ⟨by have := e.injective heq; subst this; exact hy, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, x, h1, rfl⟩
  have hR : ((Measure.map e μ).restrict (e '' s)) t = μ (s ∩ e ⁻¹' t) := by
    rw [Measure.restrict_apply ht,
      Measure.map_apply e.measurable (MeasurableSet.inter ht ((MeasurableEquiv.measurableSet_image e).mpr hs)), hpre]
  rw [hL, hR]

/-- The inverse coordinate splitting maps an interval times the smaller torus box onto the full box. -/
theorem torusBox_symm_image_piFinSuccAbove (d : ℕ) : torusBox (d+1) = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))).symm '' (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d) := by
  ext x
  constructor
  · intro hx
    exact ⟨(MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))) x,
      torusBox_image_piFinSuccAbove d ▸ Set.mem_image_of_mem _ hx, MeasurableEquiv.symm_apply_apply (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))) x⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz, hez⟩ := (torusBox_image_piFinSuccAbove d) ▸ hy
    have : x = z := by
      rw [← hez] at hxy
      rw [MeasurableEquiv.symm_apply_apply (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))) z] at hxy
      exact hxy.symm
    rw [this]; exact hz

/-- Integration over the torus box can be performed one coordinate at a time. -/
theorem integral_torusBox_peel {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (d + 1) → ℝ) → E) (hf : Integrable f (volume.restrict (torusBox (d + 1)))) :
    ∫ θ in torusBox (d + 1), f θ
      = ∫ t in Set.Icc (-Real.pi) Real.pi, ∫ θ in torusBox d, f (Fin.cons t θ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1)) with he
  have hmp : MeasurePreserving (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) volume volume :=
    MeasurePreserving.symm e (measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => volume) 0)
  have hsm : MeasurableSet (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d) :=
    MeasurableSet.prod (measurableSet_Icc : MeasurableSet (Set.Icc (-Real.pi) Real.pi)) (torusBox_measurable d)
  have h1 : torusBox (d+1) = e.symm '' (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d) := torusBox_symm_image_piFinSuccAbove d
  have hmap : Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) volume = volume := hmp.map_eq
  have hv2 : volume.restrict (e.symm '' (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))
      = Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d)) := by
    rw [map_restrict_measurableEquiv e.symm volume _ hsm, hmap]
  have hmeas : Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))
      = volume.restrict (torusBox (d+1)) := by rw [map_restrict_measurableEquiv e.symm volume _ hsm, hmap, h1]
  have htriv : MeasurePreserving (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ))
      (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))
      (Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))) := ⟨e.symm.measurable, rfl⟩
  have h2 : ∫ θ in torusBox (d+1), f θ
      = ∫ p in Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d, f (e.symm p) := by
    rw [h1, hv2]
    exact (MeasurePreserving.integral_comp htriv (MeasurableEquiv.measurableEmbedding e.symm) f).symm
  have hrr : (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))).restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d)
      = (volume.restrict (Set.Icc (-Real.pi) Real.pi)).prod (volume.restrict (torusBox d)) := by
    rw [show (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) = volume.prod volume from rfl, Measure.prod_restrict]
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) => f (e.symm p))
      ((volume.restrict (Set.Icc (-Real.pi) Real.pi)).prod (volume.restrict (torusBox d))) := by
    rw [← hrr]
    have hfm : Integrable f (Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))) := by rw [hmeas]; exact hf
    exact (MeasurePreserving.integrable_comp htriv hfm.aestronglyMeasurable).mpr hfm
  rw [h2, hrr, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  have hcons : e.symm (t, θ) = Fin.cons t θ := by
    simp [he, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]
  simp only [hcons]


/-- Every integer-frequency torus character is integrable. -/
theorem char_integrable (d : ℕ) (z : Fin (d+1) → ℤ) :
    Integrable (fun θ : Fin (d+1) → ℝ => ∏ j, Complex.exp (Complex.ofReal (θ j * (z j : ℝ)) * Complex.I))
      (volume.restrict (torusBox (d+1))) := by
  have hfin : (MeasureTheory.volume : Measure (Fin (d+1) → ℝ)) (torusBox (d+1)) < ⊤ := by
    have h2 : Set.pi Set.univ (fun i => Set.Ioc (-Real.pi) Real.pi) =ᵐ[(MeasureTheory.volume : Measure (Fin (d+1) → ℝ))] Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) := by
      rw [← Set.pi_univ_Icc]
      exact MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ => volume)
    rw [show torusBox (d+1) = Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) from rfl, ← measure_congr h2, Real.volume_pi_Ioc]
    simp
  have : IsFiniteMeasure (volume.restrict (torusBox (d+1))) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · exact (continuous_finsetProd _ (fun j _ => by continuity)).aestronglyMeasurable
  · filter_upwards with θ
    have h1 : ‖∏ j, Complex.exp (Complex.ofReal (θ j * (z j : ℝ)) * Complex.I)‖ = 1 := by
      rw [norm_prod _ _, Finset.prod_eq_one (fun j _ => by rw [Complex.norm_exp]; simp [Complex.mul_im, Complex.ofReal_im])]
    rw [h1]

/-- Integrating the basic characteristic monomial over the torus gives its orthogonality value. -/
theorem integral_char_one (k : ℤ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, Complex.exp (Complex.ofReal (t * (k : ℝ)) * Complex.I)
      = if k = 0 then 2 * Real.pi else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp
    norm_num [max_eq_left (by positivity : (0:ℝ) ≤ Real.pi + Real.pi)]
    ring
  · rw [ite_eq_right hk]
    have heq : ∀ t : ℝ, Complex.exp (Complex.ofReal (t * (k:ℝ)) * Complex.I)
        = Complex.exp (Complex.ofReal ((k:ℝ) * t) * Complex.I) := fun t => by rw [mul_comm t (k:ℝ)]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall heq)]
    exact LatticeProb.integral_exp_int_mul_restrict k hk

/-- The integral of a torus character is the product of its one-dimensional orthogonality integrals, each equal to `2π` at frequency zero and zero otherwise. -/
theorem integral_box_exp_eq (d : ℕ) (z : Fin d → ℤ) :
    ∫ θ in torusBox d, ∏ j, Complex.exp (Complex.ofReal (θ j * (z j : ℝ)) * Complex.I)
      = ∏ j, (if z j = 0 then 2 * Real.pi else 0) := by
  induction d with
    | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      have h : (Set.Icc (fun _ : Fin 0 => (-Real.pi)) (fun _ : Fin 0 => Real.pi)) = (Set.univ : Set (Fin 0 → ℝ)) := by ext; simp
      rw [MeasureTheory.integral_const]
      simp only [torusBox]
      rw [h, Measure.restrict_univ]
      show ((Measure.pi fun _ => MeasureTheory.volume) Set.univ).toReal • (1:ℂ) = ↑1
      rw [Measure.pi_univ]
      simp
    | succ d ih =>
      rw [integral_torusBox_peel _ (char_integrable d z)]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp only [MeasureTheory.integral_const_mul]
      rw [ih (fun j => z j.succ)]
      rw [MeasureTheory.integral_mul_const]
      rw [integral_char_one (z 0)]
      split
      · simp
      · simp
end

/-- The volume of the torus box is `(2π)^d`. -/
theorem volume_torusBox (d : ℕ) :
    (MeasureTheory.volume : Measure (Fin d → ℝ)) (torusBox d)
      = ENNReal.ofReal ((2 * Real.pi) ^ d) := by
  have h1 : torusBox d = Set.univ.pi (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi) := by
    rw [show torusBox d = Set.Icc (fun _ : Fin d => (-Real.pi)) (fun _ : Fin d => Real.pi) from rfl,
        ← Set.pi_univ_Icc]
  rw [h1]
  have h2 : Set.univ.pi (fun _ : Fin d => Set.Ioc (-Real.pi) Real.pi)
      =ᵐ[(MeasureTheory.volume : Measure (Fin d → ℝ))]
        Set.univ.pi (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi) :=
    MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : Fin d => volume)
  rw [← MeasureTheory.measure_congr h2, Real.volume_pi_Ioc]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2 * Real.pi)]


/-- The normalized character integral is the Kronecker delta at the origin. -/
theorem integral_char_delta (d : ℕ) (x : Site d) :
    (∫ θ in torusBox d, ∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
      / (2 * Real.pi) ^ d
      = if x = 0 then 1 else 0 := by
  rw [integral_box_exp_eq d x]
  by_cases hx : x = 0
  · subst hx
    have h1 : ∏ j, (if (0 : Fin d → ℤ) j = 0 then 2 * Real.pi else 0) = (2 * Real.pi) ^ d := by
      simp [Finset.prod_const]
    rw [h1, ite_eq_left rfl]
    norm_num [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_one]
  · have h0 : ∏ j, (if x j = 0 then 2 * Real.pi else 0) = 0 := by
      by_contra hne
      have hall : ∀ j, x j = 0 := by
        intro j
        by_contra hxj
        have hz : (if x j = 0 then 2 * Real.pi else 0) = 0 := ite_eq_right hxj
        exact hne (Finset.prod_eq_zero (Finset.mem_univ j) hz)
      exact hx (funext hall)
    rw [h0, ite_eq_right hx]
    simp


/-- A characteristic monomial factors into the monomials of a base point and its displacement. -/
theorem char_sub (d : ℕ) (θ : Fin d → ℝ) (x y : Site d) :
    (∏ j, Complex.exp (Complex.ofReal (θ j * ((y j : ℤ) : ℝ)) * Complex.I))
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * ∏ j, Complex.exp (Complex.ofReal (θ j * (((y - x) j : ℤ) : ℝ)) * Complex.I) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- The characteristic monomial at a unit vector is the corresponding coordinate phase. -/
theorem char_unit (d : ℕ) (θ : Fin d → ℝ) (i : Fin d) :
    ∏ j, Complex.exp (Complex.ofReal (θ j * (((unit i) j : ℤ) : ℝ)) * Complex.I)
      = Complex.exp (Complex.ofReal (θ i) * Complex.I) := by
  have h1 : ((unit i) i : ℤ) = 1 := by simp [unit]
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin d)), j ≠ i →
      Complex.exp (Complex.ofReal (θ j * (((unit i) j : ℤ) : ℝ)) * Complex.I) = 1 := by
    intro j _ hj
    have huj : (unit i) j = 0 := by simp [unit, hj]
    simp [huj, Complex.exp_zero, mul_zero]
  rw [Finset.prod_eq_single i h0 (fun h => absurd (Finset.mem_univ i) h), h1]; norm_num

/-- The character of the negated unit vector. -/
theorem char_neg_unit (d : ℕ) (θ : Fin d → ℝ) (i : Fin d) :
    ∏ j, Complex.exp (Complex.ofReal (θ j * (((-unit i) j : ℤ) : ℝ)) * Complex.I)
      = Complex.exp (-(Complex.ofReal (θ i) * Complex.I)) := by
  have h1 : ((-unit i) i : ℤ) = -1 := by simp [unit]
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin d)), j ≠ i →
      Complex.exp (Complex.ofReal (θ j * (((-unit i) j : ℤ) : ℝ)) * Complex.I) = 1 := by
    intro j _ hj
    have huj : (-unit i) j = 0 := by
      have hu : (unit i) j = 0 := by simp [unit, hj]
      simp [Pi.neg_apply, hu]
    simp [huj, Complex.exp_zero, mul_zero]
  rw [Finset.prod_eq_single i h0 (fun h => absurd (Finset.mem_univ i) h), h1]
  congr 1
  push_cast
  ring
/-- The two-point average of the exponential is the cosine. -/
theorem exp_pair_eq_cos (z : ℂ) :
    Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) = 2 * Complex.cos z := by
  rw [Complex.cos]
  ring

/-- The sum over all `2d` directions of the character at `x + dirVec a`
equals the character at `x` times twice the sum of the cosines. -/
theorem char_dir_sum (d : ℕ) (θ : Fin d → ℝ) (x : Site d) :
    ∑ a : Dir d, ∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec a) j : ℤ) : ℝ)) * Complex.I)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (2 * ∑ i : Fin d, Real.cos (θ i)) := by
  rw [show (Finset.univ : Finset (Dir d)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product]
  have hpair : ∀ i : Fin d,
      (∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec (i, true)) j : ℤ) : ℝ)) * Complex.I))
      + (∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec (i, false)) j : ℤ) : ℝ)) * Complex.I))
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (2 * Complex.ofReal (Real.cos (θ i))) := by
    intro i
    have hp := char_sub d θ x (x + dirVec (i, true))
    have hm := char_sub d θ x (x + dirVec (i, false))
    have hpt : (x + dirVec (i, true)) - x = unit i := by
      funext j; by_cases hji : j = i <;> simp [dirVec, unit, hji]
    have hmt : (x + dirVec (i, false)) - x = -unit i := by
      funext j; by_cases hji : j = i <;> simp [dirVec, unit, hji]
    rw [hp, hm, hpt, hmt, char_unit d θ i, char_neg_unit d θ i, ← mul_add, exp_pair_eq_cos, ← Complex.ofReal_cos]
  have hbool : ∀ i : Fin d, ∑ y : Bool, ∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec (i, y)) j : ℤ) : ℝ)) * Complex.I)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (2 * Complex.ofReal (Real.cos (θ i))) := by
    intro i; simp_rw [← hpair i]; simp
  simp_rw [hbool, Complex.ofReal_sum]
  simp only [Finset.mul_sum]

/-- Multiplication by the characteristic function equals averaging over the signed nearest-neighbour displacements. -/
theorem fourier_integrand_succ (d : ℕ) (j : ℕ) (x : Site d) (θ : Fin d → ℝ) :
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
        * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ (j + 1)
    = (∑ a : Dir d, (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
        * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) / (2 * d) := by
  have h := char_dir_sum d θ x
  rw [← Finset.sum_mul, h, pow_succ]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · simp [show d = 0 by omega]
  · have hd' : ((d : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
    have h2d : (2 * (d : ℂ)) ≠ 0 := by
      exact mul_ne_zero two_ne_zero hd'
    field_simp
    have hcomm : ∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I)
        = ∏ k, Complex.exp (Complex.I * Complex.ofReal (θ k * ((x k : ℤ) : ℝ))) := by
      refine Finset.prod_congr rfl (fun k _ => ?_)
      congr 1; ring
    rw [hcomm]
    ring

/-- A finite sum over directions commutes with integration when each summand is integrable. -/
theorem fourier_swap (d : ℕ)
    (g : Dir d → (Fin d → ℝ) → ℂ)
    (hint : ∀ a : Dir d, Integrable (g a) (volume.restrict (torusBox d))) :
    (∑ a : Dir d, ∫ θ in torusBox d, g a θ) = ∫ θ in torusBox d, ∑ a : Dir d, g a θ :=
  by rw [MeasureTheory.integral_finsetSum Finset.univ (fun a _ => hint a)]

/-- The Fourier normalization constant `(2π)^d` is nonzero. -/
theorem two_pi_pow_ne_zero (d : ℕ) : ((2 * Real.pi) ^ d : ℂ) ≠ 0 :=
  pow_ne_zero d (mul_ne_zero two_ne_zero (by exact_mod_cast (ne_of_gt Real.pi_pos)))

/-- The common factor `2d` cancels from the Fourier normalization in positive dimension. -/
theorem fourier_final_algebra (d : ℕ) (hd : 1 ≤ d) (A : ℂ) :
    (A * (2 * (d : ℂ))) / ((2 * Real.pi) ^ d * (2 * (d : ℂ))) = A / (2 * Real.pi) ^ d := by
  have hp : ((2 * Real.pi) ^ d : ℂ) ≠ 0 := two_pi_pow_ne_zero d
  have hd' : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by omega))
  have h2d : (2 * (d : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hd'
  field_simp

/-- The Fourier integrand is almost everywhere strongly measurable on the torus box. -/
theorem fourier_integrand_aemeasurable (d : ℕ) (j : ℕ) (x : Site d) :
    AEStronglyMeasurable (fun θ : Fin d → ℝ ↦
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
      (volume.restrict (torusBox d)) := by
  fun_prop

/-- The Fourier integrand is bounded by one in norm. -/
theorem fourier_integrand_norm_le_one (d : ℕ) (j : ℕ) (x : Site d)
    (θ : Fin d → ℝ) :
    ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j‖ ≤ 1 := by
  have hle : |(∑ i : Fin d, Real.cos (θ i))| ≤ (d : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs (fun i => Real.cos (θ i)) Finset.univ) ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have havg : |(∑ i : Fin d, Real.cos (θ i))| / (d : ℝ) ≤ 1 :=
    div_le_one_of_le₀ hle (Nat.cast_nonneg d)
  have hd : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg d)
  have h1 : ‖Complex.ofReal (∑ i : Fin d, Real.cos (θ i))‖ = |(∑ i : Fin d, Real.cos (θ i))| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖((d : ℕ) : ℂ)‖ = |(d : ℝ)| := by simp
  apply le_trans (norm_mul_le _ _)
  have ha : ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))‖ ≤ 1 := by
    rw [norm_prod]
    simp [Complex.norm_exp]
  refine (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans ?_
  rw [one_mul]
  rw [norm_pow, norm_div, h1, h2, hd]
  exact pow_le_one₀ (div_nonneg (abs_nonneg _) (Nat.cast_nonneg d)) havg

/-- The Fourier integrand is integrable: it is bounded by one on a finite box. -/
theorem fourier_integrand_integrable (d : ℕ) (j : ℕ) (x : Site d) :
    Integrable (fun θ : Fin d → ℝ ↦
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
      (volume.restrict (torusBox d)) := by
  have hfin : (MeasureTheory.volume : Measure (Fin d → ℝ)) (torusBox d) < ⊤ := by
    have h2 : Set.pi Set.univ (fun i => Set.Ioc (-Real.pi) Real.pi) =ᵐ[(MeasureTheory.volume : Measure (Fin d → ℝ))] Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) := by
      rw [← Set.pi_univ_Icc]
      exact MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ => volume)
    rw [show torusBox d = Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) from rfl, ← measure_congr h2, Real.volume_pi_Ioc]
    simp
  have : IsFiniteMeasure (volume.restrict (torusBox d)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · exact fourier_integrand_aemeasurable d j x
  · filter_upwards with θ
    exact fourier_integrand_norm_le_one d j x θ

/-- The simple random walk kernel is the torus integral of its character times the corresponding power of the characteristic function, divided by `(2π)^d`. -/
theorem srwHeat_eq_fourier {d : ℕ} (hd : 1 ≤ d)
    (j : ℕ) (x : Site d) :
    (srwHeat d j x : ℂ) =
      (∫ θ in torusBox d, (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
        * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) / (2 * Real.pi) ^ d := by
  have hint : ∀ (j : ℕ) (x : Site d),
    Integrable (fun θ => (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) (volume.restrict (torusBox d)) :=
    fun j x => fourier_integrand_integrable d j x
  induction j generalizing x with
  | zero =>
      rw [srwHeat_zero]
      simp only [pow_zero, mul_one]
      rw [integral_char_delta d x]
      by_cases hx : x = 0 <;> simp [hx]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      have hsum : (((∑ a : Dir d, srwHeat d j (x + dirVec a)) / (2 * (d : ℝ)) : ℝ) : ℂ)
          = ((∑ a : Dir d, ∫ θ in torusBox d,
              (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
                * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)) / ((2 * Real.pi) ^ d * (2 * (d : ℝ))) := by
        rw [Complex.ofReal_div, Complex.ofReal_sum]
        show (∑ a : Dir d, ((srwHeat d j (x + dirVec a) : ℝ) : ℂ)) / Complex.ofReal (2 * (d : ℝ)) = _
        simp only [Finset.sum_div]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [ih (x + dirVec a), div_div]
        push_cast
        ring
      rw [hsum]
      rw [fourier_swap d (fun a θ => (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I)) * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) (fun a => hint j (x + dirVec a))]
      have hI : (∫ θ in torusBox d, ∑ a : Dir d,
            (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
              * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
          = ∫ θ in torusBox d,
            (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
              * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ (j + 1) * (2 * (d : ℂ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        show (∑ a : Dir d, (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
            * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
          = (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
            * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ (j + 1) * (2 * (d : ℂ))
        rw [fourier_integrand_succ d j x θ]
        have h2d : (2 * (d : ℂ)) ≠ 0 :=
          mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hd)))
        field_simp
        have hcomm : ∀ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I)
            = Complex.exp (Complex.I * Complex.ofReal (θ k * ((x k : ℤ) : ℝ))) := by
          intro k; congr 1; ring
        simp only [mul_comm]
        have hd' : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hd))
        rw [mul_div_cancel_left₀ _ hd']
      rw [hI, integral_mul_const]
      exact fourier_final_algebra d hd _

/-- For `|t| ≤ π`, the cosine is bounded above by its quartic Taylor polynomial `1 - t²/2 + t⁴/24`. -/
theorem cos_le_one_sub_half_sq_add_quartic (t : ℝ) (ht : |t| ≤ Real.pi) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have heven : Real.cos t = Real.cos |t| := by
    rcases abs_cases t with h | h
    · rw [h.1]
    · rw [h.1, Real.cos_neg]
  rw [heven]
  have h0 : 0 ≤ |t| := abs_nonneg t
  have hpi : |t| ≤ Real.pi := ht
  have key : Real.cos |t| = 1 - 2 * Real.sin (|t| / 2) ^ 2 := by
    rw [show |t| = 2 * (|t| / 2) from by ring, Real.cos_two_mul, Real.sin_sq]
    ring
  rw [key]
  have hnn : 0 ≤ Real.sin (|t| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin : |t| / 2 - (|t| / 2) ^ 3 / 6 ≤ Real.sin (|t| / 2) :=
    Real.sin_ge_sub_cube (by linarith)
  have hbase : 0 ≤ |t| / 2 - (|t| / 2) ^ 3 / 6 := by
    have hp2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have hs2 : (|t| / 2) ^ 2 ≤ 6 := by nlinarith [hp2, hpi, h0]
    nlinarith [hs2]
  have hsq : (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 ≤ Real.sin (|t| / 2) ^ 2 :=
    pow_le_pow_left₀ hbase hsin 2
  have h2 : 2 * (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 ≤ 2 * Real.sin (|t| / 2) ^ 2 := by nlinarith [hsq]
  have h4 : 1 - 2 * (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 ≤ 1 - |t| ^ 2 / 2 + |t| ^ 4 / 24 := by
    have hu4 : (0 : ℝ) ≤ (|t| / 2) ^ 4 := by positivity
    have hu6 : (0 : ℝ) ≤ (|t| / 2) ^ 6 := by positivity
    nlinarith [hu4, hu6]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have ht4 : t ^ 4 = |t| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)]
  rw [ht2, ht4]
  have hexp : (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 = |t| ^ 2 / 4 - |t| ^ 4 / 48 + |t| ^ 6 / 2304 := by ring
  nlinarith [hsq, hexp, sq_nonneg (|t| ^ 3)]

/-- The torus measure is the restriction of volume to the torus box. -/
theorem torusMeasure_eq_restrict (d : ℕ) :
    torusMeasure d = volume.restrict (torusBox d) := by
  show Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (-Real.pi) Real.pi)) =
    volume.restrict (Set.Icc (fun _ : Fin d => -Real.pi) (fun _ : Fin d => Real.pi))
  have h : Set.Icc (fun _ : Fin d => -Real.pi) (fun _ : Fin d => Real.pi) =
      Set.univ.pi (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi) := by
    ext x
    simp [Set.mem_Icc, Pi.le_def]
  rw [h]
  exact (Measure.restrict_pi_pi (fun _ : Fin d => (volume : Measure ℝ))
    (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi)).symm


end LatticeProb.LocalCLT

end
