/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
import Mathlib.Tactic

/-!
# Exact interval and endpoint expansions for finite block kernels
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Blocks

/-- A finite support bound for an open discrepancy numerator. -/
def openCorrectorNumeratorSupport (t : ℕ → ℕ) (u s : ℕ) : Finset Site :=
  (Polymer.endpoints 0 (t (u - 1))).biUnion
    (fun x => discrepancyStringSupport t u (s + 1 - u) x)

/-- The open discrepancy numerator vanishes outside its finite walk support. -/
theorem openCorrectorNumerator_eq_zero_of_not_mem_support (β : ℝ) (t : ℕ → ℕ)
    (u s : ℕ) (ω : Disorder) (y : Site)
    (hy : y ∉ openCorrectorNumeratorSupport t u s) :
    openCorrectorNumerator β t u s ω y = 0 := by
  unfold openCorrectorNumerator
  calc
    _ = ∑' x, (0 : ℝ) := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ Polymer.endpoints 0 (t (u - 1))
      · have hyx : y ∉ discrepancyStringSupport t u (s + 1 - u) x := by
          intro hmem
          exact hy (Finset.mem_biUnion.2 ⟨x, hx, hmem⟩)
        rw [discrepancyString_eq_zero_of_not_mem_support β t u (s + 1 - u)
          x y ω hyx]
        simp
      · have hx0 : srwKernel (t (u - 1)) x = 0 := by
          simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem
            (t (u - 1)) 0 x hx
        rw [hx0]
        simp
    _ = 0 := tsum_zero

/-- For a one-block range, the open numerator is the heat average of one discrepancy. -/
theorem openCorrectorNumerator_self (β : ℝ) (t : ℕ → ℕ) (u : ℕ)
    (ω : Disorder) (y : Site) :
    openCorrectorNumerator β t u u ω y =
      ∑' z, srwKernel (t (u - 1)) z * blockDiscrepancy β t u z y ω := by
  unfold openCorrectorNumerator
  have hlen : u + 1 - u = 1 := by omega
  rw [hlen]
  simp_rw [discrepancyString_one]

/-- Closing an open discrepancy profile with the next block gives the closed activity. -/
theorem closedDiscrepancy_eq_openNumerator_close (β : ℝ) (t : ℕ → ℕ)
    (u s : ℕ) (hus : u < s) (ω : Disorder) :
    closedDiscrepancy β t u s ω =
      ∑' y, openCorrectorNumerator β t u (s - 1) ω y *
        pointToPlane β (t (s - 1)) (t s - t (s - 1)) y ω := by
  let k := s - u
  let a := t (u - 1)
  let sx := Polymer.endpoints 0 a
  let sy := sx.biUnion (fun x => discrepancyStringSupport t u k x)
  have hlen : s - 1 + 1 - u = k := by dsimp [k]; omega
  have hdouble : Summable (fun p : Site × Site =>
      srwKernel a p.1 * discrepancyString β t u k p.1 p.2 ω *
        pointToPlane β (t (s - 1)) (t s - t (s - 1)) p.2 ω) := by
    apply summable_of_ne_finset_zero (s := sx ×ˢ sy)
    intro p hp
    by_cases hx : p.1 ∈ sx
    · by_cases hy : p.2 ∈ sy
      · exact (hp (Finset.mem_product.mpr ⟨hx, hy⟩)).elim
      · have hy' : p.2 ∉ discrepancyStringSupport t u k p.1 := by
          intro hmem
          exact hy (Finset.mem_biUnion.2 ⟨p.1, hx, hmem⟩)
        rw [discrepancyString_eq_zero_of_not_mem_support β t u k p.1 p.2 ω hy']
        simp
    · have hx0 : srwKernel a p.1 = 0 := by
        simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem a 0 p.1 hx
      rw [hx0]
      simp
  calc
    _ = ∑' x, ∑' y, srwKernel a x * discrepancyString β t u k x y ω *
          pointToPlane β (t (s - 1)) (t s - t (s - 1)) y ω := by
      unfold closedDiscrepancy
      dsimp [a, k]
    _ = ∑' y, ∑' x, srwKernel a x * discrepancyString β t u k x y ω *
          pointToPlane β (t (s - 1)) (t s - t (s - 1)) y ω :=
        (Summable.tsum_comm (f := fun x y => srwKernel a x *
          discrepancyString β t u k x y ω *
            pointToPlane β (t (s - 1)) (t s - t (s - 1)) y ω) hdouble).symm
    _ = ∑' y, (∑' x, srwKernel a x * discrepancyString β t u k x y ω) *
          pointToPlane β (t (s - 1)) (t s - t (s - 1)) y ω := by
      apply tsum_congr
      intro y
      rw [← tsum_mul_right]
    _ = ∑' y, openCorrectorNumerator β t u (s - 1) ω y *
          pointToPlane β (t (s - 1)) (t s - t (s - 1)) y ω := by
      apply tsum_congr
      intro y
      unfold openCorrectorNumerator
      rw [hlen]

/-- The unnormalized endpoint profile on one block has one heat reset and one correction. -/
theorem blockEndpointNumerator_singleBlock_expansion (β : ℝ) (t : ℕ → ℕ)
    (u : ℕ) (ω : Disorder) (y : Site) :
    blockEndpointNumerator β t u u ω y =
      blockMass β t u ω * srwKernel (t u) y +
        openCorrectorNumerator β t u u ω y := by
  have hm : 0 < blockMass β t u ω := blockMass_pos β t u ω
  have hdist := smoothedEndpointDist_singleBlock_expansion β t u ω y
  have hU : smoothedEndpointDist β (t (u - 1)) (t u) 0 ω y =
      blockEndpointNumerator β t u u ω y / blockMass β t u ω := by
    unfold smoothedEndpointDist blockEndpointNumerator blockMass
    simp only [sub_zero]
  have hO : openCorrector β t u u ω y =
      openCorrectorNumerator β t u u ω y / blockMass β t u ω := by
    unfold openCorrector
    simp only [Finset.Icc_self, Finset.prod_singleton]
  rw [hU, hO] at hdist
  field_simp [ne_of_gt hm] at hdist
  simpa [mul_comm, add_comm, add_left_comm] using hdist

/-- The unnormalized endpoint profile is a sum over open discrepancy strings. -/
theorem blockEndpointNumerator_intervalExpansion (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hrs : r ≤ s) (ω : Disorder) (y : Site) :
    blockEndpointNumerator β t r s ω y =
      smoothedP2Plane β (t (r - 1)) (t s) 0 ω * srwKernel (t s) y +
        ∑ u ∈ Finset.Icc r s,
          smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
            openCorrectorNumerator β t u s ω y := by
  induction s using Nat.strong_induction_on generalizing r y with
  | h s ih =>
      by_cases hbase : r = s
      · subst r
        rw [blockEndpointNumerator_singleBlock_expansion]
        rw [Finset.Icc_self, Finset.sum_singleton]
        rw [smoothedP2Plane_eq_one_of_eq β (t (s - 1)) ω]
        unfold blockMass
        ring
      · have hrs' : r ≤ s - 1 := by omega
        have hidx : s - 1 + 1 = s := by omega
        have hprev := ih (s - 1) (by omega) r hrs'
        have hrec := blockEndpointNumerator_discrepancyRecurrence
          β t ht r (s - 1) hrs' ω y
        rw [hidx] at hrec
        let q : Site → ℝ := fun z => srwKernel (t (s - 1)) z
        let d : Site → ℝ := fun z => blockDiscrepancy β t s z y ω
        let M := smoothedP2Plane β (t (r - 1)) (t (s - 1)) 0 ω
        let S := Finset.Icc r (s - 1)
        let c : ℕ → ℝ := fun u =>
          smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω
        have hprevPoint (z : Site) :
            blockEndpointNumerator β t r (s - 1) ω z =
              M * q z + ∑ u ∈ S, c u * openCorrectorNumerator β t u (s - 1) ω z := by
          simpa [M, q, S, c] using hprev z
        have hqD : Summable (fun z : Site => M * q z * d z) := by
          apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 (t (s - 1)))
          intro z hz
          have hq0 : q z = 0 := by
            dsimp [q]
            simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem
              (t (s - 1)) 0 z hz
          rw [hq0]
          simp
        have hterm (u : ℕ) :
            Summable (fun z : Site =>
              (c u * openCorrectorNumerator β t u (s - 1) ω z) * d z) := by
          apply summable_of_ne_finset_zero
            (s := openCorrectorNumeratorSupport t u (s - 1))
          intro z hz
          rw [openCorrectorNumerator_eq_zero_of_not_mem_support
            β t u (s - 1) ω z hz]
          simp
        let Ssupport := S.biUnion (fun u => openCorrectorNumeratorSupport t u (s - 1))
        have hsumAll : Summable (fun z : Site =>
            ∑ u ∈ S,
              (c u * openCorrectorNumerator β t u (s - 1) ω z) * d z) := by
          apply summable_of_ne_finset_zero (s := Ssupport)
          intro z hz
          apply Finset.sum_eq_zero
          intro u hu
          have hzero : openCorrectorNumerator β t u (s - 1) ω z = 0 := by
            have hz' : z ∉ openCorrectorNumeratorSupport t u (s - 1) := by
              intro hmem
              exact hz (Finset.mem_biUnion.2 ⟨u, hu, hmem⟩)
            exact openCorrectorNumerator_eq_zero_of_not_mem_support
              β t u (s - 1) ω z hz'
          rw [hzero]
          simp
        have hsumIh :
            (∑' z, blockEndpointNumerator β t r (s - 1) ω z * d z) =
              M * (∑' z, q z * d z) +
                ∑ u ∈ S, c u * openCorrectorNumerator β t u s ω y := by
          calc
            _ = ∑' z, (M * q z +
                  ∑ u ∈ S, c u * openCorrectorNumerator β t u (s - 1) ω z) * d z := by
              apply tsum_congr
              intro z
              rw [hprevPoint z]
            _ = ∑' z, (M * q z * d z +
                  ∑ u ∈ S,
                    (c u * openCorrectorNumerator β t u (s - 1) ω z) * d z) := by
              apply tsum_congr
              intro z
              rw [add_mul, Finset.sum_mul]
            _ = (∑' z, M * q z * d z) +
                  ∑' z, ∑ u ∈ S,
                    (c u * openCorrectorNumerator β t u (s - 1) ω z) * d z :=
              hqD.tsum_add hsumAll
            _ = M * (∑' z, q z * d z) +
                  ∑ u ∈ S, c u *
                    (∑' z, openCorrectorNumerator β t u (s - 1) ω z * d z) := by
              congr 1
              · calc
                  _ = ∑' z, M * (q z * d z) := by
                    apply tsum_congr
                    intro z
                    ring
                  _ = _ := tsum_mul_left
              · calc
                  _ = ∑ u ∈ S, ∑' z,
                        (c u * openCorrectorNumerator β t u (s - 1) ω z) * d z :=
                    Summable.tsum_finsetSum (fun u hu => hterm u)
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    calc
                      _ = ∑' z, c u *
                            (openCorrectorNumerator β t u (s - 1) ω z * d z) := by
                        apply tsum_congr
                        intro z
                        ring
                      _ = _ := tsum_mul_left
            _ = M * (∑' z, q z * d z) +
                  ∑ u ∈ S, c u * openCorrectorNumerator β t u s ω y := by
              congr 1
              apply Finset.sum_congr rfl
              intro u hu
              have happend := openCorrectorNumerator_append β t u (s - 1) (by
                have := Finset.mem_Icc.mp hu
                omega) ω y
              rw [hidx] at happend
              rw [happend]
        have hnew :
            ∑ u ∈ S, c u * openCorrectorNumerator β t u s ω y +
                c s * openCorrectorNumerator β t s s ω y =
              ∑ u ∈ Finset.Icc r s,
                smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
                  openCorrectorNumerator β t u s ω y := by
          have hIcc : Finset.Icc r s = S ∪ {s} := by
            ext u
            simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton, S]
            omega
          have hdisj : Disjoint S {s} := by
            apply Finset.disjoint_left.mpr
            intro u hu hs
            simp only [Finset.mem_singleton] at hs
            change u ∈ Finset.Icc r (s - 1) at hu
            simp only [Finset.mem_Icc] at hu
            omega
          rw [hIcc, Finset.sum_union hdisj, Finset.sum_singleton]
        calc
          blockEndpointNumerator β t r s ω y =
              smoothedP2Plane β (t (r - 1)) (t s) 0 ω * srwKernel (t s) y +
                ∑' z, blockEndpointNumerator β t r (s - 1) ω z * d z := by
            exact hrec
          _ = smoothedP2Plane β (t (r - 1)) (t s) 0 ω * srwKernel (t s) y +
                (M * (∑' z, q z * d z) +
                  ∑ u ∈ S, c u * openCorrectorNumerator β t u s ω y) := by
            rw [hsumIh]
          _ = smoothedP2Plane β (t (r - 1)) (t s) 0 ω * srwKernel (t s) y +
                (∑ u ∈ S, c u * openCorrectorNumerator β t u s ω y +
                  c s * openCorrectorNumerator β t s s ω y) := by
            rw [← openCorrectorNumerator_self β t s ω y]
            dsimp [M, q, d, c]
            ring
          _ = _ := by rw [hnew]

/-- Adding the last block closes each open term into its closed interval activity. -/
theorem smoothedP2Plane_blockMass_recurrence (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hrs : r < s) (ω : Disorder) :
    smoothedP2Plane β (t (r - 1)) (t s) 0 ω =
      smoothedP2Plane β (t (r - 1)) (t (s - 1)) 0 ω * blockMass β t s ω +
        ∑ u ∈ Finset.Icc r (s - 1),
          smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
            closedDiscrepancy β t u s ω := by
  have hrs' : r ≤ s - 1 := by omega
  have hidx : s - 1 + 1 = s := by omega
  have hreset := blockEndpointNumerator_resetCoeff β t ht r (s - 1) hrs' ω
  rw [hidx] at hreset
  let q : Site → ℝ := fun z => srwKernel (t (s - 1)) z
  let p : Site → ℝ := fun z =>
    pointToPlane β (t (s - 1)) (t s - t (s - 1)) z ω
  let M := smoothedP2Plane β (t (r - 1)) (t (s - 1)) 0 ω
  let S := Finset.Icc r (s - 1)
  let c : ℕ → ℝ := fun u =>
    smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω
  have hqP : Summable (fun z : Site => M * q z * p z) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 (t (s - 1)))
    intro z hz
    have hq0 : q z = 0 := by
      dsimp [q]
      simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem
        (t (s - 1)) 0 z hz
    rw [hq0]
    simp
  have hterm (u : ℕ) :
      Summable (fun z : Site =>
        (c u * openCorrectorNumerator β t u (s - 1) ω z) * p z) := by
    apply summable_of_ne_finset_zero
      (s := openCorrectorNumeratorSupport t u (s - 1))
    intro z hz
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support
      β t u (s - 1) ω z hz]
    simp
  let Ssupport := S.biUnion (fun u => openCorrectorNumeratorSupport t u (s - 1))
  have hsumAll : Summable (fun z : Site =>
      ∑ u ∈ S,
        (c u * openCorrectorNumerator β t u (s - 1) ω z) * p z) := by
    apply summable_of_ne_finset_zero (s := Ssupport)
    intro z hz
    apply Finset.sum_eq_zero
    intro u hu
    have hzero : openCorrectorNumerator β t u (s - 1) ω z = 0 := by
      have hz' : z ∉ openCorrectorNumeratorSupport t u (s - 1) := by
        intro hmem
        exact hz (Finset.mem_biUnion.2 ⟨u, hu, hmem⟩)
      exact openCorrectorNumerator_eq_zero_of_not_mem_support
        β t u (s - 1) ω z hz'
    rw [hzero]
    simp
  have hprofile (z : Site) :
      blockEndpointNumerator β t r (s - 1) ω z =
        M * q z + ∑ u ∈ S, c u * openCorrectorNumerator β t u (s - 1) ω z := by
    simpa [M, q, S, c] using
      blockEndpointNumerator_intervalExpansion β t ht r (s - 1) hrs' ω z
  have hclose (u : ℕ) (hu : u ∈ S) :
      (∑' z, openCorrectorNumerator β t u (s - 1) ω z * p z) =
        closedDiscrepancy β t u s ω := by
    have hus : u < s := by
      rcases Finset.mem_Icc.mp hu with ⟨_, huS⟩
      omega
    rw [closedDiscrepancy_eq_openNumerator_close β t u s hus ω]
  have hqMass : ∑' z, q z * p z = blockMass β t s ω := by
    unfold blockMass smoothedP2Plane
    simp only [q, p, sub_zero]
  have hsumExpansion :
      (∑' z, blockEndpointNumerator β t r (s - 1) ω z * p z) =
        M * blockMass β t s ω +
          ∑ u ∈ S, c u * closedDiscrepancy β t u s ω := by
    calc
      _ = ∑' z, (M * q z +
            ∑ u ∈ S, c u * openCorrectorNumerator β t u (s - 1) ω z) * p z := by
        apply tsum_congr
        intro z
        rw [hprofile z]
      _ = ∑' z, (M * q z * p z +
            ∑ u ∈ S,
              (c u * openCorrectorNumerator β t u (s - 1) ω z) * p z) := by
        apply tsum_congr
        intro z
        rw [add_mul, Finset.sum_mul]
      _ = (∑' z, M * q z * p z) +
            ∑' z, ∑ u ∈ S,
              (c u * openCorrectorNumerator β t u (s - 1) ω z) * p z :=
        hqP.tsum_add hsumAll
      _ = M * (∑' z, q z * p z) +
            ∑ u ∈ S, c u *
              (∑' z, openCorrectorNumerator β t u (s - 1) ω z * p z) := by
        congr 1
        · calc
            _ = ∑' z, M * (q z * p z) := by
              apply tsum_congr
              intro z
              ring
            _ = _ := tsum_mul_left
        · calc
            _ = ∑ u ∈ S, ∑' z,
                  (c u * openCorrectorNumerator β t u (s - 1) ω z) * p z :=
              Summable.tsum_finsetSum (fun u hu => hterm u)
            _ = _ := by
              apply Finset.sum_congr rfl
              intro u hu
              calc
                _ = ∑' z, c u *
                      (openCorrectorNumerator β t u (s - 1) ω z * p z) := by
                  apply tsum_congr
                  intro z
                  ring
                _ = _ := tsum_mul_left
      _ = M * blockMass β t s ω +
            ∑ u ∈ S, c u * closedDiscrepancy β t u s ω := by
        rw [hqMass]
        apply congrArg (fun x => M * blockMass β t s ω + x)
        apply Finset.sum_congr rfl
        intro u hu
        rw [hclose u hu]
  rw [hreset, hsumExpansion]

/-- Products of block masses split at the first index of a suffix. -/
theorem blockMass_product_split (β : ℝ) (t : ℕ → ℕ) (r u s : ℕ)
    (hr : 1 ≤ r) (hru : r ≤ u) (hus : u ≤ s) (ω : Disorder) :
    (∏ i ∈ Finset.Icc r (u - 1), blockMass β t i ω) *
        ∏ i ∈ Finset.Icc u s, blockMass β t i ω =
      ∏ i ∈ Finset.Icc r s, blockMass β t i ω := by
  have hu : 1 ≤ u := le_trans hr hru
  have hsplit : Finset.Icc r s = Finset.Icc r (u - 1) ∪ Finset.Icc u s := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc r (u - 1)) (Finset.Icc u s) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_Icc] at hi hj
    omega
  rw [hsplit, Finset.prod_union hdisj]

/-- Membership in `intervalFamilies` records exactly the endpoint and separation conditions. -/
theorem intervalFamilies_mem_iff (r s : ℕ) (F : Finset (ℕ × ℕ)) :
    F ∈ intervalFamilies r s ↔
      (∀ I ∈ F, r ≤ I.1 ∧ I.1 ≤ s ∧ r ≤ I.2 ∧ I.2 ≤ s ∧ I.1 < I.2) ∧
      (∀ I ∈ F, ∀ J ∈ F, I ≠ J → I.2 < J.1 ∨ J.2 < I.1) := by
  unfold intervalFamilies
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff,
    Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  simp only [and_assoc]

/-- A disjoint family has at most one interval with a given right endpoint. -/
theorem intervalFamilies_rightEndpoint_unique {r s : ℕ}
    {F : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s) {v : ℕ}
    {I J : ℕ × ℕ} (hI : I ∈ F) (hJ : J ∈ F)
    (hIv : I.2 = v) (hJv : J.2 = v) : I = J := by
  by_contra hne
  have hsep := (intervalFamilies_mem_iff r s F).mp hF |>.2 I hI J hJ hne
  have hboundI := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
  have hboundJ := (intervalFamilies_mem_iff r s F).mp hF |>.1 J hJ
  rcases hsep with hsep | hsep <;> omega

/-- An interval family contains at most one interval ending at a specified endpoint. -/
theorem intervalFamilies_existsUnique_rightEndpoint {r s : ℕ}
    {F : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hex : ∃ I ∈ F, I.2 = s) : ∃! u, (u, s) ∈ F := by
  rcases hex with ⟨I, hI, hIs⟩
  rcases I with ⟨a, b⟩
  have hb : b = s := hIs
  subst b
  have hI' : (a, s) ∈ F := by simpa using hI
  refine ⟨a, hI', ?_⟩
  intro u hu
  have hEq := intervalFamilies_rightEndpoint_unique hF hI' hu rfl rfl
  exact (congrArg Prod.fst hEq).symm

/-- Appending a final interval to a family on the preceding range preserves disjointness. -/
theorem intervalFamilies_insert_last {r u s : ℕ} (hru : r ≤ u) (hus : u < s)
    (G : Finset (ℕ × ℕ)) (hG : G ∈ intervalFamilies r (u - 1)) :
    insert (u, s) G ∈ intervalFamilies r s := by
  apply (intervalFamilies_mem_iff r s _).2
  constructor
  · intro I hI
    simp only [Finset.mem_insert] at hI
    rcases hI with hI | hI
    · subst I
      simp
      omega
    · have hIb := (intervalFamilies_mem_iff r (u - 1) G).mp hG |>.1 I hI
      rcases hIb with ⟨h1, h1u, h2, h2u, hlt⟩
      exact ⟨h1, by omega, h2, by omega, hlt⟩
  · intro I hI J hJ hne
    simp only [Finset.mem_insert] at hI hJ
    rcases hI with hI | hI
    · subst I
      rcases hJ with hJ | hJ
      · subst J
        exact (hne rfl).elim
      · have hJb := (intervalFamilies_mem_iff r (u - 1) G).mp hG |>.1 J hJ
        exact Or.inr (by omega)
    · rcases hJ with hJ | hJ
      · subst J
        have hIb := (intervalFamilies_mem_iff r (u - 1) G).mp hG |>.1 I hI
        exact Or.inl (by omega)
      · have hsep := (intervalFamilies_mem_iff r (u - 1) G).mp hG |>.2 I hI J hJ
          (by intro hEq; exact hne (by simpa [hI, hJ] using hEq))
        exact hsep

/-- Removing the unique interval ending at `s` leaves a valid family before its start. -/
theorem intervalFamilies_erase_last {r u s : ℕ}
    (F : Finset (ℕ × ℕ)) (hF : F ∈ intervalFamilies r s)
    (hpair : (u, s) ∈ F) : F.erase (u, s) ∈ intervalFamilies r (u - 1) := by
  apply (intervalFamilies_mem_iff r (u - 1) _).2
  constructor
  · intro I hI
    have hIF : I ∈ F := (Finset.mem_erase.mp hI).2
    have hne : I ≠ (u, s) := (Finset.mem_erase.mp hI).1
    have hIb := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hIF
    have hsep := (intervalFamilies_mem_iff r s F).mp hF |>.2 I hIF (u, s) hpair hne
    rcases hsep with hsep | hsep
    · rcases hIb with ⟨h1, h1s, h2, h2s, hlt⟩
      exact ⟨h1, by omega, h2, by omega, hlt⟩
    · omega
  · intro I hI J hJ hne
    have hIF : I ∈ F := (Finset.mem_erase.mp hI).2
    have hJF : J ∈ F := (Finset.mem_erase.mp hJ).2
    have hneF : I ≠ J := by
      intro hEq
      exact hne hEq
    exact ((intervalFamilies_mem_iff r s F).mp hF).2 I hIF J hJF hneF

/-- Every family with a terminal interval has a prefix family decomposition. -/
theorem intervalFamilies_decompose_last {r s : ℕ}
    (F : Finset (ℕ × ℕ)) (hF : F ∈ intervalFamilies r s)
    (hhas : ∃ I ∈ F, I.2 = s) :
    ∃ u ∈ Finset.Icc r (s - 1), ∃ G ∈ intervalFamilies r (u - 1),
      F = insert (u, s) G := by
  obtain ⟨u, huF, _⟩ := intervalFamilies_existsUnique_rightEndpoint hF hhas
  have huPair : (u, s) ∈ F := huF
  have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 (u, s) huPair
  let G := F.erase (u, s)
  have hG : G ∈ intervalFamilies r (u - 1) := by
    exact intervalFamilies_erase_last F hF huPair
  refine ⟨u, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, G, hG, ?_⟩
  dsimp [G]
  exact (Finset.insert_erase huPair).symm

/-- Families with no interval ending at `s` are precisely the families on the prefix. -/
theorem intervalFamilies_prefix_iff (r s : ℕ) (F : Finset (ℕ × ℕ)) :
    F ∈ intervalFamilies r (s - 1) ↔
      F ∈ intervalFamilies r s ∧ ¬ ∃ I ∈ F, I.2 = s := by
  rw [intervalFamilies_mem_iff, intervalFamilies_mem_iff]
  constructor
  · rintro ⟨hbound, hsep⟩
    constructor
    · constructor
      · intro I hI
        rcases hbound I hI with ⟨h1, h1s, h2, h2s, hlt⟩
        exact ⟨h1, by omega, h2, by omega, hlt⟩
      · exact hsep
    · rintro ⟨I, hI, hIs⟩
      have hI' := hbound I hI
      omega
  · rintro ⟨⟨hbound, hsep⟩, hno⟩
    constructor
    · intro I hI
      rcases hbound I hI with ⟨h1, h1s, h2, h2s, hlt⟩
      have hneq : I.2 ≠ s := by
        intro hEq
        exact hno ⟨I, hI, hEq⟩
      exact ⟨h1, by omega, h2, by omega, hlt⟩
    · exact hsep

/-- The normalized activity attached to one closed discrepancy interval. -/
noncomputable def blockIntervalWeight (β : ℝ) (t : ℕ → ℕ) (ω : Disorder)
    (I : ℕ × ℕ) : ℝ :=
  closedDiscrepancy β t I.1 I.2 ω /
    ∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω

/-- The product weight of a finite family of closed discrepancy intervals. -/
noncomputable def intervalFamilyWeight (β : ℝ) (t : ℕ → ℕ) (ω : Disorder)
    (F : Finset (ℕ × ℕ)) : ℝ :=
  ∏ I ∈ F, blockIntervalWeight β t ω I

/-- The family weight factors when a final interval is inserted. -/
theorem intervalFamilyWeight_insert_last (β : ℝ) (t : ℕ → ℕ) (ω : Disorder)
    {r u s : ℕ} (hu : u < s) (G : Finset (ℕ × ℕ))
    (hG : G ∈ intervalFamilies r (u - 1)) :
    intervalFamilyWeight β t ω (insert (u, s) G) =
      blockIntervalWeight β t ω (u, s) * intervalFamilyWeight β t ω G := by
  have hnot : (u, s) ∉ G := by
    intro hmem
    have hbound := (intervalFamilies_mem_iff r (u - 1) G).mp hG |>.1 (u, s) hmem
    omega
  unfold intervalFamilyWeight
  rw [Finset.prod_insert hnot]

/-- Reindex all families with an interval ending at `s` by that interval and its prefix. -/
theorem intervalFamilies_weight_last_sum (β : ℝ) (t : ℕ → ℕ) (r s : ℕ)
    (hr : 1 ≤ r) (hrs : r < s) (ω : Disorder) :
    (∑ F ∈ (intervalFamilies r s).filter (fun F => ∃ I ∈ F, I.2 = s),
      intervalFamilyWeight β t ω F) =
      ∑ u ∈ Finset.Icc r (s - 1), ∑ G ∈ intervalFamilies r (u - 1),
        intervalFamilyWeight β t ω G * blockIntervalWeight β t ω (u, s) := by
  symm
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => insert (p.1, s) p.2)
  · intro p hp
    rcases Finset.mem_sigma.mp hp with ⟨hu, hG⟩
    have hu' := Finset.mem_Icc.mp hu
    have hvalid : insert (p.1, s) p.2 ∈ intervalFamilies r s := by
      exact intervalFamilies_insert_last hu'.1 (by omega) p.2 hG
    apply Finset.mem_filter.mpr
    constructor
    · exact hvalid
    · exact ⟨(p.1, s), Finset.mem_insert_self .., rfl⟩
  · intro p hp q hq hpq
    rcases Finset.mem_sigma.mp hp with ⟨hpu, hpg⟩
    rcases Finset.mem_sigma.mp hq with ⟨hqu, hqg⟩
    have hpu' := Finset.mem_Icc.mp hpu
    have hpf : insert (p.1, s) p.2 ∈ intervalFamilies r s := by
      exact intervalFamilies_insert_last (r := r) (u := p.1) (s := s)
        hpu'.1 (by omega) p.2 hpg
    have hpPair : (p.1, s) ∈ insert (p.1, s) p.2 := Finset.mem_insert_self ..
    have hqPair : (q.1, s) ∈ insert (q.1, s) q.2 := Finset.mem_insert_self ..
    have hqPair' : (q.1, s) ∈ insert (p.1, s) p.2 := by simp [hpq]
    have huEq := intervalFamilies_rightEndpoint_unique hpf hpPair hqPair' rfl rfl
    have hfirst : p.1 = q.1 := congrArg Prod.fst huEq
    cases p with
    | mk u G =>
      cases q with
      | mk v H =>
        dsimp at hfirst hpq ⊢
        subst v
        have hnotG : (u, s) ∉ G := by
          intro hmem
          have hbound := (intervalFamilies_mem_iff r (u - 1) G).mp hpg |>.1 (u, s) hmem
          have hrange := Finset.mem_Icc.mp hpu
          omega
        have hnotH : (u, s) ∉ H := by
          intro hmem
          have hbound := (intervalFamilies_mem_iff r (u - 1) H).mp hqg |>.1 (u, s) hmem
          have hrange := Finset.mem_Icc.mp hqu
          omega
        have hGH : G = H := by
          apply Finset.ext
          intro I
          have hmemEq := congrArg (fun K : Finset (ℕ × ℕ) => I ∈ K) hpq
          by_cases hI : I = (u, s)
          · subst I
            exact iff_of_false hnotG hnotH
          · simpa [Finset.mem_insert, hI] using hmemEq
        subst H
        rfl
  · intro F hF
    have hF' := (Finset.mem_filter.mp hF).1
    have hhas := (Finset.mem_filter.mp hF).2
    obtain ⟨u, hu, G, hG, hdecomp⟩ :=
      intervalFamilies_decompose_last F hF' hhas
    refine ⟨⟨u, G⟩, Finset.mem_sigma.mpr ⟨hu, hG⟩, ?_⟩
    exact hdecomp.symm
  · intro p hp
    have hu := Finset.mem_Icc.mp (Finset.mem_sigma.mp hp).1
    rw [intervalFamilyWeight_insert_last β t ω (by omega) p.2 (Finset.mem_sigma.mp hp).2]
    ring

/-- The family partition function satisfies the last-interval recurrence. -/
theorem intervalFamilies_weight_recurrence (β : ℝ) (t : ℕ → ℕ) (r s : ℕ)
    (hr : 1 ≤ r) (hrs : r < s) (ω : Disorder) :
    (∑ F ∈ intervalFamilies r s, intervalFamilyWeight β t ω F) =
      (∑ F ∈ intervalFamilies r (s - 1), intervalFamilyWeight β t ω F) +
        ∑ u ∈ Finset.Icc r (s - 1), ∑ G ∈ intervalFamilies r (u - 1),
          intervalFamilyWeight β t ω G * blockIntervalWeight β t ω (u, s) := by
  let hasLast : Finset (ℕ × ℕ) → Prop := fun F => ∃ I ∈ F, I.2 = s
  have hprefix :
      (intervalFamilies r s).filter (fun F => ¬ hasLast F) =
        intervalFamilies r (s - 1) := by
    ext F
    simp only [Finset.mem_filter]
    exact (intervalFamilies_prefix_iff r s F).symm
  calc
    _ = (∑ F ∈ (intervalFamilies r s).filter hasLast, intervalFamilyWeight β t ω F) +
          ∑ F ∈ (intervalFamilies r s).filter (fun F => ¬ hasLast F),
            intervalFamilyWeight β t ω F := by
      rw [← Finset.sum_filter_add_sum_filter_not (intervalFamilies r s) hasLast
        (intervalFamilyWeight β t ω)]
    _ = (∑ F ∈ intervalFamilies r (s - 1), intervalFamilyWeight β t ω F) +
          ∑ u ∈ Finset.Icc r (s - 1), ∑ G ∈ intervalFamilies r (u - 1),
            intervalFamilyWeight β t ω G * blockIntervalWeight β t ω (u, s) := by
      rw [hprefix, intervalFamilies_weight_last_sum β t r s hr hrs ω]
      ring

/-- There are no nonempty interval families on the empty block range. -/
theorem intervalFamilies_empty (r : ℕ) (hr : 1 ≤ r) :
    intervalFamilies r (r - 1) = {∅} := by
  unfold intervalFamilies
  rw [Finset.Icc_eq_empty_of_lt (by omega)]
  simp

/-- The block ratio obeys the last-interval recurrence. -/
theorem blockRatio_recurrence (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (r s : ℕ) (hr : 1 ≤ r) (hrs : r < s) (ω : Disorder) :
    blockRatio β t r s ω = blockRatio β t r (s - 1) ω +
      ∑ u ∈ Finset.Icc r (s - 1),
        blockRatio β t r (u - 1) ω *
          (closedDiscrepancy β t u s ω /
            ∏ i ∈ Finset.Icc u s, blockMass β t i ω) := by
  have hrs' : r ≤ s - 1 := by omega
  have hidx : s - 1 + 1 = s := by omega
  let P := ∏ i ∈ Finset.Icc r s, blockMass β t i ω
  let Pprev := ∏ i ∈ Finset.Icc r (s - 1), blockMass β t i ω
  have hsplitLast : Pprev * blockMass β t s ω = P := by
    have h := blockMass_product_split β t r s s hr (by omega) le_rfl ω
    simpa [P, Pprev, Finset.Icc_self, Finset.prod_singleton] using h
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i _ => blockMass_pos β t i ω
  have hPprevpos : 0 < Pprev := by
    dsimp [Pprev]
    exact Finset.prod_pos fun i _ => blockMass_pos β t i ω
  have hscalar := smoothedP2Plane_blockMass_recurrence β t ht r s hrs ω
  have hscalar' :
      smoothedP2Plane β (t (r - 1)) (t s) 0 ω =
        smoothedP2Plane β (t (r - 1)) (t (s - 1)) 0 ω * blockMass β t s ω +
          ∑ u ∈ Finset.Icc r (s - 1),
            smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
              closedDiscrepancy β t u s ω := by
    simpa only [hidx] using hscalar
  have hfirst :
      (smoothedP2Plane β (t (r - 1)) (t (s - 1)) 0 ω * blockMass β t s ω) / P =
        smoothedP2Plane β (t (r - 1)) (t (s - 1)) 0 ω / Pprev := by
    rw [← hsplitLast]
    field_simp [hPprevpos.ne', (blockMass_pos β t s ω).ne']
  have hterm (u : ℕ) (hu : u ∈ Finset.Icc r (s - 1)) :
      (smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
        closedDiscrepancy β t u s ω) / P =
        (smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω /
          ∏ i ∈ Finset.Icc r (u - 1), blockMass β t i ω) *
          (closedDiscrepancy β t u s ω /
            ∏ i ∈ Finset.Icc u s, blockMass β t i ω) := by
    have hu' := Finset.mem_Icc.mp hu
    have hsplit := blockMass_product_split β t r u s hr hu'.1 (by omega) ω
    have hpre : 0 < ∏ i ∈ Finset.Icc r (u - 1), blockMass β t i ω :=
      Finset.prod_pos fun i _ => blockMass_pos β t i ω
    have htail : 0 < ∏ i ∈ Finset.Icc u s, blockMass β t i ω :=
      Finset.prod_pos fun i _ => blockMass_pos β t i ω
    have hsplit' :
        (∏ i ∈ Finset.Icc r (u - 1), blockMass β t i ω) *
            ∏ i ∈ Finset.Icc u s, blockMass β t i ω = P := by
      simpa [P] using hsplit
    rw [← hsplit']
    field_simp [hpre.ne', htail.ne']
  unfold blockRatio
  rw [hscalar', add_div, Finset.sum_div]
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact hterm u hu

/-- The normalized block ratio is the interval-family partition function. -/
theorem blockRatio_eq_intervalFamilyWeight_sum (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (ω : Disorder) :
    blockRatio β t r s ω =
      ∑ F ∈ intervalFamilies r s, intervalFamilyWeight β t ω F := by
  have hmain : ∀ s r, 1 ≤ r → r ≤ s →
      blockRatio β t r s ω =
        ∑ F ∈ intervalFamilies r s, intervalFamilyWeight β t ω F := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro r hr hrs
      by_cases hself : r = s
      · subst s
        simpa [intervalFamilyWeight, blockIntervalWeight] using
          blockRatio_eq_sum_intervalFamilies_self β t r ω
      · have hrs' : r < s := by omega
        have hratio := blockRatio_recurrence β t ht r s hr hrs' ω
        have hfamilies := intervalFamilies_weight_recurrence β t r s hr hrs' ω
        have hprev : blockRatio β t r (s - 1) ω =
            ∑ F ∈ intervalFamilies r (s - 1), intervalFamilyWeight β t ω F := by
          apply ih (s - 1) (by omega) r hr
          omega
        have hprefix (u : ℕ) (hu : u ∈ Finset.Icc r (s - 1)) :
            blockRatio β t r (u - 1) ω =
              ∑ G ∈ intervalFamilies r (u - 1), intervalFamilyWeight β t ω G := by
          by_cases hur : u = r
          · subst u
            rw [blockRatio_empty β t r hr ω, intervalFamilies_empty r hr]
            simp [intervalFamilyWeight, blockIntervalWeight]
          · have hru : r ≤ u - 1 := by
              have hu' := Finset.mem_Icc.mp hu
              omega
            apply ih (u - 1) (by have hu' := Finset.mem_Icc.mp hu; omega) r hr hru
        rw [hratio, hfamilies, hprev]
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        rw [hprefix u hu, Finset.sum_mul]
        simp only [blockIntervalWeight]
  exact hmain s r hr hrs

/-- The normalized block ratio is the finite sum over disjoint closed discrepancy intervals. -/
theorem blockRatio_eq_sum_intervalFamilies (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (ω : Disorder) :
    blockRatio β t r s ω = ∑ F ∈ intervalFamilies r s, ∏ I ∈ F,
      closedDiscrepancy β t I.1 I.2 ω /
        ∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω := by
  simpa [intervalFamilyWeight, blockIntervalWeight] using
    blockRatio_eq_intervalFamilyWeight_sum β t ht r s hr hrs ω

/-- The normalized endpoint distribution has the exact open discrepancy expansion. -/
theorem smoothedEndpointDist_block_expansion (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s)
    (ω : Disorder) (y : Site) :
    smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y =
      srwKernel (t s) y + (blockRatio β t r s ω)⁻¹ *
        ∑ u ∈ Finset.Icc r s,
          blockRatio β t r (u - 1) ω * openCorrector β t u s ω y := by
  let M := smoothedP2Plane β (t (r - 1)) (t s) 0 ω
  let P := ∏ i ∈ Finset.Icc r s, blockMass β t i ω
  have hM : 0 < M := Polymer.smoothedP2Plane_pos β (t (r - 1)) (t s) 0 ω
  have hP : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i _ => blockMass_pos β t i ω
  have hU : smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y =
      blockEndpointNumerator β t r s ω y / M := by
    unfold smoothedEndpointDist blockEndpointNumerator M
    simp only [sub_zero]
  have hprofile := blockEndpointNumerator_intervalExpansion β t ht r s hrs ω y
  have hnorm : blockEndpointNumerator β t r s ω y / M =
      srwKernel (t s) y +
        (∑ u ∈ Finset.Icc r s,
          smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
            openCorrectorNumerator β t u s ω y) / M := by
    rw [hprofile]
    field_simp [ne_of_gt hM]
    ring
  have hterm (u : ℕ) (hu : u ∈ Finset.Icc r s) :
      (blockRatio β t r s ω)⁻¹ *
          (blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) =
        (smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
          openCorrectorNumerator β t u s ω y) / M := by
    have hu' := Finset.mem_Icc.mp hu
    have hpre : 0 < ∏ i ∈ Finset.Icc r (u - 1), blockMass β t i ω :=
      Finset.prod_pos fun i _ => blockMass_pos β t i ω
    have htail : 0 < ∏ i ∈ Finset.Icc u s, blockMass β t i ω :=
      Finset.prod_pos fun i _ => blockMass_pos β t i ω
    have hsplit := blockMass_product_split β t r u s hr hu'.1 hu'.2 ω
    have hRinv : (blockRatio β t r s ω)⁻¹ = P / M := by
      unfold blockRatio
      dsimp [P, M]
      field_simp [ne_of_gt hM, ne_of_gt hP]
    rw [hRinv]
    unfold blockRatio openCorrector
    dsimp [P, M]
    rw [← hsplit]
    field_simp [ne_of_gt hM, hpre.ne', htail.ne']
  have hsum :
      (blockRatio β t r s ω)⁻¹ *
          ∑ u ∈ Finset.Icc r s,
            blockRatio β t r (u - 1) ω * openCorrector β t u s ω y =
        (∑ u ∈ Finset.Icc r s,
          smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
            openCorrectorNumerator β t u s ω y) / M := by
    calc
      _ = ∑ u ∈ Finset.Icc r s,
            (blockRatio β t r s ω)⁻¹ *
              (blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) := by
        rw [Finset.mul_sum]
      _ = ∑ u ∈ Finset.Icc r s,
            (smoothedP2Plane β (t (r - 1)) (t (u - 1)) 0 ω *
              openCorrectorNumerator β t u s ω y) / M := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hterm u hu]
      _ = _ := by rw [Finset.sum_div]
  rw [hU, hnorm, ← hsum]

end Critical2DKPZ.Blocks

end
