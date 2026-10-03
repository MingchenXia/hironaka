/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.NonmonomialStepAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Re-basing Step 1a's restricted marked ideal across steps that are empty near the point

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 1a of Proposition `pr:resol` and the lemma on the
commutativity of the resolution procedure with étale morphisms (blow-ups whose centres miss the image pull back to
isomorphisms; the restrictions `J̄_{|H^s_α}` commute with them).

In Step 1a the value at a point `x` of the cosupport involves the lower-dimensional invariant of the restricted marked
ideal `𝓢(𝔪, y) = (Y, N ∩ H_{S(y)}, E_{S(y)}, 𝓒_N(𝔞), μ_𝓒)` (`InvDomainMemberRestriction.memberRestrict` at
`membersThrough E E₀ y`), formed at a stage depending on `x` and restricted to a neighbourhood `W`, along the rest of the
segment.  Nearby points with different start stages are compared by re-basing (property (4') of
`ResolutionInvariantExt.ResolutionInvariant`): between the two stages the centres miss `W` (`RestrictEmptyTower`), and the
marked ideal formed at the earlier stage, transformed along those steps, must be the one formed at the later stage.  This
module proves that, up to restricted equivalence, with the domain, and the resulting identity of values.

## Main results

* `eq_of_eventually_mem_iff`: **distinct members of a simple normal crossings divisor through a point differ near it** (the
  statement of the earlier `SimultaneousNormalCrossings.eq_of_eventually_mem_iff`, without `IsComplexManifold`);
* `memberInter_membersThrough_eq`, `memberRestrict_membersThrough_N`, `memberRestrict_membersThrough_E`,
  `filter_map_members`: `𝓢(𝔪, y)` by value (`H_{S(y)}` and `E_{S(y)}` as conditions on members);
* `restrictEquiv_memberRestrict_geoTransform_empty`: across a step with empty centre, `𝓢(𝔪', z) ≃ 𝓢(𝔪, π z)'` ((K3)
  `ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransform_empty` with the members of `S` deleted);
* `mem_of_preimage_val_mem_map`, `pullback_val_memberRestrict_membersThrough`: `𝓢` commutes with restriction to open sets;
* `restrictEquiv_memberRestrict_geoTransformAlong_of_isEmptyTower`: along a tower with only empty centres;
* **`restrictEquiv_memberRestrict_rebase`**: for `T` a multiple test blow-up of `𝔫` whose centres miss the open `W` and `p`
  over `W`, `𝓢(𝔫_T, p)|_{T⁻¹W} ≃ (𝓢(𝔫, T p)|_W)_{T|_W}`;
* `restrictEquiv_symm`, `isInvDomain_of_restrictEquiv`, `isInvDomain_geoTransformAlong_of_isEmptyTower`,
  `isCanonical_of_restrictEquiv`, **`inv_rebase`**: for a resolution invariant `R`, after an empty prefix `T₀` and for `𝔫`
  restricted-equivalent to `𝔪_{T₀}`, canonical segments and values re-base (`emptyPrefix` and `representative`);
* **`memberRestrict_rebase`**: the two combined -- if `𝓢(𝔫, T p)|_W` lies in the domain and `T|_W T₁` is a canonical segment
  of it, then `𝓢(𝔫_T, p)|_{T⁻¹W}` lies in the domain, `T₁` is a canonical segment of it, its transforms along `T₁` lie in the
  domain and the values agree;
* (The restricted equivalence of the companion ideals formed at two stages is not proved here.)
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.InvDomainRebase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.BoundaryCount Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealBiholomorphism

noncomputable section

variable {n : ℕ}

/-! ### Distinct members through a point differ near it -/

section SNC

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Distinct members of a simple normal crossings divisor through a point differ near it**: if `x` lies on the members
`E_i` and `E_j` and these agree near `x`, then `i = j` (in coordinates at `x` they are the hyperplanes `{w_a = 0}` and
`{w_b = 0}` with `a ≠ b` for `i ≠ j`; a point with `w_a = 0`, `w_b ≠ 0` close to `x` separates them).  The same statement
as `SimultaneousNormalCrossings.eq_of_eventually_mem_iff` (`bcalc:snc-simultaneous`), which needs `IsComplexManifold`;
found after this proof was written, and kept. -/
theorem eq_of_eventually_mem_iff {E : List (Set M)} (hE : IsSNCDivisor n E) {x : M} {i j : Fin E.length}
    (hi : x ∈ E.get i) (hj : x ∈ E.get j) (h : ∀ᶠ w in 𝓝 x, w ∈ E.get i ↔ w ∈ E.get j) : i = j := by
  by_contra hij
  obtain ⟨S, ⟨Φ, hsrc, h0, hcoord⟩, hcard, hinj⟩ := hE.2 x
  have hSij : S i ≠ S j := fun hS => hij (hinj hi hj hS)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard i hi)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hcard j hj)
  have hab : a ≠ b := fun hab => hSij (by rw [ha, hb, hab])
  have hxs : (complexChartAt (n := n) x).val x ∈ Φ.source := Φ.center_mem_source
  have h0T : (0 : ComplexModel n) ∈ Φ.target := h0 ▸ Φ.mapsTo_toFun hxs
  have hinv0 : Φ.invFun 0 = (complexChartAt (n := n) x).val x := by
    rw [← h0]; exact Φ.left_inv _ hxs
  set v : ℂ → ComplexModel n := fun t => t • EuclideanSpace.single b (1 : ℂ) with hvdef
  have hvc : Continuous v := continuous_id.smul continuous_const
  have hv0 : v 0 = 0 := by simp [hvdef]
  have hvlim : Tendsto v (𝓝[≠] 0) (𝓝 0) := by
    rw [← hv0]
    exact hvc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcont : ContinuousAt (fun w => (complexChartAt (n := n) x).val.symm (Φ.invFun w)) 0 := by
    refine ContinuousAt.comp (f := Φ.invFun) (g := (complexChartAt (n := n) x).val.symm) ?_ ?_
    · rw [hinv0]
      exact (complexChartAt (n := n) x).val.continuousAt_symm
        ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source (n := n) x))
    · exact (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0T)).continuousAt
  have hex : (complexChartAt (n := n) x).val.symm (Φ.invFun 0) = x := by
    rw [hinv0]
    exact (complexChartAt (n := n) x).val.left_inv (mem_complexChartAt_source (n := n) x)
  have hlim : Tendsto (fun t => (complexChartAt (n := n) x).val.symm (Φ.invFun (v t))) (𝓝[≠] 0) (𝓝 x) := by
    have := hcont.tendsto.comp hvlim
    rwa [hex] at this
  obtain ⟨t, ⟨hiff, hvT⟩, ht⟩ := ((hlim.eventually h).and (hvlim.eventually (Φ.isOpen_target.mem_nhds h0T))).and
    self_mem_nhdsWithin |>.exists
  have hΦs : Φ.invFun (v t) ∈ Φ.source := Φ.mapsTo_invFun hvT
  have het : Φ.invFun (v t) ∈ (complexChartAt (n := n) x).val.target := hsrc hΦs
  have hws : (complexChartAt (n := n) x).val.symm (Φ.invFun (v t)) ∈ (complexChartAt (n := n) x).val.source :=
    (complexChartAt (n := n) x).val.map_target het
  have hew : (complexChartAt (n := n) x).val ((complexChartAt (n := n) x).val.symm (Φ.invFun (v t))) =
      Φ.invFun (v t) := (complexChartAt (n := n) x).val.right_inv het
  have hΦw : Φ.toFun ((complexChartAt (n := n) x).val ((complexChartAt (n := n) x).val.symm (Φ.invFun (v t)))) =
      v t := by rw [hew]; exact Φ.right_inv _ hvT
  have hwi : (complexChartAt (n := n) x).val.symm (Φ.invFun (v t)) ∈ E.get i := by
    refine (hcoord i hi hws (by rw [hew]; exact hΦs)).mpr ?_
    rw [hΦw, ha]
    intro c hc
    rw [Finset.mem_singleton] at hc
    subst hc
    simp [hvdef, hab]
  have hwj : (complexChartAt (n := n) x).val.symm (Φ.invFun (v t)) ∉ E.get j := by
    intro hw
    have := (hcoord j hj hws (by rw [hew]; exact hΦs)).mp hw
    rw [hΦw, hb] at this
    have h1 := this b (Finset.mem_singleton_self b)
    simp [hvdef] at h1
    exact ht h1
  exact hwj (hiff.mp hwi)

end SNC

/-! ### Step 1a's restricted marked ideal by value -/

section ByValue

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- Filtering the indices of a list by a property of the entries is filtering the list. -/
theorem map_get_filter_finRange {α : Type*} (L : List α) (p : α → Bool) :
    ((List.finRange L.length).filter (fun i => p (L.get i))).map L.get = L.filter p := by
  conv_rhs => rw [← List.map_get_finRange L]
  rw [List.filter_map]
  rfl

/-- **`H_{S(y)}` by value**: the intersection of the members of `E` that belong to `E₀` and pass through `y`. -/
theorem memberInter_membersThrough_eq (E E₀ : List (Set X)) (y : X) :
    memberInter E (membersThrough E E₀ y) = {w | ∀ H ∈ E, H ∈ E₀ → y ∈ H → w ∈ H} := by
  ext w
  refine ⟨fun hw H hH hH₀ hyH => ?_, fun hw i hi => ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact hw i (mem_membersThrough.mpr ⟨hH₀, hyH⟩)
  · obtain ⟨hi₀, hyi⟩ := mem_membersThrough.mp hi
    exact hw _ (List.get_mem E i) hi₀ hyi

open Classical in
/-- **`E_{S(y)}` by value**: Step 1a's restricted marked ideal keeps exactly the members of `E` which are not members of
`E₀` through `y`, in their order. -/
theorem memberRestrict_membersThrough_E (𝔪 : MarkedIdeal n X) (E₀ : List (Set X)) (y : X) :
    (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ y)).E = 𝔪.E.filter (fun H => decide ¬(H ∈ E₀ ∧ y ∈ H)) := by
  rw [memberRestrict_E]
  refine Eq.trans ?_ (map_get_filter_finRange 𝔪.E _)
  congr 1
  refine List.filter_congr fun i _ => ?_
  rw [decide_eq_decide, mem_membersThrough]

/-- **The `N` of Step 1a's restricted marked ideal by value.** -/
theorem memberRestrict_membersThrough_N (𝔪 : MarkedIdeal n X) (E₀ : List (Set X)) (y : X) :
    (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ y)).N = 𝔪.N ∩ {w | ∀ H ∈ 𝔪.E, H ∈ E₀ → y ∈ H → w ∈ H} := by
  rw [memberRestrict_N, memberInter_membersThrough_eq]

open Classical in
/-- **Filtering commutes with a map of members** which is injective on the members through the point: for `f` a map of
sets (a strict transform, a trace on an open set), the members of `L.map f` which are not images of members of `E₀`
through `y'` are the images of the members of `L` which are not members of `E₀` through `y`, provided `y' ∈ f H` iff
`y ∈ H` and a member through `y` whose image is the image of a member of `E₀` belongs to `E₀`. -/
theorem filter_map_members {Y Z : Type*} {L E₀ : List (Set Y)} {f : Set Y → Set Z} {y : Y} {y' : Z}
    (hy : ∀ H ∈ L, y' ∈ f H ↔ y ∈ H) (hinj : ∀ H ∈ L, y ∈ H → f H ∈ E₀.map f → H ∈ E₀) :
    (L.map f).filter (fun H' => decide ¬(H' ∈ E₀.map f ∧ y' ∈ H')) =
      (L.filter (fun H => decide ¬(H ∈ E₀ ∧ y ∈ H))).map f := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun H hH => ?_
  rw [Function.comp_apply, decide_eq_decide, hy H hH]
  refine not_congr ⟨fun h => ⟨hinj H hH h.2 h.1, h.2⟩, fun h => ⟨List.mem_map_of_mem h.1, h.2⟩⟩

end ByValue

/-! ### Across a step with empty centre -/

section EmptyStep

open BlowupStrictSubmanifold ContactCanonicalAlong MarkedIdealOperationsAlong.MarkedIdeal

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → Y}

/-- A blowup along the empty set is surjective (its section over the complement of the centre). -/
theorem surjective_of_isBlowupAlong_empty (hπ : IsBlowupAlong n (∅ : Set Y) π) : Function.Surjective π := by
  obtain ⟨s, -, hsπ, -⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  exact fun y => ⟨s ⟨y, notMem_empty y⟩, congrFun hsπ ⟨y, notMem_empty y⟩⟩

open Classical in
/-- **Step 1a's restricted marked ideal across a step with empty centre** (the (K3) form for `memberRestrict`, from
`ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransform_empty`): for the blowup `π` along `∅`, a list `E₀`
of members of `E` and a point `z`, the restricted marked ideal of the transform at `z` (members of the strict
transforms of `E₀` through `z` deleted) is restricted-equivalent to the transform of the restricted marked ideal at
`π z`. (`N` a closed submanifold, coherent ideal, `d ≥ 1`, closed members.) -/
theorem restrictEquiv_memberRestrict_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hE : ∀ H ∈ 𝔪.E, IsClosed H) {E₀ : List (Set Y)}
    (hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E) (hπ : IsBlowupAlong n (∅ : Set Y) π) (z : Z) :
    RestrictEquiv
      (memberRestrict (𝔪.geoTransform ∅ π) (membersThrough (𝔪.geoTransform ∅ π).E (E₀.map (geoStrictTransform π ∅)) z))
      ((memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (π z))).geoTransform ∅ π) := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  set A := 𝔪.N ∩ memberInter 𝔪.E (membersThrough 𝔪.E E₀ (π z)) with hAdef
  have hA : IsClosed A := hN.1.inter (isClosed_memberInter hE _)
  have hK := restrictEquiv_restrictedCoeff_geoTransform_empty 𝔪 hN h𝔞 hd hπ (A := A) inter_subset_left
  have hg : ∀ H ∈ 𝔪.E, geoStrictTransform π ∅ H = π ⁻¹' H := fun H hH => geoStrictTransform_empty hπc (hE H hH)
  have hinj : Function.Injective (Set.preimage π) :=
    Set.preimage_injective.mpr (surjective_of_isBlowupAlong_empty hπ)
  have hmem : ∀ H ∈ 𝔪.E, geoStrictTransform π ∅ H ∈ E₀.map (geoStrictTransform π ∅) → H ∈ E₀ := by
    intro H hH h
    obtain ⟨H₀, hH₀, hgH⟩ := List.mem_map.mp h
    rw [hg H₀ (hE₀ H₀ hH₀), hg H hH] at hgH
    exact hinj hgH ▸ hH₀
  have hNeq : (memberRestrict (𝔪.geoTransform ∅ π)
      (membersThrough (𝔪.geoTransform ∅ π).E (E₀.map (geoStrictTransform π ∅)) z)).N = geoStrictTransform π ∅ A := by
    rw [memberRestrict_membersThrough_N, geoStrictTransform_empty hπc hA, hAdef, memberInter_membersThrough_eq,
      geoTransform_N, geoStrictTransform_empty hπc hN.1, geoTransform_E]
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, List.mem_append, List.mem_map, List.mem_singleton]
    refine and_congr_right fun _ => ⟨fun hw H hH hH₀ hzH => ?_, fun hw H' hH' hH'₀ hzH' => ?_⟩
    · have := hw (geoStrictTransform π ∅ H) (Or.inl ⟨H, hH, rfl⟩) ⟨H, hH₀, rfl⟩ (by rw [hg H hH]; exact hzH)
      rwa [hg H hH] at this
    · rcases hH' with ⟨H, hH, rfl⟩ | rfl
      · have hH₀ := hmem H hH (List.mem_map.mpr hH'₀)
        rw [hg H hH] at hzH' ⊢
        exact hw H hH hH₀ hzH'
      · exact absurd hzH' (by simp)
  have hEeq : (memberRestrict (𝔪.geoTransform ∅ π)
      (membersThrough (𝔪.geoTransform ∅ π).E (E₀.map (geoStrictTransform π ∅)) z)).E =
      ((memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (π z))).geoTransform ∅ π).E := by
    rw [memberRestrict_membersThrough_E, geoTransform_E, geoTransform_E, memberRestrict_membersThrough_E,
      List.filter_append, filter_map_members (fun H hH => by rw [hg H hH]; exact Iff.rfl)
        (fun H hH _ h => hmem H hH h)]
    congr 1
    simp
  exact ⟨hNeq, hEeq, rfl, by rw [hNeq]; exact hK.le, by rw [hNeq]; exact hK.ge⟩

end EmptyStep

/-! ### Restriction to open sets -/

section Open

open MarkedIdealRestrictOpen

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A member through a point of an open set whose trace is the trace of a member of `E₀` belongs to `E₀`** (`E` simple
normal crossings, `E₀` a list of members): the two members agree near the point, so they are the same member
(`eq_of_eventually_mem_iff`). -/
theorem mem_of_preimage_val_mem_map {E E₀ : List (Set M)} (hE : IsSNCDivisor n E) (hE₀ : ∀ H ∈ E₀, H ∈ E)
    (U : Opens M) (p : U) {H : Set M} (hH : H ∈ E) (hpH : (p : M) ∈ H)
    (h : (Subtype.val : U → M) ⁻¹' H ∈ E₀.map ((Subtype.val : U → M) ⁻¹' ·)) : H ∈ E₀ := by
  obtain ⟨H₀, hH₀, hpre⟩ := List.mem_map.mp h
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (hE₀ H₀ hH₀)
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hH
  have hU : ∀ w ∈ U, (w ∈ E.get i ↔ w ∈ E.get j) := fun w hw => by
    have := congrArg (fun s : Set U => (⟨w, hw⟩ : U) ∈ s) hpre
    simpa using this
  have hpi : (p : M) ∈ E.get i := (hU p p.2).mpr hpH
  have hij : i = j := eq_of_eventually_mem_iff hE hpi hpH
    (Filter.mem_of_superset (U.isOpen.mem_nhds p.2) fun w hw => hU w hw)
  rw [← hij]
  exact hH₀

/-- **Step 1a's restricted marked ideal commutes with restriction to open sets**: for `𝔪` well formed with `d ≥ 1`,
`E₀` a list of members and `p` a point of the open `U`, the restriction to `U` of the restricted marked ideal at `p` is
the restricted marked ideal at `p` of the restriction, with the traces of the members of `E₀`. -/
theorem pullback_val_memberRestrict_membersThrough {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed) (hd : 1 ≤ 𝔪.d)
    {E₀ : List (Set M)} (hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E) (U : Opens M) (p : U) :
    MarkedIdeal.pullback (Subtype.val : U → M) (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ p)) =
      memberRestrict (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪)
        (membersThrough (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪).E
          (E₀.map ((Subtype.val : U → M) ⁻¹' ·)) p) := by
  have hcoeff := HomogenizedIdealAlong.pullback_val_coeffMarkedAlong U 𝔪 h𝔪.isCoherent h𝔪.isClosedSubmanifold_N hd
  have hmem : ∀ H ∈ 𝔪.E, (p : M) ∈ H →
      (Subtype.val : U → M) ⁻¹' H ∈ E₀.map ((Subtype.val : U → M) ⁻¹' ·) → H ∈ E₀ :=
    fun H hH hpH h => mem_of_preimage_val_mem_map h𝔪.isSNCDivisor hE₀ U p hH hpH h
  have hI := congrArg MarkedIdeal.ideal hcoeff
  have hD := congrArg MarkedIdeal.d hcoeff
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hI hD
  · show (Subtype.val : U → M) ⁻¹' (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ p)).N = _
    rw [memberRestrict_membersThrough_N, memberRestrict_membersThrough_N]
    ext q
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun hw H' hH' hH'₀ hpH' => ?_, fun hw H hH hH₀ hpH => ?_⟩
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      exact hw H hH (hmem H hH hpH' hH'₀) hpH'
    · exact hw _ (List.mem_map_of_mem hH) (List.mem_map_of_mem hH₀) hpH
  · show (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ p)).E.map ((Subtype.val : U → M) ⁻¹' ·) = _
    rw [memberRestrict_membersThrough_E, memberRestrict_membersThrough_E]
    exact (filter_map_members (f := ((Subtype.val : U → M) ⁻¹' ·)) (y := (p : M)) (y' := p)
      (fun H _ => Iff.rfl) hmem).symm

end Open

/-! ### Along towers with only empty centres, and re-basing -/

section Tower

open BlowupStrictSubmanifold ContactCanonicalAlong MarkedIdealOperationsAlong.MarkedIdeal BlowupTowers BlowupTowerTransforms MarkedIdealRestrictOpen HomogenizedGlueingTower ResolutionInvariantExt RestrictEmptyTower

variable {X : CMfd.{u} n}

/-- **Step 1a's restricted marked ideal along a tower with only empty centres** (`T` a sequence of isomorphisms):
for `𝔫` well formed with `d ≥ 1` and `E₀` a list of members, the restricted marked ideal of `𝔫_T` at a point `z` (the
strict transforms of the members of `E₀` through `z` deleted) is restricted-equivalent to the transform along `T` of the
restricted marked ideal of `𝔫` at the image of `z`. -/
theorem restrictEquiv_memberRestrict_geoTransformAlong_of_isEmptyTower (hn : 0 < n) {𝔫 : MarkedIdeal n X}
    (h𝔫 : 𝔫.IsWellFormed) (hd : 1 ≤ 𝔫.d) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, H ∈ 𝔫.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → ∀ z : Y,
      RestrictEquiv
        (memberRestrict (geoTransformAlong 𝔫 T) (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) z))
        (geoTransformAlong (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (T.proj z))) T)
  | _, .refl, _, z => by
      rw [show E₀.map (strictAlong (BlowupTower.refl : BlowupTower X X)) = E₀ from List.map_id'' (fun _ => rfl) E₀]
      exact RestrictEquiv.refl (isWellFormed_memberRestrict hn h𝔫 _).isCoherent
  | _, .step T C π hπ, hT, z => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      subst hC
      have hTt : IsGeoTestTower 𝔫 T := isGeoTestTower_of_isEmptyTower 𝔫 T hT
      have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔫 T hTt
      have hE₀T := mem_E_geoTransformAlong_of_mem_map 𝔫 hE₀ T
      have hK := restrictEquiv_memberRestrict_geoTransform_empty (geoTransformAlong 𝔫 T) hwf.isClosedSubmanifold_N
        hwf.isCoherent (by rw [d_geoTransformAlong]; exact hd) hwf.isSNCDivisor.1 hE₀T hπ z
      have ih := restrictEquiv_memberRestrict_geoTransformAlong_of_isEmptyTower hn h𝔫 hd hE₀ T hT (π z)
      have hwfS := isWellFormed_memberRestrict hn h𝔫 (membersThrough 𝔫.E E₀ (T.proj (π z)))
      have hcT := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfS.isClosedSubmanifold_N hwfS.isCoherent T
        (isGeoTestTower_of_isEmptyTower _ T hT)).2
      have heq := ih.geoTransform_eq
        (isWellFormed_memberRestrict hn hwf _).isClosedSubmanifold_N.1
        (isWellFormed_memberRestrict hn hwf _).isCoherent hcT (C := ∅) hπ.contMDiff
      rw [heq] at hK
      have hmap : E₀.map (strictAlong (.step T ∅ π hπ)) = (E₀.map (strictAlong T)).map (geoStrictTransform π ∅) := by
        rw [List.map_map]
        rfl
      rw [hmap]
      exact hK

/-- **Re-basing Step 1a's restricted marked ideal across steps that are empty over an open set**: let `𝔫` be well formed
with `d ≥ 1`, `E₀` a list of members, `T` a multiple test blow-up of `𝔫` whose centres miss the open `W`
(`RestrictEmptyTower.CentresAvoid`), and `p` a point over `W`.  The restricted marked ideal formed at the last stage at
`p` (with the strict transforms of `E₀`), restricted to the open preimage of `W`, is restricted-equivalent to the
restricted marked ideal formed at the first stage at the image of `p`, restricted to `W` and transformed along the
restricted tower `T|_W` (whose centres are empty). -/
theorem restrictEquiv_memberRestrict_rebase (hn : 0 < n) {𝔫 : MarkedIdeal n X} (h𝔫 : 𝔫.IsWellFormed)
    (hd : 1 ≤ 𝔫.d) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, H ∈ 𝔫.E) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔫 T) (W : Opens X) (hW : CentresAvoid W T) (p : openPreimage T W) :
    RestrictEquiv
      (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
        (memberRestrict (geoTransformAlong 𝔫 T)
          (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) p)))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X)
        (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (T.proj p)))) (restrict W T)) := by
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hwfW := IsWellFormed.pullback_val h𝔫 W
  have hE₀W : ∀ H ∈ E₀.map ((Subtype.val : W → X) ⁻¹' ·), H ∈ (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).E :=
    fun H hH => by
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact List.mem_map_of_mem (hE₀ H₀ hH₀)
  have hK := restrictEquiv_memberRestrict_geoTransformAlong_of_isEmptyTower (X := CMfd.of (n := n) W) hn hwfW hd hE₀W (restrict W T) he p
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔫 T hT
  have hE₀T := mem_E_geoTransformAlong_of_mem_map 𝔫 hE₀ T
  rw [geoTransformAlong_restrict W h𝔫.isClosedSubmanifold_N h𝔫.isCoherent T hT] at hK
  have hmap : (E₀.map ((Subtype.val : W → X) ⁻¹' ·)).map (strictAlong (restrict W T)) =
      (E₀.map (strictAlong T)).map ((Subtype.val : openPreimage T W → Y) ⁻¹' ·) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun A _ => strictAlong_restrict W T A
  rw [hmap, ← pullback_val_memberRestrict_membersThrough hwfT (by rw [d_geoTransformAlong]; exact hd) hE₀T,
    ← pullback_val_memberRestrict_membersThrough h𝔫 hd hE₀ W, proj_restrict] at hK
  exact hK

end Tower

/-! ### The domain and the values after re-basing -/

section Values

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open BlowupTowers BlowupTowerTransforms ResolutionInvariantExt RestrictEmptyTower HomogenizedGlueingTower MarkedIdealOperationsAlong.MarkedIdeal

/-- Restricted equivalence is symmetric. -/
theorem restrictEquiv_symm {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) : RestrictEquiv 𝔫 𝔪 := by
  refine ⟨h.N_eq.symm, h.E_eq.symm, h.d_eq.symm, ?_, ?_⟩
  · rw [← h.N_eq]; exact h.ge
  · rw [← h.N_eq]; exact h.le

/-- **The domain is invariant under restricted equivalence** (the second ideal coherent): `N`, `E` and `d` agree, and a
germ of the first ideal not vanishing identically on `N` is, on `N`, a combination of germs of the second, one of which
then does not vanish identically on `N` either (`NonmonomialStepAlong.isNonzeroAlongAt_of_isInSpanOnAt`). -/
theorem isInvDomain_of_restrictEquiv {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {k : ℕ} {𝔪 𝔫 : MarkedIdeal n M} (h : IsInvDomain k 𝔪) (hEq : RestrictEquiv 𝔪 𝔫)
    (h𝔫 : 𝔫.ideal.IsCoherent) : IsInvDomain k 𝔫 := by
  have hwf := h.isWellFormed
  refine ⟨⟨?_, h𝔫, ?_, ?_⟩, ?_, ?_, fun y hy => ?_⟩
  · rw [← hEq.N_eq]; exact hwf.isClosedSubmanifold_N
  · rw [← hEq.E_eq]; exact hwf.isSNCDivisor
  · rw [← hEq.N_eq, ← hEq.E_eq]; exact hwf.isTransverse
  · rw [← hEq.N_eq]; exact h.dimLE
  · rw [← hEq.d_eq]; exact h.one_le_d
  · rw [← hEq.N_eq] at hy ⊢
    obtain ⟨g, hg, hfreq⟩ := h.isNonzeroAlongAt y hy
    exact NonmonomialStepAlong.isNonzeroAlongAt_of_isInSpanOnAt (hEq.le y hy g hg) hfreq

variable {X : CMfd.{u} n}

/-- **Along a tower with only empty centres the transform stays in the domain** (such a tower is a multiple test
blow-up). -/
theorem isInvDomain_geoTransformAlong_of_isEmptyTower {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (he : IsEmptyTower T) : IsInvDomain k (geoTransformAlong 𝔪 T) :=
  InvDomainTowerAlong.isInvDomain_geoTransformAlong h T (isGeoTestTower_of_isEmptyTower 𝔪 T he)

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **Canonical segments correspond along restricted equivalence** (both marked ideals in the domain): the values agree
on the common cosupports (property (7), `representative`), so the maximum loci agree. -/
theorem isCanonical_of_restrictEquiv (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 𝔫 : MarkedIdeal n X}
    (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫) (hEq : RestrictEquiv 𝔪 𝔫) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T → IsCanonical 𝔫 (R.inv 𝔫) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have hcos := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq
        h𝔪.isWellFormed.isClosedSubmanifold_N.1 h𝔪.isWellFormed.isCoherent h𝔫.isWellFormed.isCoherent T).1
      show IsCanonical 𝔫 (R.inv 𝔫) T ∧
        (C = ∅ ∨ C = ResolutionDriver.maxLocus (R.inv 𝔫 T) (geoTransformAlong 𝔫 T).cosupp)
      refine ⟨isCanonical_of_restrictEquiv R h𝔪 h𝔫 hEq T hT, hC.imp id fun h => ?_⟩
      rw [h, ← hcos]
      exact maxLocus_congr fun y hy => R.representative 𝔪 𝔫 h𝔪 h𝔫 hEq T hT y hy

/-- **Re-basing the values of a resolution invariant** (`emptyPrefix` and `representative`): let `𝔪` lie in the domain,
`T₀` a tower with only empty centres, and `𝔫` (coherent ideal) restricted-equivalent to the transform `𝔪_{T₀}` (in the
application: the marked ideal formed at the later stage).  If `T₀ T₁` is a canonical segment of `𝔪`, then `𝔫` lies in the
domain, `T₁` is a canonical segment of `𝔫`, and the values of `𝔪` along `T₀ T₁` are those of `𝔫` along `T₁` on the
cosupport. -/
theorem inv_rebase (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (h𝔪 : IsInvDomain k 𝔪)
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (h₀ : IsEmptyTower T₀) {𝔫 : MarkedIdeal n Y₀}
    (hEq : RestrictEquiv 𝔫 (geoTransformAlong 𝔪 T₀)) (h𝔫 : 𝔫.ideal.IsCoherent) (T₁ : BlowupTower Y₀ Y)
    (hcan : IsCanonical 𝔪 (R.inv 𝔪) (T₀.append T₁)) :
    IsInvDomain k 𝔫 ∧ IsCanonical 𝔫 (R.inv 𝔫) T₁ ∧
      ∀ z ∈ (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp, R.inv 𝔪 (T₀.append T₁) z = R.inv 𝔫 T₁ z := by
  have hdom₀ := isInvDomain_geoTransformAlong_of_isEmptyTower h𝔪 T₀ h₀
  have hEq' := restrictEquiv_symm hEq
  have h𝔫d : IsInvDomain k 𝔫 := isInvDomain_of_restrictEquiv hdom₀ hEq' h𝔫
  have hcan₁ := (isCanonical_append_iff R h𝔪 T₀ h₀ T₁).mp hcan
  refine ⟨h𝔫d, isCanonical_of_restrictEquiv R hdom₀ h𝔫d hEq' T₁ hcan₁, fun z hz => ?_⟩
  rw [R.emptyPrefix 𝔪 h𝔪 T₀ T₁ h₀ hcan z hz]
  rw [geoTransformAlong_append] at hz
  exact R.representative _ 𝔫 hdom₀ h𝔫d hEq' T₁ hcan₁ z hz

/-- **Step 1a's restricted marked ideal, re-based** (the form the Step 1 value function uses to compare nearby points):
let `𝔫` be well formed with `d ≥ 1`, `E₀` a list of members, `T` a multiple test blow-up of `𝔫` whose centres miss the
open `W` (the steps between two point-dependent start stages, empty near the point), `p` a point over `W`, and `R` a
resolution invariant in dimension `≤ k`.  Write `𝓢₀ = 𝓢(𝔫, y₀)|_W` for the restricted marked ideal formed at the first
stage at `y₀ = T(p)`, restricted to `W`, and `𝓢₁ = 𝓢(𝔫_T, p)|_{T⁻¹W}` for the one formed at the last stage at `p`.  If
`𝓢₀` lies in the domain and `T|_W T₁` is a canonical segment of it, then `𝓢₁` lies in the domain, `T₁` is a canonical
segment of `𝓢₁`, every transform of `𝓢₁` along `T₁` lies in the domain, and the values of `𝓢₀` along `T|_W T₁` are those of
`𝓢₁` along `T₁` on the cosupport. -/
theorem memberRestrict_rebase (hn : 0 < n) (R : ResolutionInvariant.{u, v} n k Λ) {𝔫 : MarkedIdeal n X}
    (h𝔫 : 𝔫.IsWellFormed) (hd : 1 ≤ 𝔫.d) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, H ∈ 𝔫.E) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔫 T) (W : Opens X) (hW : CentresAvoid W T) (p : openPreimage T W)
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X)
      (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (T.proj p)))))
    {Z : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) (openPreimage T W)) Z)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → X) (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (T.proj p))))
      (R.inv (MarkedIdeal.pullback (Subtype.val : W → X) (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (T.proj p)))))
      ((restrict W T).append T₁)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
        (memberRestrict (geoTransformAlong 𝔫 T) (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) p))) ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
          (memberRestrict (geoTransformAlong 𝔫 T) (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) p)))
        (R.inv (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
          (memberRestrict (geoTransformAlong 𝔫 T) (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) p))))
        T₁ ∧
      IsInvDomain k (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
        (memberRestrict (geoTransformAlong 𝔫 T) (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) p)))
        T₁) ∧
      ∀ z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X)
          (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (T.proj p)))) ((restrict W T).append T₁)).cosupp,
        R.inv (MarkedIdeal.pullback (Subtype.val : W → X) (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (T.proj p))))
            ((restrict W T).append T₁) z =
          R.inv (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
            (memberRestrict (geoTransformAlong 𝔫 T) (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) p)))
            T₁ z := by
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hEq := restrictEquiv_memberRestrict_rebase hn h𝔫 hd hE₀ T hT W hW p
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔫 T hT
  have hcoh := (MarkedIdealRestrictOpen.IsWellFormed.pullback_val
    (isWellFormed_memberRestrict hn hwfT (membersThrough (geoTransformAlong 𝔫 T).E (E₀.map (strictAlong T)) p))
    (openPreimage T W)).isCoherent
  obtain ⟨h1, h2, h3⟩ := inv_rebase (X := CMfd.of (n := n) W) R hdom (restrict W T) he hEq hcoh T₁ hcan
  exact ⟨h1, h2, isInvDomain_of_isCanonical R h1 T₁ h2, h3⟩

end Values

end

end Hironaka.InvDomainRebase
