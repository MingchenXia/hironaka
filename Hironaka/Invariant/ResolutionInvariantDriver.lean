import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A resolution invariant resolves every marked ideal of its domain over a compact base

Blueprint `hir:invariant-driver` (`blueprint/src/hironaka.tex`, Hironaka phase H4): the hypotheses of the driver
`ResolutionDriver.exists_isGeoResolution_of_bounded_invariant` (`hir:resolution-driver`) follow from the properties of a
resolution invariant (`ResolutionInvariantSpec.ResolutionInvariant`, `hir:centre-function`).  Sources:
Bierstone--Milman 2008 §7 and Włodarczyk 2005, end of the proof of the resolution theorem (the centres are the maximum
loci of the invariant; local finiteness gives termination); Kollár 2007 §3.4.

Nothing here changes the definition of a resolution invariant: the two facts the driver needs beyond the fields --
*canonical segments are multiple test blow-ups* and *the maximum locus has empty interior* -- are derived.

## Main results

* `isAdmissibleCentre_of_forall_exists_opens`, `isAdmissibleCentre_iff_forall_exists_opens`: **admissible centres are
  local** -- `C` is an admissible centre of `𝔪` iff every point has an open neighbourhood `W` such that `C ∩ W` is one of
  `𝔪|_W` (the converse of `MarkedIdealRestrictOpen.IsAdmissibleCentre.pullback_val`); in particular
  `isAdmissibleCentre_of_pullback_val_top`: admissible for `𝔪|_X` implies admissible for `𝔪`;
* `maxLocus_eq_level`: a nonempty maximum locus is the level set of its value;
* `isAdmissibleCentre_maxLocus`: along a canonical segment which is a multiple test blow-up, the maximum locus of the
  invariant on the cosupport is an admissible centre (property (1) on the whole last stage);
* `isGeoTestTower_of_isCanonical`: **canonical segments are multiple test blow-ups**;
* `interior_cosupp_eq_empty`, `interior_maxLocus_eq_empty`: the cosupport of a marked ideal of `IsInvDomain k`, hence
  every maximum locus along a multiple test blow-up, has empty interior;
* `isCanonical_of_isCanonicalSegment`, `countCentresMeeting_univ_eq_length`: the driver's canonical segments (no empty
  steps) are canonical segments, and their length is the number of centres meeting `X`;
* `exists_isGeoResolution_isCanonicalSegment`: **over a compact base, a resolution invariant in dimension `≤ k`
  resolves every marked ideal of `IsInvDomain k`, by a canonical segment** (iterate the blowup of the maximum locus;
  property (8) with `K = X` bounds the length).

**The results for the first structure are superseded, kept** (blueprint `hir:centre-function-v1-results`):
`isAdmissibleCentre_maxLocus`, `isGeoTestTower_of_isCanonical`, `isInvDomain_of_isCanonical`,
`exists_isGeoResolution_isCanonicalSegment` and `exists_isGeoResolution_isCanonical` are stated for
`ResolutionInvariantSpec.ResolutionInvariant` and lie outside the constant cone of the main theorem; the route's driver is
`ResolutionInvariantSeq.exists_isGeoResolution_isCanonicalSegment` (`hir:invariant-driver-seq`).  The facts of this module about
admissible centres, maximum loci, cosupports and canonical segments of an arbitrary value function are used by the route (all of
them lie in that cone except `isAdmissibleCentre_iff_forall_exists_opens` and `countCentresMeeting_univ_eq_length`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ResolutionInvariantDriver

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdealBiholomorphism.MarkedIdeal
  Hironaka.MarkedIdealRestrictOpen
  Hironaka.NormalCrossings
  Hironaka.ResolutionInvariantOrder Hironaka.ResolutionInvariantSpec
  Hironaka.ResolutionDriver

noncomputable section

variable {n : ℕ}

/-! ### Admissible centres are local -/

section Local

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Admissible centres are local**: if every point of `M` has an open neighbourhood `W` such that the trace `C ∩ W` is an
admissible centre of the restriction `𝔪|_W`, then `C` is an admissible centre of `𝔪` (ideal of holomorphic germs).
Closedness, the regularity of `C`, the inclusion in the cosupport and the normal crossings with `E` are all local. -/
theorem isAdmissibleCentre_of_forall_exists_opens {𝔪 : MarkedIdeal n M}
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {C : Set M}
    (hloc : ∀ x : M, ∃ W : Opens M, x ∈ W ∧
      (pullback (Subtype.val : W → M) 𝔪).IsAdmissibleCentre ((Subtype.val : W → M) ⁻¹' C)) :
    𝔪.IsAdmissibleCentre C := by
  refine ⟨⟨?_, fun x hx => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · -- closedness
    refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
    obtain ⟨W, hxW, hW⟩ := hloc x
    have hmem : ((Subtype.val : W → M) ⁻¹' C)ᶜ ∈ 𝓝 (⟨x, hxW⟩ : W) := hW.1.1.isOpen_compl.mem_nhds hx
    have hmap := W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (⟨x, hxW⟩ : W)
    change Cᶜ ∈ 𝓝 ((⟨x, hxW⟩ : W) : M)
    rw [← hmap]
    exact hmem
  · -- regularity
    obtain ⟨W, hxW, hW⟩ := hloc x
    obtain ⟨k, hk⟩ := hW.1.2 ⟨x, hxW⟩ hx
    exact ⟨k, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hk⟩
  · -- inclusion in the cosupport
    obtain ⟨W, hxW, hW⟩ := hloc x
    have h1 := hW.2.1 (show (⟨x, hxW⟩ : W) ∈ (Subtype.val : W → M) ⁻¹' C from hx)
    rw [cosupp_pullback_val 𝔪 h𝔞 W] at h1
    exact h1
  · -- normal crossings with `E`
    obtain ⟨W, hxW, hW⟩ := hloc x
    obtain ⟨S₀, S, hS, hcard⟩ := hW.2.2 ⟨x, hxW⟩ hx
    set c : Fin 𝔪.E.length → Fin (𝔪.E.map ((Subtype.val : W → M) ⁻¹' ·)).length :=
      Fin.cast (List.length_map _).symm with hc
    have hget : ∀ i : Fin 𝔪.E.length,
        (𝔪.E.map ((Subtype.val : W → M) ⁻¹' ·)).get (c i) = (Subtype.val : W → M) ⁻¹' 𝔪.E.get i := by
      intro i
      simp [hc, List.get_eq_getElem]
    refine ⟨S₀, fun i => S (c i), ?_, fun i hi => hcard (c i) ?_⟩
    · have hS' := NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hS (Option.map c)
        (A' := fun o : Option (Fin 𝔪.E.length) =>
          ((Subtype.val : W → M) ⁻¹' (o.elim C fun i => 𝔪.E.get i) : Set W))
        (S' := fun o : Option (Fin 𝔪.E.length) => o.elim S₀ fun i => S (c i))
        (by
          rintro (_ | i)
          · rfl
          · exact (hget i).symm)
        (by rintro (_ | i) <;> rfl)
      exact NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff.mp hS'
    · change (⟨x, hxW⟩ : W) ∈ (𝔪.E.map ((Subtype.val : W → M) ⁻¹' ·)).get (c i)
      rw [hget i]
      exact hi

/-- **Admissible centres are local** (iff form): `C` is an admissible centre of `𝔪` iff every point has an open
neighbourhood `W` on which `C ∩ W` is an admissible centre of `𝔪|_W`. -/
theorem isAdmissibleCentre_iff_forall_exists_opens {𝔪 : MarkedIdeal n M}
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {C : Set M} :
    𝔪.IsAdmissibleCentre C ↔ ∀ x : M, ∃ W : Opens M, x ∈ W ∧
      (pullback (Subtype.val : W → M) 𝔪).IsAdmissibleCentre ((Subtype.val : W → M) ⁻¹' C) :=
  ⟨fun hC _ => ⟨⊤, trivial, IsAdmissibleCentre.pullback_val h𝔞 hC ⊤⟩,
    isAdmissibleCentre_of_forall_exists_opens h𝔞⟩

/-- **Admissible for the restriction to the whole space implies admissible.** -/
theorem isAdmissibleCentre_of_pullback_val_top {𝔪 : MarkedIdeal n M}
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {C : Set M}
    (h : (pullback (Subtype.val : (⊤ : Opens M) → M) 𝔪).IsAdmissibleCentre
      ((Subtype.val : (⊤ : Opens M) → M) ⁻¹' C)) :
    𝔪.IsAdmissibleCentre C :=
  isAdmissibleCentre_of_forall_exists_opens h𝔞 fun _ => ⟨⊤, trivial, h⟩

/-- **The cosupport of a marked ideal of the domain has empty interior**: on an open set contained in the cosupport
(hence in `N`) every germ of the ideal vanishes (the mark is `≥ 1`), against `𝔞|_N` vanishing identically near no point
of `N`. -/
theorem interior_cosupp_eq_empty {k : ℕ} {𝔪 : MarkedIdeal n M} (h : IsInvDomain k 𝔪) :
    interior 𝔪.cosupp = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  have hyN : y ∈ 𝔪.N := (interior_subset hy : y ∈ 𝔪.cosupp).1
  obtain ⟨g, hg, hfreq⟩ := h.isNonzeroAlongAt y hyN
  obtain ⟨U, hU, hyU, m, s, hs, hgen⟩ := h.isWellFormed.isCoherent y
  obtain ⟨-, m', s', a, hs', -, hgeq⟩ := (hgen y hyU g).mp hg
  -- the local generators vanish on `U ∩ interior cosupp`
  have hvan : ∀ z ∈ U, z ∈ interior 𝔪.cosupp → ∀ j, s j z = 0 := by
    intro z hzU hzi j
    have hzc : z ∈ 𝔪.cosupp := interior_subset hzi
    have hhol : HolomorphicAt n (s j) z := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      exact (hs j w hw).mdifferentiableAt (hU.mem_nhds hw)
    have hmem : 𝔪.ideal.mem z (s j) :=
      (hgen z hzU (s j)).mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨j, rfl⟩ hhol)
    exact (vanishesToOrderOn_one_iff hzc.1 hhol).mp ((hzc.2 (s j) hmem).mono h.one_le_d)
  have hev : ∀ᶠ z in 𝓝 y, g z = 0 := by
    filter_upwards [hgeq, hU.mem_nhds hyU, isOpen_interior.mem_nhds hy] with z hz hzU hzi
    rw [hz]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨j, hj⟩ := hs' i
    rw [← hj, hvan z hzU hzi j, mul_zero]
  obtain ⟨z, ⟨-, hgz⟩, hgz'⟩ := (hfreq.and_eventually hev).exists
  exact hgz hgz'

end Local

/-! ### Maximum loci -/

section MaxLocus

variable {Λ : Type*} [LinearOrder Λ]

/-- **A nonempty maximum locus is the level set of its value.** -/
theorem maxLocus_eq_level {Y : Type*} {f : Y → Λ} {s : Set Y} {y₀ : Y} (hy₀ : y₀ ∈ maxLocus f s) :
    maxLocus f s = {y | y ∈ s ∧ f y = f y₀} := by
  ext y
  constructor
  · rintro ⟨hys, hy⟩
    exact ⟨hys, le_antisymm (hy₀.2 y hys) (hy y₀ hy₀.1)⟩
  · rintro ⟨hys, hy⟩
    exact ⟨hys, fun y' hy' => (hy₀.2 y' hy').trans hy.ge⟩

/-- The maximum locus lies in the set. -/
theorem maxLocus_subset {Y : Type*} (f : Y → Λ) (s : Set Y) : maxLocus f s ⊆ s :=
  fun _ hy => hy.1

end MaxLocus

/-! ### Canonical segments -/

section Canonical

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **The maximum locus is an admissible centre** along a canonical segment which is a multiple test blow-up: property (1)
of `hir:centre-function` on the whole last stage, with the maximum as the level, and locality of admissibility. -/
theorem isAdmissibleCentre_maxLocus (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (R.inv 𝔪) T)
    (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := by
  by_cases hne : (maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := R.admissible 𝔪 h T hcan ⊤ (R.inv 𝔪 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← maxLocus_eq_level hy₀] at hadm
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments are multiple test blow-ups**: every centre is empty or the maximum locus, which is admissible
(`isAdmissibleCentre_maxLocus`, by induction along the segment). -/
theorem isGeoTestTower_of_isCanonical (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T →
      IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
          (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical R h T hT
      refine (isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus R h T hT hTt

/-- Along a canonical segment the transform stays in the domain. -/
theorem isInvDomain_of_isCanonical (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (R.inv 𝔪) T) :
    IsInvDomain k (geoTransformAlong 𝔪 T) :=
  InvDomainTowerAlong.isInvDomain_geoTransformAlong h T (isGeoTestTower_of_isCanonical R h T hcan)

/-- **Maximum loci have empty interior** along every multiple test blow-up of a marked ideal of the domain (they lie in
the cosupport, `interior_cosupp_eq_empty`). -/
theorem interior_maxLocus_eq_empty {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (f : Y → Λ) :
    interior (maxLocus f (geoTransformAlong 𝔪 T).cosupp) = ∅ :=
  eq_empty_of_subset_empty ((interior_mono (maxLocus_subset f _)).trans
    (interior_cosupp_eq_empty (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT)).subset)

/-- **The driver's canonical segments are canonical segments** (`ResolutionDriver.IsCanonicalSegment` has no empty
steps). -/
theorem isCanonical_of_isCanonicalSegment {𝔪 : MarkedIdeal n X} (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsCanonical 𝔪 inv T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, -, hC⟩ := (isCanonicalSegment_step_iff 𝔪 inv T C π hπ).mp hcan
      exact (⟨isCanonical_of_isCanonicalSegment inv T hT, Or.inr hC⟩ :
        IsCanonical 𝔪 inv T ∧ (C = ∅ ∨ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp))

/-- **The length of a canonical segment without empty steps is its number of centres meeting `X`.** -/
theorem countCentresMeeting_univ_eq_length {𝔪 : MarkedIdeal n X}
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T →
      countCentresMeeting (univ : Set X) T = T.length
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hne, -⟩ := (isCanonicalSegment_step_iff 𝔪 inv T C π hπ).mp hcan
      have hne' : (C ∩ T.proj ⁻¹' (univ : Set X)).Nonempty := by
        rw [preimage_univ, inter_univ]
        exact hne
      simp only [countCentresMeeting, countCentresMeeting_univ_eq_length inv T hT, if_pos hne',
        BlowupTower.length_step]

/-- **A resolution invariant resolves every marked ideal of its domain over a compact base, by a canonical segment**
(`hir:canonical-resolution`, existence, from `hir:centre-function`): iterate the blowup of the maximum locus of the
invariant on the cosupport.  The cosupports are closed (`GiraudAlong.isClosed_cosupport_along`), the invariant is upper
semicontinuous on them (2), the maximum loci are admissible centres (1) with empty interior, and canonical segments have
at most `m` centres meeting the compact `X` (8): `ResolutionDriver.exists_isGeoResolution_of_bounded_invariant`.
Superseded (first structure), kept; the route uses `ResolutionInvariantSeq.exists_isGeoResolution_isCanonicalSegment`. -/
theorem exists_isGeoResolution_isCanonicalSegment [CompactSpace X] (R : ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔪 (R.inv 𝔪) T ∧ IsGeoResolution 𝔪 T := by
  obtain ⟨m, hm⟩ := R.locallyFinite 𝔪 h univ isCompact_univ
  refine exists_isGeoResolution_of_bounded_invariant 𝔪 (R.inv 𝔪) ?_ ?_ ?_ m ?_
  · intro Y T _ hT
    have hwf := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
    exact GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
  · intro Y T _ hT
    exact R.usc 𝔪 h T hT
  · intro Y T hcan hT _
    exact ⟨isAdmissibleCentre_maxLocus R h T (isCanonical_of_isCanonicalSegment _ T hcan) hT,
      interior_maxLocus_eq_empty h T hT _⟩
  · intro Y T hcan _
    rw [← countCentresMeeting_univ_eq_length (𝔪 := 𝔪) (R.inv 𝔪) T hcan]
    exact hm T (isCanonical_of_isCanonicalSegment _ T hcan)

/-- The same, with the resolution a canonical segment in the sense of `hir:centre-function`.
Superseded (first structure), kept; the route uses `ResolutionInvariantSeq.exists_isGeoResolution_isCanonical`. -/
theorem exists_isGeoResolution_isCanonical [CompactSpace X] (R : ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T ∧ IsGeoResolution 𝔪 T := by
  obtain ⟨Y, T, hcan, hres⟩ := exists_isGeoResolution_isCanonicalSegment R h
  exact ⟨Y, T, isCanonical_of_isCanonicalSegment _ T hcan, hres⟩

end Canonical

end

end Hironaka.ResolutionInvariantDriver
