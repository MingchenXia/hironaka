/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupCompact
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupSequenceIsomorphismOff
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local principalization on a non-compact complex manifold (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.10 (principalization over a
quasi-compact manifold) and §13, Theorem 13.2 (the algorithm applied over relatively compact open subsets: "the
compactness hypothesis guarantees that inv takes only finitely many values"); Włodarczyk 2005
(`wlodarczyk05-hironaka`), §2.3, "(1) ⟹ (2)".

**Statement.**  Let `X` be a complex manifold, not necessarily compact, `K ⊆ X` compact, and `𝔞` a coherent ideal sheaf on
`X` which vanishes identically on no nonempty open set.  Then there are an open neighbourhood `U` of `K`, a finite
sequence of blowups with smooth centres `f : U' → U` and an effective divisor `D` on `U'` such that `f^*(𝔞|_U) = 𝒪(-D)`,
`supp D = f⁻¹ Z(𝔞|_U)` is the union of the members of a divisor with simple normal crossings, and `f` is an isomorphism
over `U \ Z(𝔞)`.

**Route.** The local canonical driver: for a resolution invariant with well-ordered values (the canonical invariant
of `CanonicalCentres`), a marked ideal of the domain on any `X` is resolved over an open neighbourhood of a compact
`K`. Along a canonical segment `T` let `μ` be the maximum of the invariant on the part of the cosupport over `K` (a
compact set: blowups are proper maps). The points of the cosupport with value `≤ μ` form an open set `W` (upper
semicontinuity), and since the projection of the tower is a closed map, `O = X \ T.proj (Wᶜ)` is an open
neighbourhood of `K`. Over `O` the maximum of the invariant on the whole cosupport is `μ`, attained; its maximum
locus is an admissible centre, and after blowing it up every value over `K` is `< μ` (property (3)). The values are
well-ordered, so after finitely many steps nothing of the cosupport lies over `K`, and the base is shrunk once more
to the complement of the image of the cosupport. The successive bases are open sets of open sets; they are brought
back to open sets of `X` by `MaxLocusLocal.nestedDiffeo` and the transport of towers along biholomorphisms.

New basic facts, valid without compactness: a blowup (in the universal-property sense of `IsBlowupAlong`) is a proper map
and is surjective; blowup sequences are surjective and are isomorphisms off the image of their exceptional locus.

## Main results

* `isProperMap_of_isBlowupAlong`, `surjective_of_isBlowupAlong`, `isProperMap_proj`: blowups and the projections of towers
  are proper (hence closed) maps, and blowups are surjective, on any complex manifold;
* `IsBlowupSequence.surjective`, `isIsomorphismOver_compl_of_image_exceptionalLocus_subset`: the same for blowup
  sequences, and the isomorphism off the image of the exceptional locus without compactness;
* `isCanonical_restrict`: canonical segments restrict to open sets (for value functions with the properties of
  `EmbeddedFromResolution.EmbeddingFields`, e.g. every `ResolutionInvariantSeq.ResolutionInvariant`);
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaLocalPrincipalization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealBiholomorphism Hironaka.DivisorExponentAlong Hironaka.BlowupFlatCoordinates Hironaka.BlowupMonomialCharts Hironaka.BlowupLocalSurjectivity
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### Blowups are proper and surjective -/

section Proper

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

/-- **Every point has a neighbourhood with compact preimage under a blowup** (the local half of
`BlowupCompact.compactSpace_of_isBlowupAlong`): off the centre by the section over `M \ C`, on the centre by a flattening
chart and the monomial lifts. -/
theorem exists_mem_nhds_isCompact_preimage (hπ : IsBlowupAlong n C π) (y : M) :
    ∃ K ∈ 𝓝 y, IsCompact (π ⁻¹' K) := by
  by_cases hy : y ∈ C
  · obtain ⟨k, -, -, Φ, hΦsrc, -, hflat⟩ := hπ.1.2 y hy
    set q := Φ.toFun (chartAt (ComplexModel n) y y)
    have hq : q ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
    obtain ⟨R, hR, hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (Φ.isOpen_target.mem_nhds hq)
    refine ⟨_, ?_, BlowupCompact.isCompact_preimage_flatBall hπ hΦsrc hflat hRsub⟩
    have hy' := mem_flatDomain_self Φ
    have hcont : ContinuousAt (fun y' => Φ.toFun (chartAt (ComplexModel n) y y')) y :=
      ((Φ.toFun_holomorphic.differentiableAt
        (Φ.isOpen_source.mem_nhds hy'.2)).continuousAt).comp
        ((chartAt (ComplexModel n) y).continuousAt hy'.1)
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy',
      hcont.eventually (Metric.closedBall_mem_nhds q hR)] with y' h1 h2
    exact ⟨h1, h2⟩
  · have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
    obtain ⟨K, hK, hKsub, hKc⟩ :=
      local_compact_nhds (hπ.1.1.isOpen_compl.mem_nhds hy)
    exact ⟨K, hK, BlowupCompact.isCompact_preimage_of_disjoint hπ hKc
      (Set.disjoint_left.mpr fun _ h hC => hKsub h hC)⟩

/-- **A blowup is a proper map** (on any complex manifold): an ultrafilter whose image converges to `y` lives on the
compact preimage of a neighbourhood of `y`, so it converges there, to a point over `y`. -/
theorem isProperMap_of_isBlowupAlong (hπ : IsBlowupAlong n C π) : IsProperMap π := by
  refine isProperMap_iff_ultrafilter_of_t2.mpr ⟨hπ.contMDiff.continuous, fun 𝒰 y h => ?_⟩
  obtain ⟨K, hK, hKc⟩ := exists_mem_nhds_isCompact_preimage hπ y
  obtain ⟨x, -, hx⟩ := hKc.ultrafilter_le_nhds 𝒰 (le_principal_iff.mpr (h hK))
  exact ⟨x, hx⟩

/-- **A blowup is surjective** (on any complex manifold): its image is closed (a proper map is closed) and contains the
dense complement of the centre. -/
theorem surjective_of_isBlowupAlong (hπ : IsBlowupAlong n C π) : Function.Surjective π := by
  have hclosed : IsClosed (range π) := by
    rw [← image_univ]
    exact (isProperMap_of_isBlowupAlong hπ).isClosedMap _ isClosed_univ
  have hsub : Cᶜ ⊆ range π := fun y hy => by
    obtain ⟨z, -, hz⟩ :=
      (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.2.2 hy
    exact ⟨z, hz⟩
  have hdense : closure Cᶜ = univ := by rw [closure_compl, hπ.2.1, compl_empty]
  intro y
  have h := hclosed.closure_subset_iff.mpr hsub
  rw [hdense] at h
  exact h (mem_univ y)

end Proper

section Sequence

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **A blowup sequence is surjective** (on any complex manifold). -/
theorem IsBlowupSequence.surjective {f : Y → X} (hf : IsBlowupSequence n X Y f) : Function.Surjective f := by
  induction hf with
  | refl => exact Function.surjective_id
  | step f C g _hf hg ih => exact ih.comp (surjective_of_isBlowupAlong hg)

/-- **A blowup sequence is an isomorphism off every set containing the image of its exceptional locus** (on any complex
manifold). -/
theorem isIsomorphismOver_compl_of_image_exceptionalLocus_subset {f : Y → X} (hf : IsBlowupSequence n X Y f)
    {A : Set X} (hA : f '' exceptionalLocus n f ⊆ A) : IsIsomorphismOver n f Aᶜ := by
  have hsurj := IsBlowupSequence.surjective hf
  refine ⟨⟨fun y hy => hy, ?_, ?_⟩, ?_⟩
  · intro y hy y' hy' hyy'
    exact (BlowupSequenceIsomorphismOff.eq_of_apply_eq_of_not_mem_exceptionalLocus hf (y := y)
      (fun hyexc => hy (hA ⟨y, hyexc, rfl⟩)) hyy'.symm).symm
  · intro x hx
    obtain ⟨y, hy⟩ := hsurj x
    refine ⟨y, ?_, hy⟩
    intro hyA
    exact hx (hy ▸ hyA)
  · refine disjoint_left.mpr fun y hy hyexc => hy ?_
    exact hA ⟨y, hyexc, rfl⟩

end Sequence

/-- **The projection of a tower is a proper map** (hence closed, with compact preimages of compact sets). -/
theorem isProperMap_proj {X : CMfd.{u} n} : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsProperMap T.proj
  | _, .refl => isProperMap_id
  | _, .step T _ _ hπ => (isProperMap_proj T).comp (isProperMap_of_isBlowupAlong hπ)

/-! ### Canonical segments on open sets -/

section Canonical

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The restriction of a canonical segment to an open set is a canonical segment** of the restricted marked ideal. -/
theorem isCanonical_restrict (hF : EmbeddedFromResolution.EmbeddingFields n k inv) {X : CMfd.{u} n}
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
        (inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (inv 𝔪) T ∧
          (C = ∅ ∨ C = maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have ih := isCanonical_restrict hF hdom U T hT
      have hTt := hF.isGeoTestTower_of_isCanonical hdom T hT
      show IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
          (inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)) (restrict U T) ∧
        (((Subtype.val : openPreimage T U → _) ⁻¹' C) = ∅ ∨
          ((Subtype.val : openPreimage T U → _) ⁻¹' C) = maxLocus (inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
            (restrict U T)) (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp)
      refine ⟨ih, ?_⟩
      rcases hC with rfl | rfl
      · exact Or.inl preimage_empty
      · by_cases hne : ((Subtype.val : openPreimage T U → _) ⁻¹'
            maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
        · right
          rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
            hdom.isWellFormed.isCoherent U T hTt]
          exact (ResolutionInvariantSegments.maxLocus_preimage _
            (fun p hp => hF.restrictOpen 𝔪 hdom U T hT p hp) hne).symm
        · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

end Canonical

/-! ### Open sets of open sets -/

section Nested

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Back from an open set of an open set to an open set of `M`**: transporting `(𝔫|_A)|_B` along the inverse of
`MaxLocusLocal.nestedDiffeo` gives `𝔫|_D` (coherent ideal). -/
theorem pullback_symm_nestedDiffeo {𝔫 : MarkedIdeal n M} (h𝔞 : 𝔫.ideal.IsCoherent) (A : Opens M) (B : Opens A)
    (D : Opens M) (hBD : ∀ q : A, q ∈ B ↔ (q : M) ∈ D) (hDA : D ≤ A) :
    MarkedIdeal.pullback (MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm
        (MarkedIdeal.pullback (Subtype.val : B → A) (MarkedIdeal.pullback (Subtype.val : A → M) 𝔫)) =
      MarkedIdeal.pullback (Subtype.val : D → M) 𝔫 := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · show ((𝔫.E.map ((Subtype.val : A → M) ⁻¹' ·)).map ((Subtype.val : B → A) ⁻¹' ·)).map
        ((MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm ⁻¹' ·) = 𝔫.E.map ((Subtype.val : D → M) ⁻¹' ·)
    rw [List.map_map, List.map_map]
    rfl
  · show GermIdeal.pullback (m := n) (MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm
        (GermIdeal.pullback (m := n) (Subtype.val : B → A)
          (GermIdeal.pullback (m := n) (Subtype.val : A → M) 𝔫.ideal)) =
      GermIdeal.pullback (m := n) (Subtype.val : D → M) 𝔫.ideal
    rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val contMDiff_subtype_val h𝔞,
      ← GermIdealTotalTransform.pullback_comp (contMDiff_subtype_val.comp contMDiff_subtype_val)
        (MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm.contMDiff h𝔞]
    rfl

end Nested

/-! ### The local canonical driver -/

section LocalDriver

variable {Λ : Type v} [LinearOrder Λ] [WellFoundedLT Λ] {k : ℕ}

/-- **One step of the local process**: if some point of the cosupport along a canonical segment `T` of `𝔪` lies over the
compact `K`, let `μ₀` be the maximum of the invariant there.  There are an open neighbourhood `O` of `K` and a canonical
segment `T₁` of `𝔪|_O` (the restriction of `T` to `O` followed by the blowup of the maximum locus) along which every value
over `K` is `< μ₀`. -/
theorem exists_shrink_step (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ) {X : CMfd.{u} n}
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) {K : Set X} (hK : IsCompact K) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (R.inv 𝔪) T)
    (hne : ((geoTransformAlong 𝔪 T).cosupp ∩ T.proj ⁻¹' K).Nonempty) :
    ∃ z₀ ∈ (geoTransformAlong 𝔪 T).cosupp ∩ T.proj ⁻¹' K, ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y₁ : CMfd.{u} n) (T₁ : BlowupTower (CMfd.of (n := n) O) Y₁),
        IsCanonical (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪)
          (R.inv (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) T₁).cosupp,
          T₁.proj z ∈ (Subtype.val : O → X) ⁻¹' K →
          R.inv (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) T₁ z < R.inv 𝔪 T z₀ := by
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq R
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hTt
  have hSc : IsClosed (geoTransformAlong 𝔪 T).cosupp :=
    GiraudAlong.isClosed_cosupport_along hdomT.isWellFormed.isCoherent hdomT.isWellFormed.isClosedSubmanifold_N _
  -- the maximum `μ₀` of the invariant on the (compact) part of the cosupport over `K`
  have hSK : IsCompact ((geoTransformAlong 𝔪 T).cosupp ∩ T.proj ⁻¹' K) :=
    ((isProperMap_proj T).isCompact_preimage hK).inter_left hSc
  obtain ⟨z₀, hz₀, hmax⟩ :=
    ((R.isInvValue.usc 𝔪 hdom T hcan).mono inter_subset_left).exists_isMaxOn hSK hne
  refine ⟨z₀, hz₀, ?_⟩
  -- the open set `W` of the points off the cosupport or with value `≤ μ₀`
  obtain ⟨W, hWdef⟩ : ∃ W : Set Y,
      W = {y | y ∈ (geoTransformAlong 𝔪 T).cosupp → R.inv 𝔪 T y ≤ R.inv 𝔪 T z₀} := ⟨_, rfl⟩
  have hW : IsOpen W := by
    rw [hWdef, isOpen_iff_mem_nhds]
    intro y hy
    by_cases hyS : y ∈ (geoTransformAlong 𝔪 T).cosupp
    · filter_upwards [R.isInvValue.usc 𝔪 hdom T hcan y hyS] with y' hy' hy'S
      exact (hy' hy'S).trans (hy hyS)
    · filter_upwards [hSc.isOpen_compl.mem_nhds hyS] with y' hy' hy'S
      exact absurd hy'S hy'
  -- the open neighbourhood `O` of `K` over which `W` lies
  obtain ⟨O, hOdef⟩ : ∃ O : Opens X, (O : Set X) = (T.proj '' Wᶜ)ᶜ :=
    ⟨⟨_, ((isProperMap_proj T).isClosedMap _ hW.isClosed_compl).isOpen_compl⟩, rfl⟩
  have hKO : K ⊆ O := by
    rw [hOdef]
    rintro x hx ⟨y, hyW, rfl⟩
    rw [hWdef] at hyW
    exact hyW fun hyS => hmax y ⟨hyS, hx⟩
  have hOW : ∀ y : Y, T.proj y ∈ O → y ∈ W := fun y hy => by
    by_contra hyW
    rw [← SetLike.mem_coe, hOdef] at hy
    exact hy ⟨y, hyW, rfl⟩
  refine ⟨O, hKO, ?_⟩
  -- restrict to `O`
  have hdomO : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) :=
    InvDomainTowerAlong.isInvDomain_pullback_val O hdom
  have hcanO := isCanonical_restrict hF hdom O T hcan
  have hTOt := hF.isGeoTestTower_of_isCanonical hdomO (restrict O T) hcanO
  have hcosO : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T)).cosupp =
      (Subtype.val : openPreimage T O → Y) ⁻¹' (geoTransformAlong 𝔪 T).cosupp :=
    ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
      hdom.isWellFormed.isCoherent O T hTt
  have hvalO : ∀ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T)).cosupp,
      R.inv (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T) p = R.inv 𝔪 T p := fun p hp =>
    R.isInvValue.restrictOpen 𝔪 hdom O T hcan p (by rw [hcosO] at hp; exact hp)
  have hle : ∀ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T)).cosupp,
      R.inv (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T) p ≤ R.inv 𝔪 T z₀ := fun p hp => by
    rw [hvalO p hp]
    have hpS : (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp := by rw [hcosO] at hp; exact hp
    have hpW := hOW p p.2
    rw [hWdef] at hpW
    exact hpW hpS
  -- the centre: the maximum locus over `O`, the level set of `μ₀`
  have hp₀ : (⟨z₀, hKO hz₀.2⟩ : openPreimage T O) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T)).cosupp := by
    rw [hcosO]; exact hz₀.1
  obtain ⟨C, hCdef⟩ : ∃ C, C = maxLocus (R.inv (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T)).cosupp := ⟨_, rfl⟩
  have hp₀C : (⟨z₀, hKO hz₀.2⟩ : openPreimage T O) ∈ C := by
    rw [hCdef]
    exact ⟨hp₀, fun p hp => (hle p hp).trans (hvalO _ hp₀).ge⟩
  have hCadm := hF.isAdmissibleCentre_maxLocus hdomO (restrict O T) hcanO hTOt
  have hCint := ResolutionInvariantDriver.interior_maxLocus_eq_empty hdomO (restrict O T) hTOt
    (R.inv (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T))
  rw [← hCdef] at hCadm hCint
  obtain ⟨Z, π, hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hCint
  refine ⟨Z, BlowupTower.step (restrict O T) C π hπ, ⟨hcanO, Or.inr hCdef⟩, ?_⟩
  -- after the blowup every value over `K` is `< μ₀`
  have hdomTO := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdomO (restrict O T) hTOt
  intro z hz _
  have hzS : π z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (restrict O T)).cosupp :=
    TransformOffCentre.cosupp_geoTransform_subset_preimage _ hdomTO.isWellFormed.isClosedSubmanifold_N.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hdomTO.isWellFormed.isCoherent hg) hπ
      (fun p hp => by rw [hCdef] at hp; exact hp.1) hz
  obtain ⟨hdrop, heq⟩ := R.isInvValue.decrease _ hdomO (restrict O T) C π hπ hcanO ⟨_, hp₀C⟩ hCdef z hz
  by_cases hzC : π z ∈ C
  · exact (hdrop hzC).trans_le (hle _ hzS)
  · rw [heq hzC]
    refine lt_of_le_of_ne (hle _ hzS) fun h => hzC ?_
    rw [hCdef]
    exact ⟨hzS, fun p hp => (hle p hp).trans h.ge⟩

end LocalDriver

end

end Hironaka.HironakaLocalPrincipalization
