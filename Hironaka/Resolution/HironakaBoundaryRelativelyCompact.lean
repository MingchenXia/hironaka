/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Resolution.HironakaRelativelyCompact
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution relative to a simple normal crossings boundary over relatively compact open sets (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.10 and §13 (the algorithm over
relatively compact open subsets); Kollár 2007 (`kollar07-resolution`), "Principalization, III".

`HironakaPrincipalizationBoundary` principalizes a coherent ideal relative to a simple normal crossings boundary `E₀` when the
zero locus is compact.  Here: over every open set `X₀` contained in a compact set, with no compactness of `Z(𝔞)`, relative to the
restriction of `E₀` (`exists_principalization_boundary_of_subset_isCompact`), and over a relatively compact open neighbourhood of
any compact set, for principalization (`exists_principalization_boundary_local`) and for embedded resolution of a set of pure
dimension (`exists_embeddedResolution_boundary_local`).

**Route.**  The canonical resolution of `(X, X, E₀, 𝔞, 1)` over `X₀` (`HironakaRelativelyCompact.
exists_isCanonical_resolution_of_subset_isCompact`, from the local driver with canonical output), whose restriction to `X₀` is
`(X₀, X₀, E₀|_{X₀}, 𝔞|_{X₀}, 1)`; then the argument of `HironakaPrincipalizationBoundary.exists_principalization_boundary` on
`X₀`: with mark one and `N` everything, the pullback of the ideal is the ideal of the exceptional divisor of the tower, whose
support is the union of the members created by the blowups.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaBoundaryRelativelyCompact

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.DivisorExponentAlong Hironaka.BlowupTowerTransforms Hironaka.HironakaAdmissibleSequence Hironaka.MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-- **Principalization relative to a simple normal crossings boundary over an open set contained in a compact set** (any
complex manifold `X`, no compactness of `Z(𝔞)`): for `𝔞` coherent and nonzero at every point, `E₀` with simple normal crossings
and `X₀ ⊆ X` open, contained in a compact set, there are an admissible blowup sequence `f : X₀' → X₀` of `(X₀, E₀|_{X₀})` with
centres over `Z(𝔞) ∩ X₀`, with divisor `E`, and an effective divisor `D` on `X₀'` such that `E` has simple normal crossings,
`f^*(𝔞|_{X₀}) = 𝒪(-D)`, `supp D` is the union of the members of `E` created by the blowups, `supp D = f⁻¹(Z(𝔞) ∩ X₀)`, and `f` is
an isomorphism over `X₀ \ Z(𝔞)`. -/
theorem exists_principalization_boundary_of_subset_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (D : EffectiveDivisor n X₀') (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) X₀' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞) = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus)ᶜ := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, E₀, 𝔞, 1⟩ with h𝔪
  have hdom : IsInvDomain n 𝔪 := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor (M := X) h𝔞 hne hE₀
  obtain ⟨Y, T, -, hres⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) (X := CMfd.of (n := n) X) (𝔪 := 𝔪) hdom hK X₀ hX₀
  have hdom₀ : IsInvDomain n (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪) :=
    InvDomainTowerAlong.isInvDomain_pullback_val (M := X) X₀ hdom
  have h𝔞₀ : (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞).IsCoherent := hdom₀.isWellFormed.isCoherent
  have hZ₀ : (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞).zeroLocus =
      (Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus :=
    BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val h𝔞
  have hpb : GermIdeal.pullback (m := n) T.proj (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞) =
      (BlowupTowerTransforms.exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution (X := CMfd.of (n := n) X₀)
      (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪) rfl
      hdom₀.isWellFormed.isCoherent rfl T hres
  have hsuppZ : (BlowupTowerTransforms.exceptionalDivisor T).support =
      T.proj ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) := by
    rw [EffectiveDivisor.support, ← hpb, BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj h𝔞₀, hZ₀]
  have hcos : (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪).cosupp = (Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus := by
    rw [show MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪 =
      (⟨univ, E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·), GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞, 1⟩ :
        MarkedIdeal n (CMfd.of (n := n) X₀)) from rfl]
    show GermIdealOrder.cosupport n univ (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞) 1 = _
    rw [GermIdealOrder.cosupport_one
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞₀ hg), univ_inter, hZ₀]
  have hadm := isAdmissibleBlowupSequence_proj (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪) _ T hres.1
    (centresOver_cosupp _ hdom₀.isWellFormed.isClosedSubmanifold_N h𝔞₀ T hres.1)
  rw [hcos] at hadm
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop
    (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪) hdom₀.isWellFormed.isSNCDivisor.1 T
  have hlen : (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪).E.length = E₀.length := List.length_map _
  rw [hlen] at hsupp
  refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, BlowupTowerTransforms.exceptionalDivisor T, _, hadm,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom₀ T hres.1).isWellFormed.isSNCDivisor, hpb, hsupp, hsuppZ, ?_⟩
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
  rw [hsuppZ] at hz'
  exact hz'

/-- **Local principalization relative to a simple normal crossings boundary** (any complex manifold `X`): over a relatively
compact open neighbourhood `U` of a given compact set `K`, the conclusions of `exists_principalization_boundary_of_subset_isCompact`. -/
theorem exists_principalization_boundary_local {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (D : EffectiveDivisor n U') (E : List (Set U')),
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) U' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus)ᶜ := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUo⟩, hKU, hUc,
    exists_principalization_boundary_of_subset_isCompact h𝔞 hne hE₀ ⟨U, hUo⟩ hUc subset_closure⟩

/-- **Local embedded resolution relative to a simple normal crossings boundary** (any complex manifold `X`, `W` analytic of pure
dimension `d < n` with `W ⊆ closure (W \ |E₀|)`): over a relatively compact open neighbourhood `U` of a given compact set `K`, the
conclusions of `HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_subset_isCompact`. -/
theorem exists_embeddedResolution_boundary_local {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆
        f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUo⟩, hKU, hUc, HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_subset_isCompact hWa hd hpure
    hE₀ hE₀W ⟨U, hUo⟩ hUc subset_closure⟩

end

end Hironaka.HironakaBoundaryRelativelyCompact
