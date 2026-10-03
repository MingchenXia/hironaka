/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Resolution.HironakaEmbeddedExceptional
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.SmoothCentreInvariant
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Principalization and embedded resolution over relatively compact open sets (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorems 1.6 and 1.10 and §13 ("finite over
every relatively compact open subset"); Włodarczyk 2005 (`wlodarczyk05-hironaka`), §2.3.

**Statement.**  Let `X` be a complex manifold, not necessarily compact, and `X₀ ⊆ X` an open set contained in a compact set
(e.g. a relatively compact open set).
* (principalization) For a coherent ideal `𝔞` nonzero at every point there is an admissible blowup sequence `f : X₀' → X₀`
  (centres over `Z(𝔞)`) and an effective divisor `D` with `f^*(𝔞|_{X₀}) = 𝒪(-D)`, `supp D = ⋃ E = f⁻¹ Z(𝔞)` for its simple
  normal crossings divisor `E`, and `f` an isomorphism over `X₀ \ Z(𝔞)`.
* (embedded resolution) For a closed irreducible analytic subvariety `V` there is an admissible blowup sequence
  `f : X₀' → X₀` (centres over `V_sing`) with simple normal crossings divisor `E`, `Exc f = ⋃ E = f⁻¹(V_sing)`, `f` an
  isomorphism over `X₀ \ V_sing`, and the strict transform of `V ∩ X₀` a closed submanifold of pure dimension `dim V` with
  only normal crossings with `E`.
The local forms (`hir:principalization-local`, `hir:embedded-resolution-local`) follow with admissibility and with a
relatively compact neighbourhood `U` of the compact set.

**Route.**  The local canonical driver (`HironakaEmbeddedResolutionLocal.exists_local_resolution_isCanonical`) gives an open
`U ⊇ K` and a canonical segment resolving the restriction to `U`; it restricts to `X₀ ⊆ U` (`exists_isCanonical_resolution_restrict`:
canonical segments and resolutions restrict to open sets, and the open set `X₀` of `U` is brought back to the open set `X₀` of
`X` by `MaxLocusLocal.nestedDiffeo`).  Then the arguments of `HironakaAdmissibleSequence` apply over `X₀`.

## Main results

* `exists_isCanonical_resolution_restrict`, **`exists_isCanonical_resolution_of_subset_isCompact`**;
* `preimage_val_singularLocus_subset_exceptionalLocus` (the sharpening `f⁻¹(V_sing) ⊆ Exc f` over an open set);
* **`exists_principalization_of_subset_isCompact`**, **`exists_embeddedResolution_of_subset_isCompact`**;
* `exists_principalization_local_admissible`, `exists_embeddedResolution_local_admissible` (local forms with admissibility
  and a relatively compact neighbourhood).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaRelativelyCompact

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.RestrictEmptyTower Hironaka.DivisorExponentAlong Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.HironakaAdmissibleSequence Hironaka.MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.EmbeddedFromResolution (EmbeddingFields regularOpen regularAtDim_of_mem_regularOpen isInvDomain_vanishingIdeal_of_dim_lt isClosedConnectedSubmanifold_of_dim_eq)
open Hironaka.HironakaEmbeddedResolutionLocal (exceptionalDivisor_facts_of_centresAvoid subset_closure_inter_regularOpen)

noncomputable section

variable {n : ℕ}

/-! ### Canonical resolutions over open sets contained in a compact set -/

section Restrict

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **A canonical resolution over an open set restricts to a smaller open set** (for a value function with the properties
`EmbeddingFields`): a canonical segment of `𝔪|_A` with empty final cosupport gives one of `𝔪|_D` for every open `D ⊆ A`
(restriction to the open `D` of `A`, `HironakaLocalPrincipalization.isCanonical_restrict`, then transport along
`MaxLocusLocal.nestedDiffeo`). -/
theorem exists_isCanonical_resolution_restrict (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (hdom : IsInvDomain k 𝔪) (A D : Opens X) (hDA : D ≤ A) {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) A) Y)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : A → X) 𝔪)
      (inv (MarkedIdeal.pullback (Subtype.val : A → X) 𝔪)) T)
    (hres : IsGeoResolution (MarkedIdeal.pullback (Subtype.val : A → X) 𝔪) T) :
    ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) D) Y'),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : D → X) 𝔪)
        (inv (MarkedIdeal.pullback (Subtype.val : D → X) 𝔪)) T' ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : D → X) 𝔪) T' := by
  let B : Opens (CMfd.of (n := n) A) := ⟨(Subtype.val : A → X) ⁻¹' D, D.isOpen.preimage continuous_subtype_val⟩
  have hBD : ∀ q : A, q ∈ B ↔ (q : X) ∈ D := fun q => Iff.rfl
  have hdomA := InvDomainTowerAlong.isInvDomain_pullback_val A hdom
  have hdomB := InvDomainTowerAlong.isInvDomain_pullback_val B hdomA
  have hcanB := HironakaLocalPrincipalization.isCanonical_restrict hF hdomA B T hcan
  have hTtB := MarkedIdealRestrictOpen.isGeoTestTower_restrict B hdomA.isWellFormed.isClosedSubmanifold_N
    hdomA.isWellFormed.isCoherent T hres.1
  have hresB : IsGeoResolution (MarkedIdeal.pullback (Subtype.val : B → A)
      (MarkedIdeal.pullback (Subtype.val : A → X) 𝔪)) (restrict B T) := by
    refine ⟨hTtB, ?_⟩
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdomA.isWellFormed.isClosedSubmanifold_N
      hdomA.isWellFormed.isCoherent B T hres.1, hres.2, preimage_empty]
  have hiso := BlowupTowerIsomorphism.transport_isTowerIso
    (MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm (restrict B T)
  have hres' := (BlowupTowerIsomorphism.IsTowerIso.isGeoResolution_iff
    (MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm
    hdomB.isWellFormed.isClosedSubmanifold_N hdomB.isWellFormed.isCoherent hiso).mpr hresB
  have hcan' := HironakaEmbeddedResolutionLocal.isCanonical_of_isTowerIso hF hdomB
    (MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm hiso hcanB
  rw [HironakaLocalPrincipalization.pullback_symm_nestedDiffeo hdom.isWellFormed.isCoherent A B D hBD hDA]
    at hres' hcan'
  exact ⟨_, _, hcan', hres'⟩

/-- **A resolution invariant with well-ordered values resolves, by a canonical segment, the restriction of a marked ideal of
its domain to every open set contained in a compact set** (any complex manifold): the local canonical driver over a
neighbourhood of the compact set, restricted (`exists_isCanonical_resolution_restrict`). -/
theorem exists_isCanonical_resolution_of_subset_isCompact [WellFoundedLT Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ) {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (hdom : IsInvDomain k 𝔪) {K : Set X} (hK : IsCompact K) (X₀ : Opens X) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) X₀) Y),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪)
        (R.inv (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪)) T ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪) T := by
  obtain ⟨U, hKU, Y, T, hcan, hres⟩ := HironakaEmbeddedResolutionLocal.exists_local_resolution_isCanonical R hdom hK
  exact exists_isCanonical_resolution_restrict (HironakaFromSeqInvariant.embeddingFields_of_seq R) hdom U X₀
    (fun x hx => hKU (hX₀ hx)) T hcan hres

end Restrict

/-! ### `f⁻¹(V_sing) ⊆ Exc f` over an open set -/

section Exceptional

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Over an open set `U`, a smooth strict transform of `V ∩ U` forces `f⁻¹(V_sing ∩ U) ⊆ Exc f`**
(`HironakaEmbeddedExceptional.preimage_singularLocus_subset_exceptionalLocus` for the restriction of `V` to `U`, whose regular
points of dimension `dim V` are those of `V` in `U`). -/
theorem preimage_val_singularLocus_subset_exceptionalLocus {U : Opens X} {U' : Type u} [TopologicalSpace U']
    [ChartedSpace (ComplexModel n) U'] [IsComplexManifold n U'] {f : U' → U}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hreg : ∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier),
      RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) x V.dim) :
    f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ⊆ exceptionalLocus n f := by
  intro y hy
  by_contra hyE
  have hO : IsOpen (exceptionalLocus n f)ᶜ := StrictTransformComposition.isOpen_compl_exceptionalLocus hf
  have hAO : ∀ w ∈ (exceptionalLocus n f)ᶜ, w ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier) ↔
      f w ∈ (Subtype.val : U → X) ⁻¹' V.carrier := fun w hw =>
    ⟨fun h => closure_minimal sdiff_subset
      ((V.isClosed_carrier.preimage continuous_subtype_val).preimage hf.continuous) h,
      fun h => subset_closure ⟨h, hw⟩⟩
  have hyS := (hAO y hyE).mpr hy.1
  have h1 := HironakaEmbeddedExceptional.regularAtDim_of_regularAtDim_preimage hf hyE hO hyE hAO (hreg y hyS)
  exact hy.2 (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp h1)

end Exceptional

/-! ### Principalization over an open set contained in a compact set -/

section Principalization

/-- **Principalization over a relatively compact open set** (Hironaka; `hir:resolution-relatively-compact`): let `X` be any
complex manifold, `𝔞` a coherent ideal sheaf on `X` nonzero at every point, and `X₀ ⊆ X` an open set contained in a compact
set.  There are an admissible blowup sequence `f : X₀' → X₀` (from the empty divisor, centres over `Z(𝔞)`) with divisor `E`
and an effective divisor `D` such that `f^*(𝔞|_{X₀}) = 𝒪(-D)`, `E` has simple normal crossings, `supp D = ⋃ E = f⁻¹ Z(𝔞)`,
and `f` is an isomorphism over `X₀ \ Z(𝔞)`. -/
theorem exists_principalization_of_subset_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x) (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (D : EffectiveDivisor n X₀') (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) X₀' f E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞) = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus)ᶜ := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, [], 𝔞, 1⟩ with h𝔪
  have hdom : IsInvDomain n 𝔪 := HironakaPrincipalization.isInvDomain_univ (M := X) h𝔞 hne
  obtain ⟨Y, T, -, hres⟩ := exists_isCanonical_resolution_of_subset_isCompact
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
      (⟨univ, [], GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞, 1⟩ :
        MarkedIdeal n (CMfd.of (n := n) X₀)) from rfl, cosupp_univ_one h𝔞₀, hZ₀]
  have hadm := isAdmissibleBlowupSequence_proj (MarkedIdeal.pullback (Subtype.val : X₀ → X) 𝔪) _ T hres.1
    (centresOver_cosupp _ hdom₀.isWellFormed.isClosedSubmanifold_N h𝔞₀ T hres.1)
  rw [hcos] at hadm
  refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, BlowupTowerTransforms.exceptionalDivisor T, _, hadm,
    hpb, (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom₀ T hres.1).isWellFormed.isSNCDivisor,
    HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion _ rfl T, hsuppZ, ?_⟩
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
  rw [hsuppZ] at hz'
  exact hz'

/-- **Local principalization, admissible form** (`hir:principalization-local` with the admissibility of the sequence, its
centres over `Z(𝔞)`, and a relatively compact neighbourhood `U` of the compact `K`). -/
theorem exists_principalization_local_admissible {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (D : EffectiveDivisor n U') (E : List (Set U')),
      IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) U' f E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus)ᶜ := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUo⟩, hKU, hUc,
    exists_principalization_of_subset_isCompact h𝔞 hne ⟨U, hUo⟩ hUc subset_closure⟩

end Principalization

/-! ### Embedded resolution over an open set contained in a compact set -/

section EmbeddedResolution

/-- **Embedded resolution over a relatively compact open set** (Hironaka; `hir:resolution-relatively-compact`): let `X` be
any complex manifold, `V ⊆ X` a closed irreducible analytic subvariety and `X₀ ⊆ X` an open set contained in a compact set.
There is an admissible blowup sequence `f : X₀' → X₀` (from the empty divisor, centres over `V_sing`) with divisor `E` such that
`E` has simple normal crossings, `Exc f = ⋃ E = f⁻¹(V_sing ∩ X₀)`, `f` is an isomorphism over `X₀ \ V_sing`, and the strict
transform of `V ∩ X₀` is a closed submanifold of `X₀'`, of dimension `dim V` at each of its points, with only normal
crossings with `E`. -/
theorem exists_embeddedResolution_of_subset_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (V : ClosedIrreducibleAnalyticSubvariety n X)
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' singularLocus V) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' singularLocus V) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier)) x V.dim) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier)) E := by
  rcases V.dim_le.lt_or_eq with h | h
  · have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ :
        MarkedIdeal n (CMfd.of (n := n) X)) :=
      isInvDomain_vanishingIdeal_of_dim_lt le_rfl V h
        (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic)
    obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := exists_isCanonical_resolution_of_subset_isCompact
      (CanonicalCentres.canonicalInvariant.{u} n) hdom (X := CMfd.of (n := n) X) hK X₀ hX₀
    have hdom₀ := InvDomainTowerAlong.isInvDomain_pullback_val X₀ hdom
    rw [SmoothCentreInvariant.pullback_val_smoothCentreMarked (X := CMfd.of (n := n) X) X₀ V.carrier] at hcan₀ hres₀ hdom₀
    -- the data on `X₀`
    set W : Set (CMfd.of (n := n) X₀) := (Subtype.val : X₀ → X) ⁻¹' V.carrier with hWdef
    let O' : Opens (CMfd.of (n := n) X₀) :=
      ⟨(Subtype.val : X₀ → X) ⁻¹' (regularOpen V : Set X), (regularOpen V).isOpen.preimage continuous_subtype_val⟩
    have hO'c : ((O' : Set (CMfd.of (n := n) X₀))ᶜ) = (Subtype.val : X₀ → X) ⁻¹' singularLocus V := by
      ext x
      exact not_not
    have hWa : IsComplexAnalyticSubset (n := n) W :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val V.analytic
    have hreg : ∀ x ∈ W, x ∈ O' → RegularAtDim (n := n) W x V.dim := fun x hxW hxO =>
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (regularAtDim_of_mem_regularOpen hxW hxO)
    have hdense : W ⊆ closure (W ∩ O') := by
      intro x hx
      have h1 := subset_closure_inter_regularOpen V hx
      have h2 := (X₀.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val
        (V.carrier ∩ regularOpen V)
      exact (Set.ext_iff.mp h2 x).mp h1
    obtain ⟨Y, T, hTt, hT, -, hregS, hnc⟩ := exists_tower_embedded_of_isCanonical
      (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{u} n))
      hWa O' hreg hdense hdom₀ T₀ hcan₀ hres₀
    obtain ⟨hsnc, hsupp, hexc, hsing⟩ := exceptionalDivisor_facts_of_centresAvoid hdom₀ rfl O' T hTt hT
    rw [hO'c] at hsing
    have hsub := preimage_val_singularLocus_subset_exceptionalLocus T.contMDiff_proj V hregS
    have hadm := isAdmissibleBlowupSequence_proj _ ((O' : Set (CMfd.of (n := n) X₀))ᶜ) T hTt
      (centresOver_compl_of_centresAvoid O' T hT)
    rw [hO'c] at hadm
    have hExcS : T.proj '' exceptionalLocus n T.proj ⊆ (Subtype.val : X₀ → X) ⁻¹' singularLocus V := by
      rintro x ⟨z, hz, rfl⟩
      exact hsing (hexc hz)
    refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, _, hadm, hsnc, ?_, ?_,
      HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence hExcS,
      ⟨isClosed_closure, fun x hx => ⟨V.dim, hregS x hx⟩⟩, hregS, hnc⟩
    · rw [← hsupp]
      exact Subset.antisymm hexc (hsing.trans hsub)
    · rw [← hsupp]
      exact Subset.antisymm hsing (hsub.trans hexc)
  · -- `dim V = n`: `V` is a connected component of `X`, so `V ∩ X₀` is smooth and the identity works
    have hV := isClosedConnectedSubmanifold_of_dim_eq V h
    have hsing0 : singularLocus V = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 ?_
      show RegularAtDim (n := n) V.carrier x V.dim
      rw [h]
      exact hV.2.2 x hx.1
    set W : Set X₀ := (Subtype.val : X₀ → X) ⁻¹' V.carrier with hWdef
    have hst : strictTransform n (id : X₀ → X₀) W = W := by
      simp [strictTransform, exceptionalLocus_id, (V.isClosed_carrier.preimage continuous_subtype_val).closure_eq, W]
    have hregW : ∀ x ∈ W, RegularAtDim (n := n) W x V.dim := fun x hx =>
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (by rw [h]; exact hV.2.2 _ hx)
    have hWsub : IsClosedSubmanifold n W :=
      ⟨V.isClosed_carrier.preimage continuous_subtype_val, fun x hx => ⟨V.dim, hregW x hx⟩⟩
    refine ⟨X₀, inferInstance, inferInstance, inferInstance, id, [], IsAdmissibleBlowupSequence.refl, isSNCDivisor_nil,
      ?_, ?_, HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
        IsBlowupSequence.refl (by simp [exceptionalLocus_id]), ?_, ?_, ?_⟩
    · simp [exceptionalLocus_id]
    · simp [hsing0]
    · rw [hst]
      exact hWsub
    · rw [hst]
      exact hregW
    · rw [hst]
      exact hasNormalCrossings_nil_of_isClosedSubmanifold hWsub

/-- **Local embedded resolution, admissible form** (`hir:embedded-resolution-local` with `Exc f = ⋃ E = f⁻¹(V_sing ∩ U)`, the
admissibility of the sequence, its centres over `V_sing`, and a relatively compact neighbourhood `U` of the compact `K`). -/
theorem exists_embeddedResolution_local_admissible {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (V : ClosedIrreducibleAnalyticSubvariety n X)
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' singularLocus V) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) x V.dim) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) E := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUo⟩, hKU, hUc, exists_embeddedResolution_of_subset_isCompact V ⟨U, hUo⟩ hUc subset_closure⟩

end EmbeddedResolution

end

end Hironaka.HironakaRelativelyCompact
