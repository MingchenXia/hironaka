/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalPureBoundaryIndependentSource
import Hironaka.Resolution.HironakaOriginalFullDimensionIdentity

/-!
# The same local pure witnesses and all-dimensional original irreducible families

Exact empty-boundary exceptional identities concern the SAME chosen canonical
prefixes and all their actual independently stopped smooth sources. Full
ambient dimension uses literal identities on actual, possibly disconnected,
open restrictions. Blueprint:
`hironaka-original-local-canonical-irreducible-family-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalCanonicalIrreducibleFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  RestrictEmptyTower CanonicalCentres HironakaAdmissibleSequence
  HironakaOriginalLocalPureBoundaryCanonicalPrefix HironakaOriginalLocalPureBoundaryIndependentSource
  HironakaOriginalPureBoundaryCanonicalPrefix HironakaOriginalSmoothIntrinsicRegularLoci
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaOriginalFullDimensionIdentity
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Transparent OUTPUT retaining the ENTIRE actual local family and adding
exact empty-boundary fields for its SAME target and independently stopped S. -/
def HasExactIndependentLocalPureBoundaryResolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (d : ℕ)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (U : Opens X) : Prop :=
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let hWaU := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
  let hEU := isSNCDivisor_preimage_submersion (isSubmersion_val U) E₀ hE₀
  let M : MarkedIdeal n U := ⟨univ,EU,vanishingIdeal (n := n) WU,1⟩
  let O := boundaryGoodOpen (X := CMfd.of (n := n) U) WU hWaU d EU hEU
  let F₀ := WU \ regularLocus (n := n) WU d ∪ WU ∩ ⋃ H ∈ EU, H
  ∃ (Z : CMfd.{u} n) (P : BlowupTower (CMfd.of (n := n) U) Z)
    (D : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) D) (R : BlowupTower D Z),
    IsCanonical M ((canonicalInvariant n).inv M) P ∧ IsGeoResolution M P ∧
    (T.append R = P ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (WU.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T)
        (geoTransformAlong M T).cosupp, T.proj c ∈ O) ∧
      (WU = ∅ → T.length = 0 ∧ IsEmptyTower P) ∧ CentresOver F₀ T ∧
      IsAdmissibleBlowupSequence n U EU F₀ D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj WU) ∧
      (∀ z ∈ strictTransform n T.proj WU,
        RegularAtDim (n := n) (strictTransform n T.proj WU) z d) ∧
      HasNormalCrossings n (strictTransform n T.proj WU) (geoTransformAlong M T).E ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop EU.length, H ∧
      (⋃ H ∈ (geoTransformAlong M T).E.drop EU.length, H) ⊆ T.proj ⁻¹' F₀ ∧
      T.proj ⁻¹' (WU \ regularLocus (n := n) WU d) ⊆ exceptionalLocus n T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj F₀ᶜ) ∧
    (E₀=[] → exceptionalLocus n T.proj = ⋃ H∈(geoTransformAlong M T).E,H ∧
      (⋃ H∈(geoTransformAlong M T).E,H) = T.proj ⁻¹' (WU \ regularLocus (n := n) WU d)) ∧
    ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → U)
      (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
      let W' := b ⁻¹' WU
      let E' := EU.map (b ⁻¹' ·)
      let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
      let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWaU
      let hEY := isSNCDivisor_preimage_submersion hb EU hEU
      let V := boundaryGoodOpen W' hWaY (d+(m-n)) E' hEY
      let F' := W' \ regularLocus (n := m) W' (d+(m-n)) ∪ W' ∩ ⋃ H ∈ E', H
      ∃ (ZB : CMfd.{u} m) (B : BlowupTower Y ZB) (gP : ZB → Z)
        (CQ : CMfd.{u} m) (Q : BlowupTower Y CQ) (g : CQ → D)
        (C : CMfd.{u} m) (S : BlowupTower Y C) (R' : BlowupTower C ZB)
        (η : C ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CQ),
        (IsActualTowerPullback b B P gP ∧
        IsCanonical M' ((canonicalInvariant m).inv M') B ∧ IsGeoResolution M' B ∧
        IsActualTowerPullback b Q T g ∧ S.append R' = B ∧
        IsCanonical M' ((canonicalInvariant m).inv M') S ∧ IsGeoTestTower M' S ∧
        CentresAvoid V S ∧
        (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S)
          (geoTransformAlong M' S).cosupp, S.proj z ∈ V) ∧
        (¬ W'.Nonempty → S.length = 0 ∧ IsEmptyTower B) ∧ F' = b ⁻¹' F₀ ∧
        (∀ z, Q.proj (η z) = S.proj z) ∧
        (∀ η' : C ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CQ,
          (∀ z, Q.proj (η' z) = S.proj z) → η' = η) ∧
        let G := g ∘ η
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
        (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
        strictTransform m S.proj W' = G ⁻¹' strictTransform n T.proj WU ∧
        (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
          ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
        IsSNCDivisor m (geoTransformAlong M' S).E ∧
        IsClosedSubmanifold m (strictTransform m S.proj W') ∧
        (∀ z ∈ strictTransform m S.proj W',
          RegularAtDim (n := m) (strictTransform m S.proj W') z (d+(m-n))) ∧
        HasNormalCrossings m (strictTransform m S.proj W') (geoTransformAlong M' S).E ∧
        CentresOver F' S ∧
        IsAdmissibleBlowupSequence m Y E' F' C S.proj (geoTransformAlong M' S).E ∧
        exceptionalLocus m S.proj ⊆ ⋃ H ∈ (geoTransformAlong M' S).E.drop E'.length, H ∧
        (⋃ H ∈ (geoTransformAlong M' S).E.drop E'.length, H) ⊆ S.proj ⁻¹' F' ∧
        S.proj ⁻¹' (W' \ regularLocus (n := m) W' (d+(m-n))) ⊆ exceptionalLocus m S.proj ∧
        ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ S.proj ∧
        IsProperMap S.proj ∧ Surjective S.proj ∧ IsIsomorphismOver m S.proj F'ᶜ) ∧
        (E₀=[] → exceptionalLocus m S.proj = ⋃ H∈(geoTransformAlong M' S).E,H ∧
          (⋃ H∈(geoTransformAlong M' S).E,H) = S.proj ⁻¹'
            (W' \ regularLocus (n := m) W' (d+(m-n))))


private theorem empty_boundary_exact {q : ℕ} {A B : CMfd.{u} q}
    (W : Set A) (d : ℕ) (E : List (Set A)) (Ef : List (Set B))
    (T : BlowupTower A B) (hE : E=[])
    (hexc : exceptionalLocus q T.proj ⊆ ⋃ H∈Ef.drop E.length,H)
    (hborn : (⋃ H∈Ef.drop E.length,H) ⊆ T.proj ⁻¹'
      (W \ regularLocus (n := q) W d ∪ W ∩ ⋃ H∈E,H))
    (hsing : T.proj ⁻¹' (W \ regularLocus (n := q) W d) ⊆ exceptionalLocus q T.proj) :
    exceptionalLocus q T.proj=⋃ H∈Ef,H ∧
      (⋃ H∈Ef,H)=T.proj ⁻¹' (W \ regularLocus (n := q) W d) := by
  have hexc' : exceptionalLocus q T.proj ⊆ ⋃ H∈Ef,H := by simpa [hE] using hexc
  have hborn' : (⋃ H∈Ef,H) ⊆ T.proj ⁻¹' (W \ regularLocus (n := q) W d) := by
    simpa [hE] using hborn
  exact ⟨Subset.antisymm hexc' (hborn'.trans hsing),
    Subset.antisymm hborn' (hsing.trans hexc')⟩

/-- Original-only local data supply the whole old family plus SAME-witness exact
exceptional equalities; no target or source is chosen again. -/
theorem exists_local_original_pure_exact_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d<n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H∈E₀,H))
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    HasExactIndependentLocalPureBoundaryResolution W hWa d E₀ hE₀ U := by
  unfold HasExactIndependentLocalPureBoundaryResolution
  dsimp only
  have hFull := exists_local_original_independently_stopped_intrinsic_source
    W hWa d hd hpure E₀ hE₀ hE₀W U hK hUK
  unfold HasIndependentLocalPureBoundaryResolution at hFull
  dsimp only at hFull
  obtain ⟨Z,P,D,T,R,hcP,hrP,hTarget,hSources⟩ := hFull
  have hcopy := hTarget
  rcases hcopy with ⟨_hTR,_hcT,_htT,_haT,_hmT,_heT,_hoverT,_hadmT,_hSNCT,_hSMT,_hrT,_hNCT,
    hExcT,hNewT,hSingT,_hholT,_hproperT,_hsurjT,_hisoT⟩
  refine ⟨Z,P,D,T,R,hcP,hrP,hTarget,?_,?_⟩
  · intro he
    exact empty_boundary_exact _ d _ _ T (by simp [he]) hExcT hNewT hSingT
  · intro m Y b hb
    obtain ⟨ZB,B,gP,CQ,Q,g,C,S,R',η,hData⟩ := hSources Y b hb
    have hcopy := hData
    rcases hcopy with ⟨_hactualB,_hcB,_hrB,_hactualQ,_hSR,_hcS,_htS,_haS,_hmS,_heS,_hF,
      _hη,_huniq,_hG,_hproj,_hcart,_hstrict,_hboundary,_hSNCS,_hSMS,_hrS,_hNCS,_hoverS,
      _hadmS,hExcS,hNewS,hSingS,_hholS,_hproperS,_hsurjS,_hisoS⟩
    exact ⟨ZB,B,gP,CQ,Q,g,C,S,R',η,hData,fun he =>
      empty_boundary_exact _ (d+(m-n)) _ _ S (by simp [he]) hExcS hNewS hSingS⟩


/-- Literal empty original boundary, prescribed actual compact-enclosed open. -/
theorem exists_local_pure_empty_exact_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d<n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    HasExactIndependentLocalPureBoundaryResolution W hWa d [] isSNCDivisor_nil U :=
  exists_local_original_pure_exact_family W hWa d hd hpure [] isSNCDivisor_nil
    (by simpa using (subset_closure : W ⊆ closure W)) U hK hUK

/-- The actual neighbourhood is internally chosen before the full target and
all independently stopped smooth sources of the empty-boundary pure input. -/
theorem exists_pure_empty_exact_family_near_compact
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d<n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X,K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      HasExactIndependentLocalPureBoundaryResolution W hWa d [] isSNCDivisor_nil U := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U,hUo,hKU,hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U,hUo⟩,hKU,hUc,
    exists_local_pure_empty_exact_family W hWa d hd hpure ⟨U,hUo⟩ hUc subset_closure⟩

/-- OWN original dimension part and OWN pure singular set, without any
compactness or empty-interior hypothesis on the whole original mixed W. -/
theorem exists_local_dimension_part_empty_exact_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) (hk : k<n)
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    HasExactIndependentLocalPureBoundaryResolution (HironakaEmbeddedDimensionParts.dimensionPart (n := n) W k)
      (HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hWa k)
      k [] isSNCDivisor_nil U :=
  exists_local_pure_empty_exact_family _
    (HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hWa k) k hk
    (HironakaEmbeddedDimensionParts.subset_closure_regularLocus_dimensionPart hWa.isClosed k) U hK hUK

/-- One true neighbourhood for the SAME own-part family before every source. -/
theorem exists_dimension_part_empty_exact_family_near_compact
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) (hk : k<n)
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X,K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      HasExactIndependentLocalPureBoundaryResolution (HironakaEmbeddedDimensionParts.dimensionPart (n := n) W k)
        (HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hWa k)
        k [] isSNCDivisor_nil U :=
  exists_pure_empty_exact_family_near_compact _
    (HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hWa k) k hk
    (HironakaEmbeddedDimensionParts.subset_closure_regularLocus_dimensionPart hWa.isClosed k) hK

/-- The actual open restriction has exactly the original irreducible singular
locus as its own pure-dimensional singular set, even if disconnected or empty. -/
theorem singular_locus_restrict
    (V : ClosedIrreducibleAnalyticSubvariety n X) (U : Opens X) :
    ((Subtype.val : U → X) ⁻¹' V.carrier) \ regularLocus (n := n)
      ((Subtype.val : U → X) ⁻¹' V.carrier) V.dim =
      (Subtype.val : U → X) ⁻¹' singularLocus V := by
  simpa only [singularLocus,Nat.sub_self,Nat.add_zero] using
    (singular_set_preimage_eq (X := X) (Y := CMfd.of (n := n) U)
      (isSubmersion_val U) V.carrier V.dim).symm

/-- Proper-dimensional original irreducibility supplies every natural pure
input; the SAME local family retains its literal original singular dictionary. -/
theorem local_irreducible_proper_family
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hd : V.dim<n)
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    HasExactIndependentLocalPureBoundaryResolution V.carrier V.irreducible_carrier.analytic
      V.dim [] isSNCDivisor_nil U ∧
    ((Subtype.val : U → X) ⁻¹' V.carrier) \ regularLocus (n := n)
      ((Subtype.val : U → X) ⁻¹' V.carrier) V.dim =
      (Subtype.val : U → X) ⁻¹' singularLocus V := by
  exact ⟨exists_local_original_pure_exact_family V.carrier V.irreducible_carrier.analytic
    V.dim hd (HironakaEmbeddedReducible.subset_closure_regularLocus V) [] isSNCDivisor_nil
      (by simpa using (subset_closure : V.carrier ⊆ closure V.carrier)) U hK hUK,
    singular_locus_restrict V U⟩

/-- Transparent OUTPUT: literal local identity, exact own/original singular
fields and the entire actual arbitrary smooth-source identity family. -/
def FullDimensionLocalCanonicalFamily
    (V : ClosedIrreducibleAnalyticSubvariety n X) (U : Opens X) : Prop :=
  let WU := (Subtype.val : U → X) ⁻¹' V.carrier
  let F := (Subtype.val : U → X) ⁻¹' singularLocus V
  let T : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U) := .refl
  T.length=0 ∧ strictTransform n T.proj WU=WU ∧
    IsClosedSubmanifold n (strictTransform n T.proj WU) ∧
    (∀ x∈strictTransform n T.proj WU,RegularAtDim (n := n) (strictTransform n T.proj WU) x n) ∧
    IsTransverse n (strictTransform n T.proj WU) [] ∧
    HasNormalCrossings n (strictTransform n T.proj WU) [] ∧
    IsSNCDivisor n ([] : List (Set U)) ∧ F=∅ ∧
    WU \ regularLocus (n := n) WU V.dim=F ∧
    exceptionalLocus n T.proj=(⋃ H∈([] : List (Set U)),H) ∧
    (⋃ H∈([] : List (Set U)),H)=T.proj ⁻¹' F ∧
    IsAdmissibleBlowupSequence n U [] F U T.proj [] ∧
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
    IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj (univ : Set U) ∧
    ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → U)
      (_hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
      let Q : BlowupTower Y Y := .refl
      let W' := b ⁻¹' WU
      let F' := W' \ regularLocus (n := m) W' (V.dim+(m-n))
      IsActualTowerPullback b Q T b ∧ Q.length=0 ∧
        strictTransform m Q.proj W'=W' ∧
        strictTransform m Q.proj W'=b ⁻¹' strictTransform n T.proj WU ∧
        IsClosedSubmanifold m (strictTransform m Q.proj W') ∧
        (∀ y∈strictTransform m Q.proj W',RegularAtDim (n := m) (strictTransform m Q.proj W') y m) ∧
        (∀ y∈strictTransform m Q.proj W',
          RegularAtDim (n := m) (strictTransform m Q.proj W') y (V.dim+(m-n))) ∧
        IsTransverse m (strictTransform m Q.proj W') [] ∧
        HasNormalCrossings m (strictTransform m Q.proj W') [] ∧
        IsSNCDivisor m ([] : List (Set Y)) ∧ F'=b ⁻¹' F ∧
        exceptionalLocus m Q.proj=(⋃ H∈([] : List (Set Y)),H) ∧
        (⋃ H∈([] : List (Set Y)),H)=Q.proj ⁻¹' F' ∧
        IsAdmissibleBlowupSequence m Y [] F' Y Q.proj [] ∧
        ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
        IsProperMap Q.proj ∧ Surjective Q.proj ∧ IsIsomorphismOver m Q.proj (univ : Set Y) ∧
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b ∧
        (∀ y,T.proj (b y)=b (Q.proj y)) ∧
        HolomorphicSquarePullback b b Q.proj T.proj

private theorem regular_of_isOpen {q : ℕ} {A : CMfd.{u} q}
    (W : Set A) (hW : IsOpen W) (x : A) (hx : x∈W) :
    RegularAtDim (n := q) W x q :=
  RegularPointDimension.regularAtDim_of_inter_eq hW hx (by simp)
    (AnalyticIrreducibleComponents.regularAtDim_univ x)

/-- Full original dimension uses actual identities on this true open; neither
restriction nor arbitrary smooth inverse image is assumed connected. -/
theorem full_dimension_local_canonical_family
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hd : V.dim=n) (U : Opens X) :
    FullDimensionLocalCanonicalFamily V U := by
  unfold FullDimensionLocalCanonicalFamily
  dsimp only
  let WU := (Subtype.val : U → X) ⁻¹' V.carrier
  let F := (Subtype.val : U → X) ⁻¹' singularLocus V
  let T : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U) := .refl
  have hV := EmbeddedFromResolution.isClosedConnectedSubmanifold_of_dim_eq V hd
  have hVo : IsOpen V.carrier :=
    AnalyticIrreducibleComponents.isOpen_of_forall_regularAtDim_self hV.2.2
  have hWo : IsOpen WU := hVo.preimage continuous_subtype_val
  have hWc : IsClosed WU := V.isClosed_carrier.preimage continuous_subtype_val
  have hsing : singularLocus V=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hx.2
    change RegularAtDim (n := n) V.carrier x V.dim
    simpa only [hd] using hV.2.2 x hx.1
  have hF : F=∅ := by simp [F,hsing]
  have hOwn : WU \ regularLocus (n := n) WU V.dim=F := singular_locus_restrict V U
  have hst : strictTransform n T.proj WU=WU := by
    change strictTransform n (id : U → U) WU=WU
    simp [strictTransform,exceptionalLocus_id]
  have ht := isTransverse_of_isOpen (X := CMfd.of (n := n) U) WU hWo [] isSNCDivisor_nil
  have hi : IsIsomorphismOver n (id : U → U) (univ : Set U) := by
    simpa using HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      (IsBlowupSequence.refl (n := n) (X := U)) (A := (∅ : Set U)) (by simp [exceptionalLocus_id])
  refine ⟨rfl,hst,?_,?_,?_,?_,isSNCDivisor_nil,hF,hOwn,?_,?_,?_,
    contMDiff_id,isProperMap_id,surjective_id,hi,?_⟩
  · rw [hst]
    exact ⟨hWc,fun x hx => ⟨n,regular_of_isOpen (A := CMfd.of (n := n) U) WU hWo x hx⟩⟩
  · change ∀ x∈strictTransform n T.proj WU,
      RegularAtDim (n := n) (strictTransform n T.proj WU) x n
    rw [hst]
    exact regular_of_isOpen (A := CMfd.of (n := n) U) WU hWo
  · change IsTransverse n (strictTransform n T.proj WU) []
    rw [hst]
    exact ht
  · change HasNormalCrossings n (strictTransform n T.proj WU) []
    rw [hst]
    exact ht.hasNormalCrossings
  · simp [exceptionalLocus_id]
  · change (⋃ H∈([] : List (Set U)),H)=T.proj ⁻¹' F
    rw [hF]
    simp
  · change IsAdmissibleBlowupSequence n U [] F U (id : U → U) []
    rw [hF]
    exact IsAdmissibleBlowupSequence.refl
  · intro m Y b hb
    let W' := b ⁻¹' WU
    let F' := W' \ regularLocus (n := m) W' (V.dim+(m-n))
    let Q : BlowupTower Y Y := .refl
    have hW'o : IsOpen W' := hWo.preimage hb.contMDiff.continuous
    have hW'c : IsClosed W' := hWc.preimage hb.contMDiff.continuous
    have hQst : strictTransform m Q.proj W'=W' := by
      change strictTransform m (id : Y → Y) W'=W'
      simp [strictTransform,exceptionalLocus_id]
    have hF' : F'=b ⁻¹' F := by
      change (b ⁻¹' WU) \ regularLocus (n := m) (b ⁻¹' WU) (V.dim+(m-n))=b ⁻¹' F
      rw [← singular_set_preimage_eq (X := CMfd.of (n := n) U) (Y := Y) hb WU V.dim,hOwn]
    have hF'0 : F'=∅ := by rw [hF',hF,preimage_empty]
    have hshift : ∀ y∈W',RegularAtDim (n := m) W' y (V.dim+(m-n)) := by
      intro y hy
      by_contra hn
      have hh : y∈F' := ⟨hy,hn⟩
      rw [hF'0] at hh
      exact hh
    have htr := isTransverse_of_isOpen W' hW'o [] isSNCDivisor_nil
    have ha : IsActualTowerPullback b Q T b := .refl hb
    have hiso : IsIsomorphismOver m (id : Y → Y) (univ : Set Y) := by
      simpa using HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
        (IsBlowupSequence.refl (n := m) (X := Y)) (A := (∅ : Set Y)) (by simp [exceptionalLocus_id])
    refine ⟨ha,rfl,hQst,?_,?_,?_,?_,?_,?_,isSNCDivisor_nil,hF',?_,?_,?_,
      contMDiff_id,isProperMap_id,surjective_id,hiso,hb,fun _ => rfl,ha.universal⟩
    · rw [hQst,hst]
    · rw [hQst]
      exact ⟨hW'c,fun y hy => ⟨m,regular_of_isOpen W' hW'o y hy⟩⟩
    · change ∀ y∈strictTransform m Q.proj W',
        RegularAtDim (n := m) (strictTransform m Q.proj W') y m
      rw [hQst]
      exact regular_of_isOpen W' hW'o
    · change ∀ y∈strictTransform m Q.proj W',
        RegularAtDim (n := m) (strictTransform m Q.proj W') y (V.dim+(m-n))
      rw [hQst]
      exact hshift
    · change IsTransverse m (strictTransform m Q.proj W') []
      rw [hQst]
      exact htr
    · change HasNormalCrossings m (strictTransform m Q.proj W') []
      rw [hQst]
      exact htr.hasNormalCrossings
    · simp [exceptionalLocus_id]
    · change (⋃ H∈([] : List (Set Y)),H)=Q.proj ⁻¹' F'
      rw [hF'0]
      simp
    · change IsAdmissibleBlowupSequence m Y [] F' Y (id : Y → Y) []
      rw [hF'0]
      exact IsAdmissibleBlowupSequence.refl

/-- The true original compact neighbourhood and its target are chosen before
all actual smooth sources, in every original irreducible dimension. -/
theorem exists_original_local_irreducible_canonical_family
    (V : ClosedIrreducibleAnalyticSubvariety n X) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X,K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      ((V.dim<n ∧ HasExactIndependentLocalPureBoundaryResolution V.carrier
        V.irreducible_carrier.analytic V.dim [] isSNCDivisor_nil U ∧
        ((Subtype.val : U → X) ⁻¹' V.carrier) \ regularLocus (n := n)
          ((Subtype.val : U → X) ⁻¹' V.carrier) V.dim =
          (Subtype.val : U → X) ⁻¹' singularLocus V) ∨
       (V.dim=n ∧ FullDimensionLocalCanonicalFamily V U)) := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U,hUo,hKU,hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  refine ⟨⟨U,hUo⟩,hKU,hUc,?_⟩
  rcases V.dim_le.lt_or_eq with hd | hd
  · exact Or.inl ⟨hd,local_irreducible_proper_family V hd ⟨U,hUo⟩ hUc subset_closure⟩
  · exact Or.inr ⟨hd,full_dimension_local_canonical_family V hd ⟨U,hUo⟩⟩

end
end Hironaka.HironakaOriginalLocalCanonicalIrreducibleFamily
