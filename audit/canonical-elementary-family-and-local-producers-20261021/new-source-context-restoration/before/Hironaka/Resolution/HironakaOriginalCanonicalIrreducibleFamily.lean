/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionPartResolution
import Hironaka.Resolution.HironakaOriginalFullDimensionIdentity

/-!
# Same actual canonical irreducible prefixes and all-dimensional identity branch

The entire fixed-target pure source family is retained, with the original
connected target and exact empty-boundary exceptional equalities. Full dimension
uses the actual identity, never a false nonzero vanishing-ideal domain.
Blueprint: `hironaka-original-canonical-irreducible-family-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCanonicalIrreducibleFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  CanonicalCentres RestrictEmptyTower HironakaAdmissibleSequence HironakaOriginalPureBoundaryCanonicalPrefix
  HironakaOriginalCanonicalDimensionPartResolution HironakaOriginalFullDimensionIdentity
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaOriginalBoundaryCanonicalPrincipalization HironakaSmoothSubmersionNormalCrossings
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)
open ResolutionDriver (maxLocus)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Transparent OUTPUT: the actual original pure family with the SAME connected target. -/
def ConnectedPureCanonicalFamily (V : ClosedIrreducibleAnalyticSubvariety n X) : Prop :=
  let M : MarkedIdeal n X := ⟨univ,([] : List (Set X)),vanishingIdeal (n := n) V.carrier,1⟩
  let O := boundaryGoodOpen (X := X) V.carrier V.irreducible_carrier.analytic V.dim ([] : List (Set X)) isSNCDivisor_nil
  let F₀ := V.carrier \ regularLocus (n := n) V.carrier V.dim ∪ V.carrier ∩ ⋃ H ∈ ([] : List (Set X)), H
  ∃ (Z : CMfd.{u} n) (P : BlowupTower (X) Z)
    (D : CMfd.{u} n) (T : BlowupTower (X) D) (R : BlowupTower D Z),
    IsCanonical M ((canonicalInvariant n).inv M) P ∧ IsGeoResolution M P ∧
    (T.append R = P ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (V.carrier.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T)
        (geoTransformAlong M T).cosupp, T.proj c ∈ O) ∧
      (V.carrier = ∅ → T.length = 0 ∧ IsEmptyTower P) ∧ CentresOver F₀ T ∧
      IsAdmissibleBlowupSequence n X ([] : List (Set X)) F₀ D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj V.carrier) ∧
      (∀ z ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) z V.dim) ∧
      HasNormalCrossings n (strictTransform n T.proj V.carrier) (geoTransformAlong M T).E ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop ([] : List (Set X)).length, H ∧
      (⋃ H ∈ (geoTransformAlong M T).E.drop ([] : List (Set X)).length, H) ⊆ T.proj ⁻¹' F₀ ∧
      T.proj ⁻¹' (V.carrier \ regularLocus (n := n) V.carrier V.dim) ⊆ exceptionalLocus n T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj F₀ᶜ ∧
      (([] : List (Set X)) = [] → exceptionalLocus n T.proj = ⋃ H ∈ (geoTransformAlong M T).E, H ∧
        (⋃ H ∈ (geoTransformAlong M T).E, H) = T.proj ⁻¹' (V.carrier \ regularLocus (n := n) V.carrier V.dim))) ∧
    IsClosedConnectedSubmanifold n (strictTransform n T.proj V.carrier) V.dim ∧
    exceptionalLocus n T.proj = ⋃ H∈(geoTransformAlong M T).E,H ∧
    (⋃ H∈(geoTransformAlong M T).E,H)=T.proj ⁻¹' singularLocus V ∧
    ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X)
      (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
      let W' := b ⁻¹' V.carrier
      let E' := ([] : List (Set X)).map (b ⁻¹' ·)
      let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
      let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff V.irreducible_carrier.analytic
      let hEY := isSNCDivisor_preimage_submersion hb ([] : List (Set X)) isSNCDivisor_nil
      let O' := boundaryGoodOpen W' hWaY (V.dim+(m-n)) E' hEY
      let F' := W' \ regularLocus (n := m) W' (V.dim+(m-n)) ∪ W' ∩ ⋃ H ∈ E', H
      ∃ (ZB : CMfd.{u} m) (B : BlowupTower Y ZB) (gP : ZB → Z)
        (CQ : CMfd.{u} m) (Q : BlowupTower Y CQ) (g : CQ → D)
        (C : CMfd.{u} m) (S : BlowupTower Y C) (R' : BlowupTower C ZB)
        (η : C ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CQ),
        IsActualTowerPullback b B P gP ∧
        IsCanonical M' ((canonicalInvariant m).inv M') B ∧ IsGeoResolution M' B ∧
        IsActualTowerPullback b Q T g ∧ S.append R' = B ∧
        IsCanonical M' ((canonicalInvariant m).inv M') S ∧ IsGeoTestTower M' S ∧
        CentresAvoid O' S ∧
        (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S)
          (geoTransformAlong M' S).cosupp, S.proj z ∈ O') ∧
        (¬ W'.Nonempty → S.length = 0 ∧ IsEmptyTower B) ∧ F' = b ⁻¹' F₀ ∧
        (∀ z, Q.proj (η z) = S.proj z) ∧
        (∀ η' : C ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CQ,
          (∀ z, Q.proj (η' z) = S.proj z) → η' = η) ∧
        let G := g ∘ η
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
        (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
        strictTransform m S.proj W' = G ⁻¹' strictTransform n T.proj V.carrier ∧
        (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
          ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
        IsSNCDivisor m (geoTransformAlong M' S).E ∧
        IsClosedSubmanifold m (strictTransform m S.proj W') ∧
        (∀ z ∈ strictTransform m S.proj W',
          RegularAtDim (n := m) (strictTransform m S.proj W') z (V.dim+(m-n))) ∧
        HasNormalCrossings m (strictTransform m S.proj W') (geoTransformAlong M' S).E ∧
        CentresOver F' S ∧
        IsAdmissibleBlowupSequence m Y E' F' C S.proj (geoTransformAlong M' S).E ∧
        exceptionalLocus m S.proj ⊆ ⋃ H ∈ (geoTransformAlong M' S).E.drop E'.length, H ∧
        (⋃ H ∈ (geoTransformAlong M' S).E.drop E'.length, H) ⊆ S.proj ⁻¹' F' ∧
        S.proj ⁻¹' (W' \ regularLocus (n := m) W' (V.dim+(m-n))) ⊆ exceptionalLocus m S.proj ∧
        ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ S.proj ∧
        IsProperMap S.proj ∧ Surjective S.proj ∧ IsIsomorphismOver m S.proj F'ᶜ ∧
        (([] : List (Set X)) = [] → exceptionalLocus m S.proj = ⋃ H ∈ (geoTransformAlong M' S).E, H ∧
          (⋃ H ∈ (geoTransformAlong M' S).E, H) = S.proj ⁻¹'
            (W' \ regularLocus (n := m) W' (V.dim+(m-n))))

/-- Transparent OUTPUT: literal actual identity and its entire arbitrary smooth-source dictionary. -/
def FullDimensionCanonicalFamily (V : ClosedIrreducibleAnalyticSubvariety n X) : Prop :=
  exceptionalLocus n (id : X → X)=(⋃ H∈([] : List (Set X)),H) ∧
    (⋃ H∈([] : List (Set X)),H)=(id : X → X) ⁻¹' singularLocus V ∧
    let T : BlowupTower X X := .refl
    T.length = 0 ∧ strictTransform n T.proj V.carrier = V.carrier ∧
      IsClosedConnectedSubmanifold n (strictTransform n T.proj V.carrier) V.dim ∧
      IsTransverse n (strictTransform n T.proj V.carrier) ([] : List (Set X)) ∧
      HasNormalCrossings n (strictTransform n T.proj V.carrier) ([] : List (Set X)) ∧
      singularLocus V = ∅ ∧ exceptionalLocus n T.proj = ∅ ∧
      IsAdmissibleBlowupSequence n X ([] : List (Set X)) ∅ X T.proj ([] : List (Set X)) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj (univ : Set X) ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X)
        (_hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
        let Q : BlowupTower Y Y := .refl
        let E' := ([] : List (Set X)).map (b ⁻¹' ·)
        IsActualTowerPullback b Q T b ∧ Q.length = 0 ∧ IsSNCDivisor m E' ∧
          strictTransform m Q.proj (b ⁻¹' V.carrier) = b ⁻¹' V.carrier ∧
          strictTransform m Q.proj (b ⁻¹' V.carrier) = b ⁻¹' strictTransform n T.proj V.carrier ∧
          IsClosedSubmanifold m (strictTransform m Q.proj (b ⁻¹' V.carrier)) ∧
          (∀ y ∈ strictTransform m Q.proj (b ⁻¹' V.carrier),
            RegularAtDim (n := m) (strictTransform m Q.proj (b ⁻¹' V.carrier)) y m) ∧
          IsTransverse m (strictTransform m Q.proj (b ⁻¹' V.carrier)) E' ∧
          HasNormalCrossings m (strictTransform m Q.proj (b ⁻¹' V.carrier)) E' ∧
          exceptionalLocus m Q.proj = ∅ ∧
          IsAdmissibleBlowupSequence m Y E' ∅ Y Q.proj E' ∧
          ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
          IsProperMap Q.proj ∧ Surjective Q.proj ∧ IsIsomorphismOver m Q.proj (univ : Set Y) ∧
          HolomorphicSquarePullback b b Q.proj T.proj

/-- Genuine fixed original target, connected carrier and exact exceptional
identities, retaining every original smooth-source field. -/
theorem connected_pure_canonical_family (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hK : IsCompact V.carrier) (hd : V.dim<n) : ConnectedPureCanonicalFamily V := by
  obtain ⟨Z,P,D,T,R,hcP,hrP,hTarget,hSources⟩ :=
    exists_original_compact_pure_fixed_target_family V.carrier V.irreducible_carrier.analytic hK
      V.dim hd (HironakaEmbeddedReducible.subset_closure_regularLocus V) [] isSNCDivisor_nil
      (by simpa using (subset_closure : V.carrier ⊆ closure V.carrier))
  have hcopy := hTarget
  rcases hcopy with ⟨_hTR,_hc,_ht,_ha,_hm,_he,_hover,_hadm,_hSNC,hSM,hreg,_hNC,
    hexc,hborn,_hsing,_hhol,_hproper,_hsurj,_hiso,hexact⟩
  have hExcS : T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V := by
    rintro x ⟨z,hz,rfl⟩
    have hh := hborn (hexc hz)
    simpa [singularLocus] using hh
  have hconn := HironakaEmbeddedResolutionLocal.isConnected_strictTransform_of_isBlowupSequence
    T.isBlowupSequence V hExcS
  have heq := hexact rfl
  refine ⟨Z,P,D,T,R,hcP,hrP,hTarget,⟨hSM.1,hconn,hreg⟩,heq.1,?_,hSources⟩
  simpa only [singularLocus] using heq.2

/-- The original full-dimensional branch has its actual identity target and sources. -/
theorem full_dimension_canonical_family (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hd : V.dim=n) : FullDimensionCanonicalFamily V := by
  have hh := full_dimension_identity_smooth_square V hd [] isSNCDivisor_nil
  have hcopy := hh
  rcases hcopy with ⟨_hLen,_hST,_hSM,_hTr,_hNC,hsing,_hrest⟩
  refine ⟨?_,?_,hh⟩
  · simp [exceptionalLocus_id]
  · simp [hsing]

/-- All original irreducible dimensions, with their actual canonical branch,
connected target, exact exceptional equalities and full later source family. -/
theorem exists_original_irreducible_canonical_family
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hK : IsCompact V.carrier) :
    (V.dim<n ∧ ConnectedPureCanonicalFamily V) ∨
      (V.dim=n ∧ FullDimensionCanonicalFamily V) := by
  rcases V.dim_le.lt_or_eq with hd | hd
  · exact Or.inl ⟨hd,connected_pure_canonical_family V hK hd⟩
  · exact Or.inr ⟨hd,full_dimension_canonical_family V hd⟩

/-- Original compact ambient data supply carrier compactness internally. -/
theorem exists_original_irreducible_canonical_family_compactSpace [CompactSpace X]
    (V : ClosedIrreducibleAnalyticSubvariety n X) :
    (V.dim<n ∧ ConnectedPureCanonicalFamily V) ∨
      (V.dim=n ∧ FullDimensionCanonicalFamily V) :=
  exists_original_irreducible_canonical_family V V.isClosed_carrier.isCompact

end
end Hironaka.HironakaOriginalCanonicalIrreducibleFamily
