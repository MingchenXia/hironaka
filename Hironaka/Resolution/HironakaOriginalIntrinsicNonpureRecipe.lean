/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalNonpureCanonicalResolution
import Hironaka.Resolution.HironakaOriginalCanonicalOrderedChoice

/-!
# Original compact nonpure canonical elementary arrows with intrinsic source recipes

Raw empty padding is permitted by the intrinsic algorithm relation and proved
irrelevant by actual recursive uniqueness. No target comparison enters that
relation, and noncompact smooth sources need no new compact driver.
Blueprint: `hironaka-original-intrinsic-nonpure-recipe-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalIntrinsicNonpureRecipe
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  NormalCrossings HironakaAdmissibleSequence HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts
  HironakaOriginalCanonicalPartListResolution HironakaOriginalCanonicalOrderedResolution
  HironakaOriginalCanonicalSeparationChainChoice HironakaOriginalCanonicalOrderedChoice
  HironakaOriginalNonpureCanonicalResolution HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings HironakaOriginalStoppedBoundaryTransport
variable {n : ℕ} {X D D' : CMfd.{u} n}

/-- Actual intrinsic algorithm provenance, with no target or comparison condition. -/
def IntrinsicOrderedRecipe (W : Set X) (E : List (Set X))
    (T : BlowupTower X D) (Ef : List (Set D)) : Prop :=
  ∃ L : List (Set X × ℕ),
    nonemptyParts L=nonemptyParts ((List.range n).map (fun k => (dimensionPart (n := n) W k,k))) ∧
    CanonicalOrderedResolution E (singularSet (n := n) W ∪ W ∩ ⋃ H∈E,H) L T Ef

/-- Transparent elementary OUTPUT; never a premise of the original existence endpoint. -/
def HasElementaryGeometry (W : Set X) (E : List (Set X))
    (T : BlowupTower X D) (Ef : List (Set D)) : Prop :=
  let G := singularSet (n := n) W ∪ W ∩ ⋃ H∈E,H
  IsAdmissibleBlowupSequence n X E G D T.proj Ef ∧ IsSNCDivisor n Ef ∧
    exceptionalLocus n T.proj ⊆ ⋃ H∈Ef.drop E.length,H ∧
    (⋃ H∈Ef.drop E.length,H) ⊆ T.proj ⁻¹' G ∧
    T.proj ⁻¹' singularSet (n := n) W ⊆ exceptionalLocus n T.proj ∧
    IsIsomorphismOver n T.proj Gᶜ ∧
    IsClosedSubmanifold n (strictTransform n T.proj W) ∧
    strictTransform n T.proj W=⋃ k : Fin n,strictTransform n T.proj (dimensionPart (n := n) W k) ∧
    (∀ k : ℕ,∀ z∈strictTransform n T.proj (dimensionPart (n := n) W k),
      RegularAtDim (n := n) (strictTransform n T.proj W) z k) ∧
    (∀ k j : ℕ,k≠j → Disjoint (strictTransform n T.proj (dimensionPart (n := n) W k))
      (strictTransform n T.proj (dimensionPart (n := n) W j))) ∧
    HasNormalCrossings n (strictTransform n T.proj W) Ef ∧
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧ IsProperMap T.proj ∧ Surjective T.proj

/-- Every real tree has its own entire SNC boundary, not merely a compared filtered list. -/
theorem ordered_tree_final_snc {E : List (Set X)} {G : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalOrderedResolution E G L T Ef) (hE : IsSNCDivisor n E) : IsSNCDivisor n Ef := by
  induction h with
  | nil => exact hE
  | cons T₀ T₁ T hsep hhead htail ih =>
    apply ih
    exact (InvDomainTowerAlong.isInvDomain_geoTransformAlong hhead.domain T₁
      ((CanonicalCentres.canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical
        hhead.domain T₁ hhead.canonical)).isWellFormed.isSNCDivisor

/-- Every independent intrinsic actual recipe gives the same whole elementary arrow. -/
theorem intrinsic_recipe_choice {W : Set X} {E : List (Set X)}
    {T : BlowupTower X D} {S : BlowupTower X D'} {Ef : List (Set D)} {Es : List (Set D')}
    (hT : IntrinsicOrderedRecipe W E T Ef) (hS : IntrinsicOrderedRecipe W E S Es) :
    ∃! η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=S.proj z) ∧
      Es.filter (fun H => decide H.Nonempty)=(Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X,strictTransform n S.proj P=η ⁻¹' strictTransform n T.proj P := by
  obtain ⟨L,hL,hTreeT⟩ := hT
  obtain ⟨L',hL',hTreeS⟩ := hS
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hp : nonemptyParts L'=pulledParts Φ (nonemptyParts L) := by
    rw [hL',hL]
    simp [pulledParts,Φ]
  simpa only [Φ,Diffeomorph.coe_refl,Set.preimage_id,id_eq] using
    ordered_choice_over_base Φ hTreeT hTreeS (by simp [Φ]) hp

private theorem cartesian_precompose_biholomorphism {m : ℕ} {Y C C' : CMfd.{u} m}
    {b : Y → X} {g : C → D} (q : C → Y) (s : C' → Y) (p : D → X)
    (η : C' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ C)
    (hη : ∀ z,q (η z)=s z) (hU : HolomorphicSquarePullback b g q p) :
    HolomorphicSquarePullback b (g ∘ η) s p := by
  intro k W a c ha hc hcone
  obtain ⟨w,hw,huniq⟩ := hU k W a c ha hc hcone
  refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
  · intro z
    exact (hη (η.symm (w z))).symm.trans (by rw [η.apply_symm_apply];exact hw.2.1 z)
  · intro z
    change g (η (η.symm (w z)))=c z
    rw [η.apply_symm_apply]
    exact hw.2.2 z
  · intro v hv
    have he : η ∘ v=w := huniq (η ∘ v)
      ⟨η.contMDiff.comp hv.1,fun z => (hη (v z)).trans (hv.2.1 z),hv.2.2⟩
    funext z
    apply η.injective
    change η (v z)=η (η.symm (w z))
    rw [η.apply_symm_apply]
    exact congrFun he z

/-- Original-only existence, all elementary geometry, and every genuinely
independent intrinsic smooth source over the SAME target. -/
theorem exists_original_intrinsic_nonpure_resolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hint : interior W=∅)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hEW : W ⊆ closure (W \ ⋃ H∈E,H)) :
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D) (Ef : List (Set D)),
      IntrinsicOrderedRecipe W E T Ef ∧ HasElementaryGeometry W E T Ef ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X),
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
        let W' := b ⁻¹' W
        let E' := E.map (b ⁻¹' ·)
        ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
          IntrinsicOrderedRecipe W' E' Q (Ef.map (g ⁻¹' ·)) ∧
          HasElementaryGeometry W' E' Q (Ef.map (g ⁻¹' ·)) ∧
          IsActualTowerPullback b Q T g ∧
          strictTransform m Q.proj W'=g ⁻¹' strictTransform n T.proj W ∧
          (∀ k : ℕ,strictTransform m Q.proj (dimensionPart (n := m) W' (k+(m-n)))=
            g ⁻¹' strictTransform n T.proj (dimensionPart (n := n) W k)) ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
          Q.length=T.length ∧ (∀ z,T.proj (g z)=b (Q.proj z)) ∧
          HolomorphicSquarePullback b g Q.proj T.proj ∧
          ∀ (C' : CMfd.{u} m) (S : BlowupTower Y C') (Es : List (Set C')),
            IntrinsicOrderedRecipe W' E' S Es →
            IsSNCDivisor m Es ∧ IsClosedSubmanifold m (strictTransform m S.proj W') ∧
              HasNormalCrossings m (strictTransform m S.proj W') Es ∧
              ∃! η : C' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ C,
                (∀ z,Q.proj (η z)=S.proj z) ∧
                Es.filter (fun H => decide H.Nonempty)=
                  ((Ef.map (g ⁻¹' ·)).filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
                (∀ P : Set Y,strictTransform m S.proj P=η ⁻¹' strictTransform m Q.proj P) ∧
                Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (g ∘ η) ∧
                HolomorphicSquarePullback b (g ∘ η) S.proj T.proj := by
  obtain ⟨D,T,Ef,hTree,_hover,hadm,hEf,hexc,hborn,hsing,hiso,hSM,hunion,hreg,hdis,hNC,
    hhol,hproper,hsurj,hSources⟩ := exists_original_nonpure_canonical_resolution W hWa hK hint E hE hEW
  have hRecipe : IntrinsicOrderedRecipe W E T Ef := ⟨_,rfl,hTree⟩
  have hGeom : HasElementaryGeometry W E T Ef :=
    ⟨hadm,hEf,hexc,hborn,hsing,hiso,hSM,hunion,hreg,hdis,hNC,hhol,hproper,hsurj⟩
  refine ⟨D,T,Ef,hRecipe,hGeom,?_⟩
  intro m Y b hb
  obtain ⟨C,Q,g,hactual,hTreeQ,hfilterQ,hadmQ,hEQ,hexcQ,hbornQ,hsingQ,hisoQ,hstrictQ,hpartsQ,
    hSMQ,hunionQ,hregQ,hdisQ,hNCQ,hholQ,hproperQ,hsurjQ,hg,hlen,hcomm,hcart⟩ := hSources Y b hb
  have hRecipeQ : IntrinsicOrderedRecipe (b ⁻¹' W) (E.map (b ⁻¹' ·)) Q (Ef.map (g ⁻¹' ·)) :=
    ⟨_,hfilterQ.symm,hTreeQ⟩
  have hlenE : (E.map (b ⁻¹' ·)).length=E.length := List.length_map _
  have hGeomQ : HasElementaryGeometry (b ⁻¹' W) (E.map (b ⁻¹' ·)) Q (Ef.map (g ⁻¹' ·)) := by
    refine ⟨hadmQ,hEQ,?_,?_,hsingQ,hisoQ,hSMQ,hunionQ,hregQ,hdisQ,hNCQ,hholQ,hproperQ,hsurjQ⟩
    · simpa only [hlenE] using hexcQ
    · simpa only [hlenE] using hbornQ
  refine ⟨C,Q,g,hRecipeQ,hGeomQ,hactual,hstrictQ,hpartsQ,hg,hlen,hcomm,hcart,?_⟩
  intro C' S Es hRecipeS
  obtain ⟨η,hη,hu⟩ := intrinsic_recipe_choice hRecipeQ hRecipeS
  have hηsub := HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism η
  have hstrict : strictTransform m S.proj (b ⁻¹' W)=η ⁻¹' strictTransform m Q.proj (b ⁻¹' W) := hη.2.2 _
  have hSMS : IsClosedSubmanifold m (strictTransform m S.proj (b ⁻¹' W)) := by
    rw [hstrict]
    exact isClosedSubmanifold_preimage_submersion hηsub hSMQ
  have hNCS : HasNormalCrossings m (strictTransform m S.proj (b ⁻¹' W)) Es := by
    apply (hasNormalCrossings_filter_nonempty_iff _ _).mp
    rw [hstrict,hη.2.1]
    exact hasNormalCrossings_preimage_submersion hηsub
      ((hasNormalCrossings_filter_nonempty_iff _ _).mpr hNCQ)
  have hSNC : IsSNCDivisor m Es := by
    obtain ⟨L,_hL,hS⟩ := hRecipeS
    exact ordered_tree_final_snc hS (isSNCDivisor_preimage_submersion hb E hE)
  refine ⟨hSNC,hSMS,hNCS,η,⟨hη.1,hη.2.1,hη.2.2,?_,?_⟩,?_⟩
  · exact HironakaSmoothSubmersionOriginalTerminalSubmersion.isSubmersion_precompose_biholomorphism hg η
  · exact cartesian_precompose_biholomorphism Q.proj S.proj T.proj η hη.1 hcart
  · intro η' hh
    exact hu η' ⟨hh.1,hh.2.1,hh.2.2.1⟩

end
end Hironaka.HironakaOriginalIntrinsicNonpureRecipe
