/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalNonpureCanonicalResolution

/-!
# Original compact-ambient and exact empty-boundary mixed canonical forms

All existence statements internally choose the actual intrinsic canonical target.
Exact exceptional support is derived for that same target and every genuine
independent smooth-source recipe; it is never an incoming certificate.
Blueprint: `hironaka-original-nonpure-canonical-specializations-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalNonpureCanonicalSpecializations
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaAdmissibleSequence RestrictEmptyTower HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts
  HironakaOriginalIntrinsicNonpureRecipe HironakaOriginalLocalNonpureCanonicalResolution
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
variable {n : ℕ} {X D D' : CMfd.{u} n}

/-- The actual exceptional-support cycle closes by antisymmetry. -/
theorem exact_exceptional_support_of_cycle (T : BlowupTower X D) (F : Set X) (Ef : List (Set D))
    (hExc : exceptionalLocus n T.proj ⊆ ⋃ H∈Ef,H)
    (hNew : (⋃ H∈Ef,H) ⊆ T.proj ⁻¹' F)
    (hBad : T.proj ⁻¹' F ⊆ exceptionalLocus n T.proj) :
    exceptionalLocus n T.proj=(⋃ H∈Ef,H) ∧ (⋃ H∈Ef,H)=T.proj ⁻¹' F :=
  ⟨subset_antisymm hExc (hNew.trans hBad),subset_antisymm hNew (hBad.trans hExc)⟩

/-- Empty initial boundary gives equality with the OWN whole singular set. -/
theorem empty_boundary_geometry_exact {W : Set X} {T : BlowupTower X D} {Ef : List (Set D)}
    (hGeom : HasElementaryGeometry W [] T Ef) :
    exceptionalLocus n T.proj=(⋃ H∈Ef,H) ∧
      (⋃ H∈Ef,H)=T.proj ⁻¹' singularSet (n := n) W := by
  obtain ⟨_hadm,_hEf,hExc,hNew,hSing,_rest⟩ := hGeom
  apply exact_exceptional_support_of_cycle T (singularSet (n := n) W) Ef
  · simpa using hExc
  · simpa using hNew
  · exact hSing

private theorem boundary_union_filter {P : Type*} (E : List (Set P)) :
    (⋃ H∈E.filter (fun H => decide H.Nonempty),H)=⋃ H∈E,H := by
  ext x
  simp only [mem_iUnion,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨H,⟨hH,_hne⟩,hx⟩
    exact ⟨H,hH,hx⟩
  · rintro ⟨H,hH,hx⟩
    exact ⟨H,⟨hH,⟨x,hx⟩⟩,hx⟩

/-- A true comparison transports ENTIRE exceptional support, including empty entries. -/
theorem empty_boundary_exact_of_comparison {W : Set X}
    {T : BlowupTower X D} {S : BlowupTower X D'} {Ef : List (Set D)} {Es : List (Set D')}
    (hGeom : HasElementaryGeometry W [] T Ef)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (hproj : ∀ z,T.proj (η z)=S.proj z)
    (hfilter : Es.filter (fun H => decide H.Nonempty)=
      (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·)) :
    exceptionalLocus n S.proj=(⋃ H∈Es,H) ∧
      (⋃ H∈Es,H)=S.proj ⁻¹' singularSet (n := n) W := by
  obtain ⟨hExc,hSing⟩ := empty_boundary_geometry_exact hGeom
  have hUnion : (⋃ H∈Es,H)=η ⁻¹' (⋃ H∈Ef,H) := by
    rw [← boundary_union_filter Es,hfilter,
      ← HironakaEmbeddedBoundary.preimage_biUnion_list,boundary_union_filter Ef]
  have hprojEq : S.proj=T.proj ∘ η := funext fun z => (hproj z).symm
  have hηExc : exceptionalLocus n η=∅ :=
    eq_empty_of_forall_notMem (MarkedIdealTowerTransport.notMem_exceptionalLocus η)
  have hExcEq : exceptionalLocus n S.proj=η ⁻¹' exceptionalLocus n T.proj := by
    rw [hprojEq,exceptionalLocus_comp
      (T.contMDiff_proj.mdifferentiable (by simp)) (η.contMDiff.mdifferentiable (by simp)),
      hηExc,empty_union]
  constructor
  · rw [hExcEq,hExc,← hUnion]
  · rw [hUnion,hSing,hprojEq]
    rfl

/-- Full intrinsic source OUTPUT with exact support for both actual and independent towers. -/
def HasExactEmptyBoundarySmoothSources (W : Set X)
    (T : BlowupTower X D) (Ef : List (Set D)) : Prop :=
∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X),
  Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
  let W' := b ⁻¹' W
  ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
    IntrinsicOrderedRecipe W' [] Q (Ef.map (g ⁻¹' ·)) ∧
    HasElementaryGeometry W' [] Q (Ef.map (g ⁻¹' ·)) ∧
    exceptionalLocus m Q.proj=(⋃ H∈Ef.map (g ⁻¹' ·),H) ∧
    (⋃ H∈Ef.map (g ⁻¹' ·),H)=Q.proj ⁻¹' singularSet (n := m) W' ∧
    IsActualTowerPullback b Q T g ∧
    strictTransform m Q.proj W'=g ⁻¹' strictTransform n T.proj W ∧
    (∀ k : ℕ,strictTransform m Q.proj (dimensionPart (n := m) W' (k+(m-n)))=
      g ⁻¹' strictTransform n T.proj (dimensionPart (n := n) W k)) ∧
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
    Q.length=T.length ∧ (∀ z,T.proj (g z)=b (Q.proj z)) ∧
    HolomorphicSquarePullback b g Q.proj T.proj ∧
    ∀ (C' : CMfd.{u} m) (S : BlowupTower Y C') (Es : List (Set C')),
      IntrinsicOrderedRecipe W' [] S Es →
      IsSNCDivisor m Es ∧ IsClosedSubmanifold m (strictTransform m S.proj W') ∧
        HasNormalCrossings m (strictTransform m S.proj W') Es ∧
        exceptionalLocus m S.proj=(⋃ H∈Es,H) ∧
        (⋃ H∈Es,H)=S.proj ⁻¹' singularSet (n := m) W' ∧
        ∃! η : C' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ C,
          (∀ z,Q.proj (η z)=S.proj z) ∧
          Es.filter (fun H => decide H.Nonempty)=
            ((Ef.map (g ⁻¹' ·)).filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
          (∀ P : Set Y,strictTransform m S.proj P=η ⁻¹' strictTransform m Q.proj P) ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (g ∘ η) ∧
          HolomorphicSquarePullback b (g ∘ η) S.proj T.proj

/-- The SAME actual source and every intrinsic independent source have exact support. -/
theorem exact_sources_of_empty_boundary {W : Set X} {T : BlowupTower X D} {Ef : List (Set D)}
    (hSources : HasIntrinsicSmoothSources W [] T Ef) :
    HasExactEmptyBoundarySmoothSources W T Ef := by
  intro m Y b hb
  obtain ⟨C,Q,g,hRecipe,hGeom,hactual,hstrict,hparts,hg,hlen,hcomm,hcart,hIndependent⟩ := hSources Y b hb
  have hGeom' : HasElementaryGeometry (b ⁻¹' W) [] Q (Ef.map (g ⁻¹' ·)) := by
    simpa only [List.map_nil] using hGeom
  obtain ⟨hExc,hSing⟩ := empty_boundary_geometry_exact hGeom'
  refine ⟨C,Q,g,?_,hGeom',hExc,hSing,hactual,hstrict,hparts,hg,hlen,hcomm,hcart,?_⟩
  · simpa only [List.map_nil] using hRecipe
  · intro C' S Es hRecipeS
    obtain ⟨hSNC,hSM,hNC,η,hη,hu⟩ := hIndependent C' S Es (by simpa only [List.map_nil] using hRecipeS)
    obtain ⟨hExcS,hSingS⟩ := empty_boundary_exact_of_comparison hGeom' η hη.1 hη.2.1
    exact ⟨hSNC,hSM,hNC,hExcS,hSingS,η,hη,hu⟩

/-- Original compact ambient geometry derives carrier compactness internally. -/
theorem exists_original_nonpure_resolution_of_compactSpace [CompactSpace X]
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hEW : W ⊆ closure (W \ ⋃ H∈E,H)) :
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D) (Ef : List (Set D)),
      IntrinsicOrderedRecipe W E T Ef ∧ HasElementaryGeometry W E T Ef ∧
      HasIntrinsicSmoothSources W E T Ef := by
  exact exists_original_intrinsic_nonpure_resolution W hWa hWa.isClosed.isCompact hint E hE hEW

/-- Compact original carrier, empty boundary, and exact whole support for every source. -/
theorem exists_original_nonpure_empty_boundary_resolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hint : interior W=∅) :
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D) (Ef : List (Set D)),
      IntrinsicOrderedRecipe W [] T Ef ∧ HasElementaryGeometry W [] T Ef ∧
      exceptionalLocus n T.proj=(⋃ H∈Ef,H) ∧
      (⋃ H∈Ef,H)=T.proj ⁻¹' singularSet (n := n) W ∧
      HasIntrinsicSmoothSources W [] T Ef ∧ HasExactEmptyBoundarySmoothSources W T Ef := by
  have hdense : W ⊆ closure (W \ ⋃ H∈([] : List (Set X)),H) := by simpa using (subset_closure : W ⊆ closure W)
  obtain ⟨D,T,Ef,hRecipe,hGeom,hSources⟩ :=
    exists_original_intrinsic_nonpure_resolution W hWa hK hint [] isSNCDivisor_nil hdense
  obtain ⟨hExc,hSing⟩ := empty_boundary_geometry_exact hGeom
  exact ⟨D,T,Ef,hRecipe,hGeom,hExc,hSing,hSources,exact_sources_of_empty_boundary hSources⟩

/-- The compact-ambient empty-boundary endpoint retains the SAME entire source family. -/
theorem exists_original_nonpure_empty_boundary_resolution_of_compactSpace [CompactSpace X]
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅) :
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D) (Ef : List (Set D)),
      IntrinsicOrderedRecipe W [] T Ef ∧ HasElementaryGeometry W [] T Ef ∧
      exceptionalLocus n T.proj=(⋃ H∈Ef,H) ∧
      (⋃ H∈Ef,H)=T.proj ⁻¹' singularSet (n := n) W ∧
      HasIntrinsicSmoothSources W [] T Ef ∧ HasExactEmptyBoundarySmoothSources W T Ef := by
  exact exists_original_nonpure_empty_boundary_resolution W hWa hWa.isClosed.isCompact hint

/-- Original prescribed-open empty-boundary mixed resolution with exact OWN support. -/
theorem exists_original_local_nonpure_empty_boundary_resolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅)
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    let XU := CMfd.of (n := n) U
    let WU : Set XU := (Subtype.val : U → X) ⁻¹' W
    ∃ (D : CMfd.{u} n) (T : BlowupTower XU D) (Ef : List (Set D)),
      IntrinsicOrderedRecipe WU [] T Ef ∧ CentresOver (singularSet (n := n) WU) T ∧
      HasElementaryGeometry WU [] T Ef ∧
      exceptionalLocus n T.proj=(⋃ H∈Ef,H) ∧
      (⋃ H∈Ef,H)=T.proj ⁻¹' singularSet (n := n) WU ∧
      HasIntrinsicSmoothSources WU [] T Ef ∧ HasExactEmptyBoundarySmoothSources WU T Ef := by
  dsimp only
  have hdense : W ⊆ closure (W \ ⋃ H∈([] : List (Set X)),H) := by simpa using (subset_closure : W ⊆ closure W)
  obtain ⟨D,T,Ef,hTree,hover,hGeom,hSources⟩ :=
    exists_original_local_nonpure_resolution W hWa hint [] isSNCDivisor_nil hdense U hK hUK
  simp only [List.map_nil] at hTree hover hGeom hSources
  obtain ⟨hExc,hSing⟩ := empty_boundary_geometry_exact hGeom
  exact ⟨D,T,Ef,⟨_,rfl,hTree⟩,by simpa using hover,hGeom,hExc,hSing,hSources,exact_sources_of_empty_boundary hSources⟩

/-- An original compact set internally chooses one actual open and the entire exact family. -/
theorem exists_original_local_nonpure_empty_boundary_resolution_near_compact
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅)
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X,K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      let XU := CMfd.of (n := n) U
      let WU : Set XU := (Subtype.val : U → X) ⁻¹' W
      ∃ (D : CMfd.{u} n) (T : BlowupTower XU D) (Ef : List (Set D)),
        IntrinsicOrderedRecipe WU [] T Ef ∧ CentresOver (singularSet (n := n) WU) T ∧
        HasElementaryGeometry WU [] T Ef ∧
        exceptionalLocus n T.proj=(⋃ H∈Ef,H) ∧
        (⋃ H∈Ef,H)=T.proj ⁻¹' singularSet (n := n) WU ∧
        HasIntrinsicSmoothSources WU [] T Ef ∧ HasExactEmptyBoundarySmoothSources WU T Ef := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U,hUo,hKU,hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U,hUo⟩,hKU,hUc,
    exists_original_local_nonpure_empty_boundary_resolution W hWa hint ⟨U,hUo⟩ hUc subset_closure⟩

end
end Hironaka.HironakaOriginalNonpureCanonicalSpecializations
