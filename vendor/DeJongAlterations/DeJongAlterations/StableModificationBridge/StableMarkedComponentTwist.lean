/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedNativeExactness
import DeJongAlterations.StableModificationBridge.StableMarkedLocalCokernel
import DeJongAlterations.StableModificationBridge.StableOpenNormalizedMarkSet

/-! Constructed original marked dualizing bundle and ALL genuine native component
marking exactness/cokernel data. Blueprint: `stable-marked-component-twist.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableMarkedComponentTwist
open StableModification StableModification.Projectivity Cohomology
open Omega.ComponentDegree Omega.ComponentNormalization Omega.RosenlichtComponent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) (D : X.IdealSheafData)
  {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
  [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))]
  (η : pullback (C := Scheme.{u}) f a)

/-- CONSTRUCTED output data for the SAME original D, canonical singleton
normalization, native map, and original coefficient field. No data record is an input
in the producer below. -/
structure MarkedComponentTwistData [LocallyOfFinitePresentation f] (E : LocalEquations X) where
  marks : Finset (componentNormalization f a η)
  marks_mem : ∀ y, y ∈ marks ↔ componentMap f a η y ∈ (D.support : Set X)
  marks_closed : ∀ y ∈ marks, IsClosed ({y} : Set (componentNormalization f a η))
  injective : ∀ W : (componentNormalization f a η).Opens,
    Function.Injective ((StableMarkedNativePullback.pullbackMarkedTwistMap E
      (Omega.dualizingSheaf f) (componentMap f a η)).app W)
  surjective : ∀ W : (componentNormalization f a η).Opens,
    (∀ y ∈ marks, y ∉ W) →
      Function.Surjective ((StableMarkedNativePullback.pullbackMarkedTwistMap E
        (Omega.dualizingSheaf f) (componentMap f a η)).app W)
  local_cokernel : ∀ y ∈ marks, ∃ W : (componentNormalization f a η).Opens,
    IsAffineOpen W ∧ y ∈ W ∧ (∀ z ∈ marks, z ∈ W → z = y) ∧
    FiniteDimensional K (sectionsCoker (structureCoeff (componentStructure f a η))
      (StableMarkedNativePullback.pullbackMarkedTwistMap E (Omega.dualizingSheaf f)
        (componentMap f a η)) W) ∧
    Module.finrank K (sectionsCoker (structureCoeff (componentStructure f a η))
      (StableMarkedNativePullback.pullbackMarkedTwistMap E (Omega.dualizingSheaf f)
        (componentMap f a η)) W) = 1

/-- For ONE FIXED original Cartier marking bundle, all genuine native component
exactness and local cokernels are constructed from the original family. -/
theorem exists_markedComponentTwistData [DeJong.IsNodalCurve f] [IsProper f]
    [IsIntegral S] [IsLocallyNoetherian S]
    [IsAlgClosed K] [CompactSpace (pullback (C := Scheme.{u}) f a)]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → DeJong.IsSmoothAt f x)
    (hD : DeJong.IsSemistablePair f D)
    (E : LocalEquations X)
    (hEi : ∀ i, ∃ h : IsAffineOpen (E.U i),
      D.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i})
    (hEs : ∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D.support : Set X))
    (hη : η ∈ genericPoints (pullback (C := Scheme.{u}) f a)) :
    Nonempty (MarkedComponentTwistData f D a η E) := by
  classical
  obtain ⟨M, hM, hMc, -⟩ := StableOpenNormalizedMarkSet.exists_original_mark_finset f D hD a η hη
  let N := componentNormalization f a η
  let ν := componentMap f a η
  let q := componentStructure f a η
  have hω := Omega.isInvertibleModule_dualizingSheaf_of_isNodalCurve f hS hgen
  have hnmark : ν (genericPoint N) ∉ (D.support : Set X) := by
    intro hg
    have hc := hMc _ ((hM _).mpr hg)
    obtain ⟨z, hz, hzη⟩ := exists_mem_closure_ne f a hη
    obtain ⟨w, hw⟩ := exists_ne_genericPoint η hz hzη
    have H : (Set.univ : Set N) ⊆ {genericPoint N} :=
      ((genericPoint_spec N).mem_closed_set_iff hc).mp (Set.mem_singleton (genericPoint N))
    exact hw (H (Set.mem_univ w))
  have hηE : ν (genericPoint N) ∈ E.canonicalSection.nonvanishingLocus :=
    (hEs _).mpr hnmark
  obtain ⟨_, hEt⟩ := StableOpenNormalizedMarkSet.finite_etale_original_pullback_marking
    f D hD a η hη
  let : Etale ((D.comap ν).subschemeι ≫ q) := hEt
  refine ⟨⟨M, hM, hMc,
    (fun W => StableMarkedNativeExactness.injective_app E _ hω ν hηE W), ?_, ?_⟩⟩
  · intro W hW
    apply StableMarkedNativeExactness.surjective_app_of_nonvanishing E _ hω ν hηE W
    intro y hyW
    exact (hEs _).mpr (fun hyD => hW y ((hM y).mpr hyD) hyW)
  · exact StableMarkedLocalCokernel.exists_local_cokernel q E D hEi _ hω ν M hM hMc

/-- The ORIGINAL semistable family internally chooses ONE original omega(D) bundle
BEFORE all algebraically closed fields, actual geometric points, and native components.
No equation/bundle/mark-set/map exactness or cokernel certificate is an input. -/
theorem exists_uniform_markedComponentTwistData [DeJong.IsNodalCurve f] [IsProper f]
    [IsIntegral S] [IsLocallyNoetherian S]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → DeJong.IsSmoothAt f x)
    (hD : DeJong.IsSemistablePair f D) :
    ∃ E : LocalEquations X,
      (∀ i, ∃ h : IsAffineOpen (E.U i), IsRegular (E.f i) ∧
        D.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i}) ∧
      (∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D.support : Set X)) ∧
      ∃ L : LineBundleData X,
        Nonempty (L.twist (unitModule X) 1 ≅ E.toLineBundleData.twist (Omega.dualizingSheaf f) 1) ∧
        ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
          [CompactSpace (pullback (C := Scheme.{u}) f a)]
          [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))],
          ∀ η ∈ genericPoints (pullback (C := Scheme.{u}) f a),
            Nonempty (MarkedComponentTwistData f D a η E) := by
  obtain ⟨E, hEi, hEs, L, he⟩ := StableMarkedDualizingBundle.exists_markedDualizingBundle
    f hS hgen D hD
  refine ⟨E, hEi, hEs, L, he, ?_⟩
  intro K _ _ a _ _ η hη
  apply exists_markedComponentTwistData f D a η hS hgen hD E ?_ hEs hη
  intro i
  obtain ⟨ha, _, hi⟩ := hEi i
  exact ⟨ha, hi⟩

end DeJongAlterations.StableModificationBridge.StableMarkedComponentTwist
