/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedComponentTwist
import DeJongAlterations.Geometry.CanonicalComponentDegreeMinimal
import DeJongAlterations.Geometry.LineBundleNativePullback

/-! Genuine actual marked dualizing degree on SAME canonical normalization and
original coefficient action, with all exactness inputs internally produced.
Blueprint: `stable-marked-component-degree.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableMarkedComponentDegree
open StableModification StableModification.Projectivity Cohomology CurvesField CurvesField.Genus
open Omega.ComponentDegree Omega.ComponentNormalization Omega.RosenlichtComponent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [DeJong.IsNodalCurve f] [IsProper f]
  [IsIntegral S] [IsLocallyNoetherian S] (D : X.IdealSheafData)
  {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
  [CompactSpace (pullback (C := Scheme.{u}) f a)]
  [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))]
  (η : pullback (C := Scheme.{u}) f a)
  (hη : η ∈ genericPoints (pullback (C := Scheme.{u}) f a))
  (hN : IsProjectiveOver (componentStructure f a η))
  (hS : IsNormalScheme S)
  (hgen : ∀ x : X, f x = genericPoint S → DeJong.IsSmoothAt f x)
  (hD : DeJong.IsSemistablePair f D) (E : LocalEquations X)
  (hEi : ∀ i, ∃ h : IsAffineOpen (E.U i), D.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i})
  (hEs : ∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D.support : Set X))

include hη hN hS hgen hD hEi hEs

/-- The ORIGINAL semistable pair INTERNALLY supplies every native marking map,
finite mark set and local length-one input of the genuine minimal degree theorem. -/
theorem exists_marked_component_degree :
    ∃ P M : Finset (componentNormalization f a η),
      (∀ y, y ∈ P ↔ componentMap f a η y ∉ f.smoothLocus) ∧
      (∀ y, y ∈ M ↔ componentMap f a η y ∈ (D.support : Set X)) ∧
      (∀ y ∈ P, IsClosed ({y} : Set (componentNormalization f a η))) ∧
      (∀ y ∈ M, IsClosed ({y} : Set (componentNormalization f a η))) ∧
      (∀ i, FiniteDimensional K (cohomology ((Scheme.Modules.pullback (componentMap f a η)).obj
        (E.toLineBundleData.twist (Omega.dualizingSheaf f) 1))
        (structureCoeff (componentStructure f a η)) i)) ∧
      DualityScheme.eulerCharOf ((Scheme.Modules.pullback (componentMap f a η)).obj
          (E.toLineBundleData.twist (Omega.dualizingSheaf f) 1))
          (structureCoeff (componentStructure f a η)) -
        eulerChar (componentNormalization f a η) (structureCoeff (componentStructure f a η)) =
        2 * componentGenus (structureCoeff (pullback.snd f a)) η - 2 + P.card + M.card := by
  have hω := Omega.isInvertibleModule_dualizingSheaf_of_isNodalCurve f hS hgen
  let : (Omega.dualizingSheaf f).IsQuasicoherent := isQuasicoherent_of_isInvertibleModule _ hω
  obtain ⟨d⟩ := StableMarkedComponentTwist.exists_markedComponentTwistData
    f D a η hS hgen hD E hEi hEs hη
  obtain ⟨P, hP, hPc, hfd, hdeg⟩ := Omega.ComponentDegreeMinimal.degree_twist_component
    f a hη hN hS hgen
    (StableMarkedNativePullback.pullbackMarkedTwistMap E (Omega.dualizingSheaf f)
      (componentMap f a η)) d.marks d.marks_closed
    (fun W _ => d.injective W) (fun W _ => d.surjective W) d.local_cokernel
  exact ⟨P, d.marks, hP, d.marks_mem, hPc, d.marks_closed, hfd, hdeg⟩

/-- The SAME original LBD pullback has the SAME native K Euler degree, through
an actual native pulled module iso, with no caller degree or Euler comparison. -/
theorem exists_lineBundle_component_degree (L : LineBundleData X)
    (e : L.twist (unitModule X) 1 ≅ E.toLineBundleData.twist (Omega.dualizingSheaf f) 1) :
    ∃ P M : Finset (componentNormalization f a η),
      (∀ y, y ∈ P ↔ componentMap f a η y ∉ f.smoothLocus) ∧
      (∀ y, y ∈ M ↔ componentMap f a η y ∈ (D.support : Set X)) ∧
      DualityScheme.eulerCharOf ((L.pullback (componentMap f a η)).twist
          (unitModule (componentNormalization f a η)) 1)
          (structureCoeff (componentStructure f a η)) -
        eulerChar (componentNormalization f a η) (structureCoeff (componentStructure f a η)) =
        2 * componentGenus (structureCoeff (pullback.snd f a)) η - 2 + P.card + M.card := by
  obtain ⟨P, M, hP, hM, _, _, _, hdeg⟩ :=
    exists_marked_component_degree f D a η hη hN hS hgen hD E hEi hEs
  let e' := (L.nativePullbackTwistIso 1 (componentMap f a η)).symm ≪≫
    (Scheme.Modules.pullback (componentMap f a η)).mapIso e
  refine ⟨P, M, hP, hM, ?_⟩
  rw [Cohomology.eulerCharOf_eq_of_iso e']
  exact hdeg

end DeJongAlterations.StableModificationBridge.StableMarkedComponentDegree
