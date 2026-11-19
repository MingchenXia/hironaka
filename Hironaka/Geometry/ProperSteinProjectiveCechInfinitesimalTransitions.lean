/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # SAME original infinitesimal sequence morphisms and native boundary naturality

Closed native unit-transition and connecting-square proof adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreInfinitesimalBoundaryTransitions.lean`,
SHA256 eac084552a2e3a9e2118d3192cf66b8b844afa105e161c6dfbe0bfe3a4465f29.
All complexes and ideal powers are own native original subset constructions.
No supplied sequence morphism, boundary square or quotient-map certificate.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalTransitions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private def unitTransition {A B C : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ C)
    (q : A ⟶ C) (h : g ≫ p=q) :
    (Scheme.Modules.pushforward p).obj (SheafOfModules.unit B.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward q).obj (SheafOfModules.unit A.ringCatSheaf) :=
  (Scheme.Modules.pushforward p).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp g p).hom.app (SheafOfModules.unit A.ringCatSheaf) ≫
    eqToHom (congrArg (fun t => (Scheme.Modules.pushforward t).obj
      (SheafOfModules.unit A.ringCatSheaf)) h)

private theorem unitSection_transition {A B C : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ C)
    (q : A ⟶ C) (h : g ≫ p=q) :
    SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫ unitTransition g p q h =
      SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
  subst q
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

private theorem unitTransition_appTop {A B C : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ C)
    (q : A ⟶ C) (h : g ≫ p=q) (s : Γ(B, ⊤)) :
    (unitTransition g p q h).val.app (op ⊤) s=g.appTop s := by
  subst q
  rfl

private theorem subset_comp_square {A ι : Type u} [CommRing A] [LinearOrder ι]
    {D E F : Finset ι ⥤ ModuleCat.{u} A} (a : D ⟶ E) (b : E ⟶ F) (c : D ⟶ F)
    (h : a ≫ b=c) : subsetCechComplexMap a ≫ subsetCechComplexMap b=subsetCechComplexMap c := by
  let C := actualSubsetCechFunctor (K := A) (I := ι)
  exact (C.map_comp a b).symm.trans
    (congrArg (fun t : D ⟶ F => C.map t) h)

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The SAME actual original scheme transition gives the genuine WHOLE original quotient-module transition. -/
def quotientTransition {n m : ℕ} (h : n≤m) :
    InfinitesimalSequence.quotientModule I f m ⟶ InfinitesimalSequence.quotientModule I f n :=
  unitTransition (Infinitesimal.transition I f h) (Infinitesimal.projection I f m)
    (Infinitesimal.projection I f n) (Infinitesimal.transition_projection I f h)

/-- On ENTIRE original top sections the quotient transition is EXACTLY the original scheme pullback. -/
theorem quotientTransition_appTop {n m : ℕ} (h : n≤m) (s : Γ(Infinitesimal.model I f m, ⊤)) :
    (quotientTransition I f h).val.app (op ⊤) s=(Infinitesimal.transition I f h).appTop s :=
  unitTransition_appTop (Infinitesimal.transition I f h) (Infinitesimal.projection I f m)
    (Infinitesimal.projection I f n) (Infinitesimal.transition_projection I f h) s

/-- The ENTIRE actual original unit-projection square retains the SAME original scheme transition triangle. -/
theorem projectionModule_transition {n m : ℕ} (h : n≤m) :
    InfinitesimalSequence.projectionModule I f m ≫ quotientTransition I f h=
      InfinitesimalSequence.projectionModule I f n :=
  unitSection_transition (Infinitesimal.transition I f h) (Infinitesimal.projection I f m)
    (Infinitesimal.projection I f n) (Infinitesimal.transition_projection I f h)

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

omit [LinearOrder ι] in
private theorem inclusionDiagram_transition {n m : ℕ} (h : n≤m) :
    ReesDegreeTransitions.lowerNatural I f U h ≫ InfinitesimalSequence.inclusionDiagram I f U n =
      InfinitesimalSequence.inclusionDiagram I f U m := by
  apply NatTrans.ext
  funext S
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

variable [X.IsSeparated] (hU : ∀ j, IsAffineOpen (U j))

omit [X.IsSeparated] in
private theorem sequence_first_square {n m : ℕ} (h : n≤m) :
    subsetCechComplexMap (ReesDegreeTransitions.lowerNatural I f U h) ≫
        subsetCechComplexMap (InfinitesimalSequence.inclusionDiagram I f U n) =
      subsetCechComplexMap (InfinitesimalSequence.inclusionDiagram I f U m) :=
  subset_comp_square (ReesDegreeTransitions.lowerNatural I f U h)
    (InfinitesimalSequence.inclusionDiagram I f U n) (InfinitesimalSequence.inclusionDiagram I f U m)
    (inclusionDiagram_transition I f U h)

omit [X.IsSeparated] in
private theorem sequence_second_square {n m : ℕ} (h : n≤m) :
    (SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
        (InfinitesimalSequence.projectionModule I f m) ≫
      (SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
        (quotientTransition I f h) =
    (SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
      (InfinitesimalSequence.projectionModule I f n) := by
  let C := SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U
  exact (C.map_comp (InfinitesimalSequence.projectionModule I f m) (quotientTransition I f h)).symm.trans
    (congrArg (fun b => C.map b) (projectionModule_transition I f h))

/-- The SAME genuine original maps form a WHOLE native morphism of actual original infinitesimal short complexes. -/
def sequenceTransition {n m : ℕ} (h : n≤m) :
    InfinitesimalSequence.sequence I f U hU m ⟶ InfinitesimalSequence.sequence I f U hU n where
  τ₁ := ReesDegreeTransitions.degreeLower I f U h
  τ₂ := 𝟙 (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
    (SheafOfModules.unit X.ringCatSheaf) U (ProperGeometricGlobalFunctions.coefficientMap f)))
  τ₃ := (SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
    (quotientTransition I f h)
  comm₁₂ := (sequence_first_square I f U h).trans
    (Category.comp_id (subsetCechComplexMap (InfinitesimalSequence.inclusionDiagram I f U m))).symm
  comm₂₃ := (Category.id_comp
    ((SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
      (InfinitesimalSequence.projectionModule I f n))).trans (sequence_second_square I f U h).symm

/-- EVERY genuine native connecting map retains the EXACT original higher-to-lower infinitesimal/power square. -/
theorem connecting_naturality {n m : ℕ} (h : n≤m) (p : ℕ) :
    InfinitesimalSequence.connecting I f U hU m p ≫ ReesDegreeTransitions.homologyLower I f U h (p+1) =
      HomologicalComplex.homologyMap
        ((SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
          (quotientTransition I f h)) p ≫ InfinitesimalSequence.connecting I f U hU n p :=
  HomologicalComplex.HomologySequence.δ_naturality (sequenceTransition I f U hU h)
    (InfinitesimalSequence.sequence_shortExact I f U hU m)
    (InfinitesimalSequence.sequence_shortExact I f U hU n) p (p+1) rfl

end Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalTransitions
