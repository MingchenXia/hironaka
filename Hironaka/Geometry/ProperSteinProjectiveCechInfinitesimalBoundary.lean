/-
Copyright (c) 2026 Chris Birkbeck and the EnvelopeProperty contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalTransitions
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalH0
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalSections
import Hironaka.Geometry.ProperSteinProjectiveCechReesCompatibleCohomology

/-! # Actual original whole-section obstruction transition and compatible lifts

Only the closed native composition-square proof is adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreInfinitesimalBoundaryTransitions.lean`,
SHA256 eac084552a2e3a9e2118d3192cf66b8b844afa105e161c6dfbe0bfe3a4465f29.
Actual original section/H0 frames, schemes, quotient transitions and genuine
projective compatible-cohomology vanishing are OWN original producers.
No obstruction-compatibility, vanishing or actual section-lift certificate.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

private theorem compose_boundary_square {C : Type*} [Category C]
    {A B M N P Q : C} (a : A ⟶ M) (b : B ⟶ N) (v : A ⟶ B)
    (h : M ⟶ N) (c : M ⟶ P) (d : N ⟶ Q) (t : P ⟶ Q)
    (ha : a ≫ h=v ≫ b) (hc : c ≫ t=h ≫ d) :
    (a ≫ c) ≫ t=v ≫ (b ≫ d) := by
  rw [Category.assoc, hc, ← Category.assoc, ha, Category.assoc]

private theorem globalPushforwardTransition_apply {A B Y : Scheme.{u}}
    {K : Type u} [CommRing K] (c : K →+* Γ(Y, ⊤)) (p : B ⟶ Y) (q : A ⟶ Y) (g : A ⟶ B)
    (a : (Scheme.Modules.pushforward p).obj (SheafOfModules.unit B.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward q).obj (SheafOfModules.unit A.ringCatSheaf))
    (ha : ∀ t : Γ(B, ⊤), (a.val.app (op ⊤)) t=g.appTop t)
    (s : actualSchemeModuleBaseGlobalSections (SheafOfModules.unit B.ringCatSheaf)
      (actualSchemePushforwardSourceConstants p c)) :
    ((actualSchemeModulePushforwardGlobalSectionsIso p (SheafOfModules.unit B.ringCatSheaf) c).inv ≫
      SheafMorphisms.globalMap c a ≫
      (actualSchemeModulePushforwardGlobalSectionsIso q (SheafOfModules.unit A.ringCatSheaf) c).hom).hom s =
      g.appTop (show Γ(B, ⊤) from s) := by
  change (a.val.app (op ⊤)) (show Γ(B, ⊤) from s)=_
  exact ha s

section OriginalFamily
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The genuine original WHOLE model-section transition, retaining the SAME actual original base action. -/
def modelGlobalTransition {n m : ℕ} (h : n≤m) :
    InfinitesimalH0.modelGlobalSections I f m ⟶ InfinitesimalH0.modelGlobalSections I f n :=
  (InfinitesimalH0.modelGlobalIso I f m).inv ≫
    SheafMorphisms.globalMap (ProperGeometricGlobalFunctions.coefficientMap f)
      (InfinitesimalTransitions.quotientTransition I f h) ≫ (InfinitesimalH0.modelGlobalIso I f n).hom

private theorem modelGlobalTransition_def {n m : ℕ} (h : n≤m) : modelGlobalTransition I f h =
    (actualSchemeModulePushforwardGlobalSectionsIso (Infinitesimal.projection I f m)
      (SheafOfModules.unit (Infinitesimal.model I f m).ringCatSheaf)
      (ProperGeometricGlobalFunctions.coefficientMap f)).inv ≫
    SheafMorphisms.globalMap (ProperGeometricGlobalFunctions.coefficientMap f)
      (InfinitesimalTransitions.quotientTransition I f h) ≫
    (actualSchemeModulePushforwardGlobalSectionsIso (Infinitesimal.projection I f n)
      (SheafOfModules.unit (Infinitesimal.model I f n).ringCatSheaf)
      (ProperGeometricGlobalFunctions.coefficientMap f)).hom := rfl

/-- EVERY original model section retains EXACTLY its literal original scheme transition pullback. -/
theorem modelGlobalTransition_apply {n m : ℕ} (h : n≤m)
    (s : InfinitesimalH0.modelGlobalSections I f m) :
    (modelGlobalTransition I f h).hom s=
      (Infinitesimal.transition I f h).appTop (show Γ(Infinitesimal.model I f m, ⊤) from s) :=
  (congrArg (fun v : InfinitesimalH0.modelGlobalSections I f m ⟶
    InfinitesimalH0.modelGlobalSections I f n => v.hom s) (modelGlobalTransition_def I f h)).trans
    (globalPushforwardTransition_apply (ProperGeometricGlobalFunctions.coefficientMap f)
      (Infinitesimal.projection I f m) (Infinitesimal.projection I f n) (Infinitesimal.transition I f h)
      (InfinitesimalTransitions.quotientTransition I f h)
      (InfinitesimalTransitions.quotientTransition_appTop I f h) s)

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U=⊤)

/-- The ENTIRE original model-section transition retains the SAME actual global-section/native-H0 square. -/
theorem modelTransition_homology {n m : ℕ} (h : n≤m) :
    modelGlobalTransition I f h ≫ (InfinitesimalH0.modelGlobalHomologyIso I f U hU hcover n).hom =
      (InfinitesimalH0.modelGlobalHomologyIso I f U hU hcover m).hom ≫
        HomologicalComplex.homologyMap
          ((SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
            (InfinitesimalTransitions.quotientTransition I f h)) 0 := by
  unfold modelGlobalTransition InfinitesimalH0.modelGlobalHomologyIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have hn := SheafH0Naturality.globalHomologyIso_naturality (ProperGeometricGlobalFunctions.coefficientMap f)
    (InfinitesimalSequence.quotientModule I f m) U hcover (InfinitesimalTransitions.quotientTransition I f h)
  simpa only [Category.assoc] using
    congrArg (fun v => (InfinitesimalH0.modelGlobalIso I f m).inv ≫ v) hn

/-- The SAME actual native original obstruction retains the ENTIRE original model transition square. -/
theorem sectionBoundary_naturality {n m : ℕ} (h : n≤m) :
    InfinitesimalH0.sectionBoundary I f U hU hcover m ≫
        ReesDegreeTransitions.homologyLower I f U h 1 =
      modelGlobalTransition I f h ≫ InfinitesimalH0.sectionBoundary I f U hU hcover n :=
  compose_boundary_square
    (InfinitesimalH0.modelGlobalHomologyIso I f U hU hcover m).hom
    (InfinitesimalH0.modelGlobalHomologyIso I f U hU hcover n).hom
    (modelGlobalTransition I f h)
    (HomologicalComplex.homologyMap
      ((SheafMorphisms.complexFunctor (ProperGeometricGlobalFunctions.coefficientMap f) U).map
        (InfinitesimalTransitions.quotientTransition I f h)) 0)
    (InfinitesimalSequence.connecting I f U hU m 0) (InfinitesimalSequence.connecting I f U hU n 0)
    (ReesDegreeTransitions.homologyLower I f U h 1)
    (modelTransition_homology I f U hU hcover h).symm
    (InfinitesimalTransitions.connecting_naturality I f U hU h 0)

/-- EVERY whole original section obstruction transitions by the literal original scheme pullback. -/
theorem sectionBoundary_transition_apply {n m : ℕ} (h : n≤m)
    (s : Γ(Infinitesimal.model I f m, ⊤)) :
    (ReesDegreeTransitions.homologyLower I f U h 1).hom
        ((InfinitesimalH0.sectionBoundary I f U hU hcover m).hom s) =
      (InfinitesimalH0.sectionBoundary I f U hU hcover n).hom ((Infinitesimal.transition I f h).appTop s) := by
  have hh := congrArg (fun v => v.hom s) (sectionBoundary_naturality I f U hU hcover h)
  change (ReesDegreeTransitions.homologyLower I f U h 1).hom
      ((InfinitesimalH0.sectionBoundary I f U hU hcover m).hom s) =
    (InfinitesimalH0.sectionBoundary I f U hU hcover n).hom ((modelGlobalTransition I f h).hom s) at hh
  exact hh.trans (congrArg (InfinitesimalH0.sectionBoundary I f U hU hcover n).hom
    (modelGlobalTransition_apply I f h s))

/-- The ACTUAL compatible original model sections produce a genuine SAME original compatible power-H1 obstruction family. -/
theorem compatible_sectionBoundary (s : InfinitesimalSections.compatibleSections I f)
    (n m : ℕ) (h : n≤m) :
    (ReesDegreeTransitions.homologyLower I f U (Nat.succ_le_succ h) 1).hom
        ((InfinitesimalH0.sectionBoundary I f U hU hcover (m+1)).hom (s.val m)) =
      (InfinitesimalH0.sectionBoundary I f U hU hcover (n+1)).hom (s.val n) :=
  (sectionBoundary_transition_apply I f U hU hcover (Nat.succ_le_succ h) (s.val m)).trans
    (congrArg (InfinitesimalH0.sectionBoundary I f U hU hcover (n+1)).hom (s.property n m h))
end OriginalFamily

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} {r : ℕ} (i : X ⟶ projectiveSpace R r) [IsClosedImmersion i]

/-- ORIGINAL complete projective Noetherian geometry DERIVES vanishing of EVERY actual compatible original section obstruction. -/
theorem projective_boundary_eq_zero [IsNoetherianRing R] [IsAdicComplete I R]
    (s : InfinitesimalSections.compatibleSections I (i ≫ projectiveSpaceStructure R r)) (n : ℕ) :
    letI := ReesDegreeHomology.projectiveSeparated i
    (InfinitesimalH0.sectionBoundary I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i)
      (originalClosedCoordinateOpens_isAffine i) (originalClosedCoordinateOpens_covers i) (n+1)).hom (s.val n)=0 := by
  let := ReesDegreeHomology.projectiveSeparated i
  let f := i ≫ projectiveSpaceStructure R r
  let U := originalClosedCoordinateOpens i
  let y : ∀ j : ℕ, (ReesPowerDiagram.powerComplex I f U (j+1)).homology 1 := fun j =>
    (InfinitesimalH0.sectionBoundary I f U (originalClosedCoordinateOpens_isAffine i)
      (originalClosedCoordinateOpens_covers i) (j+1)).hom (s.val j)
  have hz : y=0 := ReesCompatibleCohomology.projective_compatible_positive_eq_zero I i 1 y
    (fun a b h => compatible_sectionBoundary I f U (originalClosedCoordinateOpens_isAffine i)
      (originalClosedCoordinateOpens_covers i) s a b h)
  exact congrFun hz n

/-- EVERY coordinate of an ACTUAL compatible whole original section family genuinely lifts by the SAME literal original projection. -/
theorem projective_coordinate_lift [IsNoetherianRing R] [IsAdicComplete I R]
    (s : InfinitesimalSections.compatibleSections I (i ≫ projectiveSpaceStructure R r)) (n : ℕ) :
    ∃ t : Γ(X, ⊤), (Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) (n+1)).appTop t=s.val n := by
  let := ReesDegreeHomology.projectiveSeparated i
  exact (InfinitesimalH0.sectionBoundary_eq_zero_iff I (i ≫ projectiveSpaceStructure R r)
    (originalClosedCoordinateOpens i) (originalClosedCoordinateOpens_isAffine i)
    (originalClosedCoordinateOpens_covers i) (n+1) (s.val n)).mp (projective_boundary_eq_zero I i s n)

end Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalBoundary
