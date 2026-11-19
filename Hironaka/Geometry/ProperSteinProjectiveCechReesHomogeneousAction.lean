/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesHomogeneousComplexFrames
import Hironaka.Geometry.ProperSteinProjectiveCechDirectSumDegreeInclusions
import Hironaka.Geometry.ProperSteinProjectiveCechReesDegreeHomology
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # The actual original Rees action on EVERY original cohomology class

Closed native comparison proof adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechHomogeneousAction.lean`,
SHA256 14d780e16f281d917cdfc09f3fa699b2b10a8d6457bf14cf79b0717369e1bd6b.
All maps here are SAME original native subset/section maps and the ACTUAL
original Rees coefficient action. No geometric action output is assumed.
-/
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesHomogeneousAction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- Actual coefficient restriction preserves the SAME original scalar on ENTIRE original cochains. -/
theorem scalarRestriction_homogeneous (p : reesAlgebra I) :
    (ReesDegreeComplex.originalScalarComplexIso I f U).inv ≫
      ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)).map
        (p • 𝟙 (subsetCechComplex (ReesInverseImageDiagram.baseDiagram I f U))) ≫
      (ReesDegreeComplex.originalScalarComplexIso I f U).hom =
    ReesHomogeneousComplexFrames.scalarComplex I f U p := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

variable [X.IsSeparated] [Fintype ι] (hU : ∀ j, IsAffineOpen (U j))
include hU

/-- The SAME actual scalar conjugated through the ENTIRE original degree-complex frame. -/
def gradedHomogeneous {e : ℕ} (a : ↥(I^e)) :
    SubsetDirectSum.complexSum (fun d => ReesPowerDiagram.powerComplex I f U d) ⟶
      SubsetDirectSum.complexSum (fun d => ReesPowerDiagram.powerComplex I f U d) :=
  (ReesDegreeComplex.inverseImageDegreeComplexIso I f U hU).inv ≫
    ReesHomogeneousComplexFrames.scalarComplex I f U (ReesMultiplication.monomial I e a) ≫
    (ReesDegreeComplex.inverseImageDegreeComplexIso I f U hU).hom

/-- EVERY original cochain summand has its exact ORIGINAL homogeneous multiplication and original degree shift. -/
theorem degreeInclusion_homogeneous {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    DirectSumDegreeInclusions.complexInclusion (fun j => ReesPowerDiagram.powerComplex I f U j) d ≫
      gradedHomogeneous I f U hU a =
    ReesPowerDiagram.homogeneousComplexMap I f U a d ≫
      DirectSumDegreeInclusions.complexInclusion (fun j => ReesPowerDiagram.powerComplex I f U j) (e+d) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ReesHomogeneousComplexFrames.term_homogeneous I f U hU a d n x

omit [LinearOrder ι] [X.IsSeparated] [Fintype ι] hU in
private theorem comparison_comp {C : Type*} [Category C]
    {A B D E G : C} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ E} {d : E ⟶ D}
    {t : D ⟶ G} {z : E ⟶ G} (h : a ≫ b = c ≫ d) (hz : d ≫ t=z) :
    a ≫ b ≫ t = c ≫ z := by
  rw [← Category.assoc, h, Category.assoc, hz]

/-- Native homology retains EVERY original homogeneous multiplication map and literal degree summand. -/
theorem homologyInclusion_homogeneous {e : ℕ} (a : ↥(I^e)) (d n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (DirectSumDegreeInclusions.complexInclusion (fun j => ReesPowerDiagram.powerComplex I f U j) d) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (gradedHomogeneous I f U hU a) ≫
      (SubsetDirectSum.complexSumHomologyIso (fun j => ReesPowerDiagram.powerComplex I f U j) n).hom =
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (ReesPowerDiagram.homogeneousComplexMap I f U a d) ≫
      ModuleCat.ofHom (DirectSum.lof R ℕ
        (fun j => (ReesPowerDiagram.powerComplex I f U j).homology n) (e+d)) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n
  have h := congrArg (fun b => H.map b) (degreeInclusion_homogeneous I f U hU a d)
  have h' := (H.map_comp _ _).symm.trans (h.trans (H.map_comp _ _))
  exact comparison_comp h'
    (DirectSumDegreeInclusions.homologyInclusion (fun j => ReesPowerDiagram.powerComplex I f U j) (e+d) n)

omit [LinearOrder ι] [X.IsSeparated] [Fintype ι] hU in
private instance homologyFunctor_linear (S : Type u) [CommRing S] (n : ℕ) :
    Functor.Linear S (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (.up ℕ) n) where
  map_smul φ a := by
    have h :
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map (a • φ) =
          a • (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map φ := by
      apply ShortComplex.Hom.ext <;> rfl
    change ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map (a • φ)) =
      a • ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map φ)
    rw [h]
    exact ShortComplex.homologyMap_smul _ a

omit [LinearOrder ι] [X.IsSeparated] [Fintype ι] hU in
private theorem conjugate_scalar {S C D : Type*} [CommRing S]
    [Category C] [Preadditive C] [CategoryTheory.Linear S C] [Category D]
    (F : C ⥤ D) {A B : C} {E : D} (e : A ≅ B) (t : F.obj B ≅ E) (a : S) :
    (F.mapIso e ≪≫ t).inv ≫ F.map (a • 𝟙 A) ≫ (F.mapIso e ≪≫ t).hom =
      t.inv ≫ F.map (a • 𝟙 B) ≫ t.hom := by
  have h : e.inv ≫ (a • 𝟙 A) ≫ e.hom = a • 𝟙 B := by simp
  calc
    _ = t.inv ≫ F.map (e.inv ≫ (a • 𝟙 A) ≫ e.hom) ≫ t.hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Functor.map_comp, Category.assoc]
    _ = _ := by rw [h]

/-- The SAME native original-family scalar becomes the actual original homogeneous cochain action. -/
theorem native_homogeneous {e : ℕ} (a : ↥(I^e)) :
    (ReesDegreeComplex.nativeOriginalDegreeComplexIso I f U hU).inv ≫
      ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)).map
        (ReesMultiplication.monomial I e a • 𝟙 (ReesDegreeHomology.nativeComplex I f U)) ≫
      (ReesDegreeComplex.nativeOriginalDegreeComplexIso I f U hU).hom =
    gradedHomogeneous I f U hU a := by
  let F := (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)
  change (F.mapIso (ReesInverseImageDiagram.nativeComplexIso I f U).symm ≪≫
      ReesDegreeComplex.originalDegreeComplexIso I f U hU).inv ≫ _ ≫
      (F.mapIso (ReesInverseImageDiagram.nativeComplexIso I f U).symm ≪≫
      ReesDegreeComplex.originalDegreeComplexIso I f U hU).hom = _
  calc
    _ = (ReesDegreeComplex.originalDegreeComplexIso I f U hU).inv ≫
        F.map (ReesMultiplication.monomial I e a •
          𝟙 (subsetCechComplex (ReesInverseImageDiagram.baseDiagram I f U))) ≫
        (ReesDegreeComplex.originalDegreeComplexIso I f U hU).hom :=
      conjugate_scalar F (ReesInverseImageDiagram.nativeComplexIso I f U).symm
        (ReesDegreeComplex.originalDegreeComplexIso I f U hU) (ReesMultiplication.monomial I e a)
    _ = (ReesDegreeComplex.inverseImageDegreeComplexIso I f U hU).inv ≫
        ((ReesDegreeComplex.originalScalarComplexIso I f U).inv ≫
          F.map (ReesMultiplication.monomial I e a •
            𝟙 (subsetCechComplex (ReesInverseImageDiagram.baseDiagram I f U))) ≫
          (ReesDegreeComplex.originalScalarComplexIso I f U).hom) ≫
        (ReesDegreeComplex.inverseImageDegreeComplexIso I f U hU).hom := by
      simp only [ReesDegreeComplex.originalDegreeComplexIso, Iso.trans_inv, Iso.trans_hom,
        Category.assoc]
    _ = _ := congrArg
      (fun b => (ReesDegreeComplex.inverseImageDegreeComplexIso I f U hU).inv ≫ b ≫
        (ReesDegreeComplex.inverseImageDegreeComplexIso I f U hU).hom)
      (scalarRestriction_homogeneous I f U (ReesMultiplication.monomial I e a))

/-- The WHOLE original native homology comparison before the actual original direct-sum splitting. -/
def originalHomologyIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        ((ReesDegreeHomology.nativeComplex I f U).homology n) ≅
      (SubsetDirectSum.complexSum (fun d => ReesPowerDiagram.powerComplex I f U d)).homology n :=
  (ReesDegreeHomology.scalarHomologyIso I f U n).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).mapIso
      (ReesDegreeComplex.nativeOriginalDegreeComplexIso I f U hU)

omit [LinearOrder ι] [X.IsSeparated] [Fintype ι] hU in
private theorem intertwine_conjugate {C : Type*} [Category C]
    {A B : C} (e : A ≅ B) {a : A ⟶ A} {b : B ⟶ B}
    (h : e.inv ≫ a ≫ e.hom=b) : a ≫ e.hom=e.hom ≫ b := by
  rw [← h, Iso.hom_inv_id_assoc]

omit [LinearOrder ι] [X.IsSeparated] [Fintype ι] hU in
private theorem square_comp {C : Type*} [Category C]
    {A B D : C} {a : A ⟶ A} {b : B ⟶ B} {d : D ⟶ D}
    {s : A ⟶ B} {t : B ⟶ D} (hs : a ≫ s=s ≫ b) (ht : b ≫ t=t ≫ d) :
    a ≫ (s ≫ t)=(s ≫ t) ≫ d := by
  rw [← Category.assoc, hs, Category.assoc, ht, Category.assoc]

/-- The actual WHOLE native original homology comparison retains the SAME original coefficient action. -/
theorem originalHomologyIso_homogeneous {e : ℕ} (a : ↥(I^e)) (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).map
        (ReesMultiplication.monomial I e a • 𝟙 ((ReesDegreeHomology.nativeComplex I f U).homology n)) ≫
        (originalHomologyIso I f U hU n).hom =
      (originalHomologyIso I f U hU n).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
          (gradedHomogeneous I f U hU a) := by
  let F := ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))
  let C := ReesDegreeHomology.nativeComplex I f U
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n
  let HQ := HomologicalComplex.homologyFunctor (ModuleCat.{u} (reesAlgebra I)) (.up ℕ) n
  let μ : C ⟶ C := ReesMultiplication.monomial I e a • 𝟙 C
  have hs : F.map (ReesMultiplication.monomial I e a • 𝟙 (C.homology n)) ≫
      (ReesDegreeHomology.scalarHomologyIso I f U n).inv =
    (ReesDegreeHomology.scalarHomologyIso I f U n).inv ≫
      H.map ((F.mapHomologicalComplex (.up ℕ)).map μ) := by
    have h := ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map μ) F
    change F.map (HQ.map μ) ≫ _ = _ at h
    have hμ : HQ.map μ=ReesMultiplication.monomial I e a • 𝟙 (C.homology n) :=
      (HQ.map_smul (ReesMultiplication.monomial I e a) (𝟙 C)).trans
        (congrArg (fun b => ReesMultiplication.monomial I e a • b) (HQ.map_id C))
    have h0 : F.map (HQ.map μ) ≫
        (ReesDegreeHomology.scalarHomologyIso I f U n).inv =
      (ReesDegreeHomology.scalarHomologyIso I f U n).inv ≫
        H.map ((F.mapHomologicalComplex (.up ℕ)).map μ) := h
    exact (congrArg (fun b => F.map b ≫
      (ReesDegreeHomology.scalarHomologyIso I f U n).inv) hμ).symm.trans h0
  have hc := intertwine_conjugate (ReesDegreeComplex.nativeOriginalDegreeComplexIso I f U hU)
    (native_homogeneous I f U hU a)
  have ht := congrArg (fun b => H.map b) hc
  have ht' := (H.map_comp _ _).symm.trans (ht.trans (H.map_comp _ _))
  exact square_comp hs ht'

/-- The ACTUAL finite original Rees action has the EXACT original homogeneous formula on EVERY original class. -/
theorem reesModule_homogeneous {e : ℕ} (a : ↥(I^e)) (d n : ℕ)
    (x : (ReesPowerDiagram.powerComplex I f U d).homology n) :
    letI := ReesDegreeHomology.reesModule I f U hU n
    ReesMultiplication.monomial I e a •
        DirectSum.lof R ℕ (fun j => (ReesPowerDiagram.powerComplex I f U j).homology n) d x =
      DirectSum.lof R ℕ (fun j => (ReesPowerDiagram.powerComplex I f U j).homology n) (e+d)
        (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
          (ReesPowerDiagram.homogeneousComplexMap I f U a d)).hom x) := by
  let := ReesDegreeHomology.reesModule I f U hU n
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n
  let E := ReesDegreeHomology.homologyEquiv I f U hU n
  let P := (originalHomologyIso I f U hU n).toLinearEquiv
  let Q := (SubsetDirectSum.complexSumHomologyIso (fun j => ReesPowerDiagram.powerComplex I f U j) n).toLinearEquiv
  let u : (SubsetDirectSum.complexSum (fun j => ReesPowerDiagram.powerComplex I f U j)).homology n :=
    (H.map (DirectSumDegreeInclusions.complexInclusion (fun j => ReesPowerDiagram.powerComplex I f U j) d)).hom x
  have he (y) : E y=Q (P y) := rfl
  have hu : Q u=DirectSum.lof R ℕ (fun j => (ReesPowerDiagram.powerComplex I f U j).homology n) d x :=
    congrArg (fun b => b.hom x)
      (DirectSumDegreeInclusions.homologyInclusion (fun j => ReesPowerDiagram.powerComplex I f U j) d n)
  have hi : E.symm
      (DirectSum.lof R ℕ (fun j => (ReesPowerDiagram.powerComplex I f U j).homology n) d x)=P.symm u := by
    apply E.injective
    rw [E.apply_symm_apply, he, P.apply_symm_apply]
    exact hu.symm
  have hs : P (ReesMultiplication.monomial I e a • P.symm u)=
      (H.map (gradedHomogeneous I f U hU a)).hom u := by
    have h := congrArg (fun b => b.hom (P.symm u))
      (originalHomologyIso_homogeneous I f U hU a n)
    change P (ReesMultiplication.monomial I e a • P.symm u)=
      (H.map (gradedHomogeneous I f U hU a)).hom (P (P.symm u)) at h
    simpa only [P.apply_symm_apply] using h
  have ht := congrArg (fun b => b.hom x)
    (homologyInclusion_homogeneous I f U hU a d n)
  rw [ReesDegreeHomology.reesModule_smul]
  change E (ReesMultiplication.monomial I e a • E.symm
    (DirectSum.lof R ℕ (fun j => (ReesPowerDiagram.powerComplex I f U j).homology n) d x)) = _
  rw [hi, he, hs]
  exact ht

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesHomogeneousAction
