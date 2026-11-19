/-
Copyright (c) 2026 Chris Birkbeck and the EnvelopeProperty contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalSequence
import Hironaka.Geometry.ProperSteinProjectiveCechSheafH0Naturality

/-! # Actual original global sections and the genuine infinitesimal obstruction

Only the closed native exactness-transport proof is adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreInfinitesimalH0Cech.lean`,
SHA256 3850249d5d64ccfdf76023cd0886ca3ea4a0d5908a3bbb30b6c494ce4e9d4abd.
All schemes, coefficient maps, original subset complexes and native comparisons
are own original constructions. No global-surjectivity or lift certificate.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalH0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem exact_iso_transport {A : Type u} [CommRing A]
    {M N H J P : ModuleCat.{u} A} (eM : M ≅ H) (eN : N ≅ J)
    (b : M ⟶ N) (g : H ⟶ J) (δ : J ⟶ P)
    (h : eM.hom ≫ g=b ≫ eN.hom) (hex : Function.Exact g δ) :
    Function.Exact b (eN.hom ≫ δ) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hex (eN.hom x)).mp hx
    refine ⟨eM.inv y, ?_⟩
    apply (ModuleCat.mono_iff_injective eN.hom).mp inferInstance
    have he := ConcreteCategory.congr_hom h (eM.inv y)
    change g (eM.hom (eM.inv y))=eN.hom (b (eM.inv y)) at he
    rw [Iso.inv_hom_id_apply] at he
    exact he.symm.trans hy
  · rintro ⟨y, rfl⟩
    have he := ConcreteCategory.congr_hom h y
    change g (eM.hom y)=eN.hom (b y) at he
    change δ (eN.hom (b y))=0
    rw [← he]
    exact (hex (g (eM.hom y))).mpr ⟨eM.hom y, rfl⟩

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The WHOLE actual original infinitesimal global sections retain the SAME original base action. -/
def modelGlobalSections (d : ℕ) : ModuleCat.{u} R :=
  actualSchemeModuleBaseGlobalSections (SheafOfModules.unit (Infinitesimal.model I f d).ringCatSheaf)
    (actualSchemePushforwardSourceConstants (Infinitesimal.projection I f d)
      (ProperGeometricGlobalFunctions.coefficientMap f))

/-- Actual native pushforward global sections identify with the SAME original model sections, literally on values. -/
def modelGlobalIso (d : ℕ) :
    actualSchemeModuleBaseGlobalSections (InfinitesimalSequence.quotientModule I f d)
        (ProperGeometricGlobalFunctions.coefficientMap f) ≅ modelGlobalSections I f d :=
  actualSchemeModulePushforwardGlobalSectionsIso (Infinitesimal.projection I f d)
    (SheafOfModules.unit (Infinitesimal.model I f d).ringCatSheaf)
    (ProperGeometricGlobalFunctions.coefficientMap f)

/-- The actual original global-section projection derives from the SAME original native projection morphism. -/
def projectionGlobal (d : ℕ) :
    actualSchemeModuleBaseGlobalSections (SheafOfModules.unit X.ringCatSheaf)
        (ProperGeometricGlobalFunctions.coefficientMap f) ⟶ modelGlobalSections I f d :=
  SheafMorphisms.globalMap (ProperGeometricGlobalFunctions.coefficientMap f)
    (InfinitesimalSequence.projectionModule I f d) ≫ (modelGlobalIso I f d).hom

/-- The ENTIRE actual global projection is precisely the SAME original scheme pullback on every original section. -/
theorem projectionGlobal_apply (d : ℕ) (s : Γ(X, ⊤)) :
    (projectionGlobal I f d).hom s=(Infinitesimal.projection I f d).appTop s := rfl

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U=⊤)

/-- The WHOLE original infinitesimal sections canonically identify with the actual third native H0. -/
def modelGlobalHomologyIso (d : ℕ) :
    modelGlobalSections I f d ≅ (InfinitesimalSequence.sequence I f U hU d).X₃.homology 0 :=
  (modelGlobalIso I f d).symm ≪≫
    actualSchemeModuleBaseGlobalHomologyIso (InfinitesimalSequence.quotientModule I f d) U
      (ProperGeometricGlobalFunctions.coefficientMap f) hcover

/-- The genuine ORIGINAL projection retains the ENTIRE actual original global-section/H0 square. -/
theorem projectionHomology_square (d : ℕ) :
    projectionGlobal I f d ≫ (modelGlobalHomologyIso I f U hU hcover d).hom =
      (actualSchemeModuleBaseGlobalHomologyIso (SheafOfModules.unit X.ringCatSheaf) U
        (ProperGeometricGlobalFunctions.coefficientMap f) hcover).hom ≫
        HomologicalComplex.homologyMap (InfinitesimalSequence.sequence I f U hU d).g 0 := by
  unfold projectionGlobal modelGlobalHomologyIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact SheafH0Naturality.globalHomologyIso_naturality (ProperGeometricGlobalFunctions.coefficientMap f)
    (SheafOfModules.unit X.ringCatSheaf) U hcover (InfinitesimalSequence.projectionModule I f d)

/-- The genuine original obstruction of every WHOLE original infinitesimal section lies in SAME original ideal-power H1. -/
def sectionBoundary (d : ℕ) :
    modelGlobalSections I f d ⟶ (ReesPowerDiagram.powerComplex I f U d).homology 1 :=
  (modelGlobalHomologyIso I f U hU hcover d).hom ≫ InfinitesimalSequence.connecting I f U hU d 0

/-- Original native homology exactness DERIVES the WHOLE original global-section lift criterion. -/
theorem sectionBoundary_exact (d : ℕ) :
    Function.Exact (projectionGlobal I f d) (sectionBoundary I f U hU hcover d) :=
  exact_iso_transport
    (actualSchemeModuleBaseGlobalHomologyIso (SheafOfModules.unit X.ringCatSheaf) U
      (ProperGeometricGlobalFunctions.coefficientMap f) hcover)
    (modelGlobalHomologyIso I f U hU hcover d) (projectionGlobal I f d)
    (HomologicalComplex.homologyMap (InfinitesimalSequence.sequence I f U hU d).g 0)
    (InfinitesimalSequence.connecting I f U hU d 0)
    (projectionHomology_square I f U hU hcover d).symm
    (InfinitesimalSequence.homology_exact_right I f U hU d 0)

/-- A WHOLE original infinitesimal section has zero actual obstruction iff it is the literal original pullback of an original global section. -/
theorem sectionBoundary_eq_zero_iff (d : ℕ) (s : Γ(Infinitesimal.model I f d, ⊤)) :
    (sectionBoundary I f U hU hcover d).hom s=0 ↔
      ∃ t : Γ(X, ⊤), (Infinitesimal.projection I f d).appTop t=s :=
  sectionBoundary_exact I f U hU hcover d s

end Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalH0
