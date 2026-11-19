import Hironaka.Geometry.ProperSteinProjectiveCechSheafPushforward

/-! # Actual scheme isomorphisms retain entire original regular-section Cech diagrams -/
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X Y : Scheme.{u}} (e : X ≅ Y) {K : Type u} [CommRing K]
  (c : K →+* Γ(Y, ⊤))

/-- Actual whole original regular-section pullback is linear for the SAME original coefficient action. -/
def actualSchemeIsoRegularSectionIso (V : Y.Opens) :
    letI := localSectionsGlobalModule (SheafOfModules.unit Y.ringCatSheaf) V
    letI := localSectionsGlobalModule (SheafOfModules.unit X.ringCatSheaf) (e.hom ⁻¹ᵁ V)
    (ModuleCat.restrictScalars c).obj
        (ModuleCat.of Γ(Y, ⊤) (bundleSections (SheafOfModules.unit Y.ringCatSheaf) V)) ≅
      (ModuleCat.restrictScalars (actualSchemePushforwardSourceConstants e.hom c)).obj
        (ModuleCat.of Γ(X, ⊤)
          (bundleSections (SheafOfModules.unit X.ringCatSheaf) (e.hom ⁻¹ᵁ V))) := by
  letI := localSectionsGlobalModule (SheafOfModules.unit Y.ringCatSheaf) V
  letI := localSectionsGlobalModule (SheafOfModules.unit X.ringCatSheaf) (e.hom ⁻¹ᵁ V)
  let P := (ModuleCat.restrictScalars c).obj
    (ModuleCat.of Γ(Y, ⊤) (bundleSections (SheafOfModules.unit Y.ringCatSheaf) V))
  let Q := (ModuleCat.restrictScalars (actualSchemePushforwardSourceConstants e.hom c)).obj
    (ModuleCat.of Γ(X, ⊤)
      (bundleSections (SheafOfModules.unit X.ringCatSheaf) (e.hom ⁻¹ᵁ V)))
  let φ := (asIso (e.hom.app V)).commRingCatIsoToRingEquiv
  have E : P ≃ₗ[K] Q := {
    φ.toAddEquiv with
    map_smul' := by
      intro r s
      change e.hom.app V (Y.presheaf.map V.leTop.op (c r) * (show Γ(Y, V) from s)) =
        X.presheaf.map (e.hom ⁻¹ᵁ V).leTop.op
          (actualSchemePushforwardSourceConstants e.hom c r) *
            e.hom.app V (show Γ(Y, V) from s)
      rw [map_mul, actualSchemePushforwardStructuralScalar] }
  exact E.toModuleIso

variable {I : Type u} [LinearOrder I] (U : I → Y.Opens)

/-- Actual finite intersections give the SAME literal original pullback section comparison on every subset. -/
def actualSchemeIsoRegularSubsetIso (S : Finset I) :
    (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit Y.ringCatSheaf) U c).obj S ≅
      (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf)
        (fun j => e.hom ⁻¹ᵁ U j) (actualSchemePushforwardSourceConstants e.hom c)).obj S :=
  actualSchemeIsoRegularSectionIso e c (actualSchemeSubsetOpen U S) ≪≫
    (ModuleCat.restrictScalars (actualSchemePushforwardSourceConstants e.hom c)).mapIso
      (actualSchemeModuleOpenIso (SheafOfModules.unit X.ringCatSheaf)
        (actualSchemePushforwardSubsetOpen_eq e.hom U S))

/-- EVERY original pullback/restriction square gives an actual whole natural regular-section diagram isomorphism. -/
def actualSchemeIsoRegularDiagramIso :
    actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit Y.ringCatSheaf) U c ≅
      actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf)
        (fun j => e.hom ⁻¹ᵁ U j) (actualSchemePushforwardSourceConstants e.hom c) :=
  NatIso.ofComponents (actualSchemeIsoRegularSubsetIso e c U) (by
    intro S T hST
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change X.presheaf.map _ (e.hom.app _ (Y.presheaf.map _ s)) =
      X.presheaf.map _ (X.presheaf.map _ (e.hom.app _ s))
    have hnat := congrArg
      (fun q : Γ(Y, actualSchemeSubsetOpen U S) ⟶
        Γ(X, e.hom ⁻¹ᵁ actualSchemeSubsetOpen U T) => q s)
      (e.hom.naturality
        (homOfLE (actualSchemeSubsetOpen_antitone U (leOfHom hST))).op)
    simp only [ConcreteCategory.comp_apply] at hnat
    erw [hnat]
    simp only [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp, ← op_comp]
    rfl)

/-- Native normalized Cech functoriality transports the ENTIRE actual original complex. -/
def actualSchemeIsoRegularCechIso :
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit Y.ringCatSheaf) U c) ≅
      subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf)
        (fun j => e.hom ⁻¹ᵁ U j) (actualSchemePushforwardSourceConstants e.hom c)) :=
  (actualSubsetCechFunctor (K := K) (I := I)).mapIso (actualSchemeIsoRegularDiagramIso e c U)

end
end Hironaka.Geometry.ProperSteinProjectiveCech
