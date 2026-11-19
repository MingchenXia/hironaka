import Hironaka.Geometry.ProperSteinProjectiveCechSheafSections

/-!
# Actual ORIGINAL native pushforward and inverse-image section diagrams

Adapted from the generic native portion of same-workspace
`BingWangEntropy/SchemeModulePushforwardCech.lean`,
SHA256 e95b929611f75e624503b6369e0ce468e14de1152fbec36fcd50f046e158ae4d.
All native pushforward sections and restrictions are literal originals.
Only Mathlib and owned Hironaka modules are imported.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace Hironaka.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{u}} (i : X ⟶ Y) (L : X.Modules)
  {K : Type u} [CommRing K] (c : K →+* Γ(Y, ⊤))

/-- The actual inverse-image top-section homomorphism gives the true source structural constants. -/
def actualSchemePushforwardSourceConstants : K →+* Γ(X, ⊤) :=
  i.appTop.hom.comp c

/-- Native naturality identifies actual ambient and source structural scalars on every genuine open. -/
theorem actualSchemePushforwardStructuralScalar (V : Y.Opens) (r : K) :
    i.app V (Y.presheaf.map V.leTop.op (c r)) =
      X.presheaf.map (i ⁻¹ᵁ V).leTop.op (actualSchemePushforwardSourceConstants i c r) := by
  have hh := congrArg (fun f : Γ(Y, ⊤) ⟶ Γ(X, i ⁻¹ᵁ V) => f (c r))
    (i.naturality V.leTop.op)
  exact hh

/-- Literal actual pushforward sections identify linearly with literal inverse-image sections. -/
def actualSchemeModulePushforwardSectionIso (V : Y.Opens) :
    letI := localSectionsGlobalModule ((Scheme.Modules.pushforward i).obj L) V
    letI := localSectionsGlobalModule L (i ⁻¹ᵁ V)
    (ModuleCat.restrictScalars c).obj
        (ModuleCat.of Γ(Y, ⊤) (bundleSections ((Scheme.Modules.pushforward i).obj L) V)) ≅
      (ModuleCat.restrictScalars (actualSchemePushforwardSourceConstants i c)).obj
        (ModuleCat.of Γ(X, ⊤) (bundleSections L (i ⁻¹ᵁ V))) := by
  letI := localSectionsGlobalModule ((Scheme.Modules.pushforward i).obj L) V
  letI := localSectionsGlobalModule L (i ⁻¹ᵁ V)
  let P : ModuleCat.{u} K := (ModuleCat.restrictScalars c).obj
    (ModuleCat.of Γ(Y, ⊤) (bundleSections ((Scheme.Modules.pushforward i).obj L) V))
  let Q : ModuleCat.{u} K := (ModuleCat.restrictScalars (actualSchemePushforwardSourceConstants i c)).obj
    (ModuleCat.of Γ(X, ⊤) (bundleSections L (i ⁻¹ᵁ V)))
  have e : P ≃ₗ[K] Q := {
    toFun := fun s => s
    invFun := fun s => s
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r s
      change i.app V (Y.presheaf.map V.leTop.op (c r)) • (show bundleSections L (i ⁻¹ᵁ V) from s) =
        X.presheaf.map (i ⁻¹ᵁ V).leTop.op (actualSchemePushforwardSourceConstants i c r) •
          (show bundleSections L (i ⁻¹ᵁ V) from s)
      rw [actualSchemePushforwardStructuralScalar] }
  exact e.toModuleIso

/-- Actual finite open intersections commute with the true inverse-image functor. -/
theorem actualSchemePushforwardSubsetOpen_eq {I : Type u} [LinearOrder I]
    (U : I → Y.Opens) (S : Finset I) :
    i ⁻¹ᵁ (actualSchemeSubsetOpen U S) =
      actualSchemeSubsetOpen (fun j => i ⁻¹ᵁ U j) S := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert j S hj ih =>
      simp only [actualSchemeSubsetOpen, Finset.inf_insert]
      change (i ⁻¹ᵁ U j) ⊓ (i ⁻¹ᵁ S.inf U) =
        (i ⁻¹ᵁ U j) ⊓ S.inf (fun j => i ⁻¹ᵁ U j)
      exact congrArg (fun V => (i ⁻¹ᵁ U j) ⊓ V) ih

variable {I : Type u} [LinearOrder I] (U : I → Y.Opens)

/-- Actual pushforward sections on a subset intersection identify with actual pullback-intersection sections. -/
def actualSchemeModulePushforwardSubsetIso (S : Finset I) :
    (actualSchemeModuleBaseSubsetDiagram ((Scheme.Modules.pushforward i).obj L) U c).obj S ≅
      (actualSchemeModuleBaseSubsetDiagram L (fun j => i ⁻¹ᵁ U j)
        (actualSchemePushforwardSourceConstants i c)).obj S :=
  actualSchemeModulePushforwardSectionIso i L c (actualSchemeSubsetOpen U S) ≪≫
    (ModuleCat.restrictScalars (actualSchemePushforwardSourceConstants i c)).mapIso
      (actualSchemeModuleOpenIso L (actualSchemePushforwardSubsetOpen_eq i U S))

/-- The true native pushforward and pullback-open section diagrams are genuinely naturally isomorphic. -/
def actualSchemeModulePushforwardSubsetDiagramIso :
    actualSchemeModuleBaseSubsetDiagram ((Scheme.Modules.pushforward i).obj L) U c ≅
      actualSchemeModuleBaseSubsetDiagram L (fun j => i ⁻¹ᵁ U j)
        (actualSchemePushforwardSourceConstants i c) :=
  NatIso.ofComponents (actualSchemeModulePushforwardSubsetIso i L c U) (by
    intro S T hST
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change L.presheaf.map _ (L.presheaf.map _ s) = L.presheaf.map _ (L.presheaf.map _ s)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl)

/-- The literal section-diagram comparison induces a genuine native Čech-complex isomorphism. -/
def actualSchemeModulePushforwardCechIso :
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram ((Scheme.Modules.pushforward i).obj L) U c) ≅
      subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L (fun j => i ⁻¹ᵁ U j)
        (actualSchemePushforwardSourceConstants i c)) := by
  let e := actualSchemeModulePushforwardSubsetDiagramIso i L c U
  refine {
    hom := subsetCechComplexMap e.hom
    inv := subsetCechComplexMap e.inv
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext S
    exact (e.app S).toLinearEquiv.symm_apply_apply (a.val S)
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext S
    exact (e.app S).toLinearEquiv.apply_symm_apply (a.val S)

/-- True native Čech cohomology agrees under the actual pushforward section comparison. -/
def actualSchemeModulePushforwardHomologyIso (p : ℕ) :
    (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram ((Scheme.Modules.pushforward i).obj L) U c)).homology p ≅
      (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L (fun j => i ⁻¹ᵁ U j)
        (actualSchemePushforwardSourceConstants i c))).homology p :=
  HomologicalComplex.homologyMapIso (actualSchemeModulePushforwardCechIso i L c U) p

/-- Literal actual global pushforward sections retain the actual source structural base action. -/
def actualSchemeModulePushforwardGlobalSectionsIso :
    actualSchemeModuleBaseGlobalSections ((Scheme.Modules.pushforward i).obj L) c ≅
      actualSchemeModuleBaseGlobalSections L (actualSchemePushforwardSourceConstants i c) := by
  let P := actualSchemeModuleBaseGlobalSections ((Scheme.Modules.pushforward i).obj L) c
  let Q := actualSchemeModuleBaseGlobalSections L (actualSchemePushforwardSourceConstants i c)
  have e : P ≃ₗ[K] Q := {
    toFun := fun s => s
    invFun := fun s => s
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact e.toModuleIso

end

end Hironaka.Geometry.ProperSteinProjectiveCech
