import DeJongAlterations.StableModificationBridge.NilradicalCechVanishing
import DeJongAlterations.StableModificationBridge.ShortExactCochainLift

/-! Whole actual global functions lift INTERNALLY through the SAME original affine nilradical reduction. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.NilradicalGlobalSections

open CategoryTheory Limits Opposite AlgebraicGeometry
open StableModification StableModification.Cohomology
open Geometry.ProperSteinProjectiveCech

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

private theorem augmentation_naturality {X : Scheme.{u}} {R : Type u} [CommRing R]
    {F G : X.Modules} (φ : F ⟶ G) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (c : R →+* Γ(X, ⊤)) (s : sectionsModuleCat F c ⊤ le_top) :
    (cechComplexMap U c φ).f 0 (cechAugmentation F U c s) =
      cechAugmentation G U c (φ.app ⊤ s) := by
  apply Subtype.ext
  funext T
  change φ.app (T.inf U) (if T.card = 1 then F.presheaf.map (homOfLE le_top).op s else 0) =
    if T.card = 1 then G.presheaf.map (homOfLE le_top).op (φ.app ⊤ s) else 0
  split_ifs
  · exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE le_top).op) s
  · exact map_zero _

/-- The WHOLE actual original reduction map on global functions is internally surjective, with no lift certificate. -/
theorem reduction_appTop_surjective (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffine X.nilradical.subscheme] : Function.Surjective X.nilradical.subschemeι.appTop := by
  let C := FiniteAffineCover.choose X
  let c := RingHom.id Γ(X, ⊤)
  let O := SheafOfModules.unit X.ringCatSheaf
  let P := (Scheme.Modules.pushforward X.nilradical.subschemeι).obj
    (SheafOfModules.unit X.nilradical.subscheme.ringCatSheaf)
  let f : X.nilradical.dja_toModules ⟶ O := ⟨X.nilradical.dja_toSubmodule.ι⟩
  let g : O ⟶ P :=
    SheafOfModules.unitToPushforwardObjUnit X.nilradical.subschemeι.toRingCatSheafHom
  let α := sectionsDiagramMap c f (fun T : Finset C.ι => T.inf C.U)
    (fun _ _ h => Finset.inf_mono h) (fun _ => le_top)
  let β := sectionsDiagramMap c g (fun T : Finset C.ι => T.inf C.U)
    (fun _ _ h => Finset.inf_mono h) (fun _ => le_top)
  have hlocal (T : Finset C.ι) (hT : T.Nonempty) :
      Function.Exact (α.app T).hom (β.app T).hom ∧
        Function.Injective (α.app T).hom ∧ Function.Surjective (β.app T).hom := by
    let U : X.affineOpens := ⟨T.inf C.U, C.isAffineOpen_inf T hT⟩
    change Function.Exact (f.app U) (Scheme.Modules.Hom.app g U) ∧
      Function.Injective (f.app U) ∧ Function.Surjective (Scheme.Modules.Hom.app g U)
    refine ⟨?_, ?_, X.nilradical.subschemeι_app_surjective U⟩
    · intro a
      have hker : Scheme.Modules.Hom.app g U a = 0 ↔ a ∈ X.nilradical.ideal U := by
        change X.nilradical.subschemeι.app U a = 0 ↔ a ∈ X.nilradical.ideal U
        rw [← X.nilradical.ker_subschemeι_app U]
        rfl
      rw [hker]
      constructor
      · intro ha
        exact ⟨(X.nilradical.dja_toModulesSectionsEquiv U).symm ⟨a, ha⟩, rfl⟩
      · rintro ⟨s, rfl⟩
        exact (X.nilradical.dja_toModulesSectionsEquiv U s).property
    · intro a b h
      exact Subtype.ext h
  let S := SubsetNonemptyExactness.sequence α β hlocal
  have hS : S.ShortExact := SubsetNonemptyExactness.sequence_shortExact α β hlocal
  have hH : IsZero (S.X₁.homology 1) :=
    NilradicalCechVanishing.isZero_first_of_affine_reduction X X.nilradical C c
  intro r
  let t := cechAugmentation P C.U c (show sectionsModuleCat P c ⊤ le_top from r)
  have ht : S.X₃.d 0 1 t = 0 := by
    change (subsetCechComplex (cechDiagram P C.U c)).d 0 1 t = 0
    rw [subsetCechComplex_d]
    exact cechAugmentation_mem_ker P C.U c r
  obtain ⟨z, hzc, hzt⟩ := ShortExactCochainLift.exists_closed_lift S hS hH t ht
  have hzk : z ∈ LinearMap.ker (subsetCechCardDifferential (cechDiagram O C.U c) 1) := by
    change (subsetCechCardDifferential (cechDiagram O C.U c) 1) z = 0
    change (subsetCechComplex (cechDiagram O C.U c)).d 0 1 z = 0 at hzc
    rw [subsetCechComplex_d] at hzc
    exact hzc
  obtain ⟨a, ha⟩ := cechAugmentation_surjective_ker O c C.iSup_eq_top z hzk
  refine ⟨a, ?_⟩
  change Scheme.Modules.Hom.app g ⊤ a = r
  apply cechAugmentation_injective P c C.iSup_eq_top
  rw [← augmentation_naturality g C.U c a, ha]
  exact hzt

end DeJongAlterations.StableModificationBridge.NilradicalGlobalSections
