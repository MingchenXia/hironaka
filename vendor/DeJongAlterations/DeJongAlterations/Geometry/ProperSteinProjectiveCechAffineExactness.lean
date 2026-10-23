import DeJongAlterations.Geometry.ProperSteinProjectiveCechAffineDenominators
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Actual affine quasicoherent epimorphisms and finite original generators

Native-only adaptation of selected closed proofs from
`EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean`,
SHA256 a8dc9bd99f712c3e5e4dbbd0ed5237f8e205ec957695689df4147c3ceed00d7d.
No other-project module, custom axiom, desired exactness or finiteness certificate is imported.
-/

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- On an affine spectrum, global sections send epimorphisms of quasicoherent modules to
epimorphisms of modules. -/
lemma affineQuasicoherentSpec_globalEpi {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Epi (moduleSpecΓFunctor.map f) := by
  have : IsIso M.fromTildeΓ := inferInstance
  have : IsIso N.fromTildeΓ := inferInstance
  have hnat : tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := by
    have h := Scheme.Modules.fromTildeΓNatTrans.naturality f
    change tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f at h
    exact h
  have hright : Epi (M.fromTildeΓ ≫ f) :=
    epi_comp' (by infer_instance) (by infer_instance)
  have hcomp : Epi (tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ) :=
    hnat.symm ▸ hright
  have hmapped : Epi (tilde.map (moduleSpecΓFunctor.map f)) :=
    (epi_comp_iff_of_isIso _ N.fromTildeΓ).mp hcomp
  exact (tilde.functor R).epi_of_epi_map hmapped

/-- On an affine spectrum, an epimorphism of quasicoherent modules is surjective on global
sections. -/
theorem affineQuasicoherentSpec_sectionsSurjective
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom :=
  (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f)).mp
    (affineQuasicoherentSpec_globalEpi f)


/-- On an affine scheme, an epimorphism of quasicoherent modules is surjective on global
sections. -/
theorem affineQuasicoherent_sectionsSurjective [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom := by
  have h := affineQuasicoherentSpec_sectionsSurjective
    ((restrictFunctor (Scheme.isoSpec X).inv).map f)
  change Function.Surjective
    (f.val.app (op ((Scheme.isoSpec X).inv ''ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens)))).hom at h
  have htop : (Scheme.isoSpec X).inv ''ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) = ⊤ :=
    (Scheme.isoSpec X).inv.image_top_eq_opensRange.trans
      (Scheme.isoSpec X).inv.opensRange_of_isIso
  exact htop ▸ h

/-- The global sections of a finite free sheaf form a finite module. -/
theorem affineFree_globalSections_finite
    (X : Scheme.{u}) (I : Type u) [Finite I] :
    Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free I (R := X.ringCatSheaf))) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let U := fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf
  let : HasBiproduct U := HasBiproduct.of_hasCoproduct U
  let : F.Additive := by
    change (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).Additive
    unfold SheafOfModules.evaluation
    infer_instance
  let : PreservesLimit (Discrete.functor U) F := by
    dsimp [F]
    infer_instance
  let : PreservesBiproduct U F :=
    preservesBiproduct_of_preservesProduct F
  let e : F.obj (SheafOfModules.free I) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op ⊤))
        (∀ i, F.obj (U i)) :=
    F.mapIso (biproduct.isoCoproduct U).symm ≪≫
      F.mapBiproduct U ≪≫
      biproduct.isoProduct (F.obj ∘ U) ≪≫
      ModuleCat.piIsoPi (F.obj ∘ U)
  have hfinite (i : I) :
      Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (F.obj (U i)) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      (X.ringCatSheaf.obj.obj (op ⊤))
    infer_instance
  have : Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (∀ i, F.obj (U i)) :=
    @Module.Finite.pi _ _ I (fun i ↦ F.obj (U i)) inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) hfinite
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- A quasicoherent module on an affine scheme with finitely many global generators has a
finite module of global sections. -/
theorem affineQuasicoherent_generatorsGlobalSections_finite
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  have : Finite G.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let L : X.Modules := SheafOfModules.free G.I
  let f : L ⟶ M := G.π
  let : Epi f := G.epi
  let : L.IsQuasicoherent := inferInstance
  have hL : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free G.I (R := X.ringCatSheaf)))
    exact affineFree_globalSections_finite X G.I
  let : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := hL
  have hf : Epi f := inferInstance
  have hsurj : Function.Surjective (f.val.app (op ⊤)).hom := by
    exact @affineQuasicoherent_sectionsSurjective X inferInstance
      L M f inferInstance inferInstance hf
  exact Module.Finite.of_surjective (hM := hL) (f.val.app (op ⊤)).hom hsurj


end
end DeJongAlterations.Geometry.ProperSteinProjectiveCech
