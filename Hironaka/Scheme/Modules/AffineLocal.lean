/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Modules.Sections
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite presentation from the affine opens

Mathlib's notion of a sheaf of modules of finite presentation
(`SheafOfModules.IsFinitePresentation`, which implies `IsQuasicoherent` and `IsFiniteType`) asks
for a covering family of objects of the
site and finite presentations of the restrictions over them. For a sheaf of modules `F` on a scheme
`X` such restrictions come from the affine opens: a finite presentation of the restriction of `F`
to `Spec Γ(X, U) ≅ U` gives one of `F.over U` (`Scheme.Modules.presentationOverOfRestrict`, by
Mathlib's transport of presentations along functors that preserve colimits and the unit), and over
`Spec R` a quasi-coherent sheaf `M^~` with `M` finitely presented has a finite presentation
(Mathlib's `presentationTilde`). Hence `F` is of finite presentation as soon as, over every affine
open `U`, its restriction to `Spec Γ(X, U)` is the sheaf `M^~` of the finitely presented module
`M = Γ(F, U)` (`Scheme.Modules.isFinitePresentation_of_forall_affine`).
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The restriction of `F` to an open `U` along `U.ι` is the restriction to `Spec Γ(X, U)` pushed
along `U ≅ Spec Γ(X, U)`. -/
noncomputable def restrictιIso {U : X.Opens} (hU : IsAffineOpen U) :
    (F.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ F.restrict U.ι :=
  ((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app F).symm ≪≫
    (restrictFunctorCongr (by rw [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc])).app F

/-- `F.over U` is the restriction of `F` along `U.ι`, through `overEquiv U`. -/
noncomputable def overIso (U : X.Opens) :
    (overEquiv U).inverse.obj (F.restrict U.ι) ≅ F.over U :=
  (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app F).symm ≪≫
    ((overEquiv U).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency false in
/-- **A presentation of `F.over U` from one of the restriction of `F` to `Spec Γ(X, U)`**, for an
affine open `U`: transported along the restriction to `U ≅ Spec Γ(X, U)` and the equivalence
`overEquiv U`, which preserve colimits and the unit. -/
noncomputable def presentationOverOfRestrict {U : X.Opens} (hU : IsAffineOpen U)
    (P : (F.restrict hU.fromSpec).Presentation) : (F.over U).Presentation :=
  have : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse :=
    (overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits
  (((presentationRestrict hU.isoSpec.hom P).ofIsIso (F.restrictιIso hU).hom).map
    (overEquiv U).inverse (Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf).symm).ofIsIso
      (F.overIso U).hom

set_option backward.isDefEq.respectTransparency false in
theorem isFinite_presentationOverOfRestrict {U : X.Opens} (hU : IsAffineOpen U)
    (P : (F.restrict hU.fromSpec).Presentation) [P.IsFinite] :
    (F.presentationOverOfRestrict hU P).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

/-- **Finite presentation from the affine opens**: if over every affine open `U` the restriction of
`F` to `Spec Γ(X, U)` has a finite presentation, then `F` is of finite presentation (hence
quasi-coherent and of finite type). -/
theorem isFinitePresentation_of_forall_affine
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      ∃ P : (F.restrict hU.fromSpec).Presentation, P.IsFinite) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F := by
  choose P hP using h
  let σ : SheafOfModules.QuasicoherentData.{u} (R := X.ringCatSheaf) F :=
    { I := X.affineOpens
      X := fun U => (U : X.Opens)
      coversTop := (Opens.coversTop_iff (U := fun U : X.affineOpens => (U : X.Opens))).mpr
        (iSup_affineOpens_eq_top X)
      presentation := fun (U : X.affineOpens) => F.presentationOverOfRestrict U.2 (P U U.2) }
  have hσ : σ.IsFinitePresentation := by
    constructor
    intro U
    have := hP U U.2
    exact F.isFinite_presentationOverOfRestrict U.2 (P U U.2)
  constructor
  exact ⟨σ, hσ⟩

set_option backward.isDefEq.respectTransparency false in
/-- Over an affine open `V`, if the restriction of `F` to `Spec Γ(X, V)` is the sheaf associated to
its global sections and `Γ(F, V)` is a finitely presented `Γ(X, V)`-module, the restriction has a
finite presentation (Mathlib's `presentationTilde`). -/
theorem exists_isFinite_presentation_restrict {V : X.Opens} (hV : IsAffineOpen V)
    [IsIso (F.restrict hV.fromSpec).fromTildeΓ] [Module.FinitePresentation Γ(X, V) Γ(F, V)] :
    ∃ P : (F.restrict hV.fromSpec).Presentation, P.IsFinite := by
  let M := (modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).presheaf.obj (op ⊤)
  have : Module.FinitePresentation Γ(X, V) M :=
    Module.FinitePresentation.of_equiv (F.topSectionsEquiv hV)
  obtain ⟨s, hs, t, ht⟩ : ∃ (s : Finset M), Submodule.span Γ(X, V) (s : Set M) = ⊤ ∧
      ∃ t : Finset (s →₀ Γ(X, V)), Submodule.span Γ(X, V) (t : Set (s →₀ Γ(X, V))) =
        LinearMap.ker (Finsupp.linearCombination Γ(X, V) ((↑) : s → M)) := by
    obtain ⟨s, hs, t, ht⟩ := this.out
    exact ⟨s, hs, t, ht⟩
  let P₀ := presentationTilde (M := M) (s : Set M) hs (t : Set (s →₀ Γ(X, V))) ht
  have : P₀.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set M))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ Γ(X, V))))⟩ }
  exact ⟨P₀.ofIsIso (F.restrict hV.fromSpec).fromTildeΓ, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Over `Spec R`, a quasi-coherent sheaf of modules generated by finitely many global sections has
finitely generated global sections: through the equivalence `M ↦ M^~`, which reflects epimorphisms,
the epimorphism from the free sheaf on the generators is a surjection `R^I → Γ(M)`. -/
theorem finite_moduleSpecΓ_of_generatingSections {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [IsIso M.fromTildeΓ] (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  have hcounit : (tilde.functor R).map (moduleSpecΓFunctor.map G.π) =
      Scheme.Modules.fromTildeΓ (R := R) (SheafOfModules.free G.I) ≫ G.π ≫ inv M.fromTildeΓ := by
    rw [← Category.assoc, IsIso.eq_comp_inv]
    exact (tilde.adjunction (R := R)).counit.naturality G.π
  have : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map G.π)) := by
    rw [hcounit]
    have : Epi G.π := G.epi
    exact epi_comp _ _
  have : Epi (moduleSpecΓFunctor.map G.π) := (tilde.functor R).epi_of_epi_map this
  have hsurj : Function.Surjective (moduleSpecΓFunctor.map G.π).hom :=
    (ModuleCat.epi_iff_surjective _).mp this
  have e : moduleSpecΓFunctor.obj (SheafOfModules.free G.I) ≅ ModuleCat.of R (G.I →₀ R) :=
    moduleSpecΓFunctor.mapIso (tildeFinsupp G.I).symm ≪≫
      (tilde.toTildeΓNatIso.app (ModuleCat.of R (G.I →₀ R))).symm
  have : Module.Finite R (moduleSpecΓFunctor.obj (SheafOfModules.free G.I)) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  exact Module.Finite.of_surjective _ hsurj

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

set_option backward.isDefEq.respectTransparency false in
/-- **A quasi-coherent sheaf of finite type has finitely generated sections over small affine
opens**: every point has an affine open neighbourhood `U` with `Γ(F, U)` a finitely generated
`Γ(X, U)`-module. The finitely many local generators of `F` over an open `W ∋ x`, restricted to an
affine `U ⊆ W` and transported to `Spec Γ(X, U)`, generate there the sheaf associated to
`Γ(F, U)` (`finite_moduleSpecΓ_of_generatingSections`). -/
theorem exists_isAffineOpen_finite_sections [F.IsQuasicoherent] [SheafOfModules.IsFiniteType.{u} F]
    (x : X) : ∃ (U : X.Opens) (_ : IsAffineOpen U), x ∈ U ∧ Module.Finite Γ(X, U) Γ(F, U) := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hcov := (Opens.coversTop_iff (U := σ.X)).mp σ.coversTop
  obtain ⟨i, hi⟩ : ∃ i, x ∈ σ.X i := Opens.mem_iSup.mp (hcov.symm ▸ Opens.mem_top x :
    x ∈ ⨆ i, σ.X i)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (σ.X i).isOpen
  have hU : IsAffineOpen U := hU
  let W : X.Opens := σ.X i
  have hUW : U ≤ W := hUW
  let j : Spec Γ(X, U) ⟶ W.toScheme := hU.isoSpec.inv ≫ X.homOfLE hUW
  have hj : j ≫ W.ι = hU.fromSpec := by
    rw [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.fromSpec]
  let Φ := (overEquiv W).functor ⋙ restrictFunctor j
  have : PreservesColimitsOfSize.{u, u} Φ :=
    ((overEquiv W).toAdjunction.comp (restrictAdjunction j)).leftAdjoint_preservesColimits
  let η : SheafOfModules.unit _ ≅ Φ.obj (SheafOfModules.unit _) :=
    ((restrictFunctor j).mapIso (Opens.sheafOfModulesEquivOverUnit W X.ringCatSheaf) ≪≫
      restrictUnitIso j).symm
  let e : Φ.obj (F.over W) ≅ F.restrict hU.fromSpec :=
    (restrictFunctor j).mapIso ((overFunctorEquiv W).app F) ≪≫
      ((restrictFunctorComp j W.ι).app F).symm ≪≫ (restrictFunctorCongr hj).app F
  have := hσ.isFiniteType i
  let G := ((σ.generators i).map Φ η).ofEpi e.hom
  have : G.IsFiniteType := inferInstance
  have : Module.Finite Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
    finite_moduleSpecΓ_of_generatingSections (F.restrict hU.fromSpec) G
  exact ⟨U, hU, hxU, Module.Finite.equiv (F.topSectionsEquiv hU).symm⟩

end AlgebraicGeometry.Scheme.Modules
