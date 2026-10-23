/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# Pullbacks of quasi-coherent modules are quasi-coherent

For every morphism of schemes `f : Y ⟶ X` and every quasi-coherent `𝒪_X`-module `M`, the inverse
image `f^* M = (Scheme.Modules.pullback f).obj M` is quasi-coherent (`isQuasicoherent_pullback`,
an instance). In particular the base change `F_B = q_B^* F` of a quasi-coherent module along
`q_B : X_B = X ×_V Spec B → X` is quasi-coherent, so the Čech machinery of lane COH1 (independence
of the cover, long exact sequences, vanishing for short affine covers) applies on `X_B`, e.g. on
the closed fibre in Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Proposition 4.4.6 (`semi-stable.tex` lines 3212–3219), where `H¹(𝓛_s)` is computed on the
closed fibre.

## The argument

`f^*` is a left adjoint, so it preserves colimits, and it sends `𝒪_X` to `𝒪_Y`
(`pullbackUnitIso`: Mathlib's `SheafOfModules.pullbackObjUnitToUnit` is an isomorphism because
the functor of opens `U ↦ f⁻¹U` is final, `final_opensMap`, the poset of opens `U` with
`V ⊆ f⁻¹U` having the top element `U = X`). Hence `f^*` maps presentations (cokernels of maps of
free modules) to presentations (`presentationPullback`). A quasi-coherent `M` has presentations on
the members `U_i` of an open cover (`Scheme.Modules.exists_isOpenCover_presentation`); the
restriction of `f^* M` to `f⁻¹U_i` is `(f|_{U_i})^*(M|_{U_i})` (`restrictPullbackIso`), which has
a presentation, and modules with presentations on the members of an open cover are
quasi-coherent (`isQuasicoherent_of_presentation_restrict`).

The affine case is also in AINTLIB (`isQuasicoherent_pullback_of_isAffine`,
`EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/AffineModuleBaseChange.lean`), via
tilde and extension of scalars; the local criterion below follows the pattern of its
`isQuasicoherent_over_of_restrict_of_isAffineOpen`. The present proof needs neither affineness
nor the tilde comparison.

Blueprint: `sm-cohomology-stein.tex`, `lem:sm-opens-map-final`, `lem:sm-pullback-presentation`,
`lem:sm-qcoh-local`, `thm:sm-pullback-qcoh`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

/-- **The functor of preimages is final**: for a continuous map `f : X → Y`, the functor
`U ↦ f⁻¹(U)` from opens of `Y` to opens of `X` is final; for each open `V` of `X` the opens `U`
with `V ⊆ f⁻¹(U)` form a category with terminal object `U = Y`. -/
theorem final_opensMap {X Y : TopCat.{u}} (f : X ⟶ Y) : (Opens.map f).Final where
  out V := by
    let t : StructuredArrow V (Opens.map f) :=
      StructuredArrow.mk (Y := ⊤) (homOfLE fun x _ => trivial)
    refine isConnected_of_isTerminal _ (x := t) (IsTerminal.ofUniqueHom
      (fun s => StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _))
      fun s m => ?_)
    ext
    exact Subsingleton.elim _ _

attribute [local instance] final_opensMap

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **Pullback of the structure sheaf**: `f^* 𝒪_X ≅ 𝒪_Y` for every morphism `f : Y ⟶ X`. -/
def pullbackUnitIso (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have := final_opensMap f.base
  have : IsIso (C := SheafOfModules Y.ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency false in
/-- **Pullbacks of presentations**: a presentation of `M` (a cokernel of a map of free modules)
induces a presentation of `f^* M`, `f^*` being a left adjoint which preserves `𝒪`. -/
def presentationPullback (f : Y ⟶ X) {M : X.Modules} (P : M.Presentation) :
    ((Scheme.Modules.pullback f).obj M).Presentation :=
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  P.map (Scheme.Modules.pullback f) (pullbackUnitIso f).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Local presentations give quasi-coherence**: a module whose restrictions to the members of an
open cover have presentations is quasi-coherent. (The restrictions are transported to the
over-sites `𝒪_X.over U` of Mathlib's `QuasicoherentData` along `Scheme.Modules.overEquiv`.) -/
theorem isQuasicoherent_of_presentation_restrict (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.IsQuasicoherent := by
  let q : SheafOfModules.QuasicoherentData.{u} (R := X.ringCatSheaf) M :=
    { I := ι, X := U, coversTop := ?_, presentation := fun i => ?_ }
  · exact q.isQuasicoherent
  · rw [Opens.coversTop_iff]
    exact hU
  · let N := M.restrict (U i).ι
    have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv (U i)).inverse :=
      inferInstance
    let Q : ((Scheme.Modules.overEquiv (U i)).inverse.obj N).Presentation :=
      (P i).map (Scheme.Modules.overEquiv (U i)).inverse
        ((U i).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
    let e : M.over (U i) ≅ (Scheme.Modules.overEquiv (U i)).inverse.obj N :=
      (Scheme.Modules.overEquiv (U i)).unitIso.app (M.over (U i)) ≪≫
        (Scheme.Modules.overEquiv (U i)).inverse.mapIso
          ((Scheme.Modules.overFunctorEquiv (U i)).app M)
    exact Q.ofIsIso e.inv

set_option backward.isDefEq.respectTransparency.types false in
/-- **Restriction of a pullback**: for `f : Y ⟶ X` and an open `U ⊆ X`,
`(f^* M)|_{f⁻¹U} ≅ (f|_U)^* (M|_U)`. -/
def restrictPullbackIso (f : Y ⟶ X) (U : X.Opens) (M : X.Modules) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Pullbacks of quasi-coherent modules are quasi-coherent**: for every morphism of schemes
`f : Y ⟶ X` and every quasi-coherent `𝒪_X`-module `M`, the inverse image `f^* M` is
quasi-coherent. -/
instance isQuasicoherent_pullback (f : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  obtain ⟨ι, U, pres, hU, -⟩ := M.exists_isOpenCover_presentation
  refine isQuasicoherent_of_presentation_restrict _ (fun i => f ⁻¹ᵁ U i) ?_ fun i =>
    (presentationPullback (f ∣_ U i) (pres i)).ofIsIso (restrictPullbackIso f (U i) M).inv
  refine eq_top_iff.mpr fun y _ => ?_
  have hy : f y ∈ ⨆ i, U i := by
    rw [show (⨆ i, U i) = ⊤ from hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end

end DeJongAlterations.StableModification.Cohomology
