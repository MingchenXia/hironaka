import Hironaka.Resolution.HironakaChowNativeOpenFreeKernelCoherence
import Hironaka.Resolution.HironakaChowNativeLocalOverFiniteDataTransport

/-! Finite presentation of the SAME native free kernel on actual local over-sites.
Blueprint first: hironaka-g10-native-local-over-free-kernel-coherence.tex.
Accepted Oka/free-kernel and generic transport engines receive zero duplicate credit. -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
namespace Hironaka.HironakaChowNativeLocalOverFreeKernelCoherence
open HironakaChowNativeFreePartContinuation HironakaChowNativeArbitraryOverRealization
  HironakaChowNativeLocalOverFiniteDataTransport HironakaSingularModuleSheafStalk

private theorem realization_preservesZero (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) : (realizationEquivalence X U).functor.PreservesZeroMorphisms where
  map_zero M N := by
    ext T m
    rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem local_return_preservesZero (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U)) :
    (localModuleEquivalence X U V).inverse.PreservesZeroMorphisms where
  map_zero M N := by
    ext T m
    rfl

private theorem finitePresentation_of_iso
    {C : Type} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{0}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {M N : SheafOfModules.{0} R} (e : M ≅ N) (hM : M.IsFinitePresentation) :
    N.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation R).prop_of_iso e hM

private def freeReindexIso
    {C : Type} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {I J : Type} (e : I ≃ J) : SheafOfModules.free (R := R) I ≅ SheafOfModules.free J :=
  (SheafOfModules.freeFunctor (R := R)).mapIso e.toIso

private theorem literal_free_kernel_finitePresentation {n : ℕ}
    (U : Opens (originalSpace n).toTopCat) {I J : Type} [Finite I] [Finite J]
    (f : SheafOfModules.free (R := forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪) I ⟶
      SheafOfModules.free (R := forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪) J) :
    (kernel f).IsFinitePresentation := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let R := forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪
  let ea := freeReindexIso R (Fintype.equivFin I)
  let eb := freeReindexIso R (Fintype.equivFin J)
  let g := ea.inv ≫ f ≫ eb.hom
  have : (kernel g).IsFinitePresentation := HironakaChowNativeOpenFreeKernelCoherence.original_open_kernel_isFinitePresentation U g
  let e := kernel.mapIso g f ea.symm eb.symm (by simp [g])
  exact finitePresentation_of_iso e inferInstance

-- Actual native site equivalences supply the nested sheafification proofs.
-- LOCAL instance attributes only: no imported instance or native object is replaced.
private theorem singleOverAddGroupSheafify {X : TopCat.{0}} (U : Opens X) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0} :=
  U.overEquivalence.hasSheafify ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{0}

private theorem doubleOverAddGroupSheafify {X : TopCat.{0}} (U : Opens X) (V : Over U) :
    HasSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{0} :=
  (Over.iteratedSliceEquiv V).hasSheafify (((Opens.grothendieckTopology X).over U).over V)
    ((Opens.grothendieckTopology X).over V.left) AddCommGrpCat.{0}

private theorem doubleOverAddGroupWeakSheafify {X : TopCat.{0}} (U : Opens X) (V : Over U) :
    HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{0} :=
  (doubleOverAddGroupSheafify U V).isRightAdjoint

section NativeOpenOver
attribute [local instance] singleOverAddGroupSheafify doubleOverAddGroupSheafify doubleOverAddGroupWeakSheafify

set_option backward.isDefEq.respectTransparency.types false in
private theorem literal_over_free_kernel_finitePresentation {n : ℕ}
    (U : Opens (originalSpace n).toTopCat) (V : Opens (TopCat.of U))
    {I J : Type} [Finite I] [Finite J]
    (f : SheafOfModules.free
      (R := (forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪).over V) I ⟶
        SheafOfModules.free J) : (kernel f).IsFinitePresentation := by
  let X := originalSpace n
  let W := (U.overEquivalence.inverse.obj V).left
  let E := localModuleEquivalence X U V
  let EW := realizationEquivalence X W
  let F := E.inverse ⋙ EW.functor
  have : E.inverse.IsEquivalence := E.isEquivalence_inverse
  have : EW.functor.IsEquivalence := EW.isEquivalence_functor
  have : F.IsEquivalence := inferInstance
  have : E.inverse.PreservesZeroMorphisms := local_return_preservesZero X U V
  have : EW.functor.PreservesZeroMorphisms := realization_preservesZero X W
  have : F.PreservesZeroMorphisms := inferInstance
  let ea := EW.functor.mapIso (localReturnFreeIso X U V I) ≪≫ realizationFreeIso X W I
  let eb := EW.functor.mapIso (localReturnFreeIso X U V J) ≪≫ realizationFreeIso X W J
  let g := ea.inv ≫ F.map f ≫ eb.hom
  have hK : (kernel g).IsFinitePresentation := literal_free_kernel_finitePresentation W g
  let e : F.obj (kernel f) ≅ kernel g :=
    PreservesKernel.iso F f ≪≫ kernel.mapIso (F.map f) g ea eb (by
      change F.map f ≫ eb.hom = ea.hom ≫ ea.inv ≫ (F.map f ≫ eb.hom)
      exact (ea.hom_inv_id_assoc (F.map f ≫ eb.hom)).symm)
  have : (F.obj (kernel f)).IsFinitePresentation := finitePresentation_of_iso e.symm hK
  have hReturn : (EW.inverse.obj (F.obj (kernel f))).IsFinitePresentation :=
    return_isFinitePresentation X W _
  have : (E.inverse.obj (kernel f)).IsFinitePresentation :=
    finitePresentation_of_iso (EW.unitIso.app (E.inverse.obj (kernel f))).symm hReturn
  have hForward : (E.functor.obj (E.inverse.obj (kernel f))).IsFinitePresentation :=
    local_forward_isFinitePresentation X U V _
  exact finitePresentation_of_iso (E.counitIso.app (kernel f)) hForward

end NativeOpenOver

section NativeOpenReturn
attribute [local instance] singleOverAddGroupSheafify doubleOverAddGroupSheafify doubleOverAddGroupWeakSheafify

/-- Every original local over-site finite free map has its SAME native kernel FP. -/
theorem original_open_over_free_kernel_isFinitePresentation {n : ℕ}
    (U : Opens (originalSpace n).toTopCat)
    (V : Opens ((originalSpace n).restrict U.isOpenEmbedding).toTopCat)
    {I J : Type} [Finite I] [Finite J]
    (F : SheafOfModules.free
      (R := (forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪).over V) I ⟶
        SheafOfModules.free
          (R := (forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪).over V) J) :
    (kernel F).IsFinitePresentation := by
  exact literal_over_free_kernel_finitePresentation U V F

end NativeOpenReturn

end Hironaka.HironakaChowNativeLocalOverFreeKernelCoherence
end
