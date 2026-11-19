import Hironaka.Resolution.HironakaChowNativeGeneratorNeighborhood
import Hironaka.Resolution.HironakaChowNativeLocalOverStalkTransport

/-! The SAME original stalk map has an internally constructed epimorphic
lift on the LITERAL original restricted space, with the full native square.
Blueprint FIRST: `hironaka-g10-native-same-stalk-epimorphism.tex`.
No kernel coherence or later filtration/continuation is asserted. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaChowNativeSameStalkEpimorphism

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeModuleStalkExact HironakaChowNativeFinitePresentationSpreading
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeGeneratorNeighborhood
  HironakaChowNativeArbitraryOverRealization HironakaChowNativeLocalOverFiniteDataTransport
  HironakaChowNativeLocalOverStalkTransport

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- Only ordinary native finite presentation and one-point stalk surjectivity
construct the SAME actual local map and its literal native epimorphic image. -/
theorem exists_original_same_stalk_epimorphism
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (Q N : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    [Q.IsFinitePresentation] [N.IsFinitePresentation] (p : U)
    (φ : (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj Q ⟶
      (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj N)
    (hφ : Function.Surjective φ) :
    ∃ (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : Q.over V ⟶ N.over V),
      Epi b ∧
      ModuleCat.ofHom (stalkLinearMapOfOver (X.restrict U.isOpenEmbedding).𝒪
        V b p hpV) = φ ∧
      let W : Opens X.toTopCat := (U.overEquivalence.inverse.obj V).left
      let pW : W := ⟨p.val, ⟨p, hpV, rfl⟩⟩
      let T := localOverTransport X U V
      let q := T.map b
      Epi q ∧ (T.obj (Q.over V)).IsFinitePresentation ∧
        (T.obj (N.over V)).IsFinitePresentation ∧
      (ModuleCat.restrictScalars
          (localOverRingStalkEquiv X U V p hpV).symm.toRingHom).map
          ((nativeStalkFunctor (X.restrict W.isOpenEmbedding).𝒪 pW).map q) ≫
          (localOverModuleStalkIso X U V N p hpV).hom =
        (localOverModuleStalkIso X U V Q p hpV).hom ≫ φ := by
  let R := (X.restrict U.isOpenEmbedding).𝒪
  obtain ⟨A, hpA, a, ha⟩ := exists_local_lift_of_isFinitePresentation R p φ.hom
  have hsurj : Function.Surjective (stalkLinearMapOfOver R A a p hpA) := by
    rw [ha]
    exact hφ
  obtain ⟨V, hVA, hpV, hb⟩ := exists_subopen_epi_of_stalk_surjective R A a p hpA hsurj
  let b := restrictOverHom R A V hVA a
  let : Epi b := hb
  have hstalk : ModuleCat.ofHom (stalkLinearMapOfOver R V b p hpV) = φ := by
    apply ModuleCat.hom_ext
    change stalkLinearMapOfOver R V b p hpV = φ.hom
    rw [stalkLinearMapOfOver_restrictOverHom]
    exact ha
  refine ⟨V, hpV, b, inferInstance, hstalk, ?_⟩
  dsimp only
  let W : Opens X.toTopCat := (U.overEquivalence.inverse.obj V).left
  let T := localOverTransport X U V
  have hq : Epi (T.map b) := by
    change Epi ((realizationFunctor X W).map ((localModuleEquivalence X U V).inverse.map b))
    let : Epi ((localModuleEquivalence X U V).inverse.map b) := Functor.map_epi _ b
    exact Functor.map_epi _ _
  have hQover : (Q.over V).IsFinitePresentation := over_isFinitePresentation R Q V
  have hNover : (N.over V).IsFinitePresentation := over_isFinitePresentation R N V
  have hQinv : ((localModuleEquivalence X U V).inverse.obj (Q.over V)).IsFinitePresentation :=
    @local_inverse_isFinitePresentation X U V (Q.over V) hQover
  have hNinv : ((localModuleEquivalence X U V).inverse.obj (N.over V)).IsFinitePresentation :=
    @local_inverse_isFinitePresentation X U V (N.over V) hNover
  have hQ : (T.obj (Q.over V)).IsFinitePresentation :=
    @realization_isFinitePresentation X W
      ((localModuleEquivalence X U V).inverse.obj (Q.over V)) hQinv
  have hN : (T.obj (N.over V)).IsFinitePresentation :=
    @realization_isFinitePresentation X W
      ((localModuleEquivalence X U V).inverse.obj (N.over V)) hNinv
  refine ⟨hq, hQ, hN, ?_⟩
  have hn := localOverModuleStalkIso_naturality X U V b p hpV
  rw [hstalk] at hn
  exact hn

end

end Hironaka.HironakaChowNativeSameStalkEpimorphism
