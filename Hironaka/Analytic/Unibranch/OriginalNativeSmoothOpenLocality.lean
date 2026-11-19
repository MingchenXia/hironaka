import Hironaka.Analytic.Unibranch.OriginalNativeSmoothComposition

/-! Genuine native target-open reflection and source/target open-square locality.
Blueprint first: `original-native-smooth-open-locality.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality
noncomputable section
open SourceReducedComplexSpace OriginalNativeProductWindow OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothComposition

variable {X Y Z A B C : SourceReducedComplexSpace}

/-- Actual ordinary native OIs internally produce their full native OI lift. -/
theorem exists_native_open_lift (i : B ⟶ C) (a : A ⟶ C)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
    (hr : range a.hom.left.base ⊆ range i.hom.left.base) :
    ∃ k : A ⟶ B, LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ k ≫ i = a := by
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  let : LocallyRingedSpace.IsOpenImmersion a.hom.left := ha
  let l := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left a.hom.left hr
  have hfac : l ≫ i.hom.left = a.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hp : l ≫ B.obj.hom = A.obj.hom := by
    calc
      _ = l ≫ (i.hom.left ≫ C.obj.hom) := congrArg (fun t => l ≫ t) (Over.w i.hom).symm
      _ = (l ≫ i.hom.left) ≫ C.obj.hom := (Category.assoc _ _ _).symm
      _ = a.hom.left ≫ C.obj.hom := congrArg (fun t => t ≫ C.obj.hom) hfac
      _ = _ := Over.w a.hom
  let k : A ⟶ B := ObjectProperty.homMk (Over.homMk l hp)
  have hl : LocallyRingedSpace.IsOpenImmersion l := by
    let : IsIso (CategoryTheory.Limits.pullback.snd i.hom.left a.hom.left) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset i.hom.left a.hom.left hr
    dsimp only [l,LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  refine ⟨k,hl,?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hfac

/-- Genuine target OIs reflect ordinary native smoothness of the SAME full map. -/
theorem isSmoothAt_of_postcomp_openImmersion (f : X ⟶ Y) (i : Y ⟶ Z)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (x : X.obj.left)
    (hf : IsSmoothAt (f ≫ i) x) : IsSmoothAt f x := by
  let T : Opens Z.obj.left := ⟨range i.hom.left.base,hi.base_open.isOpen_range⟩
  have hxT : (f ≫ i).hom.left.base x ∈ T := ⟨f.hom.left.base x,rfl⟩
  obtain ⟨e,r,P,W,hWP,iS,s,hiS,hs,_hsource,htarget,hsq,_hsub,_hideal⟩ :=
    exists_ambient_representation (f ≫ i) x hf ⊤ T (Set.mem_univ _) hxT
  obtain ⟨k,hk,hki⟩ := exists_native_open_lift i (targetInclusion e P) hi
    (targetInclusion_isOpenImmersion e P) htarget
  have hfull : iS ≫ f = nativeProjection e r P W hWP ≫ k := by
    let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono i.hom.left).mp
    have hnative : (iS ≫ f) ≫ i = (nativeProjection e r P W hWP ≫ k) ≫ i :=
      (Category.assoc _ _ _).trans (hsq.trans
        ((congrArg (fun a => nativeProjection e r P W hWP ≫ a) hki.symm).trans
          (Category.assoc _ _ _).symm))
    exact congrArg (fun a => a.hom.left) hnative
  have hsm : IsSmoothAt (nativeProjection e r P W hWP ≫ k) s :=
    isSmoothAt_postcomp_openImmersion (nativeProjection e r P W hWP) k hk s
      (nativeProjection_isSmooth e r P W hWP s)
  have hlocal : IsSmoothAt (iS ≫ f) s := Eq.mp (congrArg (fun a => IsSmoothAt a s) hfull.symm) hsm
  exact Eq.mp (congrArg (fun a => IsSmoothAt f a) hs)
    (isSmoothAt_of_precomp_openImmersion iS f hiS s hlocal)

theorem isSmoothMorphism_of_postcomp_openImmersion (f : X ⟶ Y) (i : Y ⟶ Z)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (hf : IsSmoothMorphism (f ≫ i)) :
    IsSmoothMorphism f := fun x => isSmoothAt_of_postcomp_openImmersion f i hi x (hf x)

/-- Restriction through actual source/target OIs and a full native square preserves smoothness. -/
theorem isSmoothAt_of_open_square (i : A ⟶ X) (j : B ⟶ Y) (f : A ⟶ B) (g : X ⟶ Y)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hsq : i ≫ g = f ≫ j)
    (a : A.obj.left) (hg : IsSmoothAt g (i.hom.left.base a)) : IsSmoothAt f a := by
  have hsm : IsSmoothAt (i ≫ g) a :=
    isSmoothAt_comp i g a (isSmoothMorphism_of_isOpenImmersion i hi a) hg
  exact isSmoothAt_of_postcomp_openImmersion f j hj a
    (Eq.mp (congrArg (fun h => IsSmoothAt h a) hsq) hsm)

theorem isSmoothMorphism_of_open_square (i : A ⟶ X) (j : B ⟶ Y) (f : A ⟶ B) (g : X ⟶ Y)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hsq : i ≫ g = f ≫ j)
    (hg : IsSmoothMorphism g) : IsSmoothMorphism f :=
  fun a => isSmoothAt_of_open_square i j f g hi hj hsq a (hg (i.hom.left.base a))

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality
