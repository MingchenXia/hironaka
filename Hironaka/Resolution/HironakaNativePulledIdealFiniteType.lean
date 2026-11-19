import Hironaka.Resolution.HironakaLegacyCoherentIdealFiniteType
import Hironaka.Resolution.HironakaNativePulledIdealStalk
import Hironaka.Resolution.HironakaNativeFiniteIdealSections

/-!
# Native finite type of the SAME entire pulled image ideal

No new ideal carrier, scalar action or space category is introduced.
Blueprint FIRST: `hironaka-native-pulled-ideal-finite-type.tex`.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Set AlgebraicGeometry

namespace Hironaka.HironakaNativePulledIdealFiniteType

open HironakaSingularModuleSheafStalk HironakaChowNativeFinitePresentationSpreading
  HironakaLegacyCoherentIdealFiniteType HironakaNativeFiniteIdealSections
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk

variable {X Y : LocallyRingedSpace.{0}} (F : X ⟶ Y)
  (B : SheafOfModules.{0} (forgetRing Y.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.toSheafedSpace.sheaf))

private theorem whole_pulled_span (V : Opens Y.toTopCat) {r : ℕ}
    (s : Fin r → B.val.obj (op V))
    (hspan : ∀ (z : Y) (hz : z ∈ V),
      LinearMap.range (stalkInclusionLinearMap Y.toSheafedSpace.sheaf B b z) =
        Ideal.span (range fun i => Y.presheaf.germ V z hz (b.val.app (op V) (s i))))
    (y : X) (hy : F.base y ∈ V) :
    LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf
      (nativePulledIdealModule F B b) (nativePulledIdealInclusion F B b) y) =
      Ideal.span (range fun i => X.presheaf.germ ((Opens.map F.base).obj V) y hy
        (nativePulledIdealSection F B b V (s i)).val) := by
  calc
    _ = nativePulledIdealStalkIdeal F B b y := nativePulledIdealStalkInclusion_range F B b y
    _ = Ideal.map (F.stalkMap y).hom
        (Ideal.span (range fun i => Y.presheaf.germ V (F.base y) hy
          (b.val.app (op V) (s i)))) :=
      congrArg (Ideal.map (F.stalkMap y).hom) (hspan (F.base y) hy)
    _ = Ideal.span (range fun i => F.stalkMap y
        (Y.presheaf.germ V (F.base y) hy (b.val.app (op V) (s i)))) := by
      rw [Ideal.map_span,← Set.range_comp]
      rfl
    _ = _ := congrArg Ideal.span (congrArg range
      (funext fun i => (nativePulledIdealSection_germ F B b V (s i) y hy).symm))

/-- Finite target sections internally supply actual source epis and ENTIRE spans. -/
theorem exists_local_finite_pulled_generators [B.IsFiniteType] (x : X) :
    ∃ (V : Opens Y.toTopCat) (_hx : F.base x ∈ V) (r : ℕ)
      (s : Fin r → B.val.obj (op V)),
      Epi (freeOverMap X.toSheafedSpace.sheaf (M := nativePulledIdealModule F B b)
        ((Opens.map F.base).obj V)
        (fun i => nativePulledIdealSection F B b V (s i))) ∧
      ∀ (y : X) (hy : F.base y ∈ V),
        LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf
          (nativePulledIdealModule F B b) (nativePulledIdealInclusion F B b) y) =
          Ideal.span (range fun i => X.presheaf.germ ((Opens.map F.base).obj V) y hy
            (nativePulledIdealSection F B b V (s i)).val) := by
  obtain ⟨V,hx,r,s,_hp,hspan⟩ := exists_finite_ideal_sections B b (F.base x)
  have hs := whole_pulled_span F B b V s hspan
  exact ⟨V,hx,r,s,finite_free_epi_of_whole_image_span X.toSheafedSpace.sheaf
    (nativePulledIdealInclusion F B b) (fun _ => Subtype.val_injective)
      ((Opens.map F.base).obj V) (fun i => nativePulledIdealSection F B b V (s i)) hs,hs⟩

/-- STANDARD finite type of the SAME existing source ideal and actual inclusion. -/
theorem nativePulledIdealModule_isFiniteType [B.IsFiniteType] :
    (nativePulledIdealModule F B b).IsFiniteType := by
  classical
  let R := X.toSheafedSpace.sheaf
  let J := nativePulledIdealModule F B b
  choose V hx r s hp hspan using exists_local_finite_pulled_generators F B b
  let U (x : X) := (Opens.map F.base).obj (V x)
  let t (x : X) (i : Fin (r x)) : J.val.obj (op (U x)) :=
    nativePulledIdealSection F B b (V x) (s x i)
  let gs (x : X) : (J.over (U x)).GeneratingSections := by
    letI : Epi (freeOverMap R (M := J) (U x) (t x)) := hp x
    exact (SheafOfModules.free.generatingSections (Fin (r x))).ofEpi
      ((freeOverIso R (U x) (Fin (r x))).hom ≫ freeOverMap R (M := J) (U x) (t x))
  have hgs (x : X) : (gs x).IsFiniteType := ⟨inferInstanceAs (Finite (Fin (r x)))⟩
  let q : J.LocalGeneratorsData.{0} :=
    { I := X
      X := U
      coversTop := by
        intro W
        apply (Opens.mem_grothendieckTopology X.toTopCat).mpr
        intro x hxW
        refine ⟨W ⊓ U x,homOfLE inf_le_left,?_,⟨hxW,hx x⟩⟩
        exact (Sieve.mem_ofObjects_iff U _).mpr ⟨x,⟨homOfLE inf_le_right⟩⟩
      generators := gs }
  exact ⟨⟨q,⟨hgs⟩⟩⟩

end Hironaka.HironakaNativePulledIdealFiniteType
