import Hironaka.Resolution.HironakaChowNativeGeneratorNeighborhood
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-! Standard native finite type supplies actual finite ideal sections on ONE
original open, spanning the ENTIRE actual inclusion-stalk image at ALL points.
No reduced ideal or source-model dictionary is assumed. Blueprint FIRST:
`hironaka-native-finite-ideal-sections.tex`. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace Set AlgebraicGeometry

namespace Hironaka.HironakaNativeFiniteIdealSections

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeGeneratorNeighborhood

variable {X : LocallyRingedSpace.{0}}
  (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf))

/-- An ACTUAL whole finite-generator epi gives the ENTIRE original image ideal
at EVERY original point, with the original section germs and native action. -/
theorem stalk_image_eq_span_of_epi (U : Opens X.toTopCat) {r : ℕ}
    (s : Fin r → B.val.obj (op U))
    [Epi (freeOverMap X.toSheafedSpace.sheaf U s)] (y : X) (hy : y ∈ U) :
    LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b y) =
      Ideal.span (Set.range fun i => X.presheaf.germ U y hy (b.val.app (op U) (s i))) := by
  let R := X.toSheafedSpace.sheaf
  let e := finiteFreeStalkLinearEquiv R (Fin r) y
  let p := stalkLinearMapOfOver R U (freeOverMap R U s) y hy
  let c := p.comp e.symm.toLinearMap
  let k := stalkInclusionLinearMap R B b y
  let I := Ideal.span (Set.range fun i => X.presheaf.germ U y hy (b.val.app (op U) (s i)))
  have hc : Function.Surjective c :=
    (stalkLinearMapOfOver_surjective_of_epi R U (freeOverMap R U s) y hy).comp e.symm.surjective
  have hsingle (i : Fin r) : c (Pi.single i 1) = TopCat.Presheaf.germ B.val.presheaf U y hy (s i) := by
    have he : e.symm (Pi.single i 1) =
        stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val y
          ((unitStalkLinearEquiv R y).symm 1) :=
      e.symm_apply_eq.mpr (finiteFreeStalkLinearEquiv_ι R (Fin r) y i 1).symm
    change p (e.symm (Pi.single i 1)) = _
    rw [he, freeOverMap_stalk_ι, one_smul]
  have hgen (v : Fin r → ↑(TopCat.Presheaf.stalk R.obj y)) : k (c v) ∈ I := by
    rw [← Finset.univ_sum_single v, map_sum, map_sum]
    apply I.sum_mem
    intro i _hi
    have hv : Pi.single i (v i) =
        v i • Pi.single i (1 : ↑(TopCat.Presheaf.stalk R.obj y)) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    rw [hv, map_smul, map_smul, hsingle]
    change v i • k (TopCat.Presheaf.germ B.val.presheaf U y hy (s i)) ∈ I
    rw [stalkInclusionLinearMap_germ]
    exact I.smul_mem _ (Ideal.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · rintro a ⟨m, rfl⟩
    obtain ⟨v, rfl⟩ := hc m
    exact hgen v
  · apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    exact ⟨TopCat.Presheaf.germ B.val.presheaf U y hy (s i),
      stalkInclusionLinearMap_germ R B b y U hy (s i)⟩

/-- STANDARD native finite type internally derives a finite family on ONE
actual original open and its ENTIRE actual image-ideal dictionary at ALL points. -/
theorem exists_finite_ideal_sections [B.IsFiniteType] (x : X) :
    ∃ (U : Opens X.toTopCat) (_hx : x ∈ U) (r : ℕ) (s : Fin r → B.val.obj (op U)),
      Epi (freeOverMap X.toSheafedSpace.sheaf U s) ∧
      ∀ (y : X) (hy : y ∈ U),
        LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b y) =
          Ideal.span (Set.range fun i => X.presheaf.germ U y hy (b.val.app (op U) (s i))) := by
  let R := X.toSheafedSpace.sheaf
  have : Module.Finite ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk B.val.presheaf x) :=
    moduleFinite_stalk_of_isFiniteType R x
  obtain ⟨r, v, hv⟩ := Module.Finite.exists_fin (R := ↑(TopCat.Presheaf.stalk R.obj x))
    (M := ↑(TopCat.Presheaf.stalk B.val.presheaf x))
  obtain ⟨U, hx, s, _hs, hp⟩ := exists_local_generators_with_original_germs R x v hv
  have : Epi (freeOverMap R U s) := hp
  exact ⟨U, hx, r, s, hp, fun y hy => stalk_image_eq_span_of_epi B b U s y hy⟩

end Hironaka.HironakaNativeFiniteIdealSections
