import Hironaka.Geometry.QuotGrassmannPivotGlobalLocalFrames
import Hironaka.Geometry.QuotGrassmannPivotOverRestriction

/-!
# Actual original global-image frames on SAME common over-sites and exact quotient cocycles

Every frame is a genuine native restriction of the internally produced original
global-image frame. Every quotient is the SAME original global quotient restricted
to that SAME common over-site. The identity, three-frame composition, and quotient
triangles are exact native equalities, without any coherence input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalNativeTransition_self {C : Type*} [Category C]
    {M N : C} (a : M ≅ N) : a.symm ≪≫ a = Iso.refl N := by
  apply Iso.ext
  exact a.inv_hom_id

private theorem originalNativeTransition_comp {C : Type*} [Category C]
    {M A B D : C} (a : M ≅ A) (b : M ≅ B) (c : M ≅ D) :
    (a.symm ≪≫ b) ≪≫ (b.symm ≪≫ c) = a.symm ≪≫ c := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, b.hom_inv_id_assoc]

private theorem originalNativeTransition_quotient {C : Type*} [Category C]
    {S M A B : C} (q : S ⟶ M) (a : M ≅ A) (b : M ≅ B) :
    (q ≫ a.hom) ≫ (a.symm ≪≫ b).hom = q ≫ b.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, a.hom_inv_id_assoc]

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- Restrict the SAME actual original global-image frame to a literal SAME native common over-site. -/
def originalGlobalImageCommonFrame (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j))
    (W : (projectiveModel R ι ν).Opens) (hW : W ≤ coordinateOpen R ι ν j) :
    (originalGlobalImageQuotient R ι ν).over W ≅
      SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf.over W) ι :=
  ((SheafOfModules.overFunctorMap (projectiveModel R ι ν).ringCatSheaf
      (homOfLE hW)).app (originalGlobalImageQuotient R ι ν)).symm ≪≫
    (SheafOfModules.overMap.{u} (projectiveModel R ι ν).ringCatSheaf (homOfLE hW)).mapIso
      (actualOriginalGlobalImageFrame R ι ν j hj) ≪≫
    (originalOverMapFreeIso (projectiveModel R ι ν) (homOfLE hW) ι).symm

/-- The SAME original native global quotient, on its SAME literal common over-site and actual frame. -/
def originalGlobalImageCommonQuotient (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j))
    (W : (projectiveModel R ι ν).Opens) (hW : W ≤ coordinateOpen R ι ν j) :
    (SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν)).over W ⟶
      SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf.over W) ι :=
  (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf W).map
    (originalGlobalQuotient R ι ν) ≫ (originalGlobalImageCommonFrame R ι ν j hj W hW).hom

/-- The actual SAME-common-site native transition is internally produced from the SAME global object. -/
def originalGlobalImageCommonTransition
    (j k : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j))
    (hk : Function.Injective (coordinateSelector ι ν k))
    (W : (projectiveModel R ι ν).Opens)
    (hWj : W ≤ coordinateOpen R ι ν j) (hWk : W ≤ coordinateOpen R ι ν k) :
    SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf.over W) ι ≅
      SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf.over W) ι :=
  (originalGlobalImageCommonFrame R ι ν j hj W hWj).symm ≪≫
    originalGlobalImageCommonFrame R ι ν k hk W hWk

/-- Identity holds for the actual original native frame restriction on every SAME original common open. -/
theorem originalGlobalImageCommonTransition_self
    (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j))
    (W : (projectiveModel R ι ν).Opens) (hWj : W ≤ coordinateOpen R ι ν j) :
    originalGlobalImageCommonTransition R ι ν j j hj hj W hWj hWj = Iso.refl _ :=
  originalNativeTransition_self (originalGlobalImageCommonFrame R ι ν j hj W hWj)

/-- Exact three-frame cocycle holds on every literal SAME original native common over-site. -/
theorem originalGlobalImageCommonTransition_comp
    (j k l : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j))
    (hk : Function.Injective (coordinateSelector ι ν k))
    (hl : Function.Injective (coordinateSelector ι ν l))
    (W : (projectiveModel R ι ν).Opens)
    (hWj : W ≤ coordinateOpen R ι ν j) (hWk : W ≤ coordinateOpen R ι ν k)
    (hWl : W ≤ coordinateOpen R ι ν l) :
    originalGlobalImageCommonTransition R ι ν j k hj hk W hWj hWk ≪≫
      originalGlobalImageCommonTransition R ι ν k l hk hl W hWk hWl =
        originalGlobalImageCommonTransition R ι ν j l hj hl W hWj hWl :=
  originalNativeTransition_comp
    (originalGlobalImageCommonFrame R ι ν j hj W hWj)
    (originalGlobalImageCommonFrame R ι ν k hk W hWk)
    (originalGlobalImageCommonFrame R ι ν l hl W hWl)

/-- The exact original native transition preserves the SAME actual native original common-source quotient. -/
theorem originalGlobalImageCommonTransition_quotient
    (j k : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j))
    (hk : Function.Injective (coordinateSelector ι ν k))
    (W : (projectiveModel R ι ν).Opens)
    (hWj : W ≤ coordinateOpen R ι ν j) (hWk : W ≤ coordinateOpen R ι ν k) :
    originalGlobalImageCommonQuotient R ι ν j hj W hWj ≫
      (originalGlobalImageCommonTransition R ι ν j k hj hk W hWj hWk).hom =
        originalGlobalImageCommonQuotient R ι ν k hk W hWk :=
  originalNativeTransition_quotient
    ((SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf W).map
      (originalGlobalQuotient R ι ν))
    (originalGlobalImageCommonFrame R ι ν j hj W hWj)
    (originalGlobalImageCommonFrame R ι ν k hk W hWk)

/-- These are actual native transitions on the SAME literal original pair intersection. -/
def originalGlobalImagePairTransition
    (j k : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j))
    (hk : Function.Injective (coordinateSelector ι ν k)) :=
  originalGlobalImageCommonTransition R ι ν j k hj hk
    (coordinateOpen R ι ν j ⊓ coordinateOpen R ι ν k) inf_le_left inf_le_right

end Hironaka.Geometry.QuotGrassmann
