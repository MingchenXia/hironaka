import Hironaka.Geometry.QuotGrassmannPivotMatrixSeparation

/-!
# Original over-site finite-free projections and coefficient faithfulness

All coefficients are actual native unit endomorphisms on the original over-site.
The original terminal open determines those whole morphisms by actual restriction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original finite-free projection on the actual native over-site. -/
def originalOverFreeProjection (X : Scheme.{u}) (U : X.Opens)
    {I : Type u} [DecidableEq I] (i : I) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf.over U) I).desc
    (Cofan.mk _ (fun j => if j = i then 𝟙 _ else 0))

/-- The original over-site projection has its actual Kronecker basis entries. -/
theorem originalOverFreeProjection_inclusion (X : Scheme.{u}) (U : X.Opens)
    {I : Type u} [DecidableEq I] (i j : I) :
    SheafOfModules.ιFree j ≫ originalOverFreeProjection X U i =
      if j = i then 𝟙 _ else 0 :=
  (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf.over U) I).fac _ (Discrete.mk j)

/-- The whole actual original finite-free identity is the sum of its actual projections. -/
theorem originalOverFreeProjection_sum (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Fintype I] [DecidableEq I] :
    ∑ i : I, originalOverFreeProjection X U i ≫ SheafOfModules.ιFree i =
      𝟙 (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  apply (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf.over U) I).hom_ext
  intro i
  change SheafOfModules.ιFree i.as ≫ _ = SheafOfModules.ιFree i.as ≫ 𝟙 _
  simp [Preadditive.comp_sum, ← Category.assoc, originalOverFreeProjection_inclusion]
  rw [Finset.sum_eq_single i.as]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Actual over-site free target projections separate all whole native sheaf maps. -/
theorem originalOverFreeProjection_hom_ext (X : Scheme.{u}) (U : X.Opens)
    {I : Type u} [Fintype I] [DecidableEq I]
    {M : SheafOfModules (X.ringCatSheaf.over U)}
    {f g : M ⟶ SheafOfModules.free (R := X.ringCatSheaf.over U) I}
    (h : ∀ i, f ≫ originalOverFreeProjection X U i = g ≫ originalOverFreeProjection X U i) :
    f = g := by
  calc
    f = f ≫ ∑ i : I, originalOverFreeProjection X U i ≫ SheafOfModules.ιFree i := by
      rw [originalOverFreeProjection_sum, Category.comp_id]
    _ = ∑ i : I, (f ≫ originalOverFreeProjection X U i) ≫ SheafOfModules.ιFree i := by
      simp only [Preadditive.comp_sum, Category.assoc]
    _ = ∑ i : I, (g ≫ originalOverFreeProjection X U i) ≫ SheafOfModules.ιFree i := by
      simp_rw [h]
    _ = g := by
      simp only [Category.assoc, ← Preadditive.comp_sum]
      rw [originalOverFreeProjection_sum, Category.comp_id]

/-- The literal terminal object of the original over-site is the same original open. -/
abbrev originalOverTop (X : Scheme.{u}) (U : X.Opens) : Over U := Over.mk (𝟙 U)

/-- Every original over-site open has its actual restriction to the original terminal open. -/
def originalOverToTop (X : Scheme.{u}) (U : X.Opens) (V : Over U) :
    V ⟶ originalOverTop X U := Over.homMk V.hom

/-- Whole actual over-site unit endomorphisms are determined by their actual values on one. -/
theorem originalOverUnitEnd_ext_one (X : Scheme.{u}) (U : X.Opens)
    {b c : End (SheafOfModules.unit (X.ringCatSheaf.over U))}
    (h : ∀ V : Over U, b.val.app (.op V) (1 : Γ(X, V.left)) =
      c.val.app (.op V) (1 : Γ(X, V.left))) : b = c := by
  apply (SheafOfModules.unit (X.ringCatSheaf.over U)).unitHomEquiv.injective
  apply Subtype.ext
  funext V
  exact h V.unop

/-- The actual value at one restricts from the same original terminal open. -/
theorem originalOverUnitEnd_one_restrict (X : Scheme.{u}) (U : X.Opens)
    (b : End (SheafOfModules.unit (X.ringCatSheaf.over U))) (V : Over U) :
    X.presheaf.map V.hom.op
        (b.val.app (.op (originalOverTop X U)) (1 : Γ(X, U))) =
      b.val.app (.op V) (1 : Γ(X, V.left)) := by
  have h := ConcreteCategory.congr_hom
    (b.val.naturality (originalOverToTop X U V).op) (1 : Γ(X, U))
  change b.val.app (.op V) (X.presheaf.map V.hom.op (1 : Γ(X, U))) =
    X.presheaf.map V.hom.op
      (b.val.app (.op (originalOverTop X U)) (1 : Γ(X, U))) at h
  have hone : X.presheaf.map V.hom.op (1 : Γ(X, U)) = (1 : Γ(X, V.left)) := map_one _
  rw [hone] at h
  exact h.symm

/-- Actual original terminal values determine whole native over-site unit endomorphisms. -/
theorem originalOverUnitEnd_ext_one_top (X : Scheme.{u}) (U : X.Opens)
    {b c : End (SheafOfModules.unit (X.ringCatSheaf.over U))}
    (h : b.val.app (.op (originalOverTop X U)) (1 : Γ(X, U)) =
      c.val.app (.op (originalOverTop X U)) (1 : Γ(X, U))) : b = c := by
  apply originalOverUnitEnd_ext_one X U
  intro V
  exact (originalOverUnitEnd_one_restrict X U b V).symm.trans
    ((congrArg (X.presheaf.map V.hom.op) h).trans
      (originalOverUnitEnd_one_restrict X U c V))

/-- Evaluation of an actual original over-site unit endomorphism at its original global one. -/
def originalOverUnitCoefficient (X : Scheme.{u}) (U : X.Opens) :
    End (SheafOfModules.unit (X.ringCatSheaf.over U)) →+ Γ(X, U) where
  toFun b := b.val.app (.op (originalOverTop X U)) (1 : Γ(X, U))
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Native over-site endomorphism composition has its exact original scalar product coefficient. -/
theorem originalOverUnitEnd_comp_one_top (X : Scheme.{u}) (U : X.Opens)
    (b c : End (SheafOfModules.unit (X.ringCatSheaf.over U))) :
    originalOverUnitCoefficient X U (b ≫ c) =
      originalOverUnitCoefficient X U b * originalOverUnitCoefficient X U c := by
  let v : Γ(X, U) := originalOverUnitCoefficient X U b
  let f : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) := (c.val.app (.op (originalOverTop X U))).hom
  have h := f.map_smul v (1 : Γ(X, U))
  change f (v * 1) = v * f (1 : Γ(X, U)) at h
  exact (congrArg f (mul_one v).symm).trans h

end Hironaka.Geometry.QuotGrassmann
