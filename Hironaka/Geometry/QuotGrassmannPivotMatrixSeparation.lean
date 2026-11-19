import Hironaka.Geometry.QuotGrassmannPivotPullbackMatrix

/-!
# Actual native finite-free matrix separation

The original finite target projections sum to the identity. The original
map is therefore determined by its original coordinate endomorphisms,
and unit-sheaf endomorphisms are determined by their values at one on all
actual original opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual finite original projection/inclusion sum is the entire native identity. -/
theorem originalFreeProjection_sum (X : Scheme.{u}) (J : Type u) [Fintype J] [DecidableEq J] :
    ∑ j : J, originalFreeProjection X j ≫ SheafOfModules.ιFree j =
      𝟙 (SheafOfModules.free (R := X.ringCatSheaf) J) := by
  apply (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) J).hom_ext
  intro j
  change SheafOfModules.ιFree j.as ≫ _ = SheafOfModules.ιFree j.as ≫ 𝟙 _
  simp [Preadditive.comp_sum, ← Category.assoc, originalFreeProjection_inclusion]
  rw [Finset.sum_eq_single j.as]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Equality of the actual original coefficient endomorphisms implies equality of the entire maps. -/
theorem originalFreeHomCoefficient_injective (X : Scheme.{u}) {I J : Type u}
    [Fintype J] [DecidableEq J]
    {q r : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J}
    (h : ∀ i j, originalFreeHomCoefficient q i j = originalFreeHomCoefficient r i j) : q = r := by
  apply (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I).hom_ext
  intro i
  change SheafOfModules.ιFree i.as ≫ q = SheafOfModules.ιFree i.as ≫ r
  calc
    _ = SheafOfModules.ιFree i.as ≫ q ≫ ∑ j : J,
        originalFreeProjection X j ≫ SheafOfModules.ιFree j := by
      rw [originalFreeProjection_sum, Category.comp_id]
    _ = ∑ j : J, originalFreeHomCoefficient q i.as j ≫ SheafOfModules.ιFree j := by
      simp only [Preadditive.comp_sum, originalFreeHomCoefficient, Category.assoc]
    _ = ∑ j : J, originalFreeHomCoefficient r i.as j ≫ SheafOfModules.ιFree j := by
      simp_rw [h]
    _ = SheafOfModules.ιFree i.as ≫ r := by
      simp only [originalFreeHomCoefficient, Category.assoc, ← Preadditive.comp_sum]
      rw [originalFreeProjection_sum, Category.comp_id]

/-- An actual native unit endomorphism is determined by its precise values at one on all original opens. -/
theorem originalUnitEnd_ext_one (X : Scheme.{u})
    {b c : End (SheafOfModules.unit X.ringCatSheaf)}
    (h : ∀ U : X.Opens, b.val.app (.op U) (1 : Γ(X, U)) = c.val.app (.op U) (1 : Γ(X, U))) :
    b = c := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  apply Subtype.ext
  funext U
  exact h U.unop

/-- Equality of all actual original coefficient values at one proves equality of the entire native maps. -/
theorem originalFreeHomCoefficient_ext_one (X : Scheme.{u}) {I J : Type u}
    [Fintype J] [DecidableEq J]
    {q r : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J}
    (h : ∀ i j (U : X.Opens),
      (originalFreeHomCoefficient q i j).val.app (.op U) (1 : Γ(X, U)) =
        (originalFreeHomCoefficient r i j).val.app (.op U) (1 : Γ(X, U))) : q = r :=
  originalFreeHomCoefficient_injective X (fun i j ↦ originalUnitEnd_ext_one X (h i j))

/-- For an actual open immersion, original inverse-image opens suffice to separate the whole maps. -/
theorem originalFreeHomCoefficient_ext_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {I J : Type u} [Fintype J] [DecidableEq J]
    {q r : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J}
    (h : ∀ i j (U : Y.Opens),
      (originalFreeHomCoefficient q i j).val.app (.op (f ⁻¹ᵁ U)) (1 : Γ(X, f ⁻¹ᵁ U)) =
        (originalFreeHomCoefficient r i j).val.app (.op (f ⁻¹ᵁ U)) (1 : Γ(X, f ⁻¹ᵁ U))) : q = r := by
  apply originalFreeHomCoefficient_ext_one X
  intro i j V
  exact Eq.mp (congrArg (fun W : X.Opens ↦
    (originalFreeHomCoefficient q i j).val.app (.op W) (1 : Γ(X, W)) =
      (originalFreeHomCoefficient r i j).val.app (.op W) (1 : Γ(X, W)))
        (f.preimage_image_eq V)) (h i j (f ''ᵁ V))

/-- Each original unit coefficient is the genuine restriction of its original global value. -/
theorem originalUnitEnd_one_restrict (X : Scheme.{u})
    (b : End (SheafOfModules.unit X.ringCatSheaf)) (U : X.Opens) :
    X.presheaf.map U.leTop.op (b.val.app (.op ⊤) (1 : Γ(X, ⊤))) =
      b.val.app (.op U) (1 : Γ(X, U)) := by
  have h := ConcreteCategory.congr_hom (b.val.naturality U.leTop.op) (1 : Γ(X, ⊤))
  change b.val.app (.op U) (X.presheaf.map U.leTop.op (1 : Γ(X, ⊤))) =
    X.presheaf.map U.leTop.op (b.val.app (.op ⊤) (1 : Γ(X, ⊤))) at h
  have hone : X.presheaf.map U.leTop.op (1 : Γ(X, ⊤)) = (1 : Γ(X, U)) := map_one _
  rw [hone] at h
  exact h.symm

/-- The true original value at one on the global open determines an actual unit endomorphism. -/
theorem originalUnitEnd_ext_one_top (X : Scheme.{u})
    {b c : End (SheafOfModules.unit X.ringCatSheaf)}
    (h : b.val.app (.op ⊤) (1 : Γ(X, ⊤)) = c.val.app (.op ⊤) (1 : Γ(X, ⊤))) : b = c := by
  apply originalUnitEnd_ext_one X
  intro U
  exact (originalUnitEnd_one_restrict X b U).symm.trans
    ((congrArg (X.presheaf.map U.leTop.op) h).trans (originalUnitEnd_one_restrict X c U))

/-- Every entire original finite-free map is determined by its genuine global coefficient values. -/
theorem originalFreeHomCoefficient_ext_top (X : Scheme.{u}) {I J : Type u}
    [Fintype J] [DecidableEq J]
    {q r : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J}
    (h : ∀ i j, (originalFreeHomCoefficient q i j).val.app (.op ⊤) (1 : Γ(X, ⊤)) =
      (originalFreeHomCoefficient r i j).val.app (.op ⊤) (1 : Γ(X, ⊤))) : q = r :=
  originalFreeHomCoefficient_injective X (fun i j ↦ originalUnitEnd_ext_one_top X (h i j))

/-- An actual top open in any original spelling suffices to identify the whole original maps. -/
theorem originalFreeHomCoefficient_ext_eq_top (X : Scheme.{u}) {I J : Type u}
    [Fintype J] [DecidableEq J]
    {q r : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J} (W : X.Opens) (hW : W = ⊤)
    (h : ∀ i j, (originalFreeHomCoefficient q i j).val.app (.op W) (1 : Γ(X, W)) =
      (originalFreeHomCoefficient r i j).val.app (.op W) (1 : Γ(X, W))) : q = r := by
  apply originalFreeHomCoefficient_ext_top X
  intro i j
  exact Eq.mp (congrArg (fun V : X.Opens ↦
    (originalFreeHomCoefficient q i j).val.app (.op V) (1 : Γ(X, V)) =
      (originalFreeHomCoefficient r i j).val.app (.op V) (1 : Γ(X, V))) hW) (h i j)

end Hironaka.Geometry.QuotGrassmann
