import Hironaka.Algebra.PluckerQuotChart
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The actual affine matrix chart with its native split free quotient sheaf

The chart is the literal polynomial spectrum. Its original universal matrix
constructs an actual split quotient of native finite free module sheaves. The
free target is natively locally free; no sheaf quotient or local-freeness
certificate is supplied as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι κ : Type u)
  [Fintype ι] [Fintype κ]

/-- The original universal coefficient ring for the normalized matrix chart. -/
abbrev ChartRing := MvPolynomial (ι × κ) R

/-- The literal affine scheme, with no supplied representing scheme. -/
def affineChart : Scheme.{u} := Spec (.of (ChartRing R ι κ))

/-- The original matrix of polynomial coordinates. -/
def universalMatrix : Matrix ι κ (ChartRing R ι κ) := fun i j ↦ MvPolynomial.X (i, j)

/-- Tilde of an actual finite coordinate module is the native free sheaf on the same indices. -/
def coordinateSheafIsoFree (B : Type u) [CommRing B] (η : Type u) [Finite η] :
    tilde (ModuleCat.of B (η → B)) ≅
      SheafOfModules.free (R := (Spec (.of B)).ringCatSheaf) η :=
  (tilde.functor (.of B)).mapIso (Pi.basisFun B η).repr.toModuleIso ≪≫ tildeFinsupp η

/-- The actual native quotient map on the literal affine polynomial chart. -/
def universalQuotient :
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) (ι ⊕ κ) ⟶
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι :=
  (coordinateSheafIsoFree (ChartRing R ι κ) (ι ⊕ κ)).inv ≫
    (tilde.functor (.of (ChartRing R ι κ))).map
      (ModuleCat.ofHom (matrixQuotient (universalMatrix R ι κ))) ≫
    (coordinateSheafIsoFree (ChartRing R ι κ) ι).hom

/-- The section uses exactly the original pivot coordinates. -/
def universalSection :
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι ⟶
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) (ι ⊕ κ) :=
  (coordinateSheafIsoFree (ChartRing R ι κ) ι).inv ≫
    (tilde.functor (.of (ChartRing R ι κ))).map
      (ModuleCat.ofHom (pivotSection (R := ChartRing R ι κ) (ι := ι) (κ := κ))) ≫
    (coordinateSheafIsoFree (ChartRing R ι κ) (ι ⊕ κ)).hom

/-- The actual free-sheaf quotient is split by the actual original coordinate section. -/
theorem universalSection_quotient : universalSection R ι κ ≫ universalQuotient R ι κ = 𝟙 _ := by
  have hlinear :
      ModuleCat.ofHom (pivotSection (R := ChartRing R ι κ) (ι := ι) (κ := κ)) ≫
        ModuleCat.ofHom (matrixQuotient (universalMatrix R ι κ)) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact matrixQuotient_pivotSection _ v
  dsimp only [universalSection, universalQuotient]
  calc
    _ = (coordinateSheafIsoFree (ChartRing R ι κ) ι).inv ≫
        (tilde.functor (.of (ChartRing R ι κ))).map
          (ModuleCat.ofHom (pivotSection (R := ChartRing R ι κ) (ι := ι) (κ := κ)) ≫
            ModuleCat.ofHom (matrixQuotient (universalMatrix R ι κ))) ≫
        (coordinateSheafIsoFree (ChartRing R ι κ) ι).hom := by
      simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
    _ = 𝟙 _ := by
      rw [hlinear]
      let e := coordinateSheafIsoFree (ChartRing R ι κ) ι
      have hm := (tilde.functor (.of (ChartRing R ι κ))).map_id
        (ModuleCat.of (ChartRing R ι κ) (ι → ChartRing R ι κ))
      apply Eq.trans (congrArg (fun h ↦ e.inv ≫ h ≫ e.hom) hm)
      exact (congrArg (fun h ↦ e.inv ≫ h) (CategoryTheory.Category.id_comp e.hom)).trans
        e.inv_hom_id

instance universalQuotient_isSplitEpi : IsSplitEpi (universalQuotient R ι κ) :=
  ⟨⟨universalSection R ι κ, universalSection_quotient R ι κ⟩⟩

instance universalQuotient_epi : Epi (universalQuotient R ι κ) := inferInstance

/-- The actual target is the native free sheaf on the original finite quotient-rank index. -/
instance universalQuotientTarget_isLocallyFree :
    (SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι).IsLocallyFree := inferInstance

/-- Finiteness is supplied by the actual original finite family of free generators. -/
instance universalQuotientTarget_isFiniteType :
    (SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι).IsFiniteType := by
  let G := SheafOfModules.free.generatingSections
    (R := (affineChart R ι κ).ringCatSheaf) ι
  let : G.IsFiniteType := ⟨by change Finite ι; infer_instance⟩
  constructor
  refine ⟨G.localGeneratorsData, ?_⟩
  constructor
  intro i
  dsimp only [SheafOfModules.GeneratingSections.localGeneratorsData]
  infer_instance

end Hironaka.Geometry.QuotGrassmann
