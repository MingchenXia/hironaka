import Hironaka.Geometry.QuotGrassmannPivotOverlapSheaf
import Hironaka.Geometry.QuotGrassmannPivotPullbackMatrix

/-!
# The original tilde coordinate frame and its actual original basis

These comparisons use exactly the coordinate isomorphism originally used
to construct the normalized universal quotient sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem bundledTildeFinsupp_inclusion (R : CommRingCat.{u}) (I : Type u) (i : I) :
    (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ≫
      (tildeFinsupp I).hom = SheafOfModules.ιFree i := by
  let H : IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R I)) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor fun _ : I ↦ ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor fun _ ↦ SheafOfModules.unit (Spec R).ringCatSheaf :=
    Discrete.natIso (fun _ ↦ tildeSelf)
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv e.symm _).symm H) (coproductIsCoproduct _) (Discrete.mk i)
  change ((tildeSelf (R := R)).inv ≫ (tilde.functor R).map
    (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R)))) ≫
      (tildeFinsupp I).hom = SheafOfModules.ιFree i at h
  calc
    _ = ((tildeSelf (R := R)).inv ≫ (tilde.functor R).map
        (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R)))) ≫
        (tildeFinsupp I).hom := by
      change _ = (𝟙 _ ≫ (tilde.functor R).map
        (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R)))) ≫ _
      exact congrArg (fun k ↦ k ≫ (tildeFinsupp I).hom)
        (Category.id_comp ((tilde.functor R).map
          (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))))).symm
    _ = _ := h

variable (B : Type u) [CommRing B]

/-- The actual native tilde coproduct isomorphism preserves the original finitely-supported inclusions. -/
theorem originalTildeFinsupp_inclusion (I : Type u) (i : I) :
    (tilde.functor (.of B)).map (ModuleCat.ofHom (Finsupp.lsingle i (R := B) (M := B))) ≫
      (tildeFinsupp I).hom = SheafOfModules.ιFree i :=
  bundledTildeFinsupp_inclusion (.of B) I i

/-- The original frozen tilde coordinate isomorphism preserves each original native basis inclusion. -/
theorem originalCoordinateSheafIso_inclusion (I : Type u) [Finite I] [DecidableEq I] (i : I) :
    (tilde.functor (.of B)).map (ModuleCat.ofHom (LinearMap.single B (fun _ : I ↦ B) i)) ≫
      (coordinateSheafIsoFree B I).hom = SheafOfModules.ιFree i := by
  let F := tilde.functor (.of B)
  let l := ModuleCat.ofHom (LinearMap.single B (fun _ : I ↦ B) i)
  let r := (Pi.basisFun B I).repr.toModuleIso.hom
  have hr : l ≫ r = ModuleCat.ofHom (Finsupp.lsingle i (R := B) (M := B)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    ext j
    simp [l, r, Pi.single_apply, Finsupp.single_apply, eq_comm]
  calc
    _ = F.map (l ≫ r) ≫ (tildeFinsupp I).hom := by
      rw [F.map_comp l r]
      rfl
    _ = _ := by
      rw [hr]
      exact originalTildeFinsupp_inclusion B I i

set_option maxHeartbeats 1000000 in
/-- The same original frozen coordinate isomorphism preserves every actual native row projection. -/
theorem originalCoordinateSheafIso_projection (I : Type u) [Finite I] [DecidableEq I] (i : I) :
    (coordinateSheafIsoFree B I).hom ≫ originalFreeProjection (Spec (.of B)) i =
      (tilde.functor (.of B)).map (ModuleCat.ofHom (LinearMap.proj i : (I → B) →ₗ[B] B)) := by
  let F := tilde.functor (.of B)
  let e := coordinateSheafIsoFree B I
  let p := ModuleCat.ofHom (LinearMap.proj i : (I → B) →ₗ[B] B)
  apply (cancel_epi e.inv).mp
  rw [e.inv_hom_id_assoc]
  apply (SheafOfModules.isColimitFreeCofan (R := (Spec (.of B)).ringCatSheaf) I).hom_ext
  intro j
  change SheafOfModules.ιFree j.as ≫ originalFreeProjection (Spec (.of B)) i =
    SheafOfModules.ιFree j.as ≫ e.inv ≫ F.map p
  rw [originalFreeProjection_inclusion, ← originalCoordinateSheafIso_inclusion B I j.as]
  simp only [Category.assoc]
  let l := ModuleCat.ofHom (LinearMap.single B (fun _ : I ↦ B) j.as)
  have hm : l ≫ p = if j.as = i then 𝟙 (ModuleCat.of B B) else 0 := by
    by_cases hji : j.as = i
    · subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      simp [l, p]
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      simp [l, p, hji, Ne.symm hji]
  have hz : (if j.as = i then 𝟙 (SheafOfModules.unit (Spec (.of B)).ringCatSheaf) else 0) =
      F.map (if j.as = i then 𝟙 (ModuleCat.of B B) else 0) := by
    change (if j.as = i then 𝟙 _ else 0) =
      tilde.map (R := CommRingCat.of B) (M := ModuleCat.of B B) (N := ModuleCat.of B B)
        (if j.as = i then 𝟙 (ModuleCat.of B B) else 0)
    split_ifs
    · exact (tilde.map_id (R := CommRingCat.of B) (M := ModuleCat.of B B)).symm
    · exact (tilde.map_zero (R := CommRingCat.of B) (M := ModuleCat.of B B)
        (N := ModuleCat.of B B)).symm
  have hc : F.map l ≫ e.hom ≫ e.inv ≫ F.map p = F.map l ≫ F.map p :=
    congrArg (fun k ↦ F.map l ≫ k) (e.hom_inv_id_assoc (F.map p))
  change (if j.as = i then 𝟙 _ else 0) = F.map l ≫ e.hom ≫ e.inv ≫ F.map p
  calc
    _ = F.map (l ≫ p) := hz.trans (congrArg F.map hm.symm)
    _ = F.map l ≫ F.map p := F.map_comp l p
    _ = _ := hc.symm

set_option maxHeartbeats 1500000 in
/-- The actual original coefficient of a native matrix sheaf map is precisely tilde of multiplication
by the same original matrix entry. -/
theorem originalMatrixQuotientSheaf_coefficient {I E : Type u}
    [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (M : Matrix I E B) (i : I) (j : E) :
    originalFreeHomCoefficient (originalMatrixQuotientSheaf B M) j i =
      tilde.map (R := CommRingCat.of B)
        (ModuleCat.ofHom (LinearMap.mulLeft B (M i j))) := by
  let F := tilde.functor (.of B)
  let s := coordinateSheafIsoFree B E
  let t := coordinateSheafIsoFree B I
  let u := tildeSelf (R := CommRingCat.of B)
  let l := ModuleCat.ofHom (LinearMap.single B (fun _ : E ↦ B) j)
  let p := ModuleCat.ofHom (LinearMap.proj i : (I → B) →ₗ[B] B)
  let q := ModuleCat.ofHom M.mulVecLin
  have hi : F.map l ≫ s.hom = u.hom ≫ SheafOfModules.ιFree j :=
    (originalCoordinateSheafIso_inclusion B E j).trans (Category.id_comp _).symm
  have hp : F.map p ≫ u.hom = t.hom ≫ originalFreeProjection (Spec (.of B)) i :=
    (Category.comp_id (F.map p)).trans (originalCoordinateSheafIso_projection B I i).symm
  have h := originalConjugatedCoefficient F u s t l p q (SheafOfModules.ιFree j)
    (originalFreeProjection (Spec (.of B)) i) hi hp
  have hm : l ≫ q ≫ p = ModuleCat.ofHom (LinearMap.mulLeft B (M i j)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (M.mulVec (Pi.single j b)) i = M i j * b
    exact congrFun (Matrix.mulVec_single M j b) i
  have hu : u.inv ≫ F.map (l ≫ q ≫ p) ≫ u.hom = F.map (l ≫ q ≫ p) := by
    change 𝟙 _ ≫ F.map (l ≫ q ≫ p) ≫ 𝟙 _ = F.map (l ≫ q ≫ p)
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact h.trans (hu.trans (congrArg F.map hm))

end Hironaka.Geometry.QuotGrassmann
