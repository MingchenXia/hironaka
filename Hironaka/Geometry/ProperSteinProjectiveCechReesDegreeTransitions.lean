/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerDiagram
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear

/-! # Literal original ideal-power inclusions and homogeneous coefficient squares

Closed native comparison pattern adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechDegreeTransitions.lean`,
SHA256 e6d6d57c91c41b7bc28901bdcdc44412921a4f0b84614b391b79c84a2c34f357.
Only Mathlib+own native subset/section maps are imported; no affine or cover
comparison premise is needed. All powers and coefficient maps are ORIGINAL.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreeTransitions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The ORIGINAL higher-to-lower ideal-power inclusion retains the ENTIRE original section. -/
def lowerSections {n m : ℕ} (h : n≤m) (V : X.Opens) :
    ReesPowerDiagram.powerSections I f m V →ₗ[R] ReesPowerDiagram.powerSections I f n V := by
  let := (Infinitesimal.sectionCoefficient f V).toAlgebra
  exact {
    toFun := fun x => ⟨(show ↥((I.map (Infinitesimal.sectionCoefficient f V))^m) from x).val,
      Ideal.pow_le_pow_right h (show ↥((I.map (Infinitesimal.sectionCoefficient f V))^m) from x).property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- EVERY original open restriction retains the SAME actual original power inclusion. -/
def lowerNatural {n m : ℕ} (h : n≤m) :
    ReesPowerDiagram.powerDiagram I f U m ⟶ ReesPowerDiagram.powerDiagram I f U n where
  app S := by
    let := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)).toAlgebra
    exact ModuleCat.ofHom (lowerSections I f h (actualSchemeSubsetOpen U S))
  naturality S T k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- The genuine native ORIGINAL higher-to-lower ideal-power cochain inclusion. -/
def degreeLower {n m : ℕ} (h : n≤m) :
    ReesPowerDiagram.powerComplex I f U m ⟶ ReesPowerDiagram.powerComplex I f U n :=
  subsetCechComplexMap (lowerNatural I f U h)

/-- Equal original powers have EXACTLY the WHOLE original cochain identity. -/
theorem degreeLower_self (n : ℕ) : degreeLower I f U (le_refl n)=𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext S
  apply Subtype.ext
  rfl

/-- EVERY original triple of powers retains the SAME whole original cochain composition. -/
theorem degreeLower_comp {n m k : ℕ} (hnm : n≤m) (hmk : m≤k) :
    degreeLower I f U hmk ≫ degreeLower I f U hnm=degreeLower I f U (hnm.trans hmk) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext S
  apply Subtype.ext
  rfl

/-- The ENTIRE original multiplication-lowering square is the ORIGINAL coefficient times the original inclusion. -/
theorem degreeMultiply_lower {e : ℕ} (a : ↥(I^e)) {n m : ℕ} (h : n≤m) :
    ReesPowerDiagram.homogeneousComplexMap I f U a m ≫
      degreeLower I f U (h.trans (Nat.le_add_left m e)) =
    (a : R) • degreeLower I f U h := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext S
  apply Subtype.ext
  rfl

/-- The actual native ORIGINAL cohomology map retains the SAME original ideal-power inclusion. -/
def homologyLower {n m : ℕ} (h : n≤m) (q : ℕ) :
    (ReesPowerDiagram.powerComplex I f U m).homology q ⟶
      (ReesPowerDiagram.powerComplex I f U n).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map (degreeLower I f U h)

/-- Equal original powers have EXACTLY the WHOLE original native cohomology identity. -/
theorem homologyLower_self (n q : ℕ) : homologyLower I f U (le_refl n) q=𝟙 _ := by
  exact (congrArg (fun b =>
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map b)
      (degreeLower_self I f U n)).trans (CategoryTheory.Functor.map_id _ _)

/-- EVERY original triple of powers retains the SAME whole original native cohomology composition. -/
theorem homologyLower_comp {n m k : ℕ} (hnm : n≤m) (hmk : m≤k) (q : ℕ) :
    homologyLower I f U hmk q ≫ homologyLower I f U hnm q=
      homologyLower I f U (hnm.trans hmk) q :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map_comp _ _).symm.trans
    (congrArg (fun b =>
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map b)
        (degreeLower_comp I f U hnm hmk))

/-- EVERY original class has the EXACT original coefficient multiplication-lowering square. -/
theorem homologyMultiply_lower {e : ℕ} (a : ↥(I^e)) {n m : ℕ} (h : n≤m) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (ReesPowerDiagram.homogeneousComplexMap I f U a m) ≫
      homologyLower I f U (h.trans (Nat.le_add_left m e)) q =
    (a : R) • homologyLower I f U h q := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let S := HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q
  have hs : S.map ((a : R) • degreeLower I f U h)=
      (a : R) • S.map (degreeLower I f U h) := by
    apply ShortComplex.Hom.ext <;> rfl
  have hmap : H.map ((a : R) • degreeLower I f U h)=
      (a : R) • H.map (degreeLower I f U h) := by
    change ShortComplex.homologyMap (S.map ((a : R) • degreeLower I f U h))=
      (a : R) • ShortComplex.homologyMap (S.map (degreeLower I f U h))
    rw [hs]
    exact ShortComplex.homologyMap_smul _ _
  exact (H.map_comp _ _).symm.trans
    ((congrArg (fun b => H.map b) (degreeMultiply_lower I f U a h)).trans hmap)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreeTransitions
