import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupUniversal
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupUniversal

/-!
# The native and the geometric blowup of a dense finite-type ideal agree (G10-02-10.a, bridge BC3)

Lane G10SB, run 0081 (route `G10SB/G10-02-10a-pulled-family-route.md`).  The flattening step blows up the base with
`OriginalFiniteIdealBlowup.sourceObject B b hDense` (dense unit locus), while the canonical-chart machinery of the
strict transform uses `OriginalFiniteIdealGeometricBlowup.sourceObject B b`.  Both carry rank-one data on the WHOLE
pulled ideal and the full universal property for such data, so they are isomorphic over the base:

* `toGeometric`, `toNative` — the two lifts; `toGeometric_comp`, `toNative_comp`;
* `blowupIso` — the isomorphism over `X` (`blowupIso_hom_comp`, `blowupIso_inv_comp`).

No analytic input; no named input.
-/

set_option autoImplicit false

open CategoryTheory

namespace Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison

open Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})

theorem exists_unique_toGeometric :
    ∃! L : OriginalFiniteIdealBlowup.sourceObject B b hDense ⟶
        OriginalFiniteIdealGeometricBlowup.sourceObject B b,
      L ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
        OriginalFiniteIdealBlowup.projectionMorphism B b hDense := by
  obtain ⟨q, hq, hu⟩ :=
    OriginalFiniteIdealBlowupUniversal.projection_ideal_exists_locallyFreeData B b hDense
  have := hq
  have : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (hu i)
  exact OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData B b _
    (OriginalFiniteIdealBlowup.projectionMorphism B b hDense) q

theorem exists_unique_toNative :
    ∃! L : OriginalFiniteIdealGeometricBlowup.sourceObject B b ⟶
        OriginalFiniteIdealBlowup.sourceObject B b hDense,
      L ≫ OriginalFiniteIdealBlowup.projectionMorphism B b hDense =
        OriginalFiniteIdealGeometricBlowup.projectionMorphism B b := by
  obtain ⟨q, hq, hu⟩ :=
    OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_exists_locallyFreeData B b
  have := hq
  have : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (hu i)
  exact OriginalFiniteIdealBlowupUniversal.exists_unique_lift_of_locallyFreeData B b hDense _
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b) q

/-- The lift of the native blowup through the geometric one. -/
def toGeometric : OriginalFiniteIdealBlowup.sourceObject B b hDense ⟶
    OriginalFiniteIdealGeometricBlowup.sourceObject B b :=
  Classical.choose (exists_unique_toGeometric B b hDense).exists

/-- The lift of the geometric blowup through the native one. -/
def toNative : OriginalFiniteIdealGeometricBlowup.sourceObject B b ⟶
    OriginalFiniteIdealBlowup.sourceObject B b hDense :=
  Classical.choose (exists_unique_toNative B b hDense).exists

theorem toGeometric_comp : toGeometric B b hDense ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
    OriginalFiniteIdealBlowup.projectionMorphism B b hDense :=
  Classical.choose_spec (exists_unique_toGeometric B b hDense).exists

theorem toNative_comp : toNative B b hDense ≫ OriginalFiniteIdealBlowup.projectionMorphism B b hDense =
    OriginalFiniteIdealGeometricBlowup.projectionMorphism B b :=
  Classical.choose_spec (exists_unique_toNative B b hDense).exists

theorem toGeometric_toNative : toGeometric B b hDense ≫ toNative B b hDense = 𝟙 _ := by
  obtain ⟨q, hq, hu⟩ :=
    OriginalFiniteIdealBlowupUniversal.projection_ideal_exists_locallyFreeData B b hDense
  have := hq
  have : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (hu i)
  have h := OriginalFiniteIdealBlowupUniversal.exists_unique_lift_of_locallyFreeData B b hDense _
    (OriginalFiniteIdealBlowup.projectionMorphism B b hDense) q
  exact h.unique (by rw [Category.assoc, toNative_comp, toGeometric_comp]) (Category.id_comp _)

theorem toNative_toGeometric : toNative B b hDense ≫ toGeometric B b hDense = 𝟙 _ := by
  obtain ⟨q, hq, hu⟩ :=
    OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_exists_locallyFreeData B b
  have := hq
  have : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (hu i)
  have h := OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData B b _
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b) q
  exact h.unique (by rw [Category.assoc, toGeometric_comp, toNative_comp]) (Category.id_comp _)

/-- **BC3.**  The native and the geometric blowup of a dense finite-type ideal are isomorphic over the base. -/
def blowupIso : OriginalFiniteIdealBlowup.sourceObject B b hDense ≅
    OriginalFiniteIdealGeometricBlowup.sourceObject B b where
  hom := toGeometric B b hDense
  inv := toNative B b hDense
  hom_inv_id := toGeometric_toNative B b hDense
  inv_hom_id := toNative_toGeometric B b hDense

theorem blowupIso_hom_comp : (blowupIso B b hDense).hom ≫
    OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      OriginalFiniteIdealBlowup.projectionMorphism B b hDense :=
  toGeometric_comp B b hDense

theorem blowupIso_inv_comp : (blowupIso B b hDense).inv ≫
    OriginalFiniteIdealBlowup.projectionMorphism B b hDense =
      OriginalFiniteIdealGeometricBlowup.projectionMorphism B b :=
  toNative_comp B b hDense

end

end Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison
