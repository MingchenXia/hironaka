import Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly
import Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison

/-!
# N2(a): the strict-transform map of one step, read in the geometric blowup

Lane G10GL, run 0081, item GL-3b/N2(a) (`work/hironaka-run0081-20261117/G10GL/GL-3b-4-route.md`).  The flattening
step blows up the base with the native `OriginalFiniteIdealBlowup.sourceObject` (dense unit locus), while the
canonical-chart machinery reads the strict transform through `OriginalFiniteIdealBlowupSquare.inducedMorphism` into
the geometric blowup `OriginalFiniteIdealGeometricBlowup.sourceObject`.  Through the comparison isomorphism
`HironakaG10SbBlowupComparison.blowupIso` (BC3) the two strict-transform maps agree (uniqueness of the induced map):

* `stepP_blowupIso_hom` — `f' ≫ blowupIso.hom = inducedMorphism`;
* `stepP_eq_inducedMorphism_blowupIso_inv` — `f' = inducedMorphism ≫ blowupIso.inv`;
* `stepP_base_eq` — on points.

No named input.
-/

set_option autoImplicit false

open CategoryTheory

namespace Hironaka.Analytic.Unibranch.HironakaG10GlStepSquare

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison

noncomputable section

/-- **The native strict-transform map, read in the geometric blowup, is the induced map.** -/
theorem stepP_blowupIso_hom (s : Stage) (c : AdmissibleCentre s.f) :
    letI := c.finiteType
    (nextWith s c).f ≫ (blowupIso c.B c.b c.dense).hom =
      OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f := by
  let _ := c.finiteType
  have h : strictP c.B c.b c.dense s.f ≫ (blowupIso c.B c.b c.dense).hom =
      OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f := by
    apply OriginalFiniteIdealBlowupSquare.inducedMorphism_unique
    rw [Category.assoc, blowupIso_hom_comp]
    exact strictP_comp c.B c.b c.dense s.f
  exact h

theorem stepP_eq_inducedMorphism_blowupIso_inv (s : Stage) (c : AdmissibleCentre s.f) :
    letI := c.finiteType
    (nextWith s c).f = OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f ≫
      (blowupIso c.B c.b c.dense).inv := by
  let _ := c.finiteType
  have h : strictP c.B c.b c.dense s.f = OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f ≫
      (blowupIso c.B c.b c.dense).inv := by
    have h0 : strictP c.B c.b c.dense s.f ≫ (blowupIso c.B c.b c.dense).hom =
        OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f := stepP_blowupIso_hom s c
    rw [← h0, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact h

/-- On points: `blowupIso (f' y'') = inducedMorphism y''`. -/
theorem stepP_base_eq (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left) :
    letI := c.finiteType
    (blowupIso c.B c.b c.dense).hom.hom.left.base ((nextWith s c).f.hom.left.base y'') =
      (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f).hom.left.base y'' := by
  let _ := c.finiteType
  exact congrArg (fun k => k.hom.left.base y'') (stepP_blowupIso_hom s c)

end

end Hironaka.Analytic.Unibranch.HironakaG10GlStepSquare
