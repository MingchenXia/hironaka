import Hironaka.Analytic.Unibranch.HironakaG10GlPresentationTransport
import Hironaka.Analytic.Unibranch.HironakaG10GlStepSquare
import Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison

/-!
# The `hpres` binder from generic presentations over the geometric blowup (Stage level)

Lane G10S1, run 0081 (splittable item S1 of lane G10HP, `work/hironaka-run0081-20261117/G10HP/STATUS.md`;
blueprint `hironaka-g10gl-presentation.tex`).  A flattening step blows up the base with the NATIVE blowup
`OriginalFiniteIdealBlowup.sourceObject` (dense unit locus), while the canonical-chart machinery reads the strict
transform over the GEOMETRIC blowup `OriginalFiniteIdealGeometricBlowup.sourceObject` through
`OriginalFiniteIdealBlowupSquare.inducedMorphism`.  Through the comparison isomorphism
`HironakaG10SbBlowupComparison.blowupIso` (BC3: `blowupIso_hom_comp`) and the identification of the two
strict-transform maps (`HironakaG10GlStepSquare.stepP_blowupIso_hom`), a generic presentation
(`HironakaG10GlPresentationTransport.GenPresentation`) over the geometric blowup at a point of the strict source
transports (`nonempty_transport`) to one over the native blowup, which IS the pulled torsion presentation of the
step (`GenPresentation.toPulled`).  Hironaka 1975, Lemma 4.4.5, proof (printed pp. 537–538): the strict transform
is the fibre product modulo its exceptional torsion, and the flattener commutes with base change; the blowup of a
dense finite-type ideal is unique up to unique isomorphism over the base (p. 535).

* `nonempty_pulledPresentation_of_gen` — at one point;
* `hpres_of_genPresentation` — the `hpres` binder of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`
  (= `HironakaG10FinalAssembly.PresentationsOverCentre`, verbatim) from generic presentations over the geometric
  blowup at every point of the strict source over the centre.

No canonical chart is used.  No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Hironaka.Analytic.Unibranch.HironakaG10GlPresentationStage

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction
  Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison
  Hironaka.Analytic.Unibranch.HironakaG10GlStepSquare Hironaka.Analytic.Unibranch.HironakaG10GlPresentationTransport
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- **One point.**  A generic presentation over the geometric blowup, at a point `y''` of the strict source of one
flattening step and at `z = inducedMorphism y''`, gives the pulled torsion presentation of the step at `y''`. -/
theorem nonempty_pulledPresentation_of_gen (s : Stage) (c : AdmissibleCentre s.f)
    (y'' : (nextWith s c).Y.obj.left)
    (z : (letI := c.finiteType; OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left)
    (hz : (letI := c.finiteType; OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f).hom.left.base y'' = z)
    (P : letI := c.finiteType
      GenPresentation (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b)
        (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f) (stepQ s c) s.f (centreIdeal c) y'' z hz) :
    Nonempty (PulledPresentation s c y'') := by
  let _ := c.finiteType
  obtain ⟨P₁⟩ := nonempty_transport (blowupIso c.B c.b c.dense)
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b) (stepQ s c) s.f (centreIdeal c)
    (nextWith s c).f y'' (stepσ s c) (blowupIso_hom_comp c.B c.b c.dense)
    (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f) (stepP_blowupIso_hom s c) z hz P
  exact ⟨P₁.toPulled s c y''⟩

/-- **The `hpres` binder** of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre` (verbatim
`HironakaG10FinalAssembly.PresentationsOverCentre`) from generic presentations over the geometric blowup at the
points of the strict source over the centre (statement S1 of `G10HP/STATUS.md`, verbatim). -/
theorem hpres_of_genPresentation
    (hgen : ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b →
      letI := c.finiteType
      ∃ (z : (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left)
        (hz : (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f).hom.left.base y'' = z),
        Nonempty (GenPresentation (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b)
          (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f) (stepQ s c) s.f (centreIdeal c) y'' z hz)) :
    ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b →
      Nonempty (PulledPresentation s c y'') := by
  intro s c y'' hc
  let _ := c.finiteType
  obtain ⟨z, hz, ⟨P⟩⟩ := hgen s c y'' hc
  exact nonempty_pulledPresentation_of_gen s c y'' z hz P

end

end Hironaka.Analytic.Unibranch.HironakaG10GlPresentationStage
