import Hironaka.Geometry.NodeCompletedLocalResiduePoint
import Hironaka.Geometry.NodeCompletedLocalMap

/-! Genuine external-field residue quotients from an ACTUAL field-valued section.
All coefficient and local representative maps are native original maps. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalSectionResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable (L : Type u) [Field L]

/-- The ACTUAL field-spectrum stalk, through its SAME native Spec/localization map. -/
def fieldStalkRingEquiv (t : Spec (.of L)) : L ≃+* (Spec (.of L)).presheaf.stalk t :=
  (IsLocalization.atUnits L t.asIdeal.primeCompl
    (S := Localization.AtPrime t.asIdeal) (by
      intro a ha
      apply isUnit_iff_ne_zero.mpr
      intro hz
      exact ha (hz ▸ t.asIdeal.zero_mem))).toRingEquiv.trans
    (Spec.stalkIso (.of L) t).symm.commRingCatIsoToRingEquiv

/-- The ENTIRE forward coefficient map is exactly the adopted native original field map. -/
theorem fieldStalkRingEquiv_toRingHom (t : Spec (.of L)) :
    (fieldStalkRingEquiv L t).toRingHom = (Scheme.baseToStalk (𝟙 (Spec (.of L))) t).hom := by
  change (CommRingCat.ofHom (algebraMap L (Localization.AtPrime t.asIdeal)) ≫
    (Spec.stalkIso (.of L) t).inv).hom = _
  trans ((Scheme.ΓSpecIso (.of L)).inv ≫
    (Spec (.of L)).presheaf.germ ⊤ t trivial).hom
  · exact congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of L) (x := t))
  · simp [Scheme.baseToStalk, Scheme.Modules.baseRingHom]

variable {L} {Y : Scheme.{u}} (q : Y ⟶ Spec (.of L))
  (r : Spec (.of L) ⟶ Y) (hr : r ≫ q = 𝟙 _) (t : Spec (.of L))

include hr in
/-- The whole actual section stalk/field coefficient triangle is the native Spec one. -/
theorem section_coefficient_triangle :
    (r.stalkMap t).hom.comp (Scheme.baseToStalk q (r t)).hom =
      (fieldStalkRingEquiv L t).toRingHom := by
  rw [← CommRingCat.hom_comp, Scheme.baseToStalk_comp_stalkMap, hr,
    fieldStalkRingEquiv_toRingHom]

/-- Evaluate EVERY local germ through the SAME actual section and native field-stalk inverse. -/
def sectionEvaluation : Y.presheaf.stalk (r t) →+* L :=
  (fieldStalkRingEquiv L t).symm.toRingHom.comp (r.stalkMap t).hom

/-- The actual evaluation fixes EVERY ORIGINAL external field coefficient. -/
def sectionEvaluationAlgHom :
    letI := Scheme.stalkAlgebra q (r t)
    Y.presheaf.stalk (r t) →ₐ[L] L := by
  letI := Scheme.stalkAlgebra q (r t)
  refine { sectionEvaluation r t with commutes' := ?_ }
  intro a
  change (fieldStalkRingEquiv L t).symm
    (((r.stalkMap t).hom.comp (Scheme.baseToStalk q (r t)).hom) a) = a
  rw [section_coefficient_triangle q r hr t]
  exact (fieldStalkRingEquiv L t).symm_apply_apply a

include q hr in
/-- Surjectivity follows from the ENTIRE original external coefficient triangle. -/
theorem sectionEvaluation_surjective : Function.Surjective (sectionEvaluation r t) := by
  let := Scheme.stalkAlgebra q (r t)
  intro a
  exact ⟨Scheme.baseToStalk q (r t) a, (sectionEvaluationAlgHom q r hr t).commutes a⟩

include q hr in
/-- The SAME actual local evaluation has exactly the native maximal kernel. -/
theorem sectionEvaluation_ker : RingHom.ker (sectionEvaluation r t) =
    maximalIdeal (Y.presheaf.stalk (r t)) :=
  IsLocalRing.ker_eq_maximalIdeal _ (sectionEvaluation_surjective q r hr t)

/-- Actual coefficient-compatible native local residue quotient, without a residue certificate. -/
def sectionQuotientEquiv :
    letI := Scheme.stalkAlgebra q (r t)
    (Y.presheaf.stalk (r t) ⧸ maximalIdeal (Y.presheaf.stalk (r t))) ≃ₐ[L] L := by
  letI := Scheme.stalkAlgebra q (r t)
  exact (Ideal.quotientEquivAlgOfEq L (sectionEvaluation_ker q r hr t).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := sectionEvaluationAlgHom q r hr t)
      (sectionEvaluation_surjective q r hr t))

/-- EVERY local quotient representative retains its SAME actual section evaluation. -/
theorem sectionQuotientEquiv_mk (a : Y.presheaf.stalk (r t)) :
    letI := Scheme.stalkAlgebra q (r t)
    sectionQuotientEquiv q r hr t (Ideal.Quotient.mk _ a) = sectionEvaluation r t a := rfl

open NodeCompletedLocalResiduePoint

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

/-- The prescribed ORIGINAL residue embedding gives the SAME actual rational geometric stalk. -/
def selectedPointQuotientEquiv :
    letI := Scheme.stalkAlgebra (pullback.snd f (selectedBaseMap f x L)) (selectedPoint f x L)
    ((SelectedFiber f x L).presheaf.stalk (selectedPoint f x L) ⧸
      maximalIdeal ((SelectedFiber f x L).presheaf.stalk (selectedPoint f x L))) ≃ₐ[L] L :=
  sectionQuotientEquiv (pullback.snd f (selectedBaseMap f x L)) (selectedSection f x L)
    (selectedSection_field f x L) (fieldPoint L)

end Hironaka.Geometry.NodeCompletedLocalSectionResidue
