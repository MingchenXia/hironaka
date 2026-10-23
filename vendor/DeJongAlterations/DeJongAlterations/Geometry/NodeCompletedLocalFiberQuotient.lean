import DeJongAlterations.Geometry.NodeCompletedLocalFiberStalk
import DeJongAlterations.Geometry.NodeCompletedLocalFiber
import Mathlib.AlgebraicGeometry.Fiber

/-! The actual original scheme fibre stalk as the original maximal-ideal quotient. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.Geometry.NodeCompletedLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

attribute [local instance] originalAlgebra

/-- The actual uncompleted original stalk quotient. -/
abbrev OriginalFiberRing := X.presheaf.stalk x ⧸ originalFiberIdeal f x

local instance originalFiberRing_local : IsLocalRing (OriginalFiberRing f x) :=
  originalFiberLocalRing f x

local instance originalFiberQuotientMap_local :
    IsLocalHom (Ideal.Quotient.mk (originalFiberIdeal f x)) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

local instance originalFiberQuotientCatMap_local :
    IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk (originalFiberIdeal f x))).hom :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- The literal quotient tensor comparison, preserving every original target germ. -/
def originalFiberTensorEquiv : OriginalFiberRing f x ≃ₐ[X.presheaf.stalk x]
    (X.presheaf.stalk x ⊗[S.presheaf.stalk (f x)] ResidueField (S.presheaf.stalk (f x))) :=
  Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x)
    (maximalIdeal (S.presheaf.stalk (f x)))

/-- The actual spectrum of the original quotient is the literal local closed-fibre pullback. -/
def originalFiberSpecIso :
    Spec (.of (OriginalFiberRing f x)) ≅
      pullback (Spec.map (f.stalkMap x)) (Spec.map (S.residue (f x))) :=
  Scheme.Spec.mapIso (originalFiberTensorEquiv f x).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (ResidueField (S.presheaf.stalk (f x)))).symm

/-- The actual projection to the original local source scheme. -/
def originalFiberToLocalSource :
    Spec (.of (OriginalFiberRing f x)) ⟶ Spec (X.presheaf.stalk x) :=
  (originalFiberSpecIso f x).hom ≫ pullback.fst _ _

/-- The actual projection to the original point residue field. -/
def originalFiberToPointResidue :
    Spec (.of (OriginalFiberRing f x)) ⟶ Spec (S.residueField (f x)) :=
  (originalFiberSpecIso f x).hom ≫ pullback.snd _ _

/-- This is the actual defining pullback, not a supplied fibre comparison. -/
theorem originalFiber_isPullback :
    IsPullback (originalFiberToLocalSource f x) (originalFiberToPointResidue f x)
      (Spec.map (f.stalkMap x)) (Spec.map (S.residue (f x))) := by
  apply IsPullback.of_iso_pullback (i := originalFiberSpecIso f x)
  · exact ⟨by simp [originalFiberToLocalSource, originalFiberToPointResidue,
      pullback.condition]⟩
  · rfl
  · rfl

/-- The local-source projection retains the literal original quotient map. -/
theorem originalFiberToLocalSource_eq :
    originalFiberToLocalSource f x =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (originalFiberIdeal f x))) := by
  change Spec.map (CommRingCat.ofHom (originalFiberTensorEquiv f x).symm.toRingHom) ≫
    (pullbackSpecIso (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (ResidueField (S.presheaf.stalk (f x)))).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  exact (originalFiberTensorEquiv f x).symm.commutes b

/-- The local fibre projections give the actual original geometric coefficient square. -/
theorem originalFiberToSource_condition :
    originalFiberToLocalSource f x ≫ X.fromSpecStalk x ≫ f =
      originalFiberToPointResidue f x ≫ S.fromSpecResidueField (f x) := by
  simpa only [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
    Scheme.fromSpecResidueField] using
      (originalFiber_isPullback f x).w_assoc (S.fromSpecStalk (f x))

/-- The actual map from the original local quotient scheme into the actual scheme fibre. -/
def originalFiberMap : Spec (.of (OriginalFiberRing f x)) ⟶ f.fiber (f x) :=
  pullback.lift (originalFiberToLocalSource f x ≫ X.fromSpecStalk x)
    (originalFiberToPointResidue f x) (originalFiberToSource_condition f x)

/-- Its original source projection is the actual original localization-quotient map. -/
theorem originalFiberMap_source :
    originalFiberMap f x ≫ f.fiberι (f x) =
      originalFiberToLocalSource f x ≫ X.fromSpecStalk x :=
  pullback.lift_fst _ _ _

/-- Its residue projection is the actual original point residue projection. -/
theorem originalFiberMap_residue :
    originalFiberMap f x ≫ f.fiberToSpecResidueField (f x) =
      originalFiberToPointResidue f x :=
  pullback.lift_snd _ _ _

/-- The original local quotient scheme is an ACTUAL base change of original scheme localization. -/
theorem originalFiberMap_isPullback :
    IsPullback (originalFiberMap f x) (originalFiberToLocalSource f x)
      (f.fiberι (f x)) (X.fromSpecStalk x) := by
  have hright : IsPullback (𝟙 (Spec (X.presheaf.stalk x))) (Spec.map (f.stalkMap x))
      (Spec.map (f.stalkMap x) ≫ S.fromSpecStalk (f x)) (S.fromSpecStalk (f x)) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hbig : IsPullback (originalFiberToLocalSource f x)
      (originalFiberToPointResidue f x) (X.fromSpecStalk x ≫ f)
        (S.fromSpecResidueField (f x)) := by
    simpa only [Category.comp_id, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.fromSpecResidueField] using (originalFiber_isPullback f x).paste_horiz hright
  have houter : IsPullback (originalFiberToLocalSource f x)
      (originalFiberMap f x ≫ f.fiberToSpecResidueField (f x))
      (X.fromSpecStalk x ≫ f) (S.fromSpecResidueField (f x)) := by
    rw [originalFiberMap_residue]
    exact hbig
  exact (IsPullback.of_bot houter (originalFiberMap_source f x).symm
    (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x)))).flip

/-- The actual point in the original scheme fibre, obtained from the ORIGINAL quotient closed point. -/
def originalFiberPoint : f.fiber (f x) :=
  originalFiberMap f x (closedPoint (CommRingCat.of (OriginalFiberRing f x)))

/-- The constructed actual fibre point lies above the ORIGINAL point, with no replacement chosen. -/
theorem originalFiberPoint_source : f.fiberι (f x) (originalFiberPoint f x) = x := by
  change (originalFiberMap f x ≫ f.fiberι (f x)) (closedPoint (CommRingCat.of (OriginalFiberRing f x))) = x
  rw [originalFiberMap_source, originalFiberToLocalSource_eq]
  have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (originalFiberIdeal f x)))
      (closedPoint (CommRingCat.of (OriginalFiberRing f x))) =
        closedPoint (X.presheaf.stalk x) := Spec_closedPoint
  exact (congrArg (X.fromSpecStalk x) hq).trans Scheme.fromSpecStalk_closedPoint

/-- At this actual point the fibre stalk is the literal original local quotient. -/
def originalFiberStalkEquiv :
    (f.fiber (f x)).presheaf.stalk (originalFiberPoint f x) ≃+* OriginalFiberRing f x := by
  letI := isIso_stalkMap_of_isPullback_fromSpecStalk (originalFiberMap_isPullback f x)
    (closedPoint (CommRingCat.of (OriginalFiberRing f x)))
  exact (asIso ((originalFiberMap f x).stalkMap (closedPoint (CommRingCat.of (OriginalFiberRing f x)))) ≪≫
    stalkClosedPointIso (.of (OriginalFiberRing f x))).commRingCatIsoToRingEquiv

/-- The literal fibre-stalk equivalence is the actual map to the local quotient closed point. -/
theorem originalFiberStalkEquiv_toRingHom :
    (originalFiberStalkEquiv f x).toRingHom =
      (Scheme.stalkClosedPointTo (originalFiberMap f x)).hom := rfl

/-- The actual original projection gives the actual stalk-to-local-quotient map. -/
theorem originalFiberStalkEquiv_projection :
    (f.fiberι (f x)).stalkMap (originalFiberPoint f x) ≫
      CommRingCat.ofHom (originalFiberStalkEquiv f x).toRingHom =
        Scheme.stalkClosedPointTo (originalFiberMap f x ≫ f.fiberι (f x)) := by
  rw [originalFiberStalkEquiv_toRingHom, Scheme.stalkClosedPointTo_comp]
  rfl

/-- Exact preservation of every original local section germ by the actual fibre-stalk equivalence. -/
theorem originalFiberStalkEquiv_germ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    originalFiberStalkEquiv f x
      ((f.fiberι (f x)).stalkMap (originalFiberPoint f x)
        (X.presheaf.germ U (f.fiberι (f x) (originalFiberPoint f x))
          (by simpa only [originalFiberPoint_source] using hx) a)) =
      Ideal.Quotient.mk (originalFiberIdeal f x) (X.presheaf.germ U x hx a) := by
  have h : X.presheaf.germ U (f.fiberι (f x) (originalFiberPoint f x))
      (by simpa only [originalFiberPoint_source] using hx) ≫
      (f.fiberι (f x)).stalkMap (originalFiberPoint f x) ≫
      CommRingCat.ofHom (originalFiberStalkEquiv f x).toRingHom =
        X.presheaf.germ U x hx ≫ CommRingCat.ofHom (Ideal.Quotient.mk (originalFiberIdeal f x)) := by
    rw [originalFiberStalkEquiv_projection]
    change X.presheaf.germ U ((originalFiberMap f x ≫ f.fiberι (f x))
        (closedPoint (CommRingCat.of (OriginalFiberRing f x)))) _ ≫
      Scheme.stalkClosedPointTo (originalFiberMap f x ≫ f.fiberι (f x)) = _
    have hg (p : Spec (.of (OriginalFiberRing f x)) ⟶ X)
        (hp : p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (originalFiberIdeal f x))) ≫
          X.fromSpecStalk x)
        (hU : p (closedPoint (CommRingCat.of (OriginalFiberRing f x))) ∈ U) :
        X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo p =
          X.presheaf.germ U x hx ≫ CommRingCat.ofHom (Ideal.Quotient.mk (originalFiberIdeal f x)) := by
      subst p
      exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
        (CommRingCat.ofHom (Ideal.Quotient.mk (originalFiberIdeal f x))) U _
    exact hg _ (by rw [originalFiberMap_source, originalFiberToLocalSource_eq]) _

  exact ConcreteCategory.congr_hom h a

/-- The actual completed local ring of the original scheme fibre is the literal completion
of its original stalk quotient, with no fibre model assumption. -/
def originalFiberCompletedEquiv :
    (f.fiber (f x)).completedLocalRing (originalFiberPoint f x) ≃+*
      Algebra.CompletionRegularityBasics.Completion (OriginalFiberRing f x) :=
  Algebra.CompletionLocalMap.completionEquiv (originalFiberStalkEquiv f x)

/-- The completed actual-fibre comparison still retains every original local section germ. -/
theorem originalFiberCompletedEquiv_germ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    originalFiberCompletedEquiv f x
      ((f.fiber (f x)).toCompletedLocalRing (originalFiberPoint f x)
        ((f.fiberι (f x)).stalkMap (originalFiberPoint f x)
          (X.presheaf.germ U (f.fiberι (f x) (originalFiberPoint f x))
            (by simpa only [originalFiberPoint_source] using hx) a))) =
      AdicCompletion.of (maximalIdeal (OriginalFiberRing f x)) (OriginalFiberRing f x)
        (Ideal.Quotient.mk (originalFiberIdeal f x) (X.presheaf.germ U x hx a)) := by
  unfold originalFiberCompletedEquiv
  rw [Scheme.toCompletedLocalRing_apply, Algebra.CompletionLocalMap.completionEquiv_apply,
    Algebra.CompletionLocalMap.completionMap_of]
  exact congrArg (AdicCompletion.of (maximalIdeal (OriginalFiberRing f x)) (OriginalFiberRing f x))
    (originalFiberStalkEquiv_germ f x U hx a)

end DeJongAlterations.Geometry.NodeCompletedLocalMap
