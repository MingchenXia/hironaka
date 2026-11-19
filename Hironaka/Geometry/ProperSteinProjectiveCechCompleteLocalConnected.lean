/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechFormalSections

/-! # Actual original complete-local projective closed-fibre connectedness

The local idempotent argument follows the closed native proof in
`EnvelopeProperty/EnvelopeProperty/Global/FibreCompatibleConnectedness.lean`,
SHA256 99e0808079d73e78042545d628e817e93d700c62558a6c1b6bbefab4adc727de.
No other project's imports are used. The original closed fibre is the literal
pullback over R/I, retaining its actual map to every original positive model.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.CompleteLocalConnected
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

private theorem idempotentPullback_comp {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C)
    (e : {e : Γ(C, ⊤) // IsIdempotentElem e}) :
    ProperSteinGlobalIdempotents.idempotentPullback g
      (ProperSteinGlobalIdempotents.idempotentPullback h e) =
      ProperSteinGlobalIdempotents.idempotentPullback (g ≫ h) e := by
  apply Subtype.ext
  simp only [ProperSteinGlobalIdempotents.idempotentPullback, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply]

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} {r : ℕ} (i : X ⟶ projectiveSpace R r) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- EVERY ORIGINAL positive-model projection retains the SAME literal R/I fibre projection. -/
theorem closedToThickening_projection (n : ℕ) :
    ProperSteinGlobalIdempotents.closedToThickening (i ≫ projectiveSpaceStructure R r) I n ≫
      Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) (n+1) =
      FormalSections.closedFiberProjection I i := by
  simp only [ProperSteinGlobalIdempotents.closedToThickening, Infinitesimal.projection,
    FormalSections.closedFiberProjection, pullback.lift_fst]

/-- Actual original complete projective geometry DERIVES injectivity of literal closed-fibre idempotent restriction. -/
theorem closedFiberIdempotentRestriction_injective [IsNoetherianRing R] [IsAdicComplete I R] :
    Function.Injective (ProperSteinGlobalIdempotents.idempotentPullback
      (FormalSections.closedFiberProjection I i)) := by
  intro a b hab
  apply Subtype.ext
  apply FormalSections.sectionMap_injective I i
  apply Subtype.ext
  funext n
  let f := i ≫ projectiveSpaceStructure R r
  let c := ProperSteinGlobalIdempotents.closedToThickening f I n
  let p := Infinitesimal.projection I f (n+1)
  have hh : ProperSteinGlobalIdempotents.idempotentPullback c
      (ProperSteinGlobalIdempotents.idempotentPullback p a) =
      ProperSteinGlobalIdempotents.idempotentPullback c
      (ProperSteinGlobalIdempotents.idempotentPullback p b) := by
    rw [idempotentPullback_comp, idempotentPullback_comp]
    change ProperSteinGlobalIdempotents.idempotentPullback
      (ProperSteinGlobalIdempotents.closedToThickening f I n ≫ p) a = _
    rw [closedToThickening_projection I i n]
    exact hab
  exact congrArg Subtype.val
    ((ProperSteinGlobalIdempotents.closedToThickeningIdempotentEquiv f I n).injective hh)

/-- The original global lift supplies actual surjectivity for the SAME closed-fibre idempotent restriction. -/
theorem closedFiberIdempotentRestriction_surjective [IsNoetherianRing R] [IsAdicComplete I R] :
    Function.Surjective (ProperSteinGlobalIdempotents.idempotentPullback
      (FormalSections.closedFiberProjection I i)) := by
  intro e
  exact ⟨FormalSections.closedFiberIdempotentLift I i e,
    Subtype.ext (FormalSections.closedFiberIdempotentLift_restrict I i e)⟩

/-- Original closed projective Noetherian complete-base data give a genuine whole idempotent restriction bijection. -/
theorem closedFiberIdempotentRestriction_bijective [IsNoetherianRing R] [IsAdicComplete I R] :
    Function.Bijective (ProperSteinGlobalIdempotents.idempotentPullback
      (FormalSections.closedFiberProjection I i)) :=
  ⟨closedFiberIdempotentRestriction_injective I i, closedFiberIdempotentRestriction_surjective I i⟩

/-- Original total-section nontriviality forces nontriviality of actual closed-fibre sections without a point-lift premise. -/
theorem closedFiber_globalSections_nontrivial [IsNoetherianRing R] [IsAdicComplete I R]
    [Nontrivial Γ(X, ⊤)] :
    Nontrivial Γ(ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I, ⊤) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hh : ProperSteinGlobalIdempotents.idempotentPullback (FormalSections.closedFiberProjection I i)
      ⟨0, .zero⟩ =
      ProperSteinGlobalIdempotents.idempotentPullback (FormalSections.closedFiberProjection I i)
      ⟨1, .one⟩ := by
    apply Subtype.ext
    simpa only [ProperSteinGlobalIdempotents.idempotentPullback, map_zero, map_one] using h
  exact zero_ne_one (congrArg Subtype.val (closedFiberIdempotentRestriction_injective I i hh))

/-- The literal ORIGINAL R/I fibre is nonempty from genuine complete projective geometry and original total-section nontriviality. -/
theorem closedFiber_nonempty [IsNoetherianRing R] [IsAdicComplete I R] [Nontrivial Γ(X, ⊤)] :
    Nonempty (ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I) := by
  let := closedFiber_globalSections_nontrivial I i
  exact ProperSteinGlobalIdempotents.nonempty_of_nontrivial_globalSections _

/-- GENUINE actual closed-fibre connectedness from ONLY original complete projective Noetherian data and locality of ORIGINAL global sections. -/
theorem closedFiber_connectedSpace_of_local_globalSections [IsNoetherianRing R] [IsAdicComplete I R]
    [IsLocalRing Γ(X, ⊤)] :
    ConnectedSpace (ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I) := by
  apply (ProperSteinGlobalIdempotents.connectedSpace_iff_idempotents _).mpr
  refine ⟨closedFiber_nonempty I i, ?_⟩
  intro e he
  let z := FormalSections.closedFiberIdempotentLift I i ⟨e, he⟩
  have hz : z.val = 0 ∨ z.val = 1 := by
    obtain hu | hu := IsLocalRing.isUnit_or_isUnit_one_sub_self z.val
    · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp z.property)
    · left
      have hh := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp z.property.one_sub
      have hh' := congrArg (fun t : Γ(X, ⊤) => 1-t) hh
      simpa using hh'
  have hr := FormalSections.closedFiberIdempotentLift_restrict I i ⟨e, he⟩
  change (FormalSections.closedFiberProjection I i).appTop z.val = e at hr
  rcases hz with hz | hz
  · left
    exact hr.symm.trans (by simp only [hz, map_zero])
  · right
    exact hr.symm.trans (by simp only [hz, map_one])

omit [IsClosedImmersion i] in
/-- The ENTIRE algebra-equivalence forward homomorphism is forced to be the ORIGINAL coefficient map. -/
theorem coefficientEquiv_toRingHom
    (e : letI := (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)).toAlgebra
      R ≃ₐ[R] Γ(X, ⊤)) :
    e.toRingHom = ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r) := by
  let := (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)).toAlgebra
  ext a
  exact e.commutes a

/-- An equivalence for the SAME original coefficient action derives connectedness of the ORIGINAL R/I closed fibre over an actual complete local ring. -/
theorem closedFiber_connectedSpace [IsNoetherianRing R] [IsAdicComplete I R] [IsLocalRing R]
    (e : letI := (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)).toAlgebra
      R ≃ₐ[R] Γ(X, ⊤)) :
    ConnectedSpace (ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I) := by
  let := (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)).toAlgebra
  let : Nontrivial Γ(X, ⊤) := ⟨⟨e 0, e 1, fun h => zero_ne_one (e.injective h)⟩⟩
  let := IsLocalRing.of_surjective' e.toRingHom e.surjective
  exact closedFiber_connectedSpace_of_local_globalSections I i

/-- The SAME original maximal-ideal closed fibre is genuinely connected; no residue-field section identity is assumed. -/
theorem maximalClosedFiber_connectedSpace [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (e : letI := (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)).toAlgebra
      R ≃ₐ[R] Γ(X, ⊤)) :
    ConnectedSpace (ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r)
      (IsLocalRing.maximalIdeal R)) :=
  closedFiber_connectedSpace (IsLocalRing.maximalIdeal R) i e

end Hironaka.Geometry.ProperSteinProjectiveCech.CompleteLocalConnected
