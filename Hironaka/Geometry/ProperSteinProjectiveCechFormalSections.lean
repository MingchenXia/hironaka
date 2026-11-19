/-
Copyright (c) 2026 Chris Birkbeck and the EnvelopeProperty contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechGlobalKernelFiltration
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalBoundary
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalSections

/-! # The actual original whole projective formal-section map

Closed native quotient reconstruction proof adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreProjectiveFormalSections.lean`,
SHA256 b6662724f8141b2cd3617b1fb96bdc58669aae6d3854515b759c6d2b9e93fe8c.
Every actual original global kernel, scheme projection, complete-base module
reconstruction and original coefficient is produced by OWN native geometry.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.FormalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} {r : ℕ} (i : X ⟶ projectiveSpace R r) [IsClosedImmersion i]

/-- ONLY original complete projective Noetherian data separate WHOLE original global functions by actual original infinitesimal coordinates. -/
theorem sectionMap_injective [IsNoetherianRing R] [IsAdicComplete I R] :
    Function.Injective (InfinitesimalSections.sectionMap I (i ≫ projectiveSpaceStructure R r)) := by
  let e := GlobalKernelFiltration.projective_quotientReconstruction I i
  intro s t hst
  apply e.injective
  apply Subtype.ext
  funext n
  apply (Submodule.Quotient.eq _).mpr
  rw [GlobalKernelFiltration.projective_mem_filtration I i (n+1)]
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg (fun z => z.val n) hst)

private theorem sectionMap_surjective_of_lifts [IsNoetherianRing R] [IsAdicComplete I R]
    (hlift : ∀ s : InfinitesimalSections.compatibleSections I (i ≫ projectiveSpaceStructure R r),
      ∀ n, ∃ t : Γ(X, ⊤), (Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) (n+1)).appTop t=s.val n) :
    Function.Surjective (InfinitesimalSections.sectionMap I (i ≫ projectiveSpaceStructure R r)) := by
  let f := i ≫ projectiveSpaceStructure R r
  let F := GlobalKernelFiltration.filtration I f (originalClosedCoordinateOpens i)
    (originalClosedCoordinateOpens_covers i)
  let e := GlobalKernelFiltration.projective_quotientReconstruction I i
  intro s
  choose t ht using hlift s
  have hproj (n m : ℕ) (h : n≤m) : (Infinitesimal.projection I f (n+1)).appTop (t m)=s.val n := by
    calc
      _ = InfinitesimalSections.restriction I f h
          ((Infinitesimal.projection I f (m+1)).appTop (t m)) :=
        (RingHom.congr_fun (InfinitesimalSections.projection_transition I f h) (t m)).symm
      _ = InfinitesimalSections.restriction I f h (s.val m) := congrArg _ (ht m)
      _ = s.val n := s.property n m h
  let q : StableFiltration.compatibleQuotients I F :=
    ⟨fun n => (F.N (n+1)).mkQ (t n), by
      intro n m h
      change (F.N (n+1)).mkQ (t m)=(F.N (n+1)).mkQ (t n)
      apply (Submodule.Quotient.eq _).mpr
      rw [GlobalKernelFiltration.projective_mem_filtration I i (n+1)]
      rw [map_sub, hproj n m h, ht n, sub_self]⟩
  refine ⟨e.symm q, ?_⟩
  apply Subtype.ext
  funext n
  have hq := congrArg (fun z : StableFiltration.compatibleQuotients I F => z.val n) (e.apply_symm_apply q)
  change (F.N (n+1)).mkQ (e.symm q)=(F.N (n+1)).mkQ (t n) at hq
  have hm := (Submodule.Quotient.eq (F.N (n+1))).mp hq
  have hz := (GlobalKernelFiltration.projective_mem_filtration I i (n+1) ((show Γ(X, ⊤) from e.symm q)-t n)).mp hm
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).trans (ht n)

/-- ORIGINAL complete projective Noetherian geometry DERIVES surjectivity of the SAME canonical whole original section ring map. -/
theorem sectionMap_surjective [IsNoetherianRing R] [IsAdicComplete I R] :
    Function.Surjective (InfinitesimalSections.sectionMap I (i ≫ projectiveSpaceStructure R r)) :=
  sectionMap_surjective_of_lifts I i (InfinitesimalBoundary.projective_coordinate_lift I i)

/-- The WHOLE original formal-section map is bijective from ONLY original complete projective Noetherian data. -/
theorem sectionMap_bijective [IsNoetherianRing R] [IsAdicComplete I R] :
    Function.Bijective (InfinitesimalSections.sectionMap I (i ≫ projectiveSpaceStructure R r)) :=
  ⟨sectionMap_injective I i, sectionMap_surjective I i⟩

/-- GENUINE whole original projective H0 formal functions, retaining the canonical actual original ring homomorphism. -/
def formalEquiv [IsNoetherianRing R] [IsAdicComplete I R] :
    Γ(X, ⊤) ≃+* InfinitesimalSections.compatibleSections I (i ≫ projectiveSpaceStructure R r) :=
  RingEquiv.ofBijective (InfinitesimalSections.sectionMap I (i ≫ projectiveSpaceStructure R r))
    (sectionMap_bijective I i)

/-- The ENTIRE original formal-functions forward homomorphism is EXACTLY the SAME original canonical section map. -/
theorem formalEquiv_toRingHom [IsNoetherianRing R] [IsAdicComplete I R] :
    (formalEquiv I i).toRingHom=InfinitesimalSections.sectionMap I (i ≫ projectiveSpaceStructure R r) := rfl

/-- EVERY original forward coordinate is the literal original projection of the SAME whole original global function. -/
theorem formalEquiv_apply [IsNoetherianRing R] [IsAdicComplete I R] (s : Γ(X, ⊤)) (n : ℕ) :
    (formalEquiv I i s).val n=(Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) (n+1)).appTop s := rfl

/-- The whole original equivalence retains the ENTIRE actual original R-coefficient homomorphism. -/
theorem formalEquiv_coefficient [IsNoetherianRing R] [IsAdicComplete I R] :
    (formalEquiv I i).toRingHom.comp (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)) =
      InfinitesimalSections.coefficient I (i ≫ projectiveSpaceStructure R r) := rfl

/-- EVERY prescribed actual model coordinate is recovered by the SAME original reconstructed global function. -/
theorem formalEquiv_symm_apply [IsNoetherianRing R] [IsAdicComplete I R]
    (s : InfinitesimalSections.compatibleSections I (i ≫ projectiveSpaceStructure R r)) (n : ℕ) :
    (Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) (n+1)).appTop ((formalEquiv I i).symm s)=s.val n :=
  congrArg (fun z : InfinitesimalSections.compatibleSections I (i ≫ projectiveSpaceStructure R r) => z.val n)
    ((formalEquiv I i).apply_symm_apply s)

/-- The actual whole formal-functions ring equivalence is an ORIGINAL R-algebra equivalence for SAME original coefficient actions. -/
def formalAlgEquiv [IsNoetherianRing R] [IsAdicComplete I R] :
    letI := (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)).toAlgebra
    letI := (InfinitesimalSections.coefficient I (i ≫ projectiveSpaceStructure R r)).toAlgebra
    Γ(X, ⊤) ≃ₐ[R] InfinitesimalSections.compatibleSections I (i ≫ projectiveSpaceStructure R r) := by
  letI := (ProperGeometricGlobalFunctions.coefficientMap (i ≫ projectiveSpaceStructure R r)).toAlgebra
  letI := (InfinitesimalSections.coefficient I (i ≫ projectiveSpaceStructure R r)).toAlgebra
  exact { toRingEquiv := formalEquiv I i, commutes' := fun _ => rfl }

omit [IsClosedImmersion i] in
/-- The literal ORIGINAL closed-fibre projection over R/I, retaining the actual original quotient presentation. -/
def closedFiberProjection : ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I ⟶ X :=
  pullback.fst _ _

omit [IsClosedImmersion i] in
private theorem closedFiber_projection_triangle :
    ProperSteinGlobalIdempotents.closedToThickening (i ≫ projectiveSpaceStructure R r) I 0 ≫
      Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) 1 = closedFiberProjection I i := by
  simp only [ProperSteinGlobalIdempotents.closedToThickening, Infinitesimal.projection,
    closedFiberProjection, pullback.lift_fst]

/-- GENUINE complete-base original formal functions lift EVERY original R/I closed-fibre idempotent to a WHOLE original global idempotent. -/
def closedFiberIdempotentLift [IsNoetherianRing R] [IsAdicComplete I R]
    (e : {e : Γ(ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I, ⊤) // IsIdempotentElem e}) :
    {e : Γ(X, ⊤) // IsIdempotentElem e} := by
  let ec := InfinitesimalSections.closedFiberLiftFamily I (i ≫ projectiveSpaceStructure R r) e
  exact ⟨(formalEquiv I i).symm ec.val, ec.property.map (formalEquiv I i).symm.toRingHom⟩

/-- The actual first original model projection recovers the SAME original compatible idempotent coordinate. -/
theorem closedFiberIdempotentLift_projection [IsNoetherianRing R] [IsAdicComplete I R]
    (e : {e : Γ(ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I, ⊤) // IsIdempotentElem e}) :
    (Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) 1).appTop (closedFiberIdempotentLift I i e).val =
      (InfinitesimalSections.closedFiberLiftFamily I (i ≫ projectiveSpaceStructure R r) e).val.val 0 :=
  formalEquiv_symm_apply I i (InfinitesimalSections.closedFiberLiftFamily I (i ≫ projectiveSpaceStructure R r) e).val 0

/-- Restricting the WHOLE original global idempotent through the literal ORIGINAL R/I fibre projection recovers EXACTLY the original idempotent. -/
theorem closedFiberIdempotentLift_restrict [IsNoetherianRing R] [IsAdicComplete I R]
    (e : {e : Γ(ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I, ⊤) // IsIdempotentElem e}) :
    (closedFiberProjection I i).appTop (closedFiberIdempotentLift I i e).val=e.val := by
  let c := ProperSteinGlobalIdempotents.closedToThickening (i ≫ projectiveSpaceStructure R r) I 0
  let p := Infinitesimal.projection I (i ≫ projectiveSpaceStructure R r) 1
  have hmap := congrArg (fun q => q.appTop) (closedFiber_projection_triangle I i)
  rw [Scheme.Hom.comp_appTop] at hmap
  calc
    _ = c.appTop (p.appTop (closedFiberIdempotentLift I i e).val) :=
      (congrArg (fun q : Γ(X, ⊤) ⟶
        Γ(ProperSteinGlobalIdempotents.closedFiber (i ≫ projectiveSpaceStructure R r) I, ⊤) =>
          q (closedFiberIdempotentLift I i e).val) hmap).symm
    _ = c.appTop ((InfinitesimalSections.closedFiberLiftFamily I (i ≫ projectiveSpaceStructure R r) e).val.val 0) :=
      congrArg c.appTop (closedFiberIdempotentLift_projection I i e)
    _ = e.val := InfinitesimalSections.closedFiberLiftFamily_restrict I (i ≫ projectiveSpaceStructure R r) e

end Hironaka.Geometry.ProperSteinProjectiveCech.FormalSections
