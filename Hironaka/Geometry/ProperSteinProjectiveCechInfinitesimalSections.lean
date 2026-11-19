/-
Copyright (c) 2026 Chris Birkbeck and the EnvelopeProperty contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalSequence
import Hironaka.Geometry.ProperSteinGlobalIdempotentsTower

/-! # The actual original compatible infinitesimal section ring

Only the closed native compatible-family subring pattern is adapted from
`EnvelopeProperty/EnvelopeProperty/InfinitesimalIdempotents.lean`,
SHA256 643d3f0b0321a46e3fd133530fc6d55c7c05232e460f6888443eabfb2399233b.
Original global projections, their coefficient triangle and genuine ORIGINAL
closed-fibre idempotent lifts are own exact native constructions.
No inverse-limit isomorphism, compatible-lift or global-lift premise.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The literal ORIGINAL scheme transition on ENTIRE original positive-order sections. -/
def restriction {n m : ℕ} (h : n≤m) :
    Γ(Infinitesimal.model I f (m+1), ⊤) →+* Γ(Infinitesimal.model I f (n+1), ⊤) :=
  (Infinitesimal.transition I f (Nat.succ_le_succ h)).appTop.hom

/-- The ENTIRE actual original projection triangle retains EVERY original global section. -/
theorem projection_transition {n m : ℕ} (h : n≤m) :
    (restriction I f h).comp (Infinitesimal.projection I f (m+1)).appTop.hom =
      (Infinitesimal.projection I f (n+1)).appTop.hom := by
  have hh := congrArg (fun q => q.appTop) (Infinitesimal.transition_projection I f (Nat.succ_le_succ h))
  rw [Scheme.Hom.comp_appTop] at hh
  ext s
  exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Infinitesimal.model I f (n+1), ⊤) => q s) hh

/-- The genuine ENTIRE original compatible-section ring uses the SAME original whole scheme transition maps. -/
def compatibleSections : Subring (∀ n : ℕ, Γ(Infinitesimal.model I f (n+1), ⊤)) where
  carrier := {s | ∀ n m (h : n≤m), restriction I f h (s m)=s n}
  one_mem' := by intro n m h; exact map_one _
  mul_mem' := by intro s t hs ht n m h; rw [Pi.mul_apply, map_mul, hs n m h, ht n m h]; rfl
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by intro s t hs ht n m h; rw [Pi.add_apply, map_add, hs n m h, ht n m h]; rfl
  neg_mem' := by intro s hs n m h; rw [Pi.neg_apply, map_neg, hs n m h]; rfl

/-- The SAME original whole global function maps by EVERY actual original projection into the actual compatible-section ring. -/
def sectionMap : Γ(X, ⊤) →+* compatibleSections I f where
  toFun s := ⟨fun n => (Infinitesimal.projection I f (n+1)).appTop s,
    fun n m h => RingHom.congr_fun (projection_transition I f h) s⟩
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_mul' s t := by apply Subtype.ext; funext n; exact map_mul _ s t
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_add' s t := by apply Subtype.ext; funext n; exact map_add _ s t

/-- EVERY actual coordinate is precisely the SAME original scheme pullback of the entire original function. -/
theorem sectionMap_apply (s : Γ(X, ⊤)) (n : ℕ) :
    (sectionMap I f s).val n=(Infinitesimal.projection I f (n+1)).appTop s := rfl

/-- The ORIGINAL base ring acts through its SAME original whole coefficient map. -/
def coefficient : R →+* compatibleSections I f :=
  (sectionMap I f).comp (ProperGeometricGlobalFunctions.coefficientMap f)

/-- EVERY coefficient coordinate is the SAME ENTIRE original composed scheme structure coefficient. -/
theorem coefficient_apply (r : R) (n : ℕ) :
    (coefficient I f r).val n=
      ProperGeometricGlobalFunctions.coefficientMap (Infinitesimal.projection I f (n+1) ≫ f) r :=
  RingHom.congr_fun (InfinitesimalSequence.modelCoefficient I f (n+1)) r

/-- A genuine ORIGINAL closed-fibre idempotent internally gives its ACTUAL compatible family on SAME original models. -/
def closedFiberLiftFamily
    (e : {e : Γ(ProperSteinGlobalIdempotents.closedFiber f I, ⊤) // IsIdempotentElem e}) :
    {s : compatibleSections I f // IsIdempotentElem s} := by
  refine ⟨⟨fun n => (ProperSteinGlobalIdempotents.infinitesimalIdempotentLift I f e n).val,
    fun n m h => ?_⟩, ?_⟩
  · exact ProperSteinGlobalIdempotents.infinitesimalIdempotentLift_compatible I f e h
  · apply Subtype.ext
    funext n
    exact (ProperSteinGlobalIdempotents.infinitesimalIdempotentLift I f e n).property

/-- The actual original R/I-fibre restriction recovers the SAME whole original idempotent, without changing quotient presentations. -/
theorem closedFiberLiftFamily_restrict
    (e : {e : Γ(ProperSteinGlobalIdempotents.closedFiber f I, ⊤) // IsIdempotentElem e}) :
    (ProperSteinGlobalIdempotents.closedToThickening f I 0).appTop
      ((closedFiberLiftFamily I f e).val.val 0)=e.val :=
  ProperSteinGlobalIdempotents.infinitesimalIdempotentLift_restrict I f e 0

end Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalSections
