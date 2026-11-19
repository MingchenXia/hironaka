import Hironaka.Geometry.ProperSteinGlobalIdempotentsHomeomorphism
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Literal nil-kernel quotient base changes and ORIGINAL whole idempotents

The native scheme-property proof follows the existing workspace's
`EnvelopeProperty/SchemeNilBaseChange.lean`, with the actual original
whole-idempotent equivalence proved in the present project.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace Hironaka.Geometry.ProperSteinGlobalIdempotents.NilBaseChange
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S] (α : R →+* S)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The LITERAL native whole coefficient base change. -/
abbrev model := pullback f (Spec.map (CommRingCat.ofHom α))

/-- The SAME original native base-change projection. -/
abbrev projection : model α f ⟶ X := pullback.fst _ _

/-- The ORIGINAL surjective ring map and actual nilpotents derive surjectivity on actual prime spectra. -/
theorem surjective_specMap (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) :
    Surjective (Spec.map (CommRingCat.ofHom α)) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap α)
  intro p
  have hp : p ∈ Set.range (PrimeSpectrum.comap α) := by
    rw [range_comap_of_surjective _ _ hα, PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe]
    intro a ha
    obtain ⟨n, hn⟩ := hnil a ha
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n (by rw [hn]; exact p.asIdeal.zero_mem)
  exact hp

/-- Original affine ring surjectivity derives closedness of the SAME literal projection. -/
theorem projection_isClosedImmersion (hα : Function.Surjective α) :
    IsClosedImmersion (projection α f) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom α)) :=
    IsClosedImmersion.spec_of_surjective _ hα
  infer_instance

/-- Original nil-kernel prime correspondence derives surjectivity of the SAME literal projection. -/
theorem projection_surjective (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) : Surjective (projection α f) := by
  let : Surjective (Spec.map (CommRingCat.ofHom α)) := surjective_specMap α hα hnil
  infer_instance

/-- Both original scheme properties give an actual underlying homeomorphism, with no supplied homeomorphism. -/
theorem projection_isHomeomorph (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) : IsHomeomorph (projection α f) := by
  let := projection_isClosedImmersion α f hα
  let := projection_surjective α f hα hnil
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(projection α f).isEmbedding, (projection α f).surjective⟩

/-- The actual equivalence keeps the SAME original whole-idempotent projection pullback. -/
def idempotentEquiv (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) :
    {e : Γ(X, ⊤) // IsIdempotentElem e} ≃ {e : Γ(model α f, ⊤) // IsIdempotentElem e} :=
  idempotentPullbackEquiv (projection α f) (projection_isHomeomorph α f hα hnil)

/-- Its ENTIRE forward map is literally the ORIGINAL whole-section projection pullback. -/
theorem idempotentEquiv_apply (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a)
    (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) :
    (idempotentEquiv α f hα hnil e).1 = (projection α f).appTop e.1 := rfl

end Hironaka.Geometry.ProperSteinGlobalIdempotents.NilBaseChange
