import DeJongAlterations.Basic
import DeJongAlterations.Projective
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Actual schematic projective compactification

The actual kernel subscheme of a native projective immersion is constructed
internally. For a quasi-compact immersion, the native image factorization
gives the actual dense open immersion into this projective closed scheme.
Integrality follows from the whole schematic-image quotient chart rings.

This supplies the compactification chosen in de Jong 4.7. The input is an
actual projective immersion, as in quasi-projectivity; Chow's lemma is separate.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveCompactification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- The actual affine quotient charts of a schematic image are reduced when its source is reduced. -/
theorem imageChart_isReduced (f : X ⟶ Y) [QuasiCompact f] [IsReduced X]
    (U : Y.affineOpens) :
    _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U) := by
  let q : (Γ(Y, U) ⧸ f.ker.ideal U) →+* Γ(X, f ⁻¹ᵁ U) :=
    Ideal.Quotient.lift (f.ker.ideal U) (f.app U).hom (by
      rw [Scheme.Hom.ker_apply]
      exact fun _ ha => ha)
  exact isReduced_of_injective q
    (RingHom.lift_injective_of_ker_le_ideal _ _ (by rw [Scheme.Hom.ker_apply]))

/-- The actual scheme-theoretic image of a quasi-compact map from a reduced scheme is reduced. -/
theorem image_isReduced (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] : IsReduced f.image := by
  have (U : Y.affineOpens) :
      IsReduced (f.ker.subschemeCover.openCover.X U) := by
    let := imageChart_isReduced f U
    change IsReduced (Spec (CommRingCat.of (Γ(Y, U) ⧸ f.ker.ideal U)))
    infer_instance
  exact IsReduced.of_openCover f.image f.ker.subschemeCover.openCover

/-- The actual image of a quasi-compact map from an irreducible scheme is irreducible. -/
theorem image_irreducibleSpace (f : X ⟶ Y) [QuasiCompact f] [IrreducibleSpace X] :
    IrreducibleSpace f.image := by
  apply (irreducibleSpace_def f.image).mpr
  have h := (IrreducibleSpace.isIrreducible_univ X).image
    f.toImage f.toImage.continuous.continuousOn
  simpa only [Set.image_univ, f.toImage.denseRange.closure_eq, Set.top_eq_univ] using h.closure

/-- The actual scheme-theoretic image of any quasi-compact map from an integral scheme is integral. -/
theorem image_isIntegral (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  let := image_isReduced f
  let := image_irreducibleSpace f
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The actual closure of the given projective morphism is its native kernel closed subscheme. -/
def closure (e : X ⟶ projectiveSpace R n) : Scheme.{u} := e.image

/-- The actual source map into its constructed schematic projective closure. -/
def inclusion (e : X ⟶ projectiveSpace R n) : X ⟶ closure e := e.toImage

/-- The actual kernel closed immersion into the original native projective space. -/
def embedding (e : X ⟶ projectiveSpace R n) : closure e ⟶ projectiveSpace R n := e.imageι

/-- The original coefficient-ring structure map on the actual projective closure. -/
def closureStructure (e : X ⟶ projectiveSpace R n) :
    closure e ⟶ Spec (CommRingCat.of R) :=
  embedding e ≫ projectiveSpaceStructure R n

instance embedding_isClosedImmersion (e : X ⟶ projectiveSpace R n) :
    IsClosedImmersion (embedding e) := by
  unfold embedding
  infer_instance

instance inclusion_isOpenImmersion (e : X ⟶ projectiveSpace R n)
    [IsImmersion e] [QuasiCompact e] : IsOpenImmersion (inclusion e) := by
  unfold inclusion
  infer_instance

instance inclusion_isDominant (e : X ⟶ projectiveSpace R n) [QuasiCompact e] :
    IsDominant (inclusion e) := by
  unfold inclusion
  infer_instance

/-- The actual kernel subscheme factorization recovers the original projective immersion. -/
@[reassoc (attr := simp)]
theorem inclusion_embedding (e : X ⟶ projectiveSpace R n) :
    inclusion e ≫ embedding e = e := e.toImage_imageι

/-- The constructed open compactification preserves the actual original coefficient structure. -/
theorem inclusion_structure (e : X ⟶ projectiveSpace R n) :
    inclusion e ≫ closureStructure e = e ≫ projectiveSpaceStructure R n := by
  rw [closureStructure, inclusion_embedding_assoc]

/-- Projectivity is witnessed by the actual native kernel closed immersion, not by a supplied certificate. -/
theorem structure_isProjective (e : X ⟶ projectiveSpace R n) : IsProjectiveOver (closureStructure e) :=
  ⟨n, embedding e, inferInstance, rfl⟩

instance structure_isProper (e : X ⟶ projectiveSpace R n) : IsProper (closureStructure e) :=
  (structure_isProjective e).isProper

/-- The constructed projective closure of an integral quasi-compact source is itself integral. -/
theorem closure_isIntegral (e : X ⟶ projectiveSpace R n) [QuasiCompact e] [IsIntegral X] :
    IsIntegral (closure e) := image_isIntegral e

variable {k : Type u} [Field k]

/-- The actual projective immersion of a variety is quasi-compact, derived from the variety's original structure map. -/
theorem immersion_isQuasiCompact (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    {n : ℕ} (e : X ⟶ projectiveSpace k n) : QuasiCompact e := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace (projectiveSpace k n) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceStructure k n)
  infer_instance

/-- The actual schematic closure of an integral variety's projective immersion is a projective variety. -/
theorem structure_isVariety (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    {n : ℕ} (e : X ⟶ projectiveSpace k n) : IsVariety (closureStructure e) := by
  let := immersion_isQuasiCompact p e
  let := closure_isIntegral e
  exact {}

/-- Source 4.7's actual dense open projective compactification, from the defining native immersion of quasi-projectivity. -/
theorem exists_projective_compactification
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    {n : ℕ} (e : X ⟶ projectiveSpace k n) [IsImmersion e]
    (he : e ≫ projectiveSpaceStructure k n = p) :
    ∃ (Xbar : Scheme.{u}) (pbar : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar),
      IsVariety pbar ∧ IsProjectiveOver pbar ∧ IsOpenImmersion j ∧ IsDominant j ∧ j ≫ pbar = p := by
  let := immersion_isQuasiCompact p e
  exact ⟨closure e, closureStructure e, inclusion e, structure_isVariety p e, structure_isProjective e,
    inferInstance, inferInstance, (inclusion_structure e).trans he⟩

end DeJongAlterations.Geometry.ProjectiveCompactification
