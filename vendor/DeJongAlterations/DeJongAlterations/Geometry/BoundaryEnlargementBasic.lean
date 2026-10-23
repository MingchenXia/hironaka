import DeJongAlterations.Theorem
import Mathlib.Topology.Connected.Clopen

/-!
# The actual compactification over a proper original target

Properness forces the actual open immersion of every full
alteration-with-boundary output to be an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.BoundaryEnlargement

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Over a proper original target, the given full output has no complement at infinity. -/
theorem inclusion_isIso_of_isProper
    {p : X ⟶ Spec (.of k)} [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) : IsIso d.inclusion := by
  let : IsVariety d.sourceStructure := d.sourceVariety
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : IsAlteration d.alteration := d.isAlteration
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  let : IsProper d.sourceStructure := by
    rw [← d.alterationOver]
    infer_instance
  let : IsProper (d.inclusion ≫ d.compactificationStructure) := by
    rw [d.inclusionOver]
    infer_instance
  let : IsProper d.inclusion := IsProper.of_comp d.inclusion d.compactificationStructure
  have hrange : Set.range d.inclusion = Set.univ :=
    (show IsClopen (Set.range d.inclusion) from
      ⟨d.inclusion.isClosedMap.isClosed_range, d.inclusion.isOpenEmbedding.isOpen_range⟩).eq_univ
        (Set.range_nonempty _)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  exact Opens.ext hrange

/-- The actual inverse to the given inclusion extends the actual alteration everywhere. -/
def compactificationMap
    {p : X ⟶ Spec (.of k)} [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) : d.compactification ⟶ X := by
  let : IsIso d.inclusion := inclusion_isIso_of_isProper d
  exact inv d.inclusion ≫ d.alteration

@[reassoc (attr := simp)]
theorem inclusion_compactificationMap
    {p : X ⟶ Spec (.of k)} [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) :
    d.inclusion ≫ compactificationMap d = d.alteration := by
  let : IsIso d.inclusion := inclusion_isIso_of_isProper d
  simp only [compactificationMap, IsIso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
theorem compactificationMap_structure
    {p : X ⟶ Spec (.of k)} [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) :
    compactificationMap d ≫ p = d.compactificationStructure := by
  let : IsIso d.inclusion := inclusion_isIso_of_isProper d
  simp only [compactificationMap, Category.assoc, d.alterationOver,
    ← d.inclusionOver, IsIso.inv_hom_id_assoc]

/-- The everywhere-defined extension is itself an actual alteration. -/
theorem compactificationMap_isAlteration
    {p : X ⟶ Spec (.of k)} [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) : IsAlteration (compactificationMap d) := by
  let : IsIso d.inclusion := inclusion_isIso_of_isProper d
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : IsAlteration d.alteration := d.isAlteration
  exact IsAlteration.comp_finite (inv d.inclusion) d.alteration

/-- The original full boundary becomes the exact inverse image under the actual extended alteration. -/
theorem boundary_support_eq_preimage
    {p : X ⟶ Spec (.of k)} [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) :
    (d.boundary.support : Set d.compactification) = compactificationMap d ⁻¹' Z := by
  let : IsIso d.inclusion := inclusion_isIso_of_isProper d
  have hsurj : Function.Surjective d.inclusion :=
    (Scheme.homeoOfIso (asIso d.inclusion)).surjective
  rw [d.boundarySupport, Set.range_eq_univ.mpr hsurj, Set.compl_univ, Set.union_empty]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := congrArg (fun f : d.source ⟶ X ↦ f y) (inclusion_compactificationMap d)
    change compactificationMap d (d.inclusion y) ∈ Z
    rw [show compactificationMap d (d.inclusion y) = d.alteration y from h]
    exact hy
  · intro hx
    refine ⟨inv d.inclusion x, hx, ?_⟩
    have h := congrArg (fun f : d.compactification ⟶ d.compactification ↦ f x)
      (IsIso.inv_hom_id d.inclusion)
    exact h

end DeJongAlterations.Geometry.BoundaryEnlargement
