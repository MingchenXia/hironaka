import DeJongAlterations.Modification
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Topology.Sets.Closeds

/-!
# The exact native isomorphism open and closed nonisomorphism center

The union of all genuine target isomorphism opens is again an isomorphism
open by native target locality. Its closed complement is the actual center,
without a selected witness or a caller-supplied locus certificate.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ModificationCenter

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- The union of all actual target opens on which the full native restriction is an isomorphism. -/
def isomorphismOpen (f : X ⟶ Y) : Y.Opens :=
  ⨆ U : { U : Y.Opens // IsIso (f ∣_ U) }, U.1

/-- Each actual isomorphism open belongs to the defining union. -/
theorem le_isomorphismOpen_of_isIso (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] :
    U ≤ isomorphismOpen f :=
  le_iSup (fun U : { U : Y.Opens // IsIso (f ∣_ U) } => U.1) ⟨U, inferInstance⟩

/-- Restricting an actual isomorphism open to a smaller target open preserves isomorphism. -/
theorem isIso_restrict_of_le (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ≤ V)
    [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have himage : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUV]
  have H := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp
      (inferInstanceAs (IsIso ((f ∣_ V) ∣_ V.ι ⁻¹ᵁ U)))
  change IsIso (f ∣_ V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) at H
  rw [himage] at H
  exact H

/-- The complete union of target isomorphism opens is itself an actual isomorphism open. -/
instance isIso_restrict_isomorphismOpen (f : X ⟶ Y) : IsIso (f ∣_ isomorphismOpen f) := by
  change (MorphismProperty.isomorphisms Scheme) (f ∣_ isomorphismOpen f)
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro y
  obtain ⟨U, hyU⟩ := TopologicalSpace.Opens.mem_iSup.mp y.2
  refine ⟨(isomorphismOpen f).ι ⁻¹ᵁ U.1, hyU, ?_⟩
  have : IsIso (f ∣_ U.1) := U.2
  have himage : (isomorphismOpen f).ι ''ᵁ ((isomorphismOpen f).ι ⁻¹ᵁ U.1) = U.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (le_isomorphismOpen_of_isIso f U.1)]
  apply ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f (isomorphismOpen f) ((isomorphismOpen f).ι ⁻¹ᵁ U.1))).mpr
  change IsIso (f ∣_ (isomorphismOpen f).ι ''ᵁ ((isomorphismOpen f).ι ⁻¹ᵁ U.1))
  rw [himage]
  exact U.2

/-- Maximality characterizes the entire actual isomorphism open. -/
theorem le_isomorphismOpen_iff (f : X ⟶ Y) (U : Y.Opens) :
    U ≤ isomorphismOpen f ↔ IsIso (f ∣_ U) := by
  constructor
  · exact fun h => isIso_restrict_of_le f h
  · intro h
    let := h
    exact le_isomorphismOpen_of_isIso f U

/-- The actual closed nonisomorphism subset, as in de Jong 2.17. -/
def center (f : X ⟶ Y) : Closeds Y := (isomorphismOpen f).compl

/-- The complement of the actual center is precisely the maximal native isomorphism open. -/
@[simp]
theorem center_compl (f : X ⟶ Y) : (center f).compl = isomorphismOpen f :=
  TopologicalSpace.Opens.compl_compl _

/-- The original morphism restricted over the actual center complement is an isomorphism. -/
instance isIso_restrict_compl_center (f : X ⟶ Y) : IsIso (f ∣_ (center f).compl) := by
  rw [center_compl]
  infer_instance

/-- The actual isomorphism over the center complement, retaining the original restricted morphism. -/
def complementIso (f : X ⟶ Y) :
    (f ⁻¹ᵁ (center f).compl).toScheme ≅ (show Y.Opens from (center f).compl).toScheme :=
  asIso (f ∣_ (center f).compl)

/-- A point belongs to the center exactly when none of its target neighborhoods is an isomorphism open. -/
theorem mem_center_iff (f : X ⟶ Y) (y : Y) :
    y ∈ center f ↔ ∀ U : Y.Opens, y ∈ U → ¬ IsIso (f ∣_ U) := by
  constructor
  · intro hy U hyU hU
    let := hU
    exact hy (le_isomorphismOpen_of_isIso f U hyU)
  · intro H hy
    obtain ⟨U, hyU⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact H U.1 hyU U.2

/-- A containing closed set gives an actual isomorphism on its entire complement, and conversely. -/
theorem center_le_iff (f : X ⟶ Y) (C : Closeds Y) :
    center f ≤ C ↔ IsIso (f ∣_ C.compl) := by
  rw [← le_isomorphismOpen_iff]
  constructor
  · intro H y hy
    by_contra hnot
    exact hy (H hnot)
  · intro H y hy
    by_contra hnot
    exact hy (H hnot)

/-- The maximal isomorphism open of an actual isomorphism is the whole original target. -/
theorem isomorphismOpen_eq_top (f : X ⟶ Y) [IsIso f] : isomorphismOpen f = ⊤ :=
  top_le_iff.mp (le_isomorphismOpen_of_isIso f ⊤)

/-- An actual isomorphism has empty center. -/
@[simp]
theorem center_eq_bot_of_isIso (f : X ⟶ Y) [IsIso f] : center f = ⊥ := by
  rw [center, isomorphismOpen_eq_top]
  ext y
  simp

/-- In particular, the identity modification has empty actual center. -/
@[simp]
theorem center_id (X : Scheme.{u}) : center (𝟙 X) = ⊥ := center_eq_bot_of_isIso _

end DeJongAlterations.Geometry.ModificationCenter
