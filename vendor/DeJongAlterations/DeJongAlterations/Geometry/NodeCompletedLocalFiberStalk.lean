/-
Adapted from the repository's Hironaka/Scheme/Smooth/LocalBlowUp.lean and
Hironaka/Scheme/Smooth/LocalBlowUpStalk.lean, adopted under
EnvelopeProperty/deps/hironaka-ep33.
SHA256 LocalBlowUp.lean:
d9ffaee0d2933bd4715f6eb1bfabb6b7773520da452feebbabd47bd90caf9d6b.
SHA256 LocalBlowUpStalk.lean:
ef482d311db19cab326360da72ac8bda81ef2f9ee58339f7d4538336baf1b8f3.
Copyright (c) 2026 Resolution; author Chris Elliott (Resolution).
Original Lean formalization by Claude Fable 5.1; Apache License 2.0.
Modified: retain only native flat local-scheme localization and actual
base-changed stalk isomorphisms, omit every blow-up object and external import,
and move into the DeJongAlterations namespace. The Apache License 2.0 is
reproduced in DeJongAlterations/Algebra/AdicCompletionTransport.lean.
-/
import DeJongAlterations.Geometry.NodeCompletedLocalMap

/-! Actual stalk preservation under base change of original scheme localization. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.NodeCompletedLocalMap

universe u
variable {X : Scheme.{u}}

/-- The actual localization of a scheme at an original point is flat. -/
theorem flat_fromSpecStalk (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [Flat.SpecMap_iff]
    let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    have hflat : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
      IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    exact RingHom.flat_algebraMap_iff.mpr hflat
  have : Flat hU.fromSpec := inferInstance
  exact Flat.comp _ _

/-- Every actual base change of original scheme localization induces actual stalk isomorphisms. -/
theorem isIso_stalkMap_of_isPullback_fromSpecStalk
    {x : X} {Y Z : Scheme.{u}} {g : Y ⟶ Z}
    {h : Y ⟶ Spec (X.presheaf.stalk x)} {p : Z ⟶ X}
    (H : IsPullback g h p (X.fromSpecStalk x)) (y : Y) : IsIso (g.stalkMap y) := by
  have : Flat g := MorphismProperty.of_isPullback (P := @Flat) H.flip (flat_fromSpecStalk x)
  have : IsPreimmersion g := MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, g.stalkMap_surjective y⟩
  algebraize [(g.stalkMap y).hom]
  have : Module.FaithfullyFlat (Z.presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ (Flat.stalkMap g y)
      (g.toLRSHom.prop y)
  exact ‹RingHom.FaithfullyFlat _›.injective

end DeJongAlterations.Geometry.NodeCompletedLocalMap
