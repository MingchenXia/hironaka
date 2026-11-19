import Hironaka.Geometry.RelativeUnramifiedFibers
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual field extensions and geometric fibres detect formal unramifiedness -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace Hironaka.Geometry.RelativeUnramified
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Literal field base change detects formal unramifiedness of the SAME original field morphism. -/
theorem formallyUnramified_of_fieldExtension {k L : Type u} [Field k] [Field L]
    [Algebra k L] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k))
    [FormallyUnramified
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))))] :
    FormallyUnramified p := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hff : (algebraMap k L).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  have hg := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap k L))).mpr hff
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @FormallyUnramified) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := p) (g := g) ⟨⟨hg.2, hg.1⟩, inferInstance⟩ inferInstance

/-- The ACTUAL original residue fibre, base changed along its native algebraic-closure map. -/
def algebraicClosureFiberMap {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    pullback (f.fiberToSpecResidueField s)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s))))) ⟶
      Spec (.of (AlgebraicClosure (S.residueField s))) :=
  pullback.snd _ _

/-- Actual algebraic-closure fibres detect unramifiedness without any Noetherian/base-flatness premise. -/
theorem formallyUnramified_of_geometricFibers {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f]
    (hf : ∀ s : S, FormallyUnramified (algebraicClosureFiberMap f s)) :
    FormallyUnramified f := by
  apply formallyUnramified_of_fibers f
  intro s
  let : FormallyUnramified
      (pullback.snd (f.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))))) :=
    hf s
  exact formallyUnramified_of_fieldExtension (k := S.residueField s)
    (L := AlgebraicClosure (S.residueField s))
    (f.fiberToSpecResidueField s)

end Hironaka.Geometry.RelativeUnramified
