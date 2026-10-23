import DeJongAlterations.Composition
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! Native alterations descend on the SAME actual scalar square; the finite open is produced. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.AlterationScalarDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual finite scalar fibre maps onto the ENTIRE actual original fibre. -/
theorem finite_preimage_of_isPullback {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {b : Y' ⟶ Y}
    (H : IsPullback a f' f b) (y' : Y') (hf : (f' ⁻¹' {y'}).Finite) :
    (f ⁻¹' {b y'}).Finite := by
  have heq : a '' (f' ⁻¹' {y'}) = f ⁻¹' {b y'} := by
    simpa only [Set.image_singleton] using
      (Scheme.image_preimage_eq_of_isPullback H.flip ({y'} : Set Y'))
  rw [← heq]
  exact hf.image a

private theorem finite_generic_fiber {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [hf : IsAlteration f] :
    (f ⁻¹' {genericPoint Y}).Finite := by
  let := hf.sourceIntegral
  let := hf.targetIntegral
  have hq := hf.genericallyFinite.quasiFiniteAt_genericPoint f
  have hc := hq.isClopen_singleton_asFiber.isClosed
  have heq (z : f.fiber (f (genericPoint X))) : z = f.asFiber (genericPoint X) := by
    have hs : f.asFiber (genericPoint X) ⤳ z := by
      apply (f.fiberι _).isEmbedding.isInducing.specializes_iff.mp
      rw [Scheme.Hom.fiberι_asFiber]
      exact genericPoint_specializes _
    exact Set.mem_singleton_iff.mp (hs.mem_closed hc (Set.mem_singleton _))
  let : Subsingleton (f.fiber (f (genericPoint X))) :=
    ⟨fun a b => (heq a).trans (heq b).symm⟩
  have hfinite : (f ⁻¹' {f (genericPoint X)}).Finite :=
    (f.fiberHomeo _).finite_iff.mp inferInstance
  simpa only [genericPoint_map_of_isDominant f] using hfinite

/-- A scalar alteration proves ORIGINAL generic finiteness by an actual finite original fibre
and its internally produced finite target neighbourhood, with no generic-finiteness certificate. -/
theorem genericallyFinite_of_isPullback {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {b : Y' ⟶ Y}
    (H : IsPullback a f' f b) [hf' : IsAlteration f'] [Surjective b]
    [IsIntegral X] [IsIntegral Y] [IsProper f] : IsGenericallyFinite f := by
  let := hf'.sourceIntegral
  let := hf'.targetIntegral
  have hfinite := finite_preimage_of_isPullback H (genericPoint Y') (finite_generic_fiber f')
  rw [genericPoint_map_of_isDominant b] at hfinite
  obtain ⟨U, hU, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    f (genericPoint Y) hfinite
  exact ⟨U, ⟨⟨genericPoint Y, hU⟩⟩, hfin⟩

/-- Actual scalar alteration geometry proves properness, dominance and generic finiteness of
ORIGINAL f on the SAME native fpqc scalar square. -/
theorem isAlteration_of_isPullback {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {b : Y' ⟶ Y}
    (H : IsPullback a f' f b) [hf' : IsAlteration f'] [Surjective b] [Flat b] [QuasiCompact b]
    [IsIntegral X] [IsIntegral Y] [IsSeparated f] [LocallyOfFiniteType f] : IsAlteration f := by
  let : UniversallyClosed f := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    H.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let : IsProper f := ⟨⟩
  let : IsDominant (a ≫ f) := by rw [H.w]; infer_instance
  let : IsDominant f := IsDominant.of_comp a f
  exact {
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    genericallyFinite := genericallyFinite_of_isPullback H }

end DeJongAlterations.Geometry.AlterationScalarDescent
