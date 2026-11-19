import Hironaka.Geometry.FiberDimensionGenericGlobalAffine
import Hironaka.Geometry.AlterationComposition

/-!
# Generic constancy of actual fibers over an arbitrary integral base

All affine neighborhoods, finite source covers and constant-dimension opens
are internally constructed from the original dominant finite-type morphism.
Both original and literally restricted scheme-theoretic fibers are computed.
This establishes generic constancy, not full upper semicontinuity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionGenericGlobal

open FiberDimension FiberDimensionGenericRestriction

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- A dominant finite-type morphism of integral schemes internally yields a dense
nonempty open where its original and restricted fibers have their computed generic dimension. -/
theorem exists_nonempty_dense_constant_fiberDimension
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f] :
    ∃ U : Y.Opens, Nonempty U ∧ Dense (U : Set Y) ∧ ∃ n : ℕ,
      fiberDimension f (genericPoint Y) = n ∧
      (∀ s : U, fiberDimension f s.val = n) ∧
      ∀ s : U, fiberDimension (f ∣_ U) s = n := by
  obtain ⟨V, hV, hη, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint Y) (U := (⊤ : Y.Opens)) (by trivial)
  let : Nonempty V := ⟨⟨genericPoint Y, hη⟩⟩
  let : IsAffine V.toScheme := hV
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : Nonempty (f ⁻¹ᵁ V).toScheme := ⟨⟨genericPoint X, by
    change f (genericPoint X) ∈ V
    rw [genericPoint_map_of_isDominant f]
    exact hη⟩⟩
  let : IsIntegral (f ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  let : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  have : IsDominant (f ∣_ V) := IsZariskiLocalAtTarget.restrict (inferInstance : IsDominant f) V
  obtain ⟨W, hW, hWdense, n, hdim⟩ :=
    FiberDimensionGenericGlobalAffine.exists_nonempty_dense_constant_fiberDimension (f ∣_ V)
  let U : Y.Opens := V.ι ''ᵁ W
  have hU : Nonempty U := hW.map (V.ι.isoImage W).hom
  have hfull (s : U) : fiberDimension f s.val = n := by
    have hs := s.property
    change s.val ∈ V.ι '' (W : Set V) at hs
    obtain ⟨t, ht, hts⟩ := hs
    have hd := (fiberDimension_morphismRestrict f V t).symm.trans (hdim ⟨t, ht⟩)
    simpa only [hts] using hd
  have hηU : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  refine ⟨U, hU, U.isOpen.dense (by simpa using hU), n, hfull ⟨_, hηU⟩, hfull, ?_⟩
  intro s
  exact (fiberDimension_morphismRestrict f U s).trans (hfull s)

/-- On an internally constructed dense nonempty open every original fiber has the actual generic dimension. -/
theorem exists_nonempty_dense_fiberDimension_eq_generic
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f] :
    ∃ U : Y.Opens, Nonempty U ∧ Dense (U : Set Y) ∧
      ∀ s : U, fiberDimension f s.val = fiberDimension f (genericPoint Y) := by
  obtain ⟨U, hU, hdense, n, hgen, hfull, hrestricted⟩ :=
    exists_nonempty_dense_constant_fiberDimension f
  exact ⟨U, hU, hdense, fun s => (hfull s).trans hgen.symm⟩

end Hironaka.Geometry.FiberDimensionGenericGlobal
