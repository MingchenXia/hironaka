import DeJongAlterations.Geometry.FiberDimension
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The actual positive-dimensional fiber locus is closed

For locally finite-type morphisms, zero-dimensional actual fibers are exactly
the discrete fibers, equivalently those consisting entirely of native
quasi-finite points. Thus the positive-dimensional fiber locus is the image
of the closed complement of the native quasi-finite locus. Universal
closedness makes this image closed. This is the threshold-one case of source
2.7(b); all thresholds follow when the actual fibers have dimension at most
one. No general higher-dimensional semicontinuity is asserted here.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace DeJongAlterations.Geometry.FiberDimensionOne

open FiberDimension

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-- An actual fiber is discrete exactly when every point above it is quasi-finite. -/
theorem discreteTopology_fiber_iff (s : S) :
    DiscreteTopology (f.fiber s) ↔ ∀ x : X, f x = s → f.QuasiFiniteAt x := by
  constructor
  · intro hd x hx
    subst s
    let := hd
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  · intro hq
    have hd : DiscreteTopology (f ⁻¹' {s}) := by
      rw [discreteTopology_iff_isOpen_singleton]
      rintro ⟨x, hx⟩
      change f x = s at hx
      subst s
      rw [← (f.fiberHomeo (f x)).symm.isOpen_image, Set.image_singleton]
      exact (hq x rfl).isClopen_singleton_asFiber.isOpen
    let := hd
    exact (f.fiberHomeo s).symm.discreteTopology

/-- Locally finite-type fibers are locally Noetherian, so dimension at most zero means discrete. -/
theorem fiberDimension_le_zero_iff_discreteTopology (s : S) :
    fiberDimension f s ≤ 0 ↔ DiscreteTopology (f.fiber s) := by
  constructor
  · intro hdim
    have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have : IsLocallyNoetherian (f.fiber s) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
    have : IsLocallyArtinian (f.fiber s) :=
      IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
    infer_instance
  · intro hd
    let := hd
    exact topologicalKrullDim_zero_of_discreteTopology (f.fiber s)

/-- The actual zero-dimensional fiber criterion uses all native points above the target point. -/
theorem fiberDimension_le_zero_iff_forall_quasiFiniteAt (s : S) :
    fiberDimension f s ≤ 0 ↔ ∀ x : X, f x = s → f.QuasiFiniteAt x :=
  (fiberDimension_le_zero_iff_discreteTopology f s).trans (discreteTopology_fiber_iff f s)

/-- Positive dimension is exactly the presence of an actual non-quasi-finite point in the fiber. -/
theorem one_le_fiberDimension_iff_exists_not_quasiFiniteAt (s : S) :
    (1 : WithBot ℕ∞) ≤ fiberDimension f s ↔
      ∃ x : X, f x = s ∧ ¬ f.QuasiFiniteAt x := by
  have hthreshold : (1 : WithBot ℕ∞) ≤ fiberDimension f s ↔ ¬ fiberDimension f s ≤ 0 := by
    simpa only [Nat.cast_zero, zero_add, lt_iff_not_ge] using
      (ENat.WithBot.add_one_le_iff (n := 0) (m := fiberDimension f s))
  rw [hthreshold, fiberDimension_le_zero_iff_forall_quasiFiniteAt]
  push Not
  rfl

/-- The actual first dimension level is the image of the complement of the native quasi-finite locus. -/
theorem fiberDimensionGE_one_eq_image :
    fiberDimensionGE f 1 = f '' ((f.quasiFiniteLocus : Set X)ᶜ) := by
  ext s
  constructor
  · intro hs
    obtain ⟨x, hx, hq⟩ := (one_le_fiberDimension_iff_exists_not_quasiFiniteAt f s).mp hs
    exact ⟨x, hq, hx⟩
  · rintro ⟨x, hq, hx⟩
    exact (one_le_fiberDimension_iff_exists_not_quasiFiniteAt f s).mpr ⟨x, hx, hq⟩

/-- The positive-dimensional fiber locus is closed for a locally finite-type universally closed map. -/
theorem isClosed_fiberDimensionGE_one [UniversallyClosed f] :
    IsClosed (fiberDimensionGE f 1) := by
  rw [fiberDimensionGE_one_eq_image]
  exact f.isClosedMap _ f.quasiFiniteLocus.2.isClosed_compl

omit [LocallyOfFiniteType f] in
/-- If all actual fibers have dimension at most one, every threshold at least two is empty. -/
theorem fiberDimensionGE_add_two_eq_empty
    (hbound : ∀ s : S, fiberDimension f s ≤ 1) (d : ℕ) :
    fiberDimensionGE f (d + 2) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have h := hs.trans (hbound s)
  have hpos : (1 : WithBot ℕ∞) < ((d + 2 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos d)
  exact hpos.not_ge h

/-- Full native upper semicontinuity under the actual relative-dimension-at-most-one bound. -/
theorem fiberDimensionUpperSemicontinuous_of_le_one [UniversallyClosed f]
    (hbound : ∀ s : S, fiberDimension f s ≤ 1) : FiberDimensionUpperSemicontinuous f := by
  intro d
  match d with
  | 0 => exact isClosed_fiberDimensionGE_zero f
  | 1 => exact isClosed_fiberDimensionGE_one f
  | d + 2 =>
    rw [fiberDimensionGE_add_two_eq_empty f hbound]
    exact isClosed_empty

end DeJongAlterations.Geometry.FiberDimensionOne
