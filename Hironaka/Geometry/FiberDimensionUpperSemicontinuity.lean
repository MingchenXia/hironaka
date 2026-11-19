import Hironaka.Geometry.FiberDimensionUpperSemicontinuityMinimum
import Hironaka.Geometry.FiberDimensionUpperSemicontinuityLocality

/-!
# All actual fiber-dimension thresholds are closed for a proper Noetherian family

Every closed irreducible base subset is given its actual native reduced
closed scheme structure. Actual component covers provide its generic minimum
and common constant open; actual fiber isomorphisms identify its fibers with
the original fibers. Native Noetherian closed-set induction proves closedness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionUpperSemicontinuity

open FiberDimension FiberDimensionUpperSemicontinuityMinimum
  FiberDimensionUpperSemicontinuityLocality

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Source 2.7(b), with every natural threshold and every literal original fiber:
proper morphisms over Noetherian schemes have upper semicontinuous fiber dimension. -/
theorem fiberDimensionUpperSemicontinuous
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] :
    FiberDimension.FiberDimensionUpperSemicontinuous f := by
  intro d
  apply isClosed_of_irreducible_closed_dichotomy (fiberDimensionGE f d)
  intro C hC
  let I : S.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal C
  let T : Scheme.{u} := I.subscheme
  let i : T ⟶ S := I.subschemeι
  let : IsClosedImmersion i := by dsimp [i, T]; infer_instance
  let : IsReduced T := ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme C
  let : IrreducibleSpace T := by
    change IrreducibleSpace C
    exact Subtype.irreducibleSpace hC
  let : IsIntegral T := isIntegral_of_irreducibleSpace_of_isReduced _
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace T := by
    change CompactSpace C
    exact isCompact_iff_compactSpace.mp C.isClosed.isCompact
  let : IsNoetherian T := ⟨⟩
  let W : Scheme.{u} := pullback f i
  let g : W ⟶ T := pullback.snd f i
  let : IsProper g := by dsimp [g, W]; infer_instance
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  let : IsNoetherian W := ⟨⟩
  have hdim (t : T) : fiberDimension g t = fiberDimension f (i t) :=
    fiberDimension_eq_of_preimmersion_isPullback (IsPullback.of_hasPullback f i) t
  obtain ⟨U, hU, hconst⟩ := exists_nonempty_constant_genericFiberDimension g
  by_cases hd : (d : WithBot ℕ∞) ≤ fiberDimension g (genericPoint T)
  · left
    intro s hsC
    let t : T := ⟨s, hsC⟩
    have hle := hd.trans (genericFiberDimension_le_fiberDimension g t)
    rw [hdim] at hle
    exact hle
  · right
    refine ⟨(U : Set T), U.isOpen, ?_, ?_⟩
    · obtain ⟨t⟩ := hU
      exact ⟨t.val, t.property⟩
    · apply Set.disjoint_left.mpr
      intro t htU htE
      have hle : (d : WithBot ℕ∞) ≤ fiberDimension g t := by
        rw [hdim]
        exact htE
      rw [hconst ⟨t, htU⟩] at hle
      exact hd hle

/-- Every original natural-number upper level of the actual fiber dimension is closed. -/
theorem isClosed_fiberDimensionGE
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] (d : ℕ) :
    IsClosed (fiberDimensionGE f d) := fiberDimensionUpperSemicontinuous f d

end Hironaka.Geometry.FiberDimensionUpperSemicontinuity
