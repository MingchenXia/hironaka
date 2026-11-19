import Hironaka.Geometry.CurveFibrationBaseChange

/-!
# Original native-fibre density implies density on every actual field fibre

The exact original subset and actual Cartesian projections are retained.
The coefficient map between field spectra is universally open, so every
base change of it pulls back a dense original residue-fibre subset densely.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Density on every ORIGINAL native residue-field fibre implies density on every actual field fibre. -/
theorem dense_fieldFiber_preimage_of_fiberwise_dense {X S : Scheme.{u}}
    (f : X ⟶ S) (B : Set X)
    (hB : ∀ s : S, Dense ((f.fiberι s) ⁻¹' B))
    {L : Type u} [Field L] (a : Spec (.of L) ⟶ S) :
    Dense ((pullback.fst f a) ⁻¹' B) := by
  obtain ⟨⟨s, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L S).symm.surjective a
  let p := f.fiberToSpecResidueField s
  let b := Spec.map φ
  let H := (IsPullback.of_hasPullback p b).paste_horiz
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
  have hd := (hB s).preimage (pullback.fst p b).isOpenMap
  have hi : H.isoPullback.inv ≫ (pullback.fst p b ≫ f.fiberι s) =
      pullback.fst f (b ≫ S.fromSpecResidueField s) := by
    calc
      _ = H.isoPullback.inv ≫ (H.isoPullback.hom ≫
          pullback.fst f (b ≫ S.fromSpecResidueField s)) :=
        congrArg (fun t => H.isoPullback.inv ≫ t) H.isoPullback_hom_fst.symm
      _ = _ := by simp
  have ht := hd.preimage H.isoPullback.inv.isOpenMap
  change Dense ((H.isoPullback.inv ≫ pullback.fst p b ≫ f.fiberι s) ⁻¹' B) at ht
  rw [hi] at ht
  exact ht

/-- Every actual field fibre retains density of the EXACT original smooth locus. -/
theorem original_smoothLocus_fieldFiber_dense {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hsm : ∀ s : S, Dense ((f.fiberι s) ⁻¹' (f.smoothLocus : Set X)))
    {L : Type u} [Field L] (a : Spec (.of L) ⟶ S) :
    Dense ((pullback.fst f a) ⁻¹' (f.smoothLocus : Set X)) :=
  dense_fieldFiber_preimage_of_fiberwise_dense f _ hsm a

end Hironaka.Geometry.CurveFibrationBaseChange
