import Hironaka.Resolution.HironakaG10HirIdealGerms
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback

/-! # A locally generated ideal family lies in its intrinsic support ideal -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
namespace Hironaka.HironakaG10CoherentSupportIdeal
noncomputable section
open HironakaG10HirIdealGerms HironakaIntrinsicReducedCentreIdealSheaf
  HironakaIntrinsicReducedCentreIdealModel HironakaIntrinsicReducedCentreOpenPullback
universe u

/-- Original local generators are actual sections of the native ideal of
the family's nonunit support. The claim needs no openness or analyticity. -/
theorem le_intrinsicCentreStalkRange_support
    (X : LocallyRingedSpace.{u}) (V : Set X)
    (J : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hJ : IsLocallyFinitelyGeneratedOn X V J) (x : X) (hx : x ∈ V) :
    J x ≤ intrinsicCentreStalkRange X {y | y ∈ V ∧ J y ≠ ⊤} x := by
  let C : Set X := {y | y ∈ V ∧ J y ≠ ⊤}
  obtain ⟨U, hxU, r, s, hs⟩ := hJ x hx
  rw [hs x hxU hx]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hsection : s i ∈ intrinsicReducedCentreSectionIdeal X C U := by
    intro y hy hyC
    apply IsLocalRing.le_maximalIdeal hyC.2
    rw [hs y hy hyC.1]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨TopCat.Presheaf.germ (intrinsicReducedCentreIdealModule X C).val.presheaf
    U x hxU ⟨s i, hsection⟩, ?_⟩
  exact intrinsicReducedCentreStalkInclusion_germ X C x U hxU ⟨s i, hsection⟩

end
end Hironaka.HironakaG10CoherentSupportIdeal
