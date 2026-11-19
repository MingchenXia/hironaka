import Hironaka.Analytic.Unibranch.HironakaG10GeometricStrictMembership
import Hironaka.Analytic.Unibranch.HironakaG10NativeSumCentreSeparation
import Hironaka.Analytic.Unibranch.HironakaG10StrictSourceThickening
import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
import Hironaka.Resolution.HironakaG10CoherentSupportIdeal

/-!
# Actual geometric separation at the original tracked sum centre

The original boundary and the original local flattener support have disjoint
geometric strict transforms over the domain where the whole centre ideal is
their powered sum. Only the proved geometric-to-algebraic implication is
needed; no reverse strict-support correspondence is assumed.

Blueprint: `hironaka-g10-geometric-sum-centre-separation.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GeometricSumCentreSeparation

noncomputable section

open Hironaka HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreOpenPullback HironakaG10ChowArtinReesCentre
  HironakaG10CoherentSupportIdeal
open Hironaka.Analytic.Unibranch.HironakaG10GeometricStrictMembership
  Hironaka.Analytic.Unibranch.HironakaG10NativeSumCentreSeparation
  Hironaka.Analytic.Unibranch.HironakaG10StrictSourceThickening
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-- Adding the second ideal after a power absorbs every mixed term. -/
theorem pow_sup_absorb {A : Type*} [CommRing A] (I H : Ideal A) (n : ℕ) :
    (I ⊔ H) ^ n ⊔ H = I ^ n ⊔ H := by
  cases n with
  | zero => simp
  | succ n =>
    apply le_antisymm
    · exact sup_le
        ((pow_succ_sup_le I H n).trans (sup_le_sup_left (Ideal.mul_le_left) _))
        le_sup_right
    · exact sup_le_sup (Ideal.pow_right_mono le_sup_left _) le_rfl

variable {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}
  (Z : LocalFlattener f)
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left | LinearMap.range
    (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})

/-- Simultaneous membership in the actual two geometric strict closures
is impossible at the original whole sum-centre stalk. -/
theorem not_both_mem_geometric_strict
    (G : Set X.obj.left) (β : ℕ) (hβ : β ≠ 0)
    (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (hxV : (stepProj B b hDense).hom.left.base x' ∈ Z.V)
    (hStalk : LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((stepProj B b hDense).hom.left.base x')) =
      (intrinsicCentreStalkRange X.obj.left G
        ((stepProj B b hDense).hom.left.base x') ⊔
        Z.H ((stepProj B b hDense).hom.left.base x')) ^ β ⊔
          Z.H ((stepProj B b hDense).hom.left.base x')) :
    ¬ (x' ∈ closure ((stepProj B b hDense).hom.left.base ⁻¹'
          (G \ nonunitLocus B b)) ∧
       x' ∈ closure ((stepProj B b hDense).hom.left.base ⁻¹'
          (Z.support \ nonunitLocus B b))) := by
  intro ⟨hG, hZ⟩
  let x := (stepProj B b hDense).hom.left.base x'
  let I := intrinsicCentreStalkRange X.obj.left G x
  let H := Z.H x
  have hD : LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = I ^ β ⊔ H := by
    exact hStalk.trans (pow_sup_absorb I H β)
  obtain ⟨_, _, _, _, hGI⟩ :=
    exists_equation_and_onStrictTransform_of_mem_closure B b hDense G x' hG I le_rfl
  have hHI : H ≤ intrinsicCentreStalkRange X.obj.left Z.support x :=
    le_intrinsicCentreStalkRange_support X.obj.left Z.V Z.H Z.fg x hxV
  obtain ⟨_, _, _, _, hZH⟩ :=
    exists_equation_and_onStrictTransform_of_mem_closure B b hDense Z.support x' hZ H hHI
  rw [hD] at hGI hZH
  apply not_both_on_strictTransform B b hDense x' (I ^ β) H hD
  exact ⟨(onStrictTransform_source_pow_iff (stepProj B b hDense) x' I (I ^ β ⊔ H)
    hβ).mpr hGI, hZH⟩

/-- Over the original flattener domain the two actual geometric strict
closures are disjoint wherever the whole centre formula holds. -/
theorem geometric_stricts_inter_eq_empty_on
    (G O : Set X.obj.left) (hOV : O ⊆ Z.V) (β : ℕ) (hβ : β ≠ 0)
    (hStalk : ∀ x ∈ O, LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) =
      (intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x) ^ β ⊔ Z.H x) :
    (stepProj B b hDense).hom.left.base ⁻¹' O ∩
      closure ((stepProj B b hDense).hom.left.base ⁻¹' (G \ nonunitLocus B b)) ∩
      closure ((stepProj B b hDense).hom.left.base ⁻¹' (Z.support \ nonunitLocus B b)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x' hx'
  exact not_both_mem_geometric_strict Z B b hDense G β hβ x'
    (hOV hx'.1.1) (hStalk _ hx'.1.1) ⟨hx'.1.2, hx'.2⟩

/-- The exact eventual centre formula supplied at an original tracked
boundary point yields actual geometric separation over an open neighbourhood. -/
theorem exists_open_geometric_stricts_separated_of_eventually
    (G : Set X.obj.left) (β : ℕ) (hβ : β ≠ 0) (x : X.obj.left) (hxV : x ∈ Z.V)
    (hStalk : ∀ᶠ y in 𝓝 x, LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b y) =
      (intrinsicCentreStalkRange X.obj.left G y ⊔ Z.H y) ^ β ⊔ Z.H y) :
    ∃ O : Set X.obj.left, IsOpen O ∧ x ∈ O ∧ O ⊆ Z.V ∧
      (stepProj B b hDense).hom.left.base ⁻¹' O ∩
        closure ((stepProj B b hDense).hom.left.base ⁻¹' (G \ nonunitLocus B b)) ∩
        closure ((stepProj B b hDense).hom.left.base ⁻¹' (Z.support \ nonunitLocus B b)) = ∅ := by
  obtain ⟨O, hO, hOo, hxO⟩ := eventually_nhds_iff.mp hStalk
  refine ⟨O ∩ Z.V, hOo.inter Z.isOpen, ⟨hxO, hxV⟩, inter_subset_right, ?_⟩
  exact geometric_stricts_inter_eq_empty_on Z B b hDense G (O ∩ Z.V)
    inter_subset_right β hβ (fun y hy => hO y hy.1)

end

end Hironaka.Analytic.Unibranch.HironakaG10GeometricSumCentreSeparation
