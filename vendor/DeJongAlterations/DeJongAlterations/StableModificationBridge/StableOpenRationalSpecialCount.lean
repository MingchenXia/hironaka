import DeJongAlterations.StableModificationBridge.StableOpenRationalNormalization
import DeJongAlterations.StableModificationBridge.StableOpenMarkedSupportCount

/-! Exact ORIGINAL special counts on the SAME arithmetic-genus-zero reduced component. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenRationalSpecialCount

open StableModification
open CurvesField.Genus Omega.ComponentNormalization Omega.ComponentDegree Cohomology
open BlowDown.ClosureComponent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original semi-stable marks and poles remain distinct on the SAME original rational component;
zero arithmetic genus internally supplies the normalization isomorphism and entire original map. -/
theorem specialPoints_encard_eq {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [DeJong.IsNodalCurve (β ≫ g)] [IsProper (β ≫ g)]
    (D' : X.IdealSheafData) (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (v : pullback (C := Scheme.{u}) (β ≫ g) a)
    (hv : v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hp : IsProjectiveOver (closureι v ≫ pullback.snd (β ≫ g) a))
    (hpa : arithmeticGenus (closureScheme v) (structureCoeff (closureι v ≫ pullback.snd (β ≫ g) a)) = 0)
    (E M : Finset (componentNormalization (β ≫ g) a v))
    (hE : ∀ y, y ∈ E ↔ componentMap (β ≫ g) a v y ∉ (β ≫ g).smoothLocus)
    (hM : ∀ y, y ∈ M ↔ componentMap (β ≫ g) a v y ∈ (D'.support : Set X)) :
    (closure {v} ∩ Global.specialPoints β g D' a).encard = (E.card + M.card : ℕ) := by
  classical
  let Y := pullback (C := Scheme.{u}) (β ≫ g) a
  let q := pullback.snd (β ≫ g) a
  let π := normalizationPointsMap ({v} : Set Y)
  have : Finite (genericPoints Y) := finite_genericPoints q
  have : IsReduced Y := DeJong.IsNodalCurve.isReduced_pullback (β ≫ g) K a
  obtain ⟨e, he⟩ := StableOpenRationalNormalization.exists_normalization_iso q
    (topologicalKrullDim_fibre_le_one (β ≫ g) a) v hp
    (exists_mem_closure_ne (β ≫ g) a hv) hpa
    (Curves.IsNodalCurve.isNodalFiber (β ≫ g) K a) hv
  have hinj : Function.Injective π := by
    have hj := (closureι v).isClosedEmbedding.injective.comp e.hom.homeomorph.injective
    change Function.Injective (e.hom ≫ closureι v) at hj
    rwa [he] at hj
  have himage : π '' (π ⁻¹' Global.specialPoints β g D' a) =
      closure {v} ∩ Global.specialPoints β g D' a := by
    rw [Set.image_preimage_eq_range_inter, range_normalizationPointsMap]
  have hdisj : Disjoint E M := Finset.disjoint_left.mpr fun y hyE hyM =>
    (hE y).mp hyE (hpair.support_subset_smoothLocus ((hM y).mp hyM))
  rw [← himage, hinj.encard_image,
    StableOpenMarkedSupportCount.preimage_specialPoints_eq_union β g D' a v E M hE hM,
    ← Finset.coe_union, Set.encard_coe_eq_coe_finsetCard, Finset.card_union_of_disjoint hdisj]

end DeJongAlterations.StableModificationBridge.StableOpenRationalSpecialCount
