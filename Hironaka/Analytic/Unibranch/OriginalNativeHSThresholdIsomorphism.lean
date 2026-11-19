import Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction
import Hironaka.Analytic.Unibranch.OriginalIntrinsicHSSuperlevels
import Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRegularity
import Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction

/-! Full actual isomorphisms outside ONE fixed original singular HS
threshold compose and survive genuine native open restriction. No future
phase, rank certificate, Lex-WF or old-space properness is assumed.
Blueprint FIRST: original-native-hs-threshold-isomorphism.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11HSPhaseInduction HironakaG11CompatibleAnalyticCover
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  OriginalRelativelyCompactRestriction

theorem threshold_iff_at_isIsoOver {X Y : SourceReducedComplexSpace} (H : ℕ → ℕ)
    {q : Y ⟶ X} {U : Set X.obj.left} (hq : IsIsoOver q U)
    {y : Y.obj.left} (hy : q.hom.left.base y ∈ U) :
    y ∈ originalSingularHSThreshold Y H ↔
      q.hom.left.base y ∈ originalSingularHSThreshold X H := by
  have hSing : y ∈ intrinsicSingularLocus Y.obj ↔
      q.hom.left.base y ∈ intrinsicSingularLocus X.obj :=
    not_congr (hq.mem_intrinsicRegularLocus_iff hy)
  change (y ∈ intrinsicSingularLocus Y.obj ∧ ∀ l,H l ≤ originalStalkHS Y y l) ↔
    (q.hom.left.base y ∈ intrinsicSingularLocus X.obj ∧
      ∀ l,H l ≤ originalStalkHS X (q.hom.left.base y) l)
  rw [hSing,originalStalkHS_isIsoOver hq hy]

theorem threshold_preimage_openImmersion {X B : SourceReducedComplexSpace} (H : ℕ → ℕ)
    (j : B ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    j.hom.left.base ⁻¹' originalSingularHSThreshold X H = originalSingularHSThreshold B H := by
  ext y
  have hSing : j.hom.left.base y ∈ intrinsicSingularLocus X.obj ↔
      y ∈ intrinsicSingularLocus B.obj :=
    Set.ext_iff.mp (preimage_intrinsicSingularLocus_of_isOpenImmersion j hj) y
  change (j.hom.left.base y ∈ intrinsicSingularLocus X.obj ∧
      ∀ l,H l ≤ originalStalkHS X (j.hom.left.base y) l) ↔
    (y ∈ intrinsicSingularLocus B.obj ∧ ∀ l,H l ≤ originalStalkHS B y l)
  rw [hSing,originalStalkHS_openImmersion j hj y]

theorem preimage_compl_threshold_subset {X Y : SourceReducedComplexSpace} (H : ℕ → ℕ)
    (q : Y ⟶ X) (hq : IsIsoOver q (originalSingularHSThreshold X H)ᶜ) :
    q.hom.left.base ⁻¹' (originalSingularHSThreshold X H)ᶜ ⊆
      (originalSingularHSThreshold Y H)ᶜ := by
  intro y hy hyThreshold
  exact hy ((threshold_iff_at_isIsoOver H hq hy).mp hyThreshold)

theorem isIsoOver_comp_threshold_compl {X Y Z : SourceReducedComplexSpace} (H : ℕ → ℕ)
    (q : Y ⟶ X) (p : Z ⟶ Y)
    (hq : IsIsoOver q (originalSingularHSThreshold X H)ᶜ)
    (hp : IsIsoOver p (originalSingularHSThreshold Y H)ᶜ) :
    IsIsoOver (p ≫ q) (originalSingularHSThreshold X H)ᶜ :=
  hq.comp (hp.of_isOpen_subset (hq.isOpen.preimage q.hom.left.base.hom.continuous)
    (preimage_compl_threshold_subset H q hq))

theorem isIsoOver_open_square_threshold_compl {X Y A B : SourceReducedComplexSpace}
    (H : ℕ → ℕ) (q : Y ⟶ X) (p : A ⟶ B) (l : A ⟶ Y) (j : B ⟶ X)
    (hl : LocallyRingedSpace.IsOpenImmersion l.hom.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (hsq : p ≫ j = l ≫ q)
    (hrange : range l.hom.left.base = q.hom.left.base ⁻¹' range j.hom.left.base)
    (hq : IsIsoOver q (originalSingularHSThreshold X H)ᶜ) :
    IsIsoOver p (originalSingularHSThreshold B H)ᶜ := by
  have h := OriginalLocalStrictWindowRegularity.isIsoOver_of_open_square
    q p l j hl hj hsq hrange (originalSingularHSThreshold X H)ᶜ hq
  rw [preimage_compl,threshold_preimage_openImmersion H j hj] at h
  exact h

theorem isIsoOver_restrictionProjection_threshold_compl {X Y : SourceReducedComplexSpace}
    (H : ℕ → ℕ) (q : Y ⟶ X) (hqProper : IsProperMap q.hom.left.base)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
    (hq : IsIsoOver q (originalSingularHSThreshold X H)ᶜ) :
    IsIsoOver (restrictionProjection U q hU hqProper)
      (originalSingularHSThreshold (restriction X U hU) H)ᶜ := by
  let j := inclusion X U hU
  let l := inclusion Y (preimageOpen U q) (isCompact_closure_preimage U q hU hqProper)
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left := inclusion_isOpenImmersion X U hU
  have hl : LocallyRingedSpace.IsOpenImmersion l.hom.left :=
    inclusion_isOpenImmersion Y (preimageOpen U q) (isCompact_closure_preimage U q hU hqProper)
  have hr : range l.hom.left.base = q.hom.left.base ⁻¹' range j.hom.left.base := by
    rw [inclusion_range,inclusion_range]
    rfl
  exact isIsoOver_open_square_threshold_compl H q (restrictionProjection U q hU hqProper) l j hl hj
    (restrictionProjection_inclusion U q hU hqProper) hr hq

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism
