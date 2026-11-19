import Hironaka.Analytic.Unibranch.HironakaG11BennettStabilization
import Hironaka.Analytic.Unibranch.OriginalIntrinsicHSSuperlevels

/-! The actual finite singular HS rank on a compact subset, without
CompactSpace X/Y. Strict descent uses real pointwise HSValue/Bennett and
actual present-phase geometry, never lex-function well-foundedness.
Blueprint FIRST: original-native-compact-shadow-rank.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry Classical
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeCompactShadowRank
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11HSPhaseInduction HironakaG11CompatibleAnalyticCover
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels

def shadowHSSet (X : SourceReducedComplexSpace) (K : Set X.obj.left) : Set HSValue :=
  hsValue X '' (K ∩ intrinsicSingularLocus X.obj)

theorem shadowHSSet_finite (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) : (shadowHSSet X K).Finite := by
  apply Set.Finite.of_finite_image (f := Subtype.val) _ Subtype.val_injective.injOn
  apply (OriginalCompactIntrinsicHSProfiles.original_stalk_hs_finite_range_on_compact X K hK).subset
  rintro _ ⟨_,⟨x,⟨hxK,_hxS⟩,rfl⟩,rfl⟩
  exact ⟨x,hxK,rfl⟩

def shadowHSValues (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K) :
    Finset HSValue := (shadowHSSet_finite X K hK).toFinset

theorem mem_shadowHSValues {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    {hK : IsCompact K} {v : HSValue} :
    v ∈ shadowHSValues X K hK ↔
      ∃ x ∈ K, x ∈ intrinsicSingularLocus X.obj ∧ hsValue X x = v := by
  rw [shadowHSValues,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨x,⟨hxK,hxS⟩,hx⟩
    exact ⟨x,hxK,hxS,hx⟩
  · rintro ⟨x,hxK,hxS,hx⟩
    exact ⟨x,⟨hxK,hxS⟩,hx⟩

def rank (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K) :
    Multiset HSValue := (shadowHSValues X K hK).val

theorem rank_order_wellFounded :
    WellFounded (Multiset.IsDershowitzMannaLT : Multiset HSValue → Multiset HSValue → Prop) := by
  let : WellFoundedLT HSValue := HironakaG11BennettStabilization.hsStabilization
  exact Multiset.wellFounded_isDershowitzMannaLT

theorem shadowHSValues_openImmersion {X B : SourceReducedComplexSpace}
    (j : B ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (K : Set X.obj.left) (hK : IsCompact K) (hRange : K ⊆ range j.hom.left.base) :
    shadowHSValues B (j.hom.left.base ⁻¹' K)
        (hj.base_open.isEmbedding.isInducing.isCompact_preimage' hK hRange) =
      shadowHSValues X K hK := by
  ext v
  have hSing := preimage_intrinsicSingularLocus_of_isOpenImmersion j hj
  constructor
  · intro hv
    obtain ⟨b,hbK,hbS,hbv⟩ := mem_shadowHSValues.mp hv
    have hjS : j.hom.left.base b ∈ intrinsicSingularLocus X.obj :=
      (Set.ext_iff.mp hSing b).mpr hbS
    exact mem_shadowHSValues.mpr ⟨j.hom.left.base b,hbK,hjS,
      (Subtype.ext (originalStalkHS_openImmersion j hj b)).trans hbv⟩
  · intro hv
    obtain ⟨x,hxK,hxS,hxv⟩ := mem_shadowHSValues.mp hv
    obtain ⟨b,hb⟩ := hRange hxK
    have hbK : j.hom.left.base b ∈ K := hb ▸ hxK
    have hjS : j.hom.left.base b ∈ intrinsicSingularLocus X.obj := hb ▸ hxS
    have hbS : b ∈ intrinsicSingularLocus B.obj := (Set.ext_iff.mp hSing b).mp hjS
    exact mem_shadowHSValues.mpr ⟨b,hbK,hbS,
      (Subtype.ext (originalStalkHS_openImmersion j hj b).symm).trans
        ((congrArg (hsValue X) hb).trans hxv)⟩

theorem rank_openImmersion {X B : SourceReducedComplexSpace}
    (j : B ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (K : Set X.obj.left) (hK : IsCompact K) (hRange : K ⊆ range j.hom.left.base) :
    rank B (j.hom.left.base ⁻¹' K)
        (hj.base_open.isEmbedding.isInducing.isCompact_preimage' hK hRange) = rank X K hK :=
  congrArg Finset.val (shadowHSValues_openImmersion j hj K hK hRange)

/-- The actual present map's HS/nonincrease, off-threshold native iso and
elimination imply strict DM descent on its actual compact inverse shadow. -/
theorem rank_drop {X Y : SourceReducedComplexSpace} (q : Y ⟶ X)
    (hq : IsProperMap q.hom.left.base) (K : Set X.obj.left) (hK : IsCompact K)
    (a : X.obj.left) (haK : a ∈ K) (haS : a ∈ intrinsicSingularLocus X.obj)
    (hMax : ∀ x ∈ K, x ∈ intrinsicSingularLocus X.obj →
      toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X a))
    (hNoninc : ∀ y, q.hom.left.base y ∈ K → y ∈ intrinsicSingularLocus Y.obj →
      originalStalkHS Y y ≤ originalStalkHS X (q.hom.left.base y))
    (hOff : IsIsoOver q (originalSingularHSThreshold X (originalStalkHS X a))ᶜ)
    (hElim : ∀ y, q.hom.left.base y ∈ K → y ∈ intrinsicSingularLocus Y.obj →
      originalStalkHS Y y ≠ originalStalkHS X a) :
    Multiset.IsDershowitzMannaLT
      (rank Y (q.hom.left.base ⁻¹' K) (hq.isCompact_preimage hK)) (rank X K hK) := by
  classical
  apply isDershowitzMannaLT_of_replace
    (h := hsValue X a) (mem_shadowHSValues.mpr ⟨a,haK,haS,rfl⟩)
  intro v hv
  obtain ⟨y,hyK,hyS,rfl⟩ := mem_shadowHSValues.mp hv
  by_cases hThreshold : q.hom.left.base y ∈ originalSingularHSThreshold X (originalStalkHS X a)
  · right
    have hOld : originalStalkHS X (q.hom.left.base y) = originalStalkHS X a :=
      congrArg ofLex (le_antisymm (hMax _ hyK hThreshold.1) (Pi.toLex_monotone hThreshold.2))
    have hLe : originalStalkHS Y y ≤ originalStalkHS X a := hOld ▸ hNoninc y hyK hyS
    have hLt : originalStalkHS Y y < originalStalkHS X a := lt_of_le_of_ne hLe (hElim y hyK hyS)
    exact hLt
  · left
    have hyOff : q.hom.left.base y ∈ (originalSingularHSThreshold X (originalStalkHS X a))ᶜ := hThreshold
    have hOldSing : q.hom.left.base y ∈ intrinsicSingularLocus X.obj :=
      fun hreg => hyS ((hOff.mem_intrinsicRegularLocus_iff hyOff).mpr hreg)
    have hEq := originalStalkHS_isIsoOver hOff hyOff
    refine ⟨mem_shadowHSValues.mpr ⟨_,hyK,hOldSing,Subtype.ext hEq.symm⟩,?_⟩
    intro hval
    exact hElim y hyK hyS (congrArg Subtype.val hval)

end
end Hironaka.Analytic.Unibranch.OriginalNativeCompactShadowRank
