/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDiscreteCosupportCanonicalHistory

/-!
# Genuine global centres above a discrete initial strict full-value cut

The entire original cosupport may be connected positive-dimensional and
noncompact. Only the literal initial high-value cut is discrete. Every
current high-cut compactness and whole local-centre trace is derived.
Blueprint: `hironaka-original-discrete-full-cut-centres-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalDiscreteFullCutCentres
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq ResolutionDriver ResolutionInvariantDriver
  CanonicalCentres HironakaComponentwiseCanonicalCentre HironakaComponentwiseCanonicalHistory
  TowerPreimageCompact InvDomainTowerAlong
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- The literal current strict upper full-value cut of the original history. -/
def strictCut (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (threshold : Λ) : Set Y :=
  {y | y∈(geoTransformAlong M T).cosupp ∧ threshold<R.inv M T y}

/-- Every actual canonical next step is nonincreasing on the whole new cosupport. -/
theorem canonical_step_value_le
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    {Z : CMfd.{u} n} (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hc : IsCanonical M (R.inv M) (.step T C π hπ))
    (z : Z) (hz : z∈(geoTransformAlong M (.step T C π hπ)).cosupp) :
    R.inv M (.step T C π hπ) z≤R.inv M T (π z) := by
  rcases hc.2 with hEmpty | hMax
  · exact (R.isInvValue.emptyStep M hM T C π hπ hEmpty hc.1 z hz).le
  · by_cases hne : C.Nonempty
    · have hh := R.isInvValue.decrease M hM T C π hπ hc.1 hne hMax z hz
      by_cases hmem : π z∈C
      · exact (hh.1 hmem).le
      · exact (hh.2 hmem).le
    · have hEmpty : C=∅ := Set.not_nonempty_iff_eq_empty.mp hne
      exact (R.isInvValue.emptyStep M hM T C π hπ hEmpty hc.1 z hz).le

/-- Actual whole-value decrease/empty-position laws imply the true original bound. -/
theorem canonical_value_le_initial
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsCanonical M (R.inv M) T →
      ∀ y∈(geoTransformAlong M T).cosupp,R.inv M T y≤R.inv M .refl (T.proj y) := by
  intro Y T
  induction T with
  | refl => intro _ y _;exact le_rfl
  | @step Y Z T C π hπ ih =>
    intro hc z hz
    have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hM T hc.1
    have hd := isInvDomain_geoTransformAlong hM T hTest
    have hNext := R.isInvValue.isGeoTestTower_of_isCanonical hM (.step T C π hπ) hc
    have hzOld : π z∈(geoTransformAlong M T).cosupp :=
      TransformOffCentre.cosupp_geoTransform_subset_preimage (geoTransformAlong M T)
        hd.isWellFormed.isClosedSubmanifold_N.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hd.isWellFormed.isCoherent hg) hπ hNext.2.2.1 hz
    have hle := canonical_step_value_le R M hM T C π hπ hc z hz
    exact hle.trans (ih hc.1 _ hzOld)

/-- The strong actual USC upper-bound neighbourhood makes the strict cut closed. -/
theorem isClosed_strictCut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hc : IsCanonical M (R.inv M) T) (threshold : Λ) : IsClosed (strictCut R M T threshold) := by
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hd := isInvDomain_geoTransformAlong hM T ht
  have hA := GiraudAlong.isClosed_cosupport_along hd.isWellFormed.isCoherent
    hd.isWellFormed.isClosedSubmanifold_N (geoTransformAlong M T).d
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  by_cases hxA : x∈(geoTransformAlong M T).cosupp
  · have hxv : R.inv M T x≤threshold := le_of_not_gt (fun h => hx ⟨hxA,h⟩)
    filter_upwards [R.isInvValue.usc M hM T hc x hxA] with y hy hyCut
    exact (not_lt_of_ge ((hy hyCut.1).trans hxv)) hyCut.2
  · filter_upwards [hA.isOpen_compl.mem_nhds hxA] with y hy hyCut
    exact hy hyCut.1

/-- An actual original ambient isolating open for the literal strict cut. -/
def cutWindow (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (threshold : Λ) [DiscreteTopology (strictCut R M .refl threshold)]
    (a : strictCut R M .refl threshold) : Opens X :=
  ⟨(discreteTopology_subtype_iff'.mp inferInstance a.val a.property).choose,
    (discreteTopology_subtype_iff'.mp inferInstance a.val a.property).choose_spec.1⟩

theorem cutWindow_inter (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (threshold : Λ) [DiscreteTopology (strictCut R M .refl threshold)]
    (a : strictCut R M .refl threshold) :
    (cutWindow R M threshold a : Set X)∩strictCut R M .refl threshold={a.val} :=
  (discreteTopology_subtype_iff'.mp inferInstance a.val a.property).choose_spec.2

theorem mem_cutWindow (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (threshold : Λ) [DiscreteTopology (strictCut R M .refl threshold)]
    (a : strictCut R M .refl threshold) : a.val∈cutWindow R M threshold a := by
  have hh : a.val∈(cutWindow R M threshold a : Set X)∩strictCut R M .refl threshold := by
    rw [cutWindow_inter]
    exact mem_singleton _
  exact hh.1

/-- No compactness of the whole current or original cosupport is assumed. -/
theorem current_high_cut_subset_fibre
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)] (a : strictCut R M .refl threshold)
    (T : BlowupTower X Y)
    (hc : IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
      (restrict (cutWindow R M threshold a) T)) :
    strictCut R (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
      (restrict (cutWindow R M threshold a) T) threshold ⊆
      (restrict (cutWindow R M threshold a) T).proj ⁻¹' {⟨a.val,mem_cutWindow R M threshold a⟩} := by
  let U := cutWindow R M threshold a
  let N := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hd := isInvDomain_pullback_val U hM
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hd (restrict U T) hc
  intro z hz
  have hInit := canonical_value_le_initial R N hd (restrict U T) hc z hz.1
  have hOld := TransformOffCentre.cosupp_geoTransformAlong_subset N hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isCoherent (restrict U T) ht hz.1
  have hVal := R.isInvValue.restrictOpen M hM U (.refl : BlowupTower X X) trivial
    ((restrict U T).proj z) (by
      have hh := hOld
      rw [cosupp_pullback_val M (fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)] at hh
      exact hh)
  have hCos : T.proj z.val∈M.cosupp := by
    have hh := hOld
    rw [cosupp_pullback_val M (fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)] at hh
    change ((restrict U T).proj z).val∈M.cosupp at hh
    rw [proj_restrict] at hh
    exact hh
  change R.inv N .refl ((restrict U T).proj z)=R.inv M .refl ((restrict U T).proj z).val at hVal
  have hPoint : T.proj z.val∈strictCut R M .refl threshold := by
    refine ⟨hCos,?_⟩
    have hh := lt_of_lt_of_le hz.2 hInit
    rw [hVal] at hh
    rw [proj_restrict] at hh
    exact hh
  have heq : T.proj z.val=a.val := by
    have hh : T.proj z.val∈(U : Set X)∩strictCut R M .refl threshold := ⟨z.property,hPoint⟩
    rw [cutWindow_inter] at hh
    exact hh
  apply Subtype.ext
  rw [proj_restrict]
  exact heq

theorem isCompact_current_high_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)] (a : strictCut R M .refl threshold)
    (T : BlowupTower X Y)
    (hc : IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
      (restrict (cutWindow R M threshold a) T)) :
    IsCompact (strictCut R (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
      (restrict (cutWindow R M threshold a) T) threshold) := by
  have hK := (HironakaLocalPrincipalization.isProperMap_proj (restrict (cutWindow R M threshold a) T)).isCompact_preimage
    (isCompact_singleton (x := (⟨a.val,mem_cutWindow R M threshold a⟩ : cutWindow R M threshold a)))
  exact hK.of_isClosed_subset
    (isClosed_strictCut R _ (isInvDomain_pullback_val _ hM) _ hc threshold)
    (current_high_cut_subset_fibre R M hM threshold a T hc)

/-- Use a whole actual maximum only while a genuine high point remains. -/
def selectedMaximum (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (threshold : Λ) : Set Y :=
  if (strictCut R M T threshold).Nonempty then
    maxLocus (R.inv M T) (geoTransformAlong M T).cosupp else ∅

theorem selectedMaximum_cases (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (threshold : Λ) :
    selectedMaximum R M T threshold=∅ ∨
      selectedMaximum R M T threshold=maxLocus (R.inv M T) (geoTransformAlong M T).cosupp := by
  by_cases hh : (strictCut R M T threshold).Nonempty
  · exact Or.inr (if_pos hh)
  · exact Or.inl (if_neg hh)

theorem selectedMaximum_subset_strictCut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (threshold : Λ) :
    selectedMaximum R M T threshold ⊆ strictCut R M T threshold := by
  by_cases hh : (strictCut R M T threshold).Nonempty
  · rw [selectedMaximum,if_pos hh]
    intro z hz
    obtain ⟨a,ha⟩ := hh
    exact ⟨hz.1,ha.2.trans_le (hz.2 a ha.1)⟩
  · simp only [selectedMaximum,if_neg hh,empty_subset]

theorem selectedMaximum_admissible
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hc : IsCanonical M (R.inv M) T) (threshold : Λ) :
    (geoTransformAlong M T).IsAdmissibleCentre (selectedMaximum R M T threshold) := by
  rcases selectedMaximum_cases R M T threshold with hh | hh
  · rw [hh]
    exact MarkedIdeal.isAdmissibleCentre_empty _
  · rw [hh]
    exact R.isInvValue.isAdmissibleCentre_maxLocus hM T hc
      (R.isInvValue.isGeoTestTower_of_isCanonical hM T hc)

theorem selectedMaximum_nonempty_of_compact_high_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hc : IsCanonical M (R.inv M) T) (threshold : Λ)
    (hK : IsCompact (strictCut R M T threshold)) (hne : (strictCut R M T threshold).Nonempty) :
    (selectedMaximum R M T threshold).Nonempty := by
  obtain ⟨a,ha,hmax⟩ := ((R.isInvValue.usc M hM T hc).mono
    (fun _ h => h.1)).exists_isMaxOn hK hne
  rw [selectedMaximum,if_pos hne]
  refine ⟨a,ha.1,?_⟩
  intro y hy
  by_cases hh : threshold<R.inv M T y
  · exact hmax y ⟨hy,hh⟩
  · exact (le_of_not_gt hh).trans ha.2.le

/-- A whole union; no analytic centre is compactly truncated. -/
def parallelCutCentre (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)] : Set Y :=
  ⋃ a : strictCut R M .refl threshold,
    (Subtype.val : openPreimage T (cutWindow R M threshold a) → Y) ''
      selectedMaximum R (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (restrict (cutWindow R M threshold a) T) threshold

theorem parallelCutCentre_subset_initial_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)]
    (hc : ∀ a : strictCut R M .refl threshold,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
        (restrict (cutWindow R M threshold a) T)) :
    parallelCutCentre R M T threshold ⊆ T.proj ⁻¹' strictCut R M .refl threshold := by
  rintro y hy
  obtain ⟨a,z,hz,rfl⟩ := mem_iUnion.mp hy
  have hHigh := selectedMaximum_subset_strictCut R _ _ threshold hz
  have hh := current_high_cut_subset_fibre R M hM threshold a T (hc a) hHigh
  have he := congrArg Subtype.val hh
  rw [proj_restrict] at he
  change T.proj z.val∈strictCut R M .refl threshold
  rw [he]
  exact a.property

theorem preimage_parallelCutCentre
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)]
    (hc : ∀ a : strictCut R M .refl threshold,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
        (restrict (cutWindow R M threshold a) T)) (a : strictCut R M .refl threshold) :
    (Subtype.val : openPreimage T (cutWindow R M threshold a) → Y) ⁻¹'
      parallelCutCentre R M T threshold=
      selectedMaximum R (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (restrict (cutWindow R M threshold a) T) threshold := by
  ext z
  constructor
  · intro hz
    have hF := parallelCutCentre_subset_initial_cut R M hM T threshold hc hz
    obtain ⟨b,w,hw,he⟩ := mem_iUnion.mp hz
    have hza : T.proj z.val=a.val := by
      have hh : T.proj z.val∈(cutWindow R M threshold a : Set X)∩strictCut R M .refl threshold :=
        ⟨z.property,hF⟩
      rw [cutWindow_inter] at hh
      exact hh
    have hwb : T.proj w.val=b.val := by
      have hh : T.proj w.val∈(cutWindow R M threshold b : Set X)∩strictCut R M .refl threshold :=
        ⟨w.property,by rwa [he]⟩
      rw [cutWindow_inter] at hh
      exact hh
    have hab : a=b := Subtype.ext (hza.symm.trans ((congrArg T.proj he).symm.trans hwb))
    subst b
    have hwz : w=z := Subtype.ext he
    simpa only [hwz] using hw
  · intro hz
    exact mem_iUnion.mpr ⟨a,z,hz,rfl⟩

/-- Natural original local histories alone produce the genuine whole global next centre. -/
theorem exists_discrete_cut_refinement
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hTest : IsGeoTestTower M T) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)]
    (hc : ∀ a : strictCut R M .refl threshold,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
        (restrict (cutWindow R M threshold a) T)) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y)
      (hπ : IsBlowupAlong n (parallelCutCentre R M T threshold) π),
      IsProperMap π ∧ IsGeoTestTower M (.step T (parallelCutCentre R M T threshold) π hπ) ∧
      ∀ a : strictCut R M .refl threshold,
        IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
          (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
          (restrict (cutWindow R M threshold a) (.step T (parallelCutCentre R M T threshold) π hπ)) := by
  have hd := isInvDomain_geoTransformAlong hM T hTest
  have hsub := parallelCutCentre_subset_initial_cut R M hM T threshold hc
  have ha : (geoTransformAlong M T).IsAdmissibleCentre (parallelCutCentre R M T threshold) := by
    apply isAdmissibleCentre_of_forall_exists_opens
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hd.isWellFormed.isCoherent hg)
    intro y
    by_cases hy : T.proj y∈strictCut R M .refl threshold
    · let a : strictCut R M .refl threshold := ⟨T.proj y,hy⟩
      let U := cutWindow R M threshold a
      refine ⟨openPreimage T U,mem_cutWindow R M threshold a,?_⟩
      rw [preimage_parallelCutCentre R M hM T threshold hc a]
      have hh := selectedMaximum_admissible R
        (MarkedIdeal.pullback (Subtype.val : U → X) M) (isInvDomain_pullback_val U hM)
        (restrict U T) (hc a) threshold
      simpa only [geoTransformAlong_restrict U hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent T hTest] using hh
    · let U : Opens X := ⟨(strictCut R M .refl threshold)ᶜ,
        (isClosed_strictCut R M hM .refl trivial threshold).isOpen_compl⟩
      refine ⟨openPreimage T U,hy,?_⟩
      have he : (Subtype.val : openPreimage T U → Y) ⁻¹' parallelCutCentre R M T threshold=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact z.property (hsub hz)
      rw [he]
      exact MarkedIdeal.isAdmissibleCentre_empty _
  have hint : interior (parallelCutCentre R M T threshold)=∅ :=
    eq_empty_of_subset_empty ((interior_mono ha.2.1).trans (interior_cosupp_eq_empty hd).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup (parallelCutCentre R M T threshold) ha.1 hint
  refine ⟨Z,π,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,⟨hTest,ha⟩,?_⟩
  intro a
  change IsCanonical _ _ (restrict (cutWindow R M threshold a) T) ∧ _
  refine ⟨hc a,?_⟩
  rw [preimage_parallelCutCentre R M hM T threshold hc a]
  exact selectedMaximum_cases R _ _ threshold

end
end Hironaka.HironakaOriginalDiscreteFullCutCentres
