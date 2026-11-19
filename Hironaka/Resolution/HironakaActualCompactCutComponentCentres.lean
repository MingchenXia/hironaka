import Hironaka.Resolution.HironakaOriginalFullHistorySuperlevelsAnalytic
import Hironaka.Resolution.HironakaDimensionGlobalComponents

/-!
# Genuine global centres above compact disjoint actual full-cut components

Actual global components supply isolating original windows. Whole local
canonical cuts lie over these compact components, even when the whole ambient
and cosupport are connected and noncompact. Their actual selected centres have
an internally proved whole trace equality and a global admissible union.
Neither smoothness of the cut components nor whole-space maximum canonicality
is assumed. Blueprint: hironaka-actual-compact-full-cut-components-extension.tex.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.HironakaActualCompactCutComponentCentres

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantDriver ResolutionInvariantOrder
  HironakaOriginalCompactUpperCutGlobalPhase HironakaDimensionGlobalComponents
  GlobalComponents InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n k : ℕ} {X Y : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- The literal initial nonstrict whole-value cut, with no component replacement. -/
def initialCut (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (b : Λ) : Set X := actualUpperCut R M .refl b

/-- The actual complement of all OTHER actual global cut components. -/
def componentWindow {Q : Set X} (hQ : IsComplexAnalyticSubset (n := n) Q)
    (K : globalComponents (n := n) Q) : Opens X :=
  ⟨(⋃₀ {L | L ∈ globalComponents (n := n) Q ∧ L ≠ K.val})ᶜ,
    (isClosed_sUnion_globalComponents_subfamily hQ (fun _ hL => hL.1)).isOpen_compl⟩

private theorem component_eq_of_mem_window {Q : Set X}
    (hQ : IsComplexAnalyticSubset (n := n) Q) (K L : globalComponents (n := n) Q)
    {x : X} (hxU : x ∈ componentWindow hQ K) (hxL : x ∈ L.val) : L = K := by
  by_contra hne
  exact hxU (mem_sUnion.mpr ⟨L.val,⟨L.property,fun he => hne (Subtype.ext he)⟩,hxL⟩)

/-- Pairwise disjointness is natural original component data, and actually
produces containment of the WHOLE component in its original open window. -/
theorem component_subset_window {Q : Set X}
    (hQ : IsComplexAnalyticSubset (n := n) Q)
    (hdisj : Pairwise (fun K L : globalComponents (n := n) Q => Disjoint K.val L.val))
    (K : globalComponents (n := n) Q) : K.val ⊆ componentWindow hQ K := by
  intro x hxK hxBad
  obtain ⟨L,⟨hL,hne⟩,hxL⟩ := mem_sUnion.mp hxBad
  have hLK : (⟨L,hL⟩ : globalComponents (n := n) Q) ≠ K := by
    intro he
    exact hne (congrArg Subtype.val he)
  exact disjoint_left.mp (hdisj hLK) hxL hxK

/-- The exact trace is produced from the actual global-component cover. -/
theorem component_window_cut_eq {Q : Set X}
    (hQ : IsComplexAnalyticSubset (n := n) Q)
    (hdisj : Pairwise (fun K L : globalComponents (n := n) Q => Disjoint K.val L.val))
    (K : globalComponents (n := n) Q) : (componentWindow hQ K : Set X) ∩ Q = K.val := by
  apply Subset.antisymm
  · rintro x ⟨hxU,hxQ⟩
    have hx := hxQ
    rw [← sUnion_globalComponents hQ] at hx
    obtain ⟨L,hL,hxL⟩ := mem_sUnion.mp hx
    have he := component_eq_of_mem_window hQ K ⟨L,hL⟩ hxU hxL
    have he' : L = K.val := congrArg Subtype.val he
    simpa only [he'] using hxL
  · intro x hxK
    exact ⟨component_subset_window hQ hdisj K hxK,subset_of_mem_globalComponents hQ K.property hxK⟩

theorem isCompact_component_in_window {Q : Set X}
    (hQ : IsComplexAnalyticSubset (n := n) Q)
    (hdisj : Pairwise (fun K L : globalComponents (n := n) Q => Disjoint K.val L.val))
    (K : globalComponents (n := n) Q) (hK : IsCompact K.val) :
    IsCompact ((Subtype.val : componentWindow hQ K → X) ⁻¹' K.val) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : (Subtype.val : componentWindow hQ K → X) ''
      ((Subtype.val : componentWindow hQ K → X) ⁻¹' K.val) = K.val := by
    apply image_preimage_eq_of_subset
    intro x hx
    exact ⟨⟨x,component_subset_window hQ hdisj K hx⟩,rfl⟩
  rwa [he]

/-- The SAME original compact component contains every actual projected high
point in any genuine local canonical restricted history. -/
theorem current_cut_subset_component
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (b : Λ)
    (hQ : IsComplexAnalyticSubset (n := n) (initialCut R M b))
    (hdisj : Pairwise (fun K L : globalComponents (n := n) (initialCut R M b) => Disjoint K.val L.val))
    (K : globalComponents (n := n) (initialCut R M b)) (T : BlowupTower X Y)
    (hc : IsCanonical (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M))
      (restrict (componentWindow hQ K) T)) :
    actualUpperCut R (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
      (restrict (componentWindow hQ K) T) b ⊆
      (restrict (componentWindow hQ K) T).proj ⁻¹'
        ((Subtype.val : componentWindow hQ K → X) ⁻¹' K.val) := by
  let U := componentWindow hQ K
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
  have hCos : T.proj z.val ∈ M.cosupp := by
    have hh := hOld
    rw [cosupp_pullback_val M (fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)] at hh
    change ((restrict U T).proj z).val ∈ M.cosupp at hh
    rw [proj_restrict] at hh
    exact hh
  change R.inv N .refl ((restrict U T).proj z) = R.inv M .refl ((restrict U T).proj z).val at hVal
  have hPoint : T.proj z.val ∈ initialCut R M b := by
    refine ⟨hCos,?_⟩
    have hv := hz.2.trans hInit
    rw [hVal,proj_restrict] at hv
    exact hv
  have hK : T.proj z.val ∈ K.val := by
    rw [← component_window_cut_eq hQ hdisj K]
    exact ⟨z.property,hPoint⟩
  change ((restrict U T).proj z).val ∈ K.val
  rw [proj_restrict]
  exact hK

/-- Actual properness and the closed whole cut give compactness, even when
the restricted WHOLE cosupport is not compact. -/
theorem isCompact_current_component_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (b : Λ)
    (hQ : IsComplexAnalyticSubset (n := n) (initialCut R M b))
    (hdisj : Pairwise (fun K L : globalComponents (n := n) (initialCut R M b) => Disjoint K.val L.val))
    (K : globalComponents (n := n) (initialCut R M b)) (hK : IsCompact K.val)
    (T : BlowupTower X Y)
    (hc : IsCanonical (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M))
      (restrict (componentWindow hQ K) T)) :
    IsCompact (actualUpperCut R (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
      (restrict (componentWindow hQ K) T) b) := by
  let U : Opens X := componentWindow hQ K
  let N : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hd : IsInvDomain k N := isInvDomain_pullback_val U hM
  have ht : IsGeoTestTower N (restrict U T) :=
    R.isInvValue.isGeoTestTower_of_isCanonical hd (restrict U T) hc
  have hw : (geoTransformAlong N (restrict U T)).IsWellFormed :=
    (isInvDomain_geoTransformAlong hd (restrict U T) ht).isWellFormed
  have hcosclosed : IsClosed (geoTransformAlong N (restrict U T)).cosupp := by
    change IsClosed (GermIdealOrder.cosupport n (geoTransformAlong N (restrict U T)).N
      (geoTransformAlong N (restrict U T)).ideal (geoTransformAlong N (restrict U T)).d)
    exact GiraudAlong.isClosed_cosupport_along hw.isCoherent hw.isClosedSubmanifold_N
      (geoTransformAlong N (restrict U T)).d
  have hclosed : IsClosed (actualUpperCut R N (restrict U T) b) := by
    change IsClosed {p | p ∈ (geoTransformAlong N (restrict U T)).cosupp ∧
      b ≤ R.inv N (restrict U T) p}
    exact (R.isInvValue.usc N hd (restrict U T) hc).isClosed_superlevel hcosclosed b
  exact ((HironakaLocalPrincipalization.isProperMap_proj (restrict U T)).isCompact_preimage
    (isCompact_component_in_window hQ hdisj K hK)).of_isClosed_subset hclosed
      (current_cut_subset_component R M hM b hQ hdisj K T hc)

/-- The true ENTIRE local maximum is used only while a high point remains. -/
def selectedComponentMaximum
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ) : Set Y :=
  if (actualUpperCut R M T b).Nonempty then maxLocus (R.inv M T) (geoTransformAlong M T).cosupp else ∅

theorem selectedComponentMaximum_cases
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ) :
    selectedComponentMaximum R M T b = ∅ ∨
      selectedComponentMaximum R M T b = maxLocus (R.inv M T) (geoTransformAlong M T).cosupp := by
  by_cases h : (actualUpperCut R M T b).Nonempty
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

theorem selectedComponentMaximum_subset_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ) :
    selectedComponentMaximum R M T b ⊆ actualUpperCut R M T b := by
  by_cases h : (actualUpperCut R M T b).Nonempty
  · rw [selectedComponentMaximum,if_pos h]
    intro z hz
    obtain ⟨a,ha⟩ := h
    exact ⟨hz.1,ha.2.trans (hz.2 a ha.1)⟩
  · simp only [selectedComponentMaximum,if_neg h,empty_subset]

theorem selectedComponentMaximum_nonempty
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hc : IsCanonical M (R.inv M) T) (b : Λ)
    (hK : IsCompact (actualUpperCut R M T b)) (hne : (actualUpperCut R M T b).Nonempty) :
    (selectedComponentMaximum R M T b).Nonempty := by
  obtain ⟨a,ha,hmax⟩ := ((R.isInvValue.usc M hM T hc).mono (fun _ h => h.1)).exists_isMaxOn hK hne
  rw [selectedComponentMaximum,if_pos hne]
  refine ⟨a,ha.1,?_⟩
  intro y hy
  by_cases hb : b ≤ R.inv M T y
  · exact hmax y ⟨hy,hb⟩
  · exact (lt_of_not_ge hb).le.trans ha.2

private theorem selectedComponentMaximum_admissible
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hc : IsCanonical M (R.inv M) T) (b : Λ) :
    (geoTransformAlong M T).IsAdmissibleCentre (selectedComponentMaximum R M T b) := by
  rcases selectedComponentMaximum_cases R M T b with he | he
  · rw [he]
    exact MarkedIdeal.isAdmissibleCentre_empty _
  · rw [he]
    exact R.isInvValue.isAdmissibleCentre_maxLocus hM T hc
      (R.isInvValue.isGeoTestTower_of_isCanonical hM T hc)

/-- A genuine whole union of local selected centres over actual cut components. -/
def componentParallelCentre
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (b : Λ)
    (hQ : IsComplexAnalyticSubset (n := n) (initialCut R M b)) : Set Y :=
  ⋃ K : globalComponents (n := n) (initialCut R M b),
    (Subtype.val : openPreimage T (componentWindow hQ K) → Y) ''
      selectedComponentMaximum R (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
        (restrict (componentWindow hQ K) T) b

private theorem selected_base_mem_component
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (b : Λ)
    (hQ : IsComplexAnalyticSubset (n := n) (initialCut R M b))
    (hdisj : Pairwise (fun K L : globalComponents (n := n) (initialCut R M b) => Disjoint K.val L.val))
    (K : globalComponents (n := n) (initialCut R M b)) (T : BlowupTower X Y)
    (hc : IsCanonical (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M))
      (restrict (componentWindow hQ K) T))
    (z : openPreimage T (componentWindow hQ K))
    (hz : z ∈ selectedComponentMaximum R (MarkedIdeal.pullback
      (Subtype.val : componentWindow hQ K → X) M) (restrict (componentWindow hQ K) T) b) :
    T.proj z.val ∈ K.val := by
  have h := current_cut_subset_component R M hM b hQ hdisj K T hc
    (selectedComponentMaximum_subset_cut R _ _ b hz)
  change ((restrict (componentWindow hQ K) T).proj z).val ∈ K.val at h
  rwa [proj_restrict] at h

/-- Actual support over the SAME original entire cut. -/
theorem componentParallelCentre_subset_initial_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (b : Λ)
    (hQ : IsComplexAnalyticSubset (n := n) (initialCut R M b))
    (hdisj : Pairwise (fun K L : globalComponents (n := n) (initialCut R M b) => Disjoint K.val L.val))
    (T : BlowupTower X Y)
    (hc : ∀ K : globalComponents (n := n) (initialCut R M b),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M))
        (restrict (componentWindow hQ K) T)) :
    componentParallelCentre R M T b hQ ⊆ T.proj ⁻¹' initialCut R M b := by
  rintro y hy
  obtain ⟨K,z,hz,rfl⟩ := mem_iUnion.mp hy
  exact subset_of_mem_globalComponents hQ K.property
    (selected_base_mem_component R M hM b hQ hdisj K T (hc K) z hz)

/-- The entire centre trace equality is PRODUCED from the actual component
windows, not supplied as a comparison certificate. -/
theorem preimage_component_parallel_centre
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (b : Λ)
    (hQ : IsComplexAnalyticSubset (n := n) (initialCut R M b))
    (hdisj : Pairwise (fun K L : globalComponents (n := n) (initialCut R M b) => Disjoint K.val L.val))
    (T : BlowupTower X Y)
    (hc : ∀ K : globalComponents (n := n) (initialCut R M b),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M))
        (restrict (componentWindow hQ K) T))
    (K : globalComponents (n := n) (initialCut R M b)) :
    (Subtype.val : openPreimage T (componentWindow hQ K) → Y) ⁻¹'
        componentParallelCentre R M T b hQ =
      selectedComponentMaximum R (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
        (restrict (componentWindow hQ K) T) b := by
  ext z
  constructor
  · intro hz
    obtain ⟨L,w,hw,he⟩ := mem_iUnion.mp hz
    have hwL := selected_base_mem_component R M hM b hQ hdisj L T (hc L) w hw
    have hzL : T.proj z.val ∈ L.val := (congrArg T.proj he) ▸ hwL
    have hLK := component_eq_of_mem_window hQ K L z.property hzL
    subst L
    have hwz : w = z := Subtype.ext he
    simpa only [hwz] using hw
  · intro hz
    exact mem_iUnion.mpr ⟨K,z,hz,rfl⟩

/-- The natural actual histories internally construct a genuine global next
map, with every actual original empty position retained on every window. -/
theorem exists_compact_component_refinement
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (b : Λ)
    (hQ : IsComplexAnalyticSubset (n := n) (initialCut R M b))
    (hdisj : Pairwise (fun K L : globalComponents (n := n) (initialCut R M b) => Disjoint K.val L.val))
    (T : BlowupTower X Y) (hTest : IsGeoTestTower M T)
    (hc : ∀ K : globalComponents (n := n) (initialCut R M b),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M))
        (restrict (componentWindow hQ K) T)) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y)
      (hπ : IsBlowupAlong n (componentParallelCentre R M T b hQ) π),
      IsProperMap π ∧ IsGeoTestTower M (.step T (componentParallelCentre R M T b hQ) π hπ) ∧
      ∀ K : globalComponents (n := n) (initialCut R M b),
        IsCanonical (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M)
          (R.inv (MarkedIdeal.pullback (Subtype.val : componentWindow hQ K → X) M))
          (restrict (componentWindow hQ K) (.step T (componentParallelCentre R M T b hQ) π hπ)) := by
  have hd := isInvDomain_geoTransformAlong hM T hTest
  have hsub := componentParallelCentre_subset_initial_cut R M hM b hQ hdisj T hc
  have ha : (geoTransformAlong M T).IsAdmissibleCentre (componentParallelCentre R M T b hQ) := by
    apply isAdmissibleCentre_of_forall_exists_opens
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hd.isWellFormed.isCoherent hg)
    intro y
    by_cases hy : T.proj y ∈ initialCut R M b
    · rw [← sUnion_globalComponents hQ] at hy
      obtain ⟨K,hK,hyK⟩ := mem_sUnion.mp hy
      let L : globalComponents (n := n) (initialCut R M b) := ⟨K,hK⟩
      let U := componentWindow hQ L
      refine ⟨openPreimage T U,component_subset_window hQ hdisj L hyK,?_⟩
      rw [preimage_component_parallel_centre R M hM b hQ hdisj T hc L]
      have hh := selectedComponentMaximum_admissible R
        (MarkedIdeal.pullback (Subtype.val : U → X) M) (isInvDomain_pullback_val U hM)
        (restrict U T) (hc L) b
      simpa only [geoTransformAlong_restrict U hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent T hTest] using hh
    · let U : Opens X := ⟨(initialCut R M b)ᶜ,hQ.isClosed.isOpen_compl⟩
      refine ⟨openPreimage T U,hy,?_⟩
      have he : (Subtype.val : openPreimage T U → Y) ⁻¹' componentParallelCentre R M T b hQ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact z.property (hsub hz)
      rw [he]
      exact MarkedIdeal.isAdmissibleCentre_empty _
  have hint : interior (componentParallelCentre R M T b hQ) = ∅ :=
    eq_empty_of_subset_empty ((interior_mono ha.2.1).trans (interior_cosupp_eq_empty hd).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup (componentParallelCentre R M T b hQ) ha.1 hint
  refine ⟨Z,π,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,⟨hTest,ha⟩,?_⟩
  intro K
  change IsCanonical _ _ (restrict (componentWindow hQ K) T) ∧ _
  refine ⟨hc K,?_⟩
  rw [preimage_component_parallel_centre R M hM b hQ hdisj T hc K]
  exact selectedComponentMaximum_cases R _ _ b

end

end Hironaka.HironakaActualCompactCutComponentCentres
