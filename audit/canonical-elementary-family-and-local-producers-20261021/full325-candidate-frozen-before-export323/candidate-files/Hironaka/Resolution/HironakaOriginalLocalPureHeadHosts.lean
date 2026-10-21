/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalCanonicalPartListResolution
import Hironaka.Resolution.HironakaOriginalLocalPureBoundaryCanonicalPrefix
import Hironaka.Resolution.HironakaOriginalCanonicalOrderedResolution

/-!
# Actual local pure first-meeting heads with genuine compact-enclosed hosts

Whole actual smooth pure-head transport discharges the real next-maximum
condition. Original locally good data then internally choose a first-meeting
stage on a larger open and its actual pullback to the local base.
Blueprint: `hironaka-original-local-pure-head-hosts-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalPureHeadHosts
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  CanonicalCentres HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
  EmbeddedFromResolution HironakaEmbeddedAnalytic HironakaOriginalCanonicalSumSeparation
  HironakaOriginalCanonicalPartListResolution HironakaOriginalPureBoundaryCanonicalPrefix
  HironakaOriginalSmoothIntrinsicRegularLoci HironakaOriginalPureBoundaryIndependentSource
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionCartesianTower
  HironakaOriginalStoppedPrefixSmoothComparison HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionRelativeControlledTower

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open HironakaOriginalCanonicalOrderedResolution HironakaOriginalLocalPureBoundaryCanonicalPrefix
  HironakaEmbeddedAnalyticLocal HironakaBaseChange HironakaActualOpenTowerHosts
  HironakaSmoothSubmersionOrderedGlobalTrace
variable {n m : ℕ} {X D : CMfd.{u} n} {Y E F : CMfd.{u} m} {b : Y → X}

private theorem partMarkedIdeal_pullback
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (E₀ : List (Set X)) (A : Set X) :
    markedPullback (m := m) b (partMarkedIdeal E₀ A) =
      partMarkedIdeal (E₀.map (b ⁻¹' ·)) (b ⁻¹' A) := by
  change (⟨b ⁻¹' univ,E₀.map (b ⁻¹' ·),GermIdeal.pullback (m := m) b (vanishingIdeal (n := n) A),1⟩ :
    MarkedIdeal m Y) = _
  rw [preimage_univ,HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb A]
  rfl

private theorem source_maximum_over_good_open
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g)
    (hc : IsCanonical (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)) T)
    (ha : CentresAvoid (boundaryGoodOpen W hWa d E₀ hE₀) T)
    (hm : W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv
        (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).cosupp,
        T.proj c ∈ boundaryGoodOpen W hWa d E₀ hE₀)
    (hne : (b ⁻¹' W).Nonempty) :
    let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
    let N := markedPullback (m := m) b M
    let O := boundaryGoodOpen W hWa d E₀ hE₀
    ∃ z ∈ maxLocus ((canonicalInvariant m).inv N Q) (geoTransformAlong N Q).cosupp,
      b (Q.proj z) ∈ O := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let N := markedPullback (m := m) b M
  let O := boundaryGoodOpen W hWa d E₀ hE₀
  let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  let hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have ht := hF.isGeoTestTower_of_isCanonical hM T hc
  have hcs := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary
    h M hM.isWellFormed ht
  have hdense : W ⊆ closure (W ∩ (O : Set X)) := HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  have hEO : ∀ H ∈ E₀, Disjoint H (O : Set X) := fun H hH =>
    disjoint_left.mpr fun x hxH hxO => hxO (Or.inr (mem_biUnion hH hxH))
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := by
    intro x hxW hxO
    by_contra hh
    exact hxO (Or.inl ⟨hxW,hh⟩)
  have hneWO : (b ⁻¹' (W ∩ (O : Set X))).Nonempty := by
    by_contra hh
    have he := Set.not_nonempty_iff_eq_empty.mp hh
    obtain ⟨y,hy⟩ := hne
    have hz := preimage_mono (f := b) hdense hy
    have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
    rw [hbo.preimage_closure_eq_closure_preimage hb.contMDiff.continuous,he,closure_empty] at hz
    exact hz
  obtain ⟨y,hyW,hyO⟩ := hneWO
  obtain ⟨z,hzy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective Q.isBlowupSequence y
  obtain ⟨c,hcm,hcO⟩ := hm ⟨b y,hyW⟩
  have hzO : T.proj (g z) ∈ O := by rw [h.proj_comm,hzy]; exact hyO
  have hzW : T.proj (g z) ∈ W := by rw [h.proj_comm,hzy]; exact hyW
  have hzm : g z ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp :=
    (HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O hEO
      (fun x hx => hreg x hx x.2) hM T hc ha hcm hcO hzO).mpr hzW
  have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hb.isSubmersionAt y)
  have hv : ∀ p, g p ∈ (geoTransformAlong M T).cosupp →
      (canonicalInvariant m).inv N Q p = ambientDimensionMap hnm ((canonicalInvariant n).inv M T (g p)) := by
    intro p hp
    exact HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_value
      h M hM hc p hp
  refine ⟨z,⟨?_,?_⟩,?_⟩
  · rw [hcs]
    exact hzm.1
  · intro p hp
    have hp' : g p ∈ (geoTransformAlong M T).cosupp := by rw [hcs] at hp; exact hp
    rw [hv p hp',hv z hzm.1]
    exact (strictMono_ambientDimensionMap hnm).monotone (hzm.2 (g p) hp')
  · rw [hzy]
    exact hyO


theorem pureHeadStage_pullback
    {E₀ : List (Set X)} {A : Set X} {d : ℕ} {T : BlowupTower X D}
    (hhead : PureCanonicalHeadStage E₀ A d T)
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    {Q : BlowupTower Y E} {g : E → D} (h : IsActualTowerPullback b Q T g) :
    PureCanonicalHeadStage (E₀.map (b ⁻¹' ·)) (b ⁻¹' A) (d+(m-n)) Q ∧
      (geoTransformAlong (partMarkedIdeal (E₀.map (b ⁻¹' ·)) (b ⁻¹' A)) Q).E =
        (geoTransformAlong (partMarkedIdeal E₀ A) T).E.map (g ⁻¹' ·) := by
  let M := partMarkedIdeal E₀ A
  let N := markedPullback (m := m) b M
  let M' := partMarkedIdeal (E₀.map (b ⁻¹' ·)) (b ⁻¹' A)
  have heq : N = M' := partMarkedIdeal_pullback hb E₀ A
  have htT := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hhead.domain T hhead.canonical
  have hrecord := (IsActualTowerPullback.relative_marked_dictionary h M hhead.domain.isWellFormed htT).2
  have hboundary : (geoTransformAlong M' Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) := by
    rw [← heq]
    exact congrArg MarkedIdeal.E hrecord
  let hAaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hhead.analytic
  let hEY := isSNCDivisor_preimage_submersion hb E₀ hhead.snc
  let O := boundaryGoodOpen A hhead.analytic d E₀ hhead.snc
  let U := boundaryGoodOpen (b ⁻¹' A) hAaY (d+(m-n)) (E₀.map (b ⁻¹' ·)) hEY
  let V : Opens Y := ⟨b ⁻¹' (O : Set X),O.isOpen.preimage hb.contMDiff.continuous⟩
  have hU : U = V := boundary_good_open_preimage_eq hb A hhead.analytic d E₀ hhead.snc
  have hM' : IsInvDomain m M' := by
    rw [← heq]
    exact original_ambient_domain_pullback hb M hhead.domain
  have hcQ : IsCanonical M' ((canonicalInvariant m).inv M') Q := by
    rw [← heq]
    exact IsActualTowerPullback.original_ambient_canonical h M hhead.domain hhead.canonical
  refine ⟨⟨hAaY,hEY,?_,pure_regular_density_preimage hb A d hhead.pure,
    boundary_density_preimage hb A E₀ hhead.boundaryDense,hM',hcQ,?_,?_⟩,hboundary⟩
  · rintro ⟨y,hy⟩
    have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hb.isSubmersionAt y)
    have hd := hhead.properDimension ⟨b y,hy⟩
    omega
  · change CentresAvoid U Q
    rw [hU]
    exact IsActualTowerPullback.centresAvoid_preimage hb h O hhead.avoids
  · intro hne
    have hd := hhead.properDimension (by obtain ⟨y,hy⟩ := hne; exact ⟨b y,hy⟩)
    obtain ⟨z,hz,hzO⟩ := source_maximum_over_good_open A hhead.analytic d hd hhead.pure E₀
      hhead.snc hhead.boundaryDense hb h hhead.canonical hhead.avoids hhead.meets hne
    refine ⟨z,?_,?_⟩
    · change z ∈ maxLocus ((canonicalInvariant m).inv M' Q) (geoTransformAlong M' Q).cosupp
      rw [← heq]
      exact hz
    · change Q.proj z ∈ U
      rw [hU]
      exact hzO

private theorem centresOver_mono {A : CMfd.{u} n} {F G : Set A} (hFG : F ⊆ G) :
    ∀ {C : CMfd.{u} n} (T : BlowupTower A C),CentresOver F T → CentresOver G T
  | _,.refl,_ => True.intro
  | _,.step T _ _ _,h => ⟨centresOver_mono hFG T h.1,fun _ hz => hFG (h.2 hz)⟩

private theorem centresOver_pullback {A C B D : CMfd.{u} n} {b : B → A}
    {Q : BlowupTower B D} {T : BlowupTower A C} {g : D → C}
    (h : IsActualTowerPullback b Q T g) (G : Set A) (hT : CentresOver G T) :
    CentresOver (b ⁻¹' G) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    refine ⟨ih hT.1,?_⟩
    intro z hz
    change b (Q.proj z) ∈ G
    rw [← h.proj_comm z]
    exact hT.2 hz

private theorem submersion_of_open {A B : CMfd.{u} n} {ι : B → A}
    (hι : IsOpenHoloEmbedding n ι) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι := by
  obtain ⟨O,Φ,hΦ⟩ := hι
  have hh := isSubmersion_val_comp (B := B) O
    (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism
      (D := B) (C := CMfd.of (n := n) O) Φ)
  have he : ι=(Subtype.val : O → A) ∘ Φ := funext hΦ
  rw [he]
  exact hh

/-- Original locally good data internally construct an actual local pure head,
retaining the SAME genuine whole host for later ordered recursion. -/
theorem exists_local_pure_head_host {X B₀ : CMfd.{u} n}
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (G : Set X) (hG : IsClosed G)
    (A : Set X) (d : ℕ) (hA : IsLocGoodPart n E₀ G A d)
    (ι : B₀ → X) (hι : IsOpenHoloEmbedding n ι)
    (hKι : ∃ K : Set X,IsCompact K ∧ range ι ⊆ K) :
    ∃ (C : CMfd.{u} n) (Q : BlowupTower B₀ C) (H : CMfd.{u} n)
      (EH : List (Set H)) (GH : Set H) (P : Set X → Set H) (j : C → H),
      PureCanonicalHeadStage (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' A) d Q ∧
      CentresOver (ι ⁻¹' G) Q ∧
      IsAdmissibleBlowupSequence n B₀ (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' G) C Q.proj
        (geoTransformAlong (partMarkedIdeal (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' A)) Q).E ∧
      IsSNCDivisor n EH ∧ IsClosed GH ∧ IsOpenHoloEmbedding n j ∧
      (∃ K : Set H,IsCompact K ∧ range j ⊆ K) ∧
      (geoTransformAlong (partMarkedIdeal (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' A)) Q).E=EH.map (j ⁻¹' ·) ∧
      j ⁻¹' GH=Q.proj ⁻¹' (ι ⁻¹' G) ∧
      (∀ S e,IsLocGoodPart n E₀ G S e → IsLocGoodPart n EH GH (P S) e) ∧
      (∀ S R,IsClosed S → IsClosed R → Disjoint S R → Disjoint (P S) (P R)) ∧
      (∀ S R,IsClosed S → IsClosed R → S ∩ R ⊆ G → P S ∩ P R ⊆ GH) ∧
      (∀ S,IsClosed S → S ⊆ closure (S \ G) →
        strictTransform n Q.proj (ι ⁻¹' S)=j ⁻¹' P S) ∧
      (∀ z∈P A,RegularAtDim (n := n) (P A) z d) ∧ HasNormalCrossings n (P A) EH := by
  obtain ⟨U,hιU,hUc,hcι⟩ := exists_opens_of_range_subset (n := n) hKι
  let ι₁ : B₀ → U := fun z => ⟨ι z,hιU (subset_closure ⟨z,rfl⟩)⟩
  have hι₁ : IsOpenHoloEmbedding n ι₁ := hι.codRestrict U _
  have hb := submersion_of_open (A := CMfd.of (n := n) U) hι₁
  let AU := (Subtype.val : U → X) ⁻¹' A
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let GU := (Subtype.val : U → X) ⁻¹' G
  have hval := isOpenHoloEmbedding_val (n := n) U
  have hAU := hA.preimage hval
  obtain ⟨Z,PT,_hcPT,_hrPT,D,T,R,_hTR,hcT,_htT,haT,hmT,_heT,hoverT,hadmT,
      hEH,_hSM,hreg,hNC,_hexc,_hborn,_hsing,_hhol,_hproper,_hsurj,_hiso⟩ :=
    exists_local_original_pure_boundary_canonical_prefix A hA.1 d hA.2.1 hA.pure
      E₀ hE₀ hA.subset_closure_diff_biUnion U hUc subset_closure
  let M := partMarkedIdeal (X := CMfd.of (n := n) U) EU AU
  let EH := (geoTransformAlong M T).E
  let GH := T.proj ⁻¹' GU
  let P : Set X → Set D := fun S => strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' S)
  have hdom : IsInvDomain n M := HironakaEmbeddedBoundary.isInvDomain_boundary hAU.1
    hAU.interior_eq_empty (hval.isSNCDivisor_map_preimage hE₀)
  have hhead : PureCanonicalHeadStage EU AU d T :=
    ⟨hAU.1,hval.isSNCDivisor_map_preimage hE₀,fun _ => hA.2.1,hAU.pure,
      hAU.subset_closure_diff_biUnion,hdom,hcT,haT,hmT⟩
  have hFG : (AU \ regularLocus (n := n) AU d ∪ AU ∩ ⋃ H∈EU,H) ⊆ GU :=
    union_subset hAU.2.2.1 hAU.2.2.2.1
  have hoverTG : CentresOver GU T := centresOver_mono hFG T hoverT
  have hadmTG := hadmT.mono hFG
  obtain ⟨C,Q,j,hactual⟩ := exists_actual_tower hb T
  obtain ⟨hheadQ,hEQ⟩ := pureHeadStage_pullback hhead hb hactual
  have hEinit : EU.map (ι₁ ⁻¹' ·)=E₀.map (ι ⁻¹' ·) := by simp only [EU,List.map_map];rfl
  simp only [Nat.sub_self,Nat.add_zero,hEinit] at hheadQ
  rw [hEinit] at hEQ
  change (geoTransformAlong (partMarkedIdeal (X := B₀) (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' A)) Q).E=
    EH.map (j ⁻¹' ·) at hEQ
  have hoverQ : CentresOver (ι ⁻¹' G) Q := centresOver_pullback hactual GU hoverTG
  have htQ := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hheadQ.domain Q hheadQ.canonical
  have hadmQ := isAdmissibleBlowupSequence_proj (partMarkedIdeal (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' A))
    (ι ⁻¹' G) Q htQ hoverQ
  let O : Opens (CMfd.of (n := n) U) := ⟨GUᶜ,(hG.preimage continuous_subtype_val).isOpen_compl⟩
  have havoid : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hoverTG
  refine ⟨C,Q,D,EH,GH,P,j,hheadQ,hoverQ,hadmQ,hEH,
    (hG.preimage continuous_subtype_val).preimage T.contMDiff_proj.continuous,
    upper_isOpenHoloEmbedding hactual hι₁,upper_range_subset_compact U hιU hcι hactual,hEQ,?_,?_,?_,?_,?_,hreg,hNC⟩
  · ext z
    change ((T.proj (j z) : U) : X) ∈ G ↔ ι (Q.proj z) ∈ G
    rw [hactual.proj_comm z]
  · intro S e hS
    exact (hS.preimage hval).strictTransform hadmTG (hval.isSNCDivisor_map_preimage hE₀).1
  · intro S R hS hR hSR
    exact ((hSR.preimage (Subtype.val : U → X)).preimage T.proj).mono
      (strictTransform_subset_preimage T.contMDiff_proj.continuous (hS.preimage continuous_subtype_val))
      (strictTransform_subset_preimage T.contMDiff_proj.continuous (hR.preimage continuous_subtype_val))
  · intro S R hS hR hSR z hz
    exact hSR ⟨strictTransform_subset_preimage T.contMDiff_proj.continuous
        (hS.preimage continuous_subtype_val) hz.1,
      strictTransform_subset_preimage T.contMDiff_proj.continuous
        (hR.preimage continuous_subtype_val) hz.2⟩
  · intro S _hS hden
    apply IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O havoid
      ((Subtype.val : U → X) ⁻¹' S)
    change (Subtype.val : U → X) ⁻¹' S ⊆ closure
      ((Subtype.val : U → X) ⁻¹' S \ (Subtype.val : U → X) ⁻¹' G)
    simpa only [hval.preimage_closure,preimage_sdiff] using
      (preimage_mono hden : (Subtype.val : U → X) ⁻¹' S ⊆ _)

end
end Hironaka.HironakaOriginalLocalPureHeadHosts
