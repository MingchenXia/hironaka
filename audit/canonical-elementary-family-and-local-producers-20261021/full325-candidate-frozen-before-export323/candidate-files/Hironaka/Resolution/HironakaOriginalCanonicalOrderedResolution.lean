/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalPartListResolution

/-!
# Actual canonical head-and-tail resolution of ordered original parts

Each auxiliary sum separator and pure first-meeting head retains its own
genuine canonical input. Literal append gives the actual final projection,
without relabelling it as a CAN history of another whole mixed ideal.
Blueprint: `hironaka-original-canonical-ordered-resolution-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalCanonicalOrderedResolution

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

/-- The literal intrinsic marking-one input of each resolved head. -/
def partMarkedIdeal {n : ℕ} {X : CMfd.{u} n} (E₀ : List (Set X)) (A : Set X) : MarkedIdeal n X :=
  ⟨univ,E₀,vanishingIdeal (n := n) A,1⟩

/-- A genuine pure first-meeting head stage, retaining its original natural
geometry. The dimension bound is required only for a nonempty head. -/
structure PureCanonicalHeadStage {n : ℕ} {X D : CMfd.{u} n}
    (E₀ : List (Set X)) (A : Set X) (d : ℕ) (T : BlowupTower X D) : Prop where
  analytic : IsComplexAnalyticSubset (n := n) A
  snc : IsSNCDivisor n E₀
  properDimension : A.Nonempty → d < n
  pure : A ⊆ closure (regularLocus (n := n) A d)
  boundaryDense : A ⊆ closure (A \ ⋃ H ∈ E₀, H)
  domain : IsInvDomain n (partMarkedIdeal E₀ A)
  canonical : IsCanonical (partMarkedIdeal E₀ A) ((canonicalInvariant n).inv (partMarkedIdeal E₀ A)) T
  avoids : CentresAvoid (boundaryGoodOpen A analytic d E₀ snc) T
  meets : A.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant n).inv (partMarkedIdeal E₀ A) T)
    (geoTransformAlong (partMarkedIdeal E₀ A) T).cosupp,
    T.proj z ∈ boundaryGoodOpen A analytic d E₀ snc

/-- Literal labelled strict parts, without deletion or reindexing. -/
def strictParts {n : ℕ} {X D : CMfd.{u} n} (T : BlowupTower X D) (L : List (Set X × ℕ)) :
    List (Set D × ℕ) := L.map (fun p => (strictTransform n T.proj p.1,p.2))

/-- The whole finite union used to keep the resolved head away from every later centre. -/
def partsUnion {Z : Type u} (L : List (Set Z × ℕ)) : Set Z := ⋃ H ∈ L.map Prod.fst, H

/-- Actual separator, first-meeting head, and cut-down tail provenance for
the SAME literal appended finite blowup tower. -/
inductive CanonicalOrderedResolution {n : ℕ} :
    {X : CMfd.{u} n} → (E₀ : List (Set X)) → (G : Set X) →
    (L : List (Set X × ℕ)) → {D : CMfd.{u} n} → BlowupTower X D → List (Set D) → Prop
  | nil {X : CMfd.{u} n} {E₀ : List (Set X)} {G : Set X} :
      CanonicalOrderedResolution E₀ G [] .refl E₀
  | cons {X D₀ D₁ D : CMfd.{u} n} {E₀ : List (Set X)} {G A : Set X} {d : ℕ}
      {L : List (Set X × ℕ)} {E₁ : List (Set D₀)} {E₂ : List (Set D)}
      (T₀ : BlowupTower X D₀) (T₁ : BlowupTower D₀ D₁) (T : BlowupTower D₁ D)
      (hsep : CanonicalSeparationChain E₀ A L T₀ E₁)
      (hhead : PureCanonicalHeadStage E₁ (strictTransform n T₀.proj A) d T₁)
      (htail : CanonicalOrderedResolution
        (geoTransformAlong (partMarkedIdeal E₁ (strictTransform n T₀.proj A)) T₁).E
        (T₁.proj ⁻¹' (T₀.proj ⁻¹' G) ∩ partsUnion (strictParts T₁ (strictParts T₀ L)))
        (strictParts T₁ (strictParts T₀ L)) T E₂) :
      CanonicalOrderedResolution E₀ G ((A,d)::L) (T₀.append (T₁.append T)) E₂

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


private theorem pureHeadStage_pullback
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

private theorem centresOver_actual_pullback
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g) (G : Set X) (hT : CentresOver G T) :
    CentresOver (b ⁻¹' G) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    refine ⟨ih hT.1,?_⟩
    intro z hz
    change b (Q.proj z) ∈ G
    rw [← h.proj_comm z]
    exact hT.2 hz

private theorem preimage_bad_eq
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g) (G : Set X) :
    g ⁻¹' (T.proj ⁻¹' G) = Q.proj ⁻¹' (b ⁻¹' G) := by
  ext z
  change T.proj (g z) ∈ G ↔ b (Q.proj z) ∈ G
  rw [h.proj_comm]

private theorem centresOver_mono {X : CMfd.{u} n} {G H : Set X} (hGH : G ⊆ H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D), CentresOver G T → CentresOver H T
  | _, .refl, _ => True.intro
  | _, .step T _C _π _hπ, h => ⟨centresOver_mono hGH T h.1,fun _z hz => hGH (h.2 hz)⟩

/-- Original compact good parts internally construct each actual canonical
auxiliary stage, the same full appended projection, and its genuine smooth source. -/
theorem exists_canonical_ordered_resolution (ℓ : ℕ) :
    ∀ {X : CMfd.{u} n} (E₀ : List (Set X)) (_hE₀ : IsSNCDivisor n E₀)
      (G : Set X) (_hG : IsClosed G) (L : List (Set X × ℕ)), L.length = ℓ →
      (∀ p ∈ L, IsGoodPart n E₀ G p.1 p.2) → L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) →
      ∃ (D : CMfd.{u} n) (T : BlowupTower X D) (E₁ : List (Set D)),
        CanonicalOrderedResolution E₀ G L T E₁ ∧ CentresOver G T ∧
        IsAdmissibleBlowupSequence n X E₀ G D T.proj E₁ ∧ IsSNCDivisor n E₁ ∧
        (∀ p ∈ L, (∀ z ∈ strictTransform n T.proj p.1,
          RegularAtDim (n := n) (strictTransform n T.proj p.1) z p.2) ∧
          HasNormalCrossings n (strictTransform n T.proj p.1) E₁) ∧
        L.Pairwise (fun p q => Disjoint (strictTransform n T.proj p.1) (strictTransform n T.proj q.1)) ∧
        ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X),
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
          ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
            IsActualTowerPullback b Q T g ∧
            CanonicalOrderedResolution (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
              (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) Q (E₁.map (g ⁻¹' ·)) ∧
            IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
              C Q.proj (E₁.map (g ⁻¹' ·)) ∧ IsSNCDivisor m (E₁.map (g ⁻¹' ·)) ∧
            (∀ p ∈ L, strictTransform m Q.proj (b ⁻¹' p.1) = g ⁻¹' strictTransform n T.proj p.1) ∧
            (∀ p ∈ L, (∀ z ∈ strictTransform m Q.proj (b ⁻¹' p.1),
              RegularAtDim (n := m) (strictTransform m Q.proj (b ⁻¹' p.1)) z (p.2+(m-n))) ∧
              HasNormalCrossings m (strictTransform m Q.proj (b ⁻¹' p.1)) (E₁.map (g ⁻¹' ·))) ∧
            L.Pairwise (fun p q => Disjoint (strictTransform m Q.proj (b ⁻¹' p.1))
              (strictTransform m Q.proj (b ⁻¹' q.1))) ∧
            Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
            Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
            HolomorphicSquarePullback b g Q.proj T.proj := by
  induction ℓ with
  | zero =>
      intro X E₀ hE₀ G _hG L hL _hgood _hpair
      rw [List.length_eq_zero_iff.mp hL]
      refine ⟨X,.refl,E₀,.nil,True.intro,IsAdmissibleBlowupSequence.refl,hE₀,
        fun p hp => absurd hp List.not_mem_nil,List.Pairwise.nil,?_⟩
      intro m Y b hb
      have hactual := IsActualTowerPullback.refl hb
      exact ⟨Y,.refl,b,hactual,.nil,IsAdmissibleBlowupSequence.refl,
        isSNCDivisor_preimage_submersion hb E₀ hE₀,fun p hp => absurd hp List.not_mem_nil,
        fun p hp => absurd hp List.not_mem_nil,List.Pairwise.nil,hb,rfl,fun _ => rfl,hactual.universal⟩
  | succ ℓ ih =>
      intro X E₀ hE₀ G hG L hL hgood hpair
      obtain ⟨⟨A,d⟩,L',rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length = ℓ := by simpa using hL
      rw [List.pairwise_cons] at hpair
      obtain ⟨hAsep,hpair'⟩ := hpair
      have hA := hgood (A,d) (List.mem_cons_self ..)
      have hgood' : ∀ p ∈ L', IsGoodPart n E₀ G p.1 p.2 := fun p hp => hgood p (List.mem_cons_of_mem _ hp)
      obtain ⟨D₀,T₀,E₁,hsep,hover₀,hadm₀,hE₁,hdisj₀,hSource₀⟩ :=
        exists_canonical_ordered_separator ℓ E₀ hE₀ G hG A d hA L' hL' hgood' hAsep
      let A₁ := strictTransform n T₀.proj A
      let L₁ := strictParts T₀ L'
      let G₁ := T₀.proj ⁻¹' G
      have hG₁ : IsClosed G₁ := hG.preimage T₀.contMDiff_proj.continuous
      have hA₁ : IsGoodPart n E₁ G₁ A₁ d := hA.strictTransform hadm₀ hE₀.1
      have hgood₁ : ∀ p ∈ L₁, IsGoodPart n E₁ G₁ p.1 p.2 := by
        intro p hp
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
        exact (hgood' p₀ hp₀).strictTransform hadm₀ hE₀.1
      have hpair₁ : L₁.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G₁) := by
        simp only [L₁,strictParts,List.pairwise_map]
        refine hpair'.imp_of_mem fun {p q} hp hq hpq z hz => hpq ?_
        exact ⟨HironakaAdmissibleCalculus.strictTransform_subset_preimage T₀.contMDiff_proj.continuous
          (hgood' p hp).isClosed hz.1,
          HironakaAdmissibleCalculus.strictTransform_subset_preimage T₀.contMDiff_proj.continuous
            (hgood' q hq).isClosed hz.2⟩
      obtain ⟨D₁,T₁,_R,hHeadGeometry⟩ := exists_original_pure_boundary_canonical_prefix A₁ hA₁.1
        hA₁.2.1 d hA₁.2.2.1 hA₁.pure E₁ hE₁ hA₁.subset_closure_diff_biUnion
      rcases hHeadGeometry with ⟨_hFactor,hcHead,_htHead,haHead,hmHead,_heHead,hoverHead,
        hadmHead,hE₂,_hSMHead,hrHead,hNCHead,_hExcHead,_hNewHead,_hSingHead,
        _hholHead,_hproperHead,_hsurjHead,_hisoHead⟩
      let MHead := partMarkedIdeal E₁ A₁
      let E₂ := (geoTransformAlong MHead T₁).E
      have hMHead : IsInvDomain n MHead := HironakaEmbeddedBoundary.isInvDomain_boundary hA₁.1
        hA₁.interior_eq_empty hE₁
      have hHead : PureCanonicalHeadStage E₁ A₁ d T₁ :=
        ⟨hA₁.1,hE₁,fun _ => hA₁.2.2.1,hA₁.pure,hA₁.subset_closure_diff_biUnion,
          hMHead,hcHead,haHead,hmHead⟩
      have hFHead : A₁ \ regularLocus (n := n) A₁ d ∪ A₁ ∩ ⋃ H ∈ E₁, H ⊆ G₁ :=
        union_subset hA₁.2.2.2.1 hA₁.2.2.2.2.1
      have hadmHeadG : IsAdmissibleBlowupSequence n D₀ E₁ G₁ D₁ T₁.proj E₂ := hadmHead.mono hFHead
      have hoverHeadG : CentresOver G₁ T₁ := centresOver_mono hFHead T₁ hoverHead
      let L₂ := strictParts T₁ L₁
      let K₂ := partsUnion L₂
      let G₂ := T₁.proj ⁻¹' G₁ ∩ K₂
      have hK₂ : IsClosed K₂ := by
        apply HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed
        intro H hH
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hH
        obtain ⟨p₁,_hp₁,rfl⟩ := List.mem_map.mp hp
        exact isClosed_closure
      have hmemK₂ : ∀ p ∈ L₂, p.1 ⊆ K₂ := fun p hp z hz =>
        mem_iUnion₂.mpr ⟨p.1,List.mem_map_of_mem hp,hz⟩
      have hG₂ : IsClosed G₂ := (hG₁.preimage T₁.contMDiff_proj.continuous).inter hK₂
      have hgood₂ : ∀ p ∈ L₂, IsGoodPart n E₂ G₂ p.1 p.2 := by
        intro p hp
        obtain ⟨p₁,hp₁,rfl⟩ := List.mem_map.mp hp
        exact ((hgood₁ p₁ hp₁).strictTransform hadmHeadG hE₁.1).inter (hmemK₂ _ hp)
      have hpair₂ : L₂.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G₂) := by
        simp only [L₂,strictParts,List.pairwise_map]
        refine hpair₁.imp_of_mem fun {p q} hp hq hpq z hz =>
          ⟨hpq ⟨HironakaAdmissibleCalculus.strictTransform_subset_preimage T₁.contMDiff_proj.continuous
            (hgood₁ p hp).isClosed hz.1,
            HironakaAdmissibleCalculus.strictTransform_subset_preimage T₁.contMDiff_proj.continuous
              (hgood₁ q hq).isClosed hz.2⟩,hmemK₂ _ (List.mem_map_of_mem hp) hz.1⟩
      obtain ⟨D,T,E₃,hTree,hoverTail,hadmTail,hE₃,hResTail,hDisjTail,hSource⟩ :=
        ih E₂ hE₂ G₂ hG₂ L₂ (by simp only [L₂,L₁,strictParts,List.length_map]; exact hL') hgood₂ hpair₂
      let TT := T₀.append (T₁.append T)
      have hTreeT : CanonicalOrderedResolution E₀ G ((A,d)::L') TT E₃ := .cons T₀ T₁ T hsep hHead hTree
      have hoverTailG : CentresOver (T₁.proj ⁻¹' G₁) T := centresOver_mono inter_subset_left T hoverTail
      have hoverT : CentresOver G TT :=
        (centresOver_append_iff G T₀ (T₁.append T)).mpr
          ⟨hover₀,(centresOver_append_iff G₁ T₁ T).mpr ⟨hoverHeadG,hoverTailG⟩⟩
      have hadmTailG := hadmTail.mono (inter_subset_left : G₂ ⊆ T₁.proj ⁻¹' G₁)
      have hadmT : IsAdmissibleBlowupSequence n X E₀ G D TT.proj E₃ := by
        simpa only [TT,BlowupTower.proj_append] using
          IsAdmissibleBlowupSequence.comp hadm₀ (IsAdmissibleBlowupSequence.comp hadmHeadG hadmTailG)
      let A₂ := strictTransform n T₁.proj A₁
      have hA₂K₂ : Disjoint A₂ K₂ := by
        rw [disjoint_left]
        intro z hzA hzK
        obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hzK
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hH
        obtain ⟨p₁,hp₁,rfl⟩ := List.mem_map.mp hp
        obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp₁
        exact disjoint_left.mp (hdisj₀ p₀ hp₀)
          (HironakaAdmissibleCalculus.strictTransform_subset_preimage T₁.contMDiff_proj.continuous hA₁.isClosed hzA)
          (HironakaAdmissibleCalculus.strictTransform_subset_preimage T₁.contMDiff_proj.continuous
            (hgood₁ _ hp₁).isClosed hzH)
      have hA₂G₂ : Disjoint A₂ G₂ := hA₂K₂.mono_right inter_subset_right
      have hST (P : Set X) : strictTransform n TT.proj P =
          strictTransform n T.proj (strictTransform n T₁.proj (strictTransform n T₀.proj P)) := by
        rw [show TT.proj = T₀.proj ∘ (T₁.proj ∘ T.proj) by simp only [TT,BlowupTower.proj_append],
          StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj
            (T₁.contMDiff_proj.comp T.contMDiff_proj),
          StrictTransformComposition.strictTransform_comp T₁.contMDiff_proj T.contMDiff_proj]
      have hResT : ∀ p ∈ (A,d)::L',
          (∀ z ∈ strictTransform n TT.proj p.1, RegularAtDim (n := n) (strictTransform n TT.proj p.1) z p.2) ∧
          HasNormalCrossings n (strictTransform n TT.proj p.1) E₃ := by
        intro p hp
        rw [hST]
        rcases List.mem_cons.mp hp with rfl | hp'
        · have hexc := IsAdmissibleBlowupSequence.exceptionalLocus_subset hadmTail
          have hpre : strictTransform n T.proj A₂ = T.proj ⁻¹' A₂ :=
            strictTransform_eq_preimage_of_disjoint T.contMDiff_proj.continuous hexc isClosed_closure hA₂G₂
          change (∀ z ∈ strictTransform n T.proj A₂, RegularAtDim (n := n) (strictTransform n T.proj A₂) z d) ∧ _
          rw [hpre]
          exact ⟨fun z hz => regularAtDim_preimage_of_disjoint T.contMDiff_proj hexc hA₂G₂ (hrHead (T.proj z) hz),
            IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint hadmTail hE₂.1 hG₂ hA₂G₂ hNCHead⟩
        · exact hResTail _ (List.mem_map_of_mem (List.mem_map_of_mem hp'))
      have hDisjT : ((A,d)::L').Pairwise (fun p q =>
          Disjoint (strictTransform n TT.proj p.1) (strictTransform n TT.proj q.1)) := by
        rw [List.pairwise_cons]
        refine ⟨?_,?_⟩
        · intro p hp
          rw [show TT.proj = T₀.proj ∘ (T₁.proj ∘ T.proj) by simp only [TT,BlowupTower.proj_append],
            StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj (T₁.contMDiff_proj.comp T.contMDiff_proj),
            StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj (T₁.contMDiff_proj.comp T.contMDiff_proj)]
          exact ((hdisj₀ p hp).preimage (T₁.proj ∘ T.proj)).mono
            (HironakaAdmissibleCalculus.strictTransform_subset_preimage
              (T₁.contMDiff_proj.comp T.contMDiff_proj).continuous isClosed_closure)
            (HironakaAdmissibleCalculus.strictTransform_subset_preimage
              (T₁.contMDiff_proj.comp T.contMDiff_proj).continuous isClosed_closure)
        · have hh := hDisjTail
          simp only [L₂,L₁,strictParts,List.pairwise_map] at hh
          refine hh.imp fun {p q} hpq => ?_
          rw [hST,hST]
          exact hpq
      refine ⟨D,TT,E₃,hTreeT,hoverT,hadmT,hE₃,hResT,hDisjT,?_⟩
      intro m Y b hb
      obtain ⟨C₀,Q₀,g₀,hactual₀,hSepQ,hadmQ₀,_hEQ₀,hStrictSepA,hStrictSepL,_hDisjSep,
        _hg₀,_hlen₀,_hcomm₀,_hcart₀⟩ := hSource₀ Y b hb
      obtain ⟨C₁,Q₁,g₁,hactual₁⟩ := exists_actual_tower hactual₀.isSubmersion T₁
      obtain ⟨hHeadQ,hEHeadQ⟩ := pureHeadStage_pullback hHead hactual₀.isSubmersion hactual₁
      obtain ⟨C,Q,g,hactual,hTreeQ,hadmQ,_hEQ,_hStrictTail,_hResTailQ,_hDisjTailQ,
        _hg,_hlen,_hcomm,_hcart⟩ := hSource C₁ g₁ hactual₁.isSubmersion
      let QQ := Q₀.append (Q₁.append Q)
      have hfull : IsActualTowerPullback b QQ TT g := hactual₀.append (hactual₁.append hactual)
      let O₁ : Opens D₀ := ⟨G₁ᶜ,hG₁.isOpen_compl⟩
      have hav₁ : CentresAvoid O₁ T₁ := centresAvoid_of_centresOver O₁ disjoint_compl_left T₁ hoverHeadG
      have hStrictHead (P : Set D₀) (hdense : P ⊆ closure (P \ G₁)) :
          strictTransform m Q₁.proj (g₀ ⁻¹' P) = g₁ ⁻¹' strictTransform n T₁.proj P :=
        IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hactual₀.isSubmersion hactual₁
          O₁ hav₁ P (by change P ⊆ closure (P \ G₁); exact hdense)
      have hLists : strictParts Q₁ (strictParts Q₀ (L'.map (fun p => (b ⁻¹' p.1,p.2+(m-n))))) =
          L₂.map (fun p => (g₁ ⁻¹' p.1,p.2+(m-n))) := by
        simp only [strictParts,L₂,L₁,List.map_map]
        apply List.map_congr_left
        intro p hp
        apply Prod.ext
        · change strictTransform m Q₁.proj (strictTransform m Q₀.proj (b ⁻¹' p.1)) =
            g₁ ⁻¹' strictTransform n T₁.proj (strictTransform n T₀.proj p.1)
          rw [hStrictSepL p hp]
          exact hStrictHead _ (hgood₁ _ (List.mem_map_of_mem hp)).2.2.2.2.2
        · rfl
      have hKdict : partsUnion (strictParts Q₁ (strictParts Q₀
          (L'.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))))) = g₁ ⁻¹' K₂ := by
        rw [hLists]
        unfold K₂ partsUnion
        rw [HironakaEmbeddedBoundary.preimage_biUnion_list]
        simp only [List.map_map]
        rfl
      have hBadBase : g₁ ⁻¹' (T₁.proj ⁻¹' G₁) = Q₁.proj ⁻¹' (Q₀.proj ⁻¹' (b ⁻¹' G)) := by
        rw [preimage_bad_eq hactual₁ G₁,preimage_bad_eq hactual₀ G]
      have hBad : Q₁.proj ⁻¹' (Q₀.proj ⁻¹' (b ⁻¹' G)) ∩
          partsUnion (strictParts Q₁ (strictParts Q₀ (L'.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))))) =
          g₁ ⁻¹' G₂ := by
        rw [show g₁ ⁻¹' G₂ = g₁ ⁻¹' (T₁.proj ⁻¹' G₁) ∩ g₁ ⁻¹' K₂ by rfl,hBadBase,hKdict]
      rw [← hStrictSepA] at hHeadQ hEHeadQ
      have hTailTree : CanonicalOrderedResolution
          (geoTransformAlong (partMarkedIdeal (E₁.map (g₀ ⁻¹' ·))
            (strictTransform m Q₀.proj (b ⁻¹' A))) Q₁).E
          (Q₁.proj ⁻¹' (Q₀.proj ⁻¹' (b ⁻¹' G)) ∩
            partsUnion (strictParts Q₁ (strictParts Q₀ (L'.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))))))
          (strictParts Q₁ (strictParts Q₀ (L'.map (fun p => (b ⁻¹' p.1,p.2+(m-n))))))
          Q (E₃.map (g ⁻¹' ·)) := by
        rw [hEHeadQ,hBad,hLists]
        exact hTreeQ
      have hTreeFull : CanonicalOrderedResolution (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
          (((A,d)::L').map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) QQ (E₃.map (g ⁻¹' ·)) :=
        .cons Q₀ Q₁ Q hSepQ hHeadQ hTailTree
      have htHeadQ := (canonicalInvariant m).isInvValue.isGeoTestTower_of_isCanonical
        hHeadQ.domain Q₁ hHeadQ.canonical
      have hoverHeadQ := centresOver_actual_pullback hactual₁ G₁ hoverHeadG
      have hadmHeadQ : IsAdmissibleBlowupSequence m C₀ (E₁.map (g₀ ⁻¹' ·))
          (Q₀.proj ⁻¹' (b ⁻¹' G)) C₁ Q₁.proj (E₂.map (g₁ ⁻¹' ·)) := by
        rw [← preimage_bad_eq hactual₀ G,← hEHeadQ]
        exact isAdmissibleBlowupSequence_proj
          (partMarkedIdeal (E₁.map (g₀ ⁻¹' ·)) (strictTransform m Q₀.proj (b ⁻¹' A)))
          (g₀ ⁻¹' G₁) Q₁ htHeadQ hoverHeadQ
      have hGtail : g₁ ⁻¹' G₂ ⊆ Q₁.proj ⁻¹' (Q₀.proj ⁻¹' (b ⁻¹' G)) := by
        rw [← hBad]
        exact inter_subset_left
      have hadmTailQ := hadmQ.mono hGtail
      have hadmFull : IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
          C QQ.proj (E₃.map (g ⁻¹' ·)) := by
        simpa only [QQ,BlowupTower.proj_append] using
          IsAdmissibleBlowupSequence.comp hadmQ₀ (IsAdmissibleBlowupSequence.comp hadmHeadQ hadmTailQ)
      let O : Opens X := ⟨Gᶜ,hG.isOpen_compl⟩
      have hav : CentresAvoid O TT := centresAvoid_of_centresOver O disjoint_compl_left TT hoverT
      have hStrictFull : ∀ p ∈ (A,d)::L', strictTransform m QQ.proj (b ⁻¹' p.1) =
          g ⁻¹' strictTransform n TT.proj p.1 := by
        intro p hp
        exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hfull O hav p.1
          (by change p.1 ⊆ closure (p.1 \ G); exact (hgood p hp).2.2.2.2.2)
      refine ⟨C,QQ,g,hfull,hTreeFull,hadmFull,isSNCDivisor_preimage_submersion hfull.isSubmersion E₃ hE₃,
        hStrictFull,?_,?_,hfull.isSubmersion,hfull.length_eq,hfull.proj_comm,hfull.universal⟩
      · intro p hp
        rw [hStrictFull p hp]
        exact ⟨fun z hz => regularAtDim_preimage_submersion (hfull.isSubmersion.isSubmersionAt z)
            ((hResT p hp).1 (g z) hz),hasNormalCrossings_preimage_submersion hfull.isSubmersion (hResT p hp).2⟩
      · refine hDisjT.imp_of_mem fun {p q} hp hq hpq => ?_
        rw [hStrictFull p hp,hStrictFull q hq]
        exact hpq.preimage g

end

end Hironaka.HironakaOriginalCanonicalOrderedResolution
