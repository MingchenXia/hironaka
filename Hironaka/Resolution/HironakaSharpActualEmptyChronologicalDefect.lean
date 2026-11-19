import Hironaka.Resolution.HironakaSharpActualFamilyDefectOpenNaturality
import Hironaka.Resolution.HironakaOriginalOldBranchEmptyProjection

/-! Whole indexed chronological ideals and actual distinct defects along genuine
empty towers.  Every original position and every empty tower constructor remains.
Complete mathematics precedes this source in
`hironaka-sharp-original-dynamic-good-prefixes-extension.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualEmptyChronologicalDefect
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFamilyDefectOpenNaturality HironakaSharpActualChronologicalOpenNaturality
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalFirstMemberRelativeStrict HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaOriginalOldBranchEmptyProjection HironakaNormalCrossingsOpenRestrictionSeparation
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  GermIdealPullbackCalculus GermIdealTotalTransform MarkedIdealBiholomorphism
  MarkedIdealTowerTransport NormalCrossings IdealWeightPowers InvertibleIdealQuotient
  NonmonomialOrderLocal GermIdealOrder DivisorExponentAlong
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
variable {n m : ℕ} {X Y : CMfd.{u} n}

private theorem coherent_mem_comp_biholo_iff
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (I : GermIdeal n X) (hI : I.IsCoherent) (y : Y) (g : X → ℂ) :
    (GermIdeal.pullback (m := n) e I).mem y (g ∘ e) ↔ I.mem (e y) g := by
  constructor
  · intro hg
    have hs : IsInSpanAt (n := n) (fun s => ∃ a,I.mem (e y) a ∧ s=a ∘ e)
        (e.symm (e y)) (g ∘ e) := by
      simpa only [e.symm_apply_apply] using GermIdeal.mem_pullback_iff.mp hg
    have hp := isInSpanAt_comp e.symm.contMDiff hs
    have hm : IsInSpanAt (n := n) (I.mem (e y)) (e y) ((g ∘ e) ∘ e.symm) := by
      apply IsInSpanAt.mono ?_ hp
      rintro s ⟨a,⟨b,hb,rfl⟩,rfl⟩
      have he : (b ∘ e) ∘ e.symm=b := funext fun x => by simp
      rwa [he]
    have he : (g ∘ e) ∘ e.symm=g := funext fun x => by simp
    rw [he] at hm
    exact HomogenizedIdeal.mem_of_isInSpanAt hI hm
  · intro hg
    exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨g,hg,rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem hI hg).comp_contMDiff
          (Eventually.of_forall fun z => e.contMDiff.contMDiffAt)))

/-- The actual whole membership dictionary uses the genuine inverse function. -/
theorem coherent_mem_pullback_biholo_iff
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (I : GermIdeal n X) (hI : I.IsCoherent) (y : Y) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) e I).mem y g ↔ I.mem (e y) (g ∘ e.symm) := by
  have he : (g ∘ e.symm) ∘ e=g := funext fun z => by simp
  simpa only [he] using coherent_mem_comp_biholo_iff e I hI y (g ∘ e.symm)

/-- Both directions preserve every actual ideal germ, including colliding positions. -/
theorem actual_ideal_germ_relation_biholo
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent) (y : Y) (i j : Fin m) :
    (actualIdealGermSetoid (fun a => GermIdeal.pullback (m := n) e (F a)) y).r i j ↔
      (actualIdealGermSetoid F (e y)).r i j := by
  constructor
  · intro h g
    exact (coherent_mem_comp_biholo_iff e (F i) (hc i) y g).symm.trans
      ((h (g ∘ e)).trans (coherent_mem_comp_biholo_iff e (F j) (hc j) y g))
  · intro h g
    rw [coherent_mem_pullback_biholo_iff e (F i) (hc i),
      coherent_mem_pullback_biholo_iff e (F j) (hc j)]
    exact h (g ∘ e.symm)

/-- The literal proper quotient image, with all original positions, has the same cardinality. -/
theorem actual_distinct_proper_count_biholo
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent) (y : Y) :
    actualDistinctProperCount (fun a => GermIdeal.pullback (m := n) e (F a)) y=
      actualDistinctProperCount F (e y) := by
  let FY := fun a => GermIdeal.pullback (m := n) e (F a)
  have hRel : ∀ i j,(actualIdealGermSetoid F (e y)).r i j ↔
      (actualIdealGermSetoid FY y).r i j :=
    fun i j => (actual_ideal_germ_relation_biholo e F hc y i j).symm
  let eQ := Quotient.congr (Equiv.refl (Fin m)) hRel
  have hProper : actualProperPositions FY y=actualProperPositions F (e y) := by
    ext i
    simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and]
    exact not_congr (coherent_mem_comp_biholo_iff e (F i) (hc i) y (1 : X → ℂ))
  have hmk : Quotient.mk (actualIdealGermSetoid FY y)=
      eQ ∘ Quotient.mk (actualIdealGermSetoid F (e y)) := by
    funext i
    exact (Quotient.congr_mk (Equiv.refl (Fin m)) hRel i).symm
  change ((actualProperPositions FY y).image (Quotient.mk (actualIdealGermSetoid FY y))).card=_
  rw [hProper,hmk,← Finset.image_image,Finset.card_image_of_injective _ eQ.injective]
  rfl

private theorem holomorphic_inverse_comp_iff
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (y : Y) (g : Y → ℂ) : HolomorphicAt n (g ∘ e.symm) (e y) ↔ HolomorphicAt n g y := by
  constructor
  · intro hg
    have h := hg.comp_contMDiff (Eventually.of_forall fun z => e.contMDiff.contMDiffAt)
    have he : (g ∘ e.symm) ∘ e=g := funext fun z => by simp
    rwa [he] at h
  · intro hg
    have h : HolomorphicAt n g (e.symm (e y)) := by simpa only [e.symm_apply_apply] using hg
    exact h.comp_contMDiff (Eventually.of_forall fun z => e.symm.contMDiff.contMDiffAt)

private theorem restricted_span_biholo_iff
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (N : Set X) (I : GermIdeal n X) (hI : I.IsCoherent) (y : Y) (g : Y → ℂ) :
    IsInSpanOnAt (n := n) N (I.mem (e y)) (e y) (g ∘ e.symm) ↔
      IsInSpanOnAt (n := n) (e ⁻¹' N) ((GermIdeal.pullback (m := n) e I).mem y) y g := by
  constructor
  · rintro ⟨k,s,a,hs,ha,heq⟩
    refine ⟨k,fun i => s i ∘ e,fun i => a i ∘ e,?_,?_,?_⟩
    · intro i
      exact (coherent_mem_comp_biholo_iff e I hI y (s i)).mpr (hs i)
    · intro i
      exact (ha i).comp_contMDiff (Eventually.of_forall fun z => e.contMDiff.contMDiffAt)
    · filter_upwards [(e.continuous.tendsto y).eventually heq] with z hz hzN
      simpa only [Function.comp_apply,e.symm_apply_apply] using hz hzN
  · rintro ⟨k,s,a,hs,ha,heq⟩
    refine ⟨k,fun i => s i ∘ e.symm,fun i => a i ∘ e.symm,?_,?_,?_⟩
    · intro i
      exact (coherent_mem_pullback_biholo_iff e I hI y (s i)).mp (hs i)
    · intro i
      have h : HolomorphicAt n (a i) (e.symm (e y)) := by
        simpa only [e.symm_apply_apply] using ha i
      exact h.comp_contMDiff (Eventually.of_forall fun z => e.symm.contMDiff.contMDiffAt)
    · have hq : ∀ᶠ z in 𝓝 (e.symm (e y)),z ∈ e ⁻¹' N → g z=∑ i : Fin k,a i z*s i z := by
        simpa only [e.symm_apply_apply] using heq
      filter_upwards [(e.symm.continuous.tendsto (e y)).eventually hq] with z hz hzN
      exact hz (by simpa only [Set.mem_preimage,e.apply_symm_apply] using hzN)

/-- Whole carrier restriction commutes with the genuine biholomorphic pullback. -/
theorem restrictOn_pullback_biholo
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent) :
    GermIdeal.pullback (m := n) e (restrictOn n N I)=
      restrictOn n (e ⁻¹' N) (GermIdeal.pullback (m := n) e I) := by
  have hr := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  ext y g
  rw [coherent_mem_pullback_biholo_iff e (restrictOn n N I) hr]
  exact and_congr (holomorphic_inverse_comp_iff e y g) (restricted_span_biholo_iff e N I hI y g)

private theorem relative_product_coherent {N : Set X} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X)) (hc : ∀ I∈L,I.IsCoherent) :
    (relativeIdealListProduct N L).IsCoherent := by
  induction L with
  | nil => exact isCoherent_unitIdeal
  | cons I L ih =>
    exact isCoherent_restrictOn (isCoherent_mul (hc I (by simp))
      (ih (fun J hJ => hc J (List.mem_cons_of_mem I hJ))))
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)

/-- Every stage of the actual relative-product recursion is retained. -/
theorem relativeIdealListProduct_pullback_biholo
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X)) (hc : ∀ I∈L,I.IsCoherent) :
    GermIdeal.pullback (m := n) e (relativeIdealListProduct N L)=
      relativeIdealListProduct (e ⁻¹' N) (L.map fun I => GermIdeal.pullback (m := n) e I) := by
  induction L with
  | nil => exact BlowupExceptionalDivisor.pullback_unitIdeal
  | cons I L ih =>
    have hI := hc I (by simp)
    have hL := fun J hJ => hc J (List.mem_cons_of_mem I hJ)
    change GermIdeal.pullback (m := n) e (restrictOn n N (I.mul (relativeIdealListProduct N L)))=
      restrictOn n (e ⁻¹' N) ((GermIdeal.pullback (m := n) e I).mul
        (relativeIdealListProduct (e ⁻¹' N) (L.map fun J => GermIdeal.pullback (m := n) e J)))
    rw [restrictOn_pullback_biholo e hN (isCoherent_mul hI (relative_product_coherent hN L hL)),
      GermIdealTotalTransform.pullback_mul e.contMDiff hI (relative_product_coherent hN L hL),ih hL]

/-- Actual full product orders are preserved before applying the defect definition. -/
theorem actual_family_product_order_biholo (hn : 0<n)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ x∈N,IsNonzeroAlongAt N (F i) x)
    (hpr : ∀ i,∀ x∈N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,(F i).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (y : Y) :
    ordinaryTraceOrder (e ⁻¹' N)
      (relativeIdealListProduct (e ⁻¹' N) (List.ofFn fun i => GermIdeal.pullback (m := n) e (F i))) y=
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) (e y) := by
  have hList : ∀ I∈List.ofFn F,I.IsCoherent ∧ (∀ x∈N,IsNonzeroAlongAt N I x) ∧
      ∀ x∈N,∃ f : X → ℂ,HolomorphicAt n f x ∧
        ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact ⟨hc i,hnz i,hpr i⟩
  obtain ⟨hP,hNz,_⟩ := relativeIdealListProduct_actual_geometry hN (List.ofFn F)
    (fun I hI => (hList I hI).1) (fun I hI => (hList I hI).2.1) (fun I hI => (hList I hI).2.2)
  have hOrd := nmOrd_pullback_diffeo hn e (ordinaryTraceMarked_isWellFormed hN hP) hNz y
  have hProd := relativeIdealListProduct_pullback_biholo e hN (List.ofFn F)
    (fun I hI => (hList I hI).1)
  rw [List.map_ofFn] at hProd
  have hRecord : MarkedIdeal.pullback e (ordinaryTraceMarked N (relativeIdealListProduct N (List.ofFn F)))=
      ordinaryTraceMarked (e ⁻¹' N)
        (relativeIdealListProduct (e ⁻¹' N) (List.ofFn fun i => GermIdeal.pullback (m := n) e (F i))) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hProd rfl
  rw [hRecord] at hOrd
  exact hOrd

/-- The exact whole defect follows from the genuine count and product identities. -/
theorem actual_family_distinct_defect_biholo (hn : 0<n)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ x∈N,IsNonzeroAlongAt N (F i) x)
    (hpr : ∀ i,∀ x∈N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,(F i).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) :
    actualFamilyDistinctDefect (e ⁻¹' N) (fun i => GermIdeal.pullback (m := n) e (F i))=
      e ⁻¹' actualFamilyDistinctDefect N F := by
  ext y
  change (e y∈N ∧ _ < _) ↔ (e y∈N ∧ _ < _)
  rw [actual_distinct_proper_count_biholo e F hc,
    actual_family_product_order_biholo hn e hN F hc hnz hpr]

private theorem vanishingIdeal_empty_unit :
    vanishingIdeal (n := n) (∅ : Set X)=unitIdeal n X := by
  ext x g
  exact ⟨fun hg => hg.1,fun hg => ⟨hg,Eventually.of_forall fun _ hx => hx.elim⟩⟩

private theorem restrictOn_idempotent (N : Set X) (I : GermIdeal n X) :
    restrictOn n N (restrictOn n N I)=restrictOn n N I := by
  ext x g
  constructor
  · rintro ⟨hg,hspan⟩
    exact ⟨hg,IsInSpanOnAt.trans (fun s hs => hs.2) hspan⟩
  · intro hg
    exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩

/-- This identifies every actual finite-power term in the independently defined saturation. -/
theorem relativeExceptionalSaturation_empty {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) :
    relativeExceptionalSaturation N I ∅=restrictOn n N I := by
  have hr := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  ext x g
  change (∃ k,(colon (restrictOn n N I) (idealPow (vanishingIdeal (n := n) (∅ : Set X)) k)).mem x g) ↔ _
  simp only [vanishingIdeal_empty_unit,BlowupControlledTransform.idealPow_unitIdeal,
    BlowupControlledTransform.colon_unitIdeal hr]
  exact ⟨fun ⟨_,hg⟩ => hg,fun hg => ⟨0,hg⟩⟩

private theorem empty_strict_carrier {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hC : C=∅) {N : Set X} (hN : IsClosedSubmanifold n N) :
    BlowupStrictSubmanifold.geoStrictTransform π C N=π ⁻¹' N := by
  subst C
  change closure (π ⁻¹' (N \ ∅))=π ⁻¹' N
  rw [Set.sdiff_empty,(hN.1.preimage hπ.contMDiff.continuous).closure_eq]

/-- A genuine empty step acts on the normalized whole chronological ideal by actual pullback. -/
theorem nextRelativeStrict_empty {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hNorm : restrictOn n N I=I)
    {π : Y → X} (hπ : IsBlowupAlong n (∅ : Set X) π) :
    nextRelativeStrict N I ∅ π=GermIdeal.pullback (m := n) π I := by
  have hCarrier := empty_strict_carrier hπ rfl hN
  have hp := isCoherent_pullback hπ.contMDiff hI
  obtain ⟨e,he⟩ := exists_empty_blowup_biholomorphism hπ
  have hef : (e : Y → X)=π := funext he
  have hPre : IsClosedSubmanifold n (π ⁻¹' N) := by
    rw [←hef]
    exact (isClosedSubmanifold_preimage_iff e).mpr hN
  change relativeExceptionalSaturation (BlowupStrictSubmanifold.geoStrictTransform π ∅ N)
    (GermIdeal.pullback (m := n) π I) (π ⁻¹' ∅)=_
  rw [hCarrier,Set.preimage_empty,relativeExceptionalSaturation_empty hPre hp,←hef,
    ← restrictOn_pullback_biholo e hN hI,hNorm]

/-- All original positions have the exact same actual composite pullback along an empty tower. -/
theorem original_members_chronological_empty (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (i : Fin E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsEmptyTower T →
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=T.proj ⁻¹' W ∧
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal=
        GermIdeal.pullback (m := n) T.proj (originalRelativeMemberMarked W (E.get i)).ideal
  | _,.refl,_ => by
    refine ⟨rfl,?_⟩
    exact (BlowupControlledTransform.pullback_id
      (original_members_actual_finite_chronological_geometry hn hW hE hdense i .refl trivial).2.2.2.1.isCoherent).symm
  | _,.step T C π hπ,he => by
    obtain ⟨heT,rfl⟩ := he
    obtain ⟨hNT,hIT⟩ := original_members_chronological_empty hn hW hE hdense i T heT
    let M := originalRelativeMemberMarked W (E.get i)
    let A := chronologicalMarked M T
    have hT := isGeoTestTower_of_isEmptyTower (geometricTemplate W []) T heT
    obtain ⟨_hAN,_hAE,_hd,hwA,_hnz,_hpr⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    have hI0 : M.ideal.IsCoherent :=
      (original_members_actual_finite_chronological_geometry hn hW hE hdense i .refl trivial).2.2.2.1.isCoherent
    obtain ⟨e,hep⟩ := exists_empty_tower_projection T heT
    have hef : (e : _ → X)=T.proj := funext hep
    have hNorm : restrictOn n A.N A.ideal=A.ideal := by
      change restrictOn n (chronologicalMarked M T).N (chronologicalMarked M T).ideal=_
      rw [hNT,hIT,←hef,← restrictOn_pullback_biholo e hW hI0]
      change GermIdeal.pullback (m := n) e
        (restrictOn n W (restrictOn n W (vanishingIdeal (n := n) (E.get i))))=_
      rw [restrictOn_idempotent]
      rfl
    refine ⟨?_,?_⟩
    · change BlowupStrictSubmanifold.geoStrictTransform π ∅ A.N=(T.proj ∘ π) ⁻¹' W
      rw [empty_strict_carrier hπ rfl hwA.isClosedSubmanifold_N,hNT]
      rfl
    · change nextRelativeStrict A.N A.ideal ∅ π=GermIdeal.pullback (m := n) (T.proj ∘ π) M.ideal
      rw [nextRelativeStrict_empty hwA.isClosedSubmanifold_N hwA.isCoherent hNorm hπ,hIT,
        ← GermIdealTotalTransform.pullback_comp T.contMDiff_proj hπ.contMDiff hI0]

private theorem template_carrier_empty {W : Set X} (hW : IsClosedSubmanifold n W) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsEmptyTower T →
      (geoTransformAlong (geometricTemplate W []) T).N=T.proj ⁻¹' W
  | _,.refl,_ => rfl
  | _,.step T C π hπ,he => by
    obtain ⟨heT,rfl⟩ := he
    have hTest := isGeoTestTower_of_isEmptyTower (geometricTemplate W []) T heT
    have hw : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hTest
    change BlowupStrictSubmanifold.geoStrictTransform π ∅ (geoTransformAlong (geometricTemplate W []) T).N=_
    rw [empty_strict_carrier hπ rfl hwT.isClosedSubmanifold_N,template_carrier_empty hW T heT]
    rfl

/-- The complete true quotient/order defect is transported by the actual empty projection. -/
theorem chronologicalDistinctDefect_empty (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (T : BlowupTower X Y) (he : IsEmptyTower T) :
    chronologicalDistinctDefect W E T=T.proj ⁻¹' chronologicalDistinctDefect W E (.refl : BlowupTower X X) := by
  obtain ⟨e,hep⟩ := exists_empty_tower_projection T he
  have hef : (e : Y → X)=T.proj := funext hep
  let F := fun i : Fin E.length => (originalRelativeMemberMarked W (E.get i)).ideal
  have hGeom (i : Fin E.length) := original_members_actual_finite_chronological_geometry hn hW hE hdense i .refl trivial
  have hT := isGeoTestTower_of_isEmptyTower (geometricTemplate W []) T he
  have hN := template_carrier_empty hW T he
  have hF : (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal)=
      (fun i : Fin E.length => GermIdeal.pullback (m := n) e (F i)) := by
    funext i
    rw [(original_members_chronological_empty hn hW hE hdense i T he).2,←hef]
  change actualFamilyDistinctDefect (geoTransformAlong (geometricTemplate W []) T).N _=
    T.proj ⁻¹' actualFamilyDistinctDefect W F
  rw [hN,hF,←hef]
  exact actual_family_distinct_defect_biholo hn e hW F
    (fun i => (hGeom i).2.2.2.1.isCoherent)
    (fun i => (hGeom i).2.2.2.2.1)
    (fun i => (hGeom i).2.2.2.2.2)

end
end Hironaka.HironakaSharpActualEmptyChronologicalDefect
