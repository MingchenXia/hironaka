import Hironaka.Resolution.HironakaActualCanonicalCosupportHistoryExtension
import Hironaka.Resolution.HironakaBaseChange

/-! The SAME given canonical history extends across a genuine open embedding
whose image contains the entire original cosupport.
Blueprint: hironaka-actual-open-embedding-canonical-extension-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.HironakaActualOpenEmbeddingCanonicalExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec InvDomainTowerAlong CanonicalCentres HironakaBaseChange
  HironakaSmoothSubmersionOrderedChoiceImageTrace

private theorem pullback_comp_marked {n : ℕ} {X Y Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    (f : Y → X) (g : Z → Y)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    MarkedIdeal.pullback g (MarkedIdeal.pullback f M)=MarkedIdeal.pullback (f∘g) M:=by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · exact List.map_map
  · exact (coherent_pullback_comp hf hg M.ideal hI).symm

/-- The original invariant domain pulls back under an actual open embedding. -/
theorem isInvDomain_pullback_of_isOpenHoloEmbedding {n k : ℕ} {X Y : CMfd.{u} n}
    (b : Y → X) (hb : IsOpenHoloEmbedding n b) {M : MarkedIdeal n X}
    (hM : IsInvDomain k M) : IsInvDomain k (MarkedIdeal.pullback b M) := by
  obtain ⟨O, Φ, hΦ⟩ := hb
  have hbEq : b=Subtype.val∘Φ:=funext hΦ
  have h:=isInvDomain_pullback Φ (isInvDomain_pullback_val O hM)
  rw [pullback_comp_marked (Subtype.val : O→X) Φ contMDiff_subtype_val
    Φ.contMDiff M hM.isWellFormed.isCoherent,←hbEq] at h
  exact h

/-- The ENTIRE cosupport pulls back under the actual open embedding. -/
theorem cosupp_pullback_of_isOpenHoloEmbedding {n : ℕ} {X Y : CMfd.{u} n}
    (b : Y → X) (hb : IsOpenHoloEmbedding n b) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) : (MarkedIdeal.pullback b M).cosupp=b ⁻¹' M.cosupp := by
  obtain ⟨O, Φ, hΦ⟩ := hb
  have hbEq : b=Subtype.val∘Φ:=funext hΦ
  have hInitial : MarkedIdeal.pullback b M=
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : O→X) M):=by
    rw [pullback_comp_marked (Subtype.val : O→X) Φ contMDiff_subtype_val Φ.contMDiff M hM.isCoherent,←hbEq]
  rw [hInitial,cosupp_pullback_eq (IsWellFormed.pullback_val hM O).isCoherent,
    cosupp_pullback_val M (fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent ha) O]
  rw [hbEq]
  rfl

private theorem maxLocus_image_of_values {A B : Type u} {Λ : Type v} [LinearOrder Λ]
    (f : A→Λ) (g : B→Λ) (s : Set A) (t : Set B) (j : B→A)
    (hImage : j '' t=s) (hValues : ∀z∈t,f (j z)=g z) :
    ResolutionDriver.maxLocus f s=j '' ResolutionDriver.maxLocus g t:=by
  ext a
  constructor
  · rintro ⟨ha,hmax⟩
    obtain ⟨b,hb,rfl⟩:=hImage.symm ▸ ha
    refine ⟨b,⟨hb,?_⟩,rfl⟩
    intro c hc
    rw [←hValues c hc,←hValues b hb]
    exact hmax (j c) (hImage ▸ mem_image_of_mem j hc)
  · rintro ⟨b,⟨hb,hmax⟩,rfl⟩
    refine ⟨hImage ▸ mem_image_of_mem j hb,?_⟩
    intro a ha
    obtain ⟨c,hc,rfl⟩:=hImage.symm ▸ ha
    rw [hValues c hc,hValues b hb]
    exact hmax c hc

/-- Construct ambient CAN from the SAME GIVEN local CAN through a genuine
entire-cosupport open embedding. Full values are used only after ambient CAN. -/
theorem exists_actual_open_embedding_canonical_extension {n k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (b : Y → X) (hb : IsOpenHoloEmbedding n b) (hCover : M.cosupp⊆range b)
    {Z : CMfd.{u} n} (P : BlowupTower Y Z)
    (hCanP : IsCanonical (MarkedIdeal.pullback b M) (R.inv (MarkedIdeal.pullback b M)) P) :
    ∃(O : Opens X) (Φ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ O),
      (∀y,b y=(Φ y : X)) ∧
      ∃(W : CMfd.{u} n) (Q : BlowupTower X W),IsCanonical M (R.inv M) Q ∧ IsGeoTestTower M Q ∧
        ∃e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q O,
          IsTowerIso Φ P (restrict O Q) e ∧
          P.length=Q.length ∧ (∀z,Q.proj (e z).val=b (P.proj z)) ∧
          geoTransformAlong (MarkedIdeal.pullback b M) P=
            MarkedIdeal.pullback (fun z=>(e z).val) (geoTransformAlong M Q) ∧
          (geoTransformAlong (MarkedIdeal.pullback b M) P).cosupp=
            (fun z=>(e z).val) ⁻¹' (geoTransformAlong M Q).cosupp ∧
          (fun z=>(e z).val) '' (geoTransformAlong (MarkedIdeal.pullback b M) P).cosupp=
            (geoTransformAlong M Q).cosupp ∧
          (∀z∈(geoTransformAlong (MarkedIdeal.pullback b M) P).cosupp,
            R.inv M Q (e z).val=R.inv (MarkedIdeal.pullback b M) P z) ∧
          ResolutionDriver.maxLocus (R.inv M Q) (geoTransformAlong M Q).cosupp=
            (fun z=>(e z).val) '' ResolutionDriver.maxLocus
              (R.inv (MarkedIdeal.pullback b M) P)
              (geoTransformAlong (MarkedIdeal.pullback b M) P).cosupp ∧
          (IsGeoResolution M Q ↔ IsGeoResolution (MarkedIdeal.pullback b M) P):=by
  have hB:=isInvDomain_pullback_of_isOpenHoloEmbedding b hb hM
  have hTestP:=R.isInvValue.isGeoTestTower_of_isCanonical hB P hCanP
  obtain ⟨O,Φ,hΦ⟩:=hb
  have hbEq : b=Subtype.val∘Φ:=funext hΦ
  let D : MarkedIdeal n (CMfd.of (n:=n) O):=MarkedIdeal.pullback (Subtype.val : O→X) M
  let B:=MarkedIdeal.pullback b M
  have hD : IsInvDomain k D:=isInvDomain_pullback_val O hM
  have hInitial : MarkedIdeal.pullback Φ D=B:=by
    dsimp only [D,B]
    rw [pullback_comp_marked (Subtype.val : O→X) Φ contMDiff_subtype_val
      Φ.contMDiff M hM.isWellFormed.isCoherent,←hbEq]
  have hbInv : b∘Φ.symm=(Subtype.val : O→X):=by
    funext x
    rw [Function.comp_apply,hΦ,Φ.apply_symm_apply]
  have hBackInitial : MarkedIdeal.pullback Φ.symm B=D:=by
    dsimp only [B,D]
    rw [pullback_comp_marked b Φ.symm (IsOpenHoloEmbedding.contMDiff ⟨O,Φ,hΦ⟩)
      Φ.symm.contMDiff M hM.isWellFormed.isCoherent,hbInv]
  let H:=transport (X':=CMfd.of (n:=n) O) Φ.symm P
  have hIsoH:=transport_isTowerIso (X':=CMfd.of (n:=n) O) Φ.symm P
  have hCanH : IsCanonical D (R.inv D) H.tower:=by
    have h:=Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
      (X:=Y) (X':=CMfd.of (n:=n) O) R hB Φ.symm hIsoH hCanP
    change IsCanonical (MarkedIdeal.pullback Φ.symm B)
      (R.inv (MarkedIdeal.pullback Φ.symm B)) H.tower at h
    simpa only [hBackInitial] using h
  have hCoverO : M.cosupp⊆O:=by
    intro x hx
    obtain ⟨y,rfl⟩:=hCover hx
    rw [hΦ]
    exact (Φ y).property
  obtain ⟨W,Q,hCanQ,hTestQ,eH,hIsoHQ,_hLenH,_hSquareH,_hWholeH,
      _hCosH,_hImageH,_hValuesH,_hMaxH,_hResolutionH⟩:=
    HironakaActualCanonicalCosupportHistoryExtension.exists_actual_canonical_extension
      R M hM O hCoverO H.tower hCanH
  let e:=H.back.symm.trans eH
  have hΦsymm : Φ.symm.symm=Φ:=by
    ext y
    rfl
  have hIso : IsTowerIso Φ P (restrict O Q) e:=by
    simpa only [hΦsymm,Diffeomorph.trans_refl] using hIsoH.symm.trans hIsoHQ
  have hCanRes:=Seq.ResolutionInvariantExt.isCanonical_restrict R hM O Q hCanQ
  have hTestRes:=R.isInvValue.isGeoTestTower_of_isCanonical hD (restrict O Q) hCanRes
  have hWholeIso : geoTransformAlong B P=
      MarkedIdeal.pullback e (geoTransformAlong D (restrict O Q)):=by
    have h:=BlowupTowerIsomorphism.IsTowerIso.geoTransformAlong_eq Φ
      hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent hIso hTestRes
    simpa only [hInitial] using h
  have hWholeRes:=MarkedIdealRestrictOpen.geoTransformAlong_restrict O
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent Q hTestQ
  have hCurrentI:=(isInvDomain_geoTransformAlong hM Q hTestQ).isWellFormed.isCoherent
  let j : Z→W:=fun z=>(e z).val
  have hWhole : geoTransformAlong B P=MarkedIdeal.pullback j (geoTransformAlong M Q):=by
    rw [hWholeIso,hWholeRes,pullback_comp_marked (Subtype.val : openPreimage Q O→W)
      e contMDiff_subtype_val e.contMDiff (geoTransformAlong M Q) hCurrentI]
    rfl
  have hCosIso : (geoTransformAlong B P).cosupp=
      e ⁻¹' (geoTransformAlong D (restrict O Q)).cosupp:=by
    have h:=BlowupTowerIsomorphism.IsTowerIso.cosupp_geoTransformAlong Φ
      hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent hIso hTestRes
    simpa only [hInitial] using h
  have hCosRes:=ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent O Q hTestQ
  have hCos : (geoTransformAlong B P).cosupp=j ⁻¹' (geoTransformAlong M Q).cosupp:=by
    rw [hCosIso,hCosRes]
    rfl
  have hCurrentCover : (geoTransformAlong M Q).cosupp⊆openPreimage Q O:=by
    intro w hw
    exact hCoverO (TransformOffCentre.cosupp_geoTransformAlong_subset M
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent Q hTestQ hw)
  have hImage : j '' (geoTransformAlong B P).cosupp=(geoTransformAlong M Q).cosupp:=by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (Set.ext_iff.mp hCos z).mp hz
    · intro hw
      let wO : openPreimage Q O:=⟨w,hCurrentCover hw⟩
      let z:=e.symm wO
      have hj : j z=w:=congrArg (fun t : openPreimage Q O=>t.val) (e.apply_symm_apply wO)
      refine ⟨z,?_,hj⟩
      rw [hCos]
      change j z∈(geoTransformAlong M Q).cosupp
      exact hj.symm ▸ hw
  have hValues : ∀z∈(geoTransformAlong B P).cosupp,R.inv M Q (j z)=R.inv B P z:=by
    intro z hz
    have hzRes : e z∈(geoTransformAlong D (restrict O Q)).cosupp:=(Set.ext_iff.mp hCosIso z).mp hz
    have hzQ : j z∈(geoTransformAlong M Q).cosupp:=(Set.ext_iff.mp hCos z).mp hz
    have hIsoValue:=R.isInvValue.towerIso Φ D hD P (restrict O Q) e hIso hCanRes z hzRes
    rw [hInitial] at hIsoValue
    exact (R.isInvValue.restrictOpen M hM O Q hCanQ (e z) hzQ).symm.trans hIsoValue.symm
  have hSquare : ∀z,Q.proj (j z)=b (P.proj z):=by
    intro z
    have h:=congrArg (fun p : O=>p.val) (hIso.proj_comm z)
    exact (proj_restrict O Q (e z)).symm.trans (h.symm.trans (hΦ (P.proj z)).symm)
  have hMaximum:=maxLocus_image_of_values (R.inv M Q) (R.inv B P)
    (geoTransformAlong M Q).cosupp (geoTransformAlong B P).cosupp j hImage hValues
  have hResolution : IsGeoResolution M Q ↔ IsGeoResolution B P:=by
    constructor
    · intro h
      refine ⟨hTestP,?_⟩
      rw [hCos,h.2,preimage_empty]
    · intro h
      refine ⟨hTestQ,?_⟩
      rw [←hImage,h.2,image_empty]
  exact ⟨O,Φ,hΦ,W,Q,hCanQ,hTestQ,e,hIso,
    hIso.length_eq.trans (length_restrict O Q),hSquare,hWhole,hCos,hImage,hValues,hMaximum,hResolution⟩

end
end Hironaka.HironakaActualOpenEmbeddingCanonicalExtension
