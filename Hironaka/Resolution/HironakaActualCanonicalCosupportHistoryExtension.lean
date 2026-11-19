import Hironaka.Resolution.HironakaOpenCosupportHistoryExtension
import Hironaka.Resolution.HironakaOriginalNCCanonicalOpenReflection
import Hironaka.Resolution.HironakaActualIteratedRelativeNormalHistory
import Hironaka.Blowup.BlowupTowerIsoTail

/-! Actual canonical extension of the SAME GIVEN local history through a
genuine entire-cosupport window. Full values follow DERIVED ambient CAN.
Blueprint: hironaka-actual-canonical-cosupport-history-extension-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualCanonicalCosupportHistoryExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec InvDomainTowerAlong CanonicalCentres
  HironakaActualRelativeNormalGeometry HironakaActualIteratedRelativeNormalHistory
  HironakaActualOpenZeroSectionDifferentials HironakaOpenCosupportHistoryExtension

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

/-- Original domain + genuine entire-cosupport open + GIVEN local CAN
construct the actual ambient CAN and all complete SAME-history comparisons.
Ambient canonicality is derived BEFORE full restriction values are invoked. -/
theorem exists_actual_canonical_extension {n k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (O : Opens X) (hCover : M.cosupp⊆O)
    {Z : CMfd.{u} n} (P : BlowupTower (CMfd.of (n:=n) O) Z)
    (hCanP : IsCanonical (MarkedIdeal.pullback (Subtype.val : O→X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : O→X) M)) P) :
    ∃(Y : CMfd.{u} n) (Q : BlowupTower X Y),IsCanonical M (R.inv M) Q ∧ IsGeoTestTower M Q ∧
      ∃e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q O,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) O ∞) P (restrict O Q) e ∧
        P.length=Q.length ∧ (∀z,Q.proj (e z).val=(P.proj z).val) ∧
        geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→X) M) P=
          MarkedIdeal.pullback (fun z=>(e z).val) (geoTransformAlong M Q) ∧
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→X) M) P).cosupp=
          (fun z=>(e z).val) ⁻¹' (geoTransformAlong M Q).cosupp ∧
        (fun z=>(e z).val) '' (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→X) M) P).cosupp=
          (geoTransformAlong M Q).cosupp ∧
        (∀z∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→X) M) P).cosupp,
          R.inv M Q (e z).val=R.inv (MarkedIdeal.pullback (Subtype.val : O→X) M) P z) ∧
        ResolutionDriver.maxLocus (R.inv M Q) (geoTransformAlong M Q).cosupp=
          (fun z=>(e z).val) '' ResolutionDriver.maxLocus
            (R.inv (MarkedIdeal.pullback (Subtype.val : O→X) M) P)
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→X) M) P).cosupp ∧
        (IsGeoResolution M Q ↔ IsGeoResolution (MarkedIdeal.pullback (Subtype.val : O→X) M) P):=by
  let B : MarkedIdeal n (CMfd.of (n:=n) O):=MarkedIdeal.pullback (Subtype.val : O→X) M
  let Φ:=Diffeomorph.refl 𝓘(ℂ,ComplexModel n) O ∞
  have hB : IsInvDomain k B:=isInvDomain_pullback_val O hM
  have hTestP:=R.isInvValue.isGeoTestTower_of_isCanonical hB P hCanP
  obtain ⟨Y,Q,hTestQ,e,hIso,hLen,hWhole⟩:=
    HironakaOpenCosupportHistoryExtension.exists_extension M hM.isWellFormed O hCover P hTestP
  have hId : MarkedIdeal.pullback (id : O→O) B=B:=
    ContactCanonicalAlong.pullback_id B hB.isWellFormed.isCoherent
  have hCanRes : IsCanonical B (R.inv B) (restrict O Q):=by
    have h:=Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
      (X:=CMfd.of (n:=n) O) (X':=CMfd.of (n:=n) O)
      (T':=restrict O Q) (T:=P) (χ:=e.symm) R hB Φ.symm hIso.symm hCanP
    change IsCanonical (MarkedIdeal.pullback (id : O→O) B)
      (R.inv (MarkedIdeal.pullback (id : O→O) B)) (restrict O Q) at h
    simpa only [hId] using h
  have hCanQ : IsCanonical M (R.inv M) Q:=
    HironakaOriginalNCCanonicalOpenReflection.isCanonical_of_restrict_cosupport_cover
      R M hM O hCover Q hTestQ hCanRes
  let j : Z→Y:=fun z=>(e z).val
  have hTestRes:=R.isInvValue.isGeoTestTower_of_isCanonical hB (restrict O Q) hCanRes
  have hCosIso : (geoTransformAlong B P).cosupp=e ⁻¹' (geoTransformAlong B (restrict O Q)).cosupp:=by
    have h:=BlowupTowerIsomorphism.IsTowerIso.cosupp_geoTransformAlong
      (X:=CMfd.of (n:=n) O) (X':=CMfd.of (n:=n) O)
      (𝔪:=B) (T':=P) (T:=restrict O Q) (χ:=e) Φ
      hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hIso hTestRes
    change (geoTransformAlong (MarkedIdeal.pullback (id : O→O) B) P).cosupp=_ at h
    simpa only [hId] using h
  have hCosRes:=ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent O Q hTestQ
  have hCos : (geoTransformAlong B P).cosupp=j ⁻¹' (geoTransformAlong M Q).cosupp:=by
    rw [hCosIso,hCosRes]
    rfl
  have hCurrentCover : (geoTransformAlong M Q).cosupp⊆openPreimage Q O:=by
    intro y hy
    exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset M
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent Q hTestQ hy)
  have hImage : j '' (geoTransformAlong B P).cosupp=(geoTransformAlong M Q).cosupp:=by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (Set.ext_iff.mp hCos z).mp hz
    · intro hy
      let w : openPreimage Q O:=⟨y,hCurrentCover hy⟩
      let z:=e.symm w
      have hj : j z=y:=congrArg (fun w : openPreimage Q O=>w.val) (e.apply_symm_apply w)
      refine ⟨z,?_,hj⟩
      rw [hCos]
      change j z∈(geoTransformAlong M Q).cosupp
      exact hj.symm ▸ hy
  have hValues : ∀z∈(geoTransformAlong B P).cosupp,R.inv M Q (j z)=R.inv B P z:=by
    intro z hz
    have hzRes : e z∈(geoTransformAlong B (restrict O Q)).cosupp:=(Set.ext_iff.mp hCosIso z).mp hz
    have hzQ : j z∈(geoTransformAlong M Q).cosupp:=(Set.ext_iff.mp hCos z).mp hz
    have hIsoValue:=R.isInvValue.towerIso Φ B hB P (restrict O Q) e hIso hCanRes z hzRes
    change R.inv (MarkedIdeal.pullback (id : O→O) B) P z=R.inv B (restrict O Q) (e z) at hIsoValue
    rw [hId] at hIsoValue
    exact (R.isInvValue.restrictOpen M hM O Q hCanQ (e z) hzQ).symm.trans hIsoValue.symm
  have hSquare : ∀z,Q.proj (j z)=(P.proj z).val:=by
    intro z
    have h:=congrArg (fun p : O=>p.val) (hIso.proj_comm z)
    change (P.proj z).val=((restrict O Q).proj (e z)).val at h
    exact (proj_restrict O Q (e z)).symm.trans h.symm
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
  exact ⟨Y,Q,hCanQ,hTestQ,e,hIso,hLen,hSquare,hWhole,hCos,hImage,hValues,hMaximum,hResolution⟩

private abbrev model {m : ℕ} (U : Opens (ComplexModel m)) : CMfd.{0} m:=CMfd.of (n:=m) U

/-- Original input alone puts the ENTIRE actual finite normal cosupport on
its literal zero section; no future canonical history is supplied. -/
theorem iterated_cosupp_subset_zeroSection {n q : ℕ} {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hn : 0<n) (hM : IsInvDomain q (relativeBaseMarked I)) (r : ℕ) :
    (iteratedMarked I r).cosupp⊆iteratedZeroSection U r '' univ:=by
  obtain ⟨Z,P,j,_hChain,_hCanP,_hTestP,_hLen,hSquare,_hBoundary,_hCos,hImage,_hValues,_hMaximum,_hResolution⟩:=
    exists_original_iterated_normal_base_history hn hM r
      (BlowupTower.refl : BlowupTower (model (iteratedOpen U r)) (model (iteratedOpen U r))) trivial
  intro y hy
  have hy' : y∈j '' (geoTransformAlong (relativeBaseMarked I) P).cosupp:=hImage.symm ▸ hy
  obtain ⟨z,_hz,rfl⟩:=hy'
  exact ⟨P.proj z,mem_univ _,(hSquare z).symm⟩

/-- A genuine window containing the ACTUAL whole normal zero section
internally gives the entire-cosupport cover and extends GIVEN local CAN. -/
theorem exists_actual_iterated_normal_window_extension {n q : ℕ}
    {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hn : 0<n) (hM : IsInvDomain q (relativeBaseMarked I)) (r : ℕ)
    (O : Opens (iteratedOpen U r)) (hZero : ∀x : U,iteratedZeroSection U r x∈O)
    {Z : CMfd.{0} (n+r)} (P : BlowupTower (CMfd.of (n:=n+r) O) Z)
    (hCanP : IsCanonical (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) (iteratedMarked I r))
      ((invFamily (by omega : 0<n+r) (q+r)).inv
        (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) (iteratedMarked I r))) P) :
    let B:=iteratedMarked I r
    let R:=invFamily (by omega : 0<n+r) (q+r)
    ∃(Y : CMfd.{0} (n+r)) (Q : BlowupTower (model (iteratedOpen U r)) Y),
      IsCanonical B (R.inv B) Q ∧ IsGeoTestTower B Q ∧
      ∃e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (n+r))⟯ openPreimage Q O,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel (n+r)) O ∞) P (restrict O Q) e ∧
        P.length=Q.length ∧ (∀z,Q.proj (e z).val=(P.proj z).val) ∧
        geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P=
          MarkedIdeal.pullback (fun z=>(e z).val) (geoTransformAlong B Q) ∧
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P).cosupp=
          (fun z=>(e z).val) ⁻¹' (geoTransformAlong B Q).cosupp ∧
        (fun z=>(e z).val) ''
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P).cosupp=
          (geoTransformAlong B Q).cosupp ∧
        (∀z∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P).cosupp,
          R.inv B Q (e z).val=R.inv (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P z) ∧
        ResolutionDriver.maxLocus (R.inv B Q) (geoTransformAlong B Q).cosupp=
          (fun z=>(e z).val) '' ResolutionDriver.maxLocus
            (R.inv (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P)
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P).cosupp ∧
        (IsGeoResolution B Q ↔
          IsGeoResolution (MarkedIdeal.pullback (Subtype.val : O→iteratedOpen U r) B) P):=by
  have hCover : (iteratedMarked I r).cosupp⊆O:=by
    intro y hy
    obtain ⟨x,_hx,hxy⟩:=iterated_cosupp_subset_zeroSection hn hM r hy
    exact hxy ▸ hZero x
  exact exists_actual_canonical_extension (invFamily (by omega : 0<n+r) (q+r))
    (iteratedMarked I r) (original_iterated_domain hM r) O hCover P hCanP

end
end Hironaka.HironakaActualCanonicalCosupportHistoryExtension
