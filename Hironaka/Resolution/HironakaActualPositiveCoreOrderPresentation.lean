import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Resolution.HironakaStageCenters

/-! The first positive outer-order presentation on genuine noncanonical
histories. Actual parent tests and geometric current order-cut inclusions
DERIVE companion tests. The whole cut and ordered boundary dictionary
refer to the SAME initially formed companion and literal tower. This is
one core layer, not a definition or closure of the recursive BM core. -/
set_option autoImplicit false
open Set Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPositiveCoreOrderPresentation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CompanionReductionAlong CompanionRebase CompanionOpen
  NonmonomialOrderLocal NonmonomialOrderTail HironakaStageCenters
  HomogenizedIdealAlong
open ResolutionInvariantSpec (IsInvDomain)

variable {n k : ℕ} {X : CMfd.{u} n}

/-- The actual once-formed companion presents exactly the geometric
positive order cut along ALL parent tests which stay in that cut. -/
theorem actual_positive_order_test_presentation
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (q : ℕ) (hq : 1≤q)
    (hbound : ∀x∈M.cosupp,x∉ordGe M (q+1)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (companionOf n M q) T ↔
        IsGeoTestTower M T ∧
          StageCentres (fun S C=>C⊆ordGe (geoTransformAlong M S) q) T
  | _, .refl => by exact ⟨fun _=>⟨trivial,trivial⟩,fun _=>trivial⟩
  | _, .step S C π hπ => by
      have hE : (geoTransformAlong (companionOf n M q) S).E=
          (geoTransformAlong M S).E :=
        E_geoTransformAlong_congr (companionAlong_E _ _ _ _ _ _) S
      constructor
      · rintro ⟨hS,hC⟩
        obtain ⟨hSM,hCuts⟩:=
          (actual_positive_order_test_presentation hn M hM q hq hbound S).mp hS
        have hcos:=cosupp_companionOf_geoTransformAlong hn hM hq hbound S hS
        have hSplit (x) (hx : x∈C) :
            x∈ordGe (geoTransformAlong M S) q ∩ (geoTransformAlong M S).cosupp := by
          rw [←hcos]
          exact hC.2.1 hx
        have hCM : (geoTransformAlong M S).IsAdmissibleCentre C :=
          ⟨hC.1,fun x hx=>(hSplit x hx).2,by simpa only [hE] using hC.2.2⟩
        exact ⟨⟨hSM,hCM⟩,hCuts,fun x hx=>(hSplit x hx).1⟩
      · rintro ⟨⟨hSM,hC⟩,hCuts,hCut⟩
        have hS:=
          (actual_positive_order_test_presentation hn M hM q hq hbound S).mpr ⟨hSM,hCuts⟩
        have hcos:=cosupp_companionOf_geoTransformAlong hn hM hq hbound S hS
        refine ⟨hS,hC.1,?_,?_⟩
        · intro x hx
          rw [hcos]
          exact ⟨hCut hx,hC.2.1 hx⟩
        · rw [hE]
          exact hC.2.2

private theorem stage_order_cut_restrict
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (W : Opens X) (q : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      StageCentres (fun S C=>C⊆ordGe (geoTransformAlong M S) q) T →
        StageCentres (fun S C=>C⊆ordGe
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W→X) M) S) q) (restrict W T)
  | _, .refl, _, _ => trivial
  | _, .step S C π hπ, hT, hCuts => by
      refine ⟨stage_order_cut_restrict hn M hM W q S hT.1 hCuts.1,?_⟩
      intro x hx
      rw [geoTransformAlong_restrict W hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent S hT.1]
      have hMS:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hM S hT.1
      exact (mem_ordGe_pullback_val_iff hn hMS.isWellFormed hMS.isNonzeroAlongAt
        (openPreimage S W) q x).mpr (hCuts.2 hx)

/-- The actual internal upper mask produces a genuine maximal-order
companion, all its tests, its ENTIRE transformed cut, the complete SAME
ordered boundary and the surviving upper bound, without canonicity. -/
theorem actual_positive_order_masked_whole_presentation
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (q : ℕ) (hq : 1≤q)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hCuts : StageCentres (fun S C=>C⊆ordGe (geoTransformAlong M S) q) T) :
    let W:=ordMask M q
    let A:=MarkedIdeal.pullback (Subtype.val : W→X) M
    let O:=companionOf n (M:=CMfd.of (n:=n) W) A q
    IsInvDomain k O ∧ IsMaximalOrderAlong O.N O.ideal O.d ∧
      IsGeoTestTower O (restrict W T) ∧
      (geoTransformAlong O (restrict W T)).cosupp=
        (Subtype.val : openPreimage T W→Y) ⁻¹'
          (ordGe (geoTransformAlong M T) q ∩ (geoTransformAlong M T).cosupp) ∧
      (geoTransformAlong O (restrict W T)).E=
        (geoTransformAlong M T).E.map
          (fun H=>(Subtype.val : openPreimage T W→Y) ⁻¹' H) ∧
      ∀z∈(geoTransformAlong M T).cosupp,T.proj z∈W →
        z∉ordGe (geoTransformAlong M T) (q+1) := by
  dsimp only
  let W:=ordMask M q
  let A:=MarkedIdeal.pullback (Subtype.val : W→X) M
  let O:=companionOf n (M:=CMfd.of (n:=n) W) A q
  have hA : IsInvDomain k A:=InvDomainTowerAlong.isInvDomain_pullback_val W hM
  have hbound : ∀x∈A.cosupp,x∉ordGe (M:=CMfd.of (n:=n) W) A (q+1):=
    bound_pullback_val hn hM.isWellFormed hM.isNonzeroAlongAt W
      (fun _ _ hx=>notMem_ordGe_of_mem_ordMask hx)
  have hTA : IsGeoTestTower A (restrict W T):=
    isGeoTestTower_restrict W hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT
  have hCutA:=stage_order_cut_restrict hn M hM W q T hT hCuts
  have hTO : IsGeoTestTower O (restrict W T):=
    (actual_positive_order_test_presentation (X:=CMfd.of (n:=n) W)
      hn A hA q hq hbound (restrict W T)).mpr ⟨hTA,hCutA⟩
  have hMT:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hTransform : geoTransformAlong A (restrict W T)=
      MarkedIdeal.pullback (Subtype.val : openPreimage T W→Y) (geoTransformAlong M T):=
    geoTransformAlong_restrict W hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT
  have hCosupp : (geoTransformAlong A (restrict W T)).cosupp=
      (Subtype.val : openPreimage T W→Y) ⁻¹' (geoTransformAlong M T).cosupp := by
    rw [hTransform]
    exact cosupp_pullback_val _
      (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hMT.isWellFormed.isCoherent hg) _
  have hOrd (r : ℕ) (x : openPreimage T W) :
      x∈ordGe (geoTransformAlong A (restrict W T)) r ↔
        (x:Y)∈ordGe (geoTransformAlong M T) r := by
    rw [hTransform]
    exact mem_ordGe_pullback_val_iff hn hMT.isWellFormed hMT.isNonzeroAlongAt _ r x
  refine ⟨InvDomainCompanion.isInvDomain_companionAlong hn hA hq,?_,hTO,?_,?_,?_⟩
  · simpa only [companionAlong_N] using
      (isMaximalOrderAlong_companionOf (X:=CMfd.of (n:=n) W)
        hn hA.isWellFormed hA.isNonzeroAlongAt hbound)
  · rw [cosupp_companionOf_geoTransformAlong (Z:=CMfd.of (n:=n) W)
      hn hA hq hbound (restrict W T) hTO]
    ext x
    exact and_congr (hOrd q x) (by rw [hCosupp];rfl)
  · have hE : (geoTransformAlong O (restrict W T)).E=
        (geoTransformAlong A (restrict W T)).E :=
      E_geoTransformAlong_congr (companionAlong_E _ _ _ _ _ _) (restrict W T)
    rw [hE,hTransform]
    rfl
  · intro z hz hzW hzBad
    let x : openPreimage T W:=⟨z,hzW⟩
    have hx : x∈(geoTransformAlong A (restrict W T)).cosupp:=by rw [hCosupp];exact hz
    exact (companionOf_tower_facts (Z:=CMfd.of (n:=n) W)
      hn hA hq hbound (restrict W T) hTO).2.1 x hx
      ((hOrd (q+1) x).mpr hzBad)

end
end Hironaka.HironakaActualPositiveCoreOrderPresentation
