import Hironaka.Resolution.HironakaActualRestrictedCompactHistoryExtension
import Hironaka.Resolution.HironakaG4OriginalPlateauHistoryCompatibility

/-! One actual top-distinct-defect order-exit block on the ORIGINAL global
ambient space. The initial local block and entire global extension are
internally constructed. Full carrier/ambient old-plus-born testness and
original compact sharp footprint are retained. Iteration of all joint
residual/cleaning phases remains separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGlobalTopOrderBlock
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
open HironakaActualGeneratedCurrentHistories HironakaActualGeneratedCurrentClocks
open HironakaActualFiniteCompactHistoryExtension HironakaActualRestrictedCompactHistoryExtension
open HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMemberProduct
open HironakaSharpOriginalMemberProductDomain SimultaneousNormalCrossings HomogenizedGlueingTower
open HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
open HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalRestrictedDistinctDefectCentre
open HironakaSharpOriginalDeepProductBlowup HironakaSharpActualOriginalDynamicStep
open HironakaSharpActualDynamicDistinctCentre HironakaG4OriginalPlateauHistoryCompatibility
open RestrictEmptyTower NormalCrossings NonmonomialOrderLocal MonomialPartAlong
open CanonicalCentres GermIdealOrder RestrictedIdealExtension
open MarkedIdealOperationsAlong RestrictedIdealWeight InvertibleIdealQuotient
open HironakaCoherentTransformExtension
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}

private theorem product_domain (hn : 0<n) {W : Set X} {E : List (Set X)}
 (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
 (hdense : W⊆closure (W \ ⋃H∈E,H)) {q : ℕ} (hq : 1≤q) :
 IsInvDomain (n+1) (originalMemberProductMarked W E q) where
 isWellFormed := ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
   isTransverse_nil_of_isClosedSubmanifold hW⟩
 dimLE := by
   intro x hx
   obtain ⟨k,hk⟩ := hW.2 x hx
   exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩
 one_le_d := hq
 isNonzeroAlongAt := fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx

private theorem pullback_template (U : Opens X) (W : Set X) (E : List (Set X)) :
 MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate W E)=
 geometricTemplate (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) := by
 simp [MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal]

private theorem open_geometry {W : Set X} {E : List (Set X)}
 (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
 (hdense : W⊆closure (W \ ⋃H∈E,H)) (U : Opens X) :
 IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' W) ∧
 IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
 (Subtype.val : U → X) ⁻¹' W⊆closure
   (((Subtype.val : U → X) ⁻¹' W) \ ⋃H∈E.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
 refine ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U,
   NormalCrossingsInvariance.isSNCDivisor_map_preimage
     (NormalCrossingsInvariance.pullsBackCoordinates_val U) continuous_subtype_val hE,?_⟩
 intro y hy
 have hp : y∈(Subtype.val : U → X) ⁻¹' closure (W \ ⋃H∈E,H) := hdense hy
 erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
   continuous_subtype_val (W \ ⋃H∈E,H)] at hp
 convert hp using 1
 congr 1
 ext z
 simp

private theorem product_order_eq_nmOrd (hn : 0<n) {W : Set X} {E : List (Set X)}
 (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
 (hdense : W⊆closure (W \ ⋃H∈E,H)) (q : ℕ) {Y : CMfd.{u} n}
 (S : BlowupTower X Y) (hS : IsGeoTestTower (originalMemberProductMarked W E q) S)
 (hGeom : IsGeoTestTower (geometricTemplate W []) S) (y : Y) :
 ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) S).N
   (HironakaSharpActualFiniteMemberProduct.chronologicalMemberProduct W E S) y=
   nmOrd (geoTransformAlong (originalMemberProductMarked W E q) S) y :=
 ((original_product_nmOrd_eq_current hn hW hE hdense q S hS y).trans
   (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense S hGeom y)).symm

private theorem mem_cosupp_of_mark_le_nmOrd {k : ℕ} {Y : CMfd.{u} n}
 {P : MarkedIdeal n Y} (hP : IsInvDomain k P) {y : Y} (hy : y∈P.N)
 (hν : P.d≤nmOrd P y) : y∈P.cosupp := by
 have hle : RestrictLe P.N P.ideal (nonmonomialPartAlong n P.N P.ideal P.E) := by
   intro z _ f hf
   exact IsInSpanAt.restrict (isInSpanAt_self
     (NonmonomialTransformAlong.le_nonmonomialPartAlong_self hP.isWellFormed.isCoherent z f hf)
     (GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hf))
 exact cosupport_subset_of_restrictLe hle P.d
   ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hy P.d).mpr hν)

/-- The native local canonical block is selected internally, then ALL of its
actual centres and blowups are extended to the original global ambient.
No local or global source block/history is an input. -/
theorem exists_actual_global_top_order_block (hn : 0<n) {W : Set X} {E : List (Set X)}
 (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
 (hdense : W⊆closure (W \ ⋃H∈E,H)) (d : ℕ)
 (hreg : ∀x∈W,RegularAtDim (n := n) W x (d+1)) (hcomp : IsCompact W)
 (hne : (originalDistinctDefectPhase W E).Nonempty) :
 ∃(q : ℕ)(U₀ : Opens X)(D : Set X),
   1≤q ∧ D.Nonempty ∧ IsCompact D ∧ D⊆U₀ ∧ D⊆originalSharpBadLocus (n := n) W E ∧
   D=originalDistinctDefectPhase W E ∩ (originalMemberProductMarked W E q).cosupp ∧
   (∀x∈originalDistinctDefectPhase W E,ordinaryTraceOrder W (originalMemberProduct E) x≤q) ∧
   (∀x∈D,ordinaryTraceOrder W (originalMemberProduct E) x=q) ∧
   ∃(Y : CMfd.{u} n)(S : BlowupTower X Y),
     IsGeoTestTower (originalMemberProductMarked W E q) S ∧
     IsGeoTestTower (geometricTemplate W []) S ∧
     IsGeoTestTower (geometricTemplate (univ : Set X) E) S ∧
     CentresOver D S ∧ CompactCentres S ∧
     (∀z : openPreimage S U₀,z.val∈(geoTransformAlong (geometricTemplate W []) S).N →
       ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) S).N
         (HironakaSharpActualFiniteMemberProduct.chronologicalMemberProduct W E S) z.val<q) ∧
     ∃(Y' : CMfd.{u} n)(T : BlowupTower (CMfd.of (n := n) U₀) Y')
       (η : CMfd.of (n := n) (openPreimage S U₀)
         ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (⊤ : Opens Y')),
       IsCanonical (MarkedIdeal.pullback (Subtype.val : U₀ → X) (originalMemberProductMarked W E q))
         ((invFamily hn (n+1)).inv (MarkedIdeal.pullback (Subtype.val : U₀ → X)
           (originalMemberProductMarked W E q))) T ∧
       Generated (originalMemberProductMarked W E q)
         (MarkedIdeal.pullback (Subtype.val : U₀ → X) (originalMemberProductMarked W E q))
         S T (openPreimage S U₀) ⊤ η ∧
       (∀z : openPreimage S U₀,z.val∈(geoTransformAlong (originalMemberProductMarked W E q) S).cosupp →
         (invFamily hn (n+1)).inv (originalMemberProductMarked W E q) S z.val=
         (invFamily hn (n+1)).inv (MarkedIdeal.pullback (Subtype.val : U₀ → X)
           (originalMemberProductMarked W E q)) T (η z).val) ∧
       ∀y∈(geoTransformAlong (geometricTemplate
           ((Subtype.val : U₀ → X) ⁻¹' W) []) T).N,
         ordinaryTraceOrder (geoTransformAlong (geometricTemplate
           ((Subtype.val : U₀ → X) ⁻¹' W) []) T).N
           (HironakaSharpActualFiniteMemberProduct.chronologicalMemberProduct
             ((Subtype.val : U₀ → X) ⁻¹' W) (E.map ((Subtype.val : U₀ → X) ⁻¹' ·)) T) y<q := by
 obtain ⟨q,U,D,hq,hDne,hDK,hDU,hDeq,hmax,hDq,_hBounds,hcos,hK,Y',T,hcan,hT,hFull,hRest⟩ :=
   exists_original_top_order_block_full_ambient_test hn hW hE hdense d hreg hcomp hne
 let M := originalMemberProductMarked W E q
 let A : Fin 3 → MarkedIdeal n X := ![M,geometricTemplate W [],geometricTemplate (univ : Set X) E]
 have hM := product_domain hn hW hE hdense hq
 have hWF : ∀i,(A i).IsWellFormed := by
   intro i
   fin_cases i
   · exact hM.isWellFormed
   · exact ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
   · exact ⟨isClosedSubmanifold_univ,IdealWeightPowers.isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
 have hAhol : ∀i x g,(A i).ideal.mem x g → HolomorphicAt n g x :=
   fun i _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hWF i).isCoherent hg
 have hBWF : ∀i,(MarkedIdeal.pullback (Subtype.val : U → X) (A i)).IsWellFormed :=
   fun i => MarkedIdealRestrictOpen.IsWellFormed.pullback_val (hWF i) U
 have hProd := pullback_val_originalMemberProductMarked hn W hE q U
 have hTarget : ∀i,IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) (A i)) T := by
   intro i
   fin_cases i
   · change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T
     rw [hProd]
     exact hT
   · change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate W [])) T
     simpa only [pullback_template,List.map_nil] using hRest.2.2.1
   · change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate (univ : Set X) E)) T
     simpa only [pullback_template,preimage_univ] using hFull
 have hDomB : IsInvDomain (n+1) (MarkedIdeal.pullback (Subtype.val : U → X) (A 0)) :=
   InvDomainTowerAlong.isInvDomain_pullback_val U hM
 have hKB : IsCompact (MarkedIdeal.pullback (Subtype.val : U → X) (A 0)).cosupp := by
   change IsCompact (MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp
   rw [hProd]
   exact hK
 have hcB : IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) (A 0))
     ((invFamily hn (n+1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) (A 0))) T := by
   change IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
     ((invFamily hn (n+1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M)) T
   rw [hProd]
   exact hcan
 have hAc : ∀x g,IsInSpanAt (n := n) ((A 0).ideal.mem x) x g → (A 0).ideal.mem x g :=
   fun _ _ hg => GermIdealTotalTransform.mem_of_isInSpanAt_mem hM.isWellFormed.isCoherent hg
 obtain ⟨Y,S,V,η,hSource,H,hOver,hCompact,hWindow,hValues⟩ :=
   exists_actual_restricted_compact_canonical_history_extension hn (n+1) (0 : Fin 3) A
     hAhol hAc U hBWF hDomB hKB T hTarget hcB
 have hFoot : (Subtype.val : U → X) '' (MarkedIdeal.pullback (Subtype.val : U → X) (A 0)).cosupp=D := by
   change (Subtype.val : U → X) '' (MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp=D
   rw [hProd,hcos]
   ext x
   constructor
   · rintro ⟨p,hp,rfl⟩;exact hp
   · intro hx;exact ⟨⟨x,hDU hx⟩,hx,rfl⟩
 have hDBad : D⊆originalSharpBadLocus (n := n) W E := fun x hx =>
   originalDistinctDefectPhase_subset_sharpBad hn hW hE hdense ((hDeq ▸ hx).1)
 rw [hFoot] at hOver
 subst hWindow
 have hTargetOrder := hRest.2.2.2.2.2.2.1
 obtain ⟨hWU,hEU,hDenseU⟩ := open_geometry hW hE hdense U
 have hSourceOrder : ∀z : openPreimage S U,
     z.val∈(geoTransformAlong (geometricTemplate W []) S).N →
     ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) S).N
       (HironakaSharpActualFiniteMemberProduct.chronologicalMemberProduct W E S) z.val<q := by
   intro z hzN
   by_contra hnot
   have hOrd := product_order_eq_nmOrd hn hW hE hdense q S (hSource 0) (hSource 1) z.val
   have hge : q≤nmOrd (geoTransformAlong M S) z.val := by
     rw [←hOrd]
     exact Nat.le_of_not_gt hnot
   have hMS := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM S (hSource 0)
   have hNM : (geoTransformAlong M S).N=(geoTransformAlong (geometricTemplate W []) S).N :=
     geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl S
   have hzP : z.val∈(geoTransformAlong M S).N := by rw [hNM];exact hzN
   have hzCos := mem_cosupp_of_mark_le_nmOrd hMS hzP (by rw [d_geoTransformAlong];exact hge)
   have hzB := (generated_order_and_cosupp (hAhol 0) hAc hDomB.isWellFormed (H 0) z).2.mp hzCos
   change (η z).val∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) T).cosupp at hzB
   rw [hProd] at hzB
   have hNmTarget := product_order_eq_nmOrd hn hWU hEU hDenseU q T hT hRest.2.2.1 (η z).val
   have hTargetNM := geoTransformAlong_N_eq_of_N_eq
     (𝔍 := originalMemberProductMarked ((Subtype.val : U → X) ⁻¹' W)
       (E.map ((Subtype.val : U → X) ⁻¹' ·)) q)
     (𝔪 := geometricTemplate ((Subtype.val : U → X) ⁻¹' W) []) rfl T
   have hLess : nmOrd (geoTransformAlong (originalMemberProductMarked
       ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) q) T) (η z).val<q := by
     rw [←hNmTarget]
     apply hTargetOrder
     rw [←hTargetNM]
     exact (geoTransformAlong _ T).cosupp_subset_N hzB
   have hFirst := congrArg (fun v : ValTy (n+1) => (ofLex v).1) (hValues z hzCos)
   change nmOrd (geoTransformAlong M S) z.val=
     nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) T) (η z).val at hFirst
   rw [hProd] at hFirst
   exact (not_lt_of_ge hge) (hFirst.trans_lt hLess)
 refine ⟨q,U,D,hq,hDne,hDK,hDU,hDBad,hDeq,hmax,hDq,Y,S,hSource 0,hSource 1,hSource 2,
   hOver,hCompact,hSourceOrder,Y',T,η,hcB,H 0,hValues,?_⟩
 exact hTargetOrder

end
end Hironaka.HironakaActualGlobalTopOrderBlock
