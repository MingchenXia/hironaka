import Hironaka.Resolution.HironakaSharpOriginalDistinctDefectAnalytic
import Hironaka.Resolution.HironakaSharpOriginalDistinctTraceUSC
import Hironaka.Resolution.HironakaSharpOriginalDeepProductBlowup
import Hironaka.Resolution.HironakaG4PrincipalSupportPower
import Hironaka.Resolution.HironakaSharpActualOriginalDynamicStep
import Hironaka.Resolution.HironakaG4DistinctResidualCountTransform
import Hironaka.Resolution.HironakaSharpActualFiniteDeepPhase
import Hironaka.Resolution.HironakaSharpOriginalFirstDefectOpenNaturality

set_option autoImplicit false

/-! One real canonical top-order block for the SAME fixed original problem.
Source-first complete proof: `hironaka-g4-original-order-block.tex`.
Full old ambient boundary compatibility remains a separate obligation. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4OriginalOrderBlock

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalDistinctDefectAnalytic
  HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalDistinctTraceUSC HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalDeepProductBlowup
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualOriginalDynamicStep
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualDynamicDistinctCentre
  HironakaCoherentTransformExtension HironakaSharpActualFiniteDeepPhase
  HironakaSharpActualInitialFullCompatibility HironakaSharpOriginalFirstDefectOpenNaturality
  HironakaAdmissibleCalculus RestrictEmptyTower
  HironakaG4DistinctResidualCountTransform HironakaG4PrincipalSupportPower
  RelativePrincipalizationSpan NormalCrossings DivisorExponentAlong GermIdealOrder
  CanonicalCentres HironakaAdmissibleSequence MarkedIdealRestrictOpen
  NonmonomialOrderLocal NonmonomialOrderCanonical NonmonomialOrderRegime
  MonomialPartAlong MarkedIdealOperationsAlong RestrictedIdealWeight InvertibleIdealQuotient

open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y Z : CMfd.{u} n}


/-- Every recorded actual centre lies in the true distinct defect of the
same chronological original family, retaining every original position. -/
def IsDistinctPhaseTower (W : Set X) (E : List (Set X)) :
    {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => IsDistinctPhaseTower W E T ∧ C ⊆ chronologicalDistinctDefect W E T

private theorem chronological_count_le_initial (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) y ≤
      actualDistinctProperCount (fun i : Fin E.length =>
        (originalRelativeMemberMarked W (E.get i)).ideal) (T.proj y)
  | _, .refl, _ => le_rfl
  | _, .step T _C π hπ, y =>
      (original_chronological_distinct_count_step_le W E T hπ y).trans
        (chronological_count_le_initial W E T (π y))

private theorem original_domain_succ (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {q : ℕ} (hq : 1 ≤ q) :
    IsInvDomain (n+1) (originalMemberProductMarked W E q) where
  isWellFormed := ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold hW⟩
  dimLE := by
    intro x hx
    obtain ⟨k,hk⟩ := hW.2 x hx
    exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩
  one_le_d := hq
  isNonzeroAlongAt := fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx

private theorem mem_cosupp_of_mark_le_nmOrd {M : MarkedIdeal n X} {k : ℕ}
    (hM : IsInvDomain k M) {x : X} (hx : x ∈ M.N) (hν : M.d ≤ nmOrd M x) :
    x ∈ M.cosupp := by
  have hle : RestrictLe M.N M.ideal (nonmonomialPartAlong n M.N M.ideal M.E) := by
    intro y _ f hf
    exact IsInSpanAt.restrict (isInSpanAt_self
      (NonmonomialTransformAlong.le_nonmonomialPartAlong_self hM.isWellFormed.isCoherent y f hf)
      (GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hf))
  exact cosupport_subset_of_restrictLe hle M.d
    ((mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hx M.d).mpr hν)

private theorem original_nmOrd_eq_actual (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (q : ℕ)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E q) T) (y : Y) :
    nmOrd (geoTransformAlong (originalMemberProductMarked W E q) T) y=
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) y := by
  have hw : (originalMemberProductMarked W E q).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  rw [original_product_nmOrd_eq_current hn hW hE hdense q T hT]
  exact currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T
    (actual_original_test_history_template _ hw T hT) y

private theorem first_order_prefix {M : MarkedIdeal n X} {k : ℕ}
    (hn : 0 < n) (hM : IsInvDomain k M)
    {Λ : Type} [LinearOrder Λ] (f : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Y → Λ)
    (hf : OrdMonotone M f) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T → IsCanonical M f T →
      (∀ y ∈ (geoTransformAlong M T).N,nmOrd (geoTransformAlong M T) y < M.d) →
      ∃ (Z : CMfd.{u} n) (B : BlowupTower X Z),IsGeoTestTower M B ∧ IsCanonical M f B ∧
        (∀ y ∈ (geoTransformAlong M B).N,nmOrd (geoTransformAlong M B) y < M.d) ∧
        CentresOrdGt M (M.d-1) B
  | _, .refl, hT, hcan, hlow => ⟨X,.refl,hT,hcan,hlow,trivial⟩
  | _, .step T C π hπ, hT, hcan, hlow => by
      by_cases hprev : ∀ y ∈ (geoTransformAlong M T).N,nmOrd (geoTransformAlong M T) y < M.d
      · exact first_order_prefix hn hM f hf T hT.1 hcan.1 hprev
      · push Not at hprev
        obtain ⟨y,hy,hyν⟩ := hprev
        have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT.1
        have hyd : (geoTransformAlong M T).d ≤ nmOrd (geoTransformAlong M T) y := by
          rw [d_geoTransformAlong]
          exact hyν
        have hycos := mem_cosupp_of_mark_le_nmOrd hdomT hy hyd
        refine ⟨_,.step T C π hπ,hT,hcan,hlow,?_⟩
        have hq : M.d-1+1 ≤ nmOrd (geoTransformAlong M T) y := by
          have hpos := hM.one_le_d
          omega
        simpa only [BlowupTower.refl_append,geoTransformAlong_refl] using
          (centresOrdGt_of_canonical hn hM hf (.refl : BlowupTower X X) T C π hπ
            (by simpa only [BlowupTower.refl_append] using hT)
            (by simpa only [BlowupTower.refl_append] using hcan) y
            (by simpa only [BlowupTower.refl_append] using hycos)
            (by simpa only [BlowupTower.refl_append] using hq))

private theorem original_inv_ordMonotone (hn : 0 < n) (W : Set X) (E : List (Set X)) (q : ℕ) :
    OrdMonotone (originalMemberProductMarked W E q)
      ((invFamily hn (n+1)).inv (originalMemberProductMarked W E q)) :=
  ordMonotone_toLex _ (fun {Y} T y =>
    (ofLex ((invFamily hn (n+1)).inv (originalMemberProductMarked W E q) (Y := Y) T y)).2)

private theorem phase_of_centresOrdGt (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {q : ℕ} (hq : 1 ≤ q)
    (hcount : ∀ x ∈ (originalMemberProductMarked W E q).cosupp,
      actualDistinctProperCount (fun i : Fin E.length =>
        (originalRelativeMemberMarked W (E.get i)).ideal) x < q) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (originalMemberProductMarked W E q) T →
      CentresOrdGt (originalMemberProductMarked W E q) (q-1) T → IsDistinctPhaseTower W E T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hT, hcentres => by
      refine ⟨phase_of_centresOrdGt hn hW hE hdense hq hcount T hT.1 hcentres.1,?_⟩
      intro c hc
      let M := originalMemberProductMarked W E q
      have hdom := original_domain_succ hn hW hE hdense hq
      have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hT.1
      have hcQ := hT.2.2.1 hc
      have hcN := (geoTransformAlong M T).cosupp_subset_N hcQ
      have hN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
      have hcTemp : c ∈ (geoTransformAlong (geometricTemplate W []) T).N := by
        rw [←hN]
        exact hcN
      have hcν := (mem_ordGe_iff hdomT.isWellFormed hdomT.isNonzeroAlongAt hcN (q-1+1)).mp
        (hcentres.2 hc)
      have hcActual : q ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) c := by
        rw [←original_nmOrd_eq_actual hn hW hE hdense q T hT.1]
        omega
      have hOver := centresOver_cosupp M hW (isCoherent_originalMemberProduct hn hE)
        (.step T C π hπ) hT
      have hsmall := (chronological_count_le_initial W E T c).trans_lt
        (hcount (T.proj c) (hOver.2 hc))
      change c ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
        actualDistinctProperCount (fun i : Fin E.length =>
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) c < _
      refine ⟨hcTemp,?_⟩
      rw [←chronological_product_eq_actual_family_product W E T]
      exact hsmall.trans_le hcActual

private theorem original_open_geometry {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (U : Opens X) :
    IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' W) ∧
      IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (Subtype.val : U → X) ⁻¹' W ⊆ closure ((Subtype.val : U → X) ⁻¹' W \
        ⋃ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
  refine ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U,
    NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val U) continuous_subtype_val hE,?_⟩
  intro y hy
  have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
  erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
    continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

/-- A true compact original defect internally supplies the positive top mark,
its entire compact plateau, and one actual open product problem whose full
cosupport is precisely that plateau. -/
theorem exists_original_top_order_window (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1)) (hcomp : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (q : ℕ) (U : Opens X) (D : Set X),1 ≤ q ∧ D.Nonempty ∧ IsCompact D ∧ D ⊆ U ∧
      D=originalDistinctDefectPhase W E ∩ (originalMemberProductMarked W E q).cosupp ∧
      (∀ x ∈ originalDistinctDefectPhase W E,
        ordinaryTraceOrder W (originalMemberProduct E) x ≤ q) ∧
      (∀ x ∈ D,ordinaryTraceOrder W (originalMemberProduct E) x=q) ∧
      (∀ x ∈ W,x ∈ U → ordinaryTraceOrder W (originalMemberProduct E) x ≤ q ∧
        distinctProperTraceGermCount (n := n) W E x < q) ∧
      (originalMemberProductMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) q).cosupp=
          (Subtype.val : U → X) ⁻¹' D ∧
      IsCompact (originalMemberProductMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) q).cosupp := by
  let ν : X → ℕ := ordinaryTraceOrder W (originalMemberProduct E)
  let t : X → ℕ := distinctProperTraceGermCount (n := n) W E
  let Z₀ : Set X := originalDistinctDefectPhase W E
  have hZ : IsCompact Z₀ := isCompact_originalDistinctDefectPhase hn hW hE hdense d hreg hcomp
  have hI := isCoherent_originalMemberProduct hn hE
  have hNZ : ∀ x ∈ W,IsNonzeroAlongAt W (originalMemberProduct E) x :=
    fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx
  obtain ⟨A,hA⟩ := exists_bounded_ordinaryTraceOrder_on_isCompact hn hW hI hNZ hZ
    (fun _ hx => hx.1)
  let R : Finset ℕ := (Finset.range (A+1)).filter (fun j => ∃ x ∈ Z₀,ν x=j)
  have hmem (x : X) (hx : x ∈ Z₀) : ν x ∈ R := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hA x hx)),x,hx,rfl⟩
  obtain ⟨a,ha⟩ := hne
  have hR : R.Nonempty := ⟨ν a,hmem a ha⟩
  let q : ℕ := R.max' hR
  obtain ⟨b,hb,hbν⟩ := (Finset.mem_filter.mp (Finset.max'_mem R hR)).2
  have hmax (x : X) (hx : x ∈ Z₀) : ν x ≤ q := Finset.le_max' R (ν x) (hmem x hx)
  have hq : 1 ≤ q := by
    have ht : t b < ν b := hb.2
    omega
  let D : Set X := Z₀ ∩ (originalMemberProductMarked W E q).cosupp
  have hbD : b ∈ D := ⟨hb,(ordinaryTraceOrder_cosupport_iff hW hI hNZ hb.1 q).mpr (by
    change q ≤ ν b
    omega)⟩
  have hDc : IsCompact D := hZ.inter_right
    (isComplexAnalyticSubset_originalMemberProduct_cosupport hn hW hE q).isClosed
  have hDν (x : X) (hx : x ∈ D) : ν x=q :=
    le_antisymm (hmax x hx.1) ((ordinaryTraceOrder_cosupport_iff hW hI hNZ hx.1.1 q).mp hx.2)
  let U : Opens X := ⟨interior {x | x ∈ W → ν x ≤ q ∧ t x < q},isOpen_interior⟩
  have hDU : D ⊆ U := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [eventually_originalProductTraceOrder_le hn hW hE hdense hx.1.1,
      eventually_distinctProperTraceGermCount_le hn hW hE hx.1.1] with y hyν hyt hyW
    have heq := hDν x hx
    have ht : t x < ν x := hx.1.2
    exact ⟨by change ν y ≤ ν x at hyν; omega,
      lt_of_le_of_lt (hyt hyW) (by change t x < q; omega)⟩
  have hwindow (x : X) (hxW : x ∈ W) (hxU : x ∈ U) : ν x ≤ q ∧ t x < q :=
    interior_subset hxU hxW
  have hrestriction :
      (originalMemberProductMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) q).cosupp=
          (Subtype.val : U → X) ⁻¹' (originalMemberProductMarked W E q).cosupp := by
    rw [← pullback_val_originalMemberProductMarked hn W hE q U]
    exact cosupp_pullback_val _ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) U
  have hcos :
      (originalMemberProductMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) q).cosupp=
          (Subtype.val : U → X) ⁻¹' D := by
    rw [hrestriction]
    ext y
    constructor
    · intro hy
      have hyW : y.val ∈ W := hy.1
      have hyt := (hwindow y.val hyW y.property).2
      have hyν := (ordinaryTraceOrder_cosupport_iff hW hI hNZ hyW q).mp hy
      exact ⟨⟨hyW,lt_of_lt_of_le hyt hyν⟩,hy⟩
    · intro hy
      exact hy.2
  have hDopen : IsCompact ((Subtype.val : U → X) ⁻¹' D) := by
    let : CompactSpace D := isCompact_iff_compactSpace.mp hDc
    let lift : D → U := fun x => ⟨x.val,hDU x.property⟩
    have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
    have hrange : Set.range lift=(Subtype.val : U → X) ⁻¹' D := by
      ext y
      constructor
      · rintro ⟨x,rfl⟩
        exact x.property
      · intro hy
        exact ⟨⟨y.val,hy⟩,Subtype.ext rfl⟩
    rw [← hrange]
    exact isCompact_range hlift
  exact ⟨q,U,D,hq,⟨b,hbD⟩,hDc,hDU,rfl,hmax,hDν,hwindow,hcos,hcos.symm ▸ hDopen⟩

private theorem exists_fixed_original_order_block (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {q : ℕ} (hq : 1 ≤ q)
    (hK : IsCompact (originalMemberProductMarked W E q).cosupp)
    (hcount : ∀ x ∈ (originalMemberProductMarked W E q).cosupp,
      distinctProperTraceGermCount (n := n) W E x < q) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical (originalMemberProductMarked W E q)
        ((invFamily hn (n+1)).inv (originalMemberProductMarked W E q)) T ∧
      IsGeoTestTower (originalMemberProductMarked W E q) T ∧
      IsDistinctPhaseTower W E T ∧ CentresOrdGt (originalMemberProductMarked W E q) (q-1) T ∧
      IsGeoTestTower (geometricTemplate W []) T ∧
      CentresOver (originalMemberProductMarked W E q).cosupp T ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalMemberProductMarked W E q).cosuppᶜ ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) y < q) ∧
      IsClosedSubmanifold n (geoTransformAlong (geometricTemplate W []) T).N ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate W []) T).E ∧
      IsTransverse n (geoTransformAlong (geometricTemplate W []) T).N
        (geoTransformAlong (geometricTemplate W []) T).E := by
  let M := originalMemberProductMarked W E q
  have hdom := original_domain_succ hn hW hE hdense hq
  obtain ⟨Y,T,hcan,hres⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (invFamily hn (n+1)) hdom hK
  have hterminal := terminal_original_marking_bounds_actual_product hn hW hE hdense hq T hres
  have hlow : ∀ y ∈ (geoTransformAlong M T).N,nmOrd (geoTransformAlong M T) y < M.d := by
    intro y hy
    rw [original_nmOrd_eq_actual hn hW hE hdense q T hres.1]
    apply hterminal y
    rw [←geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T]
    exact hy
  obtain ⟨Z,B,hBtest,hBcan,hBlow,hBcentres⟩ := first_order_prefix hn hdom
    ((invFamily hn (n+1)).inv M) (original_inv_ordMonotone hn W E q) T hres.1 hcan hlow
  have hBphase : IsDistinctPhaseTower W E B := by
    apply phase_of_centresOrdGt hn hW hE hdense hq (T := B) (hcount := ?_) hBtest hBcentres
    intro x hx
    rw [initial_actual_distinct_count_eq_source]
    exact hcount x hx
  have hGeom := actual_original_test_history_template M hdom.isWellFormed B hBtest
  have hOver := centresOver_cosupp M hW (isCoherent_originalMemberProduct hn hE) B hBtest
  have hAdm := isAdmissibleBlowupSequence_proj M M.cosupp B hBtest hOver
  have hIso := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm
  have hwTemp : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwTemp B hGeom
  refine ⟨Z,B,hBcan,hBtest,hBphase,hBcentres,hGeom,hOver,
    isProperMap_of_isBlowupSequence B.isBlowupSequence,hIso,?_,
    hwB.isClosedSubmanifold_N,hwB.isSNCDivisor,hwB.isTransverse⟩
  intro y hy
  rw [←original_nmOrd_eq_actual hn hW hE hdense q B hBtest]
  apply hBlow y
  rw [geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl B]
  exact hy

/-- Internally choose the true original top-order window, apply compact canonical
resolution ONCE to that fixed actual mark-q input, and retain its actual first
order-exit block. This asserts only auxiliary born-boundary test geometry. -/
theorem exists_original_top_order_block (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1)) (hcomp : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (q : ℕ) (U : Opens X) (D : Set X),
      let WU := (Subtype.val : U → X) ⁻¹' W
      let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
      let M := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU q
      1 ≤ q ∧ D.Nonempty ∧ IsCompact D ∧ D ⊆ U ∧
      D=originalDistinctDefectPhase W E ∩ (originalMemberProductMarked W E q).cosupp ∧
      (∀ x ∈ originalDistinctDefectPhase W E,
        ordinaryTraceOrder W (originalMemberProduct E) x ≤ q) ∧
      (∀ x ∈ D,ordinaryTraceOrder W (originalMemberProduct E) x=q) ∧
      (∀ x ∈ W,x ∈ U → ordinaryTraceOrder W (originalMemberProduct E) x ≤ q ∧
        distinctProperTraceGermCount (n := n) W E x < q) ∧
      M.cosupp=(Subtype.val : U → X) ⁻¹' D ∧ IsCompact M.cosupp ∧
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsCanonical M ((invFamily hn (n+1)).inv M) T ∧ IsGeoTestTower M T ∧
        IsDistinctPhaseTower WU EU T ∧ CentresOrdGt M (q-1) T ∧
        IsGeoTestTower (geometricTemplate WU []) T ∧ CentresOver M.cosupp T ∧
        IsProperMap T.proj ∧ IsIsomorphismOver n T.proj M.cosuppᶜ ∧
        (∀ y ∈ (geoTransformAlong (geometricTemplate WU []) T).N,
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate WU []) T).N
            (chronologicalMemberProduct WU EU T) y < q) ∧
        IsClosedSubmanifold n (geoTransformAlong (geometricTemplate WU []) T).N ∧
        IsSNCDivisor n (geoTransformAlong (geometricTemplate WU []) T).E ∧
        IsTransverse n (geoTransformAlong (geometricTemplate WU []) T).N
          (geoTransformAlong (geometricTemplate WU []) T).E := by
  obtain ⟨q,U,D,hq,hDne,hDc,hDU,hDeq,hmax,hDν,hwindow,hcos,hcompact⟩ :=
    exists_original_top_order_window hn hW hE hdense d hreg hcomp hne
  refine ⟨q,U,D,hq,hDne,hDc,hDU,hDeq,hmax,hDν,hwindow,hcos,hcompact,?_⟩
  obtain ⟨hWU,hEU,hdenseU⟩ := original_open_geometry hW hE hdense U
  apply exists_fixed_original_order_block hn hWU hEU hdenseU hq hcompact
  intro x hx
  rw [original_distinct_count_open hn hE U x hx.1]
  exact (hwindow x.val hx.1 x.property).2

end

end Hironaka.HironakaG4OriginalOrderBlock
