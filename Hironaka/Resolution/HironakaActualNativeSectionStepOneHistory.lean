import Hironaka.Resolution.HironakaActualNativeSectionInitialBar
import Hironaka.Resolution.HironakaActualSectionBoundaryGeometry

/-! The ORIGINAL bar record and Step One special/level chronology on actual
finite native histories. Initial bar naturality is produced on the literal
zero plane, and current records/clocks follow without any restart. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionStepOneHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings StepOneValue StepOneRegime BoundaryCount
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionRegularity HironakaActualNativeSectionMemberLocus
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
variable {n k : ℕ}

section Generic
variable {X : CMfd.{0} n} {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n:=n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

private theorem original_bar_records
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M)) :
    geoTransformAlong (barMarked (nativePullback hk W hW M)) Q=
      nativePullback hk V hV (geoTransformAlong (barMarked M) T) := by
  have hHol : ∀x g,(barMarked M).ideal.mem x g → HolomorphicAt n g x:=
    fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (isCoherent_barMarked M hN hI) hg
  have hr:=h.whole_records hn hE hTrans (barMarked M) hME hMN hHol
  rwa [hBar] at hr

private theorem original_member_prefix
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M)) :
    (origMembers M T).map ((Subtype.val : V→Y) ⁻¹' ·)=
      origMembers (nativePullback hk W hW M) Q := by
  have hr:=original_bar_records h hn hE hTrans M hME hMN hN hI hBar
  have he:=congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV)=>K.E) hr
  have hLen : (nativePullback hk W hW M).E.length=M.E.length:=List.length_map _
  change (geoTransformAlong (barMarked (nativePullback hk W hW M)) Q).E=
    (geoTransformAlong (barMarked M) T).E.map ((Subtype.val : V→Y) ⁻¹' ·) at he
  unfold origMembers
  rw [he,hLen,←List.map_take]

private theorem original_level_special
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M))
    (p : nativeManifold hk V hV) :
    level M T p.val=level (nativePullback hk W hW M) Q p ∧
      (IsSpecial M T p.val ↔ IsSpecial (nativePullback hk W hW M) Q p) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let B:=nativePullback hk W hW M
  let MT:=geoTransformAlong (barMarked M) T
  let BQ:=geoTransformAlong (barMarked B) Q
  have hHol : ∀x g,(barMarked M).ideal.mem x g → HolomorphicAt n g x:=
    fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (isCoherent_barMarked M hN hI) hg
  have hOrig:=original_member_prefix h hn hE hTrans M hME hMN hN hI hBar
  have hLevel : level M T p.val=level B Q p:=by
    unfold level
    rw [←hOrig,boundaryCount_map]
    rfl
  have hr:=original_bar_records h hn hE hTrans M hME hMN hN hI hBar
  have hNrec : BQ.N=(Subtype.val : V→Y) ⁻¹' MT.N:=
    congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV)=>K.N) hr
  have hCrec : BQ.cosupp=(Subtype.val : V→Y) ⁻¹' MT.cosupp:=by
    have hc:=Lift.current_cosupport h hn hE hTrans (barMarked M) hME hMN hHol
    rwa [hBar] at hc
  have hZ:=(HironakaActualNativeSectionRegularity.Lift.current_codimOnePart h
    hn hE hTrans (barMarked M) hME hMN hHol)
  rw [hBar] at hZ
  have hZp : p.val∈CodimOneSupportAlong.codimOnePartAlong MT.N MT.ideal MT.d ↔
      p∈CodimOneSupportAlong.codimOnePartAlong BQ.N BQ.ideal BQ.d:=
    Iff.of_eq (congrArg (fun S : Set (nativeManifold hk V hV)=>p∈S) hZ)
  have hNsub : MT.N⊆V:=Lift.current_carrier_subset h (barMarked M) hMN
  have hImageN : (Subtype.val : V→Y) '' ((Subtype.val : V→Y) ⁻¹' MT.N)=MT.N:=by
    ext y
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hy;exact ⟨⟨y,hNsub hy⟩,hy,rfl⟩
  have hImageC : (Subtype.val : V→Y) '' ((Subtype.val : V→Y) ⁻¹' MT.cosupp)=MT.cosupp:=by
    ext y
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hy;exact ⟨⟨y,hNsub (MT.cosupp_subset_N hy)⟩,hy,rfl⟩
  have hL:=memberInterLocus_native_preimage ((Subtype.val : V→Y) ⁻¹' MT.N)
    ((Subtype.val : V→Y) ⁻¹' MT.cosupp) (origMembers M T)
  rw [hImageN,hImageC,←hNrec,←hCrec,hOrig] at hL
  have hLp : p.val∈MemberInterLocusAlong.memberInterLocus MT.N (origMembers M T) MT.cosupp ↔
      p∈MemberInterLocusAlong.memberInterLocus BQ.N (origMembers B Q) BQ.cosupp:=
    Iff.of_eq (congrArg (fun S : Set (nativeManifold hk V hV)=>p∈S) hL)
  refine ⟨hLevel,?_⟩
  unfold IsSpecial
  change ((level M T p.val=0 ∧ p.val∈CodimOneSupportAlong.codimOnePartAlong MT.N MT.ideal MT.d) ∨
      (1≤level M T p.val ∧ p.val∈MemberInterLocusAlong.memberInterLocus MT.N (origMembers M T) MT.cosupp)) ↔
    ((level B Q p=0 ∧ p∈CodimOneSupportAlong.codimOnePartAlong BQ.N BQ.ideal BQ.d) ∨
      (1≤level B Q p ∧ p∈MemberInterLocusAlong.memberInterLocus BQ.N (origMembers B Q) BQ.cosupp))
  rw [hLevel]
  exact or_congr (and_congr Iff.rfl hZp) (and_congr Iff.rfl hLp)

private theorem original_step_regime
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M))
    (s : ℕ) (p : nativeManifold hk V hV) :
    stepRegime M s T p.val ↔ stepRegime (nativePullback hk W hW M) s Q p := by
  obtain ⟨hl,hs⟩:=original_level_special h hn hE hTrans M hME hMN hN hI hBar p
  change (level M T p.val=s ∧ ¬IsSpecial M T p.val) ↔
    (level (nativePullback hk W hW M) Q p=s ∧ ¬IsSpecial (nativePullback hk W hW M) Q p)
  exact and_congr (by rw [hl]) (not_congr hs)

private theorem original_step_regime_run
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M))
    (s : ℕ) : ∀p : nativeManifold hk V hV,
    regimeRun (stepRegime M s) T p.val=
      regimeRun (stepRegime (nativePullback hk W hW M) s) Q p := by
  induction h with
  | refl => intro p;rfl
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    intro p
    classical
    let z:=nativeProjection hk hVc hV D π hπ p
    have hp:=original_step_regime h hn hE hTrans M hME hMN hN hI hBar s z
    change (if stepRegime M s T z.val then regimeRun (stepRegime M s) T z.val+1 else 0)=
      if stepRegime (nativePullback hk W hW M) s Q z then
        regimeRun (stepRegime (nativePullback hk W hW M) s) Q z+1 else 0
    by_cases hz : stepRegime M s T z.val
    · rw [if_pos hz,if_pos (hp.mp hz),ih z]
    · rw [if_neg hz,if_neg (fun h' => hz (hp.mpr h'))]

end Generic

private theorem zeroPlane_closed (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n:=n) (M:=U))).1

/-- On the actual zero plane, initial bar naturality is produced internally.
The conclusion concerns the whole original bar record, the ordered original
boundary prefix, both branches of specialness, and the unreset primitive
level-regime clock at every point of every geometry-only native history. -/
theorem actual_section_step_one_chronology
    (U : Opens (ComplexModel n)) (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (hE : IsSNCDivisor n E)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ)
    {Y : CMfd.{0} (n+1)} {T : BlowupTower (CMfd.of (n:=n+1) (productOpen U)) Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n+1) V y n}
    {Q : BlowupTower (nativeManifold (Y:=CMfd.of (n:=n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Nat.le_succ n) V hV)}
    (h : Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U)
      (E.map (projection U ⁻¹' ·)) T V hVc hV Q) :
    let M : MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B:=nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
    geoTransformAlong (barMarked B) Q=
        nativePullback (Nat.le_succ n) V hV (geoTransformAlong (barMarked M) T) ∧
      (origMembers M T).map ((Subtype.val : V→Y) ⁻¹' ·)=origMembers B Q ∧
      (∀p : nativeManifold (Nat.le_succ n) V hV,
        level M T p.val=level B Q p ∧ (IsSpecial M T p.val ↔ IsSpecial B Q p)) ∧
      (∀s (p : nativeManifold (Nat.le_succ n) V hV),stepRegime M s T p.val ↔ stepRegime B s Q p) ∧
      (∀s (p : nativeManifold (Nat.le_succ n) V hV),
        regimeRun (stepRegime M s) T p.val=regimeRun (stepRegime B s) Q p) := by
  let M : MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  have hMN : M.N⊆zeroPlane U:=fun _ hx=>⟨mem_univ _,hx.2⟩
  have hN : IsClosedSubmanifold (n+1) M.N:=
    liftedCarrier_closed_submanifold hA
  have hE' :=HironakaActualSectionBoundaryGeometry.isSNCDivisor_preimage_projection (U:=U) E hE
  have hTrans :=HironakaActualSectionBoundaryGeometry.isTransverse_liftedCarrier (U:=U) (univ : Set U) E
    (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE)
  have hBar:=nativePullback_section_barMarked U A hA E J hJ d
  have hn : 0<n+1:=Nat.zero_lt_succ n
  exact ⟨original_bar_records h hn hE' hTrans M rfl hMN hN hJ hBar,
    original_member_prefix h hn hE' hTrans M rfl hMN hN hJ hBar,
    original_level_special h hn hE' hTrans M rfl hMN hN hJ hBar,
    original_step_regime h hn hE' hTrans M rfl hMN hN hJ hBar,
    original_step_regime_run h hn hE' hTrans M rfl hMN hN hJ hBar⟩

end
end Hironaka.HironakaActualNativeSectionStepOneHistory

namespace Hironaka.HironakaActualNativeSectionStepOneHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings StepOneValue StepOneRegime BoundaryCount
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionRegularity HironakaActualNativeSectionMemberLocus
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
variable {n k : ℕ}

section PublicNativeChronology
variable {X : CMfd.{0} n} {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n:=n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

/- Root-approved append-only exact private export; zero producer credit. -/
theorem native_original_bar_records
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M)) :
    geoTransformAlong (barMarked (nativePullback hk W hW M)) Q=
      nativePullback hk V hV (geoTransformAlong (barMarked M) T) :=
  original_bar_records h hn hE hTrans M hME hMN hN hI hBar

/- Root-approved append-only exact private export; zero producer credit. -/
theorem native_original_member_prefix
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M)) :
    (origMembers M T).map ((Subtype.val : V→Y) ⁻¹' ·)=
      origMembers (nativePullback hk W hW M) Q :=
  original_member_prefix h hn hE hTrans M hME hMN hN hI hBar

/- Root-approved append-only exact private export; zero producer credit. -/
theorem native_original_level_special
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M))
    (p : nativeManifold hk V hV) :
    level M T p.val=level (nativePullback hk W hW M) Q p ∧
      (IsSpecial M T p.val ↔ IsSpecial (nativePullback hk W hW M) Q p) :=
  original_level_special h hn hE hTrans M hME hMN hN hI hBar p

/- Root-approved append-only exact private export; zero producer credit. -/
theorem native_original_step_regime
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M))
    (s : ℕ) (p : nativeManifold hk V hV) :
    stepRegime M s T p.val ↔ stepRegime (nativePullback hk W hW M) s Q p :=
  original_step_regime h hn hE hTrans M hME hMN hN hI hBar s p

/- Root-approved append-only exact private export; zero producer credit. -/
theorem native_original_step_regime_run
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hBar : nativePullback hk W hW (barMarked M)=barMarked (nativePullback hk W hW M))
    (s : ℕ) : ∀p : nativeManifold hk V hV,
    regimeRun (stepRegime M s) T p.val=
      regimeRun (stepRegime (nativePullback hk W hW M) s) Q p :=
  original_step_regime_run h hn hE hTrans M hME hMN hN hI hBar s

end PublicNativeChronology
end
end Hironaka.HironakaActualNativeSectionStepOneHistory
