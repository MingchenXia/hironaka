import Hironaka.Resolution.HironakaActualSharedBornTraceTests
import Hironaka.Resolution.HironakaActualCartierTraceSuccessor
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSharedCartierTraceTests
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  NormalCrossings BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec RelativePrincipalizationSpan InvertibleIdealQuotient
  GiraudAlong GermIdealTotalTransform GermIdealPullbackCalculus GermIdealOrder
  IdealOrderArithmetic IdealWeightPowers CompanionReductionAlong
  HironakaSharpOriginalProductTraceOrder HironakaActualAnchoredVerticalChart
  HironakaActualAnchoredOriginalIdealOrder HironakaActualAnchoredSeedTotalFactor
  HironakaActualProperOriginalTowerFactor HironakaActualProjectionTestRecord
  HironakaActualProjectionVerticalBlowupChart HironakaActualProjectionVerticalOrder
  HironakaOneDimensionalCanonicalSuperlevels InvDomainTowerAlong
  BlowupExceptionalDivisor BlowupFunctionTransform MarkedIdealOperationsAlong
  RestrictedIdealWeight RestrictedIdealQuotient NonmonomialOrderLocal
  HironakaActualCartierTraceSuccessor HironakaActualPolymorphicBornExponent
  MemberInterAlong DivisorExponentAlong
open HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci
open scoped ProductComplexManifold

/-! Native P09 count geometry and whole-record outputs. The recursive
geometric state has no ideal, mark, admissibility or native-test field.
Blueprint FIRST: `hironaka-actual-shared-cartier-trace-tests.tex`. -/

structure CartierGeometryState {m : ℕ} (X : CMfd.{u} m) where
  Y : CMfd.{u} m
  R : BlowupTower X Y
  N : Set Y
  E : List (Set Y)
  i : Fin E.length
  z : Y
  hN : IsClosedSubmanifold m N
  hE : IsSNCDivisor m E
  hT : IsTransverse m N E
  hz : z ∈ N ∩ E.get i

structure CartierGeometryFamily {m : ℕ} (X : CMfd.{u} m) where
  state : ℕ → CartierGeometryState X
  zeroAmbient : (state 0).Y = X
  zeroTower : HEq (state 0).R (BlowupTower.refl : BlowupTower X X)
  π : (s : ℕ) → (state (s+1)).Y → (state s).Y
  hπ : ∀ s, IsBlowupAlong m ((state s).N ∩ (state s).E.get (state s).i) (π s)
  stepTower : ∀ s, (state (s+1)).R = BlowupTower.step (state s).R
    ((state s).N ∩ (state s).E.get (state s).i) (π s) (hπ s)
  stepN : ∀ s, (state (s+1)).N = geoStrictTransform (π s)
    ((state s).N ∩ (state s).E.get (state s).i) (state s).N
  stepE : ∀ s, (state (s+1)).E =
    (state s).E.map (geoStrictTransform (π s) ((state s).N ∩ (state s).E.get (state s).i)) ++
      [(π s) ⁻¹' ((state s).N ∩ (state s).E.get (state s).i)]
  lastIndex : ∀ s, ((state (s+1)).i).val = (state s).E.length
  pointMap : ∀ s, π s (state (s+1)).z = (state s).z
  carrierImage : ∀ s, π s '' (state (s+1)).N = (state s).N
  separatedSlot : ∀ s, (state (s+1)).N ∩ geoStrictTransform (π s)
    ((state s).N ∩ (state s).E.get (state s).i) ((state s).E.get (state s).i) = ∅
  towerLength : ∀ s, (state s).R.length = s
  boundaryLength : ∀ s, (state s).E.length = (state 0).E.length+s
  retainedSlots : ∀ s (h : Fin (state s).E.length),
    (state (s+1)).E.get ⟨h.val, by have hs0 := boundaryLength s; have hs1 := boundaryLength (s+1); omega⟩ =
      geoStrictTransform (π s) ((state s).N ∩ (state s).E.get (state s).i)
        ((state s).E.get h)
  bornSlot : ∀ s, (state (s+1)).E.get (state (s+1)).i =
    (π s) ⁻¹' ((state s).N ∩ (state s).E.get (state s).i)

abbrev CartierQueryCountOutput {m k : ℕ} {X : CMfd.{u} m}
    (Q : MarkedIdeal m X) (beta : ℕ) (G : CartierGeometryFamily X) : Prop :=
  (∀ s,
    let S := Q.geoTransformAlong (G.state s).R
    let D := (G.state s).E.get (G.state s).i
    let C := (G.state s).N ∩ D
    S.N = (G.state s).N ∧ S.E = (G.state s).E ∧ S.d = Q.d ∧
    (IsGeoTestTower Q (G.state s).R ↔ s*Q.d≤beta) ∧
    (IsGeoTestTower Q (G.state s).R →
      IsInvDomain k S ∧ (S.IsAdmissibleCentre C ↔ Q.d≤beta-s*Q.d) ∧
      ∀ w∈C, divExpAlong m S.N S.ideal D w = beta-s*Q.d ∧
        (∀ e, IsDivNearAlong m S.N S.ideal D e w ↔ e≤beta-s*Q.d) ∧
        IsDivNearAlong m S.N S.ideal D (beta-s*Q.d) w ∧
        ¬ IsDivNearAlong m S.N S.ideal D (beta-s*Q.d+1) w ∧
        (∀ f, S.ideal.mem w f →
          ∃ g, (idealPow (vanishingIdeal (n:=m) C) (beta-s*Q.d)).mem w g ∧
            ∀ᶠ v in 𝓝 w, v∈S.N → f v=g v))) ∧
  (∀ s,
    let S := Q.geoTransformAlong (G.state s).R
    let S' := Q.geoTransformAlong (G.state (s+1)).R
    let C := (G.state s).N ∩ (G.state s).E.get (G.state s).i
    S' = S.geoTransform C (G.π s) ∧
    S'.ideal = colonAlong m (geoStrictTransform (G.π s) C S.N)
      (GermIdeal.pullback (G.π s) S.ideal)
      (idealPow (GermIdeal.pullback (G.π s) (vanishingIdeal (n:=m) C)) Q.d) ∧
    (IsGeoTestTower Q (G.state (s+1)).R →
      let F := idealPow (exceptionalDivisor (G.hπ s)).ideal Q.d
      let B := GermIdeal.pullback (m:=m) (G.π s) S.ideal
      RestrictLe S'.N B (F.mul S'.ideal) ∧ RestrictLe S'.N (F.mul S'.ideal) B)) ∧
  (let a := beta/Q.d
    let S := Q.geoTransformAlong (G.state a).R
    let C := (G.state a).N ∩ (G.state a).E.get (G.state a).i
    IsGeoTestTower Q (G.state a).R ∧ ¬ IsGeoTestTower Q (G.state (a+1)).R ∧
    (∃ w∈C, w∉S.cosupp) ∧
    ¬ IsDivNearAlong m S.N S.ideal ((G.state a).E.get (G.state a).i) Q.d (G.state a).z)

abbrev CartierOriginalHistoryCountOutput {n : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (I : GermIdeal n X) (d : ℕ) {Y : CMfd.{u} (n+1)}
    (T : BlowupTower (projectionAmbient X) Y)
    (beta : ℕ) (q : ℕ) (G : CartierGeometryFamily Y) : Prop :=
  let M : MarkedIdeal n X := ⟨M0.N,M0.E,I,d⟩
  ∀ s,
    let TS := T.append (G.state s).R
    let H := HironakaActualProjectionTowerHistory.projectionTowerHistory M0 TS
    let Q := (projectionTest M).geoTransformAlong TS
    HironakaActualMixedTestPowerNormalization.record M H = Q ∧
    (HironakaActualMixedTestPowerNormalization.IsTest M H ↔ s*M.d≤beta) ∧
    (IsGeoTestTower (projectionTest M) TS ↔ s*M.d≤beta) ∧
    Q.N = (G.state s).N ∧ Q.E = (G.state s).E ∧ Q.d = M.d ∧
    HironakaActualMixedTestPowerNormalization.projections H = 1 ∧
    HironakaActualMixedTestPowerNormalization.length H = q+s+1 ∧
    HironakaActualMixedTestPowerNormalization.baseMap H =
      (Prod.fst : projectionAmbient X → X) ∘ TS.proj ∧
    Q.E.length = M.E.length+1+q+s


private structure PureStep {m : ℕ} {X : CMfd.{u} m} (s : CartierGeometryState X) where
  Y : CMfd.{u} m
  π : Y → s.Y
  hπ : IsBlowupAlong m (s.N ∩ s.E.get s.i) π
  z : Y
  hN : IsClosedSubmanifold m (geoStrictTransform π (s.N ∩ s.E.get s.i) s.N)
  hE : IsSNCDivisor m (s.E.map (geoStrictTransform π (s.N ∩ s.E.get s.i)) ++
    [π ⁻¹' (s.N ∩ s.E.get s.i)])
  hT : IsTransverse m (geoStrictTransform π (s.N ∩ s.E.get s.i) s.N)
    (s.E.map (geoStrictTransform π (s.N ∩ s.E.get s.i)) ++ [π ⁻¹' (s.N ∩ s.E.get s.i)])
  hImage : π '' geoStrictTransform π (s.N ∩ s.E.get s.i) s.N = s.N
  hzN : z ∈ geoStrictTransform π (s.N ∩ s.E.get s.i) s.N
  hMap : π z = s.z
  hzD : z ∈ π ⁻¹' (s.N ∩ s.E.get s.i)
  hSeparated : geoStrictTransform π (s.N ∩ s.E.get s.i) s.N ∩
    geoStrictTransform π (s.N ∩ s.E.get s.i) (s.E.get s.i) = ∅

private def choosePureStep {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (s : CartierGeometryState X) : PureStep s := Classical.choice (by
  obtain ⟨Y,π,hπ,z,hN,hE,hT,hImage,hzN,hMap,hzD,hSep,_hLen,_hOld,_hBorn⟩ :=
    exists_pure_cartier_trace_successor hm s.N s.E s.hN s.hE s.hT s.i s.z s.hz
  exact ⟨⟨Y,π,hπ,z,hN,hE,hT,hImage,hzN,hMap,hzD,hSep⟩⟩)

private def nextPureState {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (s : CartierGeometryState X) : CartierGeometryState X :=
  let d := choosePureStep hm s
  { Y := d.Y
    R := .step s.R (s.N ∩ s.E.get s.i) d.π d.hπ
    N := geoStrictTransform d.π (s.N ∩ s.E.get s.i) s.N
    E := s.E.map (geoStrictTransform d.π (s.N ∩ s.E.get s.i)) ++ [d.π ⁻¹' (s.N ∩ s.E.get s.i)]
    i := ⟨s.E.length,by simp⟩
    z := d.z
    hN := d.hN
    hE := d.hE
    hT := d.hT
    hz := ⟨d.hzN,by simpa [List.get_eq_getElem] using d.hzD⟩ }

private def seedState {m : ℕ} {X : CMfd.{u} m}
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold m N)
    (hE : IsSNCDivisor m E) (hT : IsTransverse m N E)
    (i : Fin E.length) (z : X) (hz : z∈N∩E.get i) : CartierGeometryState X :=
  ⟨X,.refl,N,E,i,z,hN,hE,hT,hz⟩

private def pureStates {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (a : CartierGeometryState X) : ℕ → CartierGeometryState X :=
  Nat.rec a (fun _ s=>nextPureState hm s)

private theorem mapped_boundary_length {A B : Type*} (L : List A) (f : A→B) (P : B) :
    (L.map f++[P]).length=L.length+1 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simpa only [List.map_cons,List.cons_append,List.length_cons] using congrArg Nat.succ ih

private theorem next_boundary_length {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (s : CartierGeometryState X) : (nextPureState hm s).E.length=s.E.length+1 := by
  exact mapped_boundary_length s.E _ _

private theorem pure_lengths {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (a : CartierGeometryState X) (hR : a.R.length=0) (s : ℕ) :
    (pureStates hm a s).R.length=s ∧
      (pureStates hm a s).E.length=a.E.length+s := by
  induction s with
  | zero => exact ⟨hR,by simp [pureStates]⟩
  | succ s ih =>
    constructor
    · change (pureStates hm a s).R.length+1=s+1
      omega
    · change (nextPureState hm (pureStates hm a s)).E.length=a.E.length+(s+1)
      rw [next_boundary_length]
      omega

private theorem old_slot {A B : Type*} (L : List A) (f : A → B) (P : B)
    (i : Fin L.length) (h : i.val<(L.map f++[P]).length) :
    (L.map f++[P]).get ⟨i.val,h⟩=f (L.get i) := by
  simp [List.get_eq_getElem,i.isLt]

private theorem new_slot {A B : Type*} (L : List A) (f : A → B) (P : B)
    (h : L.length<(L.map f++[P]).length) :
    (L.map f++[P]).get ⟨L.length,h⟩=P := by
  simp [List.get_eq_getElem]

private def pureFamily {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold m N)
    (hE : IsSNCDivisor m E) (hT : IsTransverse m N E)
    (i : Fin E.length) (z : X) (hz : z∈N∩E.get i) : CartierGeometryFamily X :=
  let a := seedState N E hN hE hT i z hz
  let F := pureStates hm a
  { state := F
    zeroAmbient := rfl
    zeroTower := HEq.rfl
    π := fun s=>(choosePureStep hm (F s)).π
    hπ := fun s=>(choosePureStep hm (F s)).hπ
    stepTower := fun _=>rfl
    stepN := fun _=>rfl
    stepE := fun _=>rfl
    lastIndex := fun _=>rfl
    pointMap := fun s=>(choosePureStep hm (F s)).hMap
    carrierImage := fun s=>(choosePureStep hm (F s)).hImage
    separatedSlot := fun s=>(choosePureStep hm (F s)).hSeparated
    towerLength := fun s=>(pure_lengths hm a rfl s).1
    boundaryLength := fun s=>(pure_lengths hm a rfl s).2
    retainedSlots := by
      intro s h
      exact old_slot (F s).E _ _ h _
    bornSlot := by
      intro s
      exact new_slot (F s).E _ _ _ }


/-- Pure existence of the entire test-free family, including its literal
source seed. The recursive geometry is chosen without any queried record. -/
theorem exists_cartier_trace_geometry {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold m N)
    (hE : IsSNCDivisor m E) (hT : IsTransverse m N E)
    (i : Fin E.length) (z : X) (hz : z∈N∩E.get i) :
    ∃ G : CartierGeometryFamily X,
      HEq (G.state 0).N N ∧ HEq (G.state 0).E E ∧ HEq (G.state 0).i i ∧ HEq (G.state 0).z z := by
  exact ⟨pureFamily hm N E hN hE hT i z hz,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

private theorem query_geometry {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold m N)
    (hE : IsSNCDivisor m E) (hT : IsTransverse m N E)
    (i : Fin E.length) (z : X) (hz : z∈N∩E.get i)
    (Q : MarkedIdeal m X) (hQN : Q.N=N) (hQE : Q.E=E) (s : ℕ) :
    let G := pureFamily hm N E hN hE hT i z hz
    let S := Q.geoTransformAlong (G.state s).R
    S.N=(G.state s).N ∧ S.E=(G.state s).E ∧ S.d=Q.d := by
  induction s with
  | zero => exact ⟨hQN,hQE,rfl⟩
  | succ s ih =>
    let a := pureStates hm (seedState N E hN hE hT i z hz) s
    let d := choosePureStep hm a
    let C := a.N ∩ a.E.get a.i
    change geoStrictTransform d.π C (Q.geoTransformAlong a.R).N =
        geoStrictTransform d.π C a.N ∧
      (Q.geoTransformAlong a.R).E.map (geoStrictTransform d.π C) ++ [d.π ⁻¹' C] =
        a.E.map (geoStrictTransform d.π C) ++ [d.π ⁻¹' C] ∧
      (Q.geoTransformAlong a.R).d=Q.d
    exact ⟨congrArg (geoStrictTransform d.π C) ih.1,
      congrArg (fun B : List (Set a.Y)=>B.map (geoStrictTransform d.π C) ++ [d.π ⁻¹' C]) ih.2.1,
      ih.2.2⟩

private theorem centre_admissible_iff {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (s : CartierGeometryState X) (Q : MarkedIdeal m s.Y)
    (hQN : Q.N=s.N) (hQE : Q.E=s.E) (b : ℕ)
    (hCuts : ∀ w∈s.N∩s.E.get s.i,∀ e,
      IsDivNearAlong m Q.N Q.ideal (s.E.get s.i) e w ↔ e≤b) :
    Q.IsAdmissibleCentre (s.N∩s.E.get s.i) ↔ Q.d≤b := by
  constructor
  · intro hAdm
    have hDiv : IsDivNearAlong m Q.N Q.ideal (s.E.get s.i) Q.d s.z :=
      Eventually.of_forall fun y hyN hyD=>hAdm.2.1 ⟨hQN ▸ hyN,hyD⟩
    exact (hCuts s.z s.hz Q.d).mp hDiv
  · intro hBound
    have hC : IsClosedSubmanifold m (s.N∩s.E.get s.i) := by
      simpa only [memberInter_singleton] using
        isClosedSubmanifold_inter_memberInter hm s.hN.1 s.hE s.hT {s.i}
    have hNC : HasNormalCrossings m (s.N∩s.E.get s.i) Q.E := by
      rw [hQE]
      simpa only [memberInter_singleton] using hasNormalCrossings_inter_memberInter s.hT {s.i}
    refine ⟨hC,?_,hNC⟩
    intro w hw
    have hDiv := (hCuts w hw Q.d).mpr hBound
    exact hDiv.self_of_nhds (hQN.symm ▸ hw.1) hw.2

private theorem conditional_cuts {m k : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold m N)
    (hE : IsSNCDivisor m E) (hT : IsTransverse m N E)
    (i : Fin E.length) (z : X) (hz : z∈N∩E.get i)
    (Q : MarkedIdeal m X) (hQ : IsInvDomain k Q)
    (hQN : Q.N=N) (hQE : Q.E=E) (beta : ℕ)
    (hBeta : ∀ w∈N∩E.get i,∀ e,IsDivNearAlong m Q.N Q.ideal (E.get i) e w ↔ e≤beta)
    (s : ℕ) :
    let G := pureFamily hm N E hN hE hT i z hz
    let S := Q.geoTransformAlong (G.state s).R
    (IsGeoTestTower Q (G.state s).R ↔ s*Q.d≤beta) ∧
    (IsGeoTestTower Q (G.state s).R →
      ∀ w∈(G.state s).N∩(G.state s).E.get (G.state s).i,∀ e,
        IsDivNearAlong m S.N S.ideal ((G.state s).E.get (G.state s).i) e w ↔
          e≤beta-s*Q.d) := by
  let G := pureFamily hm N E hN hE hT i z hz
  change (IsGeoTestTower Q (G.state s).R ↔ s*Q.d≤beta) ∧ _
  induction s with
  | zero =>
    refine ⟨by simp [G,pureFamily,pureStates,seedState,IsGeoTestTower],?_⟩
    intro _ht
    simp only [Nat.zero_mul,Nat.sub_zero]
    change ∀ w∈N∩E.get i,∀ e,IsDivNearAlong m Q.N Q.ideal (E.get i) e w ↔ e≤beta
    exact hBeta
  | succ s ih =>
    let a := G.state s
    let C := a.N∩a.E.get a.i
    let S := Q.geoTransformAlong a.R
    let d := choosePureStep hm a
    have hGeom : S.N=a.N ∧ S.E=a.E ∧ S.d=Q.d :=
      query_geometry hm N E hN hE hT i z hz Q hQN hQE s
    have hAdm (ht : IsGeoTestTower Q a.R) : S.IsAdmissibleCentre C ↔ S.d≤beta-s*Q.d :=
      centre_admissible_iff hm a S hGeom.1 hGeom.2.1 (beta-s*Q.d) (ih.2 ht)
    have hTest : IsGeoTestTower Q (G.state (s+1)).R ↔ (s+1)*Q.d≤beta := by
      change (IsGeoTestTower Q a.R ∧ S.IsAdmissibleCentre C) ↔ _
      constructor
      · rintro ⟨ht,hc⟩
        have hPre := ih.1.mp ht
        have hb := (hAdm ht).mp hc
        rw [hGeom.2.2] at hb
        rw [Nat.add_mul,Nat.one_mul]
        omega
      · intro hb
        have hb' := hb
        rw [Nat.add_mul,Nat.one_mul] at hb'
        have ht := ih.1.mpr (show s*Q.d≤beta by omega)
        refine ⟨ht,(hAdm ht).mpr ?_⟩
        rw [hGeom.2.2]
        omega
    refine ⟨hTest,?_⟩
    intro ht w hw e
    have hTestPair : IsGeoTestTower Q a.R ∧ S.IsAdmissibleCentre C := ht
    have hDom := isInvDomain_geoTransformAlong hQ a.R hTestPair.1
    have hGeomNext := query_geometry hm N E hN hE hT i z hz Q hQN hQE (s+1)
    have hNextBound := hTest.mp ht
    rw [Nat.add_mul,Nat.one_mul] at hNextBound
    have hwN : w∈(S.geoTransform C d.π).N := hGeomNext.1.symm ▸ hw.1
    have hwC : d.π w∈C := by
      have hwD := hw.2
      change w∈(a.E.map (geoStrictTransform d.π C)++[d.π ⁻¹' C]).get
        ⟨a.E.length,_⟩ at hwD
      have hh : w∈d.π ⁻¹' C := by simpa [List.get_eq_getElem] using hwD
      exact hh
    have hBorn := controlled_born_divisibility S hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent hTestPair.2 d.hπ hwN hwC e
    have hCentre : C=S.N∩a.E.get a.i := by rw [hGeom.1]
    have hSource := ih.2 hTestPair.1 (d.π w) hwC (S.d+e)
    have hTransport := isDivNearAlong_inter_carrier_iff S.N (a.E.get a.i) S.ideal (S.d+e) (d.π w)
    change IsDivNearAlong m (S.geoTransform C d.π).N (S.geoTransform C d.π).ideal
      ((a.E.map (geoStrictTransform d.π C)++[d.π ⁻¹' C]).get ⟨a.E.length,_⟩) e w ↔ _
    have hLast : (a.E.map (geoStrictTransform d.π C)++[d.π ⁻¹' C]).get
        ⟨a.E.length,by simp⟩ = d.π ⁻¹' C := by simp [List.get_eq_getElem]
    rw [hLast,hBorn,hCentre,hTransport,hSource,hGeom.2.2]
    rw [Nat.add_mul,Nat.one_mul]
    omega

private theorem exponent_of_all_cuts {m : ℕ} {X : CMfd.{u} m}
    (N D : Set X) (I : GermIdeal m X) (w : X) (b : ℕ)
    (hCuts : ∀ e,IsDivNearAlong m N I D e w ↔ e≤b) :
    divExpAlong m N I D w=b := by
  have hGood := (hCuts b).mpr le_rfl
  have hBad : ¬ IsDivNearAlong m N I D (b+1) w :=
    fun h=>Nat.not_succ_le_self b ((hCuts (b+1)).mp h)
  have hExists : ∃ e,¬IsDivNearAlong m N I D (e+1) w := ⟨b,hBad⟩
  unfold divExpAlong
  rw [dif_pos hExists]
  apply Nat.le_antisymm (Nat.find_min' hExists hBad)
  by_contra h
  exact Nat.find_spec hExists (DivisorExponentAlong.IsDivNearAlong.mono hGood (by omega))

private theorem query_counts {m k : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold m N)
    (hE : IsSNCDivisor m E) (hT : IsTransverse m N E)
    (i : Fin E.length) (z : X) (hz : z∈N∩E.get i)
    (Q : MarkedIdeal m X) (hQ : IsInvDomain k Q)
    (hQN : Q.N=N) (hQE : Q.E=E) (beta : ℕ)
    (hBeta : ∀ w∈N∩E.get i,∀ e,IsDivNearAlong m Q.N Q.ideal (E.get i) e w ↔ e≤beta) :
    CartierQueryCountOutput (k:=k) Q beta (pureFamily hm N E hN hE hT i z hz) := by
  let G := pureFamily hm N E hN hE hT i z hz
  have hGeom (s : ℕ) := query_geometry hm N E hN hE hT i z hz Q hQN hQE s
  have hInv (s : ℕ) := conditional_cuts hm N E hN hE hT i z hz Q hQ hQN hQE beta hBeta s
  change CartierQueryCountOutput (k:=k) Q beta G
  refine ⟨?_,?_,?_⟩
  · intro s
    let a := G.state s
    let S := Q.geoTransformAlong a.R
    let D := a.E.get a.i
    let C := a.N∩D
    refine ⟨(hGeom s).1,(hGeom s).2.1,(hGeom s).2.2,(hInv s).1,?_⟩
    intro ht
    have hDom : IsInvDomain k S := isInvDomain_geoTransformAlong hQ a.R ht
    have hCuts := (hInv s).2 ht
    have hAdm := centre_admissible_iff hm a S (hGeom s).1 (hGeom s).2.1 (beta-s*Q.d) hCuts
    rw [(hGeom s).2.2] at hAdm
    refine ⟨hDom,hAdm,?_⟩
    intro w hw
    let b := beta-s*Q.d
    have hCut := hCuts w hw
    have hGood := (hCut b).mpr le_rfl
    have hBad : ¬ IsDivNearAlong m S.N S.ideal D (b+1) w :=
      fun h=>Nat.not_succ_le_self b ((hCut (b+1)).mp h)
    refine ⟨exponent_of_all_cuts S.N D S.ideal w b hCut,hCut,hGood,hBad,?_⟩
    intro f hf
    obtain ⟨rN,hrN⟩ := hDom.isWellFormed.isClosedSubmanifold_N.2 w ((hGeom s).1.symm ▸ hw.1)
    obtain ⟨r,hr⟩ := exists_isLocalRetraction hrN
    have hClosedC : IsClosedSubmanifold m C := by
      simpa only [memberInter_singleton] using
        isClosedSubmanifold_inter_memberInter hm a.hN.1 a.hE a.hT {a.i}
    obtain ⟨rC,hrC⟩ := hClosedC.2 w hw
    have hrC' : RegularAtDim (n:=m) (S.N∩D) w rC := by
      rw [(hGeom s).1]
      exact hrC
    obtain ⟨g,hg,hEq⟩ := (isDivNearAlong_iff hDom.isWellFormed.isCoherent hr hrC').mp hGood f hf
    refine ⟨g,?_,hEq⟩
    rw [(hGeom s).1] at hg
    exact hg
  · intro s
    let a := G.state s
    let S := Q.geoTransformAlong a.R
    let C := a.N∩a.E.get a.i
    let d := choosePureStep hm a
    change S.geoTransform C d.π = S.geoTransform C d.π ∧ _
    refine ⟨rfl,?_,?_⟩
    · change (S.geoTransform C d.π).ideal = colonAlong m (geoStrictTransform d.π C S.N)
        (GermIdeal.pullback d.π S.ideal)
        (idealPow (GermIdeal.pullback d.π (vanishingIdeal (n:=m) C)) Q.d)
      rw [geoTransform_ideal,(hGeom s).2.2]
    · intro ht
      have hPair : IsGeoTestTower Q a.R ∧ S.IsAdmissibleCentre C := ht
      have hDom := isInvDomain_geoTransformAlong hQ a.R hPair.1
      have hFactor := MarkedIdealOperationsAlong.MarkedIdeal.restrictLe_pullback_geoTransform
        hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent hPair.2 d.hπ
      rw [←exceptionalDivisor_ideal d.hπ,(hGeom s).2.2] at hFactor
      exact hFactor
  · let a := beta/Q.d
    let A := G.state a
    let S := Q.geoTransformAlong A.R
    let D := A.E.get A.i
    let C := A.N∩D
    have hPos : 0<Q.d := by have hd:=hQ.one_le_d;omega
    have hLow : a*Q.d≤beta := Nat.div_mul_le_self beta Q.d
    have hHigh : beta<(a+1)*Q.d := by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ beta hPos
    have ht : IsGeoTestTower Q A.R := (hInv a).1.mpr hLow
    have hNot : ¬ IsGeoTestTower Q (G.state (a+1)).R :=
      fun h=>Nat.not_le_of_lt hHigh ((hInv (a+1)).1.mp h)
    have hSmall : beta-a*Q.d<Q.d := by
      rw [Nat.add_mul,Nat.one_mul] at hHigh
      omega
    have hBad : ¬ IsDivNearAlong m S.N S.ideal D Q.d A.z :=
      fun h=>Nat.not_le_of_lt hSmall (((hInv a).2 ht A.z A.hz Q.d).mp h)
    refine ⟨ht,hNot,?_,hBad⟩
    by_contra hn
    push Not at hn
    apply hBad
    exact Eventually.of_forall fun w hwN hwD=>by
      have hw : w∈S.cosupp := hn w ⟨(hGeom a).1 ▸ hwN,hwD⟩
      change w∈cosupport m S.N S.ideal S.d at hw
      rw [(hGeom a).2.2] at hw
      exact hw

/-- Choose the pure native Cartier family BEFORE every queried ideal/mark.
The auxiliary whole-trace hypothesis is consumed by the genuine conditional
count proof; the ordinary two-record theorem derives it internally. -/
theorem exists_cartier_trace_test_counts {m : ℕ} {X : CMfd.{u} m} (hm : 0<m)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold m N)
    (hE : IsSNCDivisor m E) (hT : IsTransverse m N E)
    (i : Fin E.length) (z : X) (hz : z∈N∩E.get i) :
    ∃ G : CartierGeometryFamily X,
      HEq (G.state 0).N N ∧ HEq (G.state 0).E E ∧ HEq (G.state 0).i i ∧ HEq (G.state 0).z z ∧
      ∀ (Q : MarkedIdeal m X) (k : ℕ) (_hQ : IsInvDomain k Q)
        (_hQN : Q.N=N) (_hQE : Q.E=E) (beta : ℕ),
        (∀ w∈N∩E.get i,∀ e,IsDivNearAlong m Q.N Q.ideal (E.get i) e w ↔ e≤beta) →
        CartierQueryCountOutput (k:=k) Q beta G := by
  exact ⟨pureFamily hm N E hN hE hT i z hz,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,
    fun Q k hQ hQN hQE beta hBeta=>query_counts hm N E hN hE hT i z hz Q hQ hQN hQE beta hBeta⟩


/- PRIVATE copies of the accepted complete P08 descriptors. These preserve
whole inherited source fields and are not calls to private mother names. -/
private abbrev recordMark {a : ℕ} (X : CMfd.{u} a) (Q : MarkedIdeal a X) : ℕ :=
  @MarkedIdeal.d a X.carrier X.topologicalSpace X.chartedSpace Q

private abbrev recordBoundary {a : ℕ} (X : CMfd.{u} a) (Q : MarkedIdeal a X) : List (Set X) :=
  @MarkedIdeal.E a X.carrier X.topologicalSpace X.chartedSpace Q

private abbrev wholeTailCuts {n : ℕ} {X : CMfd.{u} n}
    {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    {Z : CMfd.{u} (n+1)} (N : Set X) (Nt : Set Z) (x : X) (z : Z)
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z) : Prop :=
  let κ : Z→X := (Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj
  let B : GermIdeal n X→GermIdeal (n+1) Z:=fun I=>
    GermIdeal.pullback (m:=n+1) R.proj (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I))
  κ z=x ∧ z∈Nt ∧ ∀(I : GermIdeal n X),I.IsCoherent→
    B I=GermIdeal.pullback (m:=n+1) κ I ∧ (B I).IsCoherent ∧
    ∀a : ℕ,(z∈cosupport (n+1) Nt (B I) ((R.length+2)*a) ↔ x∈cosupport n N I a) ∧
      ∀b : ℕ,b≤R.length+1→
        (z∈cosupport (n+1) Nt (B I) ((R.length+2)*a+b+1) ↔
          x∈cosupport n N I (a+1))

private abbrev controlledTailOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1))) (z : Z) : Prop :=
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let P:=projectionTest M
  let Q1:=P.geoTransform C π1
  let A : BlowupTower (CMfd.of (projectionAmbient X)) Y1:=
    .step .refl C π1 (isBlowupAlong_blowupProj (n:=n+1) (C:=C)
      (projection_point_centre M hM x hx).2)
  let T:=A.append R
  let Q:=Q1.geoTransformAlong R
  let B:=GermIdeal.pullback (m:=n+1) R.proj
    (GermIdeal.pullback (m:=n+1) π1
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal))
  let F:=idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let q:=R.length+1
  let ν:=q*M.d
  let μ:=(q+1)*ρ
  let s:=ρ+q*(ρ-M.d)
  IsGeoTestTower P T ∧ Q=P.geoTransformAlong T ∧ IsInvDomain (k+1) Q ∧
  Q.d=M.d ∧ Q.E.length=M.E.length+2+R.length ∧
  B=GermIdeal.pullback (m:=n+1) T.proj P.ideal ∧
  RestrictLe Q.N B (F.mul Q.ideal) ∧ RestrictLe Q.N (F.mul Q.ideal) B ∧
  (∀g : Z→ℂ,F.mem z g↔IsInSpanAt (n:=n+1)
    (·=fun v=>e v (Fin.last n)^ν) z g) ∧
  z∈cosupport (n+1) Q.N F ν ∧ z∉cosupport (n+1) Q.N F (ν+1) ∧
  GermIdealOrder.order (n+1) Q.N F z=(ν : ℕ∞) ∧
  ν+s=μ ∧
  z∈cosupport (n+1) Q.N Q.ideal s ∧
  z∉cosupport (n+1) Q.N Q.ideal (s+1) ∧
  ordinaryTraceOrder Q.N Q.ideal z=s ∧
  GermIdealOrder.order (n+1) Q.N Q.ideal z=(s : ℕ∞) ∧
  M.d≤s ∧ z∈Q.cosupp ∧ Q.IsAdmissibleCentre ({z} : Set Z)



private def oldMask {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter fun i=>i.castAdd 1∈S

private abbrev wholeCutsOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  let p : projectionAmbient X := (x,0)
  let C : Set (projectionAmbient X) := {p}
  let _ : Fact (IsClosedSubmanifold (n+1) C) := ⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X := blowupProj (n+1) C
  let Q : MarkedIdeal (n+1) Y := (projectionTest M).geoTransform C π
  let z := c.invFun 0
  Φ.source⊆(chartAt (ComplexModel n) x).target ∧ Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
  c.y₀=p ∧ c.k=0 ∧ c.j=Fin.last n ∧
  (∀(y : projectionAmbient X)(i : Fin n),flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1) ∧
  (∀y : projectionAmbient X,flatCoord c.Φ (Fin.last n) y=y.2 0) ∧
  (∀y∈flatDomain c.Φ,y∈(projectionTest M).N ↔
    c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace SN) ∧
  (∀i,x∈M.E.get i→∀y∈flatDomain c.Φ,y∈(Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i ↔
    c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace (SE i)) ∧
  Fin.last n∉SN ∧ (∀i,Fin.last n∉SE i) ∧ (0 : ComplexModel (n+1))∈c.target ∧
  z∈c.source ∧ π z=p ∧ c.toFun z=0 ∧ IsBlowupAlong (n+1) C π ∧
  c.homeo∈atlas (ComplexModel (n+1)) Y ∧ IsInvDomain (k+1) Q ∧ z∈Q.cosupp ∧
  recordMark Y Q=M.d ∧
  recordBoundary Y Q=M.E.map (fun H=>geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' H))++
    [geoStrictTransform π C (horizontal X),π ⁻¹' C] ∧
  (recordBoundary Y Q).length=M.E.length+2 ∧
  IsOpen U ∧ z∈U ∧ U⊆c.source ∧
  (∀v∈U,v∈Q.N↔c.toFun v∈coordSubspace SN) ∧
  (∀i,(x∈M.E.get i→∀v∈U,v∈geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i)↔
      c.toFun v∈coordSubspace (SE i)) ∧
    (x∉M.E.get i→∀v∈U,v∉geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i))) ∧
  (∀v∈U,v∉geoStrictTransform π C (horizontal X)) ∧
  (∀v∈U,v∈π ⁻¹' C↔c.toFun v (Fin.last n)=0) ∧

  Φs.toFun=Φ.toFun ∧ Φs.invFun=Φ.invFun ∧
  Φs.source⊆Φ.source ∧ Φs.target⊆Φ.target ∧
  Φs.source⊆(chartAt (ComplexModel n) x).target ∧
  Φs.toFun (chartAt (ComplexModel n) x x)=0 ∧
  flatDomain Φs=flatDomain Φ∩(fun y : X=>((y,0) : projectionAmbient X)) ⁻¹' flatDomain c.Φ ∧
  (∀y∈flatDomain Φs,y∈M.N↔flatMap Φs y∈coordSubspace (oldMask SN)) ∧

  ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (_hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (_hz : z∈e.source) (_he0 : e z=0),
    wholeTailCuts M.N (Q.geoTransformAlong R).N x z R

private abbrev projectionQueriesOutput {n : ℕ} {X : CMfd.{u} n}
    (N : Set X) (x : X) : Prop :=
  let p : projectionAmbient X:=(x,0)
  let hf:=ProductComplexManifold.contMDiff_fst
    (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
  let τ:=actualHolomorphicGermPullback hf p
  (∀I : GermIdeal n X,I.IsCoherent→
    Ideal.map τ.toRingHom (wholeChartStalkIdeal I x x (mem_chart_source _ x))=
      wholeChartStalkIdeal (GermIdeal.pullback (m:=n+1)
        (Prod.fst : projectionAmbient X→X) I) p p (mem_chart_source _ p) ∧
    (∀b : ℕ,p∈cosupport (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I) b ↔
        x∈cosupport n N I b) ∧
    GermIdealOrder.order (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I) p=
        GermIdealOrder.order n N I x) ∧
  (∀(f : X→ℂ) (hf0 : HolomorphicAt n f x),
    τ (chartTranslatedGerm x x (mem_chart_source _ x) f hf0)=
      chartTranslatedGerm p p (mem_chart_source _ p) (f∘Prod.fst)
        (hf0.comp_contMDiff (Eventually.of_forall fun _=>hf.contMDiffAt))) ∧
  ∀(c : ℂ) (a : HolGerm (ComplexModel n)),τ (c • a)=c • τ a

private abbrev NativeTailState {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    (Q1 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))) : Type (u+1) :=
  Σ Z : CMfd.{u} (n+1), Σ R : BlowupTower Y1 Z,
    Σ e : OpenPartialHomeomorph Z (ComplexModel (n+1)),
      {z : Z // AnchoredInheritedLastChartChain a R e ∧
        IsGeoTestTower Q1 R ∧ z∈e.source ∧ e z=0}

private abbrev tailPoint {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    {Q1 : MarkedIdeal (n+1) Y1}
    {a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))}
    (s : NativeTailState Q1 a) : s.1 := s.2.2.2.val

private abbrev initialQueryOutput {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X) (I : GermIdeal n X) (d : ℕ)
    (_hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (_hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let P:=projectionTest M
  let p : projectionAmbient X:=(x,0)
  let ρ:=ordinaryTraceOrder M.N I x
  let H:=HironakaActualProjectionTowerHistory.projectionTowerHistory M0
    (BlowupTower.refl : BlowupTower (projectionAmbient X) (projectionAmbient X))
  projectionQueriesOutput M0.N x ∧ IsInvDomain (k+1) P ∧ p∈P.cosupp ∧
  P.N=(Prod.fst : projectionAmbient X→X) ⁻¹' M0.N ∧
  P.ideal=GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I ∧
  P.d=d ∧ P.E=M0.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·)++[horizontal X] ∧
  P.E.length=M0.E.length+1 ∧ d≤ρ ∧
  GermIdealOrder.order n M.N I x=(ρ : ℕ∞) ∧
  ordinaryTraceOrder P.N P.ideal p=ρ ∧ GermIdealOrder.order (n+1) P.N P.ideal p=(ρ : ℕ∞) ∧
  P.IsAdmissibleCentre ({p} : Set (projectionAmbient X)) ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H ∧
  HironakaActualMixedTestPowerNormalization.record M H=P ∧
  HironakaActualMixedTestPowerNormalization.length H=1 ∧
  HironakaActualMixedTestPowerNormalization.projections H=1 ∧
  HironakaActualMixedTestPowerNormalization.baseMap H=(Prod.fst : projectionAmbient X→X)

private abbrev queryAtState {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState
      (Y1:=CMfd.of (n:=n+1) (BlowupSpace (n+1)
        ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let Z:=s.1
  let R:=s.2.1
  let e:=s.2.2.1
  let z:=tailPoint s
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let T:=A.append R
  let Q:=((projectionTest M).geoTransform C π1).geoTransformAlong R
  let Q0:=((projectionTest M0).geoTransform C π1).geoTransformAlong R
  let H:=HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T
  let V:=e.source∩R.proj ⁻¹' (U∩c.source)
  let B:=GermIdeal.pullback (m:=n+1) R.proj
    (GermIdeal.pullback (m:=n+1) π1
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I))
  let ρ:=ordinaryTraceOrder M.N I x
  let q:=R.length+1
  IsGeoTestTower ((projectionTest M).geoTransform C π1) R ∧
  wholeTailCuts M0.N Q.N x z R ∧
  ordinaryTraceOrder Q.N B z=(q+1)*ρ ∧
  GermIdealOrder.order (n+1) Q.N B z=(((q+1)*ρ : ℕ) : ℕ∞) ∧
  controlledTailOutput M hM x hx R e z ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H ∧
  HironakaActualMixedTestPowerNormalization.record M H=Q ∧
  Q.N=Q0.N ∧ Q.E=Q0.E ∧
  HironakaActualMixedTestPowerNormalization.baseMap H=
    (Prod.fst : projectionAmbient X→X)∘T.proj ∧
  HironakaActualMixedTestPowerNormalization.baseMap H z=x ∧
  HironakaActualMixedTestPowerNormalization.length H=q+1 ∧
  HironakaActualMixedTestPowerNormalization.projections H=1 ∧
  T.length=q ∧ Q.d=d ∧ Q.E.length=M0.E.length+1+q ∧
  (ρ=d→ ordinaryTraceOrder Q.N Q.ideal z=d) ∧
  IsOpen V ∧ z∈V ∧
  Q.E.map (fun K=>V∩K)=
    List.ofFn (fun i : Fin M0.E.length=>
      {v : Z | v∈V ∧ x∈M0.E.get i ∧ e v∈coordSubspace (SE i)}) ++
      [(∅ : Set Z)] ++ List.replicate R.length (∅ : Set Z) ++
      [V∩{v | e v (Fin.last n)=0}]

private abbrev sameNextGeometry {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    (Q0 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1)))
    (s t : NativeTailState Q0 a) : Prop :=
  ∃ (c2 : FlatChart (n+1) ({tailPoint s} : Set s.1))
    (hπ2 : IsBlowupAlong (n+1) ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1))),
    c2.y₀=tailPoint s ∧ c2.k=0 ∧ c2.j=Fin.last n ∧
    c2.invFun 0∈c2.source ∧ c2.toFun (c2.invFun 0)=0 ∧
    blowupProj (n+1) ({tailPoint s} : Set s.1) (c2.invFun 0)=tailPoint s ∧
    (∀v∈c2.source,
      blowupProj (n+1) ({tailPoint s} : Set s.1) v∈s.2.2.1.source ∧
      s.2.2.1 (blowupProj (n+1) ({tailPoint s} : Set s.1) v)=
        monomial 0 (Fin.last n) (c2.toFun v)) ∧
    HEq t.1 (CMfd.of (n:=n+1) (BlowupSpace (n+1) ({tailPoint s} : Set s.1))) ∧
    HEq t.2.1 (BlowupTower.step
      (Z:=CMfd.of (n:=n+1) (BlowupSpace (n+1) ({tailPoint s} : Set s.1)))
      s.2.1 ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1)) hπ2) ∧
    HEq t.2.2.1 c2.homeo ∧ HEq (tailPoint t) (c2.invFun 0)
private abbrev bornAtState {n : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 (blowupProj (n+1) C0) hπ1
  let T:=A.append s.2.1
  let Q:=(projectionTest M).geoTransformAlong T
  let Q0:=(projectionTest M0).geoTransformAlong T
  let D : Set s.1:=Q0.E.getLastD ∅
  let C : Set s.1:=Q0.N∩D
  let β:=(s.2.1.length+1)*(ordinaryTraceOrder M.N I x-d)
  Q.N=Q0.N ∧ Q.E=Q0.E ∧ tailPoint s∈D ∧ C.Nonempty ∧
  IsClosedSubmanifold (n+1) C ∧ HasNormalCrossings (n+1) C Q0.E ∧
  (∀y∈C, divExpAlong (n+1) Q.N Q.ideal D y=β ∧
    (∀e : ℕ,IsDivNearAlong (n+1) Q.N Q.ideal D e y ↔ e≤β) ∧
    IsDivNearAlong (n+1) Q.N Q.ideal D β y ∧
    ¬IsDivNearAlong (n+1) Q.N Q.ideal D (β+1) y ∧
    ∀f : s.1→ℂ,Q.ideal.mem y f→
      ∃g,(idealPow (vanishingIdeal (n:=n+1) C) β).mem y g ∧
        ∀ᶠz in 𝓝 y,z∈Q.N→f z=g z) ∧
  (Q.IsAdmissibleCentre C ↔ d≤β)

private abbrev queryWithBornAtState {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp) : Prop :=
  queryAtState M0 x hπ1 c SE U s I d hM hx ∧ bornAtState M0 x hπ1 c s I d

private abbrev sharedBornFamilyOutput {n k0 : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (hM0 : IsInvDomain k0 M0) (x : X) (hx0 : x∈M0.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M0 hM0 x hx0 Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M0).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M0 hM0 x hx0).2
  ∃ h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
    IsGeoTestTower Q0 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0,
  ∃ Next : NativeTailState Q0 a→NativeTailState Q0 a,
    (∀s,sameNextGeometry Q0 a s (Next s)) ∧
    let s0 : NativeTailState Q0 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
    let F : ℕ→NativeTailState Q0 a:=Nat.rec s0 (fun _ s=>Next s)
    F 0=s0 ∧ (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=Next (F r)) ∧
    ∀ (I : GermIdeal n X) (d k : ℕ)
      (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
      (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp),
      initialQueryOutput M0 x I d hM hx ∧
      ∀r : ℕ,queryWithBornAtState M0 x hπ1 c SE U (F r) I d hM hx




private abbrev p08TwoRecordOutput {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 : MarkedIdeal n X) (hM1 : IsInvDomain k1 M1) (x : X) (hx1 : x∈M1.cosupp)
    (M2 : MarkedIdeal n X) (hM2 : IsInvDomain k2 M2) (hx2 : x∈M2.cosupp)
    (h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M1.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M1 hM1 x hx1 Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M1).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M1 hM1 x hx1).2
  ∃ h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
    IsGeoTestTower Q0 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0,
  ∃ Next : NativeTailState Q0 a→NativeTailState Q0 a,
    (∀s,sameNextGeometry Q0 a s (Next s)) ∧
    let s0 : NativeTailState Q0 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
    let F : ℕ→NativeTailState Q0 a:=Nat.rec s0 (fun _ s=>Next s)
    F 0=s0 ∧ (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=Next (F r)) ∧
    initialQueryOutput M1 x M1.ideal M1.d hM1 hx1 ∧
    initialQueryOutput M1 x M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2) ∧
    ∀r : ℕ,
      queryWithBornAtState M1 x hπ1 c SE U (F r) M1.ideal M1.d hM1 hx1 ∧
      queryWithBornAtState M1 x hπ1 c SE U (F r) M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2)




private abbrev currentQuery {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 (blowupProj (n+1) C0) hπ1
  let T:=A.append s.2.1
  let Q:=(projectionTest M).geoTransformAlong T
  let ρ:=ordinaryTraceOrder M.N I x
  let q:=s.2.1.length+1
  IsGeoTestTower (projectionTest M) T ∧ IsInvDomain (k+1) Q ∧
  Q.d=d ∧ tailPoint s∈Q.cosupp ∧
  ordinaryTraceOrder Q.N Q.ideal (tailPoint s)=ρ+q*(ρ-d)

private theorem current_dictionary {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp)
    (hQuery : queryAtState M0 x hπ1 c SE U s I d hM hx) :
    currentQuery (k:=k) M0 x hπ1 c s I d := by
  have hCtl:=hQuery.2.2.2.2.1
  rcases hCtl with ⟨hT,hRecord,hDom,hMark,_hELen,_hB,_hLeft,_hRight,
    _hSpan,_hFGood,_hFBad,_hFOrd,_hSum,_hGood,_hBad,hNat,_hOrd,_hd,hCos,_hAdmiss⟩
  dsimp only [currentQuery]
  rw [←hRecord]
  exact ⟨hT,hDom,hMark,hCos,hNat⟩


private theorem literal_last_index {A : Type*} (L : List A) (a : A) (h : L≠[]) :
    ∃ i : Fin L.length,i.val+1=L.length ∧ L.get i=L.getLastD a := by
  induction L with
  | nil => exact False.elim (h rfl)
  | cons b L ih =>
    cases L with
    | nil => exact ⟨⟨0,by simp⟩,rfl,rfl⟩
    | cons c L =>
      obtain ⟨i,hi,hget⟩ := ih (by simp)
      refine ⟨⟨i.val+1,by simpa using Nat.succ_lt_succ i.isLt⟩,?_,?_⟩
      · simpa only [List.length_cons,Nat.add_assoc] using congrArg Nat.succ hi
      · change (c::L).get i=(c::L).getLastD a
        exact hget

private theorem original_history_counts {n : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (I : GermIdeal n X) (d : ℕ)
    {Y : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Y)
    (hT : IsGeoTestTower (projectionTest (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X)) T)
    (q : ℕ) (hLen : T.length=q) (G : CartierGeometryFamily Y) (beta : ℕ) (k : ℕ)
    (hCounts : CartierQueryCountOutput (k:=k)
      ((projectionTest (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X)).geoTransformAlong T) beta G) :
    CartierOriginalHistoryCountOutput M0 I d T beta q G := by
  let M : MarkedIdeal n X := ⟨M0.N,M0.E,I,d⟩
  intro s
  let TS := T.append (G.state s).R
  have hNative : IsGeoTestTower (projectionTest M) TS ↔ s*M.d≤beta := by
    rw [isGeoTestTower_append_iff]
    have hh := (hCounts.1 s).2.2.2.1
    have hc : IsGeoTestTower ((projectionTest M).geoTransformAlong T) (G.state s).R ↔ s*M.d≤beta := by
      change (IsGeoTestTower ((projectionTest M).geoTransformAlong T) (G.state s).R ↔
        s*((projectionTest M).geoTransformAlong T).d≤beta) at hh
      have hMark : ((projectionTest M).geoTransformAlong T).d=M.d :=
        d_geoTransformAlong (projectionTest M) T
      rw [hMark] at hh
      exact hh
    exact ⟨fun h=>hc.mp h.2,fun h=>⟨hT,hc.mpr h⟩⟩
  have hRecord := HironakaActualSharedRecursivePointTests.shared_projection_history_record M0 I d TS
  have hTest := HironakaActualSharedRecursivePointTests.shared_projection_history_test_iff M0 I d TS
  have hDict := HironakaActualProjectionTowerHistory.projectionTowerHistory_dictionary M0 TS
  have hQueryDict := HironakaActualProjectionTowerHistory.projectionTowerHistory_dictionary M TS
  refine ⟨hRecord,hTest.trans hNative,hNative,?_,?_,?_,hDict.2.1,?_,hDict.2.2.1,?_⟩
  · simpa only [geoTransformAlong_append] using (hCounts.1 s).1
  · simpa only [geoTransformAlong_append] using (hCounts.1 s).2.1
  · exact d_geoTransformAlong (projectionTest M) TS
  · have hh := hDict.1
    rw [BlowupTower.length_append,hLen,G.towerLength] at hh
    omega
  · change ((projectionTest M).geoTransformAlong TS).E.length=M.E.length+1+q+s
    calc
      _ = M.E.length+1+TS.length := hQueryDict.2.2.2
      _ = M.E.length+1+q+s := by
        rw [BlowupTower.length_append,hLen,G.towerLength]
        omega

private abbrev cartierAtState {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 M2 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M1).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo) : Prop :=
  let C0 : Set (projectionAmbient X) := {(x,0)}
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1 := .step .refl C0 (blowupProj (n+1) C0) hπ1
  let T := A.append s.2.1
  let Q1 := (projectionTest M1).geoTransformAlong T
  let Q2 := (projectionTest M2).geoTransformAlong T
  let beta1 := (s.2.1.length+1)*(ordinaryTraceOrder M1.N M1.ideal x-M1.d)
  let beta2 := (s.2.1.length+1)*(ordinaryTraceOrder M1.N M2.ideal x-M2.d)
  ∃ G : CartierGeometryFamily s.1,
    HEq (G.state 0).N Q1.N ∧ HEq (G.state 0).E Q1.E ∧
    ((G.state 0).i).val+1=(G.state 0).E.length ∧ HEq (G.state 0).z (tailPoint s) ∧
    CartierQueryCountOutput (k:=k1+1) Q1 beta1 G ∧
    CartierQueryCountOutput (k:=k2+1) Q2 beta2 G ∧
    CartierOriginalHistoryCountOutput M1 M1.ideal M1.d T beta1 (s.2.1.length+1) G ∧
    CartierOriginalHistoryCountOutput M1 M2.ideal M2.d T beta2 (s.2.1.length+1) G

private theorem cartier_at_state {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 M2 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M1.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M1).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (hM1 : IsInvDomain k1 M1) (hx1 : x∈M1.cosupp)
    (hM2 : IsInvDomain k2 M2) (hx2 : x∈M2.cosupp)
    (h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2)
    (hQuery1 : queryWithBornAtState M1 x hπ1 c SE U s M1.ideal M1.d hM1 hx1)
    (hQuery2 : queryWithBornAtState M1 x hπ1 c SE U s M2.ideal M2.d
      (h2.symm ▸ hM2) (h2.symm ▸ hx2)) :
    cartierAtState (k1:=k1) (k2:=k2) M1 M2 x hπ1 c s := by
  let C0 : Set (projectionAmbient X) := {(x,0)}
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1 := .step .refl C0 (blowupProj (n+1) C0) hπ1
  let T := A.append s.2.1
  let Q1 := (projectionTest M1).geoTransformAlong T
  let M2r : MarkedIdeal n X := ⟨M1.N,M1.E,M2.ideal,M2.d⟩
  let Q2r := (projectionTest M2r).geoTransformAlong T
  let Q2 := (projectionTest M2).geoTransformAlong T
  let D := Q1.E.getLastD ∅
  let beta1 := (s.2.1.length+1)*(ordinaryTraceOrder M1.N M1.ideal x-M1.d)
  let beta2 := (s.2.1.length+1)*(ordinaryTraceOrder M1.N M2.ideal x-M2.d)
  have hCurr1 := current_dictionary M1 x hπ1 c SE U s M1.ideal M1.d hM1 hx1 hQuery1.1
  have hCurr2 := current_dictionary M1 x hπ1 c SE U s M2.ideal M2.d
    (h2.symm ▸ hM2) (h2.symm ▸ hx2) hQuery2.1
  rcases hCurr1 with ⟨hTest1,hDom1,hMark1,hCos1,_hOrder1⟩
  rcases hCurr2 with ⟨hTest2,hDom2,hMark2,_hCos2,_hOrder2⟩
  have hBorn1 := hQuery1.2
  have hBorn2 := hQuery2.2
  rcases hBorn1 with ⟨_hN1,_hE1,hzD,_hNonempty,_hClosed,_hNC,hAll1,_hAdm1⟩
  rcases hBorn2 with ⟨hN2,hE2,_hzD2,_hNonempty2,_hClosed2,_hNC2,hAll2,_hAdm2⟩
  change tailPoint s∈D at hzD
  change Q2r.N=Q1.N at hN2
  change Q2r.E=Q1.E at hE2
  have hNotNil : Q1.E≠[] := by
    intro h
    have hh := hzD
    change tailPoint s∈Q1.E.getLastD ∅ at hh
    simp [h] at hh
  obtain ⟨i,hi,hD⟩ := literal_last_index Q1.E (∅ : Set s.1) hNotNil
  have hz : tailPoint s∈Q1.N∩Q1.E.get i := by
    refine ⟨Q1.cosupp_subset_N hCos1,?_⟩
    rw [hD]
    exact hzD
  let G := pureFamily (Nat.succ_pos n) Q1.N Q1.E hDom1.isWellFormed.isClosedSubmanifold_N
    hDom1.isWellFormed.isSNCDivisor hDom1.isWellFormed.isTransverse i (tailPoint s) hz
  have hBeta1 : ∀w∈Q1.N∩Q1.E.get i,∀e,
      IsDivNearAlong (n+1) Q1.N Q1.ideal (Q1.E.get i) e w ↔ e≤beta1 := by
    intro w hw e
    rw [hD] at hw ⊢
    exact ((hAll1 w hw).2.1 e)
  have hBeta2 : ∀w∈Q1.N∩Q1.E.get i,∀e,
      IsDivNearAlong (n+1) Q2r.N Q2r.ideal (Q1.E.get i) e w ↔ e≤beta2 := by
    intro w hw e
    rw [hD] at hw ⊢
    exact ((hAll2 w hw).2.1 e)
  have hCounts1 : CartierQueryCountOutput (k:=k1+1) Q1 beta1 G :=
    query_counts (Nat.succ_pos n) Q1.N Q1.E hDom1.isWellFormed.isClosedSubmanifold_N
      hDom1.isWellFormed.isSNCDivisor hDom1.isWellFormed.isTransverse i (tailPoint s) hz
      Q1 hDom1 rfl rfl beta1 hBeta1
  have hCounts2r : CartierQueryCountOutput (k:=k2+1) Q2r beta2 G :=
    query_counts (Nat.succ_pos n) Q1.N Q1.E hDom1.isWellFormed.isClosedSubmanifold_N
      hDom1.isWellFormed.isSNCDivisor hDom1.isWellFormed.isTransverse i (tailPoint s) hz
      Q2r hDom2 hN2 hE2 beta2 hBeta2
  have hQ2 : Q2r=Q2 := congrArg (fun M : MarkedIdeal n X=>(projectionTest M).geoTransformAlong T) h2
  have hCounts2 : CartierQueryCountOutput (k:=k2+1) Q2 beta2 G := hQ2 ▸ hCounts2r
  have hLen : T.length=s.2.1.length+1 := by
    calc
      _ = A.length+s.2.1.length := BlowupTower.length_append A s.2.1
      _ = s.2.1.length+1 := by change 1+s.2.1.length=s.2.1.length+1;omega
  have hOrig1 := original_history_counts M1 M1.ideal M1.d T hTest1
    (s.2.1.length+1) hLen G beta1 (k1+1) hCounts1
  have hOrig2 := original_history_counts M1 M2.ideal M2.d T hTest2
    (s.2.1.length+1) hLen G beta2 (k2+1) hCounts2r
  refine ⟨G,HEq.rfl,HEq.rfl,?_,HEq.rfl,hCounts1,hCounts2,hOrig1,hOrig2⟩
  exact hi


private abbrev twoRecordCartierCountOutput {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 : MarkedIdeal n X) (hM1 : IsInvDomain k1 M1) (x : X) (hx1 : x∈M1.cosupp)
    (M2 : MarkedIdeal n X) (hM2 : IsInvDomain k2 M2) (hx2 : x∈M2.cosupp)
    (h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M1.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M1 hM1 x hx1 Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M1).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M1 hM1 x hx1).2
  ∃ h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
    IsGeoTestTower Q0 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0,
  ∃ Next : NativeTailState Q0 a→NativeTailState Q0 a,
    (∀s,sameNextGeometry Q0 a s (Next s)) ∧
    let s0 : NativeTailState Q0 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
    let F : ℕ→NativeTailState Q0 a:=Nat.rec s0 (fun _ s=>Next s)
    F 0=s0 ∧ (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=Next (F r)) ∧
    initialQueryOutput M1 x M1.ideal M1.d hM1 hx1 ∧
    initialQueryOutput M1 x M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2) ∧
    ∀r : ℕ,
      queryWithBornAtState M1 x hπ1 c SE U (F r) M1.ideal M1.d hM1 hx1 ∧
      queryWithBornAtState M1 x hπ1 c SE U (F r) M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2) ∧
      cartierAtState (k1:=k1) (k2:=k2) M1 M2 x hπ1 c (F r)



/-- Only the ordinary original records/domains, common cosupport point and
whole source N/E equalities are inputs. The SAME public P08 family and SAME
literal histories are retained; pure Cartier geometry is chosen once before
both ideal/mark count proofs. -/
theorem exists_two_record_shared_cartier_trace_test_counts {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 M2 : MarkedIdeal n X) (hM1 : IsInvDomain k1 M1) (hM2 : IsInvDomain k2 M2)
    (x : X) (hx1 : x∈M1.cosupp) (hx2 : x∈M2.cosupp)
    (hN : M2.N=M1.N) (hE : M2.E=M1.E) :
    ∃(h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2)
      (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M1.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      twoRecordCartierCountOutput M1 hM1 x hx1 M2 hM2 hx2 h2 Φ Φs c SN SE U := by
  obtain ⟨h2,Φ,Φs,c,SN,SE,U,hFamily⟩ :=
    HironakaActualSharedBornTraceTests.exists_two_record_shared_born_trace_tests
      M1 M2 hM1 hM2 x hx1 hx2 hN hE
  change p08TwoRecordOutput M1 hM1 x hx1 M2 hM2 hx2 h2 Φ Φs c SN SE U at hFamily
  let C0 : Set (projectionAmbient X) := {(x,0)}
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C0)
  let Q0 := (projectionTest M1).geoTransform C0 (blowupProj (n+1) C0)
  let hπ1 := isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
    (projection_point_centre M1 hM1 x hx1).2
  rcases hFamily with ⟨hWhole,h0,Next,hNext,hData⟩
  extract_lets s0 F at hData
  change ℕ→NativeTailState (Y1:=Y1) Q0 c.homeo at F
  rcases hData with ⟨hZero,hLen,hSucc,hInit1,hInit2,hAll⟩
  refine ⟨h2,Φ,Φs,c,SN,SE,U,hWhole,h0,Next,hNext,hZero,hLen,hSucc,hInit1,hInit2,?_⟩
  intro r
  obtain ⟨hq1,hq2⟩ := hAll r
  exact ⟨hq1,hq2,cartier_at_state M1 M2 x hπ1 c SE U (F r)
    hM1 hx1 hM2 hx2 h2 hq1 hq2⟩

end
end Hironaka.HironakaActualSharedCartierTraceTests
