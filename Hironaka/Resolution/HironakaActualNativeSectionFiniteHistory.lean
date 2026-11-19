import Hironaka.Resolution.HironakaActualNativeSectionStepModel
import Hironaka.Resolution.HironakaActualNativeSectionMemberLocus
import Hironaka.Resolution.HironakaActualRawRecordPullbacks
/-! Actual finite native histories are specified by recursive geometry only.
Every native variety is the literal induced strict subset and every native
map the literal restricted projection. Full SNC/transversality, lengths,
strict carrier, projection square, every old/born boundary slot, original
prefix and uniform whole raw marked records are DERIVED by induction.
No numerical invariant, locus or clock equality is a relation field, and
no complete chronological invariant comparison or descent is claimed. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionFiniteHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace BlowupStrictSubmanifold HironakaActualClosedContactBlowupRestriction
  HironakaActualNativeSectionStepModel NormalCrossings
variable {n k : ℕ}

def nativeManifold (hk : k≤n) {Y : CMfd.{0} n} (W : Set Y)
    (hW : ∀y∈W,RegularAtDim (n := n) W y k) : CMfd.{0} k := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  exact CMfd.of (n := k) W

def boundary {X : CMfd.{0} n} (E : List (Set X)) {Y : CMfd.{0} n} (T : BlowupTower X Y) : List (Set Y):=
  (geoTransformAlong (⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X) T).E

theorem strictRegular {Y Z : CMfd.{0} n} {W : Set Y} (hWc : IsClosed W)
    (hW : ∀y∈W,RegularAtDim (n := n) W y k) (D : Set W)
    (π : Z→Y) (hπ : IsBlowupAlong n ((Subtype.val : W→Y) '' D) π) :
    ∀z∈geoStrictTransform π ((Subtype.val : W→Y) '' D) W,
      RegularAtDim (n := n) (geoStrictTransform π ((Subtype.val : W→Y) '' D) W) z k :=
  fun _ hz => regularAtDim_geoStrictTransform hπ hWc hW (by
    rintro _ ⟨y,_hy,rfl⟩
    exact y.property) hz

def nativeProjection (hk : k≤n) {Y Z : CMfd.{0} n} {W : Set Y} (hWc : IsClosed W)
    (hW : ∀y∈W,RegularAtDim (n := n) W y k) (D : Set (nativeManifold hk W hW))
    (π : Z→Y) (hπ : IsBlowupAlong n ((Subtype.val : W→Y) '' D) π) :
    nativeManifold hk (geoStrictTransform π ((Subtype.val : W→Y) '' D) W) (strictRegular hWc hW D π hπ) →
      nativeManifold hk W hW := restrictedProjection hWc D hπ

theorem nativeProjection_genuine (hk : k≤n) {Y Z : CMfd.{0} n} {W : Set Y} (hWc : IsClosed W)
    (hW : ∀y∈W,RegularAtDim (n := n) W y k) (D : Set (nativeManifold hk W hW))
    (hD : IsClosedSubmanifold k D) (hint : interior D=∅)
    (π : Z→Y) (hπ : IsBlowupAlong n ((Subtype.val : W→Y) '' D) π) :
    IsBlowupAlong k D (nativeProjection hk hWc hW D π hπ) := by
  exact restrictedProjection_isBlowupAlong hk hWc hW D hπ hD hint

inductive Lift {X : CMfd.{0} n} (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) (E : List (Set X)) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → (V : Set Y) → (hVc : IsClosed V) →
      (hV : ∀y∈V,RegularAtDim (n := n) V y k) →
      BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV) → Prop
  | refl : Lift hk W hWc hW E .refl W hWc hW .refl
  | step {Y Z : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
      {hV : ∀y∈V,RegularAtDim (n := n) V y k}
      {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
      (h : Lift hk W hWc hW E T V hVc hV Q)
      (D : Set (nativeManifold hk V hV)) (hD : IsClosedSubmanifold k D) (hint : interior D=∅)
      (π : Z→Y) (hπ : IsBlowupAlong n ((Subtype.val : V→Y) '' D) π)
      (hNC : HasNormalCrossings n ((Subtype.val : V→Y) '' D) (boundary E T)) :
      Lift hk W hWc hW E (.step T ((Subtype.val : V→Y) '' D) π hπ)
        (geoStrictTransform π ((Subtype.val : V→Y) '' D) V) isClosed_closure
        (strictRegular hVc hV D π hπ)
        (.step Q D (nativeProjection hk hVc hV D π hπ)
          (nativeProjection_genuine hk hVc hV D hD hint π hπ))

open HomogenizedGlueingTower

variable {X : CMfd.{0} n} {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n := n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

theorem Lift.geometry (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hT : IsTransverse n W E) :
    IsSNCDivisor n (boundary E T) ∧ IsTransverse n V (boundary E T) := by
  induction h with
  | refl => exact ⟨hE,hT⟩
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    obtain ⟨_hσ,_hEmb,hE',hT',_hRecords⟩:=actual_native_step hn hk hVc hV
      D hD hint π hπ (boundary E T) ih.1 ih.2 hNC
    exact ⟨hE',hT'⟩

theorem Lift.length (h : Lift hk W hWc hW E T V hVc hV Q) : Q.length=T.length := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

theorem Lift.carrier (h : Lift hk W hWc hW E T V hVc hV Q) : V=strictAlong T W := by
  induction h with
  | refl => rfl
  | step h D hD hint π hπ hNC ih =>
    rw [strictAlong_step,←ih]

theorem Lift.square (h : Lift hk W hWc hW E T V hVc hV Q) :
    ∀z : nativeManifold hk V hV,T.proj z.val=(Q.proj z).val := by
  induction h with
  | refl => intro z;rfl
  | step h D hD hint π hπ hNC ih =>
    intro z
    exact ih (nativeProjection hk _ _ D π hπ z)

open HironakaActualNativeSectionBoundaryTrace

theorem Lift.full_boundary (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hT : IsTransverse n W E) :
    (boundary E T).map ((Subtype.val : V→Y) ⁻¹' ·)=
      boundary (E.map ((Subtype.val : W→X) ⁻¹' ·)) Q := by
  induction h with
  | refl => rfl
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    obtain ⟨hEcur,hTcur⟩:=h.geometry hn hE hT
    have hb:=whole_ordered_boundary_preimage hn hVc D hπ hEcur hTcur hNC
    change ((boundary E T).map (geoStrictTransform π ((Subtype.val : V→Y) '' D)) ++
        [π ⁻¹' ((Subtype.val : V→Y) '' D)]).map
        ((Subtype.val : geoStrictTransform π ((Subtype.val : V→Y) '' D) V→Z) ⁻¹' ·)=
      ((boundary E T).map ((Subtype.val : V→Y) ⁻¹' ·)).map
        (geoStrictTransform (nativeProjection hk hVc hV D π hπ) D) ++
        [(nativeProjection hk hVc hV D π hπ) ⁻¹' D] at hb
    rw [ih] at hb
    exact hb

theorem Lift.original_boundary (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hT : IsTransverse n W E) :
    (E.map (strictAlong T)).map ((Subtype.val : V→Y) ⁻¹' ·)=
      (E.map ((Subtype.val : W→X) ⁻¹' ·)).map (strictAlong Q) := by
  let M : MarkedIdeal n X:=⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩
  let E0:=E.map ((Subtype.val : W→X) ⁻¹' ·)
  let B : MarkedIdeal k (nativeManifold hk W hW):=⟨univ,E0,IdealWeightPowers.unitIdeal k _,1⟩
  have hs:=MemberInterTowerAlong.take_E_geoTransformAlong M T
  have ht:=MemberInterTowerAlong.take_E_geoTransformAlong B Q
  change (boundary E T).take E.length=E.map (strictAlong T) at hs
  change (boundary E0 Q).take E0.length=E0.map (strictAlong Q) at ht
  have hlen : E0.length=E.length:=List.length_map _
  rw [hlen] at ht
  have hb:=congrArg (List.take E.length) (h.full_boundary hn hE hT)
  rw [←List.map_take,hs] at hb
  exact hb.trans ht

private theorem strictAlong_mono {X : CMfd.{0} n} {A B : Set X} (hAB : A⊆B) :
    ∀{Y : CMfd.{0} n} (T : BlowupTower X Y),strictAlong T A⊆strictAlong T B
  | _,.refl => hAB
  | _,.step T C π hπ => by
    apply closure_mono
    intro y hy
    exact ⟨strictAlong_mono hAB T hy.1,hy.2⟩

open HironakaSmoothSubmersionCoefficientIdeals

def nativePullback (hk : k≤n) {Y : CMfd.{0} n} (W : Set Y)
    (hW : ∀y∈W,RegularAtDim (n := n) W y k) (M : MarkedIdeal n Y) :
    MarkedIdeal k (nativeManifold hk W hW) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  exact markedPullback (m := k) (Subtype.val : W→Y) M

theorem Lift.whole_records (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E) :
    ∀(M : MarkedIdeal n X),M.E=E → M.N⊆W →
      (∀x g,M.ideal.mem x g → HolomorphicAt n g x) →
      geoTransformAlong (nativePullback hk W hW M) Q=nativePullback hk V hV (geoTransformAlong M T) := by
  induction h with
  | refl => intro M _hME _hMN _hhol;rfl
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    intro M hME hMN hhol
    let := chartedSpace hk hV
    have := isComplexManifold_chartedSpace hk hV
    let := strictChartedSpace hk hVc hV hπ
    have := strict_isComplexManifold hk hVc hV hπ
    let C:=(Subtype.val : V→Y) '' D
    let S:=geoStrictTransform π C V
    let MT:=geoTransformAlong M T
    let BQ:=geoTransformAlong (nativePullback hk W hW M) Q
    have ihrec : BQ=nativePullback hk V hV MT:=ih M hME hMN hhol
    obtain ⟨hEcur,hTcur⟩:=h.geometry hn hE hTrans
    have hEN : MT.E=boundary E T := by
      exact MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
        (𝔪 := M) (𝔫 := (⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) hME T
    have hNsub : MT.N⊆V := by
      change (geoTransformAlong M T).N⊆V
      rw [N_geoTransformAlong,h.carrier]
      exact strictAlong_mono hMN T
    have hBQ_N : BQ.N=(Subtype.val : V→Y) ⁻¹' MT.N:=
      congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV) => K.N) ihrec
    have hImage : (Subtype.val : V→Y) '' BQ.N=MT.N := by
      rw [hBQ_N]
      ext y
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact hp
      · intro hy
        exact ⟨⟨y,hNsub hy⟩,hy,rfl⟩
    have hMT : ∀y g,MT.ideal.mem y g → HolomorphicAt n g y:=
      HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong M hhol T
    let M0 : MarkedIdeal n Y:=⟨(Subtype.val : V→Y) '' BQ.N,boundary E T,MT.ideal,MT.d⟩
    let B0 : MarkedIdeal k (nativeManifold hk V hV):=
      ⟨BQ.N,(boundary E T).map ((Subtype.val : V→Y) ⁻¹' ·),
        GermIdeal.pullback (m := k) (Subtype.val : V→Y) MT.ideal,MT.d⟩
    have hM0 : M0=MT := by
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · exact hImage
      · exact hEN.symm
      · rfl
      · rfl
    have hB0 : B0=BQ := by
      have hBE : BQ.E=MT.E.map ((Subtype.val : V→Y) ⁻¹' ·):=
        congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV) => K.E) ihrec
      have hBI : BQ.ideal=GermIdeal.pullback (m := k) (Subtype.val : V→Y) MT.ideal:=
        congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV) => K.ideal) ihrec
      have hBd : BQ.d=MT.d:=congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV) => K.d) ihrec
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · rfl
      · exact (hBE.trans (congrArg (List.map ((Subtype.val : V→Y) ⁻¹' ·)) hEN)).symm
      · exact hBI.symm
      · exact hBd.symm
    have hRecord:=markedPullback_actual_restricted_geoTransform hn hk hVc hV
      D BQ.N MT.ideal hMT MT.d hπ hEcur hTcur hNC
    change markedPullback (m := k) (Subtype.val : S→Z) (M0.geoTransform C π)=
      B0.geoTransform D (nativeProjection hk hVc hV D π hπ) at hRecord
    rw [hM0,hB0] at hRecord
    change BQ.geoTransform D (nativeProjection hk hVc hV D π hπ)=
      markedPullback (m := k) (Subtype.val : S→Z) (MT.geoTransform C π)
    exact hRecord.symm

end
end Hironaka.HironakaActualNativeSectionFiniteHistory
