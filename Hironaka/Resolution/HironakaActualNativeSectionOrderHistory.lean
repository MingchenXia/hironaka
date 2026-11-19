import Hironaka.Resolution.HironakaActualNativeSectionFiniteHistory
import Hironaka.Resolution.HironakaActualNativeSectionBoundaryParts
import Hironaka.Invariant.NonmonomialOrderRegime
/-! Original current cosupport and nonmonomial order, then ORIGINAL chronological
order-regime runs, on actual finite induced native histories. There is no fresh
value restart and no supplied comparison field in the geometric Lift relation.
Step1 special loci and complete invariant/lower histories remain separate. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionOrderHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
  SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionOrder HironakaActualNativeSectionBoundaryParts
  HironakaActualRawRecordPullbacks RelativePrincipalizationSpan GermIdealOrder
  NonmonomialOrderLocal NonmonomialOrderRegime StepOneRegime NormalCrossings

variable {n k : ℕ}

theorem cosupp_nativePullback (hk : k≤n) {Y : CMfd.{0} n} (V : Set Y)
    (hV : ∀y∈V,RegularAtDim (n := n) V y k) (M : MarkedIdeal n Y)
    (hMN : M.N⊆V) (hhol : ∀y g,M.ideal.mem y g → HolomorphicAt n g y) :
    (nativePullback hk V hV M).cosupp=(Subtype.val : V→Y) ⁻¹' M.cosupp := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let A:=(Subtype.val : V→Y) ⁻¹' M.N
  have hImage : (Subtype.val : V→Y) '' A=M.N := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hy
      exact ⟨⟨y,hMN hy⟩,hy,rfl⟩
  have hc:=cosupport_native_preimage hk hV A M.ideal hhol M.d
  rw [hImage] at hc
  exact hc.symm

theorem nmOrd_nativePullback (hk : k≤n) {Y : CMfd.{0} n} (V : Set Y)
    (hV : ∀y∈V,RegularAtDim (n := n) V y k) (M : MarkedIdeal n Y)
    (hMN : M.N⊆V) (hE : IsSNCDivisor n M.E) (hT : IsTransverse n V M.E)
    (hhol : ∀y g,M.ideal.mem y g → HolomorphicAt n g y) (p : nativeManifold hk V hV) :
    nmOrd M p.val=nmOrd (M := nativeManifold hk V hV) (nativePullback hk V hV M) p := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let A:=(Subtype.val : V→Y) ⁻¹' M.N
  have hImage : (Subtype.val : V→Y) '' A=M.N := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y,hMN hy⟩,hy,rfl⟩
  let M0 : MarkedIdeal n Y:=⟨(Subtype.val : V→Y) '' A,M.E,M.ideal,M.d⟩
  have hM0 : M0=M:=by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact hImage
    · rfl
    · rfl
    · rfl
  have hv:=nmOrd_native_eq hk hV A M.E hE hT M.ideal hhol M.d p
  change nmOrd (M := Y) M0 p.val=
    nmOrd (M := nativeManifold hk V hV) (nativePullback hk V hV M) p at hv
  rwa [hM0] at hv

variable {X : CMfd.{0} n} {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n := n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

theorem Lift.current_carrier_subset (h : Lift hk W hWc hW E T V hVc hV Q)
    (M : MarkedIdeal n X) (hMN : M.N⊆W) : (geoTransformAlong M T).N⊆V := by
  induction h with
  | refl => exact hMN
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    apply closure_mono
    intro z hz
    exact ⟨ih hz.1,hz.2⟩

theorem Lift.current_cosupport (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) :
    (geoTransformAlong (nativePullback hk W hW M) Q).cosupp=
      (Subtype.val : V→Y) ⁻¹' (geoTransformAlong M T).cosupp := by
  have hrec:=h.whole_records hn hE hTrans M hME hMN hhol
  have hc:=cosupp_nativePullback hk V hV (geoTransformAlong M T)
    (Lift.current_carrier_subset h M hMN) (holomorphic_geoTransformAlong M hhol T)
  exact (congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV) => K.cosupp) hrec).trans hc

theorem Lift.current_nmOrd (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) (p : nativeManifold hk V hV) :
    nmOrd (geoTransformAlong M T) p.val=
      nmOrd (M := nativeManifold hk V hV) (geoTransformAlong (nativePullback hk W hW M) Q) p := by
  have hrec:=h.whole_records hn hE hTrans M hME hMN hhol
  obtain ⟨hEcur,hTcur⟩:=h.geometry hn hE hTrans
  have hEN : (geoTransformAlong M T).E=boundary E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := M) (𝔫 := (⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) hME T
  rw [←hEN] at hEcur hTcur
  have hv:=nmOrd_nativePullback hk V hV (geoTransformAlong M T)
    (Lift.current_carrier_subset h M hMN) hEcur hTcur (holomorphic_geoTransformAlong M hhol T) p
  exact hv.trans (congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV) =>
    nmOrd (M := nativeManifold hk V hV) K p) hrec).symm

theorem Lift.original_order_regime (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) (o : ℕ) (p : nativeManifold hk V hV) :
    OrdRegime M o T p.val ↔ OrdRegime (nativePullback hk W hW M) o Q p := by
  have hc:=Lift.current_cosupport h hn hE hTrans M hME hMN hhol
  have hv:=Lift.current_nmOrd h hn hE hTrans M hME hMN hhol p
  change (p.val∈(geoTransformAlong M T).cosupp ∧ nmOrd (geoTransformAlong M T) p.val=o) ↔
    (p∈(geoTransformAlong (nativePullback hk W hW M) Q).cosupp ∧
      nmOrd (M := nativeManifold hk V hV) (geoTransformAlong (nativePullback hk W hW M) Q) p=o)
  have hp : p.val∈(geoTransformAlong M T).cosupp ↔
      p∈(geoTransformAlong (nativePullback hk W hW M) Q).cosupp:=
    Iff.of_eq (congrArg (fun S : Set (nativeManifold hk V hV) => p∈S) hc).symm
  exact and_congr hp (by rw [hv])

theorem Lift.original_order_regime_run (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) (o : ℕ) :
    ∀p : nativeManifold hk V hV,
      regimeRun (OrdRegime M o) T p.val=
        regimeRun (OrdRegime (nativePullback hk W hW M) o) Q p := by
  induction h with
  | refl => intro p;rfl
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    intro p
    classical
    let z:=nativeProjection hk hVc hV D π hπ p
    have hp:=Lift.original_order_regime h hn hE hTrans M hME hMN hhol o z
    change (if OrdRegime M o T z.val then regimeRun (OrdRegime M o) T z.val+1 else 0)=
      if OrdRegime (nativePullback hk W hW M) o Q z then
        regimeRun (OrdRegime (nativePullback hk W hW M) o) Q z+1 else 0
    by_cases hz : OrdRegime M o T z.val
    · rw [if_pos hz,if_pos (hp.mp hz),ih z]
    · rw [if_neg hz,if_neg (fun h' => hz (hp.mpr h'))]

end
end Hironaka.HironakaActualNativeSectionOrderHistory
