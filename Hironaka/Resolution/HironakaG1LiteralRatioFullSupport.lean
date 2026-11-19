import Hironaka.Resolution.HironakaG1SharedNativeLift
import Hironaka.Resolution.HironakaG1RatioBlockNativeStates

/-! The full-section criterion for the two literal ratio adapters. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1LiteralRatioFullSupport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaG1SNCReaderNormalization HironakaG1RelativeReaderWindow
  HironakaG1RelativeBoundaryProjections HironakaG1ReaderProductSubmersions
  HironakaG1RatioGraphProductEquations HironakaG1RatioBlockGraphAdapters
  HironakaG1RatioBlockNativeStates HironakaActualCentreJointJets
  HironakaActualIntrinsicStableAmbientIso HironakaG1NormalGraphFlags
  HironakaBaseChange HironakaG1RatioSectionBlowup
  HironakaActualNativeSectionFiniteHistory HironakaG1SharedNativeLift

private theorem preimage_blockGraph_regular {d k t : ℕ} (h : d = k+t)
    {U : Opens (ComplexModel k)} {X : CMfd.{0} d}
    (e : X → blockOpen U t) (O : Opens (blockOpen U t))
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel (k+t))⟯ O)
    (hb : ∀ x, e x = (b x).val)
    (f : U → ComplexModel t)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel t) ∞ f) :
    ∀ x ∈ e ⁻¹' blockGraph f univ, RegularAtDim (n := d) (e ⁻¹' blockGraph f univ) x k := by
  subst d
  exact sectionSupport_regular ⟨O,b,hb⟩ hf

variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m} {p : M} {q : N}
    {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
    (R : RelativeReaders p q E F τ) (U : Opens M) (V : Opens N)
    (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
    (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a)

/-- The full left graph support in the actual common ratio open. -/
def leftFullSupport : Set (Common R U V) :=
  leftBlockMap R U V ⁻¹' blockGraph (leftBlockGraphValue R U a forward) univ

/-- The full scaled right graph support in the actual common ratio open. -/
def rightFullSupport : Set (Common R U V) :=
  rightBlockMap R U V ⁻¹' blockGraph (rightBlockGraphValue R V b backward) univ

/-- Equality of the literal supports is precisely agreement of the two
full graph equations on the common window. -/
theorem fullSupport_eq_iff :
    leftFullSupport R U V a forward = rightFullSupport R U V b backward ↔
      ∀ z : Common R U V,
        let w := graphEquationWindowToRatio R U V z
        (sourceProduct R.r R.a R.b w.val).2 = leftGraphValue R a forward (firstReaderMap R w) ↔
          (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b w.val)).2 =
            rightGraphValue R b backward (secondReaderMap R w) := by
  have hL (z : Common R U V) :
      z ∈ leftFullSupport R U V a forward ↔
        let w := graphEquationWindowToRatio R U V z
        (sourceProduct R.r R.a R.b w.val).2 = leftGraphValue R a forward (firstReaderMap R w) := by
    change (blockProjection (leftBlockMap R U V z) ∈ univ ∧
      actualJointNormalProjection _ _ (join _ _) =
        leftGraphValue R a forward
          (normalizedBaseMap R.sourceDiffeomorph U (blockProjection (leftBlockMap R U V z)))) ↔ _
    rw [second_join,leftBlockMap_base]
    exact ⟨And.right,fun h => ⟨mem_univ _,h⟩⟩
  have hR (z : Common R U V) :
      z ∈ rightFullSupport R U V b backward ↔
        let w := graphEquationWindowToRatio R U V z
        (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b w.val)).2 =
          rightGraphValue R b backward (secondReaderMap R w) := by
    change (blockProjection (rightBlockMap R U V z) ∈ univ ∧
      actualJointNormalProjection _ _ (join _ _) =
        rightGraphValue R b backward
          (normalizedBaseMap R.targetDiffeomorph V (blockProjection (rightBlockMap R U V z)))) ↔ _
    rw [second_join,rightBlockMap_base]
    exact ⟨And.right,fun h => ⟨mem_univ _,h⟩⟩
  constructor
  · intro h z
    exact (hL z).symm.trans ((Iff.of_eq (congrArg (fun A : Set (Common R U V) => z ∈ A) h)).trans (hR z))
  · intro h
    exact Set.ext fun z => (hL z).trans ((h z).trans (hR z).symm)

/-- For unequal original dimensions a nonempty full-support equality is
impossible. The right smoothness here is in its original scaled block
order, with the dimension reindexed only after applying its open chart. -/
theorem dimension_eq_of_fullSupport_eq
    (ha : ∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x)
    (hb : ∀ y ∈ V, ∀ i, HolomorphicAt m (b i) y)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel R.b) ∞ forward U)
    (hg : ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel R.a) ∞ backward V)
    (hEq : leftFullSupport R U V a forward = rightFullSupport R U V b backward)
    (hne : (leftFullSupport R U V a forward).Nonempty) : n = m := by
  let d := (R.r+R.a)+(R.r+R.b)
  let X := CMfd.of (n := d) (Common R U V)
  obtain ⟨z,hz⟩ := hne
  obtain ⟨OL,eL,hOL⟩ := leftBlockMap_openImage R U V
  obtain ⟨OR,eR,hOR⟩ := rightBlockMap_openImage R U V
  have hl := preimage_blockGraph_regular (X := X) rfl _ OL eL hOL _
    (leftBlockGraphValue_hol R U a forward ha hf) z hz
  have hzR : z ∈ rightFullSupport R U V b backward := hEq ▸ hz
  have hr := preimage_blockGraph_regular (X := X) (Nat.add_comm _ _) _ OR eR hOR _
    (rightBlockGraphValue_hol R V b backward hb hg) z hzR
  have hregR : RegularAtDim (n := d) (rightFullSupport R U V b backward) z (R.r+R.b) := hr
  have hregL : RegularAtDim (n := d) (leftFullSupport R U V a forward) z (R.r+R.b) :=
    hEq.symm ▸ hregR
  have hdim : R.r + R.a = R.r + R.b :=
    RegularPointDimension.eq_of_regularAtDim hl hregL
  exact R.dimension₁.trans (hdim.trans R.dimension₂.symm)


/-- The actual paired analytic cut sits in both full supports. This is the
precise distinction between the paired cut equations and full equality. -/
theorem pairedCut_subset_fullSupports
    {C : Set M} {D : Set N} {G : Set (readerUnitWindow R)}
    (hL : ∀ z : readerUnitWindow R, z ∈ G ↔ firstReaderMap R z ∈ C ∩ (U : Set M) ∧
      (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (firstReaderMap R z))
    (hR : ∀ z : readerUnitWindow R, z ∈ G ↔ secondReaderMap R z ∈ D ∩ (V : Set N) ∧
      (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).2 =
        rightGraphValue R b backward (secondReaderMap R z)) :
    graphEquationWindowToRatio R U V ⁻¹' G ⊆
      leftFullSupport R U V a forward ∩ rightFullSupport R U V b backward := by
  obtain ⟨hl,hr⟩ := blockGraph_preimages R U V a b forward backward hL hR
  intro z hz
  exact ⟨⟨mem_univ _,(hl.symm ▸ hz).2⟩,⟨mem_univ _,(hr.symm ▸ hz).2⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The two literal ratio lifts share the native tower if the full graph
equations agree on the actual common open and a common source point
exists. The inherited ordered boundary and the genuine upper
projection history are the same. -/
theorem literalRatio_shared_lifts
    {Y : CMfd.{0} ((R.r+R.a)+(R.r+R.b))}
    (T : BlowupTower (CMfd.of (n := (R.r+R.a)+(R.r+R.b)) (Common R U V)) Y)
    (E₀ : List (Set (Common R U V))) :
    let WL := leftFullSupport R U V a forward
    let WR := rightFullSupport R U V b backward
    let d := (R.r+R.a)+(R.r+R.b)
    let kL := R.r+R.a
    let kR := R.r+R.b
    let hkL : kL ≤ d := Nat.le_add_right _ _
    let hkR : kR ≤ d := Nat.le_add_left _ _
    ∀ (_hFull : WL = WR) (_hne : WL.Nonempty)
      {hWLc : IsClosed WL} {hWRc : IsClosed WR}
      {hWL : ∀ x ∈ WL, RegularAtDim (n := d) WL x kL}
      {hWR : ∀ x ∈ WR, RegularAtDim (n := d) WR x kR}
      {VL VR : Set Y} {hVLc : IsClosed VL} {hVRc : IsClosed VR}
      {hVL : ∀ y ∈ VL, RegularAtDim (n := d) VL y kL}
      {hVR : ∀ y ∈ VR, RegularAtDim (n := d) VR y kR}
      {BL : BlowupTower (nativeManifold (Y := CMfd.of (n := d) (Common R U V)) hkL WL hWL) (nativeManifold hkL VL hVL)}
      {BR : BlowupTower (nativeManifold (Y := CMfd.of (n := d) (Common R U V)) hkR WR hWR) (nativeManifold hkR VR hVR)},
      Lift hkL WL hWLc hWL E₀ T VL hVLc hVL BL →
      Lift hkR WR hWRc hWR E₀ T VR hVRc hVR BR →
      n = m ∧ VL = VR ∧ HEq BL BR := by
  intro WL WR d kL kR hkL hkR hFull hne hWLc hWRc hWL hWR VL VR hVLc hVRc hVL hVR BL BR hL hR
  let c := Equiv.setCongr hFull
  have hc (x : WL) : x.val = (c x).val := rfl
  obtain ⟨hk,_,hV,hB⟩ := nativeLift_heq_of_nonempty_source_square
    hL hR (Equiv.refl WL) (Equiv.refl WR) c hc hne
  exact ⟨R.dimension₁.trans (hk.trans R.dimension₂.symm),hV,hB⟩


open MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  NormalCrossings HironakaG8LocalHistory HironakaG11InvBMClass DivisorExponentAlong
  HironakaG1CrossAmbientNativeComparison HironakaG1CrossAmbientNativeClassComparison
  BlowupTowerIsomorphism BlowupTowerIsoTail

/-- Once the full supports are identified, the shared lift compares the
two supported records on their common actual upper tower. The only
numerical givens are the weak class, carrier dimension and normalized
boundary exponents of the exact native inputs. -/
theorem supported_order_on_literal_shared_lift {d k q : ℕ} {X Y : CMfd.{0} d}
    (hk : k ≤ d) (hkpos : 0 < k) {W : Set X} {hc : IsClosed W}
    {hw : ∀ x ∈ W, RegularAtDim (n := d) W x k} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := d) V y k}
    {T : BlowupTower X Y}
    {B : BlowupTower (nativeManifold hk W hw) (nativeManifold hk V hV)}
    (P Q : MarkedIdeal d X) (hP : IsInvDomain q P) (hQ : IsInvDomain q Q)
    (hPN : P.N ⊆ W) (hQN : Q.N ⊆ W) (hE : Q.E = P.E)
    (hTr : IsTransverse d W P.E) (hLift : Lift hk W hc hw P.E T V hVc hV B) :
    let L := nativePullback hk W hw P
    let R := nativePullback hk W hw Q
    let I := invFamily (hkpos.trans_le hk) ((d-k)+q)
    ∀ (_hClass : LocWPEquiv L R) (_hDim : SameCarrierDim L R)
      (_hExp : ∀ H ∈ L.E, ∀ x ∈ L.cosupp, x ∈ H →
        R.d * divExpAlong k L.N L.ideal H x = L.d * divExpAlong k R.N R.ideal H x),
      (IsCanonical P (I.inv P) T ↔ IsCanonical Q (I.inv Q) T) ∧
      (IsCanonical P (I.inv P) T →
        let K := (geoTransformAlong P T).cosupp
        K = (geoTransformAlong Q T).cosupp ∧
        (∀ x ∈ K, ∀ y ∈ K, I.inv P T x < I.inv P T y ↔ I.inv Q T x < I.inv Q T y) ∧
        maxLocus (I.inv P T) K = maxLocus (I.inv Q T) K) := by
  intro L R I hClass hDim hExp
  let A := nativeManifold hk W hw
  let Z := nativeManifold hk V hV
  let a := Diffeomorph.refl 𝓘(ℂ,ComplexModel k) A ∞
  let z := Diffeomorph.refl 𝓘(ℂ,ComplexModel k) Z ∞
  have hLD := HironakaActualNativeInvariantDomain.isInvDomain_nativePullback
    (hkpos.trans_le hk) hk hw P hP hPN hTr
  have hRD := HironakaActualNativeInvariantDomain.isInvDomain_nativePullback
    (hkpos.trans_le hk) hk hw Q hQ hQN (hE.symm ▸ hTr)
  let l : NativeChartRealization L B d q :=
    ⟨X,Y,P,hP,T,hk,W,hc,hw,hPN,hTr,V,hVc,hV,B,hLift,a,z,IsTowerIso.refl_self B,
      ContactCanonicalAlong.pullback_id L hLD.isWellFormed.isCoherent⟩
  let r : NativeChartRealization R B d q :=
    ⟨X,Y,Q,hQ,T,hk,W,hc,hw,hQN,hE.symm ▸ hTr,V,hVc,hV,B,hE.symm ▸ hLift,a,z,
      IsTowerIso.refl_self B,ContactCanonicalAlong.pullback_id R hRD.isWellFormed.isCoherent⟩
  obtain ⟨hCan,hRead⟩ := cross_ambient_native_comparison_of_class l r hkpos hClass hDim hExp
  refine ⟨hCan,fun h => ?_⟩
  obtain ⟨hL,hR,hOrder,_,hMaxL,hMaxR⟩ := hRead h
  have hMaps : l.endpointMap = r.endpointMap := rfl
  rw [← hMaps] at hR
  have hK := hL.symm.trans hR
  refine ⟨hK,?_,?_⟩
  · intro x hx y hy
    rw [← hL] at hx hy
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    exact hOrder u hu v hv
  · calc
      _ = maxLocus (I.inv Q T) (geoTransformAlong Q T).cosupp :=
        hMaxL.symm.trans (show l.endpointMap '' _ = _ from hMaxR)
      _ = _ := congrArg (maxLocus (I.inv Q T)) hK.symm

end
end Hironaka.HironakaG1LiteralRatioFullSupport
