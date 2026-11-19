import Hironaka.Resolution.HironakaActualRelativeNormalCanonicalHistory

/-! Actual finite relative normal histories on the SAME original clock, with
all whole boundary positions and an explicit actual native Lift chain.
Blueprint: hironaka-actual-iterated-relative-normal-history-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe v
namespace Hironaka.HironakaActualIteratedRelativeNormalHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec InvDomainTowerAlong CanonicalCentres NormalCrossings
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeHistoryExistence HironakaActualNativeInvariantDomain
  HironakaOriginalFamilyDepthStability HironakaActualRelativeNormalGeometry
  HironakaActualSectionBoundaryDimension
  HironakaActualRelativeNormalCanonicalHistory HironakaDisjointCoherentNormalRecoding
  RelativePrincipalizationSpan GermIdealOrder

private abbrev model {m : ℕ} (V : Opens (ComplexModel m)) : CMfd.{0} m:=CMfd.of (n:=m) V

def iteratedOpen {n : ℕ} (U : Opens (ComplexModel n)) : (r : ℕ)→Opens (ComplexModel (n+r))
  | 0=>U
  | r+1=>productOpen (iteratedOpen U r)

def iteratedIdeal {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) :
    (r : ℕ)→GermIdeal (n+r) (iteratedOpen U r)
  | 0=>I
  | r+1=>relativeNormalIdeal (iteratedIdeal I r)

def iteratedMarked {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) (r : ℕ) :
    MarkedIdeal (n+r) (model (iteratedOpen U r)):=relativeBaseMarked (iteratedIdeal I r)

def iteratedZeroSection {n : ℕ} (U : Opens (ComplexModel n)) : (r : ℕ)→U→iteratedOpen U r
  | 0,x=>x
  | r+1,x=>zeroSection (iteratedOpen U r) (iteratedZeroSection U r x)

theorem iteratedZeroSection_contMDiff {n : ℕ} (U : Opens (ComplexModel n)) (r : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+r)) ∞ (iteratedZeroSection U r):=by
  induction r with
  | zero=>exact contMDiff_id
  | succ r ih=>exact (zeroSection_contMDiff (iteratedOpen U r)).comp ih

def iteratedValueEmbedding (q : ℕ) : (r : ℕ)→ValTy q→ValTy (q+r)
  | 0,v=>v
  | r+1,v=>initialEmbedding (q+r) (sameIndexMap 1 (q+r) (iteratedValueEmbedding q r v))

theorem strictMono_iteratedValueEmbedding (q r : ℕ) : StrictMono (iteratedValueEmbedding q r):=by
  induction r with
  | zero=>exact strictMono_id
  | succ r ih=>exact (initialEmbedding (q+r)).strictMono.comp ((strictMono_sameIndexMap 1 (q+r)).comp ih)

theorem original_iterated_domain {n q : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hM : IsInvDomain q (relativeBaseMarked I)) (r : ℕ) : IsInvDomain (q+r) (iteratedMarked I r):=by
  induction r with
  | zero=>exact hM
  | succ r ih=>exact (relative_normal_original_geometry ih).1

private theorem plane_closed {m : ℕ} (V : Opens (ComplexModel m)) : IsClosed (normalPlane V):=by
  have h : IsClosed {z : (⊤ : Opens (productOpen V)) | actualJointNormalProjection m 1 z.val.val=0}:=
    isClosed_eq ((actualJointNormalProjection m 1).continuous.comp
      ((continuous_subtype_val : Continuous (Subtype.val : productOpen V→ComplexModel (m+1))).comp
        (continuous_subtype_val : Continuous (Subtype.val : (⊤ : Opens (productOpen V))→productOpen V)))) continuous_const
  have he : normalPlane V={z : (⊤ : Opens (productOpen V)) | actualJointNormalProjection m 1 z.val.val=0}:=by
    ext z
    change (projection V z.val∈univ ∧ actualJointNormalProjection m 1 z.val.val=0) ↔
      actualJointNormalProjection m 1 z.val.val=0
    simp only [mem_univ,true_and]
  exact he.symm ▸ h

/-- Actual native Lift data at EVERY normal stage, constructed as a conclusion.
The successor uses the SAME actual transported lower tower, not a supplied
compatible family or merely an equality of final resolution maps. -/
inductive NormalHistoryLift {n : ℕ} (U : Opens (ComplexModel n)) (I : GermIdeal n U) :
    (r : ℕ)→{Y : CMfd.{0} (n+r)}→BlowupTower (model (iteratedOpen U r)) Y→
      {Z : CMfd.{0} n}→BlowupTower (model U) Z→(Z→Y)→Prop where
  | refl {Y : CMfd.{0} n} (T : BlowupTower (model U) Y) : NormalHistoryLift U I 0 T T id
  | step {r : ℕ} {Y : CMfd.{0} (n+(r+1))} {T : BlowupTower (model (iteratedOpen U (r+1))) Y}
      (V : Set (openPreimage T (⊤ : Opens (iteratedOpen U (r+1)))) )
      (hVc : IsClosed V) (hV : ∀z∈V,RegularAtDim (n:=n+(r+1)) V z (n+r))
      (Q : BlowupTower
        (nativeManifold (Nat.le_succ (n+r)) (normalPlane (iteratedOpen U r)) (normalPlane_regular (iteratedOpen U r)))
        (nativeManifold (Y:=CMfd.of (n:=n+(r+1)) (openPreimage T (⊤ : Opens (iteratedOpen U (r+1)))))
          (Nat.le_succ (n+r)) V hV))
      (hLift : Lift (Nat.le_succ (n+r)) (normalPlane (iteratedOpen U r)) (plane_closed (iteratedOpen U r))
        (normalPlane_regular (iteratedOpen U r)) (relativeNormalContact (iteratedIdeal I r)).E
        (restrict ⊤ T) V hVc hV Q)
      {Z : CMfd.{0} n} {P : BlowupTower (model U) Z}
      (k : Z→(transport (normalBaseEquiv (iteratedOpen U r)) Q).target)
      (rest : NormalHistoryLift U I r (transport (normalBaseEquiv (iteratedOpen U r)) Q).tower P k) :
      NormalHistoryLift U I (r+1) T P
        (fun z=>((transport (normalBaseEquiv (iteratedOpen U r)) Q).back (k z)).val.val)

/-- The ACTUAL zero-dimensional native terminal branch. No positive-dimensional
invariant family or chosen base point is invented at ambient dimension zero. -/
theorem zero_dimensional_cosupp_empty {q : ℕ} {X : CMfd.{v} 0}
    (M : MarkedIdeal 0 X) (hM : IsInvDomain q M) : M.cosupp=∅:=by
  let : DiscreteTopology X:=ChartedSpace.discreteTopology (ComplexModel 0) X
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨g,hg,hf⟩:=hM.isNonzeroAlongAt x hx.1
  have hfx : g x≠0:=by
    have h : x∈M.N ∧ g x≠0:=by simpa only [nhds_discrete,Filter.frequently_pure] using hf
    exact h.2
  have hx1 : x∈cosupport 0 M.N M.ideal 1:=cosupport_anti hM.one_le_d hx
  exact hfx ((vanishesToOrderOn_one_iff hx1.1
    (GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)).mp (hx1.2 g hg))

theorem zero_dimensional_test_resolution {q : ℕ} {X Y : CMfd.{v} 0}
    (M : MarkedIdeal 0 X) (hM : IsInvDomain q M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) : IsGeoResolution M T:=
  ⟨hT,zero_dimensional_cosupp_empty (geoTransformAlong M T)
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT)⟩

/-- EVERY finite normal extension internally produces the SAME actual original
base history and its full stage geometry. No compatible family is supplied. -/
theorem exists_original_iterated_normal_base_history {n q : ℕ} {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hn : 0<n) (hM : IsInvDomain q (relativeBaseMarked I)) :
    ∀(r : ℕ) {Y : CMfd.{0} (n+r)} (T : BlowupTower (model (iteratedOpen U r)) Y),
      IsCanonical (iteratedMarked I r)
        ((invFamily (by omega : 0<n+r) (q+r)).inv (iteratedMarked I r)) T →
      ∃(Z : CMfd.{0} n) (P : BlowupTower (model U) Z) (j : Z→Y),
        NormalHistoryLift U I r T P j ∧
        IsCanonical (relativeBaseMarked I) ((invFamily hn q).inv (relativeBaseMarked I)) P ∧
        IsGeoTestTower (relativeBaseMarked I) P ∧ P.length=T.length ∧
        (∀z,T.proj (j z)=iteratedZeroSection U r (P.proj z)) ∧
        (geoTransformAlong (relativeBaseMarked I) P).E=
          (geoTransformAlong (iteratedMarked I r) T).E.map (j ⁻¹' ·) ∧
        (geoTransformAlong (relativeBaseMarked I) P).cosupp=
          j ⁻¹' (geoTransformAlong (iteratedMarked I r) T).cosupp ∧
        j '' (geoTransformAlong (relativeBaseMarked I) P).cosupp=
          (geoTransformAlong (iteratedMarked I r) T).cosupp ∧
        (∀z∈(geoTransformAlong (relativeBaseMarked I) P).cosupp,
          (invFamily (by omega : 0<n+r) (q+r)).inv (iteratedMarked I r) T (j z)=
            iteratedValueEmbedding q r ((invFamily hn q).inv (relativeBaseMarked I) P z)) ∧
        ResolutionDriver.maxLocus ((invFamily (by omega : 0<n+r) (q+r)).inv (iteratedMarked I r) T)
          (geoTransformAlong (iteratedMarked I r) T).cosupp=
          j '' ResolutionDriver.maxLocus ((invFamily hn q).inv (relativeBaseMarked I) P)
            (geoTransformAlong (relativeBaseMarked I) P).cosupp ∧
        (IsGeoResolution (iteratedMarked I r) T ↔ IsGeoResolution (relativeBaseMarked I) P):=by
  intro r
  induction r with
  | zero=>
    intro Y T hCan
    have ht:=Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical (invFamily hn q) hM T hCan
    refine ⟨Y,T,id,NormalHistoryLift.refl T,hCan,ht,rfl,?_,?_,?_,?_,?_,?_,?_⟩
    · intro z
      rfl
    · change (geoTransformAlong (relativeBaseMarked I) T).E=
        (geoTransformAlong (relativeBaseMarked I) T).E.map id
      rw [List.map_id]
    · rfl
    · simp only [image_id]
      rfl
    · intro z _
      rfl
    · simp only [image_id]
      rfl
    · rfl
  | succ r ih=>
    intro Y T hCan
    obtain ⟨V,hVc,hV,Q,hLift,hCanL,hTestL,hLenL,hSquareL,hBoundaryL,hCosL,hImageL,hValuesL,hMaximumL,hResolutionL⟩:=
      exists_original_relative_normal_base_history (n:=n+r) (q:=q+r) (U:=iteratedOpen U r)
        (I:=iteratedIdeal I r) (by omega) (original_iterated_domain hM r) T hCan
    let H:=transport (normalBaseEquiv (iteratedOpen U r)) Q
    obtain ⟨Z,P,k,hRest,hCanP,hTestP,hLenP,hSquareP,hBoundaryP,hCosP,hImageP,hValuesP,hMaximumP,hResolutionP⟩:=
      ih H.tower hCanL
    let l : H.target→Y:=fun w=>(H.back w).val.val
    let j : Z→Y:=l∘k
    change (geoTransformAlong (iteratedMarked I r) H.tower).E=
      (geoTransformAlong (iteratedMarked I (r+1)) T).E.map (l ⁻¹' ·) at hBoundaryL
    change (geoTransformAlong (iteratedMarked I r) H.tower).cosupp=
      l ⁻¹' (geoTransformAlong (iteratedMarked I (r+1)) T).cosupp at hCosL
    change ResolutionDriver.maxLocus
        ((invFamily (by omega : 0<n+(r+1)) (q+(r+1))).inv (iteratedMarked I (r+1)) T)
        (geoTransformAlong (iteratedMarked I (r+1)) T).cosupp=
      l '' ResolutionDriver.maxLocus
        ((invFamily (by omega : 0<n+r) (q+r)).inv (iteratedMarked I r) H.tower)
        (geoTransformAlong (iteratedMarked I r) H.tower).cosupp at hMaximumL
    have hChain : NormalHistoryLift U I (r+1) T P j:=NormalHistoryLift.step V hVc hV Q hLift k hRest
    have hSquare : ∀z,T.proj (j z)=iteratedZeroSection U (r+1) (P.proj z):=by
      intro z
      exact (hSquareL (k z)).trans (congrArg (zeroSection (iteratedOpen U r)) (hSquareP z))
    have hBoundary : (geoTransformAlong (relativeBaseMarked I) P).E=
        (geoTransformAlong (iteratedMarked I (r+1)) T).E.map (j ⁻¹' ·):=by
      rw [hBoundaryP,hBoundaryL,List.map_map]
      rfl
    have hCos : (geoTransformAlong (relativeBaseMarked I) P).cosupp=
        j ⁻¹' (geoTransformAlong (iteratedMarked I (r+1)) T).cosupp:=by
      rw [hCosP,hCosL]
      rfl
    have hImage : j '' (geoTransformAlong (relativeBaseMarked I) P).cosupp=
        (geoTransformAlong (iteratedMarked I (r+1)) T).cosupp:=by
      calc
        j '' (geoTransformAlong (relativeBaseMarked I) P).cosupp=
            l '' (k '' (geoTransformAlong (relativeBaseMarked I) P).cosupp):=by
              rw [Set.image_image]
              rfl
        _=(geoTransformAlong (iteratedMarked I (r+1)) T).cosupp:=by rw [hImageP];exact hImageL
    have hValues : ∀z∈(geoTransformAlong (relativeBaseMarked I) P).cosupp,
        (invFamily (by omega : 0<n+(r+1)) (q+(r+1))).inv (iteratedMarked I (r+1)) T (j z)=
          iteratedValueEmbedding q (r+1) ((invFamily hn q).inv (relativeBaseMarked I) P z):=by
      intro z hz
      have hk : k z∈(geoTransformAlong (iteratedMarked I r) H.tower).cosupp:=(Set.ext_iff.mp hCosP z).mp hz
      exact (hValuesL (k z) hk).trans
        (congrArg (fun v : ValTy (q+r)=>initialEmbedding (q+r) (sameIndexMap 1 (q+r) v)) (hValuesP z hz))
    have hMaximum :
        ResolutionDriver.maxLocus ((invFamily (by omega : 0<n+(r+1)) (q+(r+1))).inv (iteratedMarked I (r+1)) T)
          (geoTransformAlong (iteratedMarked I (r+1)) T).cosupp=
          j '' ResolutionDriver.maxLocus ((invFamily hn q).inv (relativeBaseMarked I) P)
            (geoTransformAlong (relativeBaseMarked I) P).cosupp:=by
      rw [hMaximumL,hMaximumP,Set.image_image]
      rfl
    exact ⟨Z,P,j,hChain,hCanP,hTestP,hLenP.trans hLenL,hSquare,hBoundary,hCos,hImage,hValues,hMaximum,
      hResolutionL.trans hResolutionP⟩

end
end Hironaka.HironakaActualIteratedRelativeNormalHistory
