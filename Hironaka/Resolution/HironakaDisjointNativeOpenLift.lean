import Hironaka.Resolution.HironakaDisjointNativeReferenceWindow
import Hironaka.Analytic.SubmanifoldCodRestrict
import Hironaka.Blowup.BlowupTowerIsomorphism

/-! Genuine geometry-only lifts on literal ambient reference restrictions.
Actual induced-open native frames identify every original native step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointNativeOpenLift
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOriginalCuts
  HironakaDisjointNativeReferenceWindow SubmanifoldChartedSpace SubmanifoldCodRestrict
  BlowupTowerIsomorphism BlowupRestrictOpen MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsInvariance BlowupStrictSubmanifold

variable {n k : ℕ} {X : CMfd.{0} n}

/-- The literal section inside the SAME ambient reference open. -/
def openSection (W : Set X) (O : Opens X) : Set (CMfd.of (n := n) O):=
  (Subtype.val : O→X) ⁻¹' W

theorem openSection_regular {W : Set X}
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) (O : Opens X) :
    ∀p∈openSection W O,RegularAtDim (n := n) (openSection W O) p k :=
  fun p hp=>AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hW p.val hp)

/-- Canonical biholomorphism from the ACTUAL induced open-section atlas
to the actual open of the original native manifold, with identical points. -/
def windowEquiv (hk : k≤n) (W : Set X)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) (hWc : IsClosed W) (O : Opens X) :
    nativeManifold hk (openSection W O) (openSection_regular hW O) ≃ₘ⟮
      𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ CMfd.of (n := k) (nativeWindow hk W hW O) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk (openSection_regular hW O)
  have := isComplexManifold_chartedSpace hk (openSection_regular hW O)
  refine ⟨⟨(fun p=>⟨⟨p.val.val,p.property⟩,p.val.property⟩),
    (fun p=>⟨sourceInclusion hk W hW O p,p.val.property⟩),fun _=>rfl,fun _=>rfl⟩,?_,?_⟩
  · apply (ContMDiff.subtypeVal_comp_iff (nativeWindow hk W hW O) _).mp
    exact contMDiff_codRestrict hk hW
      (contMDiff_subtype_val.comp (contMDiff_val hk (openSection_regular hW O)))
      (fun p=>p.property)
  · exact contMDiff_codRestrict hk (openSection_regular hW O)
      (source_geometry hk W hW hWc O).1 (fun p=>p.val.property)

private def equalOpensEquiv {m : ℕ} {Z : CMfd.{0} m} (U V : Opens Z) (e : U=V) :
    CMfd.of (n := m) U ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CMfd.of (n := m) V := by
  subst V
  exact Diffeomorph.refl _ _ _

private theorem equalOpensEquiv_val {m : ℕ} {Z : CMfd.{0} m}
    (U V : Opens Z) (e : U=V) (p : U) : (equalOpensEquiv U V e p).val=p.val := by
  subst V
  rfl

variable {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n := n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

/-- The ACTUAL endpoint native frame onto the literal restricted original
native history, constructed from the true original projection square. -/
def endpointEquiv (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X) :
    nativeManifold hk (openSection V (openPreimage T O))
      (openSection_regular hV (openPreimage T O)) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
        CMfd.of (n := k) (openPreimage Q (nativeWindow hk W hW O)) := by
  have he : nativeWindow hk V hV (openPreimage T O)=openPreimage Q (nativeWindow hk W hW O) := by
    apply Opens.ext
    ext p
    change T.proj p.val∈O ↔ (Q.proj p).val∈O
    rw [h.square p]
  exact (windowEquiv hk V hV hVc (openPreimage T O)).trans (equalOpensEquiv _ _ he)

private theorem endpointEquiv_val (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X)
    (p : nativeManifold hk (openSection V (openPreimage T O))
      (openSection_regular hV (openPreimage T O))) :
    (endpointEquiv h O p).val.val=p.val.val := by
  unfold endpointEquiv
  change (equalOpensEquiv _ _ _ ((windowEquiv hk V hV hVc (openPreimage T O)) p)).val.val=_
  rw [equalOpensEquiv_val]
  rfl

private def sectionFrame (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X)
    (S : Set (CMfd.of (n := n) (openPreimage T O)))
    (hS : ∀p∈S,RegularAtDim (n := n) S p k)
    (he : S=openSection V (openPreimage T O)) :
    nativeManifold hk S hS ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      CMfd.of (n := k) (openPreimage Q (nativeWindow hk W hW O)) := by
  subst S
  exact endpointEquiv h O

private theorem sectionFrame_val (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X)
    (S : Set (CMfd.of (n := n) (openPreimage T O)))
    (hS : ∀p∈S,RegularAtDim (n := n) S p k)
    (he : S=openSection V (openPreimage T O)) (p : nativeManifold hk S hS) :
    (sectionFrame h O S hS he p).val.val=p.val.val := by
  subst S
  exact endpointEquiv_val h O p

private theorem boundary_restrict (E : List (Set X)) (O : Opens X) (T : BlowupTower X Y) :
    boundary (E.map ((Subtype.val : O→X) ⁻¹' ·)) (restrict O T)=
      (boundary E T).map ((Subtype.val : openPreimage T O→Y) ⁻¹' ·) := by
  let M : MarkedIdeal n X:=⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩
  let B : MarkedIdeal n (CMfd.of (n := n) O):=
    ⟨univ,E.map ((Subtype.val : O→X) ⁻¹' ·),IdealWeightPowers.unitIdeal n _,1⟩
  have hE:=MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
    (𝔪 := B) (𝔫 := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O→X) M)
    rfl (restrict O T)
  have hRaw:=HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol M
    (fun _ _ hg=>hg) O T
  exact hE.trans (congrArg (fun A : MarkedIdeal n (CMfd.of (n := n) (openPreimage T O))=>A.E) hRaw)

private theorem step_congr_centre {A B C : CMfd.{0} n} (T : BlowupTower A B)
    {D D' : Set B} (e : D=D') {π : C→B}
    (hπ : IsBlowupAlong n D π) (hπ' : IsBlowupAlong n D' π) :
    BlowupTower.step T D π hπ=BlowupTower.step T D' π hπ' := by
  cases e
  rfl

private theorem open_lift_core (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X) :
    ∃(S : Set (CMfd.of (n := n) (openPreimage T O)))(hSc : IsClosed S)
      (hS : ∀p∈S,RegularAtDim (n := n) S p k)
      (P : BlowupTower
        (nativeManifold hk (openSection W O) (openSection_regular hW O)) (nativeManifold hk S hS))
      (χ : nativeManifold hk S hS ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
        CMfd.of (n := k) (openPreimage Q (nativeWindow hk W hW O))),
      S=openSection V (openPreimage T O) ∧
      Lift hk (openSection W O) (hWc.preimage continuous_subtype_val) (openSection_regular hW O)
        (E.map ((Subtype.val : O→X) ⁻¹' ·)) (restrict O T) S hSc hS P ∧
      IsTowerIso (windowEquiv hk W hW hWc O) P (restrict (nativeWindow hk W hW O) Q) χ ∧
      ∀p,(χ p).val.val=p.val.val := by
  induction h with
  | refl =>
    refine ⟨openSection W O,hWc.preimage continuous_subtype_val,openSection_regular hW O,
      .refl,windowEquiv hk W hW hWc O,rfl,Lift.refl,IsTowerIso.refl,fun _=>rfl⟩
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    obtain ⟨S,hSc,hS,P,χ,hSe,hLift,hIso,hPoint⟩:=ih
    let U:=openPreimage T O
    let U':=openPreimage (.step T ((Subtype.val : V→Y) '' D) π hπ) O
    let QO:=openPreimage Q (nativeWindow hk W hW O)
    let D₀ : Set (CMfd.of (n := k) QO):=(Subtype.val : QO→nativeManifold hk V hV) ⁻¹' D
    let D' : Set (nativeManifold hk S hS):=χ ⁻¹' D₀
    have hD₀ : IsClosedSubmanifold k D₀:=isClosedSubmanifold_preimage_val hD QO
    have hD' : IsClosedSubmanifold k D':=
      (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff χ).mpr hD₀
    have hint₀ : interior D₀=∅:=interior_preimage_val_eq_empty hint QO
    have hint' : interior D'=∅:=by
      simpa only [Diffeomorph.coe_toHomeomorph,hint₀,preimage_empty]
        using (χ.toHomeomorph.preimage_interior D₀).symm
    have hCentre : (Subtype.val : S→U) '' D'=(Subtype.val : U→Y) ⁻¹' ((Subtype.val : V→Y) '' D) := by
      ext y
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨(χ p).val,hp,hPoint p⟩
      · rintro ⟨z,hz,hzy⟩
        have hyS : y∈S := by
          rw [hSe]
          change y.val∈V
          exact hzy ▸ z.property
        let p : nativeManifold hk S hS:=⟨y,hyS⟩
        have hpz : (χ p).val=z:=Subtype.ext ((hPoint p).trans hzy.symm)
        refine ⟨p,?_,rfl⟩
        change (χ p).val∈D
        rw [hpz]
        exact hz
    let πO : CMfd.of (n := n) U'→CMfd.of (n := n) U:=fun p=>⟨π p.val,p.property⟩
    have hπO : IsBlowupAlong n ((Subtype.val : U→Y) ⁻¹' ((Subtype.val : V→Y) '' D)) πO:=
      isBlowupAlong_restrict hπ U (U.isOpen.preimage hπ.contMDiff.continuous)
    have hπO' : IsBlowupAlong n ((Subtype.val : S→U) '' D') πO:=hCentre.symm ▸ hπO
    have hNC' : HasNormalCrossings n ((Subtype.val : S→U) '' D')
        (boundary (E.map ((Subtype.val : O→X) ⁻¹' ·)) (restrict O T)) := by
      rw [hCentre,boundary_restrict]
      exact hasNormalCrossings_preimage (pullsBackCoordinates_val U) hNC
    let S':=geoStrictTransform πO ((Subtype.val : S→U) '' D') S
    have hS' : ∀p∈S',RegularAtDim (n := n) S' p k:=strictRegular hSc hS D' πO hπO'
    have hS'eq : S'=openSection (geoStrictTransform π ((Subtype.val : V→Y) '' D) V) U' := by
      change geoStrictTransform πO ((Subtype.val : S→U) '' D') S=_
      rw [hCentre,hSe]
      exact MarkedIdealRestrictOpen.geoStrictTransform_restrict U
        (U.isOpen.preimage hπ.contMDiff.continuous) V
    let hFull:=Lift.step h D hD hint π hπ hNC
    let χ':=sectionFrame hFull O S' hS' hS'eq
    let P':=BlowupTower.step P D' (nativeProjection hk hSc hS D' πO hπO')
      (nativeProjection_genuine hk hSc hS D' hD' hint' πO hπO')
    have hAmbient : BlowupTower.step (restrict O T) ((Subtype.val : S→U) '' D') πO hπO'=
        restrict O (.step T ((Subtype.val : V→Y) '' D) π hπ) := by
      exact step_congr_centre (restrict O T) hCentre hπO' hπO
    have hLift':=Lift.step hLift D' hD' hint' πO hπO' hNC'
    rw [hAmbient] at hLift'
    refine ⟨S',isClosed_closure,hS',P',χ',hS'eq,hLift',?_,?_⟩
    · apply IsTowerIso.step hIso
        (nativeProjection_genuine hk hSc hS D' hD' hint' πO hπO')
        (isBlowupAlong_restrict (nativeProjection_genuine hk hVc hV D hD hint π hπ) QO
          (QO.isOpen.preimage (nativeProjection_genuine hk hVc hV D hD hint π hπ).contMDiff.continuous)) χ'
      · intro p
        apply Subtype.ext
        apply Subtype.ext
        change π (χ' p).val.val=(χ (nativeProjection hk hSc hS D' πO hπO' p)).val.val
        rw [hPoint,sectionFrame_val]
        rfl
      · rfl
    · exact sectionFrame_val hFull O S' hS' hS'eq

/-- An actual geometric Lift over the LITERAL restricted ambient tower,
with the LITERAL final restricted section and actual induced native atlas.
The native tower is stagewise isomorphic to the ORIGINAL restricted Q. -/
theorem exists_open_lift (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X) :
    ∃(hSc : IsClosed (openSection V (openPreimage T O)))
      (hS : ∀p∈openSection V (openPreimage T O),
        RegularAtDim (n := n) (openSection V (openPreimage T O)) p k)
      (P : BlowupTower
        (nativeManifold hk (openSection W O) (openSection_regular hW O))
        (nativeManifold hk (openSection V (openPreimage T O)) hS)),
      Lift hk (openSection W O) (hWc.preimage continuous_subtype_val) (openSection_regular hW O)
        (E.map ((Subtype.val : O→X) ⁻¹' ·)) (restrict O T)
        (openSection V (openPreimage T O)) hSc hS P ∧
      IsTowerIso (windowEquiv hk W hW hWc O) P (restrict (nativeWindow hk W hW O) Q)
        (endpointEquiv h O) := by
  obtain ⟨S,hSc,hS,P,χ,hSe,hLift,hIso,hPoint⟩:=open_lift_core h O
  subst S
  have hχ : χ=endpointEquiv h O := by
    ext p
    apply Subtype.ext
    exact (hPoint p).trans (endpointEquiv_val h O p).symm
  exact ⟨hSc,hS,P,hLift,hχ ▸ hIso⟩

/-- The SAME geometric closure on every original reference head/tail,
retaining the entire boundary born before that original cut. -/
theorem exists_original_reference_lift
    (h : Lift hk W hWc hW E T V hVc hV Q) (j : ℕ) :
    ∃(A : Set (BlowupTowerSplit.split T j).1)(hAc : IsClosed A)
      (hA : ∀x∈A,RegularAtDim (n := n) A x k)
      (e : (BlowupTowerSplit.split Q j).1=nativeManifold hk A hA),
      Lift hk W hWc hW E (BlowupTowerSplit.head T j) A hAc hA
        (recastTarget e (BlowupTowerSplit.head Q j)) ∧
      ∃hTail : Lift hk A hAc hA (boundary E (BlowupTowerSplit.head T j))
        (BlowupTowerSplit.tail T j) V hVc hV (recastSource e (BlowupTowerSplit.tail Q j)),
      ∀O : Opens (BlowupTowerSplit.split T j).1,
      ∃(hSc : IsClosed (openSection V (openPreimage (BlowupTowerSplit.tail T j) O)))
        (hS : ∀p∈openSection V (openPreimage (BlowupTowerSplit.tail T j) O),
          RegularAtDim (n := n) (openSection V (openPreimage (BlowupTowerSplit.tail T j) O)) p k)
        (P : BlowupTower
          (nativeManifold hk (openSection A O) (openSection_regular hA O))
          (nativeManifold hk (openSection V (openPreimage (BlowupTowerSplit.tail T j) O)) hS)),
        Lift hk (openSection A O) (hAc.preimage continuous_subtype_val) (openSection_regular hA O)
          ((boundary E (BlowupTowerSplit.head T j)).map
            ((Subtype.val : O→(BlowupTowerSplit.split T j).1) ⁻¹' ·))
          (restrict O (BlowupTowerSplit.tail T j))
          (openSection V (openPreimage (BlowupTowerSplit.tail T j) O)) hSc hS P ∧
        IsTowerIso (windowEquiv hk A hA hAc O) P
          (restrict (nativeWindow hk A hA O) (recastSource e (BlowupTowerSplit.tail Q j)))
          (endpointEquiv hTail O) := by
  obtain ⟨A,hAc,hA,e,hHead,hTail⟩:=
    HironakaActualNativeSectionOriginalCuts.Lift.original_head_tails h j
  exact ⟨A,hAc,hA,e,hHead,hTail,fun O=>exists_open_lift hTail O⟩

end
end Hironaka.HironakaDisjointNativeOpenLift

namespace Hironaka.HironakaDisjointNativeOpenLift
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOriginalCuts
  HironakaDisjointNativeReferenceWindow SubmanifoldChartedSpace SubmanifoldCodRestrict
  BlowupTowerIsomorphism BlowupRestrictOpen MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsInvariance BlowupStrictSubmanifold

variable {n k : ℕ} {X : CMfd.{0} n}

variable {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n := n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

/- Root-approved exact private point-law export, append-only and zero credit. -/
theorem endpointEquiv_val_native (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X)
    (p : nativeManifold hk (openSection V (openPreimage T O))
      (openSection_regular hV (openPreimage T O))) :
    (endpointEquiv h O p).val.val=p.val.val :=
  endpointEquiv_val h O p

end
end Hironaka.HironakaDisjointNativeOpenLift
