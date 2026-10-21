import TranscendentalNakamaye.Pending.HironakaNormalCrossingsSNCBlockCarrier
import TranscendentalNakamaye.Pending.HironakaNormalCrossingsOpenRestrictionSeparation

/-!
# The same coefficient phase has a global old/born NC carrier

Actual open trace coordinates glue without a chart certificate. Empty local
histories retain their literal empty born positions. This reconstructs the
whole transformed pair, without asserting any global old-count decrease.
Blueprint: `hironaka-normal-crossings-global-phase-carrier-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaNormalCrossingsGlobalPhaseCarrier
noncomputable section
open FirstPass FirstPass.BlowupSequences FirstPass.HolomorphicIdealSheaves
  NormalCrossings NormalCrossingsInvariance BlowupFlatCoordinates
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsSNCBlockCarrier
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  CoefficientIdeal CoefficientIdealRestriction MemberInterTowerAlong RestrictEmptyTower
  AnalyticSubsetOpens GermIdealOrder
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ}

/-- Genuine open traces construct the actual whole boundary-adapted carrier. -/
theorem boundaryAdapted_of_open_traces {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {H : Set X} {E : List (Set X)} (hH : IsClosed H) (hE : ∀ A∈E,IsClosed A)
    (hloc : ∀ x : X,∃ U : Opens X,x∈U ∧
      IsBoundaryAdaptedCarrier (n := n) ((Subtype.val : U→X) ⁻¹' H)
        (E.map (fun A=>(Subtype.val : U→X) ⁻¹' A))) :
    IsBoundaryAdaptedCarrier (n := n) H E := by
  refine ⟨hH,hE,fun x=>?_⟩
  obtain ⟨U,hxU,hU⟩ := hloc x
  let p : U := ⟨x,hxU⟩
  obtain ⟨Φ,S,D,hsrc,h0,hOld,hD,hinj,hBorn⟩ := hU.2.2 p
  let c : Fin E.length→Fin (E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)).length :=
    Fin.cast (List.length_map _).symm
  have hget (i : Fin E.length) :
      (E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)).get (c i)=(Subtype.val : U→X) ⁻¹' E.get i := by
    simp [c,List.get_eq_getElem]
  have hThrough (i : Fin E.length) (hi : x∈E.get i) :
      p∈(E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)).get (c i) := by
    rw [hget]
    exact hi
  have hInside {y : X} (hy : y∈flatDomain (M:=X) (y₀:=x) Φ) : y∈U :=
    mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
  refine ⟨Φ,S,(fun i=>D (c i)),hsrc.trans (chartAt_opens_target_subset p),h0,?_,?_,?_,?_⟩
  · intro y hy
    exact hOld ⟨y,hInside hy⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩
  · intro i hi
    exact hD (c i) (hThrough i hi)
  · intro i hi j hj he
    exact Fin.cast_injective _ (hinj (hThrough i hi) (hThrough j hj) he)
  · intro i hi y hy
    have hh := hBorn (c i) (hThrough i hi) ⟨y,hInside hy⟩
      ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩
    rw [hget] at hh
    exact hh

/-- True empty histories retain all literal appended empty born positions. -/
theorem boundaryAdapted_empty_tower {X : CMfd.{u} n} (M : MarkedIdeal n X)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsEmptyTower T→
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E
  | _,.refl,_ => h
  | _,.step T C π hπ,hT => by
      obtain ⟨hT,hC⟩ := hT
      have hPrev := boundaryAdapted_empty_tower M h T hT
      let hNC := isNormalCrossingsCarrier_of_boundaryAdapted hPrev
      have hZ : {x | n+1≤branchMultiplicity hNC x}=(∅ : Set _) := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hb := branchMultiplicity_le hNC x
        change n+1≤branchMultiplicity hNC x at hx
        omega
      have hπZ : IsBlowupAlong n {x | n+1≤branchMultiplicity hNC x} π := by
        rw [hZ,←hC]
        exact hπ
      have hn := boundaryAdapted_strict_highest hPrev (r:=n+1)
        (fun x=>(branchMultiplicity_le hNC x).trans (Nat.le_succ n)) hπZ
      rw [hZ,←hC] at hn
      exact hn

private theorem centresOver_of_centresIn {X : CMfd.{u} n} {S : Set X} (hS : IsClosed S) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresIn S T→CentresOver S T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,hT =>
      ⟨centresOver_of_centresIn hS T hT.1,fun _ hp=>strictAlong_subset_preimage T hS (hT.2 hp)⟩

private theorem split_zero {X Y : CMfd.{u} n} (T : BlowupTower X Y) :
    split T 0=⟨Y,T,.refl⟩ := by
  cases T <;> rfl

/-- A whole ORIGINAL-only phase produces the genuine GLOBAL transformed pair;
high old crossings outside current permitted cosupport need not disappear. -/
theorem exists_original_phase_global_old_born_carrier {X : CMfd.{u} n}
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r) :
    let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
    let Z := {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T ∧
      IsGeoTestTower M T ∧ CentresIn Z T ∧
      (geoTransformAlong M T).cosupp∩strictAlong T Z=∅ ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
  let Z := {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  obtain ⟨Y,T,hres,hTM,hTZ,hclear,hLocal⟩ :=
    exists_original_phase_current_local_carriers I hI d hd hK h hr hbound
  have hZ : IsClosed Z := isClosed_branchMultiplicity_superlevel _ _
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ,hI,isSNCDivisor_of_boundaryAdapted h,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor (isSNCDivisor_of_boundaryAdapted h)⟩
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hTM
  refine ⟨Y,T,hres,hTM,hTZ,hclear,?_⟩
  apply boundaryAdapted_of_open_traces (isClosed_strictAlong T h.1) hw.isSNCDivisor.1
  intro y
  have hRewrite (U : Opens X) :
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U→X) M) (restrict U T)=
        MarkedIdeal.pullback (Subtype.val : openPreimage T U→Y) (geoTransformAlong M T) :=
    geoTransformAlong_restrict U isClosedSubmanifold_univ hI T hTM
  by_cases hy : T.proj y∈Z
  · obtain ⟨U,B,hxU,_hUnion,hCurrent⟩ := hLocal (T.proj y) hy
    obtain ⟨hc,_hCount⟩ := hCurrent 0
    simp only [head] at hc
    rw [split_zero (restrict U T)] at hc
    refine ⟨openPreimage T U,hxU,?_⟩
    change IsBoundaryAdaptedCarrier (n := n)
      (strictAlong (restrict U T) ((Subtype.val : U→X) ⁻¹' H))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U→X) M) (restrict U T)).E at hc
    rw [strictAlong_restrict,hRewrite] at hc
    exact hc
  · let U : Opens X := ⟨Zᶜ,hZ.isOpen_compl⟩
    have hEmpty : IsEmptyTower (restrict U T) := isEmptyTower_restrict_of_centresOver U
      (by exact disjoint_compl_left) T (centresOver_of_centresIn hZ T hTZ)
    have hOrig := boundaryAdapted_open U h
    have hc := boundaryAdapted_empty_tower (MarkedIdeal.pullback (Subtype.val : U→X) M) hOrig
      (restrict U T) hEmpty
    refine ⟨openPreimage T U,hy,?_⟩
    rw [strictAlong_restrict,hRewrite] at hc
    exact hc

end
end TranscendentalNakamaye.Pending.HironakaNormalCrossingsGlobalPhaseCarrier
