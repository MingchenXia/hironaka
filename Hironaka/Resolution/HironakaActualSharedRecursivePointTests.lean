import Hironaka.Resolution.HironakaActualAnchoredRecursivePointTests
import Hironaka.Resolution.HironakaActualAnchoredSeedTotalFactor
import Hironaka.Resolution.HironakaActualProperOriginalTowerFactor
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels

/-!
# Two original records on one actual inherited point family

One ordinary reference record constructs the native recursive geometry before
all queried ideals and marks. Every query test, sharp whole/controlled order,
full old/horizontal/born boundary and original mixed-history dictionary is
derived on that same family. The ordinary two-record corollary needs only
shared original N/E and a common cosupport point. All original histories use
the SAME literal reference history value with their own entire ideals/marks.

Blueprint FIRST: `hironaka-actual-shared-recursive-point-tests.tex`.
The fixed-seed private sharpness and output notation reuse accepted mothers;
this module adds their shared-family integration, not another such engine.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSharedRecursivePointTests
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
  RestrictedIdealWeight NonmonomialOrderLocal
open HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci
open scoped ProductComplexManifold

private theorem chart_smooth {r : ℕ} {X : CMfd.{u} r}
    (e : OpenPartialHomeomorph X (ComplexModel r))
    (he : e∈atlas (ComplexModel r) X) :
    ∀z∈e.source,ContMDiffAt 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel r) ∞ e z := by
  have hmax:=IsManifold.subset_maximalAtlas (I:=𝓘(ℂ,ComplexModel r)) (n:=∞) he
  intro z hz
  exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (e.open_source.mem_nhds hz)

/-- LOCAL whole TOTAL-power sharpness. Every current guard is genuine geometry
or derived from the actual existing test; no whole chart mask is required. -/
private theorem same_seed_total_power_sharp {n : ℕ} {X : CMfd.{u} (n+1)}
    {C : Set X} [Fact (IsClosedSubmanifold (n+1) C)]
    (P : MarkedIdeal (n+1) X) (hN : IsClosedSubmanifold (n+1) P.N)
    (hI : P.ideal.IsCoherent) (hC : P.IsAdmissibleCentre C)
    (c : FlatChart (n+1) C)
    (hπ : IsBlowupAlong (n+1) C (blowupProj (n+1) C)) (hj : c.j=Fin.last n)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z)
    (hR : IsGeoTestTower (P.geoTransform C (blowupProj (n+1) C)) R)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (hz : z∈e.source)
    (hzN : z∈((P.geoTransform C (blowupProj (n+1) C)).geoTransformAlong R).N)
    (he0 : e z=0) (d : ℕ) :
    let A : BlowupTower X (CMfd.of (BlowupSpace (n+1) C)):=
      .step .refl C (blowupProj (n+1) C) hπ
    let F:=idealPow (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal d
    let Nt:=((P.geoTransform C (blowupProj (n+1) C)).geoTransformAlong R).N
    z∈cosupport (n+1) Nt F ((R.length+1)*d) ∧
      z∉cosupport (n+1) Nt F ((R.length+1)*d+1) := by
  dsimp only
  let A : BlowupTower X (CMfd.of (BlowupSpace (n+1) C)):=
    .step .refl C (blowupProj (n+1) C) hπ
  have hTotal:=anchored_seed_total_factor c hπ hj R e hA z hz
  cases R with
  | refl =>
    rcases hA with ⟨rfl,hAtlas⟩
    simp only [BlowupTower.length_refl,Nat.zero_add,Nat.one_mul,geoTransformAlong_refl] at hTotal ⊢
    have hzC : blowupProj (n+1) C z∈C := by
      apply (c.toFun_j_eq_zero_iff hz).mp
      rw [hj]
      exact congrArg (fun w : ComplexModel (n+1)=>w (Fin.last n)) he0
    have hSmooth : ∀v∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1))
        𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun v := by
      intro v hv
      exact chart_smooth (X:=CMfd.of (BlowupSpace (n+1) C)) c.homeo hAtlas v hv
    have hBorn:=GlueingTrivialAction.isLocalEquation_monomial hπ c.hsrc c.hflat c.hj
      c.isOpen_source (W:=c.toFun) hSmooth
      (fun v hv=>⟨hv.1,c.monomial_toFun hv⟩)
    rw [hj] at hBorn
    have hSharp:=exceptional_power_order_at_strict hπ hN hC.subset_N z hzN hzC d
    have hWhole (g : _→ℂ) :
        (idealPow (BlowupTowerTransforms.exceptionalDivisor (A.append .refl)).ideal d).mem z g ↔
        (idealPow (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
          (vanishingIdeal (n:=n+1) C)) d).mem z g := by
      have hh:=((hTotal.2 d g).trans (hBorn.idealPow_mem_iff d z hz g).symm)
      simpa only [BlowupTower.length_refl,Nat.zero_add,Nat.one_mul,hj,exceptionalDivisor_ideal] using hh
    constructor
    · exact ⟨hzN,fun g hg=>hSharp.1.2 g ((hWhole g).mp hg)⟩
    · intro h
      exact hSharp.2.1 ⟨hzN,fun g hg=>h.2 g ((hWhole g).mpr hg)⟩
  | step R C2 π2 hπ2 =>
    obtain ⟨he,eold,y,Φ,hPrev,hC2,hy,hy0,hsrc,hflat,_hInherited,hNative⟩:=hA
    have hBorn:=GlueingTrivialAction.isLocalEquation_monomial hπ2 hsrc hflat
      (Nat.zero_le (Fin.last n).val) e.open_source (chart_smooth e he) hNative
    have hzC : π2 z∈C2 := by
      apply (hflat (hNative z hz).1.1 (hNative z hz).1.2).mpr
      rw [←(hNative z hz).2,he0]
      intro i hi
      simp [monomial_apply]
    have hFirst : IsGeoTestTower P A:=⟨trivial,hC⟩
    have hQ1:=MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hN hI A hFirst
    have hQprev:=MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hQ1.1 hQ1.2 R hR.1
    have hCN : C2⊆((P.geoTransform C (blowupProj (n+1) C)).geoTransformAlong R).N :=
      fun v hv=>(hR.2.2.1 hv).1
    let a:=((BlowupTower.step R C2 π2 hπ2).length+1)*d
    have hSharp:=exceptional_power_order_at_strict hπ2 hQprev.1 hCN z hzN hzC a
    have hWhole (g : _→ℂ) :
        (idealPow (BlowupTowerTransforms.exceptionalDivisor
          (A.append (.step R C2 π2 hπ2))).ideal d).mem z g ↔
        (idealPow (GermIdeal.pullback (m:=n+1) π2 (vanishingIdeal (n:=n+1) C2)) a).mem z g := by
      have hh:=((hTotal.2 d g).trans (hBorn.idealPow_mem_iff a z hz g).symm)
      simpa only [exceptionalDivisor_ideal] using hh
    constructor
    · exact ⟨hzN,fun g hg=>hSharp.1.2 g ((hWhole g).mp hg)⟩
    · intro h
      exact hSharp.2.1 ⟨hzN,fun g hg=>h.2 g ((hWhole g).mpr hg)⟩

private theorem enat_from_sharp {r : ℕ} {X : CMfd.{u} r}
    (N : Set X) (I : GermIdeal r X) (x : X) (a : ℕ)
    (hHol : ∀g,I.mem x g→HolomorphicAt r g x)
    (hGood : x∈cosupport r N I a) (hBad : x∉cosupport r N I (a+1)) :
    GermIdealOrder.order r N I x=(a : ℕ∞) := by
  apply le_antisymm
  · apply ENat.lt_natCast_add_one_iff.mp
    apply lt_of_not_ge
    intro h
    exact hBad ⟨hGood.1,(le_order_iff hHol).mp
      (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
  · exact (le_order_iff hHol).mpr hGood.2

private instance point_closed_fact {a : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X] (x : X) :
    Fact (IsClosedSubmanifold a ({x} : Set X)) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1⟩

private theorem nat_trace_from_sharp {n : ℕ} {X : CMfd.{u} n}
    (N : Set X) (I : GermIdeal n X) (hI : I.IsCoherent) (x : X) (a : ℕ)
    (hGood : x∈cosupport n N I a) (hBad : x∉cosupport n N I (a+1)) :
    ordinaryTraceOrder N I x=a := by
  apply Nat.le_antisymm
  · change nmOrd (ordinaryTraceMarked N I) x≤a
    apply nmOrd_le_of_notMem
    rw [ordGe_ordinaryTraceMarked_eq_cosupport N I hI (a+1)]
    exact hBad
  · cases a with
    | zero => exact Nat.zero_le _
    | succ a =>
      change a+1≤nmOrd (ordinaryTraceMarked N I) x
      exact succ_le_nmOrd_of_mem (𝔪:=ordinaryTraceMarked N I) (y:=x)
        ⟨a+1,by rw [ordGe_ordinaryTraceMarked_eq_cosupport N I hI (a+1+1)];exact hBad⟩
        (by rw [ordGe_ordinaryTraceMarked_eq_cosupport N I hI (a+1)];exact hGood)

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

/-- The SAME reference projection-tower history evaluates the whole native
record for every queried original ideal and mark on the shared N/E. -/
theorem shared_projection_history_record {n : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (I : GermIdeal n X) (d : ℕ)
    {Y : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Y) :
    let M : MarkedIdeal n X := ⟨M0.N, M0.E, I, d⟩
    HironakaActualMixedTestPowerNormalization.record M
      (HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T) =
      (projectionTest M).geoTransformAlong T := by
  dsimp only
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    change (HironakaActualMixedTestPowerNormalization.record
      (⟨M0.N, M0.E, I, d⟩ : MarkedIdeal n X)
      (HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T)).geoTransform C π = _
    rw [ih]
    rfl

/-- Original testhood on ONE literal mixed history is exactly native testhood
for each queried original ideal/mark. -/
theorem shared_projection_history_test_iff {n : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (I : GermIdeal n X) (d : ℕ)
    {Y : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Y) :
    let M : MarkedIdeal n X := ⟨M0.N, M0.E, I, d⟩
    HironakaActualMixedTestPowerNormalization.IsTest M
      (HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T) ↔
      IsGeoTestTower (projectionTest M) T := by
  dsimp only
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    change (HironakaActualMixedTestPowerNormalization.IsTest
      (⟨M0.N, M0.E, I, d⟩ : MarkedIdeal n X)
      (HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T) ∧
      (HironakaActualMixedTestPowerNormalization.record
        (⟨M0.N, M0.E, I, d⟩ : MarkedIdeal n X)
        (HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T)).IsAdmissibleCentre C) ↔ _
    rw [shared_projection_history_record, ih]
    rfl


/-- PRIVATE fixed-seed join: the already existing query test and the actual
reference ALL-I cut callback derive query orders and next admissibility.
The public ordinary producer internally supplies every premise. -/
private theorem fixed_query_controlled_order {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (hπ : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (hcj : c.j=Fin.last n)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1)
      ({(x,0)} : Set (projectionAmbient X)))) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (hz : z∈e.source) (he0 : e z=0)
    (hR : IsGeoTestTower ((projectionTest M).geoTransform
      ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) R)
    (hCuts : wholeTailCuts M.N (((projectionTest M).geoTransform
      ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))).geoTransformAlong R).N x z R) :
    controlledTailOutput M hM x hx R e z := by
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let P:=projectionTest M
  let Q1:=P.geoTransform C π1
  let A : BlowupTower (CMfd.of (projectionAmbient X)) Y1:=.step .refl C π1 hπ
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
  have hP:=projection_test_isInvDomain M hM
  have hC : P.IsAdmissibleCentre C:=(projection_point_centre M hM x hx).1
  have hFirst : IsGeoTestTower P A:=⟨trivial,hC⟩
  have hT : IsGeoTestTower P T:=
    (isGeoTestTower_append_iff P A R).mpr ⟨hFirst,hR⟩
  have hRecord : Q=P.geoTransformAlong T:=(geoTransformAlong_append P A R).symm
  have hQ1 : IsInvDomain (k+1) Q1:=isInvDomain_geoTransformAlong hP A hFirst
  have hdQ1 : Q1.d=M.d:=rfl
  have hLength : Q1.E.length=M.E.length+2:=by
    rw [length_E_geoTransform]
    have hh : P.E.length=M.E.length+1 :=
      (projection_test_dictionary M hM).2.2.2.2.1
    rw [hh]
  have hQ : IsInvDomain (k+1) Q:=isInvDomain_geoTransformAlong hQ1 R hR
  have hdQ : Q.d=M.d:=(d_geoTransformAlong Q1 R).trans hdQ1
  have hLen : Q.E.length=M.E.length+2+R.length := by
    rw [length_E_geoTransformAlong, hLength]
  have hBComp : B=GermIdeal.pullback (m:=n+1) T.proj P.ideal := by
    change GermIdeal.pullback (m:=n+1) R.proj
      (GermIdeal.pullback (m:=n+1) π1 P.ideal)=_
    have hProj : T.proj=π1∘R.proj := by
      simp only [T,A,BlowupTower.proj_append,BlowupTower.proj_step,
        BlowupTower.proj_refl,Function.id_comp]
    rw [hProj,pullback_comp hπ.contMDiff R.contMDiff_proj hP.isWellFormed.isCoherent]
  have hdP : P.d=M.d:=(projection_test_dictionary M hM).2.2.1
  have hFactors:=original_tower_factor P hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent T hT
  have hBProd : RestrictLe Q.N B (F.mul Q.ideal) := by
    simpa only [←hRecord,←hBComp,hdP] using hFactors.1
  have hProdB : RestrictLe Q.N (F.mul Q.ideal) B := by
    simpa only [←hRecord,←hBComp,hdP] using hFactors.2
  have hWholeAt:=hCuts
  have hzN : z∈Q.N:=hWholeAt.2.1
  have hSourceCrit (a : ℕ) : x∈cosupport n M.N M.ideal a ↔ a≤ρ :=
    ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.isNonzeroAlongAt (M.cosupp_subset_N hx) a
  have hdρ : M.d≤ρ := (hSourceCrit M.d).mp hx
  have hGoodSource : x∈cosupport n M.N M.ideal ρ := (hSourceCrit ρ).mpr le_rfl
  have hBadSource : x∉cosupport n M.N M.ideal (ρ+1) :=
    fun h=>Nat.not_succ_le_self ρ ((hSourceCrit (ρ+1)).mp h)
  have hQICuts:=hCuts.2.2 M.ideal hM.isWellFormed.isCoherent
  have hBGood : z∈cosupport (n+1) Q.N B μ := (hQICuts.2.2 ρ).1.mpr hGoodSource
  have hBBad : z∉cosupport (n+1) Q.N B (μ+1) := by
    intro h
    apply hBadSource
    apply ((hQICuts.2.2 ρ).2 0 (Nat.zero_le _)).mp
    simpa only [Nat.add_zero] using h
  have hTotal:=anchored_seed_total_factor c hπ hcj R e hA z hz
  have hFGen : ∀f : Z→ℂ,F.mem z f↔IsInSpanAt (n:=n+1)
      (·=fun v=>e v (Fin.last n)^ν) z f := hTotal.2 M.d
  obtain ⟨hFGood,hFBad⟩:=same_seed_total_power_sharp P hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent hC c hπ hcj R hR e hA z hz hzN he0 M.d
  have hFOrd:=enat_from_sharp Q.N F z ν
    (fun _ hf=>GermIdealOrder.holomorphicAt_of_mem_idealPow hf) hFGood hFBad
  have hSplit : M.d+(ρ-M.d)=ρ:=Nat.add_sub_of_le hdρ
  have hSum : ν+s=μ := by
    dsimp only [ν,s,μ]
    calc
      q*M.d+(ρ+q*(ρ-M.d))=ρ+q*(M.d+(ρ-M.d)) := by ring
      _=ρ+q*ρ := by rw [hSplit]
      _=(q+1)*ρ := by ring
  have hνμ : ν≤μ:=by omega
  have hDiff : μ-ν=s:=by omega
  have hProductGood : z∈cosupport (n+1) Q.N (F.mul Q.ideal) μ:=
    cosupport_subset_of_restrictLe hProdB μ hBGood
  have hQGood : z∈cosupport (n+1) Q.N Q.ideal s := by
    have hh:=mem_cosupport_of_mem_cosupport_mul_along hQ.isWellFormed.isClosedSubmanifold_N.2
      (fun _ _ hf=>GermIdealOrder.holomorphicAt_of_mem_idealPow hf)
      (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hf)
      hνμ hProductGood hFBad
    simpa only [hDiff] using hh
  have hQBad : z∉cosupport (n+1) Q.N Q.ideal (s+1) := by
    intro h
    have hProd:=inter_cosupport_subset_cosupport_mul ν (s+1) ⟨hFGood,h⟩
    have hAdd : ν+(s+1)=μ+1:=by omega
    rw [hAdd] at hProd
    exact hBBad (cosupport_subset_of_restrictLe hBProd (μ+1) hProd)
  have hQOrd:=enat_from_sharp Q.N Q.ideal z s
    (fun _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hf)
    hQGood hQBad
  have hCrit (a : ℕ) : z∈cosupport (n+1) Q.N Q.ideal a ↔
      a≤ordinaryTraceOrder Q.N Q.ideal z :=
    ordinaryTraceOrder_cosupport_iff hQ.isWellFormed.isClosedSubmanifold_N
      hQ.isWellFormed.isCoherent hQ.isNonzeroAlongAt hzN a
  have hQNat : ordinaryTraceOrder Q.N Q.ideal z=s := by
    apply Nat.le_antisymm
    · by_contra h
      exact hQBad ((hCrit (s+1)).mpr (by omega))
    · exact (hCrit s).mp hQGood
  have hds : M.d≤s:=by dsimp only [s];omega
  have hzQ : z∈Q.cosupp := by
    change z∈cosupport (n+1) Q.N Q.ideal Q.d
    rw [hdQ]
    exact cosupport_anti hds hQGood
  have hPoint : Q.IsAdmissibleCentre ({z} : Set Z) :=
    ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence z).1,
      (fun y hy=>by rw [mem_singleton_iff.mp hy];exact hzQ),
      hasNormalCrossings_singleton z hQ.isWellFormed.isSNCDivisor⟩
  dsimp only [controlledTailOutput]
  exact ⟨hT,hRecord,hQ,hdQ,hLen,hBComp,hBProd,hProdB,hFGen,hFGood,hFBad,hFOrd,
    hSum,hQGood,hQBad,hQNat,hQOrd,hds,hzQ,hPoint⟩

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

private abbrev sharedFamilyOutput {n k0 : ℕ} {X : CMfd.{u} n}
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
      ∀r : ℕ,queryAtState M0 x hπ1 c SE U (F r) I d hM hx


/-- Entire carrier and boundary depend only on the one fixed history's
original carrier and labels, before any query-test premise. -/
private theorem shared_geometry {n : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (I : GermIdeal n X) (d : ℕ)
    {Y : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Y) :
    let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
    ((projectionTest M).geoTransformAlong T).N=
      ((projectionTest M0).geoTransformAlong T).N ∧
    ((projectionTest M).geoTransformAlong T).E=
      ((projectionTest M0).geoTransformAlong T).E := by
  dsimp only
  have hQ:=shared_projection_history_record M0 I d T
  have h0:=HironakaActualProjectionTowerHistory.record_projectionTowerHistory M0 T
  dsimp only at hQ
  let H:=HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  constructor
  · calc
      ((projectionTest M).geoTransformAlong T).N =
          (HironakaActualMixedTestPowerNormalization.record M H).N :=
        (congrArg (fun L : MarkedIdeal (n+1) Y=>L.N) hQ).symm
      _ = (HironakaActualMixedTestPowerNormalization.record M0 H).N := rfl
      _ = ((projectionTest M0).geoTransformAlong T).N :=
        congrArg (fun L : MarkedIdeal (n+1) Y=>L.N) h0
  · calc
      ((projectionTest M).geoTransformAlong T).E =
          (HironakaActualMixedTestPowerNormalization.record M H).E :=
        (congrArg (fun L : MarkedIdeal (n+1) Y=>L.E) hQ).symm
      _ = (HironakaActualMixedTestPowerNormalization.record M0 H).E := rfl
      _ = ((projectionTest M0).geoTransformAlong T).E :=
        congrArg (fun L : MarkedIdeal (n+1) Y=>L.E) h0


/-- Projection-only base on the SAME literal reference history, with every
whole original query and its genuine first singleton admissibility. -/
private theorem initial_query {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X) (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp) :
    initialQueryOutput M0 x I d hM hx := by
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let P:=projectionTest M
  let p : projectionAmbient X:=(x,0)
  have hb:=HironakaActualAnchoredFirstPointBase.projection_first_point_base M hM x hx
  rcases hb with ⟨hQueries,hP,hPN,hPI,hPd,hPE,hPLen,_hpN,hpCos,hdρ,hSourceOrder,
    hPNat,hPOrder,_hRest⟩
  let T : BlowupTower (projectionAmbient X) (projectionAmbient X):=.refl
  have hTest:=(shared_projection_history_test_iff M0 I d T).mpr True.intro
  have hRec:=shared_projection_history_record M0 I d T
  have hClock:=HironakaActualProjectionTowerHistory.projectionTowerHistory_dictionary M0 T
  dsimp only [initialQueryOutput]
  exact ⟨hQueries,hP,hpCos,hPN,hPI,hPd,hPE,hPLen,hdρ,hSourceOrder,hPNat,hPOrder,
    (projection_point_centre M hM x hx).1,hTest,hRec,hClock.1,hClock.2.1,hClock.2.2.1⟩

private theorem whole_query_orders {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1)
      ({(x,0)} : Set (projectionAmbient X)))) Z)
    (Nt : Set Z) (z : Z) (hCuts : wholeTailCuts M.N Nt x z R) :
    let B:=GermIdeal.pullback (m:=n+1) R.proj
      (GermIdeal.pullback (m:=n+1) (blowupProj (n+1)
        ({(x,0)} : Set (projectionAmbient X)))
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal))
    let ρ:=ordinaryTraceOrder M.N M.ideal x
    ordinaryTraceOrder Nt B z=(R.length+2)*ρ ∧
      GermIdealOrder.order (n+1) Nt B z=(((R.length+2)*ρ : ℕ) : ℕ∞) := by
  dsimp only
  let B:=GermIdeal.pullback (m:=n+1) R.proj
    (GermIdeal.pullback (m:=n+1) (blowupProj (n+1)
      ({(x,0)} : Set (projectionAmbient X)))
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal))
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  have hCrit (a : ℕ) : x∈cosupport n M.N M.ideal a ↔ a≤ρ :=
    ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.isNonzeroAlongAt (M.cosupp_subset_N hx) a
  have hGoodSource : x∈cosupport n M.N M.ideal ρ := (hCrit ρ).mpr le_rfl
  have hBadSource : x∉cosupport n M.N M.ideal (ρ+1) :=
    fun h=>Nat.not_succ_le_self ρ ((hCrit (ρ+1)).mp h)
  have hQI:=hCuts.2.2 M.ideal hM.isWellFormed.isCoherent
  have hGood : z∈cosupport (n+1) Nt B ((R.length+2)*ρ) :=
    (hQI.2.2 ρ).1.mpr hGoodSource
  have hBad : z∉cosupport (n+1) Nt B ((R.length+2)*ρ+1) := by
    intro h
    apply hBadSource
    apply ((hQI.2.2 ρ).2 0 (Nat.zero_le _)).mp
    simpa only [Nat.add_zero] using h
  exact ⟨nat_trace_from_sharp Nt B hQI.2.1 z _ hGood hBad,
    enat_from_sharp Nt B z _
      (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hQI.2.1 hg) hGood hBad⟩

private abbrev sharpTailOutput {n : ℕ} {X : CMfd.{u} n}
    {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    {Z : CMfd.{u} (n+1)} (M : MarkedIdeal n X) (g : X→ℂ) (ρ : ℕ)
    (Nt : Set Z) (z : Z) (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z) : Prop :=
  let κ : Z→X:=(Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj
  let B:=GermIdeal.pullback (m:=n+1) R.proj
    (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal))
  let μ:=(R.length+2)*ρ
  z∈cosupport (n+1) Nt B μ ∧ z∉cosupport (n+1) Nt B (μ+1) ∧
    ordinaryTraceOrder Nt B z=μ ∧ GermIdealOrder.order (n+1) Nt B z=(μ : ℕ∞) ∧
    B.mem z (g∘κ) ∧ VanishesToOrderOn (n+1) Nt z μ (g∘κ) ∧
      ¬VanishesToOrderOn (n+1) Nt z (μ+1) (g∘κ)

private abbrev familyTailDictionary {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (g : X→ℂ) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState
      (Y1:=CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M).geoTransform ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo) : Prop :=
  let Z:=s.1
  let R:=s.2.1
  let e:=s.2.2.1
  let z:=tailPoint s
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M hM x hx).2
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let T:=A.append R
  let Q:=((projectionTest M).geoTransform C π1).geoTransformAlong R
  let H:=HironakaActualProjectionTowerHistory.projectionTowerHistory M T
  let V:=e.source∩R.proj ⁻¹' (U∩c.source)
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let q:=R.length+1
  wholeTailCuts M.N Q.N x z R ∧
  sharpTailOutput M g ρ Q.N z R ∧
  controlledTailOutput M hM x hx R e z ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H ∧
  HironakaActualMixedTestPowerNormalization.record M H=Q ∧
  HironakaActualMixedTestPowerNormalization.baseMap H=
    (Prod.fst : projectionAmbient X→X)∘T.proj ∧
  HironakaActualMixedTestPowerNormalization.baseMap H z=x ∧
  HironakaActualMixedTestPowerNormalization.length H=q+1 ∧
  HironakaActualMixedTestPowerNormalization.projections H=1 ∧
  T.length=q ∧ recordMark Z Q=M.d ∧
  (recordBoundary Z Q).length=M.E.length+1+q ∧
  (ρ=M.d→ ordinaryTraceOrder Q.N Q.ideal z=M.d) ∧
  IsOpen V ∧ z∈V ∧
  (recordBoundary Z Q).map (fun K=>V∩K)=
    List.ofFn (fun i : Fin M.E.length=>
      {v : Z | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) ++
      [(∅ : Set Z)] ++ List.replicate R.length (∅ : Set Z) ++
      [V∩{v | e v (Fin.last n)=0}]


/-- The query dictionary is assembled only after its actual native test on
this SAME existing reference state has been established. -/
private theorem query_at_existing_state {n k0 k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (hM0 : IsInvDomain k0 M0) (x : X) (hx0 : x∈M0.cosupp)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (g : X→ℂ)
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (hRef : familyTailDictionary M0 hM0 x hx0 c g SE U s)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (hcj : c.j=Fin.last n)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp)
    (hR : IsGeoTestTower ((projectionTest (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X)).geoTransform
      ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) s.2.1) :
    queryAtState M0 x hπ1 c SE U s I d hM hx := by
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let R:=s.2.1
  let e:=s.2.2.1
  let z:=tailPoint s
  let T:=A.append R
  let Q:=((projectionTest M).geoTransform C π1).geoTransformAlong R
  let Q0:=((projectionTest M0).geoTransform C π1).geoTransformAlong R
  have hGeometry : Q.N=Q0.N ∧ Q.E=Q0.E := by
    have hG:=shared_geometry M0 I d T
    simpa only [T,geoTransformAlong_append,A,geoTransformAlong_step,geoTransformAlong_refl] using hG
  have hCuts : wholeTailCuts M.N Q.N x z R := by
    rw [hGeometry.1]
    exact hRef.1
  have hs:=s.2.2.2.property
  have hCtl:=fixed_query_controlled_order M hM x hx c hπ1 hcj
    R e hs.1 z hs.2.2.1 hs.2.2.2 hR hCuts
  have hOrders:=whole_query_orders M hM x hx R Q.N z hCuts
  have hControlCopy:=hCtl
  rcases hControlCopy with ⟨hT,hQ,_hDom,hMark,_hELen,_hB,_hLeft,_hRight,
    _hFGen,_hFGood,_hFBad,_hFOrd,_hSum,_hGood,_hBad,hNat,_hOrd,_hd,_hCos,_hAdmiss⟩
  have hSharedTest:=(shared_projection_history_test_iff M0 I d T).mpr hT
  have hSharedRecord:=(shared_projection_history_record M0 I d T).trans hQ.symm
  rcases hRef with ⟨_hRefCuts,_hRefSharp,_hRefCtl,_hRefTest,_hRefRecord,
    hMap,hPoint,hHLength,hProjections,hTLength,_hRefMark,hELength,_hRefEqual,
    hOpen,hOrigin,hWord⟩
  dsimp only [queryAtState]
  refine ⟨hR,hCuts,hOrders.1,hOrders.2,hCtl,hSharedTest,hSharedRecord,
    hGeometry.1,hGeometry.2,hMap,hPoint,hHLength,hProjections,hTLength,hMark,
    ?_,?_,hOpen,hOrigin,?_⟩
  · rw [hGeometry.2]
    exact hELength
  · intro hρ
    rw [hNat,hρ,Nat.sub_self,Nat.mul_zero,Nat.add_zero]
  · rw [hGeometry.2]
    exact hWord
/-- One actual inherited family is fixed before EVERY queried original ideal
and mark. Each queried native test is then derived on its same prefixes. -/
theorem exists_shared_recursive_point_tests {n k0 : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (hM0 : IsInvDomain k0 M0) (x : X) (hx0 : x∈M0.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M0.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      sharedFamilyOutput M0 hM0 x hx0 Φ Φs c SN SE U := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hFamily⟩:=
    HironakaActualAnchoredRecursivePointTests.exists_original_anchored_recursive_point_tests
      M0 hM0 x hx0
  rcases hFamily with ⟨hSeed,_g,_hg,_hgBad,h0,chooseNext,_hZero,hLength,_hSuccessor,hDictionary⟩
  have hWhole : wholeCutsOutput M0 hM0 x hx0 Φ Φs c SN SE U:=hSeed.1.1.1.1
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M0).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M0 hM0 x hx0).2
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let Next : NativeTailState Q0 a→NativeTailState Q0 a:=fun s=>by
    rcases chooseNext s with ⟨c2,hπ2,_hCentre,_hCodim,_hPivot,hSource,hZero,_hProjects,_hVector,hTest,hChain⟩
    exact ⟨CMfd.of (n:=n+1) (BlowupSpace (n+1) ({tailPoint s} : Set s.1)),
      .step s.2.1 ({tailPoint s} : Set s.1)
        (blowupProj (n+1) ({tailPoint s} : Set s.1)) hπ2,
      c2.homeo,⟨c2.invFun 0,hChain,hTest,hSource,hZero⟩⟩
  let s0 : NativeTailState Q0 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
  let F : ℕ→NativeTailState Q0 a:=Nat.rec s0 (fun _ s=>Next s)
  have hFLength : ∀r : ℕ,(F r).2.1.length=r:=hLength
  change ∀r : ℕ,familyTailDictionary M0 hM0 x hx0 c _g SE U (F r) at hDictionary
  have hNextGeometry : ∀s,sameNextGeometry Q0 a s (Next s) := by
    intro s
    dsimp only [Next]
    rcases chooseNext s with ⟨c2,hπ2,hCentre,hCodim,hPivot,hSource,hZero,hProjects,hVector,hTest,hChain⟩
    exact ⟨c2,hπ2,hCentre,hCodim,hPivot,hSource,hZero,hProjects,hVector,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩
  refine ⟨Φ,Φs,c,SN,SE,U,hWhole,?_⟩
  dsimp only [sharedFamilyOutput]
  refine ⟨h0,Next,hNextGeometry,rfl,hFLength,(fun _=>rfl),?_⟩
  intro I d k hM hx
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let Qfirst : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C π1
  let QAt : (r : ℕ)→MarkedIdeal (n+1) (F r).1:=
    fun r=>Qfirst.geoTransformAlong (F r).2.1
  let RefAt : (r : ℕ)→MarkedIdeal (n+1) (F r).1:=
    fun r=>Q0.geoTransformAlong (F r).2.1
  have hGeometry (r : ℕ) : (QAt r).N=(RefAt r).N ∧ (QAt r).E=(RefAt r).E := by
    have hG:=shared_geometry M0 I d (A.append (F r).2.1)
    simpa only [geoTransformAlong_append,A,geoTransformAlong_step,geoTransformAlong_refl] using hG
  have hCuts (r : ℕ) : wholeTailCuts M.N (QAt r).N x (tailPoint (F r)) (F r).2.1 := by
    rw [(hGeometry r).1]
    exact (hDictionary r).1
  have hTests : ∀r : ℕ,IsGeoTestTower Qfirst (F r).2.1 := by
    intro r
    induction r with
    | zero => trivial
    | succ r ih =>
      let s:=F r
      have hs:=s.2.2.2.property
      have hCtl:=fixed_query_controlled_order M hM x hx c hπ1 hWhole.2.2.2.2.1
        s.2.1 s.2.2.1 hs.1 (tailPoint s) hs.2.2.1 hs.2.2.2 ih (hCuts r)
      rcases hCtl with ⟨_hT,_hQ,_hDom,_hMark,_hELen,_hB,_hLeft,_hRight,
        _hFGen,_hFGood,_hFBad,_hFOrd,_hSum,_hGood,_hBad,_hNat,_hOrd,_hd,_hCos,hAdmiss⟩
      change IsGeoTestTower Qfirst (Next (F r)).2.1
      dsimp only [Next]
      rcases chooseNext (F r) with ⟨c2,hπ2,hCentre,hCodim,hPivot,hSource,hZero,hProjects,hVector,hTest,hChain⟩
      exact ⟨ih,hAdmiss⟩
  refine ⟨initial_query M0 x I d hM hx,?_⟩
  intro r
  exact query_at_existing_state M0 hM0 x hx0 c SE U _g (F r) (hDictionary r)
    hπ1 hWhole.2.2.2.2.1 I d hM hx (hTests r)

private abbrev twoRecordFamilyOutput {n k1 k2 : ℕ} {X : CMfd.{u} n}
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
      queryAtState M1 x hπ1 c SE U (F r) M1.ideal M1.d hM1 hx1 ∧
      queryAtState M1 x hπ1 c SE U (F r) M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2)

/-- Only TWO ordinary original records, their common point and identical whole
N/E are inputs. The first record is an internal reference for ONE family;
both genuine test/order dictionaries use its same history values. -/
theorem exists_two_record_shared_recursive_point_tests {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 M2 : MarkedIdeal n X) (hM1 : IsInvDomain k1 M1) (hM2 : IsInvDomain k2 M2)
    (x : X) (hx1 : x∈M1.cosupp) (hx2 : x∈M2.cosupp)
    (hN : M2.N=M1.N) (hE : M2.E=M1.E) :
    ∃(h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2)
      (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M1.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      twoRecordFamilyOutput M1 hM1 x hx1 M2 hM2 hx2 h2 Φ Φs c SN SE U := by
  have h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2 := by
    cases M2 with
    | mk N2 E2 I2 d2 =>
      change N2=M1.N at hN
      change E2=M1.E at hE
      cases hN
      cases hE
      rfl
  obtain ⟨Φ,Φs,c,SN,SE,U,hFamily⟩:=exists_shared_recursive_point_tests M1 hM1 x hx1
  rcases hFamily with ⟨hWhole,h0,Next,hNext,hZero,hLen,hSucc,hQueries⟩
  refine ⟨h2,Φ,Φs,c,SN,SE,U,hWhole,?_⟩
  dsimp only [twoRecordFamilyOutput]
  refine ⟨h0,Next,hNext,hZero,hLen,hSucc,?_⟩
  have hQuery1:=hQueries M1.ideal M1.d k1 hM1 hx1
  have hQuery2:=hQueries M2.ideal M2.d k2 (h2.symm ▸ hM2) (h2.symm ▸ hx2)
  exact ⟨hQuery1.1,hQuery2.1,fun r=>⟨hQuery1.2 r,hQuery2.2 r⟩⟩

end
end Hironaka.HironakaActualSharedRecursivePointTests
