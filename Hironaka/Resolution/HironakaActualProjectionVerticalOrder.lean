import Hironaka.Resolution.HironakaActualProjectionVerticalFunctionOrder
import Hironaka.Resolution.HironakaActualExceptionalTestRecord
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Resolution.HironakaDivisorPowers

/-! P05-B. Whole original ideal cuts at ONE genuine vertical witness,
then native proper-factor cancellation. Blueprint FIRST. No future history,
raw order or CAN claim; all native numerical limits remain unchanged. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u v
namespace Hironaka.HironakaActualProjectionVerticalOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupSNCTransform BlowupStrictSubmanifold
  NormalCrossings BlowupMonomialCharts HironakaSmoothSubmersionUniversalBlowupChartEquality
  ProductComplexManifold MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaActualProjectionTestRecord HironakaActualProjectionVerticalBlowupChart
  HironakaActualProjectionVerticalFunctionOrder HironakaSharpOriginalProductTraceOrder
  HironakaActualExceptionalTestRecord HironakaSmoothSubmersionContactParameterCoefficientIdeals
  RelativePrincipalizationSpan InvertibleIdealQuotient IdealWeightPowers GermIdealOrder
  GermIdealPullbackCalculus IdealOrderArithmetic OrderTaylor CompanionReductionAlong DivisorExponentAlong
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  BlowupExceptionalDivisor MemberTraceIdealAlong HironakaSharpSingleBoundaryTraceCentre
  SmoothCentreLocus MonomialPart BlowupFlatCoordinates
open scoped ProductComplexManifold

private theorem order_from_sharp {n : ℕ} {X : CMfd.{u} n}
    (N : Set X) (I : GermIdeal n X) (x : X) (q : ℕ)
    (hI : ∀g,I.mem x g→HolomorphicAt n g x)
    (hGood : x∈cosupport n N I q) (hBad : x∉cosupport n N I (q+1)) :
    GermIdealOrder.order n N I x=(q : ℕ∞) := by
  apply le_antisymm
  · apply ENat.lt_natCast_add_one_iff.mp
    apply lt_of_not_ge
    intro h
    apply hBad
    exact ⟨hGood.1,(le_order_iff hI).mp
      (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
  · exact (le_order_iff hI).mpr hGood.2

private theorem nat_order_from_sharp {n : ℕ} {X : CMfd.{u} n}
    {N : Set X} {I : GermIdeal n X} (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hne : ∀y∈N,IsNonzeroAlongAt N I y) {x : X} (hx : x∈N) (q : ℕ)
    (hGood : x∈cosupport n N I q) (hBad : x∉cosupport n N I (q+1)) :
    ordinaryTraceOrder N I x=q := by
  apply Nat.le_antisymm
  · by_contra h
    apply hBad
    exact (ordinaryTraceOrder_cosupport_iff hN hI hne hx (q+1)).mpr (by omega)
  · exact (ordinaryTraceOrder_cosupport_iff hN hI hne hx q).mp hGood

/-- Genuine ordinary blowup geometry derives the sharp order of the ENTIRE
exceptional power on its actual strict proper carrier. -/
theorem exceptional_power_order_at_strict {n : ℕ} {X Y : CMfd.{u} n}
    {C N : Set X} {π : Y→X} (hπ : IsBlowupAlong n C π)
    (hN : IsClosedSubmanifold n N) (hCN : C⊆N)
    (z : Y) (hzN : z∈geoStrictTransform π C N) (hzC : π z∈C) (e : ℕ) :
    let W:=geoStrictTransform π C N
    let J:=GermIdeal.pullback (m:=n) π (vanishingIdeal (n:=n) C)
    z∈cosupport n W (idealPow J e) e ∧
      z∉cosupport n W (idealPow J e) (e+1) ∧
      GermIdealOrder.order n W (idealPow J e) z=(e : ℕ∞) := by
  let W:=geoStrictTransform π C N
  let D:=π ⁻¹' C
  let J:=GermIdeal.pullback (m:=n) π (vanishingIdeal (n:=n) C)
  have hn:=SimultaneousNormalCrossings.pos_of_isBlowupAlong hπ hzC
  have hE:=isSNCDivisor_preimage_centre hπ
  have hT:=isTransverse_preimage_centre hπ hN hCN
  have hW : IsClosedSubmanifold n W:=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hdense : W⊆closure (W\D) := by
    change closure (π ⁻¹' (N\C))⊆_
    apply closure_mono
    intro y hy
    exact ⟨subset_closure hy,hy.2⟩
  have hEmpty : cosupport n W (vanishingIdeal (n:=n) D) 2=∅ :=
    originalBoundaryTraceMarked_cosupp_eq_empty_of_normalCrossings hn hE hT.hasNormalCrossings hdense
  have hMem (g : Y→ℂ) : J.mem z g↔(vanishingIdeal (n:=n) D).mem z g :=
    exceptionalDivisor_mem_iff_vanishingIdeal hπ hzC g
  have hBase (q : ℕ) : z∈cosupport n W J q↔z∈cosupport n W (vanishingIdeal (n:=n) D) q := by
    constructor
    · intro h
      exact ⟨h.1,fun g hg=>h.2 g ((hMem g).mpr hg)⟩
    · intro h
      exact ⟨h.1,fun g hg=>h.2 g ((hMem g).mp hg)⟩
  have hGood1 : z∈cosupport n W J 1 := by
    apply (hBase 1).mpr
    rw [cosupport_vanishingIdeal_one (hE.1 D (by simp [D]))]
    exact ⟨hzN,hzC⟩
  have hBad2 : z∉cosupport n W J 2 := by
    intro h
    have hD:=(hBase 2).mp h
    rw [hEmpty] at hD
    exact hD
  have hGood : z∈cosupport n W (idealPow J e) e := by
    simpa only [Nat.one_mul] using cosupport_subset_cosupport_idealPow 1 e hGood1
  have hBad : z∉cosupport n W (idealPow J e) (e+1) := by
    cases e with
    | zero =>
      change z∉cosupport n W (unitIdeal n Y) 1
      rw [cosupport_unitIdeal (Nat.le_refl 1)]
      simp
    | succ e =>
      intro h
      apply hBad2
      have hEq:=HironakaDivisorPowers.cosupport_idealPow_mul_succ_eq_along
        hW.2 (fun _ _ (hg : J.mem _ _)=>hg.1) (Nat.succ_le_succ (Nat.zero_le e)) 1
      rw [←hEq]
      simpa only [Nat.mul_one] using h
  exact ⟨hGood,hBad,order_from_sharp W (idealPow J e) z e
    (fun _ hg=>holomorphicAt_of_mem_idealPow hg) hGood hBad⟩

private theorem whole_cut_of_scalar {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} m}
    (κ : Y→X) (hκ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ κ)
    (N : Set X) (W : Set Y) (x : X) (z : Y) (hκz : κ z=x) (hx : x∈N) (hz : z∈W)
    (a b : ℕ)
    (hCut : ∀(g : X→ℂ),HolomorphicAt n g x→
      (VanishesToOrderOn m W z b (g∘κ)↔VanishesToOrderOn n N x a g))
    (I : GermIdeal n X) (hI : I.IsCoherent) :
    z∈cosupport m W (GermIdeal.pullback (m:=m) κ I) b↔x∈cosupport n N I a := by
  have hκat : ∀ᶠy in 𝓝 z,ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ κ y:=
    Eventually.of_forall fun _=>hκ.contMDiffAt
  constructor
  · intro h
    refine ⟨hx,fun g hg=>?_⟩
    have hgh:=GermIdeal.IsCoherent.holomorphicAt_mem hI hg
    have hgi : I.mem (κ z) g := by rw [hκz];exact hg
    have hgh' : HolomorphicAt n g (κ z):=GermIdeal.IsCoherent.holomorphicAt_mem hI hgi
    have hGen : (GermIdeal.pullback (m:=m) κ I).mem z (g∘κ):=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hgi,rfl⟩ (hgh'.comp_contMDiff hκat))
    exact (hCut g hgh).mp (h.2 _ hGen)
  · intro h
    refine ⟨hz,fun g hg=>?_⟩
    apply IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨f,hf,rfl⟩
    have hfx : I.mem x f := by rwa [hκz] at hf
    exact (hCut f (GermIdeal.IsCoherent.holomorphicAt_mem hI hfx)).mpr (h.2 f hfx)

private theorem power_generator {n : ℕ} {X : CMfd.{u} n}
    (I : GermIdeal n X) (τ : X→ℂ) (x : X) (hτhol : HolomorphicAt n τ x)
    (hτ : I.mem x τ) (hGen : ∀g,I.mem x g↔IsInSpanAt (n:=n) (·=τ) x g) (e : ℕ) :
    ∀g,(idealPow I e).mem x g↔IsInSpanAt (n:=n) (·=(fun y=>τ y^e)) x g := by
  intro g
  constructor
  · intro hg
    obtain ⟨a,ha,hEq⟩:=MonomialPart.exists_eq_mul_pow_of_mem_idealPow
      (fun f hf=>(hGen f).mp hf) hg
    exact isInSpanAt_eq_iff.mpr ⟨holomorphicAt_of_mem_idealPow hg,a,ha,hEq⟩
  · intro hg
    apply GermIdealOrder.mem_idealPow_of_isInSpanAt
    refine hg.mono ?_
    intro s hs
    rw [hs]
    exact OrderMultiplicativity.pow_mem_idealPow hτ hτhol e


private theorem pivot_power_generator {m : ℕ} {A : CMfd.{u} m} {C : Set A}
    [Fact (IsClosedSubmanifold m C)] (c : FlatChart m C)
    (hπ : IsBlowupAlong m C (blowupProj m C))
    (hWs : ∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ c.toFun u)
    (z : BlowupSpace m C) (hz : z∈c.source) (e : ℕ) :
    ∀g,(idealPow (GermIdeal.pullback (m:=m) (blowupProj m C) (vanishingIdeal (n:=m) C)) e).mem z g↔
      IsInSpanAt (n:=m) (·=(fun u=>c.toFun u c.j^e)) z g := by
  let J:=GermIdeal.pullback (m:=m) (blowupProj m C) (vanishingIdeal (n:=m) C)
  let τ : BlowupSpace m C→ℂ:=fun u=>c.toFun u c.j
  have hRaw (g : BlowupSpace m C→ℂ) := BlowupStrictIdeal.exceptionalDivisor_mem_iff_of_chart
    hπ c.hsrc c.hflat c.hj c.isOpen_source hWs
    (fun u hu=>⟨hu.1,c.monomial_toFun hu⟩) hz g
  have hBase (g : BlowupSpace m C→ℂ) : J.mem z g↔IsInSpanAt (n:=m) (·=τ) z g := by
    constructor
    · intro hg
      apply IsInSpanAt.mono ?_ ((hRaw g).mp hg)
      rintro f ⟨i,hi⟩
      exact hi.symm
    · intro hg
      apply (hRaw g).mpr
      refine hg.mono ?_
      intro f hf
      exact ⟨0,hf.symm⟩
  have hτhol : HolomorphicAt m τ z:=BlowupStrictIdeal.holomorphicAt_coord c.isOpen_source hWs c.j hz
  have hτ : J.mem z τ:=(hBase τ).mpr (isInSpanAt_self rfl hτhol)
  exact power_generator (X:=CMfd.of (n:=m) (BlowupSpace m C)) J τ z hτhol hτ hBase e

variable {n : ℕ} {X : CMfd.{u} n}

/-- ONE internally derived geometry witness gives ENTIRE original ideal cuts,
then sharp finite original pullback and native controlled order. -/
theorem exists_projection_vertical_order {k : ℕ}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    let p : projectionAmbient X:=(x,0)
    let C : Set (projectionAmbient X):={p}
    let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(projection_point_centre M hM x hx).1.1⟩
    let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
    let π : Y → projectionAmbient X:=blowupProj (n+1) C
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) C) (SN : Finset (Fin (n+1)))
      (SE : Fin M.E.length → Finset (Fin (n+1))),
      (Φ.source⊆(chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      c.y₀=p ∧ c.k=0 ∧ c.j=Fin.last n ∧
      (∀(y : projectionAmbient X)(i : Fin n),flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1) ∧
      (∀y : projectionAmbient X,flatCoord c.Φ (Fin.last n) y=y.2 0) ∧
      (∀y∈flatDomain c.Φ,y∈(projectionTest M).N ↔
        c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace SN) ∧
      (∀i,x∈M.E.get i → ∀y∈flatDomain c.Φ,
        y∈(Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i ↔
          c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace (SE i)) ∧
      Fin.last n∉SN ∧ (∀i,Fin.last n∉SE i) ∧
      (0 : ComplexModel (n+1))∈c.target ∧
      let z:=c.invFun 0
      z∈c.source ∧ π z=p ∧ c.toFun z=0 ∧
      IsBlowupAlong (n+1) C π ∧
      z∈((projectionTest M).geoTransform C π).N ∧
      (∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun u) ∧
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (flatParameterLift c) ∧
      (∀u∈c.source,monomial 0 (Fin.last n) (c.toFun u)=
        c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ (π u))) ∧
      (∀u∈c.source,u∈((projectionTest M).geoTransform C π).N ↔ c.toFun u∈coordSubspace SN) ∧
      (∀i,x∈M.E.get i → ∀u∈c.source,
        u∈geoStrictTransform π C ((Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i) ↔
          c.toFun u∈coordSubspace (SE i)) ∧
      (∀u∈c.source,u∉geoStrictTransform π C (horizontal X)) ∧
      (∀u∈c.source,u∈π ⁻¹' C ↔ c.toFun u (Fin.last n)=0) ∧
      (∃O : Set Y,IsOpen O ∧ z∈O ∧ O⊆c.source ∧
        ∀i,x∉M.E.get i → ∀u∈O,
          u∉geoStrictTransform π C ((Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i)) ∧
      IsInvDomain (k+1) ((projectionTest M).geoTransform C π) ∧
      ((projectionTest M).geoTransform C π).d=M.d ∧
      ((projectionTest M).geoTransform C π).E=
        M.E.map (fun H=>geoStrictTransform π C ((Prod.fst : projectionAmbient X → X) ⁻¹' H)) ++
          [geoStrictTransform π C (horizontal X),π ⁻¹' C] ∧
      ((projectionTest M).geoTransform C π).E.length=M.E.length+2) ∧
      let z:=c.invFun 0
      let Q:=(projectionTest M).geoTransform C π
      let W:=Q.N
      let B:=fun I : GermIdeal n X=>GermIdeal.pullback (m:=n+1) π
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I)
      let ρ:=ordinaryTraceOrder M.N M.ideal x
      let F:=idealPow (GermIdeal.pullback (m:=n+1) π (vanishingIdeal (n:=n+1) C)) M.d
      let τ : Y→ℂ:=fun u=>c.toFun u (Fin.last n)
      let r:=2*ρ-M.d
      (∀(I : GermIdeal n X),I.IsCoherent→∀q : ℕ,
        (z∈cosupport (n+1) W (B I) (2*q)↔x∈cosupport n M.N I q) ∧
        (z∈cosupport (n+1) W (B I) (2*q+1)↔x∈cosupport n M.N I (q+1))) ∧
      M.d≤ρ ∧ GermIdealOrder.order n M.N M.ideal x=(ρ : ℕ∞) ∧
      z∈cosupport (n+1) W (B M.ideal) (2*ρ) ∧
      z∉cosupport (n+1) W (B M.ideal) (2*ρ+1) ∧
      ordinaryTraceOrder W (B M.ideal) z=2*ρ ∧
      GermIdealOrder.order (n+1) W (B M.ideal) z=((2*ρ : ℕ) : ℕ∞) ∧
      (∀g,F.mem z g↔IsInSpanAt (n:=n+1) (·=(fun u=>τ u^M.d)) z g) ∧
      VanishesToOrderOn (n+1) W z M.d (fun u=>τ u^M.d) ∧
      ¬VanishesToOrderOn (n+1) W z (M.d+1) (fun u=>τ u^M.d) ∧
      z∈cosupport (n+1) W Q.ideal r ∧ z∉cosupport (n+1) W Q.ideal (r+1) ∧
      ordinaryTraceOrder W Q.ideal z=r ∧
      GermIdealOrder.order (n+1) W Q.ideal z=(r : ℕ∞) ∧
      M.d≤r ∧ z∈Q.cosupp := by
  dsimp only
  let p : projectionAmbient X:=(x,0)
  let C : Set (projectionAmbient X):={p}
  let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X:=blowupProj (n+1) C
  obtain ⟨Φ,c,SN,SE,hGeometry,hScalar⟩:=exists_projection_vertical_function_order M hM x hx
  refine ⟨Φ,c,SN,SE,hGeometry,?_⟩
  rcases hGeometry with ⟨_hΦs,_hΦ0,_hcp,_hck,hcj,_hOld,_hLast,_hSourceN,_hSourceE,_hSN,_hSE,_h0c,
    hzSource,hzp,_hWz,hπ,hzN,hWs,_hInv,_hMon,_hTargetN,_hTargetE,_hEmptyH,_hBorn,
    _hWindow,hQ,hdQ,_hEword,_hLength⟩
  let Q:=(projectionTest M).geoTransform C π
  let W:=Q.N
  let B:=fun I : GermIdeal n X=>GermIdeal.pullback (m:=n+1) π
    (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I)
  let z : Y:=c.invFun 0
  let κ : Y→X:=(Prod.fst : projectionAmbient X→X)∘π
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let F:=idealPow (GermIdeal.pullback (m:=n+1) π (vanishingIdeal (n:=n+1) C)) M.d
  let τ : Y→ℂ:=fun u=>c.toFun u (Fin.last n)
  let r:=2*ρ-M.d
  have hzp' : π z=(x,0):=hzp
  have hxN : x∈M.N:=M.cosupp_subset_N hx
  have hFst : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞
      (Prod.fst : projectionAmbient X→X):=
    ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
  have hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ κ:=hFst.comp hπ.contMDiff
  have hκz : κ z=x := by change (π z).1=x;rw [hzp']
  have hWhole (I : GermIdeal n X) (hI : I.IsCoherent) (q : ℕ) :
      (z∈cosupport (n+1) W (B I) (2*q)↔x∈cosupport n M.N I q) ∧
      (z∈cosupport (n+1) W (B I) (2*q+1)↔x∈cosupport n M.N I (q+1)) := by
    have hComp:=coherent_parameter_pullback_comp hFst hπ.contMDiff I hI
    change (z∈cosupport (n+1) W (GermIdeal.pullback (m:=n+1) π
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I)) (2*q)↔_) ∧
      (z∈cosupport (n+1) W (GermIdeal.pullback (m:=n+1) π
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I)) (2*q+1)↔_)
    rw [←hComp]
    exact ⟨whole_cut_of_scalar κ hκ M.N W x z hκz hxN hzN q (2*q)
      (fun f hf=>(hScalar f hf q).1) I hI,
      whole_cut_of_scalar κ hκ M.N W x z hκz hxN hzN (q+1) (2*q+1)
      (fun f hf=>(hScalar f hf q).2) I hI⟩
  have hCrit (t : ℕ) : x∈cosupport n M.N M.ideal t↔t≤ρ:=
    ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.isNonzeroAlongAt hxN t
  have hSourceGood : x∈cosupport n M.N M.ideal ρ:=(hCrit ρ).mpr le_rfl
  have hSourceBad : x∉cosupport n M.N M.ideal (ρ+1):=fun h=>Nat.not_succ_le_self ρ ((hCrit _).mp h)
  have hdρ : M.d≤ρ:=(hCrit M.d).mp hx
  have hSourceOrder:=order_from_sharp M.N M.ideal x ρ
    (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)
    hSourceGood hSourceBad
  have hBGood : z∈cosupport (n+1) W (B M.ideal) (2*ρ):=
    (hWhole M.ideal hM.isWellFormed.isCoherent ρ).1.mpr hSourceGood
  obtain ⟨g,hg,hgNot⟩:=exists_not_vanishesToOrderOn_of_notMem hxN hSourceBad
  have hBBad : z∉cosupport (n+1) W (B M.ideal) (2*ρ+1) := by
    intro h
    exact hgNot (((hWhole M.ideal hM.isWellFormed.isCoherent ρ).2.mp h).2 g hg)
  have hP:=projection_test_isInvDomain M hM
  have hBCoh : (B M.ideal).IsCoherent:=isCoherent_pullback hπ.contMDiff hP.isWellFormed.isCoherent
  have hBNZ : ∀y∈W,IsNonzeroAlongAt W (B M.ideal) y:=
    ordinary_pullback_nonzero_on_strict hπ hP.isWellFormed.isClosedSubmanifold_N.1
      hP.isWellFormed.isCoherent hP.isNonzeroAlongAt
  have hBNat:=nat_order_from_sharp hQ.isWellFormed.isClosedSubmanifold_N hBCoh hBNZ hzN
    (2*ρ) hBGood hBBad
  have hBOrder:=order_from_sharp W (B M.ideal) z (2*ρ)
    (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hBCoh hg) hBGood hBBad
  have hC : (projectionTest M).IsAdmissibleCentre C:=(projection_point_centre M hM x hx).1
  have hzC : π z∈C := by rw [hzp'];exact mem_singleton p
  obtain ⟨hFGood,hFBad,_hFOrder⟩:=exceptional_power_order_at_strict hπ
    hP.isWellFormed.isClosedSubmanifold_N hC.subset_N z hzN hzC M.d
  have hFGen:=pivot_power_generator c hπ hWs z hzSource M.d
  simp only [hcj] at hFGen
  have hτhol : HolomorphicAt (n+1) τ z:=
    BlowupStrictIdeal.holomorphicAt_coord c.isOpen_source hWs (Fin.last n) hzSource
  have hτPowHol : HolomorphicAt (n+1) (fun u=>τ u^M.d) z:=
    CompanionReduction.holomorphicAt_pow_of hτhol M.d
  have hτPowMem : F.mem z (fun u=>τ u^M.d):=
    (hFGen _).mpr (isInSpanAt_self rfl hτPowHol)
  have hτGood : VanishesToOrderOn (n+1) W z M.d (fun u=>τ u^M.d):=hFGood.2 _ hτPowMem
  have hτBad : ¬VanishesToOrderOn (n+1) W z (M.d+1) (fun u=>τ u^M.d) := by
    intro h
    apply hFBad
    refine ⟨hzN,fun f hf=>?_⟩
    exact IsInSpanAt.vanishesToOrderOn ((hFGen f).mp hf) (fun s hs=>by rw [hs];exact h)
  obtain ⟨hBProd,hProdB⟩:=MarkedIdealOperationsAlong.MarkedIdeal.restrictLe_pullback_geoTransform
    hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hC hπ
  have hProductGood : z∈cosupport (n+1) W (F.mul Q.ideal) (2*ρ):=
    cosupport_subset_of_restrictLe hProdB (2*ρ) hBGood
  have hdTwo : M.d≤2*ρ:=by omega
  have hQGood : z∈cosupport (n+1) W Q.ideal r:=
    mem_cosupport_of_mem_cosupport_mul_along hQ.isWellFormed.isClosedSubmanifold_N.2
      (fun _ _ hg=>holomorphicAt_of_mem_idealPow hg)
      (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg)
      hdTwo hProductGood hFBad
  have hQBad : z∉cosupport (n+1) W Q.ideal (r+1) := by
    intro h
    have hProd:=inter_cosupport_subset_cosupport_mul M.d (r+1) ⟨hFGood,h⟩
    have hEq : M.d+(r+1)=2*ρ+1:=by dsimp only [r];omega
    rw [hEq] at hProd
    exact hBBad (cosupport_subset_of_restrictLe hBProd (2*ρ+1) hProd)
  have hQNat:=nat_order_from_sharp hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent
    hQ.isNonzeroAlongAt hzN r hQGood hQBad
  have hQOrder:=order_from_sharp W Q.ideal z r
    (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg) hQGood hQBad
  have hdr : M.d≤r:=by dsimp only [r];omega
  have hzQ : z∈Q.cosupp := by
    change z∈cosupport (n+1) W Q.ideal Q.d
    rw [hdQ]
    exact cosupport_anti hdr hQGood
  exact ⟨hWhole,hdρ,hSourceOrder,hBGood,hBBad,hBNat,hBOrder,hFGen,hτGood,hτBad,
    hQGood,hQBad,hQNat,hQOrder,hdr,hzQ⟩

end
end Hironaka.HironakaActualProjectionVerticalOrder
