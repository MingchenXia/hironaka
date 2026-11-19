import Hironaka.Resolution.HironakaActualAnchoredOriginalGermSquare
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder

/-! Whole ORIGINAL ideal cuts/order from ONE retained actual scalar geometry.
The private span helper is shared, not a caller packet or an old private call.
No controlled order, raw invariant, future test or all-q history is claimed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredOriginalIdealOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates NormalCrossings
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
  GiraudAlong GermIdealTotalTransform GermIdealOrder IdealOrderArithmetic IdealWeightPowers
  HironakaActualAnchoredVerticalChart HironakaActualAnchoredOriginalGermSquare
  HironakaActualProjectionTestRecord HironakaActualProjectionVerticalBlowupChart
  HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal CompanionReductionAlong
open scoped ProductComplexManifold

private def oldMask {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter fun i=>i.castAdd 1∈S
private instance point_closed_fact {a : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X] (x : X) :
    Fact (IsClosedSubmanifold a ({x} : Set X)) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1⟩
private abbrev recordMark {a : ℕ} (X : CMfd.{u} a) (Q : MarkedIdeal a X) : ℕ :=
  @MarkedIdeal.d a X.carrier X.topologicalSpace X.chartedSpace Q
private abbrev recordBoundary {a : ℕ} (X : CMfd.{u} a) (Q : MarkedIdeal a X) : List (Set X) :=
  @MarkedIdeal.E a X.carrier X.topologicalSpace X.chartedSpace Q

/-- PRIVATE finite-span composition, populated only by retained actual scalar
facts inside the ordinary public constructions. ALL target coefficients occur. -/
private theorem whole_cut_at_fixed_geometry {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}
    (κ : Y→X) (hκ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ κ)
    (N : Set X) (Nt : Set Y) (x : X) (z : Y)
    (hκz : κ z=x) (hxN : x∈N) (hzNt : z∈Nt) (a b : ℕ)
    (hScalar : ∀(f : X→ℂ),HolomorphicAt n f x→
      (VanishesToOrderOn m Nt z b (f∘κ)↔VanishesToOrderOn n N x a f))
    (I : GermIdeal n X) (hI : I.IsCoherent) :
    z∈cosupport m Nt (GermIdeal.pullback (m:=m) κ I) b ↔
      x∈cosupport n N I a := by
  have hκat : ∀ᶠy in 𝓝 z,ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ κ y :=
    Eventually.of_forall fun _=>hκ.contMDiffAt
  constructor
  · intro h
    refine ⟨hxN,fun g hg=>?_⟩
    have hgh:=GermIdeal.IsCoherent.holomorphicAt_mem hI hg
    have hgi : I.mem (κ z) g := by rw [hκz];exact hg
    have hgh' : HolomorphicAt n g (κ z):=GermIdeal.IsCoherent.holomorphicAt_mem hI hgi
    have hGen : (GermIdeal.pullback (m:=m) κ I).mem z (g∘κ) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hgi,rfl⟩ (hgh'.comp_contMDiff hκat))
    exact (hScalar g hgh).mp (h.2 _ hGen)
  · intro h
    refine ⟨hzNt,fun g hg=>?_⟩
    apply IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨f,hf,rfl⟩
    have hfx : I.mem x f := by rwa [hκz] at hf
    exact (hScalar f (GermIdeal.IsCoherent.holomorphicAt_mem hI hfx)).mpr (h.2 f hfx)

private abbrev scalarCutsAt {n : ℕ} {X : CMfd.{u} n} {Z : CMfd.{u} (n+1)}
    (N : Set X) (Nt : Set Z) (x : X) (z : Z) (r : ℕ) (κ : Z→X) : Prop :=
  ∀(f : X→ℂ),HolomorphicAt n f x→∀a : ℕ,
    (VanishesToOrderOn (n+1) Nt z ((r+2)*a) (f∘κ) ↔ VanishesToOrderOn n N x a f) ∧
    ∀b : ℕ,b≤r+1→
      (VanishesToOrderOn (n+1) Nt z ((r+2)*a+b+1) (f∘κ) ↔
        VanishesToOrderOn n N x (a+1) f)

/- Reducible OUTPUT dictionary at one actual native geometry. -/
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

private theorem whole_tail_from_same_scalar {n : ℕ} {X : CMfd.{u} n}
    {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    {Z : CMfd.{u} (n+1)} (N : Set X) (Nt : Set Z) (x : X) (z : Z)
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z)
    (hκz : ((Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj) z=x)
    (hxN : x∈N) (hzNt : z∈Nt)
    (hScalar : scalarCutsAt N Nt x z R.length
      ((Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj)) :
    wholeTailCuts N Nt x z R := by
  dsimp only [wholeTailCuts]
  let κ : Z→X:=(Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj
  have hFst:=ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
  have hπ : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞
      (blowupProj (n+1) C) := contMDiff_blowupProj
  have hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ κ :=
    (hFst.comp hπ).comp R.contMDiff_proj
  refine ⟨hκz,hzNt,?_⟩
  intro I hI
  have hComp : GermIdeal.pullback (m:=n+1) R.proj
      (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I))=
      GermIdeal.pullback (m:=n+1) κ I := by
    have h1:=coherent_parameter_pullback_comp hFst (hπ.comp R.contMDiff_proj) I hI
    have h2:=GermIdealTotalTransform.pullback_comp hπ R.contMDiff_proj (isCoherent_pullback hFst hI)
    exact (h1.trans h2).symm
  refine ⟨hComp,?_,?_⟩
  · rw [hComp]
    exact isCoherent_pullback hκ hI
  · intro a
    rw [hComp]
    exact ⟨whole_cut_at_fixed_geometry κ hκ N Nt x z hκz hxN hzNt a ((R.length+2)*a)
      (fun f hf=>(hScalar f hf a).1) I hI,
      fun b hb=>whole_cut_at_fixed_geometry κ hκ N Nt x z hκz hxN hzNt (a+1)
        ((R.length+2)*a+b+1) (fun f hf=>(hScalar f hf a).2 b hb) I hI⟩

/- Entire SAME first native seed is retained in fully reducible OUTPUT notation. -/
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

/-- ONE ordinary call retains the actual scalar callback privately; all
coherent original ideals and ALL target coefficients are handled afterwards. -/
theorem exists_original_anchored_whole_ideal_cuts {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      wholeCutsOutput M hM x hx Φ Φs c SN SE U := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hSeed⟩:=exists_original_anchored_scalar_cuts M hM x hx
  rcases hSeed with ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
    hEmask,hEmptyH,hBorn,hTo,hInv,hSub,hTSub,hSrc,hZero,hDom,hSource,hTails⟩
  refine ⟨Φ,Φs,c,SN,SE,U,?_⟩
  dsimp only [wholeCutsOutput]
  refine ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
    hEmask,hEmptyH,hBorn,hTo,hInv,hSub,hTSub,hSrc,hZero,hDom,hSource,?_⟩
  intro Z R e hA z hz he0
  obtain ⟨W,Θ,hκz,_hW,_hWo,_hzW,_hWs,_hΘs,hΘ0,hMask,_hVector,_hPoint,hScalars⟩:=
    hTails R e hA z hz he0
  have hzNt :=
    ((hMask z (mem_flatDomain_self Θ)).2.2).mpr (by
      change Θ.toFun (chartAt (ComplexModel (n+1)) z z)∈coordSubspace SN
      rw [hΘ0]
      intro i hi
      rfl)
  apply whole_tail_from_same_scalar M.N _ x z R hκz (M.cosupp_subset_N hx) hzNt
  intro f hf a
  obtain ⟨_hF,_hG,_hEq,_hCoeff,hMult,hSucc,_hOrd⟩:=hScalars f hf
  exact ⟨hMult a,fun b hb=>hSucc a b hb⟩

private theorem enat_order_from_sharp {n : ℕ} {X : CMfd.{u} n}
    (N : Set X) (I : GermIdeal n X) (x : X) (a : ℕ)
    (hHol : ∀g,I.mem x g→HolomorphicAt n g x)
    (hGood : x∈cosupport n N I a) (hBad : x∉cosupport n N I (a+1)) :
    GermIdealOrder.order n N I x=(a : ℕ∞) := by
  apply le_antisymm
  · apply ENat.lt_natCast_add_one_iff.mp
    apply lt_of_not_ge
    intro h
    exact hBad ⟨hGood.1,(le_order_iff hHol).mp
      (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
  · exact (le_order_iff hHol).mpr hGood.2

/- The ACTUAL failure supplies the finite sInf guard. No global N/domain/NZ. -/
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

/- OUTPUT only: BOTH dictionaries are constructed on ONE retained seed. -/
private abbrev wholeOrderOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M hM x hx Φ Φs c SN SE U ∧
  let p : projectionAmbient X := (x,0)
  let C : Set (projectionAmbient X) := {p}
  let _ : Fact (IsClosedSubmanifold (n+1) C) := ⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X := blowupProj (n+1) C
  let Q : MarkedIdeal (n+1) Y := (projectionTest M).geoTransform C π
  let _z := c.invFun 0
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  M.d≤ρ ∧ GermIdealOrder.order n M.N M.ideal x=(ρ : ℕ∞) ∧
    ∃g : X→ℂ,M.ideal.mem x g ∧ ¬VanishesToOrderOn n M.N x (ρ+1) g ∧
    ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y Z)
      (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
      (_hA : AnchoredInheritedLastChartChain c.homeo R e)
      (z : Z) (_hz : z∈e.source) (_he0 : e z=0),
      sharpTailOutput M g ρ (Q.geoTransformAlong R).N z R

/-- ONE parent call privately retains SAME geometry/scalar data for BOTH
whole cuts and the fixed source member. There is no existential reselection. -/
theorem exists_original_anchored_whole_ideal_order {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      wholeOrderOutput M hM x hx Φ Φs c SN SE U := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hSeed⟩:=exists_original_anchored_scalar_cuts M hM x hx
  rcases hSeed with ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
    hEmask,hEmptyH,hBorn,hTo,hInv,hSub,hTSub,hSrc,hZero,hDom,hSource,hTails⟩
  -- This dependent choice is made from the ONE retained callback BEFORE g/I.
  choose WAt ΘAt data_at using @hTails
  let C : Set (projectionAmbient X):={(x,0)}
  let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X:=blowupProj (n+1) C
  let Q : MarkedIdeal (n+1) Y:=(projectionTest M).geoTransform C π
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  have hI:=hM.isWellFormed.isCoherent
  have hxN : x∈M.N:=M.cosupp_subset_N hx
  have hCrit (a : ℕ) : x∈cosupport n M.N M.ideal a ↔ a≤ρ :=
    ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N hI
      hM.isNonzeroAlongAt hxN a
  have hGoodSource : x∈cosupport n M.N M.ideal ρ :=(hCrit ρ).mpr le_rfl
  have hBadSource : x∉cosupport n M.N M.ideal (ρ+1) :=
    fun h=>Nat.not_succ_le_self ρ ((hCrit (ρ+1)).mp h)
  have hdρ : M.d≤ρ :=(hCrit M.d).mp hx
  have hSourceOrder:=enat_order_from_sharp M.N M.ideal x ρ
    (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hGoodSource hBadSource
  obtain ⟨g,hg,hgBad⟩:=exists_not_vanishesToOrderOn_of_notMem hxN hBadSource
  have hgh:=GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  have both_at : ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y Z)
      (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
      (hA : AnchoredInheritedLastChartChain c.homeo R e)
      (z : Z) (hz : z∈e.source) (he0 : e z=0),
      wholeTailCuts M.N (Q.geoTransformAlong R).N x z R ∧
        sharpTailOutput M g ρ (Q.geoTransformAlong R).N z R := by
    intro Z R e hA z hz he0
    let Θ:=@ΘAt Z R e hA z hz he0
    rcases @data_at Z R e hA z hz he0 with
      ⟨hκz,_hW,_hWo,_hzW,_hWs,_hΘs,hΘ0,hMask,_hVector,_hPoint,hScalars⟩
    let Nt:=(Q.geoTransformAlong R).N
    let κ : Z→X:=(Prod.fst : projectionAmbient X→X)∘π∘R.proj
    change κ z=x at hκz
    let B:=GermIdeal.pullback (m:=n+1) R.proj
      (GermIdeal.pullback (m:=n+1) π
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal))
    let μ:=(R.length+2)*ρ
    have hzNt : z∈Nt :=((hMask z (mem_flatDomain_self Θ)).2.2).mpr (by
      change Θ.toFun (chartAt (ComplexModel (n+1)) z z)∈coordSubspace SN
      rw [hΘ0]
      intro i hi
      rfl)
    have hScalar : scalarCutsAt M.N Nt x z R.length κ := by
      intro f hf a
      obtain ⟨_hF,_hG,_hEq,_hCoeff,hMult,hSucc,_hOrd⟩:=hScalars f hf
      exact ⟨hMult a,fun b hb=>hSucc a b hb⟩
    have hWhole:=whole_tail_from_same_scalar M.N Nt x z R hκz hxN hzNt hScalar
    have hWholeI:=hWhole.2.2 M.ideal hI
    have hComp : B=GermIdeal.pullback (m:=n+1) κ M.ideal:=hWholeI.1
    have hBcoh : B.IsCoherent:=hWholeI.2.1
    have hGood : z∈cosupport (n+1) Nt B μ :=(hWholeI.2.2 ρ).1.mpr hGoodSource
    have hBad : z∉cosupport (n+1) Nt B (μ+1) := by
      intro h
      exact hBadSource (((hWholeI.2.2 ρ).2 0 (Nat.zero_le _)).mp h)
    have hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ κ :=
      ((ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)).comp
        contMDiff_blowupProj).comp R.contMDiff_proj
    have hgκ : M.ideal.mem (κ z) g := by rw [hκz];exact hg
    have hghκ : HolomorphicAt n g (κ z) :=by rw [hκz];exact hgh
    have hGen : (GermIdeal.pullback (m:=n+1) κ M.ideal).mem z (g∘κ) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hgκ,rfl⟩
        (hghκ.comp_contMDiff (Eventually.of_forall fun _=>hκ.contMDiffAt)))
    have hgB : B.mem z (g∘κ):=hComp.symm ▸ hGen
    refine ⟨hWhole,hGood,hBad,?_,?_,hgB,hGood.2 _ hgB,?_⟩
    · exact nat_trace_from_sharp Nt B hBcoh z μ hGood hBad
    · exact enat_order_from_sharp Nt B z μ
        (fun _ hs=>GermIdeal.IsCoherent.holomorphicAt_mem hBcoh hs) hGood hBad
    · intro h
      exact hgBad (((hScalar g hgh ρ).2 0 (Nat.zero_le _)).mp h)
  have hWhole : wholeCutsOutput M hM x hx Φ Φs c SN SE U := by
    dsimp only [wholeCutsOutput]
    refine ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
      hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
      hEmask,hEmptyH,hBorn,hTo,hInv,hSub,hTSub,hSrc,hZero,hDom,hSource,?_⟩
    intro Z R e hA z hz he0
    exact (both_at R e hA z hz he0).1
  refine ⟨Φ,Φs,c,SN,SE,U,?_⟩
  dsimp only [wholeOrderOutput]
  refine ⟨hWhole,hdρ,hSourceOrder,g,hg,hgBad,?_⟩
  intro Z R e hA z hz he0
  exact (both_at R e hA z hz he0).2

end
end Hironaka.HironakaActualAnchoredOriginalIdealOrder
