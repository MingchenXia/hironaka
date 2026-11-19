import Hironaka.Resolution.HironakaActualProjectionVerticalOrder
import Hironaka.Analytic.PointSupportedIdealPrincipalization

/-! A next native point chart in the SAME inherited coordinates. Geometry
and domain only: a current cosupport point need not stay in cosupport at
the selected next point. The entire old/horizontal/born word is retained. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualInheritedVerticalPointChart
open scoped ProductComplexManifold
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  BlowupTowers BlowupStrictSubmanifold BlowupConstruction BlowupFlatCoordinates
  BlowupMonomialCharts BlowupSNCTransform BlowupLocalSurjectivity InvDomainTowerAlong
  HironakaSmoothSubmersionUniversalBlowupChartEquality
  HironakaActualProjectionTestRecord HironakaActualProjectionVerticalBlowupChart
  HironakaActualProjectionVerticalOrder HironakaOneDimensionalCanonicalSuperlevels
  PointSupportedIdealPrincipalization GiraudAlong

private instance singleton_closed_fact {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel m) X] [IsComplexManifold m X] (x : X) :
    Fact (IsClosedSubmanifold m ({x} : Set X)):=⟨(singleton_geometry_and_coherence x).1⟩

/-- Package an ACTUAL inherited centred atlas chart, preserving its entire
coordinate function on a derived preferred-chart domain. -/
theorem exists_inherited_coordinates {m : ℕ} {X : CMfd.{u} m}
    (e : OpenPartialHomeomorph X (ComplexModel m))
    (he : e∈atlas (ComplexModel m) X) (x : X) (hxe : x∈e.source) (he0 : e x=0)
    (U : Set X) (hU : IsOpen U) (hxU : x∈U) (_hUs : U⊆e.source) :
    ∃Θ : LocalHolomorphicEquivAt (n:=m) (chartAt (ComplexModel m) x x),
      Θ.source⊆(chartAt (ComplexModel m) x).target ∧
      Θ.toFun (chartAt (ComplexModel m) x x)=0 ∧
      ∀y∈flatDomain Θ,y∈U ∧ flatMap Θ y=e y := by
  let a:=chartAt (ComplexModel m) x
  let t:=a.symm.trans (e.restrOpen U hU)
  have hmax:=IsManifold.subset_maximalAtlas (I:=𝓘(ℂ,ComplexModel m)) (n:=∞) he
  have htSrc : t.source=a.target∩a.symm ⁻¹' (e.source∩U) := rfl
  have htTgt : t.target=(e.target∩e.symm ⁻¹' U)∩e.symm ⁻¹' a.source := rfl
  have hforw : DifferentiableOn ℂ t t.source := by
    intro w hw
    rw [htSrc] at hw
    have h1:=contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ComplexModel m)) (n:=∞) x) hw.1
    have h2:=contMDiffAt_of_mem_maximalAtlas hmax hw.2.1
    exact (mdifferentiableAt_iff_differentiableAt.mp
      ((h2.comp w h1).mdifferentiableAt (by simp))).differentiableWithinAt
  have hinv : DifferentiableOn ℂ t.symm t.target := by
    intro w hw
    rw [htTgt] at hw
    have h1:=contMDiffAt_symm_of_mem_maximalAtlas hmax hw.1.1
    have h2:=contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ComplexModel m)) (n:=∞) x) hw.2
    exact (mdifferentiableAt_iff_differentiableAt.mp
      ((h2.comp w h1).mdifferentiableAt (by simp))).differentiableWithinAt
  have hxA : x∈a.source:=mem_chart_source _ x
  have hcent : a x∈t.source := by
    rw [htSrc]
    exact ⟨a.map_source hxA,by
      change a.symm (a x)∈e.source∩U
      rw [a.left_inv hxA]
      exact ⟨hxe,hxU⟩⟩
  let Θ : LocalHolomorphicEquivAt (n:=m) (a x) := {
    source:=t.source
    target:=t.target
    isOpen_source:=t.open_source
    isOpen_target:=t.open_target
    center_mem_source:=hcent
    toFun:=t
    invFun:=t.symm
    toFun_holomorphic:=hforw
    invFun_holomorphic:=hinv
    mapsTo_toFun:=fun _ hw=>t.map_source hw
    mapsTo_invFun:=fun _ hw=>t.map_target hw
    left_inv:=fun w hw=>t.left_inv hw
    right_inv:=fun w hw=>t.right_inv hw }
  refine ⟨Θ,?_,?_,?_⟩
  · intro w hw
    have hwt : w∈t.source:=hw
    exact (htSrc ▸ hwt).1
  · change e (a.symm (a x))=0
    rw [a.left_inv hxA,he0]
  · intro y hy
    have hyA : y∈a.source:=hy.1
    have hyt : a y∈t.source:=hy.2
    rw [htSrc] at hyt
    have hyEU : a.symm (a y)∈e.source∩U:=hyt.2
    rw [a.left_inv hyA] at hyEU
    exact ⟨hyEU.2,by change e (a.symm (a y))=e y;rw [a.left_inv hyA]⟩

private theorem singleton_flat {m : ℕ} {X : CMfd.{u} m} (x : X)
    (Θ : LocalHolomorphicEquivAt (n:=m) (chartAt (ComplexModel m) x x))
    (h0 : Θ.toFun (chartAt (ComplexModel m) x x)=0) :
    ∀{y : X},y∈(chartAt (ComplexModel m) x).source →
      chartAt (ComplexModel m) x y∈Θ.source →
      (y∈({x} : Set X)↔Θ.toFun (chartAt (ComplexModel m) x y)∈complexCoordinatePlane m 0) := by
  intro y hy hyΘ
  constructor
  · intro hyx
    rw [mem_singleton_iff.mp hyx,h0]
    intro i hi
    rfl
  · intro hz
    have hzero : Θ.toFun (chartAt (ComplexModel m) x y)=0:=by
      ext i
      exact hz i (Nat.zero_le _)
    have heq : chartAt (ComplexModel m) x y=chartAt (ComplexModel m) x x:=by
      calc
        _=Θ.invFun (Θ.toFun (chartAt (ComplexModel m) x y)):=(Θ.left_inv _ hyΘ).symm
        _=Θ.invFun (Θ.toFun (chartAt (ComplexModel m) x x)):=by rw [hzero,h0]
        _=_:=Θ.left_inv _ Θ.center_mem_source
    exact (chartAt (ComplexModel m) x).injOn hy (mem_chart_source _ x) heq

private theorem singleton_interior_empty {n : ℕ} {X : CMfd.{u} (n+1)}
    (e : OpenPartialHomeomorph X (ComplexModel (n+1))) (x : X) (hx : x∈e.source) :
    interior ({x} : Set X)=∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  have hyx : y=x:=mem_singleton_iff.mp (interior_subset hy)
  subst y
  have hopen : IsOpen ({x} : Set X):=by
    apply isOpen_iff_mem_nhds.mpr
    intro y hyx
    rw [mem_singleton_iff.mp hyx]
    exact mem_interior_iff_mem_nhds.mp hy
  have him:=e.isOpen_image_of_subset_source hopen (singleton_subset_iff.mpr hx)
  rw [image_singleton] at him
  exact not_isOpen_singleton (e x) him

private theorem strict_in_inherited_chart {m : ℕ} {X : CMfd.{u} m} {C B : Set X}
    [Fact (IsClosedSubmanifold m C)] (hCi : interior C=∅) (c : FlatChart m C)
    {S : Finset (Fin m)}
    (hflat : ∀{y : X},y∈(chartAt (ComplexModel m) c.y₀).source →
      chartAt (ComplexModel m) c.y₀ y∈c.Φ.source →
      (y∈B↔c.Φ.toFun (chartAt (ComplexModel m) c.y₀ y)∈coordSubspace S)) :
    ∀u∈c.source,u∈geoStrictTransform (blowupProj m C) C B↔
      c.j∉S ∧ c.toFun u∈coordSubspace S := by
  have hπ:=isBlowupAlong_blowupProj (n:=m) (C:=C) hCi
  have hmax:=IsManifold.subset_maximalAtlas (I:=𝓘(ℂ,ComplexModel m)) (n:=∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  have hWs : ∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ c.toFun u:=by
    intro u hu
    exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (c.isOpen_source.mem_nhds hu)
  intro u hu
  apply mem_geoStrictTransform_iff_of_chart hπ c.hsrc c.hflat hflat c.hj c.isOpen_source hWs
    (fun v hv=>⟨hv.1,c.monomial_toFun hv⟩) ?_ hu
  intro ℓ hℓs hℓπ v hv hw
  obtain ⟨ℓ₀,hℓ₀,huniq⟩:=existsUnique_monomialLift hπ c.hsrc c.hflat c.hj
  have he1 : ℓ=ℓ₀:=huniq ℓ ⟨hℓs,hℓπ⟩
  have he2 : flatParameterLift c=ℓ₀:=huniq (flatParameterLift c)
    ⟨flatParameterLift_contMDiff c,flatParameterLift_proj c⟩
  rw [he1,←he2]
  exact c.left_inv hv

section Generic
variable {n : ℕ} {X : CMfd.{u} (n+1)}

/-- Ordinary inherited chart/masks derive the NEXT point chart and domain.
There is deliberately no new-point cosupport conclusion. -/
theorem exists_inherited_vertical_point_chart {k : ℕ}
    (M : MarkedIdeal (n+1) X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (e : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (he : e∈atlas (ComplexModel (n+1)) X) (hxe : x∈e.source) (he0 : e x=0)
    (U : Set X) (hU : IsOpen U) (hxU : x∈U) (hUs : U⊆e.source)
    (SN : Finset (Fin (n+1))) (hSN : Fin.last n∉SN)
    (hN : ∀y∈U,y∈M.N↔e y∈coordSubspace SN)
    (SE : Fin M.E.length→Finset (Fin (n+1)))
    (hE : ∀i,x∈M.E.get i→∀y∈U,y∈M.E.get i↔e y∈coordSubspace (SE i)) :
    let C : Set X:={x}
    let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(singleton_geometry_and_coherence x).1⟩
    let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
    let π : Y→X:=blowupProj (n+1) C
    ∃c : FlatChart (n+1) C,
      c.y₀=x ∧ c.k=0 ∧ c.j=Fin.last n ∧
      (0 : ComplexModel (n+1))∈c.target ∧
      let z:=c.invFun 0
      z∈c.source ∧ π z=x ∧ c.toFun z=0 ∧
      M.IsAdmissibleCentre C ∧ IsBlowupAlong (n+1) C π ∧
      z∈(M.geoTransform C π).N ∧
      (∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun u) ∧
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (flatParameterLift c) ∧
      (∀u∈c.source,π u∈U ∧ e (π u)=monomial 0 (Fin.last n) (c.toFun u)) ∧
      (∀u∈c.source,u∈(M.geoTransform C π).N↔c.toFun u∈coordSubspace SN) ∧
      (∀i,x∈M.E.get i→∀u∈c.source,
        u∈geoStrictTransform π C (M.E.get i)↔
          Fin.last n∉SE i ∧ c.toFun u∈coordSubspace (SE i)) ∧
      (∀i,x∉M.E.get i→∀u∈c.source,u∉geoStrictTransform π C (M.E.get i)) ∧
      (∀u∈c.source,u∈π ⁻¹' C↔c.toFun u (Fin.last n)=0) ∧
      IsInvDomain k (M.geoTransform C π) ∧
      (M.geoTransform C π).d=M.d ∧
      (M.geoTransform C π).E=M.E.map (geoStrictTransform π C)++[π ⁻¹' C] ∧
      (M.geoTransform C π).E.length=M.E.length+1 := by
  dsimp only
  let C : Set X:={x}
  let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(singleton_geometry_and_coherence x).1⟩
  let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π : Y→X:=blowupProj (n+1) C
  let V : Set X:=U∩⋂i : Fin M.E.length,if x∈M.E.get i then Set.univ else (M.E.get i)ᶜ
  have hVo : IsOpen V:=hU.inter (isOpen_iInter_of_finite fun i=>by
    split_ifs
    · exact isOpen_univ
    · exact (hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem M.E i)).isOpen_compl)
  have hxV : x∈V:=⟨hxU,mem_iInter.mpr fun i=>by split_ifs with hi <;> simp_all⟩
  obtain ⟨Θ,hΘs,hΘ0,hΘdom⟩:=exists_inherited_coordinates e he x hxe he0 V hVo hxV
    (fun _ hy=>hUs hy.1)
  let c : FlatChart (n+1) C:={
    y₀:=x
    k:=0
    Φ:=Θ
    hsrc:=hΘs
    hflat:=singleton_flat x Θ hΘ0
    j:=Fin.last n
    hj:=Nat.zero_le _ }
  have hCi : interior C=∅:=singleton_interior_empty e x hxe
  have hπ : IsBlowupAlong (n+1) C π:=isBlowupAlong_blowupProj (n:=n+1) (C:=C) hCi
  have hC : M.IsAdmissibleCentre C:=⟨(singleton_geometry_and_coherence x).1,
    fun y hy=>by rw [mem_singleton_iff.mp hy];exact hx,
    hasNormalCrossings_singleton x hM.isWellFormed.isSNCDivisor⟩
  have hc0 : (0 : ComplexModel (n+1))∈c.target:=by
    change monomial 0 (Fin.last n) 0∈Θ.target
    have hm : monomial 0 (Fin.last n) (0 : ComplexModel (n+1))=0:=by
      ext i
      simp [monomial_apply]
    rw [hm,←hΘ0]
    exact Θ.mapsTo_toFun Θ.center_mem_source
  have hz : c.invFun 0∈c.source:=c.map_target hc0
  have hz0 : c.toFun (c.invFun 0)=0:=c.right_inv hc0
  have hzp : π (c.invFun 0)=x:=by
    change (c.invFun 0).base=x
    rw [c.base_invFun hc0]
    exact (c.pt_mem_iff hc0).mpr (by rfl)
  have hSourceN : ∀{y : X},y∈(chartAt (ComplexModel (n+1)) x).source→
      chartAt (ComplexModel (n+1)) x y∈Θ.source→
      (y∈M.N↔Θ.toFun (chartAt (ComplexModel (n+1)) x y)∈coordSubspace SN):=by
    intro y hy hyΘ
    obtain ⟨hyV,hyEq⟩:=hΘdom y ⟨hy,hyΘ⟩
    change y∈M.N↔flatMap Θ y∈coordSubspace SN
    rw [hyEq]
    exact hN y hyV.1
  have hSourceE : ∀i,x∈M.E.get i→∀{y : X},y∈(chartAt (ComplexModel (n+1)) x).source→
      chartAt (ComplexModel (n+1)) x y∈Θ.source→
      (y∈M.E.get i↔Θ.toFun (chartAt (ComplexModel (n+1)) x y)∈coordSubspace (SE i)):=by
    intro i hi y hy hyΘ
    obtain ⟨hyV,hyEq⟩:=hΘdom y ⟨hy,hyΘ⟩
    change y∈M.E.get i↔flatMap Θ y∈coordSubspace (SE i)
    rw [hyEq]
    exact hE i hi y hyV.1
  have hN':=strict_in_inherited_chart hCi c hSourceN
  have hE':=fun i hi=>strict_in_inherited_chart hCi c (hSourceE i hi)
  have hmax:=IsManifold.subset_maximalAtlas (I:=𝓘(ℂ,ComplexModel (n+1))) (n:=∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  have hWs : ∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun u:=by
    intro u hu
    exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (c.isOpen_source.mem_nhds hu)
  have hBase : ∀u∈c.source,π u∈V ∧ e (π u)=monomial 0 (Fin.last n) (c.toFun u):=by
    intro u hu
    obtain ⟨hUV,heq⟩:=hΘdom (π u) hu.1
    exact ⟨hUV,heq.symm.trans (c.monomial_toFun hu).symm⟩
  let T : BlowupTower X Y:=.step .refl C π hπ
  have hT : IsGeoTestTower M T:=⟨trivial,hC⟩
  refine ⟨c,rfl,rfl,rfl,hc0,hz,hzp,hz0,hC,hπ,?_,hWs,flatParameterLift_contMDiff c,
    (fun u hu=>⟨(hBase u hu).1.1,(hBase u hu).2⟩),?_,hE',?_,?_,?_,rfl,rfl,?_⟩
  · exact (hN' _ hz).mpr ⟨hSN,by rw [hz0];intro i hi;rfl⟩
  · intro u hu
    exact (hN' u hu).trans (and_iff_right hSN)
  · intro i hi u hu hmem
    have hnot : π u∉M.E.get i:=by
      have hvi:=mem_iInter.mp (hBase u hu).1.2 i
      simpa only [if_neg hi,mem_compl_iff] using hvi
    exact hnot (geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      (hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem M.E i)) hmem)
  · intro u hu
    exact (c.toFun_j_eq_zero_iff hu).symm
  · exact isInvDomain_geoTransformAlong hM T hT
  · exact length_E_geoTransform M C π

end Generic

private abbrev pointBlowupAmbient {m : ℕ} (X : CMfd.{u} m) (x : X) : CMfd.{u} m :=
  let _ : Fact (IsClosedSubmanifold m ({x} : Set X)):=⟨(singleton_geometry_and_coherence x).1⟩
  CMfd.of (BlowupSpace m ({x} : Set X))

private abbrev pointBlowupProjection {m : ℕ} (X : CMfd.{u} m) (x : X) :
    pointBlowupAmbient X x→X:=blowupProj m ({x} : Set X)

private abbrev pointTransformRecord {m : ℕ} (X : CMfd.{u} m)
    (M : MarkedIdeal m X) (x : X) : MarkedIdeal m (pointBlowupAmbient X x):=
  M.geoTransform ({x} : Set X) (pointBlowupProjection X x)

private abbrev recordMark {m : ℕ} (X : CMfd.{u} m) (M : MarkedIdeal m X) : ℕ:=
  @MarkedIdeal.d m X.carrier X.topologicalSpace X.chartedSpace M

private abbrev recordBoundary {m : ℕ} (X : CMfd.{u} m) (M : MarkedIdeal m X) : List (Set X):=
  @MarkedIdeal.E m X.carrier X.topologicalSpace X.chartedSpace M

private abbrev pointTransformDomain {m : ℕ} (X : CMfd.{u} m)
    (M : MarkedIdeal m X) (x : X) (k : ℕ) : Prop:=
  IsInvDomain k (pointTransformRecord X M x)

/- Reducible OUTPUT notation only: this body is EVERY original geometry,
native domain/mark/full-E/clock, coordinate and empty-slot field. The public
producer constructs c₁ existentially; c₁ is not an ordinary input premise. -/
private abbrev secondChartOutput {m k : ℕ} (A : CMfd.{u} m)
    (M : MarkedIdeal m A) (hM : IsInvDomain k M) (x : A) (hx : x∈M.cosupp)
    (Φ : LocalHolomorphicEquivAt (n:=m) (chartAt (ComplexModel m) x x))
    (c₁ : FlatChart (m+1) ({(x,0)} : Set (projectionAmbient A)))
    (SN : Finset (Fin (m+1))) : Prop:=
  let p : projectionAmbient A:=(x,0)
  let C₁ : Set (projectionAmbient A):={p}
  let _ : Fact (IsClosedSubmanifold (m+1) C₁):=⟨(projection_point_centre M hM x hx).1.1⟩
  let Y₁ : CMfd.{u} (m+1):=CMfd.of (BlowupSpace (m+1) C₁)
  let π₁ : Y₁→projectionAmbient A:=blowupProj (m+1) C₁
  let Q₁ : MarkedIdeal (m+1) Y₁:=(projectionTest M).geoTransform C₁ π₁
  Φ.source⊆(chartAt (ComplexModel m) x).target ∧
  Φ.toFun (chartAt (ComplexModel m) x x)=0 ∧
  c₁.k=0 ∧ c₁.j=Fin.last m ∧ Fin.last m∉SN ∧
  (0 : ComplexModel (m+1))∈c₁.target ∧
  let z₁ : Y₁:=c₁.invFun 0
  z₁∈c₁.source ∧ π₁ z₁=p ∧ c₁.toFun z₁=0 ∧
  IsBlowupAlong (m+1) C₁ π₁ ∧ IsInvDomain (k+1) Q₁ ∧ z₁∈Q₁.cosupp ∧
  Q₁.E=M.E.map (fun H=>geoStrictTransform π₁ C₁ ((Prod.fst : projectionAmbient A→A) ⁻¹' H))++
    [geoStrictTransform π₁ C₁ (horizontal A),π₁ ⁻¹' C₁] ∧
  let C₂ : Set Y₁:={z₁}
  let Y₂ : CMfd.{u} (m+1):=pointBlowupAmbient Y₁ z₁
  let π₂ : Y₂→Y₁:=pointBlowupProjection Y₁ z₁
  let Q₂ : MarkedIdeal (m+1) Y₂:=pointTransformRecord Y₁ Q₁ z₁
  pointTransformDomain Y₁ Q₁ z₁ (k+1) ∧ recordMark Y₂ Q₂=recordMark A M ∧
  (recordBoundary Y₂ Q₂)=Q₁.E.map (geoStrictTransform π₂ C₂)++[π₂ ⁻¹' C₂] ∧
  (recordBoundary Y₂ Q₂).length=M.E.length+3 ∧
  ∃(SE₁ : Fin Q₁.E.length→Finset (Fin (m+1))) (c₂ : FlatChart (m+1) C₂),
    (c₂.y₀=z₁ ∧ c₂.k=0 ∧ c₂.j=Fin.last m ∧
    (0 : ComplexModel (m+1))∈c₂.target ∧
    let z₂ : Y₂:=c₂.invFun 0
    z₂∈c₂.source ∧ π₂ z₂=z₁ ∧ c₂.toFun z₂=0 ∧
    Q₁.IsAdmissibleCentre C₂ ∧ IsBlowupAlong (m+1) C₂ π₂ ∧
    z₂∈Q₂.N ∧
    (∀(u : Y₂),u∈c₂.source →ContMDiffAt 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ c₂.toFun u) ∧
    ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ (flatParameterLift c₂) ∧
    (∀(u : Y₂),u∈c₂.source →π₂ u∈c₁.source ∧ c₁.toFun (π₂ u)=monomial 0 (Fin.last m) (c₂.toFun u)) ∧
    (∀(u : Y₂),u∈c₂.source →(u∈Q₂.N↔c₂.toFun u∈coordSubspace SN)) ∧
    (∀(i : Fin Q₁.E.length),z₁∈Q₁.E.get i→∀(u : Y₂),u∈c₂.source →
      (u∈geoStrictTransform π₂ C₂ (Q₁.E.get i)↔
        Fin.last m∉SE₁ i ∧ c₂.toFun u∈coordSubspace (SE₁ i))) ∧
    (∀(i : Fin Q₁.E.length),z₁∉Q₁.E.get i→∀(u : Y₂),u∈c₂.source →u∉geoStrictTransform π₂ C₂ (Q₁.E.get i)) ∧
    (∀(u : Y₂),u∈c₂.source →(u∈π₂ ⁻¹' C₂↔c₂.toFun u (Fin.last m)=0))) ∧
    (∀(u : Y₂),u∈c₂.source →∀i : Fin m,
      flatCoord Φ i (π₁ (π₂ u)).1=(c₂.toFun u (Fin.last m))^2*c₂.toFun u (i.castAdd 1)) ∧
    (∀(u : Y₂),u∈c₂.source →(π₁ (π₂ u)).2 0=c₂.toFun u (Fin.last m)) ∧
    (∀(u : Y₂),u∈c₂.source →u∉geoStrictTransform π₂ C₂ (geoStrictTransform π₁ C₁ (horizontal A)) ∧
      u∉geoStrictTransform π₂ C₂ (π₁ ⁻¹' C₁))

/-- Original ordinary inputs derive a SECOND last-pivot chart on the SAME
one-projection history. No order/cosupport at the second selected point. -/
theorem exists_second_vertical_point_chart {m k : ℕ} {A : CMfd.{u} m}
    (M : MarkedIdeal m A) (hM : IsInvDomain k M) (x : A) (hx : x∈M.cosupp) :
    ∃(Φ : LocalHolomorphicEquivAt (n:=m) (chartAt (ComplexModel m) x x))
      (c₁ : FlatChart (m+1) ({(x,0)} : Set (projectionAmbient A)))
      (SN : Finset (Fin (m+1))), secondChartOutput A M hM x hx Φ c₁ SN := by
  let p : projectionAmbient A:=(x,0)
  let C₁ : Set (projectionAmbient A):={p}
  let _ : Fact (IsClosedSubmanifold (m+1) C₁):=⟨(projection_point_centre M hM x hx).1.1⟩
  let Y₁ : CMfd.{u} (m+1):=CMfd.of (BlowupSpace (m+1) C₁)
  let π₁ : Y₁→projectionAmbient A:=blowupProj (m+1) C₁
  let Q₁ : MarkedIdeal (m+1) Y₁:=(projectionTest M).geoTransform C₁ π₁
  obtain ⟨Φ,c₁,SN,SE,hGeometry,hOrder⟩:=exists_projection_vertical_order M hM x hx
  rcases hGeometry with ⟨hΦs,hΦ0,_hc₁p,hc₁k,hc₁j,hOld,hLast,_hSourceN,_hSourceE,hSN,_hSE,hc₁0,
    hz₁Source,hz₁p,hz₁0,hπ₁,_hz₁N,_hWs₁,_hInv₁,hMon₁,hTargetN₁,hTargetE₁,hEmptyH₁,hBorn₁,
    hWindow,hQ₁,hdQ₁,hWord₁,hLength₁⟩
  let z₁ : Y₁:=c₁.invFun 0
  let C₂ : Set Y₁:={z₁}
  let Y₂ : CMfd.{u} (m+1):=pointBlowupAmbient Y₁ z₁
  let π₂ : Y₂→Y₁:=pointBlowupProjection Y₁ z₁
  let Q₂ : MarkedIdeal (m+1) Y₂:=pointTransformRecord Y₁ Q₁ z₁
  have hz₁p : π₁ z₁=p:=hz₁p
  have hWord₁ : Q₁.E=M.E.map (fun H=>geoStrictTransform π₁ C₁
      ((Prod.fst : projectionAmbient A→A) ⁻¹' H))++
      [geoStrictTransform π₁ C₁ (horizontal A),π₁ ⁻¹' C₁]:=hWord₁
  have hLength₁ : Q₁.E.length=M.E.length+2:=hLength₁
  have hMon₁ : ∀u∈c₁.source,monomial 0 (Fin.last m) (c₁.toFun u)=
      c₁.Φ.toFun (chartAt (ComplexModel (m+1)) c₁.y₀ (π₁ u)):=hMon₁
  have hz₁cos : z₁∈Q₁.cosupp:=hOrder.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨U,hU,hz₁U,hUs,_hAbsent₁⟩:=hWindow
  let SE₁ : Fin Q₁.E.length→Finset (Fin (m+1)):=
    fun i=>if hi : i.val<M.E.length then SE ⟨i.val,hi⟩ else {Fin.last m}
  have hGetOld (i : Fin Q₁.E.length) (hi : i.val<M.E.length) :
      Q₁.E.get i=geoStrictTransform π₁ C₁
        ((Prod.fst : projectionAmbient A→A) ⁻¹' M.E.get ⟨i.val,hi⟩):=by
    simp only [List.get_eq_getElem,hWord₁,List.getElem_append,List.length_map,hi,↓reduceDIte,
      List.getElem_map]
  have hGetH (i : Fin Q₁.E.length) (hi : i.val=M.E.length) :
      Q₁.E.get i=geoStrictTransform π₁ C₁ (horizontal A):=by
    simp [List.get_eq_getElem,hWord₁,hi]
  have hGetD (i : Fin Q₁.E.length) (hi : i.val=M.E.length+1) :
      Q₁.E.get i=π₁ ⁻¹' C₁:=by
    simp [List.get_eq_getElem,hWord₁,hi]
  have hMasks : ∀(i : Fin Q₁.E.length),z₁∈Q₁.E.get i→∀y∈U,
      y∈Q₁.E.get i↔c₁.homeo y∈coordSubspace (SE₁ i):=by
    intro i hInc y hy
    by_cases hi : i.val<M.E.length
    · have hiSrc : x∈M.E.get ⟨i.val,hi⟩:=by
        have hInc':=hInc
        rw [hGetOld i hi] at hInc'
        have hpre:=geoStrictTransform_subset_preimage hπ₁.contMDiff.continuous
          ((hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem M.E ⟨i.val,hi⟩)).preimage continuous_fst) hInc'
        change (π₁ z₁).1∈M.E.get ⟨i.val,hi⟩ at hpre
        rw [hz₁p] at hpre
        exact hpre
      simpa only [hGetOld i hi,SE₁,dif_pos hi,FlatChart.homeo_apply] using
        hTargetE₁ ⟨i.val,hi⟩ hiSrc y (hUs hy)
    · have hcases : i.val=M.E.length ∨ i.val=M.E.length+1:=by
        have hlt : i.val<M.E.length+2:=lt_of_lt_of_eq i.isLt hLength₁
        omega
      rcases hcases with hhi | hdi
      · exfalso
        rw [hGetH i hhi] at hInc
        exact hEmptyH₁ z₁ hz₁Source hInc
      · simpa only [hGetD i hdi,SE₁,dif_neg hi,FlatChart.homeo_apply,
          mem_coordSubspace_singleton] using hBorn₁ y (hUs hy)
  have he₁ : c₁.homeo∈atlas (ComplexModel (m+1)) Y₁:=
    atlasHomeo_mem_atlas c₁.toPartialEquiv (Or.inl ⟨c₁,rfl⟩)
  have hN₁ : ∀y∈U,y∈Q₁.N↔c₁.homeo y∈coordSubspace SN:=
    fun y hy=>hTargetN₁ y (hUs hy)
  obtain ⟨c₂,hGeometry₂⟩:=exists_inherited_vertical_point_chart Q₁ hQ₁ z₁ hz₁cos
    c₁.homeo he₁ hz₁Source hz₁0 U hU hz₁U hUs SN hSN hN₁ SE₁ hMasks
  rcases hGeometry₂ with ⟨hc₂p,hc₂k,hc₂j,hc₂0,hz₂Source,hz₂p,hz₂0,hC₂,hπ₂,hz₂N,
    hWs₂,hInv₂,hBase₂,hTargetN₂,hTargetE₂,hAbsent₂,hBorn₂,hQ₂,hdQ₂,hWord₂,hLength₂⟩
  have hLength₂ : (recordBoundary Y₂ Q₂).length=Q₁.E.length+1:=hLength₂
  have hWord₂ : recordBoundary Y₂ Q₂=Q₁.E.map (geoStrictTransform π₂ C₂)++[π₂ ⁻¹' C₂]:=hWord₂
  have hComp (u : Y₂) (hu : u∈c₂.source) :
      c₁.toFun (π₂ u)=monomial 0 (Fin.last m) (c₂.toFun u):=(hBase₂ u hu).2
  have hFirstSource (u : Y₂) (hu : u∈c₂.source) : π₂ u∈c₁.source:=hUs (hBase₂ u hu).1
  have hGeom₂ : c₂.y₀=z₁ ∧ c₂.k=0 ∧ c₂.j=Fin.last m ∧
      (0 : ComplexModel (m+1))∈c₂.target ∧
      let z₂ : Y₂:=c₂.invFun 0
      z₂∈c₂.source ∧ π₂ z₂=z₁ ∧ c₂.toFun z₂=0 ∧
      Q₁.IsAdmissibleCentre C₂ ∧ IsBlowupAlong (m+1) C₂ π₂ ∧ z₂∈Q₂.N ∧
      (∀(u : Y₂),u∈c₂.source →ContMDiffAt 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ c₂.toFun u) ∧
      ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ (flatParameterLift c₂) ∧
      (∀(u : Y₂),u∈c₂.source →π₂ u∈c₁.source ∧ c₁.toFun (π₂ u)=monomial 0 (Fin.last m) (c₂.toFun u)) ∧
      (∀(u : Y₂),u∈c₂.source →(u∈Q₂.N↔c₂.toFun u∈coordSubspace SN)) ∧
      (∀(i : Fin Q₁.E.length),z₁∈Q₁.E.get i→∀(u : Y₂),u∈c₂.source →(u∈geoStrictTransform π₂ C₂ (Q₁.E.get i)↔
        Fin.last m∉SE₁ i ∧ c₂.toFun u∈coordSubspace (SE₁ i))) ∧
      (∀(i : Fin Q₁.E.length),z₁∉Q₁.E.get i→∀(u : Y₂),u∈c₂.source →u∉geoStrictTransform π₂ C₂ (Q₁.E.get i)) ∧
      (∀(u : Y₂),u∈c₂.source →(u∈π₂ ⁻¹' C₂↔c₂.toFun u (Fin.last m)=0)):=
    ⟨hc₂p,hc₂k,hc₂j,hc₂0,hz₂Source,hz₂p,hz₂0,hC₂,hπ₂,hz₂N,hWs₂,hInv₂,
      fun u hu=>⟨hFirstSource u hu,hComp u hu⟩,hTargetN₂,hTargetE₂,hAbsent₂,hBorn₂⟩
  refine ⟨Φ,c₁,SN,hΦs,hΦ0,hc₁k,hc₁j,hSN,hc₁0,hz₁Source,hz₁p,hz₁0,hπ₁,hQ₁,hz₁cos,hWord₁,
    hQ₂,hdQ₂.trans hdQ₁,hWord₂,(by
      change (recordBoundary Y₂ Q₂).length=M.E.length+3
      calc
        _=Q₁.E.length+1:=hLength₂
        _=(M.E.length+2)+1:=congrArg (fun t : ℕ=>t+1) hLength₁
        _=M.E.length+3:=by omega),SE₁,c₂,hGeom₂,?_,?_,?_⟩
  · intro u hu i
    have hneq : i.castAdd 1≠Fin.last m:=by
      intro h
      have hv:=congrArg Fin.val h
      change i.val=m at hv
      exact (Nat.ne_of_lt i.isLt) hv
    have hOldMono (w : ComplexModel (m+1)) :
        monomial 0 (Fin.last m) w (i.castAdd 1)=w (i.castAdd 1)*w (Fin.last m):=by
      simp [monomial_apply,hneq]
    have hLastMono (w : ComplexModel (m+1)) :
        monomial 0 (Fin.last m) w (Fin.last m)=w (Fin.last m):=by
      simp [monomial_apply]
    calc
      flatCoord Φ i (π₁ (π₂ u)).1=flatCoord c₁.Φ (i.castAdd 1) (π₁ (π₂ u)):=
        (hOld (π₁ (π₂ u)) i).symm
      _=monomial 0 (Fin.last m) (c₁.toFun (π₂ u)) (i.castAdd 1):=
        (congrArg (fun w : ComplexModel (m+1)=>w (i.castAdd 1))
          (hMon₁ (π₂ u) (hFirstSource u hu))).symm
      _=(c₂.toFun u (Fin.last m))^2*c₂.toFun u (i.castAdd 1):=by
        rw [hComp u hu,hOldMono,hOldMono,hLastMono]
        ring
  · intro u hu
    calc
      (π₁ (π₂ u)).2 0=flatCoord c₁.Φ (Fin.last m) (π₁ (π₂ u)):=
        (hLast (π₁ (π₂ u))).symm
      _=monomial 0 (Fin.last m) (c₁.toFun (π₂ u)) (Fin.last m):=
        (congrArg (fun w : ComplexModel (m+1)=>w (Fin.last m))
          (hMon₁ (π₂ u) (hFirstSource u hu))).symm
      _=c₂.toFun u (Fin.last m):=by rw [hComp u hu];simp [monomial_apply]
  · intro u hu
    constructor
    · intro hmem
      have hpre:=geoStrictTransform_subset_preimage hπ₂.contMDiff.continuous
        (show IsClosed (geoStrictTransform π₁ C₁ (horizontal A)) from isClosed_closure) hmem
      exact hEmptyH₁ (π₂ u) (hFirstSource u hu) hpre
    · let iD : Fin Q₁.E.length:=⟨M.E.length+1,by rw [hLength₁];omega⟩
      have hiD : Q₁.E.get iD=π₁ ⁻¹' C₁:=hGetD iD rfl
      have hzD : z₁∈Q₁.E.get iD:=by
        rw [hiD]
        change π₁ z₁∈C₁
        rw [hz₁p]
        exact mem_singleton p
      have hSD : SE₁ iD={Fin.last m}:=by simp [SE₁,iD]
      intro hmem
      have h:=((hTargetE₂ iD hzD u hu).mp (hiD.symm ▸ hmem)).1
      rw [hSD] at h
      exact h (Finset.mem_singleton_self _)

end
end Hironaka.HironakaActualInheritedVerticalPointChart
