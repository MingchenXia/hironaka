import Hironaka.Resolution.HironakaActualProjectionTestRecord
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Resolution.HironakaSmoothSubmersionUniversalBlowupChartEquality
import Hironaka.Invariant.InvDomainTowerAlong

/-! Actual projected singleton and a constructed vertical chart. The fibre
pivot is LAST; all original boundary labels and the horizontal slot survive.
No order amplification, future lower comparison or CAN assertion. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProjectionVerticalBlowupChart
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings NormalCrossingsInvariance ProductComplexManifold MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec BlowupTowers BlowupStrictSubmanifold
  BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts BlowupSNCTransform
  BlowupLocalSurjectivity InvDomainTowerAlong
  HironakaActualProjectionTestRecord HironakaOneDimensionalCanonicalSuperlevels
  HironakaSmoothSubmersionUniversalBlowupChartEquality
open scoped ProductComplexManifold
variable {n : ℕ} {X : CMfd.{u} n}

private def liftAxes (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.castAddEmb 1)

private theorem last_not_lift (S : Finset (Fin n)) : Fin.last n ∉ liftAxes S := by
  intro h
  obtain ⟨i,_hi,he⟩:=Finset.mem_map.mp h
  have hv:=congrArg Fin.val he
  change i.val=n at hv
  exact (Nat.ne_of_lt i.isLt) hv

private theorem split_old (w : ComplexModel (n+1)) (i : Fin n) :
    ((prodModelEquiv n 1).symm w).1 i=w (i.castAdd 1) := by
  rfl

private theorem split_normal (w : ComplexModel (n+1)) (i : Fin 1) :
    ((prodModelEquiv n 1).symm w).2 i=w (i.natAdd n) := by
  rfl

private theorem product_old (a : ComplexModel n) (b : ComplexModel 1) (i : Fin n) :
    prodModelEquiv n 1 (a,b) (i.castAdd 1)=a i := by
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.1 i)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [split_old] at h
  exact h

private theorem product_last (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b) (Fin.last n)=b 0 := by
  have he : Fin.last n=(0 : Fin 1).natAdd n:=Fin.ext (by simp)
  rw [he]
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.2 0)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [split_normal] at h
  exact h

private theorem product_mask (a : ComplexModel n) (b : ComplexModel 1) (S : Finset (Fin n)) :
    prodModelEquiv n 1 (a,b)∈coordSubspace (liftAxes S) ↔ a∈coordSubspace S := by
  constructor
  · intro h i hi
    exact (product_old a b i) ▸ h (i.castAdd 1) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · intro h j hj
    obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hj
    change prodModelEquiv n 1 (a,b) (i.castAdd 1)=0
    rw [product_old]
    exact h i hi

private theorem product_normal (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b)∈coordSubspace {Fin.last n} ↔ b=0 := by
  constructor
  · intro h
    ext i
    obtain rfl : i=0:=Subsingleton.elim _ _
    simpa only [product_last,PiLp.zero_apply] using h (Fin.last n) (Finset.mem_singleton_self _)
  · intro hb j hj
    rw [Finset.mem_singleton.mp hj,product_last,hb]
    rfl

private def productCoordinates (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1)) :
    LocalHolomorphicEquivAt (n := n+1) (chartAt (ComplexModel (n+1)) p p) where
  source := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.source
  target := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  isOpen_target := Φ.isOpen_target.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  center_mem_source := by
    simpa only [mem_preimage,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply]
      using Φ.center_mem_source
  toFun w := prodModelEquiv n 1
    (Φ.toFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2-p.2)
  invFun w := prodModelEquiv n 1
    (Φ.invFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2+p.2)
  toFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.toFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.sub_const p.2).differentiableOn)
  invFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.invFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.add_const p.2).differentiableOn)
  mapsTo_toFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_toFun hw
  mapsTo_invFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_invFun hw
  left_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.left_inv _ hw,sub_add_cancel,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w
  right_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.right_inv _ hw,add_sub_cancel_right,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w

private theorem product_family {ι : Type*} (A : ι → Set X) (S : ι → Finset (Fin n))
    (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) p.1).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) p.1 p.1)=0)
    (hflat : ∀i,p.1∈A i → ∀ {y : X},y∈(chartAt (ComplexModel n) p.1).source →
      chartAt (ComplexModel n) p.1 y∈Φ.source →
      (y∈A i ↔ Φ.toFun (chartAt (ComplexModel n) p.1 y)∈coordSubspace (S i))) :
    let Ψ:=productCoordinates p Φ
    Ψ.source⊆(chartAt (ComplexModel (n+1)) p).target ∧
      Ψ.toFun (chartAt (ComplexModel (n+1)) p p)=0 ∧
      ∀i,p∈(Sum.elim (fun i=>(Prod.fst : projectionAmbient X → X) ⁻¹' A i)
        (fun _ : Unit=>horizontal X)) i →
        ∀ {y : projectionAmbient X},y∈(chartAt (ComplexModel (n+1)) p).source →
          chartAt (ComplexModel (n+1)) p y∈Ψ.source →
          (y∈(Sum.elim (fun i=>(Prod.fst : projectionAmbient X → X) ⁻¹' A i)
            (fun _ : Unit=>horizontal X)) i ↔
            Ψ.toFun (chartAt (ComplexModel (n+1)) p y)∈coordSubspace
              ((Sum.elim (fun i=>liftAxes (S i)) (fun _ : Unit=>{Fin.last n})) i)) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro w hw
    change w∈(prodChart (chartAt (ComplexModel n) p.1) (chartAt (ComplexModel 1) p.2)).target
    rw [prodChart_target]
    exact ⟨hsrc hw,Set.mem_univ _⟩
  · change prodModelEquiv n 1
      (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).1,
        ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).2-p.2)=0
    have hzero : Φ.toFun (chartAt (ComplexModel n) p.1 p.1)=0:=h0
    simp only [chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
      chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,hzero,sub_self]
    exact (prodModelEquiv n 1).map_zero
  · rintro (i | u) hp q hq hqΦ
    · have hpair : q∈(chartAt (ComplexModel n) p.1).source ×ˢ
          (chartAt (ComplexModel 1) p.2).source:=by
        simpa only [complexChartAt,chartAt_prod,prodChart_source] using hq
      have hbase : q.1∈(chartAt (ComplexModel n) p.1).source:=hpair.1
      have hΦ : chartAt (ComplexModel n) p.1 q.1∈Φ.source:=by
        simpa only [productCoordinates,complexChartAt,chartAt_prod,prodChart_apply,
          ContinuousLinearEquiv.symm_apply_apply,mem_preimage] using hqΦ
      change q.1∈A i ↔ _
      rw [hflat i hp hbase hΦ]
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,Sum.elim_inl]
        using (product_mask (Φ.toFun (chartAt (ComplexModel n) p.1 q.1))
          ((chartAt (ComplexModel 1) p.2) q.2-p.2) (S i)).symm
    · change q.2=0 ↔ _
      change p.2=0 at hp
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
        chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,Sum.elim_inr,hp,sub_zero]
        using (product_normal (Φ.toFun (chartAt (ComplexModel n) p.1 q.1)) q.2).symm


private theorem singleton_flat {m : ℕ} {A : CMfd.{u} m} (x : A)
    (Φ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel m) x x)=0) :
    ∀ {y : A}, y∈(chartAt (ComplexModel m) x).source →
      chartAt (ComplexModel m) x y∈Φ.source →
      (y∈({x} : Set A) ↔ Φ.toFun (chartAt (ComplexModel m) x y)∈complexCoordinatePlane m 0) := by
  intro y hy hyΦ
  constructor
  · intro hyx
    rw [mem_singleton_iff.mp hyx,h0]
    intro i hi
    rfl
  · intro h
    have hz : Φ.toFun (chartAt (ComplexModel m) x y)=0 := by
      ext i
      exact h i (Nat.zero_le _)
    have he : chartAt (ComplexModel m) x y=chartAt (ComplexModel m) x x := by
      calc
        _=Φ.invFun (Φ.toFun (chartAt (ComplexModel m) x y)) := (Φ.left_inv _ hyΦ).symm
        _=Φ.invFun (Φ.toFun (chartAt (ComplexModel m) x x)) := by rw [hz,h0]
        _=_ := Φ.left_inv _ Φ.center_mem_source
    exact (chartAt (ComplexModel m) x).injOn hy (mem_chart_source _ x) he

private theorem point_closed {m : ℕ} {A : CMfd.{u} m} (x : A) :
    IsClosedSubmanifold m ({x} : Set A) := by
  refine ⟨isClosed_singleton,?_⟩
  intro y hy
  rw [mem_singleton_iff.mp hy]
  obtain ⟨Φ,hs,h0⟩:=exists_centred_coordinates (n := m) x
  exact ⟨0,⟨Nat.zero_le _,mem_singleton x,Φ,hs,h0,singleton_flat x Φ h0⟩⟩

/-- Genuine whole projected cosupport and native SNC imply actual point
admissibility. The product singleton is nowhere dense. -/
theorem projection_point_centre {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (x : X) (hx : x∈M.cosupp) :
    (projectionTest M).IsAdmissibleCentre ({(x,0)} : Set (projectionAmbient X)) ∧
      interior ({(x,0)} : Set (projectionAmbient X))=∅ := by
  have hP:=projection_test_isInvDomain M hM
  have hcos:=(projection_test_dictionary M hM).2.2.2.2.2.2.2
  refine ⟨⟨point_closed (A := projectionAmbient X) (x,0),?_,hasNormalCrossings_singleton (x,0) hP.isWellFormed.isSNCDivisor⟩,?_⟩
  · intro y hy
    rw [mem_singleton_iff.mp hy,hcos]
    exact hx
  · have he : ({(x,0)} : Set (projectionAmbient X))=({x} : Set X) ×ˢ ({0} : Set (ComplexModel 1)) := by
      ext y
      simp only [mem_singleton_iff,mem_prod]
      exact Prod.ext_iff
    rw [he,interior_prod_eq]
    have hline : interior ({0} : Set (ComplexModel 1))=∅ := interior_singleton (0 : ComplexModel 1)
    rw [hline,prod_empty]

private theorem strict_in_flat_chart {m : ℕ} {A : CMfd.{u} m} {C B : Set A}
    [Fact (IsClosedSubmanifold m C)] (hCi : interior C=∅) (c : FlatChart m C)
    {T : Finset (Fin m)}
    (hflat : ∀ {y : A},y∈(chartAt (ComplexModel m) c.y₀).source →
      chartAt (ComplexModel m) c.y₀ y∈c.Φ.source →
      (y∈B ↔ c.Φ.toFun (chartAt (ComplexModel m) c.y₀ y)∈coordSubspace T)) :
    ∀ u∈c.source,
      u∈geoStrictTransform (blowupProj m C) C B ↔ c.j∉T ∧ c.toFun u∈coordSubspace T := by
  have hπ:=isBlowupAlong_blowupProj (n := m) (C := C) hCi
  have hmax:=IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ComplexModel m)) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  have hWs : ∀ u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ c.toFun u := by
    intro u hu
    exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (c.isOpen_source.mem_nhds hu)
  intro u hu
  apply mem_geoStrictTransform_iff_of_chart hπ c.hsrc c.hflat hflat c.hj c.isOpen_source hWs
    (fun v hv=>⟨hv.1,c.monomial_toFun hv⟩) ?_ hu
  intro ℓ hℓs hℓπ v hv hw
  obtain ⟨ℓ₀,hℓ₀,huniq⟩:=existsUnique_monomialLift hπ c.hsrc c.hflat c.hj
  have he₁ : ℓ=ℓ₀:=huniq ℓ ⟨hℓs,hℓπ⟩
  have he₂ : flatParameterLift c=ℓ₀:=huniq (flatParameterLift c)
    ⟨flatParameterLift_contMDiff c,flatParameterLift_proj c⟩
  rw [he₁,←he₂]
  exact c.left_inv hv

/-- One actual vertical native blowup chart, constructed from the source
N/E coordinates. The explicit fibre pivot is last; the full global boundary
keeps old, horizontal (locally empty) and newborn slots. -/
theorem exists_projection_vertical_blowup_chart {k : ℕ}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    let p : projectionAmbient X:=(x,0)
    let C : Set (projectionAmbient X):={p}
    let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(projection_point_centre M hM x hx).1.1⟩
    let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
    let π : Y → projectionAmbient X:=blowupProj (n+1) C
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) C) (SN : Finset (Fin (n+1)))
      (SE : Fin M.E.length → Finset (Fin (n+1))),
      Φ.source⊆(chartAt (ComplexModel n) x).target ∧
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
      ((projectionTest M).geoTransform C π).E.length=M.E.length+2 := by
  dsimp only
  let p : projectionAmbient X:=(x,0)
  let C : Set (projectionAmbient X):={p}
  let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π : Y → projectionAmbient X:=blowupProj (n+1) C
  have hCi : interior C=∅:=(projection_point_centre M hM x hx).2
  have hπ : IsBlowupAlong (n+1) C π:=isBlowupAlong_blowupProj hCi
  obtain ⟨S₀,S,hFamily,hCard⟩:=hM.isWellFormed.isTransverse x (M.cosupp_subset_N hx)
  obtain ⟨Φ,hΦs,hΦ0,hΦflat⟩:=hFamily
  let Ψ:=productCoordinates p Φ
  obtain ⟨hΨs,hΨ0,hΨflat⟩:=product_family
    (fun o : Option (Fin M.E.length)=>o.elim M.N (fun i=>M.E.get i))
    (fun o=>o.elim S₀ S) p Φ hΦs hΦ0 hΦflat
  have hflatC : ∀ {y : projectionAmbient X},y∈(chartAt (ComplexModel (n+1)) p).source →
      chartAt (ComplexModel (n+1)) p y∈Ψ.source →
      (y∈C ↔ Ψ.toFun (chartAt (ComplexModel (n+1)) p y)∈complexCoordinatePlane (n+1) 0) :=
    singleton_flat p Ψ hΨ0
  let c : FlatChart (n+1) C:=⟨p,0,Ψ,hΨs,hflatC,Fin.last n,Nat.zero_le _⟩
  have hold (y : projectionAmbient X) (i : Fin n) :
      flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1 := by
    change prodModelEquiv n 1
      (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p y)).1,
        ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p y)).2-p.2) (i.castAdd 1)=_
    rw [product_old]
    simp only [chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,flatCoord,p]
  have hlast (y : projectionAmbient X) : flatCoord c.Φ (Fin.last n) y=y.2 0 := by
    change prodModelEquiv n 1
      (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p y)).1,
        ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p y)).2-p.2) (Fin.last n)=_
    rw [product_last]
    simp only [chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
      chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,p,sub_zero]
  have hc0 : (0 : ComplexModel (n+1))∈c.target := by
    change monomial 0 (Fin.last n) 0∈Ψ.target
    have hm : monomial 0 (Fin.last n) (0 : ComplexModel (n+1))=0 := by
      ext i
      simp [monomial_apply]
    rw [hm,←hΨ0]
    exact Ψ.mapsTo_toFun Ψ.center_mem_source
  have hz : c.invFun 0∈c.source:=c.map_target hc0
  have hz0 : c.toFun (c.invFun 0)=0:=c.right_inv hc0
  have hzp : π (c.invFun 0)=p := by
    change (c.invFun 0).base=p
    rw [c.base_invFun hc0]
    exact (c.pt_mem_iff hc0).mpr (by rfl)
  have hN : ∀ {y : projectionAmbient X},y∈(chartAt (ComplexModel (n+1)) p).source →
      chartAt (ComplexModel (n+1)) p y∈Ψ.source →
      (y∈(projectionTest M).N ↔ Ψ.toFun (chartAt (ComplexModel (n+1)) p y)∈coordSubspace (liftAxes S₀)) := by
    intro y hy hyΨ
    exact hΨflat (Sum.inl none) (M.cosupp_subset_N hx) hy hyΨ
  have hE : ∀i,x∈M.E.get i → ∀ {y : projectionAmbient X},
      y∈(chartAt (ComplexModel (n+1)) p).source →
      chartAt (ComplexModel (n+1)) p y∈Ψ.source →
      (y∈(Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i ↔
        Ψ.toFun (chartAt (ComplexModel (n+1)) p y)∈coordSubspace (liftAxes (S i))) := by
    intro i hi y hy hyΨ
    exact hΨflat (Sum.inl (some i)) hi hy hyΨ
  have hH : ∀ {y : projectionAmbient X},y∈(chartAt (ComplexModel (n+1)) p).source →
      chartAt (ComplexModel (n+1)) p y∈Ψ.source →
      (y∈horizontal X ↔ Ψ.toFun (chartAt (ComplexModel (n+1)) p y)∈coordSubspace {Fin.last n}) := by
    intro y hy hyΨ
    exact hΨflat (Sum.inr ()) (by rfl) hy hyΨ
  have hN' := strict_in_flat_chart hCi c hN
  have hE' := fun i hi=>strict_in_flat_chart hCi c (hE i hi)
  have hH' := strict_in_flat_chart hCi c hH
  have hmax:=IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ComplexModel (n+1))) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  have hWs : ∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun u := by
    intro u hu
    exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (c.isOpen_source.mem_nhds hu)
  let T : BlowupTower (projectionAmbient X) Y:=.step .refl C π hπ
  have hT : IsGeoTestTower (projectionTest M) T:=⟨trivial,(projection_point_centre M hM x hx).1⟩
  let V : Set (projectionAmbient X):=⋂ i : Fin M.E.length,
    if x∈M.E.get i then Set.univ else ((Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i)ᶜ
  have hVo : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact isOpen_univ
    · exact ((hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem M.E i)).preimage continuous_fst).isOpen_compl
  have hpV : p∈V := by
    apply mem_iInter.mpr
    intro i
    split_ifs with hi
    · trivial
    · exact hi
  have hWindow : ∃O : Set Y,IsOpen O ∧ c.invFun 0∈O ∧ O⊆c.source ∧
      ∀i,x∉M.E.get i → ∀u∈O,
        u∉geoStrictTransform π C ((Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i) := by
    refine ⟨c.source∩π ⁻¹' V,c.isOpen_source.inter (hVo.preimage hπ.contMDiff.continuous),
      ⟨hz,by change π (c.invFun 0)∈V; rw [hzp]; exact hpV⟩,inter_subset_left,?_⟩
    intro i hi u hu hmem
    have hnot : π u∉(Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i := by
      have hvi:=mem_iInter.mp hu.2 i
      simpa only [if_neg hi,mem_compl_iff] using hvi
    exact hnot (geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      ((hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem M.E i)).preimage continuous_fst) hmem)
  have hDom:=isInvDomain_geoTransformAlong (projection_test_isInvDomain M hM) T hT
  refine ⟨Φ,c,liftAxes S₀,fun i=>liftAxes (S i),hΦs,hΦ0,rfl,rfl,rfl,hold,hlast,
    (fun y hy=>hN hy.1 hy.2),(fun i hi y hy=>hE i hi hy.1 hy.2),last_not_lift S₀,
    fun i=>last_not_lift (S i),hc0,hz,hzp,hz0,hπ,?_,hWs,flatParameterLift_contMDiff c,
    ?_,?_,?_,?_,?_,hWindow,?_,rfl,?_,?_⟩
  · exact (hN' _ hz).mpr ⟨last_not_lift S₀,by rw [hz0]; intro i hi; rfl⟩
  · intro u hu
    exact c.monomial_toFun hu
  · intro u hu
    exact (hN' u hu).trans (and_iff_right (last_not_lift S₀))
  · intro i hi u hu
    exact (hE' i hi u hu).trans (and_iff_right (last_not_lift (S i)))
  · intro u hu hmem
    exact ((hH' u hu).mp hmem).1 (Finset.mem_singleton_self _)
  · intro u hu
    exact (c.toFun_j_eq_zero_iff hu).symm
  · exact hDom
  · simp only [geoTransform_E,(projection_test_dictionary M hM).2.2.2.1,List.map_append,
      List.map_map,List.map_singleton,List.append_assoc,List.singleton_append,Function.comp_def]
  · rw [length_E_geoTransform,(projection_test_dictionary M hM).2.2.2.2.1]
end
end Hironaka.HironakaActualProjectionVerticalBlowupChart
