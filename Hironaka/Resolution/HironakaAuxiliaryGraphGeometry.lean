import Hironaka.Analytic.ProductComplexManifold
import Hironaka.Analytic.ConstantRankSubmanifold
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback

set_option autoImplicit false

/-!
# Product projections and smooth auxiliary graphs

Genuine summed-dimension products retain submersion projections and the
regular dimension of the graph of a holomorphic map on a smooth carrier.
No Hilbert--Samuel comparison or resolution algorithm is asserted here.

Blueprint: `hironaka-auxiliary-graph-geometry.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaAuxiliaryGraphGeometry

noncomputable section

open Hironaka.BlowupSequences ProductComplexManifold
  ConstantRankSubmanifold

open scoped ProductComplexManifold

variable {n m : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- The genuine first product projection has the second model as complement. -/
theorem isSubmersionOfComplement_fst :
    Manifold.IsSubmersionOfComplement (ComplexModel m)
      𝓘(ℂ, ComplexModel (n+m)) 𝓘(ℂ, ComplexModel n) ∞ (Prod.fst : X × Y → X) := by
  intro p
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
    (prodModelEquiv n m).symm (chartAt (ComplexModel (n+m)) p)
    (chartAt (ComplexModel n) p.1) (mem_chart_source _ p) (mem_chart_source _ p.1)
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
  · intro z hz
    have hz' : z ∈ (chartAt (ComplexModel n) p.1).source ×ˢ
        (chartAt (ComplexModel m) p.2).source := by
      simpa only [chartAt_prod, prodChart_source] using hz
    exact hz'.1
  · intro z hz
    have hz' : (prodModelEquiv n m).symm z ∈
        (chartAt (ComplexModel n) p.1).target ×ˢ (chartAt (ComplexModel m) p.2).target := by
      simpa [OpenPartialHomeomorph.extend, chartAt_prod, prodChart_target] using hz
    change (chartAt (ComplexModel n) p.1)
      ((chartAt (ComplexModel n) p.1).symm ((prodModelEquiv n m).symm z).1) = _
    exact (chartAt (ComplexModel n) p.1).right_inv hz'.1

/-- The genuine second product projection has the first model as complement. -/
theorem isSubmersionOfComplement_snd :
    Manifold.IsSubmersionOfComplement (ComplexModel n)
      𝓘(ℂ, ComplexModel (n+m)) 𝓘(ℂ, ComplexModel m) ∞ (Prod.snd : X × Y → Y) := by
  intro p
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
    ((prodModelEquiv n m).symm.trans (ContinuousLinearEquiv.prodComm ℂ _ _))
    (chartAt (ComplexModel (n+m)) p) (chartAt (ComplexModel m) p.2)
    (mem_chart_source _ p) (mem_chart_source _ p.2)
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
  · intro z hz
    have hz' : z ∈ (chartAt (ComplexModel n) p.1).source ×ˢ
        (chartAt (ComplexModel m) p.2).source := by
      simpa only [chartAt_prod, prodChart_source] using hz
    exact hz'.2
  · intro z hz
    have hz' : (prodModelEquiv n m).symm z ∈
        (chartAt (ComplexModel n) p.1).target ×ˢ (chartAt (ComplexModel m) p.2).target := by
      simpa [OpenPartialHomeomorph.extend, chartAt_prod, prodChart_target] using hz
    change (chartAt (ComplexModel m) p.2)
      ((chartAt (ComplexModel m) p.2).symm ((prodModelEquiv n m).symm z).2) = _
    exact (chartAt (ComplexModel m) p.2).right_inv hz'.2

/-- Both genuine product projections are holomorphic submersions. -/
theorem isSubmersion_fst :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+m)) 𝓘(ℂ, ComplexModel n) ∞
      (Prod.fst : X × Y → X) := isSubmersionOfComplement_fst.isSubmersion

/-- The second genuine product projection is a holomorphic submersion. -/
theorem isSubmersion_snd :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+m)) 𝓘(ℂ, ComplexModel m) ∞
      (Prod.snd : X × Y → Y) := isSubmersionOfComplement_snd.isSubmersion

private theorem flattening_fderiv_injective {r : ℕ} {p : ComplexModel r}
    (Φ : LocalHolomorphicEquivAt p) : Function.Injective (fderiv ℂ Φ.toFun p) := by
  have hd := Φ.toFun_holomorphic.differentiableAt
    (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hi := Φ.invFun_holomorphic.differentiableAt
    (Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun Φ.center_mem_source))
  have he : Φ.invFun ∘ Φ.toFun =ᶠ[𝓝 p] id :=
    eventually_of_mem (Φ.isOpen_source.mem_nhds Φ.center_mem_source) Φ.left_inv
  have hc := fderiv_comp p hi hd
  rw [he.fderiv_eq, fderiv_id] at hc
  intro a b hab
  have hh := congrArg (fderiv ℂ Φ.invFun (Φ.toFun p)) hab
  simpa only [← ContinuousLinearMap.comp_apply, ← hc, ContinuousLinearMap.id_apply] using hh

private theorem exists_graph_coordinates {q : ℕ} (hq : q ≤ m)
    {p : ComplexModel m} (Φ : LocalHolomorphicEquivAt p) (hΦ0 : Φ.toFun p = 0)
    (F : ComplexModel m → ComplexModel n) (hF : DifferentiableOn ℂ F Φ.source)
    (O : Set (ComplexModel n)) (hO : IsOpen O) (hpO : F p ∈ O) :
    ∃ Ψ : LocalHolomorphicEquivAt (prodModelEquiv n m (F p,p)),
      Ψ.source ⊆ (prodModelEquiv n m).symm ⁻¹' (O ×ˢ Φ.source) ∧
      Ψ.toFun (prodModelEquiv n m (F p,p)) = 0 ∧
      ∀ z ∈ Ψ.source, Ψ.toFun z ∈ complexCoordinatePlane (n+m) q ↔
        Φ.toFun ((prodModelEquiv n m).symm z).2 ∈ complexCoordinatePlane m q ∧
          ((prodModelEquiv n m).symm z).1 = F ((prodModelEquiv n m).symm z).2 := by
  let J : ComplexModel q →ₗ[ℂ] (ComplexModel m × ComplexModel n) :=
    (RegularLocusDense.coordinateInclusion m q).toLinearMap.prod 0
  have hJ : Function.Injective J := by
    intro a b he
    have hh := congrArg (fun z => RegularLocusDense.coordinateProjection m q z.1) he
    change RegularLocusDense.coordinateProjection m q
      (RegularLocusDense.coordinateInclusion m q a) =
      RegularLocusDense.coordinateProjection m q
        (RegularLocusDense.coordinateInclusion m q b) at hh
    simpa only [RegularLocusDense.coordinateProjection_coordinateInclusion hq] using hh
  let W := LinearMap.range J
  have hWdim : Module.finrank ℂ W = q := by
    rw [LinearMap.finrank_range_of_inj hJ, finrank_euclideanSpace_fin]
  have hdim : Module.finrank ℂ (ComplexModel m × ComplexModel n) = n+m := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin, Nat.add_comm]
  obtain ⟨A,hA⟩ := exists_linearEquiv_mem_plane_iff hdim W hWdim
  have hmem (v : ComplexModel m × ComplexModel n) : v ∈ W ↔
      v.1 ∈ complexCoordinatePlane m q ∧ v.2 = 0 := by
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨RegularLocusDense.coordinateInclusion_mem_complexCoordinatePlane w,rfl⟩
    · rintro ⟨hv,hz⟩
      refine ⟨RegularLocusDense.coordinateProjection m q v.1,?_⟩
      exact Prod.ext (RegularLocusDense.coordinateInclusion_coordinateProjection hv) hz.symm
  let P := (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel m)).comp
    (prodModelEquiv n m).symm.toContinuousLinearMap
  let Q := (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel m)).comp
    (prodModelEquiv n m).symm.toContinuousLinearMap
  let N := (prodModelEquiv n m).symm ⁻¹' (O ×ˢ Φ.source)
  let z0 := prodModelEquiv n m (F p,p)
  have hN : IsOpen N := (hO.prod Φ.isOpen_source).preimage (prodModelEquiv n m).symm.continuous
  have hzN : z0 ∈ N := by
    simpa [N,z0] using And.intro hpO Φ.center_mem_source
  let Θ : ComplexModel (n+m) → ComplexModel (n+m) :=
    fun z => A (Φ.toFun (Q z),P z-F (Q z))
  have hQN : MapsTo Q N Φ.source := fun _ hz => hz.2
  have hΘd : DifferentiableOn ℂ Θ N :=
    A.differentiable.comp_differentiableOn
      ((Φ.toFun_holomorphic.comp Q.differentiableOn hQN).prodMk
        (P.differentiableOn.sub (hF.comp Q.differentiableOn hQN)))
  have hQ0 : Q z0 = p := congrArg Prod.snd ((prodModelEquiv n m).symm_apply_apply (F p,p))
  have hP0 : P z0 = F p := congrArg Prod.fst ((prodModelEquiv n m).symm_apply_apply (F p,p))
  have hΦd := Φ.toFun_holomorphic.differentiableAt
    (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hFd := hF.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hΦQ : HasFDerivAt (fun z => Φ.toFun (Q z))
      ((fderiv ℂ Φ.toFun p).comp Q) z0 := by
    have hh : HasFDerivAt Φ.toFun (fderiv ℂ Φ.toFun p) (Q z0) := by
      rw [hQ0]
      exact hΦd.hasFDerivAt
    exact hh.comp z0 Q.hasFDerivAt
  have hFQ : HasFDerivAt (fun z => F (Q z)) ((fderiv ℂ F p).comp Q) z0 := by
    have hh : HasFDerivAt F (fderiv ℂ F p) (Q z0) := by
      rw [hQ0]
      exact hFd.hasFDerivAt
    exact hh.comp z0 Q.hasFDerivAt
  have hΘD := A.hasFDerivAt.comp z0 (hΦQ.prodMk (P.hasFDerivAt.sub hFQ))
  change HasFDerivAt Θ _ z0 at hΘD
  have hinj : Function.Injective (fderiv ℂ Θ z0) := by
    rw [hΘD.fderiv]
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hzero : ((fderiv ℂ Φ.toFun p) (Q z),P z-(fderiv ℂ F p) (Q z))=0 :=
      A.injective (by simpa using hz)
    have hqz : Q z=0 := flattening_fderiv_injective Φ
      (by simpa using congrArg Prod.fst hzero)
    have hpz : P z=0 := by simpa [hqz] using congrArg Prod.snd hzero
    apply (prodModelEquiv n m).symm.injective
    simpa only [map_zero] using Prod.ext hpz hqz
  obtain ⟨Ψ,hΨN,hΨΘ,_⟩ := exists_localHolomorphicEquivAt hN hzN hΘd hinj
  refine ⟨Ψ,hΨN,?_,?_⟩
  · rw [hΨΘ]
    change A (Φ.toFun (Q z0),P z0-F (Q z0))=0
    rw [hQ0,hP0,hΦ0,sub_self]
    exact A.map_zero
  · intro z _hz
    rw [hΨΘ,hA,hmem]
    change (_ ∧ P z-F (Q z)=0) ↔ (_ ∧ P z=F (Q z))
    rw [sub_eq_zero]
    rfl

/-- The actual graph subset retains the original map and original carrier. -/
def graphOn (f : Y → X) (S : Set Y) : Set (X × Y) :=
  {p | p.2 ∈ S ∧ p.1 = f p.2}

/-- A graph retains the genuine regular dimension of its original carrier. -/
theorem regularAtDim_graph {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {S : Set Y} {y : Y} {q : ℕ} (hy : RegularAtDim (n := m) S y q) :
    RegularAtDim (n := n+m) (graphOn f S) (f y,y) q := by
  obtain ⟨hq,hyS,Φ,hΦt,hΦ0,hΦS⟩ := hy
  let a := chartAt (ComplexModel n) (f y)
  let b := chartAt (ComplexModel m) y
  let F : ComplexModel m → ComplexModel n := fun v => a (f (b.symm v))
  let W := b.target ∩ b.symm ⁻¹' (f ⁻¹' a.source)
  have hW : IsOpen W := b.isOpen_inter_preimage_symm
    (hf.continuous.isOpen_preimage _ a.open_source)
  have hyW : b y ∈ W := by
    refine ⟨b.map_source (mem_chart_source _ y),?_⟩
    change f (b.symm (b y)) ∈ a.source
    rw [b.left_inv (mem_chart_source _ y)]
    exact mem_chart_source _ (f y)
  let Φ' := Φ.restrict W hW (b y) ⟨Φ.center_mem_source,hyW⟩
  have hFW : DifferentiableOn ℂ F W := by
    have h := (contMDiffOn_iff.mp (hf.contMDiffOn (s := univ))).2 y (f y)
    refine (h.differentiableOn (by simp)).mono ?_
    intro v hv
    exact ⟨⟨mem_univ _,hv.1⟩,mem_univ _,hv.2,mem_univ _⟩
  have hF : DifferentiableOn ℂ F Φ'.source := hFW.mono inter_subset_right
  have hF0 : F (b y)=a (f y) := by
    change a (f (b.symm (b y)))=a (f y)
    rw [b.left_inv (mem_chart_source _ y)]
  have hO : F (b y) ∈ a.target := by
    rw [hF0]
    exact a.map_source (mem_chart_source _ (f y))
  have hh := exists_graph_coordinates hq Φ' hΦ0 F hF a.target a.open_target hO
  rw [hF0] at hh
  obtain ⟨Ψ,hΨN,hΨ0,hΨflat⟩ := hh
  refine ⟨hq.trans (Nat.le_add_left m n),⟨hyS,rfl⟩,Ψ,?_,hΨ0,?_⟩
  · intro z hz
    have hh := hΨN hz
    change z ∈ (prodChart a b).target
    rw [prodChart_target]
    exact ⟨hh.1,hΦt hh.2.1⟩
  · rintro ⟨x,z⟩ hxz hcoord
    change (x,z) ∈ (prodChart a b).source at hxz
    rw [prodChart_source] at hxz
    have hx : x ∈ a.source := by
      exact hxz.1
    have hz : z ∈ b.source := by
      exact hxz.2
    have hxy : (complexChartAt (n := n+m) (f y,y)).val (x,z)=
        prodModelEquiv n m (a x,b z) := rfl
    rw [hΨflat _ hcoord]
    have hparts : (prodModelEquiv n m).symm
        ((complexChartAt (n := n+m) (f y,y)).val (x,z))=(a x,b z) := by
      rw [hxy,ContinuousLinearEquiv.symm_apply_apply]
    rw [hparts]
    have hzΦ : b z ∈ Φ.source := by
      have hp := (hΨN hcoord).2.1
      rwa [hparts] at hp
    have hzf : f z ∈ a.source := by
      have hp := (hΨN hcoord).2.2.2
      rw [hparts] at hp
      change f (b.symm (b z)) ∈ a.source at hp
      rwa [b.left_inv hz] at hp
    have hFz : F (b z)=a (f z) := by
      change a (f (b.symm (b z)))=a (f z)
      rw [b.left_inv hz]
    change (z ∈ S ∧ x=f z) ↔
      (Φ.toFun (b z) ∈ complexCoordinatePlane m q ∧ a x=F (b z))
    have hzS : z ∈ S ↔ Φ.toFun (b z) ∈ complexCoordinatePlane m q := hΦS hz hzΦ
    rw [hFz,← hzS]
    exact and_congr_right fun _ => ⟨fun he => congrArg a he,fun he => a.injOn hx hzf he⟩

omit [IsComplexManifold m Y] in
/-- The graph is closed whenever its original carrier is closed. -/
theorem isClosed_graphOn {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {S : Set Y} (hS : IsClosed S) : IsClosed (graphOn f S) :=
  (hS.preimage continuous_snd).inter
    (isClosed_eq continuous_fst (hf.continuous.comp continuous_snd))

/-- A genuine closed smooth carrier has a genuine closed smooth graph. -/
theorem isClosedSubmanifold_graph {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {S : Set Y} (hS : IsClosedSubmanifold m S) :
    IsClosedSubmanifold (n+m) (graphOn f S) := by
  refine ⟨isClosed_graphOn hf hS.1,?_⟩
  rintro ⟨x,y⟩ ⟨hy,hxy⟩
  obtain ⟨q,hq⟩ := hS.2 y hy
  change x=f y at hxy
  subst x
  exact ⟨q,regularAtDim_graph hf hq⟩

end

end Hironaka.HironakaAuxiliaryGraphGeometry
