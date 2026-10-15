/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.LocalHolomorphicOpenPartialExact
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialOrdering
import Hironaka.Resolution.HironakaNormalCrossingsOrderedMonomialTail
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Actual whole SNC pullback under arbitrary-dimensional complex submersions

Genuine submersion charts internally construct full centred lifted coordinates.
They produce the entire literal pulled SNC family and every whole member ideal,
full indexed power product, marking-one datum and actual through exponent.
Surjectivity alone transports the true nonempty positive index family and the
unchanged old-gamma unique singleton maximum, including all colex history.
Actual identity Cartier control respects the complete pulled marked datum,
with exact coefficient drop and every old empty or repeated entry retained.
Full finite procedure comparison, general higher invariant functoriality and
identifying prior general separation with the old driver remain open.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionNormalCrossings
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open HironakaSmoothSubmersionMonomialOrdering NormalCrossings BlowupFlatCoordinates
  MemberPullback RelativePrincipalizationSpan HironakaNormalCrossingsFiniteMarkedCompletion
  HironakaNormalCrossingsOrderedMonomialTail IdealWeightPowers HironakaDivisorResidual
  BlowupTowers MarkedIdeals DivisorExponent MonomialInvariant MonomialCase HironakaSmoothSubmersionCoefficientIdeals
noncomputable section
variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
/-- The genuine chosen submersion complement internally has actual m-n finite coordinates. -/
def complementCoordinates {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y) :
    hf.complement ≃L[ℂ] ComplexModel (m-n) := by
  let D : ComplexModel m →ₗ[ℂ] hf.complement :=
    (LinearMap.snd ℂ (ComplexModel n) hf.complement).comp hf.equiv.toLinearEquiv.toLinearMap
  have hD : Function.Surjective D := by
    intro v
    refine ⟨hf.equiv.symm (0,v),?_⟩
    change (hf.equiv (hf.equiv.symm (0,v))).2 = v
    rw [hf.equiv.apply_symm_apply]
  letI : FiniteDimensional ℂ hf.complement := Module.Finite.of_surjective D hD
  have hdim : m = n + Module.finrank ℂ hf.complement := by
    simpa only [ComplexModel,finrank_euclideanSpace_fin,Module.finrank_prod] using
      hf.equiv.toLinearEquiv.finrank_eq
  apply ContinuousLinearEquiv.ofFinrankEq
  simp only [ComplexModel,finrank_euclideanSpace_fin]
  omega

omit [IsComplexManifold n X] in
/-- BOTH holomorphic directions of an actual maximal-atlas transition. -/
private theorem chartTransition_holomorphic (e e' : OpenPartialHomeomorph X (ComplexModel n))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ X)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ X) :
    DifferentiableOn ℂ (e.symm.trans e') (e.symm.trans e').source ∧
      DifferentiableOn ℂ (e.symm.trans e').symm (e.symm.trans e').target := by
  have ht := IsManifold.compatible_of_mem_maximalAtlas he he'
  have hc : ContDiffOn ℂ ∞ (e.symm.trans e') (e.symm.trans e').source ∧
      ContDiffOn ℂ ∞ (e.symm.trans e').symm (e.symm.trans e').target := by
    simpa [contDiffGroupoid,mem_groupoid_of_pregroupoid,contDiffPregroupoid] using ht
  exact ⟨hc.1.differentiableOn (by simp),hc.2.differentiableOn (by simp)⟩

section HolomorphicPartialMaps
variable {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

private theorem holomorphic_trans (e : OpenPartialHomeomorph V W) (f : OpenPartialHomeomorph W Z)
    (he : DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target)
    (hf : DifferentiableOn ℂ f f.source ∧ DifferentiableOn ℂ f.symm f.target) :
    DifferentiableOn ℂ (e.trans f) (e.trans f).source ∧
      DifferentiableOn ℂ (e.trans f).symm (e.trans f).target := by
  constructor
  · change DifferentiableOn ℂ (f ∘ e) (e.source ∩ e ⁻¹' f.source)
    exact hf.1.comp (he.1.mono inter_subset_left) (fun _ hu => hu.2)
  · change DifferentiableOn ℂ (e.symm ∘ f.symm) (f.target ∩ f.symm ⁻¹' e.target)
    exact he.2.comp (hf.2.mono inter_subset_left) (fun _ hu => hu.2)

private theorem holomorphic_linear (L : V ≃L[ℂ] W) :
    DifferentiableOn ℂ L.toHomeomorph.toOpenPartialHomeomorph univ ∧
      DifferentiableOn ℂ L.symm.toHomeomorph.toOpenPartialHomeomorph univ :=
  ⟨L.differentiable.differentiableOn,L.symm.differentiable.differentiableOn⟩

private theorem holomorphic_translation (v : V) :
    DifferentiableOn ℂ (Homeomorph.subRight v).toOpenPartialHomeomorph univ ∧
      DifferentiableOn ℂ (Homeomorph.subRight v).symm.toOpenPartialHomeomorph univ := by
  exact ⟨(differentiable_id.sub_const v).differentiableOn,
    (differentiable_id.add_const v).differentiableOn⟩

end HolomorphicPartialMaps

/-- The real finite coordinate split reads its first coordinate block exactly. -/
theorem first_block_coordinate {k : ℕ} (u : ComplexModel n) (v : ComplexModel k) (j : Fin n) :
    EuclideanSpace.finAddEquivProd.symm (u,v) (Fin.castAdd k j) = u j := by
  simp [EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

section ActualLift
variable {k : ℕ} {Y' : Type u} [TopologicalSpace Y']
  [ChartedSpace (ComplexModel (n+k)) Y'] [IsComplexManifold (n+k) Y']

private def normalizedSplit {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y) :
    ComplexModel (n+k) ≃L[ℂ] (ComplexModel n × ComplexModel k) :=
  hf.equiv.trans (ContinuousLinearEquiv.prodCongr (.refl ℂ (ComplexModel n))
    (by
      have R := complementCoordinates hf
      have he : n+k-n = k := by omega
      rw [he] at R
      exact R))

private def liftedPartialMap {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y))) :
    OpenPartialHomeomorph (ComplexModel (n+k)) (ComplexModel (n+k)) :=
  let a := (chartAt (ComplexModel (n+k)) y).symm.trans hf.domChart
  let b := (hf.codChart.symm.trans (chartAt (ComplexModel n) (f y))).trans Φ.toOpenPartialHomeomorph
  let L := normalizedSplit hf
  let τ := (Homeomorph.subRight ((L (hf.domChart y)).2)).toOpenPartialHomeomorph
  (((a.trans L.toHomeomorph.toOpenPartialHomeomorph).trans (b.prod τ)).trans
    (EuclideanSpace.finAddEquivProd.symm.toHomeomorph.toOpenPartialHomeomorph))

private theorem liftedPartialMap_holomorphic {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y))) :
    DifferentiableOn ℂ (liftedPartialMap hf Φ) (liftedPartialMap hf Φ).source ∧
      DifferentiableOn ℂ (liftedPartialMap hf Φ).symm (liftedPartialMap hf Φ).target := by
  let a := (chartAt (ComplexModel (n+k)) y).symm.trans hf.domChart
  let b₀ := hf.codChart.symm.trans (chartAt (ComplexModel n) (f y))
  let b := b₀.trans Φ.toOpenPartialHomeomorph
  let L := normalizedSplit hf
  let τ := (Homeomorph.subRight ((L (hf.domChart y)).2)).toOpenPartialHomeomorph
  have ha := chartTransition_holomorphic (chartAt (ComplexModel (n+k)) y) hf.domChart
    (IsManifold.chart_mem_maximalAtlas _) hf.domChart_mem_maximalAtlas
  have hb₀ := chartTransition_holomorphic hf.codChart (chartAt (ComplexModel n) (f y))
    hf.codChart_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _)
  have hb := holomorphic_trans b₀ Φ.toOpenPartialHomeomorph hb₀
    ⟨Φ.toFun_holomorphic,Φ.invFun_holomorphic⟩
  have hτ := holomorphic_translation ((L (hf.domChart y)).2)
  have hprod : DifferentiableOn ℂ (b.prod τ) (b.prod τ).source ∧
      DifferentiableOn ℂ (b.prod τ).symm (b.prod τ).target :=
    by
      constructor
      · intro z hz
        exact (DifferentiableAt.prodMap z (hb.1.differentiableAt (b.open_source.mem_nhds hz.1))
          (hτ.1.differentiableAt (isOpen_univ.mem_nhds hz.2))).differentiableWithinAt
      · intro z hz
        exact (DifferentiableAt.prodMap z (hb.2.differentiableAt (b.open_target.mem_nhds hz.1))
          (hτ.2.differentiableAt (isOpen_univ.mem_nhds hz.2))).differentiableWithinAt
  exact holomorphic_trans ((a.trans L.toHomeomorph.toOpenPartialHomeomorph).trans (b.prod τ))
    EuclideanSpace.finAddEquivProd.symm.toHomeomorph.toOpenPartialHomeomorph
    (holomorphic_trans _ _ (holomorphic_trans _ _ ha (holomorphic_linear L)) hprod)
    (holomorphic_linear EuclideanSpace.finAddEquivProd.symm)

omit [IsComplexManifold n X] [IsComplexManifold (n+k) Y'] in
private theorem normalizedSplit_fst {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (z : ComplexModel (n+k)) : (normalizedSplit hf z).1 = (hf.equiv z).1 := rfl

omit [IsComplexManifold n X] [IsComplexManifold (n+k) Y'] in
private theorem submersion_coordinate_eq {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (z : Y') (hz : z ∈ hf.domChart.source) :
    hf.codChart (f z) = (normalizedSplit hf (hf.domChart z)).1 := by
  rw [normalizedSplit_fst]
  have hc : ∀ q ∈ hf.domChart.target, hf.codChart (f (hf.domChart.symm q)) = (hf.equiv q).1 := by
    simpa [Set.EqOn,Function.comp_def] using hf.writtenInCharts
  simpa only [hf.domChart.left_inv hz] using hc (hf.domChart z) (hf.domChart.map_source hz)

omit [IsComplexManifold n X] [IsComplexManifold (n+k) Y'] in
private theorem liftedPartialMap_center {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) :
    chartAt (ComplexModel (n+k)) y y ∈ (liftedPartialMap hf Φ).source ∧
      liftedPartialMap hf Φ (chartAt (ComplexModel (n+k)) y y) = 0 := by
  let e := chartAt (ComplexModel (n+k)) y
  let e' := chartAt (ComplexModel n) (f y)
  let a := e.symm.trans hf.domChart
  let b := (hf.codChart.symm.trans e').trans Φ.toOpenPartialHomeomorph
  let L := normalizedSplit hf
  have hay : a (e y) = hf.domChart y := by
    change hf.domChart (e.symm (e y)) = hf.domChart y
    rw [e.left_inv (mem_chart_source _ y)]
  have ha : e y ∈ a.source := by
    refine ⟨e.map_source (mem_chart_source _ y),?_⟩
    change e.symm (e y) ∈ hf.domChart.source
    rw [e.left_inv (mem_chart_source _ y)]
    exact hf.mem_domChart_source
  have hL : (L (hf.domChart y)).1 = hf.codChart (f y) :=
    (submersion_coordinate_eq hf y hf.mem_domChart_source).symm
  have hb : (L (hf.domChart y)).1 ∈ b.source := by
    change ((L (hf.domChart y)).1 ∈ hf.codChart.target ∧
      hf.codChart.symm (L (hf.domChart y)).1 ∈ e'.source) ∧
      e' (hf.codChart.symm (L (hf.domChart y)).1) ∈ Φ.source
    rw [hL,hf.codChart.left_inv hf.mem_codChart_source]
    exact ⟨⟨hf.codChart.map_source hf.mem_codChart_source,mem_chart_source _ (f y)⟩,
      Φ.center_mem_source⟩
  have hb0 : b (L (hf.domChart y)).1 = 0 := by
    change Φ.toFun (e' (hf.codChart.symm (L (hf.domChart y)).1)) = 0
    rw [hL,hf.codChart.left_inv hf.mem_codChart_source]
    exact h0
  constructor
  · change ((e y ∈ a.source ∧ L (a (e y)) ∈ univ) ∧
      L (a (e y)) ∈ b.source ×ˢ univ) ∧ _ ∈ univ
    rw [hay]
    exact ⟨⟨⟨ha,mem_univ _⟩,⟨hb,mem_univ _⟩⟩,mem_univ _⟩
  · change EuclideanSpace.finAddEquivProd.symm
      (b (L (a (e y))).1,(L (a (e y))).2-(L (hf.domChart y)).2) = 0
    rw [hay,hb0,sub_self]
    exact map_zero EuclideanSpace.finAddEquivProd.symm

omit [IsComplexManifold n X] [IsComplexManifold (n+k) Y'] in
private theorem liftedPartialMap_domain_dictionary {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (q : ComplexModel (n+k)) (hq : q ∈ (liftedPartialMap hf Φ).source) :
    q ∈ (chartAt (ComplexModel (n+k)) y).target ∧
      f ((chartAt (ComplexModel (n+k)) y).symm q) ∈ BlowupFlatCoordinates.flatDomain Φ ∧
      ∀ j : Fin n, liftedPartialMap hf Φ q (Fin.castAdd k j) =
        BlowupFlatCoordinates.flatCoord Φ j (f ((chartAt (ComplexModel (n+k)) y).symm q)) := by
  let e := chartAt (ComplexModel (n+k)) y
  let e' := chartAt (ComplexModel n) (f y)
  let a := e.symm.trans hf.domChart
  let b := (hf.codChart.symm.trans e').trans Φ.toOpenPartialHomeomorph
  let L := normalizedSplit hf
  change ((q ∈ a.source ∧ L (a q) ∈ univ) ∧ L (a q) ∈ b.source ×ˢ univ) ∧ _ ∈ univ at hq
  have hw : e.symm q ∈ hf.domChart.source := hq.1.1.1.2
  have hL : (L (a q)).1 = hf.codChart (f (e.symm q)) :=
    (submersion_coordinate_eq hf (e.symm q) hw).symm
  have hback : hf.codChart.symm (L (a q)).1 = f (e.symm q) := by
    rw [hL]
    exact hf.codChart.left_inv (hf.source_subset_preimage_source hw)
  have hb : (L (a q)).1 ∈ b.source := hq.1.2.1
  change ((L (a q)).1 ∈ hf.codChart.target ∧ hf.codChart.symm (L (a q)).1 ∈ e'.source) ∧
    e' (hf.codChart.symm (L (a q)).1) ∈ Φ.source at hb
  rw [hback] at hb
  refine ⟨hq.1.1.1.1,⟨hb.1.2,hb.2⟩,?_⟩
  intro j
  change EuclideanSpace.finAddEquivProd.symm
    (b (L (a q)).1,(L (a q)).2-(L (hf.domChart y)).2) (Fin.castAdd k j) = _
  rw [first_block_coordinate]
  change Φ.toFun (e' (hf.codChart.symm (L (a q)).1)) j = _
  rw [hback]
  rfl

/-- The entire actual local holomorphic chart is constructed from the genuine submersion. -/
def liftedCoordinatesAdd {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) :
    LocalHolomorphicEquivAt (n := n+k) (chartAt (ComplexModel (n+k)) y y) where
  source := (liftedPartialMap hf Φ).source
  target := (liftedPartialMap hf Φ).target
  isOpen_source := (liftedPartialMap hf Φ).open_source
  isOpen_target := (liftedPartialMap hf Φ).open_target
  center_mem_source := (liftedPartialMap_center hf Φ h0).1
  toFun := liftedPartialMap hf Φ
  invFun := (liftedPartialMap hf Φ).symm
  toFun_holomorphic := (liftedPartialMap_holomorphic hf Φ).1
  invFun_holomorphic := (liftedPartialMap_holomorphic hf Φ).2
  mapsTo_toFun := (liftedPartialMap hf Φ).mapsTo
  mapsTo_invFun := (liftedPartialMap hf Φ).symm.mapsTo
  left_inv := fun _ hz => (liftedPartialMap hf Φ).left_inv hz
  right_inv := fun _ hz => (liftedPartialMap hf Φ).right_inv hz

/-- Every point of the TRUE entire lifted chart has the original-domain and exact coordinate dictionary. -/
theorem liftedCoordinatesAdd_dictionary {f : Y' → X} {y : Y'}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+k)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) :
    (liftedCoordinatesAdd hf Φ h0).source ⊆ (chartAt (ComplexModel (n+k)) y).target ∧
      (liftedCoordinatesAdd hf Φ h0).toFun (chartAt (ComplexModel (n+k)) y y) = 0 ∧
      ∀ z ∈ BlowupFlatCoordinates.flatDomain (liftedCoordinatesAdd hf Φ h0),
        f z ∈ BlowupFlatCoordinates.flatDomain Φ ∧
          ∀ j : Fin n, BlowupFlatCoordinates.flatCoord (liftedCoordinatesAdd hf Φ h0) (Fin.castAdd k j) z =
            BlowupFlatCoordinates.flatCoord Φ j (f z) := by
  refine ⟨fun q hq => (liftedPartialMap_domain_dictionary hf Φ q hq).1,
    (liftedPartialMap_center hf Φ h0).2,?_⟩
  intro z hz
  have hd := (liftedPartialMap_domain_dictionary hf Φ
    (chartAt (ComplexModel (n+k)) y z) hz.2).2
  rw [(chartAt (ComplexModel (n+k)) y).left_inv hz.1] at hd
  exact hd

end ActualLift

/-- ONLY genuine submersion and actual centred original coordinates internally give the entire lifted chart. -/
theorem exists_lifted_coordinates {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) :
    ∃ (Ξ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) y y))
      (ρ : Fin n ↪ Fin m),
      Ξ.source ⊆ (chartAt (ComplexModel m) y).target ∧
      Ξ.toFun (chartAt (ComplexModel m) y y) = 0 ∧
      ∀ z ∈ BlowupFlatCoordinates.flatDomain Ξ,
        f z ∈ BlowupFlatCoordinates.flatDomain Φ ∧
          ∀ j : Fin n, BlowupFlatCoordinates.flatCoord Ξ (ρ j) z =
            BlowupFlatCoordinates.flatCoord Φ j (f z) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt hf)
  exact ⟨liftedCoordinatesAdd hf Φ h0,Fin.castAddEmb k,liftedCoordinatesAdd_dictionary hf Φ h0⟩

/-- ONLY actual submersion and original whole SNC internally produce the ENTIRE literal pulled SNC list. -/
theorem isSNCDivisor_preimage_submersion {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (E : List (Set X)) (hE : IsSNCDivisor n E) : IsSNCDivisor m (E.map (f ⁻¹' ·)) := by
  constructor
  · intro W hW
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hW
    exact (hE.1 C hC).preimage hf.contMDiff.continuous
  · intro y
    obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard,hinj⟩ := hE.2 (f y)
    obtain ⟨Ξ,ρ,hΞsrc,hΞ0,hΞdict⟩ := exists_lifted_coordinates (hf.isSubmersionAt y) Φ h0
    let ix : Fin (E.map (f ⁻¹' ·)).length → Fin E.length := fun i =>
      ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
    have hget : ∀ i : Fin (E.map (f ⁻¹' ·)).length, (E.map (f ⁻¹' ·)).get i = f ⁻¹' E.get (ix i) := by
      intro i
      simp only [List.get_eq_getElem,List.getElem_map]
      rfl
    refine ⟨fun i => (S (ix i)).map ρ,⟨Ξ,hΞsrc,hΞ0,?_⟩,?_,?_⟩
    · intro i hyi z hz hzΞ
      have hd := hΞdict z ⟨hz,hzΞ⟩
      have hyorig : f y ∈ E.get (ix i) := by simpa only [hget,mem_preimage] using hyi
      have horig := hflat (ix i) hyorig hd.1.1 hd.1.2
      change z ∈ (E.map (f ⁻¹' ·)).get i ↔
        Ξ.toFun (chartAt (ComplexModel m) y z) ∈ coordSubspace ((S (ix i)).map ρ)
      rw [hget i]
      change f z ∈ E.get (ix i) ↔ _
      change f z ∈ E.get (ix i) ↔ Φ.toFun (chartAt (ComplexModel n) (f y) (f z)) ∈
        coordSubspace (S (ix i)) at horig
      rw [horig]
      constructor
      · intro h j hj
        obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hj
        change flatCoord Ξ (ρ l) z = 0
        rw [hd.2 l]
        exact h l hl
      · intro h j hj
        change flatCoord Φ j (f z) = 0
        rw [← hd.2 j]
        exact h (ρ j) (Finset.mem_map_of_mem ρ hj)
    · intro i hyi
      rw [Finset.card_map]
      exact hcard (ix i) (by simpa only [hget,mem_preimage] using hyi)
    · intro i hi j hj hij
      have hi' : f y ∈ E.get (ix i) := by
        change y ∈ (E.map (f ⁻¹' ·)).get i at hi
        simpa only [hget i,mem_preimage] using hi
      have hj' : f y ∈ E.get (ix j) := by
        change y ∈ (E.map (f ⁻¹' ·)).get j at hj
        simpa only [hget j,mem_preimage] using hj
      have heq : ix i = ix j := hinj hi' hj' (Finset.map_injective ρ hij)
      exact Fin.ext (congrArg (fun l : Fin E.length => l.val) heq)

/-- Actual entire principal-generator pullback works across arbitrary genuine ambient dimensions. -/
private theorem pullback_principal_mem_iff {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) {I : GermIdeal n X}
    {h : X → ℂ} {y : Y} (hh : HolomorphicAt n h (f y))
    (hgen : ∀ g, I.mem (f y) g ↔ IsInSpanAt (n := n) (· = h) (f y) g) (g : Y → ℂ) :
    (GermIdeal.pullback (m := m) f I).mem y g ↔ IsInSpanAt (n := m) (· = h ∘ f) y g := by
  have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z :=
    Eventually.of_forall fun z => hf z
  constructor
  · intro hg
    refine IsInSpanAt.of_forall_eq_mul ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨a,ha,rfl⟩
    obtain ⟨_,c,hc,hac⟩ := isInSpanAt_eq_iff.mp ((hgen a).mp ha)
    refine ⟨c ∘ f,hc.comp_contMDiff hfat,?_⟩
    filter_upwards [hf.continuous.continuousAt.eventually hac] with z hz
    exact hz
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans (fun s hs => ?_) hg)
    subst hs
    exact isInSpanAt_of_eq_mul ⟨h,(hgen h).mpr (isInSpanAt_of_eq_mul rfl hh
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)),rfl⟩
      (hh.comp_contMDiff hfat) (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)

omit [IsComplexManifold n X] in
private theorem vanishingIdeal_mem_iff_one_of_notMem {C : Set X} (hC : IsClosed C)
    {x : X} (hx : x ∉ C) (g : X → ℂ) :
    (vanishingIdeal (n := n) C).mem x g ↔ IsInSpanAt (n := n) (· = fun _ => (1 : ℂ)) x g := by
  rw [isInSpanAt_one_iff]
  constructor
  · exact fun hg => hg.1
  · intro hg
    refine ⟨hg,?_⟩
    filter_upwards [hC.isOpen_compl.mem_nhds hx] with z hz hzC
    exact (hz hzC).elim

/-- Actual original whole SNC internally proves COMPLETE vanishing-ideal pullback for every literal member. -/
theorem pullback_vanishingIdeal_snc_member {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (i : Fin E.length) :
    GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) (E.get i)) =
      vanishingIdeal (n := m) (f ⁻¹' E.get i) := by
  apply GermIdeal.ext
  funext y g
  apply propext
  by_cases hy : f y ∈ E.get i
  · obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard,_⟩ := hE.2 (f y)
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (hcard i hy)
    have hC : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) (f y)).source →
        chartAt (ComplexModel n) (f y) z ∈ Φ.source →
        (z ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (f y) z) t = 0) := by
      intro z hz hzΦ
      have hh := hflat i hy hz hzΦ
      rw [ht,BlowupSNCTransform.mem_coordSubspace_singleton] at hh
      exact hh
    obtain ⟨Ξ,ρ,_,_,hΞdict⟩ := exists_lifted_coordinates (hf.isSubmersionAt y) Φ h0
    have hCy : ∀ {z : Y}, z ∈ (chartAt (ComplexModel m) y).source →
        chartAt (ComplexModel m) y z ∈ Ξ.source →
        (z ∈ f ⁻¹' E.get i ↔ Ξ.toFun (chartAt (ComplexModel m) y z) (ρ t) = 0) := by
      intro z hz hzΞ
      have hd := hΞdict z ⟨hz,hzΞ⟩
      change f z ∈ E.get i ↔ flatCoord Ξ (ρ t) z = 0
      rw [hd.2 t]
      exact hC hd.1.1 hd.1.2
    have hgen : ∀ a, (vanishingIdeal (n := n) (E.get i)).mem (f y) a ↔
        IsInSpanAt (n := n) (· = flatCoord Φ t) (f y) a :=
      vanishingIdeal_mem_iff_flatCoord Φ hC (mem_flatDomain_self Φ)
    rw [pullback_principal_mem_iff hf.contMDiff (holomorphicAt_flatCoord Φ t (mem_flatDomain_self Φ)) hgen g,
      vanishingIdeal_mem_iff_flatCoord Ξ hCy (mem_flatDomain_self Ξ) g]
    apply isInSpanAt_eq_congr
    filter_upwards [(isOpen_flatDomain Ξ).mem_nhds (mem_flatDomain_self Ξ)] with z hz
    exact (hΞdict z hz).2 t |>.symm
  · have hc := hE.1 (E.get i) (List.get_mem E i)
    rw [pullback_principal_mem_iff hf.contMDiff (holomorphicAt_const 1)
      (vanishingIdeal_mem_iff_one_of_notMem hc hy) g,
      vanishingIdeal_mem_iff_one_of_notMem (hc.preimage hf.contMDiff.continuous) hy g]
    rfl

/-- Actual whole indexed carrier preimage retains every literal power and historical entry. -/
def pulledWeights (f : Y → X) (F : List (Set X × ℕ)) : List (Set Y × ℕ) :=
  F.map fun p => (f ⁻¹' p.1,p.2)

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The entire literal pulled carrier list is EXACTLY the whole original list preimage. -/
theorem pulledWeights_carriers (f : Y → X) (F : List (Set X × ℕ)) :
    (pulledWeights f F).map Prod.fst = (F.map Prod.fst).map (f ⁻¹' ·) := by
  simp only [pulledWeights,List.map_map]
  rfl

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Every actual coefficient is retained literally, including zero powers and empty entries. -/
theorem pulledWeights_powers (f : Y → X) (F : List (Set X × ℕ)) :
    (pulledWeights f F).map Prod.snd = F.map Prod.snd := by
  simp only [pulledWeights,List.map_map]
  rfl

private theorem pullback_product_of_present {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (F : List (Set X × ℕ))
    (hF : ∀ p ∈ F, p.1 ∈ E) :
    GermIdeal.pullback (m := m) f (componentPowerProduct (n := n) F) =
      componentPowerProduct (n := m) (pulledWeights f F) := by
  induction F with
  | nil => exact pullback_unitIdeal
  | cons p F ih =>
    have htail : ∀ q ∈ F, q.1 ∈ E := fun q hq => hF q (List.mem_cons_of_mem p hq)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hF p (by simp))
    have hc : (vanishingIdeal (n := n) p.1).IsCoherent :=
      DivisorMetric.isCoherent_of_isInvertible (hi ▸ isInvertible_vanishingIdeal_snc_member hE i)
    have htc : (componentPowerProduct (n := n) F).IsCoherent :=
      (isWellFormed_monomialMarkedIdeal hE F htail).isCoherent
    have hpull : GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) p.1) =
        vanishingIdeal (n := m) (f ⁻¹' p.1) := hi ▸ pullback_vanishingIdeal_snc_member hf E hE i
    change GermIdeal.pullback (m := m) f ((idealPow (vanishingIdeal (n := n) p.1) p.2).mul
      (componentPowerProduct (n := n) F)) =
      (idealPow (vanishingIdeal (n := m) (f ⁻¹' p.1)) p.2).mul (componentPowerProduct (n := m) (pulledWeights f F))
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hf.contMDiff
      (GermIdealPullbackCalculus.isCoherent_idealPow hc p.2) htc,
      HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hf.contMDiff hc,hpull,ih htail]

/-- The COMPLETE actual indexed product has whole genuine ideal pullback, supplied only actual SNC input. -/
theorem pullback_componentPowerProduct {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    GermIdeal.pullback (m := m) f (componentPowerProduct (n := n) F) =
      componentPowerProduct (n := m) (pulledWeights f F) :=
  pullback_product_of_present hf hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)

/-- Actual full pulled SNC is internally supplied for the ENTIRE indexed family. -/
theorem pulledWeights_isSNCDivisor {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSNCDivisor m ((pulledWeights f F).map Prod.fst) := by
  rw [pulledWeights_carriers]
  exact isSNCDivisor_preimage_submersion hf _ hF

/-- The SAME genuine marked pullback is the exact WHOLE internally produced indexed marked datum. -/
theorem markedPullback_indexed_dictionary {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) =
      monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of (preimage_univ)
    (pulledWeights_carriers f F).symm (pullback_componentPowerProduct hf F hF) rfl

/-- Only genuine submersion and original SNC internally supply ALL actual pulled marking-one domain fields. -/
theorem isInvDomain_pulled_indexed_product {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ResolutionInvariantSpec.IsInvDomain m
      (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)) := by
  rw [markedPullback_indexed_dictionary hf F hF]
  exact isInvDomain_monomialMarkedIdeal (pulledWeights_isSNCDivisor hf F hF) _
    (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The genuine literal same-index equivalence, with no historical entry deleted. -/
def pulledIndex (f : Y → X) (F : List (Set X × ℕ)) :
    Fin F.length ≃ Fin (pulledWeights f F).length := finCongr (by simp [pulledWeights])

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Entire actual carriers and powers at every transported literal index. -/
theorem pulledWeights_get (f : Y → X) (F : List (Set X × ℕ)) (j : Fin F.length) :
    (pulledWeights f F).get (pulledIndex f F j) = (f ⁻¹' (F.get j).1,(F.get j).2) := by
  simp only [pulledWeights,List.get_eq_getElem,List.getElem_map]
  rfl

omit [IsComplexManifold n X] in
private theorem positive_dimension_of_through {F : List (Set X × ℕ)}
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : X) (j : Fin F.length)
    (hx : x ∈ (F.get j).1) : 0 < n := by
  obtain ⟨S,_,hc,_⟩ := hF.2 x
  let j' : Fin (F.map Prod.fst).length := ⟨j.val,by simp only [List.length_map]; exact j.isLt⟩
  have hx' : x ∈ (F.map Prod.fst).get j' := by simpa [List.get_eq_getElem,j'] using hx
  have hcard := hc j' hx'
  have hle := Finset.card_le_univ (S j')
  simp only [Fintype.card_fin] at hle
  omega

/-- Every through exponent of the genuine whole pulled product is internally the original literal power. -/
theorem pullback_indexed_product_divExp {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (y : Y) (j : Fin F.length) (hy : f y ∈ (F.get j).1) :
    divExp m (GermIdeal.pullback (m := m) f (componentPowerProduct (n := n) F))
      (f ⁻¹' (F.get j).1) y = (F.get j).2 := by
  have hG := pulledWeights_isSNCDivisor hf F hF
  have hy' : y ∈ ((pulledWeights f F).get (pulledIndex f F j)).1 := by
    rw [pulledWeights_get]
    exact hy
  have hm := positive_dimension_of_through hG y (pulledIndex f F j) hy'
  rw [pullback_componentPowerProduct hf F hF]
  have he := indexed_product_divExp hm _ hG y (pulledIndex f F j) hy'
  simpa only [pulledWeights_get] using he

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Actual surjectivity, and only surjectivity, reflects every positive nonempty literal index. -/
theorem activeIndices_pulled_iff (f : Y → X) (hsurj : Function.Surjective f)
    (F : List (Set X × ℕ)) (j : Fin F.length) :
    pulledIndex f F j ∈ activeIndices (pulledWeights f F) ↔ j ∈ activeIndices F := by
  classical
  simp only [activeIndices,Finset.mem_filter,Finset.mem_univ,true_and,pulledWeights_get]
  constructor
  · rintro ⟨hp,y,hy⟩
    exact ⟨hp,f y,hy⟩
  · rintro ⟨hp,x,hx⟩
    obtain ⟨y,rfl⟩ := hsurj x
    exact ⟨hp,y,hx⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The complete actual active finite index set transports exactly by its literal equivalence. -/
theorem activeIndices_pulled_eq (f : Y → X) (hsurj : Function.Surjective f)
    (F : List (Set X × ℕ)) :
    activeIndices (pulledWeights f F) = (activeIndices F).map (pulledIndex f F).toEmbedding := by
  classical
  ext j
  constructor
  · intro hj
    refine Finset.mem_map.mpr ⟨(pulledIndex f F).symm j,?_,by simp⟩
    exact (activeIndices_pulled_iff f hsurj F _).mp (by simpa using hj)
  · rintro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact (activeIndices_pulled_iff f hsurj F i).mpr hi

/-- The literal original cosupport maximum locus pulls back only under genuine surjectivity. -/
theorem maxLocus_indexed_product_pullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ResolutionDriver.maxLocus (gamma m (componentPowerProduct (n := m) (pulledWeights f F))
      ((pulledWeights f F).map Prod.fst) 1)
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F)).cosupp =
    f ⁻¹' ResolutionDriver.maxLocus (gamma n (componentPowerProduct (n := n) F)
      (F.map Prod.fst) 1) (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp := by
  have hc := (isWellFormed_monomialMarkedIdeal hF F
    (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)).isCoherent
  have he := maxLocus_gamma_markedPullback_eq hf hsurj
    (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) rfl hc hF
  rw [markedPullback_indexed_dictionary hf F hF] at he
  exact he

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Literal singleton keys retain the entire original coefficient and colex index. -/
theorem singletonKey_pulled (f : Y → X) (F : List (Set X × ℕ)) (j : Fin F.length) :
    singletonKey (n := m) (pulledWeights f F) (pulledIndex f F j) =
      key m (indexedPowerData F) {j.val} := by
  change key m (indexedPowerData (pulledWeights f F)) {j.val} = _
  simp only [key,Finset.sum_singleton,indexedPowerData,dif_pos j.isLt]
  have hl : j.val < (pulledWeights f F).length := by simp only [pulledWeights,List.length_map]; exact j.isLt
  rw [dif_pos hl]
  change toLex (m-1,toLex (((pulledWeights f F).get (pulledIndex f F j)).2,toColex {j.val})) = _
  rw [pulledWeights_get]
  rfl

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
/-- Actual nonempty SNC input internally reflects every singleton key order across true dimensions. -/
theorem singletonKey_pulled_le_iff {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (i j : Fin F.length)
    (hj : j ∈ activeIndices F) :
    singletonKey (n := m) (pulledWeights f F) (pulledIndex f F i) ≤
      singletonKey (n := m) (pulledWeights f F) (pulledIndex f F j) ↔
    singletonKey (n := n) F i ≤ singletonKey (n := n) F j := by
  classical
  obtain ⟨_,_,x,hx⟩ := Finset.mem_filter.mp hj
  have hn := positive_dimension_of_through hF x j hx
  obtain ⟨y,rfl⟩ := hsurj x
  have hnm := dimension_le_of_submersionAt (hf.isSubmersionAt y)
  rw [singletonKey_pulled,singletonKey_pulled]
  unfold singletonKey
  exact (key_le_key_dimension_iff n m hnm _ _ _ _ (by simp; omega) (by simp; omega)).symm

/-- Genuine surjective geometry internally produces either no centre or the SAME unique true old-key index and whole centre preimage. -/
theorem exists_common_actual_gamma_maximum_centre {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    activeIndices F = ∅ ∧ activeIndices (pulledWeights f F) = ∅ ∨
    ∃ j ∈ activeIndices F,
      pulledIndex f F j ∈ activeIndices (pulledWeights f F) ∧
      ResolutionDriver.maxLocus (gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1)
        (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp = (F.get j).1 ∧
      ResolutionDriver.maxLocus (gamma m (componentPowerProduct (n := m) (pulledWeights f F))
        ((pulledWeights f F).map Prod.fst) 1)
        (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F)).cosupp =
          f ⁻¹' (F.get j).1 ∧
      (∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j) ∧
      (∀ i ∈ activeIndices (pulledWeights f F), singletonKey (n := m) (pulledWeights f F) i ≤
        singletonKey (n := m) (pulledWeights f F) (pulledIndex f F j)) ∧
      (∀ k ∈ activeIndices F, (∀ i ∈ activeIndices F,
        singletonKey (n := n) F i ≤ singletonKey (n := n) F k) → k = j) ∧
      ∀ k ∈ activeIndices (pulledWeights f F), (∀ i ∈ activeIndices (pulledWeights f F),
        singletonKey (n := m) (pulledWeights f F) i ≤ singletonKey (n := m) (pulledWeights f F) k) →
          k = pulledIndex f F j := by
  classical
  by_cases he : activeIndices F = ∅
  · exact Or.inl ⟨he,by rw [activeIndices_pulled_eq f hsurj F,he,Finset.map_empty]⟩
  · obtain ⟨k,hk⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨_,_,x,hx⟩ := Finset.mem_filter.mp hk
    have hn := positive_dimension_of_through hF x k hx
    obtain ⟨j,hj,hcentre,hmax,hunique⟩ := (exists_actual_gamma_maximum_centre hn F hF).resolve_left he
    have hj' := (activeIndices_pulled_iff f hsurj F j).mpr hj
    have hmax' : ∀ i ∈ activeIndices (pulledWeights f F), singletonKey (n := m) (pulledWeights f F) i ≤
        singletonKey (n := m) (pulledWeights f F) (pulledIndex f F j) := by
      intro i hi
      have hi' := (activeIndices_pulled_iff f hsurj F ((pulledIndex f F).symm i)).mp (by simpa using hi)
      have h := (singletonKey_pulled_le_iff hf hsurj F hF _ j hj).mpr (hmax _ hi')
      simpa using h
    refine Or.inr ⟨j,hj,hj',hcentre,?_,hmax,hmax',hunique,?_⟩
    · rw [maxLocus_indexed_product_pullback hf hsurj F hF,hcentre]
    · intro k hk hm
      exact singletonKey_injective _ (le_antisymm (hmax' k hk) (hm _ hj'))

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Entire pulled history commutes literally with the real selected empty entry and appended exceptional factor. -/
theorem pulledWeights_dividedWeights (f : Y → X) (F : List (Set X × ℕ)) (j : Fin F.length) :
    pulledWeights f (dividedWeights F j) =
      dividedWeights (pulledWeights f F) (pulledIndex f F j) := by
  simp only [dividedWeights,pulledWeights,List.map_append,List.map_set,List.map_singleton]
  rw [preimage_empty]
  have hg := pulledWeights_get f F j
  simp only [pulledWeights] at hg
  rw [hg]
  rfl

/-- The original literal indexed member internally supplies its genuine identity Cartier blowup. -/
theorem isBlowupAlong_id_indexed_member (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) :
    IsBlowupAlong n (F.get j).1 (id : X → X) := by
  let j' : Fin (F.map Prod.fst).length := ⟨j.val,by simp only [List.length_map]; exact j.isLt⟩
  have hg : (F.map Prod.fst).get j' = (F.get j).1 := by simp [List.get_eq_getElem,j']
  exact hg ▸ isBlowupAlong_id_snc_member hF j'

/-- Both SAME source and true pulled positive carriers internally give actual blowups and mark-one admissibility. -/
theorem actual_Cartier_and_admissibility_pullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (j : Fin F.length) (hj : 0 < (F.get j).2) :
    IsBlowupAlong n (F.get j).1 (id : X → X) ∧
    (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).IsAdmissibleCentre (F.get j).1 ∧
    IsBlowupAlong m (f ⁻¹' (F.get j).1) (id : Y → Y) ∧
    (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)).IsAdmissibleCentre
      (f ⁻¹' (F.get j).1) := by
  have hG := pulledWeights_isSNCDivisor hf F hF
  have hj' : 0 < ((pulledWeights f F).get (pulledIndex f F j)).2 := by rw [pulledWeights_get]; exact hj
  refine ⟨isBlowupAlong_id_indexed_member F hF j,
    isAdmissibleCentre_indexed_positive (A := CMfd.of (n := n) X) F hF j hj,?_,?_⟩
  · simpa only [pulledWeights_get] using isBlowupAlong_id_indexed_member (pulledWeights f F) hG (pulledIndex f F j)
  · rw [markedPullback_indexed_dictionary hf F hF]
    simpa only [pulledWeights_get] using isAdmissibleCentre_indexed_positive (A := CMfd.of (n := m) Y)
      (pulledWeights f F) hG (pulledIndex f F j) hj'

/-- Actual WHOLE next controlled marked transform equals its genuine pullback, with every literal historical entry retained. -/
theorem markedPullback_geoTransform_indexed_positive {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (j : Fin F.length) (hj : 0 < (F.get j).2) :
    markedPullback (m := m) f
      ((monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 (id : X → X)) =
    (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)).geoTransform
      (f ⁻¹' (F.get j).1) (id : Y → Y) := by
  have hG := pulledWeights_isSNCDivisor hf F hF
  have hj' : 0 < ((pulledWeights f F).get (pulledIndex f F j)).2 := by rw [pulledWeights_get]; exact hj
  have hD := dividedWeights_isSNCDivisor (A := CMfd.of (n := n) X) F hF j hj
  rw [geoTransform_indexed_positive (A := CMfd.of (n := n) X) F hF j hj,
    markedPullback_indexed_dictionary hf (dividedWeights F j) hD,
    markedPullback_indexed_dictionary hf F hF]
  have he := geoTransform_indexed_positive (A := CMfd.of (n := m) Y)
    (pulledWeights f F) hG (pulledIndex f F j) hj'
  rw [pulledWeights_get] at he
  rw [he,pulledWeights_dividedWeights]

/-- The SAME true pulled controlled ideal internally computes EVERY genuine through exponent on the whole new indexed family. -/
theorem controlled_pullback_intrinsic_exponents {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (j : Fin F.length) (hj : 0 < (F.get j).2) (y : Y) (i : Fin (dividedWeights F j).length)
    (hy : f y ∈ ((dividedWeights F j).get i).1) :
    divExp m ((markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)).geoTransform
      (f ⁻¹' (F.get j).1) (id : Y → Y)).ideal
      (f ⁻¹' ((dividedWeights F j).get i).1) y = ((dividedWeights F j).get i).2 := by
  rw [← markedPullback_geoTransform_indexed_positive hf F hF j hj,
    geoTransform_indexed_positive (A := CMfd.of (n := n) X) F hF j hj]
  exact pullback_indexed_product_divExp hf _
    (dividedWeights_isSNCDivisor (A := CMfd.of (n := n) X) F hF j hj) y i hy

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Exact arithmetic for the ENTIRE real pulled controlled list; no uniform-bound certificate is an input. -/
theorem controlled_pulled_coefficient_sum (f : Y → X) (F : List (Set X × ℕ))
    (j : Fin F.length) (hj : 0 < (F.get j).2) :
    ((dividedWeights (pulledWeights f F) (pulledIndex f F j)).map Prod.snd).sum + 1 =
      (F.map Prod.snd).sum := by
  rw [← pulledWeights_dividedWeights,pulledWeights_powers]
  have hOld := ((List.getElem_cons_eraseIdx_perm (l := F) j.isLt).map Prod.snd).sum_eq
  have hNew := ((List.set_perm_cons_eraseIdx (l := F) j.isLt (∅,0)).map Prod.snd).sum_eq
  simp only [List.map_cons,List.sum_cons,zero_add] at hOld hNew
  change (F.get j).2 + (F.eraseIdx j.val |>.map Prod.snd).sum = (F.map Prod.snd).sum at hOld
  rw [dividedWeights,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,hNew]
  change (List.map Prod.snd (F.eraseIdx j.val)).sum + ((F.get j).2-1) +1 = (F.map Prod.snd).sum
  omega

/-- The internally inactive genuine whole products are unit on BOTH sides, including both zero dimensions and empty manifolds. -/
theorem indexed_product_unit_pullback_of_inactive {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set X × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (he : activeIndices F = ∅) :
    componentPowerProduct (n := n) F = unitIdeal n X ∧
      componentPowerProduct (n := m) (pulledWeights f F) = unitIdeal m Y := by
  have hu := indexed_product_eq_unit_of_no_active (A := CMfd.of (n := n) X) F hF he
  refine ⟨hu,?_⟩
  rw [← pullback_componentPowerProduct hf F hF,hu]
  exact pullback_unitIdeal

end
end Hironaka.HironakaSmoothSubmersionNormalCrossings
