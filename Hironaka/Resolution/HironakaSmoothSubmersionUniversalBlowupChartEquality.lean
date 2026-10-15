/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionAdaptedBlowupCoverage
import Hironaka.Resolution.HironakaSmoothSubmersionBlowupLift
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionUniversalBlowupChartEquality
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  HironakaSmoothSubmersionAdaptedProductCoordinates HironakaSmoothSubmersionAdaptedBlowupCharts
  HironakaSmoothSubmersionAdaptedBlowupCoverage HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionOrderedChoiceImageTrace
  VanishingIdealCoherent
noncomputable section
section Parameters
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {C : Set X}

def flatParameterLift (c : FlatChart n C) :
    LiftedOpen.{u} (monomialDomain c.Φ c.k c.j) → BlowupSpace n C :=
  fun w => c.invFun (LiftedOpen.toModel _ w)

theorem flatParameterLift_contMDiff [Fact (IsClosedSubmanifold n C)] (c : FlatChart n C) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (flatParameterLift c) := by
  intro w
  have ht : c.homeo.target = c.target :=
    congrArg (fun e => e.target) (atlasHomeo_toPartialEquiv c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  have hw : LiftedOpen.toModel _ w ∈ c.homeo.target := by
    rw [ht]
    exact LiftedOpen.toModel_mem _ w
  have hmax := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  exact (contMDiffAt_symm_of_mem_maximalAtlas hmax hw).comp w (LiftedOpen.contMDiff_toModel _ w)

theorem flatParameterLift_proj (c : FlatChart n C) :
    blowupProj n C ∘ flatParameterLift c = monomialChart c.Φ c.k c.j := by
  funext w
  exact c.base_invFun (LiftedOpen.toModel_mem _ w)
end Parameters

section OriginalIdeal
variable {n r : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X} {C : Set X}

theorem actual_parameter_base_ideal_eq
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hC : IsClosedSubmanifold n C) (c' : FlatChart (n+r) (f ⁻¹' C)) :
    GermIdeal.pullback (m := n+r) (f ∘ monomialChart c'.Φ c'.k c'.j)
      (vanishingIdeal (n := n) C) =
    GermIdeal.pullback (m := n+r) (monomialChart c'.Φ c'.k c'.j)
      (vanishingIdeal (n := n+r) (f ⁻¹' C)) := by
  rw [coherent_pullback_comp hf.contMDiff (contMDiff_monomialChart c'.hsrc) _
    (isCoherent_vanishingIdeal hC),pullback_vanishingIdeal_submersion hf hC]

theorem actual_parameter_base_ideal_invertible
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hC : IsClosedSubmanifold n C) (c' : FlatChart (n+r) (f ⁻¹' C)) :
    (GermIdeal.pullback (m := n+r) (f ∘ monomialChart c'.Φ c'.k c'.j)
      (vanishingIdeal (n := n) C)).IsInvertible := by
  rw [actual_parameter_base_ideal_eq hf hC c']
  exact isInvertible_pullback_monomialChart c'.hsrc c'.hflat c'.hj

variable [Fact (IsClosedSubmanifold n C)] [Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C))]

private theorem canonical_lift_eqOn_flatChart
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C))
    (R : TopologicalSpace.Opens (ComplexModel r))
    (hdom : c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target))
    (hpoint : ∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w))
    (G : BlowupSpace (n+r) (f ⁻¹' C) → BlowupSpace n C)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ G)
    (hGsquare : blowupProj n C ∘ G = f ∘ blowupProj (n+r) (f ⁻¹' C)) :
    EqOn G (flatChartMap c c') c'.source := by
  let O := monomialDomain c'.Φ c'.k c'.j
  have hdropmem (w : LiftedOpen.{u} O) : adaptedTargetProjection n r (LiftedOpen.toModel O w) ∈ c.target := by
    have hw : LiftedOpen.toModel O w ∈ c'.target := LiftedOpen.toModel_mem _ w
    rw [hdom] at hw
    exact hw.2
  let L : ComplexModel (n+r) →L[ℂ] ComplexModel n :=
    (ContinuousLinearMap.snd ℂ (ComplexModel r) (ComplexModel n)).comp (fibreFirstSplit n r).toContinuousLinearMap
  have hdrop : ContMDiff 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞
      (fun w : LiftedOpen.{u} O => adaptedTargetProjection n r (LiftedOpen.toModel O w)) :=
    L.contDiff.contMDiff.comp (LiftedOpen.contMDiff_toModel O)
  let G₁ : LiftedOpen.{u} O → BlowupSpace n C := G ∘ flatParameterLift c'
  let G₂ : LiftedOpen.{u} O → BlowupSpace n C :=
    fun w => c.invFun (adaptedTargetProjection n r (LiftedOpen.toModel O w))
  have h₁ : ContMDiff 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ G₁ :=
    hG.comp (flatParameterLift_contMDiff c')
  have h₂ : ContMDiff 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ G₂ := by
    intro w
    have ht : c.homeo.target = c.target :=
      congrArg (fun e => e.target) (atlasHomeo_toPartialEquiv c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
    have hw : adaptedTargetProjection n r (LiftedOpen.toModel O w) ∈ c.homeo.target := by
      rw [ht]
      exact hdropmem w
    have hmax := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
    exact (contMDiffAt_symm_of_mem_maximalAtlas hmax hw).comp w (hdrop w)
  have hsq₁ : ∀ w : LiftedOpen.{u} O,
      blowupProj n C (G₁ w) = (f ∘ monomialChart c'.Φ c'.k c'.j) w := by
    intro w
    have hh := congrFun hGsquare (flatParameterLift c' w)
    change blowupProj n C (G₁ w) = f (blowupProj (n+r) (f ⁻¹' C) (flatParameterLift c' w)) at hh
    have hb := congrFun (flatParameterLift_proj c') w
    change blowupProj (n+r) (f ⁻¹' C) (flatParameterLift c' w) = monomialChart c'.Φ c'.k c'.j w at hb
    rw [hb] at hh
    exact hh
  have hsq₂ : ∀ w : LiftedOpen.{u} O,
      blowupProj n C (G₂ w) = (f ∘ monomialChart c'.Φ c'.k c'.j) w := by
    intro w
    change (c.invFun (adaptedTargetProjection n r (LiftedOpen.toModel O w))).base = _
    rw [c.base_invFun (hdropmem w)]
    exact (hpoint _ (LiftedOpen.toModel_mem O w)).symm
  have he := lift_eqOn (hf.contMDiff.comp (contMDiff_monomialChart c'.hsrc))
    (actual_parameter_base_ideal_invertible hf Fact.out c') isOpen_univ
    (fun w _ => (h₁ w).continuousAt) (fun w _ => (h₂ w).continuousAt)
    (fun w _ => hsq₁ w) (fun w _ => hsq₂ w)
  intro p hp
  let w : LiftedOpen.{u} O := LiftedOpen.mk O (c'.toFun p) (c'.map_source hp)
  have hw : flatParameterLift c' w = p := c'.left_inv hp
  calc
    G p = G₁ w := (congrArg G hw).symm
    _ = G₂ w := he (mem_univ w)
    _ = flatChartMap c c' p := rfl

theorem canonical_actualLift_eqOn_flatChart
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hCi : interior C = ∅)
    (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C))
    (R : TopologicalSpace.Opens (ComplexModel r))
    (hdom : c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target))
    (hpoint : ∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w)) :
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hCi' := (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) hCi'
    EqOn (actualLift (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ') (flatChartMap c c') c'.source := by
  dsimp only
  apply canonical_lift_eqOn_flatChart hf c c' R hdom hpoint
  · exact actualLift_contMDiff hf _ _
  · exact actualLift_proj_comm (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf
      (isBlowupAlong_blowupProj (n := n) (C := C) hCi)
      (isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
        (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf
          (isBlowupAlong_blowupProj (n := n) (C := C) hCi)).2)
private theorem matching_flatChartMap_submersionAt {f : Y → X} {C : Set X}
    [Fact (IsClosedSubmanifold n C)] [Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C))]
    (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C))
    (R : TopologicalSpace.Opens (ComplexModel r))
    (hdom : c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target))
    (p : BlowupSpace (n+r) (f ⁻¹' C)) (hp : p ∈ c'.source) :
    Manifold.IsSubmersionAtOfComplement (ComplexModel r)
      𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ (flatChartMap c c') p := by
  have drop_mem {w : ComplexModel (n+r)} (hw : w ∈ c'.target) :
      adaptedTargetProjection n r w ∈ c.target := by
    rw [hdom] at hw
    exact hw.2
  have hG : flatChartMap c c' p ∈ c.source := c.map_target (drop_mem (c'.map_source hp))
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
    ((fibreFirstSplit n r).trans (ContinuousLinearEquiv.prodComm ℂ (ComplexModel r) (ComplexModel n)))
    c'.homeo c.homeo hp hG
    (IsManifold.subset_maximalAtlas (atlasHomeo_mem_atlas _ (Or.inl ⟨c',rfl⟩)))
    (IsManifold.subset_maximalAtlas (atlasHomeo_mem_atlas _ (Or.inl ⟨c,rfl⟩)))
  · intro q hq
    exact c.map_target (drop_mem (c'.map_source hq))
  · intro w hw
    have hw' : w ∈ c'.target := by
      have hw0 : w ∈ c'.homeo.target := by simpa using hw
      have ht : c'.homeo.target = c'.target := by
        exact congrArg (fun e => e.target) (atlasHomeo_toPartialEquiv c'.toPartialEquiv (Or.inl ⟨c',rfl⟩))
      rwa [ht] at hw0
    change c.toFun (c.invFun (adaptedTargetProjection n r (c'.toFun (c'.invFun w)))) =
      adaptedTargetProjection n r w
    rw [c'.right_inv hw',c.right_inv (drop_mem hw')]


end OriginalIdeal

section OriginalExceptional
variable {n r : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X}

theorem actualLift_exceptional_isSubmersionAtOfComplement
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hCi' := (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) hCi'
    ∀ p : BlowupSpace (n+r) (f ⁻¹' C), p.base ∈ f ⁻¹' C →
      Manifold.IsSubmersionAtOfComplement (ComplexModel r)
        𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞
        (actualLift (D := CMfd.of (BlowupSpace n C))
          (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ') p := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  intro p hpC
  obtain ⟨R,S,k,j,c,c',_,_,_,_,_,_,_,_,_,_,hs,hp,hpoint⟩ :=
    (exists_original_exceptional_matching_charts hf C hC).2 p hpC
  have hh := matching_flatChartMap_submersionAt c c' R hs p hp
  apply hh.congr_of_eventuallyEq
  filter_upwards [c'.isOpen_source.mem_nhds hp] with q hq
  exact (canonical_actualLift_eqOn_flatChart hf hCi c c' R hs hpoint hq).symm
end OriginalExceptional

end
end Hironaka.HironakaSmoothSubmersionUniversalBlowupChartEquality
