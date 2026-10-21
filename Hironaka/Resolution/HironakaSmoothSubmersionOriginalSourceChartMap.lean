/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTargetChartCompatibility
import Mathlib.Data.Set.UnionLift
/-! Entire original source-chart maps and their genuine full Cartesian squares.
Complete mathematics preceded code. Real target-index compatibility and a true
cover construct the map; actual local universal properties construct and glue
all cone lifts internally, including their real joint point injectivity. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaSmoothSubmersionOriginalSourceChartMap
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaSmoothSubmersionOriginalLocalChartArrow HironakaSmoothSubmersionOriginalLocalGlobalArrow
  HironakaSmoothSubmersionOriginalTargetChartCompatibility HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {m n : ℕ}

/-- Genuine holomorphic universal uniqueness includes actual pointwise
joint injectivity: constant maps use the actual final source as test manifold. -/
theorem holomorphicSquarePullback_jointInjective
    {Y E : CMfd.{u} m} {X D : CMfd.{u} n} {f : Y → X} {g : E → D} {p : E → Y} {t : D → X}
    (hU : HolomorphicSquarePullback f g p t) (hcomm : ∀ y, t (g y)=f (p y))
    (y z : E) (hp : p y=p z) (hg : g y=g z) : y=z := by
  obtain ⟨w,_hw,huniq⟩ := hU m E (fun _ => p y) (fun _ => g y)
    contMDiff_const contMDiff_const (fun _ => (hcomm y).symm)
  have he : (fun _ : E => y)=(fun _ : E => z) :=
    (huniq (fun _ => y) ⟨contMDiff_const,fun _ => rfl,fun _ => rfl⟩).trans
      (huniq (fun _ => z) ⟨contMDiff_const,fun _ => hp.symm,fun _ => hg.symm⟩).symm
  exact congrFun he y

private theorem cover_iUnion {k : ℕ} {A : CMfd.{u} k} {ι : Type v}
    (O : ι → Opens A) (hcover : ∀ x : A, ∃ i, x ∈ O i) :
    (⋃ i, (O i : Set A))=univ := eq_univ_iff_forall.mpr (fun x => mem_iUnion.mpr (hcover x))

def holomorphicOpenCoverGlue {k l : ℕ} {A : CMfd.{u} k} {B : CMfd.{u} l} {ι : Type v}
    (O : ι → Opens A) (F : ∀ i, O i → B)
    (hF : ∀ i j x hxi hxj, F i ⟨x,hxi⟩=F j ⟨x,hxj⟩)
    (hcover : ∀ x : A, ∃ i, x ∈ O i) : A → B :=
  Set.liftCover (fun i => (O i : Set A)) F hF (cover_iUnion O hcover)

theorem holomorphicOpenCoverGlue_local {k l : ℕ} {A : CMfd.{u} k} {B : CMfd.{u} l} {ι : Type v}
    (O : ι → Opens A) (F : ∀ i, O i → B)
    (hF : ∀ i j x hxi hxj, F i ⟨x,hxi⟩=F j ⟨x,hxj⟩)
    (hcover : ∀ x : A, ∃ i, x ∈ O i) (i : ι) (x : O i) :
    holomorphicOpenCoverGlue O F hF hcover x.val=F i x :=
  Set.liftCover_coe (S := fun i => (O i : Set A)) (f := F) (hf := hF)
    (hS := cover_iUnion O hcover) x

theorem holomorphicOpenCoverGlue_contMDiff {k l : ℕ} {A : CMfd.{u} k} {B : CMfd.{u} l} {ι : Type v}
    (O : ι → Opens A) (F : ∀ i, O i → B)
    (hF : ∀ i j x hxi hxj, F i ⟨x,hxi⟩=F j ⟨x,hxj⟩)
    (hcover : ∀ x : A, ∃ i, x ∈ O i)
    (hhol : ∀ i, ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel l) ∞ (F i)) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel l) ∞ (holomorphicOpenCoverGlue O F hF hcover) := by
  intro x
  obtain ⟨i,hi⟩ := hcover x
  have he : (holomorphicOpenCoverGlue O F hF hcover) ∘ (Subtype.val : O i → A)=F i :=
    funext (holomorphicOpenCoverGlue_local O F hF hcover i)
  have hh : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel l) ∞
      ((holomorphicOpenCoverGlue O F hF hcover) ∘ (Subtype.val : O i → A)) := by rw [he]; exact hhol i
  exact contMDiffAt_subtype_iff.mp (hh ⟨x,hi⟩)

section Original
variable {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
  (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)

private def A := actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)

private theorem sourceChartFinal_cover (i : Y) :
    ∀ x : (A hf M hM).finalSpace i, ∃ j, x ∈ originalLocalSmoothChartArrowSourceOpen hf M hM i j := by
  intro x
  let j := f ((((A hf M hM).tower i).proj x).val)
  exact ⟨j,⟨(((A hf M hM).tower i).proj x).property,(actualLocalTerminalAtlas M hM).point_mem j⟩⟩

private theorem sourceChartFinal_compatible (i : Y) (j k : X)
    (x : (A hf M hM).finalSpace i)
    (hxj : x ∈ originalLocalSmoothChartArrowSourceOpen hf M hM i j)
    (hxk : x ∈ originalLocalSmoothChartArrowSourceOpen hf M hM i k) :
    originalLocalTerminalSmoothGlobalArrow hf M hM i j ⟨x,hxj⟩=
      originalLocalTerminalSmoothGlobalArrow hf M hM i k ⟨x,hxk⟩ := by
  let U := actualSmoothChartNestedOpen hf ((A hf M hM).openSet i) ((actualLocalTerminalAtlas M hM).openSet j)
  let V := actualSmoothChartNestedOpen hf ((A hf M hM).openSet i) ((actualLocalTerminalAtlas M hM).openSet k)
  let q : openPreimage ((A hf M hM).tower i) (U ⊓ V) := ⟨x,⟨hxj,hxk⟩⟩
  exact congrFun (originalLocalTerminalSmoothGlobalArrow_target_compatibility hf M hM i j k) q

def originalSourceChartBaseMap (i : Y) : (A hf M hM).openSet i → X := fun y => f y.val

/-- Only original inputs glue all actual target chart arrows on the ENTIRE
original source local final manifold. -/
def originalSourceChartSmoothMap (i : Y) : (A hf M hM).finalSpace i → originalTerminalManifold M hM :=
  holomorphicOpenCoverGlue (originalLocalSmoothChartArrowSourceOpen hf M hM i)
    (originalLocalTerminalSmoothGlobalArrow hf M hM i) (sourceChartFinal_compatible hf M hM i)
    (sourceChartFinal_cover hf M hM i)

theorem originalSourceChartSmoothMap_local (i : Y) (j : X)
    (x : originalLocalSmoothChartArrowSourceOpen hf M hM i j) :
    originalSourceChartSmoothMap hf M hM i x.val=originalLocalTerminalSmoothGlobalArrow hf M hM i j x :=
  holomorphicOpenCoverGlue_local _ _ _ _ j x

theorem originalSourceChartSmoothMap_contMDiff (i : Y) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (originalSourceChartSmoothMap hf M hM i) :=
  holomorphicOpenCoverGlue_contMDiff _ _ _ _
    (fun j => (originalLocalTerminalSmoothGlobalArrow_properties hf M hM i j).1)

theorem originalSourceChartSmoothMap_proj (i : Y) (x : (A hf M hM).finalSpace i) :
    originalTerminalGluedProjection M hM (originalSourceChartSmoothMap hf M hM i x)=
      f ((((A hf M hM).tower i).proj x).val) := by
  obtain ⟨j,hj⟩ := sourceChartFinal_cover hf M hM i x
  rw [originalSourceChartSmoothMap_local hf M hM i j ⟨x,hj⟩]
  exact (originalLocalTerminalSmoothGlobalArrow_properties hf M hM i j).2.1 ⟨x,hj⟩

private theorem originalChartArrow_commutes (i : Y) (j : X)
    (x : originalLocalSmoothChartArrowSourceOpen hf M hM i j) :
    originalTerminalGluedProjection M hM (originalLocalTerminalSmoothGlobalArrow hf M hM i j x)=
      originalSmoothChartOriginalBaseMap hf M hM i j
        ((restrict (actualSmoothChartNestedOpen hf ((A hf M hM).openSet i)
          ((actualLocalTerminalAtlas M hM).openSet j)) ((A hf M hM).tower i)).proj x) := by
  let V := actualSmoothChartNestedOpen hf ((A hf M hM).openSet i) ((actualLocalTerminalAtlas M hM).openSet j)
  let q : openPreimage ((A hf M hM).tower i) V := x
  have hp := congrArg (fun z : (A hf M hM).openSet i => z.val) (proj_restrict V ((A hf M hM).tower i) q)
  exact ((originalLocalTerminalSmoothGlobalArrow_properties hf M hM i j).2.1 q).trans (congrArg f hp.symm)

theorem originalSourceChartSmoothMap_cartesian (i : Y) :
    HolomorphicSquarePullback (originalSourceChartBaseMap hf M hM i) (originalSourceChartSmoothMap hf M hM i)
      ((A hf M hM).tower i).proj (originalTerminalGluedProjection M hM) := by
  intro k W a b ha hb hcone
  let C := A hf M hM
  let B := actualLocalTerminalAtlas M hM
  let Q (j : X) := actualSmoothChartNestedOpen hf (C.openSet i) (B.openSet j)
  let O (j : X) : Opens W := ⟨a ⁻¹' (Q j : Set (C.openSet i)),(Q j).isOpen.preimage ha.continuous⟩
  have hcover : ∀ x : W, ∃ j, x ∈ O j := by
    intro x
    let j := f (a x).val
    exact ⟨j,⟨(a x).property,B.point_mem j⟩⟩
  let aj (j : X) : O j → Q j := fun z => ⟨a z.val,z.property⟩
  have haj (j : X) : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ (aj j) :=
    BlowupRestrictOpen.contMDiff_opens_mk (ha.comp contMDiff_subtype_val) (fun z => z.property)
  have hex (j : X) : ∃ r : O j → openPreimage (C.tower i) (Q j),
      ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ r ∧
      (∀ z, (restrict (Q j) (C.tower i)).proj (r z)=aj j z) ∧
      ∀ z, originalLocalTerminalSmoothGlobalArrow hf M hM i j (r z)=b z.val :=
    ((originalLocalTerminalSmoothGlobalArrow_properties hf M hM i j).2.2 k
      (CMfd.of (n := k) (O j)) (aj j) (b ∘ Subtype.val) (haj j) (hb.comp contMDiff_subtype_val)
      (fun z => hcone z.val)).exists
  choose r hr using hex
  let rfull (j : X) : O j → C.finalSpace i := Subtype.val ∘ r j
  have hsource (j : X) (z : O j) : (C.tower i).proj (rfull j z)=a z.val :=
    (proj_restrict (Q j) (C.tower i) (r j z)).symm.trans (congrArg Subtype.val ((hr j).2.1 z))
  have htarget (j : X) (z : O j) : originalSourceChartSmoothMap hf M hM i (rfull j z)=b z.val :=
    (originalSourceChartSmoothMap_local hf M hM i j (r j z)).trans ((hr j).2.2 z)
  have hcompat : ∀ j l x hxj hxl, rfull j ⟨x,hxj⟩=rfull l ⟨x,hxl⟩ := by
    intro j l x hxj hxl
    let rj := r j ⟨x,hxj⟩
    let rl := rfull l ⟨x,hxl⟩
    have hlmem : rl ∈ originalLocalSmoothChartArrowSourceOpen hf M hM i j := by
      change (C.tower i).proj rl ∈ Q j
      rw [hsource l ⟨x,hxl⟩]
      exact hxj
    let rlJ : originalLocalSmoothChartArrowSourceOpen hf M hM i j := ⟨rl,hlmem⟩
    have hp : (restrict (Q j) (C.tower i)).proj rj=(restrict (Q j) (C.tower i)).proj rlJ := by
      apply Subtype.ext
      exact (proj_restrict (Q j) (C.tower i) rj).trans
        ((hsource j ⟨x,hxj⟩).trans ((hsource l ⟨x,hxl⟩).symm.trans
          (proj_restrict (Q j) (C.tower i) rlJ).symm))
    have ht : originalLocalTerminalSmoothGlobalArrow hf M hM i j rj=
        originalLocalTerminalSmoothGlobalArrow hf M hM i j rlJ :=
      ((hr j).2.2 ⟨x,hxj⟩).trans
        ((originalSourceChartSmoothMap_local hf M hM i j rlJ).symm.trans (htarget l ⟨x,hxl⟩)).symm
    exact congrArg Subtype.val (holomorphicSquarePullback_jointInjective
      (originalLocalTerminalSmoothGlobalArrow_properties hf M hM i j).2.2
      (originalChartArrow_commutes hf M hM i j) rj rlJ hp ht)
  let L := holomorphicOpenCoverGlue O rfull hcompat hcover
  have hLhol : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ L :=
    holomorphicOpenCoverGlue_contMDiff O rfull hcompat hcover
      (fun j => contMDiff_subtype_val.comp (hr j).1)
  have hLlocal (j : X) (z : O j) : L z.val=rfull j z :=
    holomorphicOpenCoverGlue_local O rfull hcompat hcover j z
  refine ⟨L,⟨hLhol,?_,?_⟩,?_⟩
  · intro z
    obtain ⟨j,hj⟩ := hcover z
    rw [hLlocal j ⟨z,hj⟩]
    exact hsource j ⟨z,hj⟩
  · intro z
    obtain ⟨j,hj⟩ := hcover z
    rw [hLlocal j ⟨z,hj⟩]
    exact htarget j ⟨z,hj⟩
  · intro v hv
    funext z
    obtain ⟨j,hj⟩ := hcover z
    have hvmem : v z ∈ originalLocalSmoothChartArrowSourceOpen hf M hM i j := by
      change (C.tower i).proj (v z) ∈ Q j
      rw [hv.2.1 z]
      exact hj
    let vj : originalLocalSmoothChartArrowSourceOpen hf M hM i j := ⟨v z,hvmem⟩
    let rj := r j ⟨z,hj⟩
    have hp : (restrict (Q j) (C.tower i)).proj rj=(restrict (Q j) (C.tower i)).proj vj := by
      apply Subtype.ext
      exact (proj_restrict (Q j) (C.tower i) rj).trans
        ((hsource j ⟨z,hj⟩).trans ((hv.2.1 z).symm.trans (proj_restrict (Q j) (C.tower i) vj).symm))
    have ht : originalLocalTerminalSmoothGlobalArrow hf M hM i j rj=
        originalLocalTerminalSmoothGlobalArrow hf M hM i j vj :=
      ((hr j).2.2 ⟨z,hj⟩).trans
        ((originalSourceChartSmoothMap_local hf M hM i j vj).symm.trans (hv.2.2 z)).symm
    have he := holomorphicSquarePullback_jointInjective
      (originalLocalTerminalSmoothGlobalArrow_properties hf M hM i j).2.2
      (originalChartArrow_commutes hf M hM i j) rj vj hp ht
    rw [hLlocal j ⟨z,hj⟩]
    exact (congrArg Subtype.val he).symm

end Original
end
end Hironaka.HironakaSmoothSubmersionOriginalSourceChartMap
