/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveSuccessorLocalBlowup

/-! Actual local universal lifts agree on genuine test-open intersections;
the whole global blowup universal property is constructed from those lifts. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalSuccessorBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupRestrictOpen HironakaSharpActualCurveSuccessorLocalBlowup
variable {n m : ℕ} {X Y : CMfd.{u} n} {Z : CMfd.{u} m}

def mapPreimageOpen (f : Z → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) (U : Opens X) : Opens Z :=
  ⟨f ⁻¹' (U : Set X),U.isOpen.preimage hf.continuous⟩

def restrictedMap (f : Z → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) (U : Opens X) :
    mapPreimageOpen f hf U → U := fun z => ⟨f z.val,z.property⟩

private theorem actual_restricted_holomorphic (f : Z → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) (U : Opens X) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (restrictedMap f hf U) :=
  contMDiff_opens_mk (hf.comp contMDiff_subtype_val) (fun z => z.property)

private theorem actual_test_invertible (C : Set X) (g : Z → X)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hInv : (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).IsInvertible) (U : Opens X) :
    (GermIdeal.pullback (m := m) (restrictedMap g hg U)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' C))).IsInvertible := by
  rw [pullback_vanishingIdeal_opens (n := n) (m := m) U (restrictedMap g hg U) C]
  exact IsInvertible.pullback_comp_val (mapPreimageOpen g hg U) hInv

private theorem actual_local_lifts_agree (C : Set X) (π : Y → X)
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (U V : Opens X)
    (hU : IsBlowupAlong n ((Subtype.val : U → X) ⁻¹' C) (restrictedMap π hπ U))
    (g : Z → X) (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hInv : (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).IsInvertible)
    (a : mapPreimageOpen g hg U → mapPreimageOpen π hπ U)
    (ha : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ a)
    (haπ : ∀ z,π (a z).val=g z.val)
    (b : mapPreimageOpen g hg V → mapPreimageOpen π hπ V)
    (hb : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (hbπ : ∀ z,π (b z).val=g z.val)
    (z : mapPreimageOpen g hg U) (hzV : g z.val∈V) :
    (a z).val=(b ⟨z.val,hzV⟩).val := by
  let P := mapPreimageOpen g hg U ⊓ mapPreimageOpen g hg V
  let ai : P → Y := fun p => (a ⟨p.val,p.property.1⟩).val
  let bi : P → Y := fun p => (b ⟨p.val,p.property.2⟩).val
  have hai : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ ai :=
    contMDiff_subtype_val.comp (ha.comp (contMDiff_inclusion (U := P) (V := mapPreimageOpen g hg U) inf_le_left))
  have hbi : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ bi :=
    contMDiff_subtype_val.comp (hb.comp (contMDiff_inclusion (U := P) (V := mapPreimageOpen g hg V) inf_le_right))
  have haiU : ∀ p : P,π (ai p)∈U := fun p => by
    change π (a ⟨p.val,p.property.1⟩).val∈U
    rw [haπ]
    exact p.property.1
  have hbiU : ∀ p : P,π (bi p)∈U := fun p => by
    change π (b ⟨p.val,p.property.2⟩).val∈U
    rw [hbπ]
    exact p.property.1
  let a' : P → mapPreimageOpen π hπ U := fun p => ⟨ai p,haiU p⟩
  let b' : P → mapPreimageOpen π hπ U := fun p => ⟨bi p,hbiU p⟩
  let g' : P → U := fun p => ⟨g p.val,p.property.1⟩
  have hg' : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g' :=
    contMDiff_opens_mk (hg.comp contMDiff_subtype_val) (fun (p : P) => p.property.1)
  have hInv' : (GermIdeal.pullback (m := m) g'
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' C))).IsInvertible := by
    rw [pullback_vanishingIdeal_opens (n := n) (m := m) U g' C]
    exact IsInvertible.pullback_comp_val P hInv
  obtain ⟨_,_,hUnique⟩ := hU.2.2.2.2 m P g' hg' hInv'
  have ha' := hUnique a' ⟨contMDiff_opens_mk hai haiU,by
    funext p
    exact Subtype.ext (haπ ⟨p.val,p.property.1⟩)⟩
  have hb' := hUnique b' ⟨contMDiff_opens_mk hbi hbiU,by
    funext p
    exact Subtype.ext (hbπ ⟨p.val,p.property.2⟩)⟩
  exact congrArg Subtype.val (congrFun (ha'.trans hb'.symm) ⟨z.val,⟨z.property,hzV⟩⟩)

theorem exists_unique_lift_of_open_cover {ι : Type u} (C : Set X) (π : Y → X)
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (U : ι → Opens X) (hcover : ∀ x : X,∃ i,x∈U i)
    (hLocal : ∀ i,IsBlowupAlong n ((Subtype.val : U i → X) ⁻¹' C) (restrictedMap π hπ (U i)))
    (g : Z → X) (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hInv : (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).IsInvertible) :
    ∃! h : Z → Y,ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ h ∧ π ∘ h=g := by
  have hExists (i : ι) : ∃! a : mapPreimageOpen g hg (U i) → mapPreimageOpen π hπ (U i),
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ a ∧
        (restrictedMap π hπ (U i)) ∘ a=restrictedMap g hg (U i) :=
    (hLocal i).2.2.2.2 m _ (restrictedMap g hg (U i))
      (actual_restricted_holomorphic g hg (U i)) (actual_test_invertible C g hg hInv (U i))
  choose a ha using fun i => (hExists i).exists
  have haπ (i : ι) (z : mapPreimageOpen g hg (U i)) : π (a i z).val=g z.val :=
    congrArg Subtype.val (congrFun (ha i).2 z)
  let index : Z → ι := fun z => Classical.choose (hcover (g z))
  have hIndex (z : Z) : g z∈U (index z) := Classical.choose_spec (hcover (g z))
  let H : Z → Y := fun z => (a (index z) ⟨z,hIndex z⟩).val
  have hKey (i : ι) (z : mapPreimageOpen g hg (U i)) : H z.val=(a i z).val := by
    exact (actual_local_lifts_agree C π hπ (U i) (U (index z.val)) (hLocal i)
      g hg hInv (a i) (ha i).1 (haπ i) (a (index z.val))
      (ha (index z.val)).1 (haπ (index z.val)) z (hIndex z.val)).symm
  have hH : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ H := by
    intro z
    have hLoc : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞
        (fun w : mapPreimageOpen g hg (U (index z)) => H w.val) := by
      have hEq : (fun w : mapPreimageOpen g hg (U (index z)) => H w.val)=
          fun w => (a (index z) w).val := funext (hKey (index z))
      rw [hEq]
      exact contMDiff_subtype_val.comp (ha (index z)).1
    exact contMDiffAt_subtype_iff.mp (hLoc ⟨z,hIndex z⟩)
  refine ⟨H,⟨hH,funext (fun z => haπ (index z) ⟨z,hIndex z⟩)⟩,?_⟩
  rintro h ⟨hh,hπh⟩
  funext z
  let i := index z
  have hLanding : ∀ w : mapPreimageOpen g hg (U i),π (h w.val)∈U i := fun w => by
    have he : π (h w.val)=g w.val := congrFun hπh w.val
    exact he.symm ▸ w.property
  let b : mapPreimageOpen g hg (U i) → mapPreimageOpen π hπ (U i) :=
    fun w => ⟨h w.val,hLanding w⟩
  have hb : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b :=
    contMDiff_opens_mk (hh.comp contMDiff_subtype_val) hLanding
  have hbπ : restrictedMap π hπ (U i) ∘ b=restrictedMap g hg (U i) := by
    funext w
    exact Subtype.ext (congrFun hπh w.val)
  have hEq : b=a i := (hExists i).unique ⟨hb,hbπ⟩ (ha i)
  exact (congrArg Subtype.val (congrFun hEq ⟨z,hIndex z⟩)).trans (hKey i ⟨z,hIndex z⟩).symm

open HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveLocalRangeBiholomorphism
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGlobalSuccessorMap
  HironakaSharpActualCurveGlobalSuccessorGeometry HironakaSharpActualCurveGlobalSuccessorCentre
  HironakaSharpActualCurveGlobalSuccessorCentreIdeal
attribute [local instance] endpointChartedSpace

private theorem actual_canonical_range_blowup {J : Type u} (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    IsBlowupAlong n
      ((Subtype.val : localRangeOpen (uniformStageHistories A k) hc i →
        endpointManifold (uniformStageHistories A k) hc) ⁻¹' globalUniformCentre A k)
      (restrictedMap (X := endpointManifold (uniformStageHistories A k) hc)
        (Z := endpointManifold (uniformStageHistories A (k+1)) hc)
        (globalUniformSuccessor A k) (globalUniformSuccessor_contMDiff A hc k)
        (localRangeOpen (uniformStageHistories A k) hc i)) := by
  let Y₀ := endpointManifold (uniformStageHistories A k) hc
  let Y₁ := endpointManifold (uniformStageHistories A (k+1)) hc
  let f : Y₁ → Y₀ := globalUniformSuccessor A k
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f :=
    globalUniformSuccessor_contMDiff A hc k
  let U := localRangeOpen (uniformStageHistories A k) hc i
  let V := mapPreimageOpen (X := Y₀) (Z := Y₁) f hf U
  have hOpen : V=localRangeOpen (uniformStageHistories A (k+1)) hc i := by
    apply Opens.ext
    exact globalUniformSuccessor_preimage_range A k i
  let e := BlowupTowerIsoTail.opensCongr (n := n) hOpen
  have hKnown := isBlowupAlong_localRangeUniformSuccessor A hc k i
  have hMoved := isBlowupAlong_comp_diffeomorph (X := CMfd.of (n := n) U) e hKnown
  have hMap : restrictedMap (X := Y₀) (Z := Y₁) f hf U=
      (localRangeUniformSuccessor A hc k i) ∘ e := by
    funext z
    exact Subtype.ext rfl
  exact Eq.mpr (congrArg (IsBlowupAlong n
    ((Subtype.val : U → Y₀) ⁻¹' globalUniformCentre A k)) hMap) hMoved

/-- The SAME global arrow satisfies every clause of the original universal-property blowup. -/
theorem isBlowupAlong_globalUniformSuccessor {J : Type u} (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    IsBlowupAlong n (globalUniformCentre A k : Set (endpointManifold (uniformStageHistories A k) hc))
      (globalUniformSuccessor A k : endpointManifold (uniformStageHistories A (k+1)) hc →
        endpointManifold (uniformStageHistories A k) hc) := by
  refine ⟨isClosedSubmanifold_globalUniformCentre A hc k,interior_globalUniformCentre A k,
    globalUniformSuccessor_contMDiff A hc k,isInvertible_globalSuccessorCentrePullback A hc k,?_⟩
  intro m' Z' _ _ _ g hg hInv
  exact exists_unique_lift_of_open_cover
    (X := endpointManifold (uniformStageHistories A k) hc)
    (Y := endpointManifold (uniformStageHistories A (k+1)) hc) (Z := CMfd.of (n := m') Z')
    (globalUniformCentre A k) (globalUniformSuccessor A k) (globalUniformSuccessor_contMDiff A hc k)
    (localRangeOpen (uniformStageHistories A k) hc)
    (by
      intro q
      obtain ⟨i,z,hz⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A k) q
      exact ⟨i,z,hz⟩)
    (actual_canonical_range_blowup A hc k) g hg hInv

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

theorem isBlowupAlong_originalUniformSuccessor (k : ℕ) :
    IsBlowupAlong n (originalUniformCentre hn hW hE hdense hr k)
      (originalUniformSuccessor hn hW hE hdense hr k) :=
  isBlowupAlong_globalUniformSuccessor (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalSuccessorBlowup
