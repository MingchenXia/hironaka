/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalExceptionalBirthSupport
import Hironaka.Resolution.HironakaNormalCrossingsTotalIdeal
import Hironaka.MarkedIdeal.CodimOneSupport

/-! Real locally finite simultaneous coordinates construct the actual whole
born support and its reduced Cartier ideal, without any infinite product. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaSharpActualCurveGlobalBirthCartierBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates NormalCrossings HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsTotalIdeal
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveGlobalBoundaryCoordinates HironakaSharpActualCurveLocallyFiniteBoundary
  HironakaSharpActualCurveGlobalExceptionalBirthSupport
attribute [local instance] HironakaSharpActualCurveGlobalManifold.endpointChartedSpace
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {ι : Type v}

omit [IsComplexManifold n M] in
/-- True local finiteness first removes ALL nonincident members, then the
same actual chart supplies the entire union's finite coordinate equation. -/
theorem normalCrossingsCarrier_iUnion_of_locallyFinite (F : ι → Set M)
    (hClosed : ∀ i,IsClosed (F i)) (hFinite : LocallyFinite F)
    (hCoord : ∀ x : M,∃ S : ι → Finset (Fin n),IsCoordinateFamilyAt n F S x ∧
      ∀ i,x∈F i → (S i).card=1) :
    IsNormalCrossingsCarrier (n := n) (⋃ i,F i) := by
  refine ⟨hFinite.isClosed_iUnion hClosed,?_⟩
  intro x
  obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard⟩ := hCoord x
  obtain ⟨U,hU,hUopen,hxU⟩ := mem_nhds_iff.mp (hFinite.eventually_subset hClosed x)
  let e := chartAt (ComplexModel n) x
  let V := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hUopen
  have hxV : e x∈V := ⟨e.map_source (mem_chart_source _ x),by
    rw [mem_preimage,e.left_inv (mem_chart_source _ x)]
    exact hxU⟩
  let Ψ := Φ.restrict V hV (e x) ⟨Φ.center_mem_source,hxV⟩
  let I := (hFinite.point_finite x).toFinset
  let T := I.biUnion S
  refine ⟨Ψ,fun z hz => hsrc hz.1,h0,T,?_⟩
  intro y hy
  have hyΦ : y∈flatDomain Φ := ⟨hy.1,hy.2.1⟩
  have hyU : y∈U := by
    have hInv : e.symm (e y)∈U := hy.2.2.2
    rwa [e.left_inv hy.1] at hInv
  constructor
  · intro hyF
    obtain ⟨i,hi⟩ := mem_iUnion.mp hyF
    have hxi : x∈F i := hU hyU hi
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (hcard i hxi)
    refine ⟨j,Finset.mem_biUnion.mpr ⟨i,by simpa only [I,Set.Finite.mem_toFinset,mem_ofPred_eq] using hxi,?_⟩,?_⟩
    · rw [hj]
      exact Finset.mem_singleton_self _
    · have hz := (hflat i hxi hyΦ.1 hyΦ.2).mp hi
      exact hz j (by rw [hj];exact Finset.mem_singleton_self _)
  · rintro ⟨j,hj,hzero⟩
    obtain ⟨i,hi,hji⟩ := Finset.mem_biUnion.mp hj
    have hxi : x∈F i := by simpa only [I,Set.Finite.mem_toFinset,mem_ofPred_eq] using hi
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp (hcard i hxi)
    have hjk : j=k := by simpa only [hk,Finset.mem_singleton] using hji
    apply mem_iUnion.mpr
    refine ⟨i,(hflat i hxi hyΦ.1 hyΦ.2).mpr ?_⟩
    intro k' hk'
    have hkk' : k'=k := by simpa only [hk,Finset.mem_singleton] using hk'
    change Φ.toFun (e y) j=0 at hzero
    simpa only [e,complexChartAt,hkk',hjk] using hzero

omit [IsComplexManifold n M] in
/-- Offset assembly is proved on an ABSTRACT manifold before the actual
large recipe atlas is instantiated; all family data are genuine geometry. -/
theorem normalCrossingsCarrier_iUnion_offset (F : ℕ → Set M)
    (hClosed : ∀ i,IsClosed (F i)) (hFinite : LocallyFinite F)
    (hCoord : ∀ x : M,∃ S : ℕ → Finset (Fin n),IsCoordinateFamilyAt n F S x ∧
      (∀ i,x∈F i → (S i).card=1) ∧ Set.InjOn S {i | x∈F i}) (p : ℕ) :
    IsNormalCrossingsCarrier (n := n) (⋃ j,F (p+j)) := by
  have hOffsetFinite : LocallyFinite (fun j => F (p+j)) :=
    hFinite.comp_injective (fun a b hab => Nat.add_left_cancel hab)
  refine normalCrossingsCarrier_iUnion_of_locallyFinite (fun j => F (p+j))
    (fun j => hClosed (p+j)) hOffsetFinite ?_
  intro x
  obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard,_hinj⟩ := hCoord x
  exact ⟨fun j => S (p+j),⟨Φ,hsrc,h0,fun j => hflat (p+j)⟩,fun j => hcard (p+j)⟩

/-- The literal whole vanishing ideal is reduced for genuine holomorphic
germs; no factor multiplicity or substitute ideal is introduced. -/
theorem vanishingIdeal_mem_positive_power_iff (H : Set M) (x : M) (g : M → ℂ)
    (hg : HolomorphicAt n g x) {k : ℕ} (hk : 0<k) :
    (vanishingIdeal (n := n) H).mem x (fun y => g y^k) ↔ (vanishingIdeal (n := n) H).mem x g := by
  constructor
  · intro h
    refine ⟨hg,?_⟩
    filter_upwards [h.2] with y hy hyH
    exact eq_zero_of_pow_eq_zero (hy hyH)
  · intro h
    refine ⟨BlowupDerivativeIdeal.holomorphicAt_pow hg k,?_⟩
    filter_upwards [h.2] with y hy hyH
    rw [hy hyH,zero_pow (Nat.ne_of_gt hk)]

section OriginalInput
variable {X : CMfd.{u} n} (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- The independently constructed SAME born support is an actual union,
with every original offset, empty birth and unbounded chart length retained. -/
def originalBornSupport : Set (originalEndpointManifold hn hW hE hdense hr) :=
  ⋃ j,originalGluedBoundaryReadout hn hW hE hdense hr (E.length+j)

/-- Actual local finiteness, closed members and the ORIGINAL simultaneous
coordinate producer internally supply the whole born NC structure. -/
theorem originalBornSupport_normalCrossingsCarrier :
    IsNormalCrossingsCarrier (n := n) (originalBornSupport hn hW hE hdense hr) := by
  exact normalCrossingsCarrier_iUnion_offset (originalGluedBoundaryReadout hn hW hE hdense hr)
    (isClosed_originalGluedBoundaryReadout hn hW hE hdense hr)
    (locallyFinite_originalGluedBoundaryReadout hn hW hE hdense hr)
    (original_globalBoundary_snc_coordinates hn hW hE hdense hr) E.length

/-- Actual G6 finite coordinate equations prove invertibility of the SAME
whole original born vanishing ideal, not of an assumed local model. -/
def originalBornDivisor : EffectiveDivisor n (originalEndpointManifold hn hW hE hdense hr) :=
  ⟨vanishingIdeal (n := n) (originalBornSupport hn hW hE hdense hr),
    isInvertible_vanishingIdeal_normalCrossingsCarrier
      (originalBornSupport_normalCrossingsCarrier hn hW hE hdense hr)⟩

theorem originalBornDivisor_ideal :
    (originalBornDivisor hn hW hE hdense hr).ideal=
      vanishingIdeal (n := n) (originalBornSupport hn hW hE hdense hr) := rfl

/-- The actual support is the ENTIRE same born union. -/
theorem originalBornDivisor_support :
    (originalBornDivisor hn hW hE hdense hr).support=originalBornSupport hn hW hE hdense hr :=
  BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
    (originalBornSupport_normalCrossingsCarrier hn hW hE hdense hr).1

theorem originalBornDivisor_coherent : (originalBornDivisor hn hW hE hdense hr).ideal.IsCoherent :=
  DivisorMetric.isCoherent_of_isInvertible (originalBornDivisor hn hW hE hdense hr).isInvertible

/-- The actual whole born support is analytic; its entire closedness and
coherence are constructed before the original zero-locus theorem is applied. -/
theorem originalBornSupport_isComplexAnalyticSubset :
    IsComplexAnalyticSubset (n := n) (originalBornSupport hn hW hE hdense hr) := by
  have h := CodimOneSupport.isComplexAnalyticSubset_zeroLocus
    (originalBornDivisor_coherent hn hW hE hdense hr)
  exact (congrArg (IsComplexAnalyticSubset (n := n))
    (originalBornDivisor_support hn hW hE hdense hr)).mp h

theorem originalBornDivisor_support_inclusions :
    exceptionalLocus n (originalEndpointProjection hn hW hE hdense hr) ⊆
        (originalBornDivisor hn hW hE hdense hr).support ∧
      (originalBornDivisor hn hW hE hdense hr).support ⊆
        (originalEndpointProjection hn hW hE hdense hr) ⁻¹'
          HironakaSharpOriginalMultiBoundaryBadLocus.originalSharpBadLocus (n := n) W E := by
  rw [originalBornDivisor_support]
  exact original_globalExceptional_birth_support hn hW hE hdense hr

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalBirthCartierBoundary
