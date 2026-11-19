import Hironaka.Resolution.HironakaActualLocallyFiniteBoundaryContinuation
import Hironaka.Resolution.HironakaActualLocallyFiniteCarrierTransverse
import Hironaka.Resolution.HironakaActualLocallyFiniteControlledIdeal
import Hironaka.Resolution.HironakaCoherentTransformExtension

/-! Actual carrier and entire indexed boundary geometry through a given
next blowup of the same locally finite history. No scheduler is assumed
to have been internally produced. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualLocallyFiniteTransverseContinuation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings NormalCrossingsInvariance
  HironakaActualLocallyFiniteBoundary HironakaActualLocallyFiniteCarrierTransverse
  HironakaActualLocallyFiniteBoundaryContinuation
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem prefix_get (D : ℕ → Set X) (N : ℕ)
    (i : Fin (List.ofFn (fun j : Fin N=>D j.val)).length) :
    (List.ofFn (fun j : Fin N=>D j.val)).get i=D i.val := by
  simp only [List.get_eq_getElem,List.getElem_ofFn]

theorem isTransverse_finite_prefix (A : Set X) (D : ℕ → Set X)
    (hT : IsTransverseBoundaryFamily n A D) (N : ℕ) :
    IsTransverse n A (List.ofFn (fun i : Fin N=>D i.val)) := by
  intro x hx
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩:=hT x hx
  refine ⟨S₀,fun i=>S i.val,⟨Φ,hsrc,hzero,?_⟩,?_⟩
  · intro o ho z hz hzΦ
    cases o with
    | none => exact hcoord none ho hz hzΦ
    | some i =>
      change z∈(List.ofFn (fun j : Fin N=>D j.val)).get i ↔ _
      change x∈(List.ofFn (fun j : Fin N=>D j.val)).get i at ho
      rw [prefix_get] at ho ⊢
      exact hcoord (some i.val) ho hz hzΦ
  · intro i hi
    rw [prefix_get] at hi
    exact hcard i.val hi

theorem isTransverseBoundaryFamily_continuedBoundary
    (D : ℕ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    {A C : Set X} (hA : IsClosed A) (hT : IsTransverseBoundaryFamily n A D)
    (hCA : C ⊆ A) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hNC : HasNormalCrossingsWithIndexedBoundary C D) :
    IsTransverseBoundaryFamily n (geoStrictTransform π C A) (continuedBoundary D C π) := by
  classical
  intro y hy
  obtain ⟨b,hb⟩:=(hD.1.point_finite (π y)).bddAbove
  let N:=b+1
  have hInc (i : ℕ) (hi : π y∈D i) : i<N:=Nat.lt_succ_of_le (hb hi)
  let E₀:=List.ofFn (fun i : Fin N=>D i.val)
  let E:=E₀.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  have hE : IsTransverse n (geoStrictTransform π C A) E:=
    SimultaneousNormalCrossings.isTransverse_geoTransformE_of_hasNormalCrossings hπ hA hCA
      (isSNCDivisor_finite_prefix D hD N) (isTransverse_finite_prefix A D hT N)
      (hasNormalCrossings_finite_prefix C D hNC N)
  have hLen : E.length=N+1:=by
    simp only [E,E₀,List.length_append,List.length_map,List.length_ofFn,List.length_singleton]
  let last : Fin E.length:=⟨N,by rw [hLen];omega⟩
  let slot : Option ℕ → Fin E.length:=fun o=>
    o.elim last (fun i=>if hi : i<N then ⟨i,by rw [hLen];omega⟩ else last)
  have hGetOld (i : ℕ) (hi : i<N) :
      E.get ⟨i,by rw [hLen];omega⟩=geoStrictTransform π C (D i) := by
    simp only [E,E₀,List.get_eq_getElem,List.getElem_append,List.length_map,List.length_ofFn,
      dif_pos hi,List.getElem_map,List.getElem_ofFn]
  have hGetBorn : E.get last=π ⁻¹' C := by
    change (E₀.map (geoStrictTransform π C) ++ [π ⁻¹' C])[N]'last.isLt=π ⁻¹' C
    exact List.getElem_concat_length (by simp only [List.length_map,E₀,List.length_ofFn]) _
  have hSet (o : Option ℕ) (ho : y∈continuedBoundary D C π o) :
      E.get (slot o)=continuedBoundary D C π o := by
    cases o with
    | none => exact hGetBorn
    | some i =>
      have hi:=hInc i (geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hD.2.1 i) ho)
      simpa only [slot,Option.elim_some,dif_pos hi,continuedBoundary,Option.elim'_some] using hGetOld i hi
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩:=hE y hy
  refine ⟨S₀,fun o=>S (slot o),⟨Φ,hsrc,hzero,?_⟩,?_⟩
  · intro o ho z hz hzΦ
    cases o with
    | none => exact hcoord none ho hz hzΦ
    | some i =>
      have heq:=hSet i ho
      have hyE : y∈E.get (slot i):=heq.symm ▸ ho
      have h:=hcoord (some (slot i)) hyE hz hzΦ
      change z∈continuedBoundary D C π i ↔ _
      rw [←heq]
      exact h
  · intro o ho
    exact hcard (slot o) ((hSet o ho).symm ▸ ho)

open ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteLimitStrictTransforms
  MarkedIdeals.MarkedIdeal
attribute [local instance] limitChartedSpace

theorem actual_limit_carrier_continuation
    (M : MarkedIdeals.MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀j,IsGeoTestTower M (s.stage j).2)
    {Z : CMfd.{u} n} {C : Set (limitManifold s hLF)} {π : Z → limitManifold s hLF}
    (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ limitStrictTransform s hLF M.N)
    (hNC : HasNormalCrossingsWithIndexedBoundary C (limitBoundaryMember M s hLF)) :
    IsProperMap (fun z=>gluedProjection s hLF (π z)) ∧
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z=>gluedProjection s hLF (π z)) ∧
    IsLocallyFiniteSNCDivisor n (continuedBoundary (limitBoundaryMember M s hLF) C π) ∧
    IsClosedSubmanifold n (geoStrictTransform π C (limitStrictTransform s hLF M.N)) ∧
    IsTransverseBoundaryFamily n (geoStrictTransform π C (limitStrictTransform s hLF M.N))
      (continuedBoundary (limitBoundaryMember M s hLF) C π) := by
  let : IsComplexManifold n (HironakaActualLocallyFiniteHistoryOverlap.actualHistoryGluedSpace s hLF) :=
    limitSpace_isComplexManifold s hLF
  obtain ⟨hp,hh,hB⟩:=actual_limit_boundary_continuation M hM s hLF hT hπ hNC
  have hN:=isClosedSubmanifold_limitCarrier M hM s hLF hT
  refine ⟨hp,hh,hB,
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN,?_⟩
  exact isTransverseBoundaryFamily_continuedBoundary (limitBoundaryMember M s hLF)
    (isLocallyFiniteSNCDivisor_limitBoundaryMember M hM s hLF hT) hN.1
    (isTransverseBoundaryFamily_limitCarrier M hM s hLF hT) hCN hπ hNC

open HironakaActualLocallyFiniteControlledIdeal RestrictedIdealQuotient
  GermIdealTotalTransform GermIdealPullbackCalculus IdealWeightPowers

/-- The literal controlled ideal of the next step of this SAME limit
history is coherent. The infinite boundary is retained separately in the
preceding geometric theorem; no finite replacement boundary is introduced. -/
theorem actual_limit_controlled_ideal_continuation
    (M : MarkedIdeals.MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀j,IsGeoTestTower M (s.stage j).2)
    {Z : CMfd.{u} n} {C : Set (limitManifold s hLF)} {π : Z → limitManifold s hLF}
    (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ limitStrictTransform s hLF M.N) :
    (colonAlong n (geoStrictTransform π C (limitStrictTransform s hLF M.N))
      (GermIdeal.pullback (m:=n) π (limitControlledIdeal M s hLF))
      (idealPow (GermIdeal.pullback (m:=n) π (vanishingIdeal (n:=n) C)) M.d)).IsCoherent := by
  let : IsComplexManifold n (HironakaActualLocallyFiniteHistoryOverlap.actualHistoryGluedSpace s hLF) :=
    limitSpace_isComplexManifold s hLF
  have hN:=isClosedSubmanifold_limitCarrier M hM s hLF hT
  have hN':=BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hI:=isCoherent_limitControlledIdeal M
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hM.isClosedSubmanifold_N)
    hM.isCoherent s hLF
  exact HironakaCoherentTransformExtension.isCoherent_colonAlong_without_inclusion
    (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hI)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
    (isCoherent_idealPow (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) M.d)

end
end Hironaka.HironakaActualLocallyFiniteTransverseContinuation
