/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsSNCBlockCarrier

/-!
# Actual old-block high loci lie in original strict high loci

The genuine original member-intersection theorem and exact intrinsic old-block
count give high-locus control under an actual whole joint test tower. Neither
a high-locus comparison nor a desired output support is an input.
Blueprint: `hironaka-normal-crossings-old-block-superlevels-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsOldBlockSuperlevels
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MemberInterTowerAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings BoundaryCount
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsSNCBlockCarrier
  HironakaBoundaryCoefficientBranchHistories
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem count_map_get {α β : Type*} (B : List α) (f : α→β) (P : β→Prop) :
    (Finset.univ.filter (fun i : Fin (B.map f).length=>P ((B.map f).get i))).card=
      (Finset.univ.filter (fun i : Fin B.length=>P (f (B.get i)))).card := by
  let c : Fin (B.map f).length→Fin B.length := Fin.cast (List.length_map f)
  have hg (i : Fin (B.map f).length) : (B.map f).get i=f (B.get (c i)) := by
    simp [c,List.get_eq_getElem]
  apply Finset.card_bij (fun i _=>c i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg i ▸ (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    exact Fin.cast_injective _ he
  · intro j hj
    let i : Fin (B.map f).length := Fin.cast (List.length_map f).symm j
    have hc : c i=j := by simp [i,c]
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hc⟩
    rw [hg,hc]
    exact (Finset.mem_filter.mp hj).2

private theorem current_carrier_univ (M : MarkedIdeal n X) (hN : M.N=univ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),(geoTransformAlong M T).N=univ
  | _,.refl => hN
  | _,.step T _ _ hπ => geoTransform_N_eq_univ (current_carrier_univ M hN T) hπ

/-- Actual testness internally produces the current old carrier and forces
EVERY current old-count superlevel into the original strict superlevel. -/
theorem exists_current_old_carrier_superlevel_control
    (B E : List (Set X)) (hBE : IsSNCDivisor n (B++E))
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,B++E,I,d⟩ : MarkedIdeal n X) T) :
    let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
    ∃ hc : IsBoundaryAdaptedCarrier (n := n) (⋃ A∈B.map (strictAlong T),A) (geoTransformAlong M T).E,
      ∀ q : ℕ,
        {y | q≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} ⊆
          strictAlong T {x | q≤branchMultiplicity
            (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append B E hBE)) x} := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
  let MB : MarkedIdeal n X := ⟨univ,B++E,I,d⟩
  have hMB : MB.IsWellFormed := ⟨isClosedSubmanifold_univ,hI,hBE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hBE⟩
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMB T hT
  have hSNC : IsSNCDivisor n (B.map (strictAlong T)++(geoTransformAlong M T).E) := by
    rw [←entire_old_retained_boundary M B T]
    exact hw.isSNCDivisor
  let hc := boundaryAdapted_union_of_snc_append _ _ hSNC
  refine ⟨hc,?_⟩
  intro q y hy
  let J := Finset.univ.filter (fun i : Fin B.length=>y∈strictAlong T (B.get i))
  let K := Finset.univ.filter (fun i : Fin MB.E.length=>y∈strictAlong T (MB.E.get i))
  have hcount : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y=J.card := by
    exact (branchMultiplicity_union_eq_count _ _ hSNC y).1.trans
      (count_map_get B (strictAlong T) (fun A=>y∈A))
  have hNy : y∈(geoTransformAlong MB T).N := by
    rw [current_carrier_univ MB rfl T]
    exact mem_univ _
  have hyK : y∈strictAlong T (MB.N∩memberInter MB.E K) :=
    mem_strictAlong_inter_memberInter_self MB hMB T hT hNy
  apply strictAlong_mono T (B:= {x | q≤branchMultiplicity
    (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append B E hBE)) x}) ?_ hyK
  intro z hz
  let old (i : Fin B.length) : Fin MB.E.length := ⟨i.val,by
    change i.val<(B++E).length
    rw [List.length_append]
    omega⟩
  have hOld (i : Fin B.length) : MB.E.get (old i)=B.get i := by
    change (B++E).get ⟨i.val,_⟩=B.get i
    simp [List.get_eq_getElem]
  have hsub : J⊆Finset.univ.filter (fun i : Fin B.length=>z∈B.get i) := by
    intro i hi
    have hiK : old i∈K := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      rw [hOld]
      exact (Finset.mem_filter.mp hi).2⟩
    have hzi : z∈MB.E.get (old i) := hz.2 (old i) hiK
    rw [hOld] at hzi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzi⟩
  calc
    q≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y := hy
    _=J.card := hcount
    _≤(Finset.univ.filter (fun i : Fin B.length=>z∈B.get i)).card := Finset.card_le_card hsub
    _=branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append B E hBE)) z :=
      (branchMultiplicity_union_eq_count B E hBE z).1.symm

end
end Hironaka.HironakaNormalCrossingsOldBlockSuperlevels
