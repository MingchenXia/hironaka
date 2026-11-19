import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Invariant.InvDomainCompanion

/-! Actual finite marked sums retain every original row, common carrier
and entire boundary. Their genuine test towers and terminal cosupports
are derived from the controlled-transform restricted equivalence. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualFiniteMarkedSumHistories
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  RestrictedIdealExtension IdealWeightPowers GermIdealPullbackCalculus
variable {n : ℕ} {X Y : CMfd.{u} n}

def finiteSum (A : MarkedIdeal n X) : List (MarkedIdeal n X) → MarkedIdeal n X
  | []=>A
  | B::L=>MarkedIdealOperationsTransform.MarkedIdeal.add A (finiteSum B L)

theorem finiteSum_mark_one (A : MarkedIdeal n X) (L : List (MarkedIdeal n X))
    (hd : A.d=1) (hL : ∀B∈L,B.d=1) : (finiteSum A L).d=1 := by
  induction L generalizing A with
  | nil => exact hd
  | cons B L ih =>
    change A.d*(finiteSum B L).d=1
    rw [hd,ih B (hL B (by simp)) (fun C hC=>hL C (List.mem_cons_of_mem B hC)),one_mul]

private theorem tail_data {A B : MarkedIdeal n X} {L : List (MarkedIdeal n X)}
    (h : ∀C∈B::L,C.N=A.N ∧ C.E=A.E ∧ C.ideal.IsCoherent ∧ 1≤C.d) :
    ∀C∈L,C.N=B.N ∧ C.E=B.E ∧ C.ideal.IsCoherent ∧ 1≤C.d := by
  intro C hC
  have hB:=h B (by simp)
  have hC':=h C (by simp only [List.mem_cons];exact Or.inr hC)
  exact ⟨hC'.1.trans hB.1.symm,hC'.2.1.trans hB.2.1.symm,hC'.2.2⟩

theorem finiteSum_geometry (A : MarkedIdeal n X) (L : List (MarkedIdeal n X))
    (hA : A.ideal.IsCoherent) (hd : 1≤A.d)
    (hL : ∀B∈L,B.N=A.N ∧ B.E=A.E ∧ B.ideal.IsCoherent ∧ 1≤B.d) :
    (finiteSum A L).N=A.N ∧ (finiteSum A L).E=A.E ∧
      (finiteSum A L).ideal.IsCoherent ∧ 1≤(finiteSum A L).d := by
  induction L generalizing A with
  | nil => exact ⟨rfl,rfl,hA,hd⟩
  | cons B L ih =>
    have hB:=hL B (by simp)
    obtain ⟨_hN,_hE,hCo,hPos⟩:=ih B hB.2.2.1 hB.2.2.2 (tail_data hL)
    exact ⟨rfl,rfl,isCoherent_sumIdeal (isCoherent_idealPow hA _)
      (isCoherent_idealPow hCo _),Nat.mul_pos (by omega) (by omega)⟩

theorem finiteSum_history (A : MarkedIdeal n X) (L : List (MarkedIdeal n X))
    (hN : IsClosedSubmanifold n A.N) (hA : A.ideal.IsCoherent) (hd : 1≤A.d)
    (hL : ∀B∈L,B.N=A.N ∧ B.E=A.E ∧ B.ideal.IsCoherent ∧ 1≤B.d)
    (T : BlowupTower X Y) :
    (IsGeoTestTower (finiteSum A L) T ↔ ∀B∈A::L,IsGeoTestTower B T) ∧
    (IsGeoTestTower (finiteSum A L) T →
      (geoTransformAlong (finiteSum A L) T).cosupp=
        {y | ∀B∈A::L,y∈(geoTransformAlong B T).cosupp} ∧
      (geoTransformAlong (finiteSum A L) T).ideal.IsCoherent) := by
  induction L generalizing A with
  | nil =>
    refine ⟨?_,?_⟩
    · simp only [finiteSum,List.mem_singleton,forall_eq]
    · intro hT
      refine ⟨?_,?_⟩
      · ext y
        simp only [finiteSum,List.mem_singleton,forall_eq,Set.mem_ofPred_eq]
      · exact (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hA T hT).2
  | cons B L ih =>
    have hB:=hL B (by simp)
    have hBN : IsClosedSubmanifold n B.N:=hB.1.symm ▸ hN
    have hRest:=ih B hBN hB.2.2.1 hB.2.2.2 (tail_data hL)
    obtain ⟨hSumN,hSumE,hSumCo,hSumPos⟩:=finiteSum_geometry B L hB.2.2.1 hB.2.2.2 (tail_data hL)
    have hPair : IsSubmanifoldPair A (finiteSum B L):=
      ⟨(hSumN.trans hB.1).symm,(hSumE.trans hB.2.1).symm,hN,hA,hSumCo⟩
    obtain ⟨hTests,hTrans⟩:=geoTransformAlong_add_along A (finiteSum B L) hPair hd hSumPos T
    have hAll : IsGeoTestTower (finiteSum A (B::L)) T ↔ ∀C∈A::B::L,IsGeoTestTower C T := by
      change IsGeoTestTower (MarkedIdealOperationsTransform.MarkedIdeal.add A (finiteSum B L)) T ↔ _
      rw [hTests,hRest.1]
      constructor
      · rintro ⟨hTA,hTail⟩ C hC
        rcases List.mem_cons.mp hC with rfl|hC
        · exact hTA
        · exact hTail C hC
      · intro h
        exact ⟨h A (by simp),fun C hC=>h C (List.mem_cons_of_mem A hC)⟩
    refine ⟨hAll,?_⟩
    intro hT
    obtain ⟨hTA,hTail⟩:=hTests.mp hT
    obtain ⟨hEq,hCurrentPair,hCo⟩:=hTrans hTA hTail
    obtain ⟨hTailCos,_hTailCo⟩:=hRest.2 hTail
    have hHeadPos : 1≤(geoTransformAlong A T).d:=by rw [d_geoTransformAlong];exact hd
    have hTailPos : 1≤(geoTransformAlong (finiteSum B L) T).d:=by
      rw [d_geoTransformAlong];exact hSumPos
    refine ⟨?_,hCo⟩
    change (geoTransformAlong (MarkedIdealOperationsTransform.MarkedIdeal.add A (finiteSum B L)) T).cosupp=_
    rw [hEq.cosupp_eq,cosupp_add_along hCurrentPair hHeadPos hTailPos,hTailCos]
    ext y
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,List.mem_cons,forall_eq_or_imp]

theorem isGeoResolution_finiteSum_iff (A : MarkedIdeal n X) (L : List (MarkedIdeal n X))
    (hN : IsClosedSubmanifold n A.N) (hA : A.ideal.IsCoherent) (hd : 1≤A.d)
    (hL : ∀B∈L,B.N=A.N ∧ B.E=A.E ∧ B.ideal.IsCoherent ∧ 1≤B.d)
    (T : BlowupTower X Y) :
    IsGeoResolution (finiteSum A L) T ↔ (∀B∈A::L,IsGeoTestTower B T) ∧
      {y | ∀B∈A::L,y∈(geoTransformAlong B T).cosupp}=(∅ : Set Y) := by
  obtain ⟨hTests,hCos⟩:=finiteSum_history A L hN hA hd hL T
  constructor
  · rintro ⟨hT,hEmpty⟩
    exact ⟨hTests.mp hT,(hCos hT).1.symm.trans hEmpty⟩
  · rintro ⟨hAll,hEmpty⟩
    have hT:=hTests.mpr hAll
    exact ⟨hT,(hCos hT).1.trans hEmpty⟩

open DivisorExponentAlong

theorem finiteSum_nonzero (A : MarkedIdeal n X) (L : List (MarkedIdeal n X))
    (hA : A.ideal.IsCoherent) (hnz : ∀x∈A.N,IsNonzeroAlongAt A.N A.ideal x) :
    ∀x∈(finiteSum A L).N,
      IsNonzeroAlongAt (finiteSum A L).N (finiteSum A L).ideal x := by
  cases L with
  | nil => exact hnz
  | cons B L =>
    intro x hx
    exact InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left
      (fun _ _ hg=>GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
      (InvDomainCompanion.isNonzeroAlongAt_idealPow
        (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA hg)
        (hnz x hx) (finiteSum B L).d)

theorem finiteSum_isInvDomain {q : ℕ} (A : MarkedIdeal n X) (L : List (MarkedIdeal n X))
    (hA : ResolutionInvariantSpec.IsInvDomain q A)
    (hL : ∀B∈L,B.N=A.N ∧ B.E=A.E ∧ B.ideal.IsCoherent ∧ 1≤B.d) :
    ResolutionInvariantSpec.IsInvDomain q (finiteSum A L) := by
  obtain ⟨hN,hE,hCo,hPos⟩:=finiteSum_geometry A L hA.isWellFormed.isCoherent hA.one_le_d hL
  refine ⟨⟨?_,hCo,?_,?_⟩,?_,hPos,
    finiteSum_nonzero A L hA.isWellFormed.isCoherent hA.isNonzeroAlongAt⟩
  · rw [hN];exact hA.isWellFormed.isClosedSubmanifold_N
  · rw [hE];exact hA.isWellFormed.isSNCDivisor
  · rw [hN,hE];exact hA.isWellFormed.isTransverse
  · rw [hN];exact hA.dimLE

end
end Hironaka.HironakaActualFiniteMarkedSumHistories
