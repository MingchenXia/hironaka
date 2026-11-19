import Hironaka.Resolution.HironakaG4PreparedMixedSelectedStep
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Resolution.HironakaG4PreparedResidualPreservation

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG3PreparedMixedGivenBlowup

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  BoundaryCount MemberInterAlong MonomialPart MonomialPartAlong
  BlowupStrictSubmanifold HironakaG4CommonMonomialChart
  HironakaG4PreparedCentreCoordinates HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact
  HironakaG4MonomialCoefficientDeletion DivisorExponentAlong GermIdealOrder
  RestrictedIdealExtension MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong

variable {n : ℕ} {X : CMfd.{u} n}


open RelativePrincipalizationSpan InvertibleIdealQuotient BlowupBiholomorphismLift
  MarkedIdealTowerTransport MonomialPartEtale DerivativeIdealAlongEtale
  BlowupRestrictOpen NormalCrossingsInvariance BlowupSNCTransform MonomialCaseAlong

theorem exists_prepared_mixed_window_for_any_blowup (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (hOrd : ∀ y ∈ N, ∀ i, ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hPrepared : ∀ y ∈ N, IsPreparedResidualSNCAt N old born y)
    {x : X} (hxN : x ∈ N)
    (hActive : (properRows (fun (i : Fin old.length) (j : Fin born.length) =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)).Nonempty)
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hSJ : S ⊆ Finset.univ.filter (fun j => x ∈ born.get j))
    (hFeasible : ∀ i ∈ properRows
      (fun (i : Fin old.length) (j : Fin born.length) =>
        divExpAlong n N (oldMonomialPart N old born i) (born.get j) x),
      1 ≤ ∑ j ∈ S, divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) :
    let A := fun (i : Fin old.length) (j : Fin born.length) =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
    ∃ (U : Opens X) (hxU : x ∈ U),
      let NU := (Subtype.val : U → X) ⁻¹' N
      let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
      let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
      let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
      let SU := S.map e
      let CU := NU ∩ memberInter bornU SU
      let IU : Fin old.length → GermIdeal n U := fun i => restrictOn n NU
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
      let DU := fun i => monomialPartAlong n NU (IU i) bornU
      let JU := fun i => nonmonomialPartAlong n NU (IU i) bornU
      let AU := fun (i : Fin old.length) (j : Fin bornU.length) =>
        divExpAlong n NU (DU i) (bornU.get j) (⟨x, hxU⟩ : U)
      let d := fun i => if i ∈ properRows A then 1 else 0
      let MI := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (IU i) (d i)
      let MD := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (DU i) (d i)
      ∀ (Y : CMfd.{u} n) (π : Y → U), IsBlowupAlong n CU π →
        let N' := geoStrictTransform π CU NU
        let old' := oldU.map (geoStrictTransform π CU)
        let born' := bornU.map (geoStrictTransform π CU) ++ [π ⁻¹' CU]
        let I' := fun i => restrictOn n N' (vanishingIdeal (n := n)
          (geoStrictTransform π CU ((Subtype.val : U → X) ⁻¹' old.get i)))
        let D' := fun i => monomialPartAlong n N' (I' i) born'
        let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
        let G := fun i => ((MD i).geoTransform CU π).ideal
        let T := fun i => (nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y) NU (JU i) CU π).ideal
        CU = (Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S) ∧
        (⟨x, hxU⟩ : U) ∈ CU ∧ IsClosedSubmanifold n CU ∧ interior CU = ∅ ∧
        HasNormalCrossings n CU (oldU ++ bornU) ∧
        CU ⊆ originalSharpBadLocus (n := n) NU (oldU ++ bornU) ∧
        (∀ y ∈ NU, ∀ i, ordinaryTraceOrder NU (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) y ≤ 1) ∧
        (∀ y ∈ NU, IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) NU oldU bornU y) ∧
        IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old' ++ born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born', H) ∧
        (∀ z ∈ N', ∀ i, ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
        (∀ z ∈ N', IsPreparedResidualSNCAt N' old' born' z) ∧
        (∀ i j, AU i (e j) = A i j) ∧
        (∀ i,
          (i ∈ properRows A → CU ⊆ (Subtype.val : U → X) ⁻¹' old.get i) ∧
          (i ∉ properRows A → (∀ y : U, (DU i).mem y (fun _ => (1 : ℂ))) ∧
            IsTransverse n CU [((Subtype.val : U → X) ⁻¹' old.get i)]) ∧
          (MI i).IsAdmissibleCentre CU ∧ (MD i).IsAdmissibleCentre CU ∧
          ((MI i).geoTransform CU π).ideal = I' i ∧ D' i = G i ∧ J' i = T i ∧
          I' i = restrictOn n N' ((D' i).mul (J' i)) ∧
          (I' i).IsCoherent ∧ (∀ z ∈ N', IsNonzeroAlongAt N' (I' i) z) ∧
          (D' i).IsCoherent ∧ (∀ z ∈ N', IsNonzeroAlongAt N' (D' i) z) ∧
          IsMonomialAlong n N' (D' i) born' ∧
          (J' i).IsCoherent ∧ (∀ z ∈ N', IsNonzeroAlongAt N' (J' i) z) ∧
          monomialPartAlong n N' (J' i) born' = IdealWeightPowers.unitIdeal n Y) ∧
        (∀ z ∈ N', π z = (⟨x, hxU⟩ : U) →
          let R := Finset.univ.filter (fun j => z ∈ geoStrictTransform π CU (bornU.get j))
          R ⊆ Finset.univ.filter (fun j => (⟨x, hxU⟩ : U) ∈ bornU.get j) ∧
          (∃ p, p ∈ SU ∧ p ∉ R) ∧
          ∀ i (j : Fin born'.length),
            divExpAlong n N' (D' i) (born'.get j) z =
              transformMarkedRows d SU R AU i (Fin.cast (by simp [born']) j) ∧
            divExpAlong n N' (D' i) (born'.get j) z =
              transformFamily 1 SU R AU i (Fin.cast (by simp [born']) j)) ∧
        ∀ z ∈ N', π z ∉ CU → ∀ i (j : Fin born'.length),
          divExpAlong n N' (D' i) (born'.get j) z =
            appendAbsentRow (fun k => divExpAlong n NU (DU i) (bornU.get k) (π z))
              (Fin.cast (by simp [born']) j)
 := by
  obtain ⟨U,hxU,Y0,π0,hπ0,hCeq,hxC,hCU,hThin,hCFull,hSharp,hOrdU,hPreparedU,
      hN0,hFull0,hTr0,hDense0,hAU,hRows0,hMatrix0,hOff0⟩ :=
    HironakaG4PreparedMixedSelectedStep.exists_prepared_mixed_selected_strict_trace_step
      hn hN hE hTr hdense hOrd hPrepared hxN hActive S hS hSJ hFeasible
  let A := fun (i : Fin old.length) (j : Fin born.length) =>
    divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
  let eO : Fin old.length ↪ Fin oldU.length := (finCongr (by simp [oldU])).toEmbedding
  let SU := S.map e
  let CU := NU ∩ memberInter bornU SU
  let IU := fun i : Fin old.length => restrictOn n NU
    (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
  let DU := fun i => monomialPartAlong n NU (IU i) bornU
  let JU := fun i => nonmonomialPartAlong n NU (IU i) bornU
  let AU := fun (i : Fin old.length) (j : Fin bornU.length) =>
    divExpAlong n NU (DU i) (bornU.get j) (⟨x,hxU⟩ : U)
  let d := fun i => if i ∈ properRows A then 1 else 0
  let MI := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (IU i) (d i)
  let MD := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (DU i) (d i)
  let N0 := geoStrictTransform π0 CU NU
  let old0 := oldU.map (geoStrictTransform π0 CU)
  let born0 := bornU.map (geoStrictTransform π0 CU) ++ [π0 ⁻¹' CU]
  let I0 := fun i : Fin old.length => restrictOn n N0 (vanishingIdeal (n := n)
    (geoStrictTransform π0 CU ((Subtype.val : U → X) ⁻¹' old.get i)))
  let D0 := fun i => monomialPartAlong n N0 (I0 i) born0
  let J0 := fun i => nonmonomialPartAlong n N0 (I0 i) born0
  have hCoh0 (i : Fin old.length) : (I0 i).IsCoherent ∧ (D0 i).IsCoherent ∧ (J0 i).IsCoherent := by
    obtain ⟨_,_,_,_,_,_,_,_,hI,_,hD,_,_,hJ,_,_⟩ := hRows0 i
    exact ⟨hI,hD,hJ⟩
  have hDict0 (i : Fin old.length) :
      ((MI i).geoTransform CU π0).ideal=I0 i ∧
      D0 i=((MD i).geoTransform CU π0).ideal ∧
      J0 i=(nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y0) NU (JU i) CU π0).ideal := by
    obtain ⟨_,_,_,_,hI,hD,hJ,_,_,_,_,_,_,_,_,_⟩ := hRows0 i
    exact ⟨hI,hD,hJ⟩
  have hMPJ0 (i : Fin old.length) : monomialPartAlong n N0 (J0 i) born0=IdealWeightPowers.unitIdeal n Y0 := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h⟩ := hRows0 i
    exact h
  have hNU := isClosedSubmanifold_preimage_val hN U
  have hFullU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ oldU ++ bornU,H) := by
    intro q hq
    have hp : q ∈ (Subtype.val : U → X) ⁻¹' closure (N \ ⋃ H ∈ old ++ born,H) := hdense hq
    erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (N \ ⋃ H ∈ old ++ born,H)] at hp
    have hList : oldU ++ bornU = (old ++ born).map ((Subtype.val : U → X) ⁻¹' ·) :=
      List.map_append.symm
    have hSet : NU \ ⋃ H ∈ oldU ++ bornU,H =
        (Subtype.val : U → X) ⁻¹' (N \ ⋃ H ∈ old ++ born,H) := by
      ext z
      simp only [hList,Set.mem_sdiff,Set.mem_iUnion,Set.mem_preimage]
      constructor
      · rintro ⟨hzN,hz⟩
        refine ⟨hzN,?_⟩
        rintro ⟨H,hm,hzH⟩
        exact hz ⟨_,List.mem_map.mpr ⟨H,hm,rfl⟩,hzH⟩
      · rintro ⟨hzN,hz⟩
        refine ⟨hzN,?_⟩
        rintro ⟨H,hm,hzH⟩
        obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hm
        exact hz ⟨H,hH,hzH⟩
    rw [hSet]
    exact hp
  have hOldGet (i : Fin old.length) : oldU.get (eO i)=(Subtype.val : U → X) ⁻¹' old.get i := by
    simp [oldU,eO]
  have hPartU (i : Fin old.length) := actual_old_parts_geometry (X := CMfd.of (n := n) U)
    (N := NU) hn hNU hFullU hTrU hDenseU (eO i)
  have hcIU (i : Fin old.length) : (IU i).IsCoherent := by
    simpa only [oldTraceIdeal,hOldGet] using (hPartU i).1
  have hcDU (i : Fin old.length) : (DU i).IsCoherent := by
    simpa only [oldMonomialPart,oldTraceIdeal,hOldGet] using (hPartU i).2.2.2.2.1
  have hcJU (i : Fin old.length) : (JU i).IsCoherent := by
    simpa only [oldResidualPart,oldTraceIdeal,hOldGet] using (hPartU i).2.2.1
  refine ⟨U,hxU,?_⟩
  dsimp only
  intro Y π hπ
  let N' := geoStrictTransform π CU NU
  let old' := oldU.map (geoStrictTransform π CU)
  let born' := bornU.map (geoStrictTransform π CU) ++ [π ⁻¹' CU]
  let I' := fun i : Fin old.length => restrictOn n N' (vanishingIdeal (n := n)
    (geoStrictTransform π CU ((Subtype.val : U → X) ⁻¹' old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
  let G := fun i => ((MD i).geoTransform CU π).ideal
  let T := fun i => (nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y) NU (JU i) CU π).ideal
  obtain ⟨a,b,ha,hb,hπa,_hπb,hba,hab⟩ := BlowupUniqueness.exists_biholomorphism_over hπ hπ0
  let χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y0 :=
    ⟨⟨a,b,congrFun hba,congrFun hab⟩,ha,hb⟩
  have hComp : π0 ∘ χ=π := hπa
  have hPoint (z : Y) : π0 (χ z)=π z := congrFun hComp z
  have hStrict (H : Set U) : geoStrictTransform π CU H=χ ⁻¹' geoStrictTransform π0 CU H := by
    rw [←hComp]
    exact geoStrictTransform_comp_diffeo χ π0 CU H
  have hN : N'=χ ⁻¹' N0 := hStrict NU
  have hOld : old'=old0.map (χ ⁻¹' ·) := by
    simp only [old',old0,List.map_map]
    exact List.map_congr_left fun H _ => hStrict H
  have hBorn : born'=born0.map (χ ⁻¹' ·) := by
    simp only [born',born0,List.map_append,List.map_map,List.map_cons,List.map_nil]
    congr 1
    · exact List.map_congr_left fun H _ => hStrict H
    · congr 1
      ext z
      change π z ∈ CU ↔ π0 (χ z) ∈ CU
      rw [hPoint]
  have hFullList : old' ++ born'=(old0 ++ born0).map (χ ⁻¹' ·) := by
    rw [hOld,hBorn]
    exact List.map_append.symm
  have hN' : IsClosedSubmanifold n N' := by
    rw [hN]
    exact (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff χ).mpr hN0
  have hFull' : IsSNCDivisor n (old' ++ born') := by
    rw [hFullList]
    exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff χ).mpr hFull0
  have hTr' : IsTransverse n N' born' := by
    rw [hN,hBorn]
    exact (MarkedIdealTowerTransport.isTransverse_preimage_iff χ).mpr hTr0
  have hDense' : N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born',H) := by
    intro z hz
    have hz0 : χ z ∈ N0 := by
      change z ∈ χ ⁻¹' N0
      rw [←hN]
      exact hz
    have hp : z ∈ χ.toHomeomorph ⁻¹' closure (N0 \ ⋃ H ∈ old0 ++ born0,H) := hDense0 hz0
    rw [χ.toHomeomorph.preimage_closure] at hp
    have hUnion : (⋃ H ∈ old' ++ born',H)=χ ⁻¹' (⋃ H ∈ old0 ++ born0,H) := by
      rw [hFullList]
      ext q
      simp only [Set.mem_iUnion,Set.mem_preimage]
      constructor
      · rintro ⟨H,hm,hqH⟩
        obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hm
        exact ⟨H,hH,hqH⟩
      · rintro ⟨H,hm,hqH⟩
        exact ⟨_,List.mem_map.mpr ⟨H,hm,rfl⟩,hqH⟩
    rw [hN,hUnion,←Set.preimage_sdiff]
    exact hp
  have hloc : ∀ z : Y,∃ ψ : Y0 → Y,IsLocalInverseAt n (χ : Y → Y0) ψ z := by
    intro z
    exact ⟨χ.symm,isLocalInverseAt_of_inverse
      (fun q => (χ.contMDiff q).mdifferentiableAt (by simp))
      (fun q => (χ.symm.contMDiff q).mdifferentiableAt (by simp))
      χ.apply_symm_apply χ.symm_apply_apply z⟩
  have hI (i : Fin old.length) : I' i=GermIdeal.pullback (m := n) χ (I0 i) := by
    let H0 := geoStrictTransform π0 CU ((Subtype.val : U → X) ⁻¹' old.get i)
    have hOld0 : IsSNCDivisor n old0 := isSNCDivisor_of_sublist hFull0 (List.sublist_append_left old0 born0)
    have hMem : H0 ∈ old0 := by
      refine List.mem_map.mpr ⟨(Subtype.val : U → X) ⁻¹' old.get i,?_,rfl⟩
      exact List.mem_map.mpr ⟨old.get i,List.get_mem old i,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hMem
    have hH0 : IsClosedSubmanifold n H0 := by
      simpa only [hj] using MonomialPart.isClosedSubmanifold_get hn hOld0 j
    have hcH0 := VanishingIdealCoherent.isCoherent_vanishingIdeal hH0
    have hPreH0 := MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
      χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply hH0
    have hVanish : GermIdeal.pullback (m := n) χ (vanishingIdeal (n := n) H0)=
        vanishingIdeal (n := n) (χ ⁻¹' H0) := by
      have h := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
        (φ := (χ : Y → Y0)) (ψ := (χ.symm : Y0 → Y))
        χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply
        (g := (id : Y → Y)) contMDiff_id H0
      rw [BlowupControlledTransform.pullback_id
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hPreH0),Function.comp_id] at h
      exact h.symm
    change restrictOn n N' (vanishingIdeal (n := n)
      (geoStrictTransform π CU ((Subtype.val : U → X) ⁻¹' old.get i))) = _
    rw [hN,hStrict,←hVanish]
    ext z g
    rw [mem_restrictOn_pullback_diffeo_iff χ hcH0,
      mem_pullback_diffeo_iff χ (hCoh0 i).1]
  have hD (i : Fin old.length) : D' i=GermIdeal.pullback (m := n) χ (D0 i) := by
    have h := pullback_monomialPartAlong (N := N0) (E := born0) hloc
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hCoh0 i).1 hg)
    change GermIdeal.pullback (m := n) χ (D0 i)=
      monomialPartAlong n (χ ⁻¹' N0) (GermIdeal.pullback (m := n) χ (I0 i))
        (born0.map (χ ⁻¹' ·)) at h
    rw [←hN,←hI i,←hBorn] at h
    exact h.symm
  have hJ (i : Fin old.length) : J' i=GermIdeal.pullback (m := n) χ (J0 i) := by
    have h := pullback_nonmonomialPartAlong hloc (hCoh0 i).1 (hCoh0 i).2.1 (hCoh0 i).2.2
    change GermIdeal.pullback (m := n) χ (J0 i)=
      nonmonomialPartAlong n (χ ⁻¹' N0) (GermIdeal.pullback (m := n) χ (I0 i))
        (born0.map (χ ⁻¹' ·)) at h
    rw [←hN,←hI i,←hBorn] at h
    exact h.symm
  have hcCU := VanishingIdealCoherent.isCoherent_vanishingIdeal hCU
  have hDict (i : Fin old.length) : ((MI i).geoTransform CU π).ideal=I' i := by
    have hc : ((MI i).geoTransform CU π0).ideal.IsCoherent := by rw [(hDict0 i).1]; exact (hCoh0 i).1
    have h := congrArg MarkedIdeal.ideal
      (geoTransform_comp_diffeo χ (MI i) (hcIU i) CU hcCU hπ0.contMDiff hc)
    rw [hComp] at h
    change ((MI i).geoTransform CU π).ideal=GermIdeal.pullback (m := n) χ
      ((MI i).geoTransform CU π0).ideal at h
    rw [(hDict0 i).1] at h
    exact h.trans (hI i).symm
  have hDG (i : Fin old.length) : D' i=G i := by
    have hc : ((MD i).geoTransform CU π0).ideal.IsCoherent := by rw [←(hDict0 i).2.1]; exact (hCoh0 i).2.1
    have h := congrArg MarkedIdeal.ideal
      (geoTransform_comp_diffeo χ (MD i) (hcDU i) CU hcCU hπ0.contMDiff hc)
    rw [hComp] at h
    change G i=GermIdeal.pullback (m := n) χ ((MD i).geoTransform CU π0).ideal at h
    rw [←(hDict0 i).2.1] at h
    exact (hD i).trans h.symm
  have hJT (i : Fin old.length) : J' i=T i := by
    let M := markedRow (X := CMfd.of (n := n) U) NU [] (JU i) 0
    have hc : (M.geoTransform CU π0).ideal.IsCoherent := by
      change (nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y0) NU (JU i) CU π0).ideal.IsCoherent
      rw [←(hDict0 i).2.2]
      exact (hCoh0 i).2.2
    have h := congrArg MarkedIdeal.ideal
      (geoTransform_comp_diffeo χ M (hcJU i) CU hcCU hπ0.contMDiff hc)
    rw [hComp] at h
    change T i=GermIdeal.pullback (m := n) χ
      (nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y0) NU (JU i) CU π0).ideal at h
    rw [←(hDict0 i).2.2] at h
    exact (hJ i).trans h.symm
  have hMPJ (i : Fin old.length) : monomialPartAlong n N' (J' i) born'=IdealWeightPowers.unitIdeal n Y := by
    have h := pullback_monomialPartAlong (N := N0) (E := born0) hloc
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hCoh0 i).2.2 hg)
    change GermIdeal.pullback (m := n) χ (monomialPartAlong n N0 (J0 i) born0)=
      monomialPartAlong n (χ ⁻¹' N0) (GermIdeal.pullback (m := n) χ (J0 i))
        (born0.map (χ ⁻¹' ·)) at h
    rw [hMPJ0 i,BlowupExceptionalDivisor.pullback_unitIdeal,←hN,←hJ i,←hBorn] at h
    exact h.symm
  let eO' : Fin old.length ↪ Fin old'.length := (finCongr (by simp [old',oldU])).toEmbedding
  have hOldGet' (i : Fin old.length) : old'.get (eO' i)=
      geoStrictTransform π CU ((Subtype.val : U → X) ⁻¹' old.get i) := by
    simp [old',oldU,eO']
  have hPart' (i : Fin old.length) := actual_old_parts_geometry hn hN' hFull' hTr' hDense' (eO' i)
  have hSU : SU.Nonempty := by
    obtain ⟨j,hj⟩ := hS
    exact ⟨e j,Finset.mem_map.mpr ⟨j,hj,rfl⟩⟩
  have hNext := HironakaG4PreparedResidualPreservation.actual_selected_born_total_prepared
    (X := CMfd.of (n := n) U) (Y := Y) hn hNU hFullU hTrU hDenseU SU hSU hOrdU hPreparedU π hπ
  let TT : Fin oldU.length → GermIdeal n Y := fun i =>
    (nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y) NU
      (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) CU π).ideal
  let cO : Fin old'.length → Fin oldU.length := Fin.cast (by simp [old'])
  have hCanonJT (i : Fin old'.length) : oldResidualPart N' old' born' i=TT (cO i) := by
    let j : Fin old.length := Fin.cast (by simp [oldU]) (cO i)
    simpa only [J',I',T,JU,IU,TT,oldResidualPart,oldTraceIdeal,old',oldU,
      List.get_eq_getElem,List.getElem_map,cO,j,Fin.val_cast] using hJT j
  have hNextOrd : ∀ z ∈ N',∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1 := by
    intro z hz i
    rw [hCanonJT]
    exact (hNext z hz).1 (cO i)
  have hNextPrepared : ∀ z ∈ N',IsPreparedResidualSNCAt N' old' born' z := by
    intro z hz
    obtain ⟨_hOrdT,Q,p,hFam,hFree,hInj⟩ := hNext z hz
    let ZT : Fin oldU.length ⊕ Fin born'.length → Set Y :=
      Sum.elim (fun i => N' ∩ (TT i).zeroLocus) (fun j => N' ∩ born'.get j)
    let c : Fin old'.length ⊕ Fin born'.length → Fin oldU.length ⊕ Fin born'.length := Sum.map cO id
    have hSupport (a : Fin old'.length ⊕ Fin born'.length) :
        preparedSupport N' old' born' a=ZT (c a) := by
      cases a with
      | inl i => simp only [preparedSupport,ZT,c,Sum.map_inl,Sum.elim_inl,hCanonJT]
      | inr i => rfl
    have hcInj : Function.Injective c := by
      intro a b hab
      cases a with
      | inl i =>
        cases b with
        | inl j =>
          have hij : cO i=cO j := Sum.inl.inj hab
          have hval := congrArg (fun q : Fin oldU.length => q.val) hij
          have hij' : i=j := Fin.ext (by simpa only [cO,Fin.val_cast] using hval)
          exact congrArg Sum.inl hij'
        | inr j => cases hab
      | inr i =>
        cases b with
        | inl j => cases hab
        | inr j => exact congrArg Sum.inr (Sum.inr.inj hab)
    change ∀ a,z ∈ ZT a → p a ∉ Q at hFree
    change Set.InjOn p {a | z ∈ ZT a} at hInj
    refine ⟨Q,p ∘ c,?_,?_,?_⟩
    · apply IsCoordinateFamilyAt.reindex hFam (Option.map c)
      · rintro (_ | a)
        · rfl
        · exact hSupport a
      · rintro (_ | a) <;> rfl
    · intro a ha
      apply hFree (c a)
      rw [←hSupport]
      exact ha
    · intro a ha b hb hab
      apply hcInj
      apply hInj
      · change z ∈ ZT (c a)
        rw [←hSupport]
        exact ha
      · change z ∈ ZT (c b)
        rw [←hSupport]
        exact hb
      · exact hab
  have hExp (i : Fin old.length) (z : Y) (k : ℕ) :
      expDataAlong n N' (D' i) born' z k=expDataAlong n N0 (D0 i) born0 (χ z) k := by
    rw [hN,hD,hBorn]
    exact MonomialInvariantFunctorialAlong.expDataAlong_pullback
      (fun q => cosupport_pullback_of_local hloc
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hCoh0 i).2.1 hg) N0 q)
      (map_nhds_eq_of_local (Classical.choose_spec (hloc z))) born0 k
  have hLen : born'.length=born0.length := by simp [born',born0]
  have hR (z : Y) :
      (Finset.univ.filter fun j => z ∈ geoStrictTransform π CU (bornU.get j))=
      (Finset.univ.filter fun j => χ z ∈ geoStrictTransform π0 CU (bornU.get j)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hStrict,mem_preimage]
  refine ⟨hCeq,hxC,hCU,hThin,hCFull,hSharp,hOrdU,hPreparedU,hN',hFull',hTr',hDense',
    hNextOrd,hNextPrepared,hAU,?_,?_,?_⟩
  · intro i
    obtain ⟨hCont,hUnit,hAdmI,hAdmD,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hRows0 i
    obtain ⟨hcI',hnzI',hcJ',hnzJ',hcD',hnzD',hmD',hFactor'⟩ := hPart' i
    refine ⟨hCont,hUnit,hAdmI,hAdmD,hDict i,hDG i,hJT i,?_,?_,?_,?_,?_,?_,?_,?_,hMPJ i⟩
    · simpa only [oldTraceIdeal,oldMonomialPart,oldResidualPart,hOldGet'] using hFactor'
    · simpa only [oldTraceIdeal,hOldGet'] using hcI'
    · simpa only [oldTraceIdeal,hOldGet'] using hnzI'
    · simpa only [oldMonomialPart,oldTraceIdeal,hOldGet'] using hcD'
    · simpa only [oldMonomialPart,oldTraceIdeal,hOldGet'] using hnzD'
    · simpa only [oldMonomialPart,oldTraceIdeal,hOldGet'] using hmD'
    · simpa only [oldResidualPart,oldTraceIdeal,hOldGet'] using hcJ'
    · simpa only [oldResidualPart,oldTraceIdeal,hOldGet'] using hnzJ'
  · intro z hz hzx
    have hz0 : χ z ∈ N0 := by
      change z ∈ χ ⁻¹' N0
      rw [←hN]
      exact hz
    have hx0 : π0 (χ z)=(⟨x,hxU⟩ : U) := (congrFun hComp z).trans hzx
    obtain ⟨hSub,hPivot,hCols⟩ := hMatrix0 (χ z) hz0 hx0
    rw [←hR z] at hSub hPivot hCols
    refine ⟨hSub,hPivot,?_⟩
    intro i j
    let j0 : Fin born0.length := Fin.cast hLen j
    have he : divExpAlong n N' (D' i) (born'.get j) z=
        divExpAlong n N0 (D0 i) (born0.get j0) (χ z) := by
      have hj : j.val < born'.length := j.isLt
      have hj0 : j.val < born0.length := j0.isLt
      have he := hExp i z j.val
      simp only [expDataAlong,dif_pos hj,dif_pos hj0] at he
      exact he
    have hIndex : Fin.cast (show born0.length=bornU.length+1 by simp [born0]) j0=
        Fin.cast (show born'.length=bornU.length+1 by simp [born']) j := Fin.ext rfl
    have hc := hCols i j0
    rw [hIndex] at hc
    exact ⟨he.trans hc.1,he.trans hc.2⟩
  · intro z hz hzC i j
    have hz0 : χ z ∈ N0 := by
      change z ∈ χ ⁻¹' N0
      rw [←hN]
      exact hz
    have hx0 : π0 (χ z) ∉ CU := by
      rw [hPoint]
      exact hzC
    let j0 : Fin born0.length := Fin.cast hLen j
    have he : divExpAlong n N' (D' i) (born'.get j) z=
        divExpAlong n N0 (D0 i) (born0.get j0) (χ z) := by
      have hj : j.val < born'.length := j.isLt
      have hj0 : j.val < born0.length := j0.isLt
      have he := hExp i z j.val
      simp only [expDataAlong,dif_pos hj,dif_pos hj0] at he
      exact he
    have hc := hOff0 (χ z) hz0 hx0 i j0
    have hIndex : Fin.cast (show born0.length=bornU.length+1 by simp [born0]) j0=
        Fin.cast (show born'.length=bornU.length+1 by simp [born']) j := Fin.ext rfl
    change divExpAlong n N0 (D0 i) (born0.get j0) (χ z)=
      appendAbsentRow (fun k => divExpAlong n NU (DU i) (bornU.get k) (π0 (χ z)))
        (Fin.cast (show born0.length=bornU.length+1 by simp [born0]) j0) at hc
    rw [hIndex,hPoint] at hc
    exact he.trans hc

end
end Hironaka.HironakaG3PreparedMixedGivenBlowup
