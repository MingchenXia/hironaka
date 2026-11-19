import Hironaka.Resolution.HironakaG8DisjointMarkedSwap
import Hironaka.Resolution.HironakaG4PermutedFullTest
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.Resolution.HironakaG8SingularFootprintExtension

/-! Terminal marked-record transport for a physical disjoint swap. -/
set_option autoImplicit false
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace Hironaka.HironakaG8DisjointSwapRecord
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealPullbackCalculus GermIdealTotalTransform BlowupExceptionalDivisor
  VanishingIdealCoherent IdealWeightPowers RestrictLeCalculus
  BlowupStrictSubmanifold HironakaAdmissibleCalculus
  HironakaSingularSubspaceBlowupLift BlowupControlledTransform StrictTransformComposition
  HironakaG4PermutedFullTest HironakaG8SingularFootprintExtension
  HironakaNormalCrossingsSeparationChoiceComparison HironakaStageCenters HironakaEmbeddedAnalytic
  MarkedIdealTowerTransport MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  BlowupTowerIsomorphism MarkedIdealOpenBiholomorphism

variable {n : ℕ} {X Y W Z Q : CMfd.{0} n}

private abbrev twice
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q) :
    BlowupTower X Z := .step (.step .refl C π hπ) (π ⁻¹' D) q hq

theorem exceptional_ideal_disjoint_two_steps
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hD : IsClosedSubmanifold n D) (hCD : Disjoint C D) :
    (BlowupTowerTransforms.exceptionalDivisor (twice hπ hq)).ideal =
      (GermIdeal.pullback (m := n) (π ∘ q) (vanishingIdeal (n := n) C)).mul
        (GermIdeal.pullback (m := n) (π ∘ q) (vanishingIdeal (n := n) D)) := by
  have hCohC := isCoherent_vanishingIdeal_centre hπ
  have hCohD := isCoherent_vanishingIdeal hD
  have hSingle :
      (BlowupTowerTransforms.exceptionalDivisor (.step (.refl : BlowupTower X X) C π hπ)).ideal =
        GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) := by
    rw [exceptionalDivisor_step_ideal,exceptionalDivisor_refl_ideal,
      BlowupExceptionalDivisor.pullback_unitIdeal,unitIdeal_mul (isCoherent_pullback hπ.contMDiff hCohC)]
  rw [twice,exceptionalDivisor_step_ideal,hSingle,
    ← pullback_comp hπ.contMDiff hq.contMDiff hCohC,
    ← FactorizationFromResolution.pullback_vanishingIdeal_eq_of_disjoint hπ hD.1 hCD,
    ← pullback_comp hπ.contMDiff hq.contMDiff hCohD]

private theorem cancel_invertible_left {L A B : GermIdeal n Z}
    (hL : L.IsInvertible) (hA : A.IsCoherent) (hB : B.IsCoherent)
    (h : L.mul A = L.mul B) : A = B := by
  rw [← colon_mul_eq hL hA, ← colon_mul_eq hL hB, h]

/-- The terminal whole controlled ideals of the two actual disjoint
orders agree by the same comparison, at every ambient germ. -/
theorem controlled_ideal_disjoint_swap
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : W → X} {r : Q → W}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hCD : Disjoint C D) (hL : IsGeoTestTower M (twice hπ hq))
    (hR : IsGeoTestTower M (twice hρ hr))
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) :
    (geoTransformAlong M (twice hπ hq)).ideal =
      GermIdeal.pullback (m := n) e (geoTransformAlong M (twice hρ hr)).ideal := by
  let L := twice hπ hq
  let R := twice hρ hr
  have hEq : R.proj ∘ e = L.proj := he
  obtain ⟨_,hLI,hLf⟩ := pullback_eq_mul_geoTransformAlong M hN hM.isCoherent L hL
  obtain ⟨_,hRI,hRf⟩ := pullback_eq_mul_geoTransformAlong M hN hM.isCoherent R hR
  have hEQL : (BlowupTowerTransforms.exceptionalDivisor L).ideal =
      (GermIdeal.pullback (m := n) L.proj (vanishingIdeal (n := n) C)).mul
      (GermIdeal.pullback (m := n) L.proj (vanishingIdeal (n := n) D)) :=
    exceptional_ideal_disjoint_two_steps hπ hq hρ.1 hCD
  have hEQR : (BlowupTowerTransforms.exceptionalDivisor R).ideal =
      (GermIdeal.pullback (m := n) R.proj (vanishingIdeal (n := n) D)).mul
      (GermIdeal.pullback (m := n) R.proj (vanishingIdeal (n := n) C)) :=
    exceptional_ideal_disjoint_two_steps hρ hr hπ.1 hCD.symm
  have hCohC := isCoherent_vanishingIdeal_centre hπ
  have hCohD := isCoherent_vanishingIdeal_centre hρ
  have hEF : GermIdeal.pullback (m := n) e (BlowupTowerTransforms.exceptionalDivisor R).ideal =
      (BlowupTowerTransforms.exceptionalDivisor L).ideal := by
    rw [hEQR,GermIdealTotalTransform.pullback_mul e.contMDiff
      (isCoherent_pullback R.contMDiff_proj hCohD) (isCoherent_pullback R.contMDiff_proj hCohC),
      ← pullback_comp R.contMDiff_proj e.contMDiff hCohD,
      ← pullback_comp R.contMDiff_proj e.contMDiff hCohC,hEq,hEQL,RestrictLeCalculus.mul_comm']
  have hLpow := BlowupExceptionalDivisor.isInvertible_idealPow
    (BlowupTowerTransforms.exceptionalDivisor L).isInvertible M.d
  apply cancel_invertible_left hLpow hLI (isCoherent_pullback e.contMDiff hRI)
  rw [← hLf]
  have hP := congrArg (GermIdeal.pullback (m := n) e) hRf
  rw [← pullback_comp R.contMDiff_proj e.contMDiff hM.isCoherent,hEq,
    GermIdealTotalTransform.pullback_mul e.contMDiff
      (isCoherent_idealPow (isCoherent_ideal _) _) hRI,
    BlowupExceptionalDivisor.pullback_idealPow e.contMDiff (isCoherent_ideal _),hEF] at hP
  exact hP

private theorem old_strict_trace_double
    {C D H : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q) (hD : IsClosed D) :
    geoStrictTransform q (π ⁻¹' D) (geoStrictTransform π C H) =
      closure ((π ∘ q) ⁻¹' (H \ (C ∪ D))) := by
  let S := π ⁻¹' (H \ C)
  let F := π ⁻¹' D
  have hSet : (π ∘ q) ⁻¹' (H \ (C ∪ D)) = q ⁻¹' (S \ F) := by
    ext z
    simp only [S,F,mem_preimage,Set.mem_sdiff,mem_union,comp_apply]
    tauto
  rw [hSet]
  change closure (q ⁻¹' (closure S \ F)) = closure (q ⁻¹' (S \ F))
  refine subset_antisymm (closure_minimal ?_ isClosed_closure) ?_
  · rintro z ⟨hzS,hzF⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    have hzE : z ∉ exceptionalLocus n q := fun h =>
      hzF (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hq h)
    have hUF : U ∩ (q ⁻¹' F)ᶜ ∈ 𝓝 z :=
      inter_mem hU (((hD.preimage hπ.contMDiff.continuous).preimage
        hq.contMDiff.continuous).isOpen_compl.mem_nhds hzF)
    have hImg : q '' (U ∩ (q ⁻¹' F)ᶜ) ∈ 𝓝 (q z) := by
      rw [← map_nhds_eq_of_not_mem_exceptionalLocus hq.contMDiff hzE]
      exact image_mem_map hUF
    obtain ⟨_, ⟨w,⟨hwU,hwF⟩,rfl⟩,hwS⟩ := mem_closure_iff_nhds.mp hzS _ hImg
    exact ⟨w,hwU,hwS,hwF⟩
  · exact closure_mono (preimage_mono (sdiff_subset_sdiff_left subset_closure))

private theorem strict_first_birth {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q) (hCD : Disjoint C D) :
    geoStrictTransform q (π ⁻¹' D) (π ⁻¹' C) = (π ∘ q) ⁻¹' C := by
  change closure (q ⁻¹' ((π ⁻¹' C) \ (π ⁻¹' D))) = _
  rw [sdiff_eq_left.mpr (hCD.preimage π),
    ((hπ.1.1.preimage hπ.contMDiff.continuous).preimage hq.contMDiff.continuous).closure_eq]
  rfl

/-- Exact chronological boundary readback. The old slots agree in their
original order, while the two actual birth slots exchange positions. -/
theorem ordered_boundary_disjoint_swap
    (M : MarkedIdeal n X)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : W → X} {r : Q → W}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hCD : Disjoint C D) (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) :
    let old := M.E.map (fun H => closure ((π ∘ q) ⁻¹' (H \ (C ∪ D))))
    (geoTransformAlong M (twice hπ hq)).E =
      old ++ [(π ∘ q) ⁻¹' C,(π ∘ q) ⁻¹' D] ∧
    (geoTransformAlong M (twice hρ hr)).E.map (e ⁻¹' ·) =
      old ++ [(π ∘ q) ⁻¹' D,(π ∘ q) ⁻¹' C] := by
  dsimp only
  have hListL : (geoTransformAlong M (twice hπ hq)).E =
      M.E.map (fun H => closure ((π ∘ q) ⁻¹' (H \ (C ∪ D)))) ++
        [(π ∘ q) ⁻¹' C,(π ∘ q) ⁻¹' D] := by
    simp only [twice,geoTransformAlong_step,geoTransformAlong_refl,geoTransform_E,
      List.map_append,List.map_map,List.map_cons,List.map_nil,List.append_assoc]
    rw [strict_first_birth hπ hq hCD]
    congr 1
    apply List.map_congr_left
    intro H _
    exact old_strict_trace_double hπ hq hρ.1.1
  refine ⟨hListL,?_⟩
  have hListR : (geoTransformAlong M (twice hρ hr)).E =
      M.E.map (fun H => closure ((ρ ∘ r) ⁻¹' (H \ (D ∪ C)))) ++
        [(ρ ∘ r) ⁻¹' D,(ρ ∘ r) ⁻¹' C] := by
    simp only [twice,geoTransformAlong_step,geoTransformAlong_refl,geoTransform_E,
      List.map_append,List.map_map,List.map_cons,List.map_nil,List.append_assoc]
    rw [strict_first_birth hρ hr hCD.symm]
    congr 1
    apply List.map_congr_left
    intro H _
    exact old_strict_trace_double hρ hr hπ.1.1
  rw [hListR]
  simp only [List.map_append,List.map_map,List.map_cons,List.map_nil]
  have hSlots : ∀ H : Set X, e ⁻¹' ((ρ ∘ r) ⁻¹' H) = (π ∘ q) ⁻¹' H := by
    intro H
    rw [← preimage_comp,he]
  rw [hSlots,hSlots]
  congr 1
  apply List.map_congr_left
  intro H _
  change e ⁻¹' closure ((ρ ∘ r) ⁻¹' (H \ (D ∪ C))) =
    closure ((π ∘ q) ⁻¹' (H \ (C ∪ D)))
  have hh := e.toHomeomorph.preimage_closure ((ρ ∘ r) ⁻¹' (H \ (D ∪ C)))
  change e ⁻¹' closure _ = closure (e ⁻¹' _) at hh
  rw [hh,hSlots,union_comm D C]

private theorem current_nonboundary_fields_of_same
    (M P : MarkedIdeal n X) (hN : M.N = P.N) (hI : M.ideal = P.ideal) (hd : M.d = P.d) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      (geoTransformAlong M T).N = (geoTransformAlong P T).N ∧
      (geoTransformAlong M T).ideal = (geoTransformAlong P T).ideal ∧
      (geoTransformAlong M T).d = (geoTransformAlong P T).d := by
  intro Y T
  induction T with
  | refl => exact ⟨hN,hI,hd⟩
  | step T C π hπ ih =>
    obtain ⟨hNT,hIT,hdT⟩ := ih
    simp only [geoTransformAlong_step,geoTransform_N,geoTransform_d]
    refine ⟨congrArg (geoStrictTransform π C) hNT,?_,hdT⟩
    simp only [geoTransform,hNT,hIT,hdT]

/-- A pure permutation of ordered boundary slots preserves all original
TEST towers, including nonzero marks and nontrivial controlled ideals. -/
theorem isGeoTestTower_iff_of_boundary_perm_and_same_fields
    (M P : MarkedIdeal n X) (hN : M.N = P.N) (hI : M.ideal = P.ideal) (hd : M.d = P.d)
    (hE : M.E.Perm P.E) (T : BlowupTower X Y) :
    IsGeoTestTower M T ↔ IsGeoTestTower P T := by
  induction T with
  | refl => exact Iff.rfl
  | step T C π hπ ih =>
    have hF := current_nonboundary_fields_of_same M P hN hI hd T
    have hE' := perm_geoTransformAlong_boundary M P hE T
    have hCos : (geoTransformAlong M T).cosupp = (geoTransformAlong P T).cosupp := by
      simp only [MarkedIdeal.cosupp,hF.1,hF.2.1,hF.2.2]
    rw [isGeoTestTower_step_iff,isGeoTestTower_step_iff,ih]
    apply and_congr_right
    intro _
    refine and_congr_right fun _ => ?_
    rw [hCos]
    exact and_congr_right fun _ => ⟨
      fun h => NormalCrossingsComparison.hasNormalCrossings_of_forall_mem h hE'.symm.subset,
      fun h => NormalCrossingsComparison.hasNormalCrossings_of_forall_mem h hE'.subset⟩

/-- The actual common endpoint of a marked disjoint swap carries the same
ambient carrier, whole controlled ideal, and mark, with the exact two
birth positions exchanged. Every subsequent TEST and intrinsic singular
tail transports to the swapped endpoint by the genuine tower transport. -/
theorem transport_tail_after_disjoint_swap
    (A : Set X) (hA : IsClosed A) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : M.N = univ)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : W → X} {r : Q → W}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hCD : Disjoint C D) (hL : IsGeoTestTower M (twice hπ hq))
    (hR : IsGeoTestTower M (twice hρ hr))
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) {F : CMfd.{0} n} (S : BlowupTower Z F)
    (hTest : IsGeoTestTower (geoTransformAlong M (twice hπ hq)) S)
    (hSing : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (π ∘ q) A))) S) :
    let S' := transport (X' := Q) e.symm S
    IsGeoTestTower (geoTransformAlong M (twice hρ hr)) S'.tower ∧
    StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (ρ ∘ r) A))) S'.tower := by
  let L := twice hπ hq
  let R := twice hρ hr
  let ML := geoTransformAlong M L
  let MR := geoTransformAlong M R
  have hMR := isWellFormed_geoTransformAlong hM R hR
  have hFields : ML.N = (MarkedIdeal.pullback e MR).N ∧
      ML.ideal = (MarkedIdeal.pullback e MR).ideal ∧ ML.d = (MarkedIdeal.pullback e MR).d := by
    have hNL := (pullback_eq_mul_geoTransformAlong M hN hM.isCoherent L hL).1
    have hNR := (pullback_eq_mul_geoTransformAlong M hN hM.isCoherent R hR).1
    refine ⟨?_,controlled_ideal_disjoint_swap M hM hN hπ hq hρ hr hCD hL hR e he,?_⟩
    · change ML.N = e ⁻¹' MR.N
      rw [hNL,hNR,preimage_univ]
    · change (geoTransformAlong M L).d = (geoTransformAlong M R).d
      rw [d_geoTransformAlong,d_geoTransformAlong]
  obtain ⟨hEL,hER⟩ := ordered_boundary_disjoint_swap M hπ hq hρ hr hCD e he
  have hPerm : ML.E.Perm (MarkedIdeal.pullback e MR).E := by
    change (geoTransformAlong M L).E.Perm ((geoTransformAlong M R).E.map (e ⁻¹' ·))
    rw [hEL,hER]
    exact (List.Perm.swap _ _ []).append_left _
  have hIso := (transport_isTowerIso (X' := Q) e.symm S).symm
  have hT := (isGeoTestTower_iff_of_boundary_perm_and_same_fields ML
    (MarkedIdeal.pullback e MR) hFields.1 hFields.2.1 hFields.2.2 hPerm S).mp hTest
  have hOn := IsTowerIso.isGeoTestTower_iff (𝔪 := MR) e hMR.isClosedSubmanifold_N hMR.isCoherent hIso
  have hStrict : strictTransform n (π ∘ q) A = e ⁻¹' strictTransform n (ρ ∘ r) A := by
    change strictTransform n L.proj A = e ⁻¹' strictTransform n R.proj A
    simpa using strictTransform_preimage_of_square
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) e L.contMDiff_proj R.contMDiff_proj
      A hA (fun z => congrFun he z)
  refine ⟨hOn.mp hT,?_⟩
  rw [hStrict] at hSing
  exact singular_stages_of_tower_iso (strictTransform n (ρ ∘ r) A) isClosed_closure e hIso hSing

end Hironaka.HironakaG8DisjointSwapRecord
