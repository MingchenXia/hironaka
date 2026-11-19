import Hironaka.Resolution.HironakaActualProtectedGammaMaximumWindow

/-! # Protection of a prepared row by normal-crossing centres (G4K1B, route B)

Lane G34 (run 0080, round 3).  Blueprint: `hironaka-g34-resume-protection-nc-centre.tex`.
Human decision I-1307 C-0002 (route B): the old-row phases of G4K1B are to restrict near every
prepared row to a PROTECTED phase, protection coming from normal-crossing centres.

The protected configuration of a prepared row `i` near a point (held `protected_slice_window`):
a carrier `N`, an auxiliary hypersurface `H` with `S_i = N ∩ H`, and the row's boundary `F`, with
`H :: F` simple normal crossings and transverse to `N`.

* `protection_of_nc_centre`: one blowup whose centre `C ⊆ N` has normal crossings with `H :: F` and
  is transverse to `H` keeps the configuration protected: `N'` is a closed submanifold, `H' :: F'`
  (`F'` with the exceptional divisor) is SNC and transverse to `N'`, the strict transform of
  `S_i` is `N' ∩ H'`, a closed submanifold whose ideal is the relative strict transform of the
  ideal of `S_i`, with normal crossings with `F'` and dense off `F'` (so the row stays prepared:
  its residual is the ideal of a smooth hypersurface of the carrier).
* `nc_centre_of_local_strata` (the "union of strata" criterion): a centre that is, near each of
  its points, a stratum `N ∩ ⋂_{q ∈ Q} F_q` of the row's boundary on the carrier (no `H`
  equation) has normal crossings with `H :: F` and is transverse to `H`.
* `protection_of_stratum_centre`: the two combined.

The geometric engines are held (`transverse_slice_step`, `isSNCDivisor_geoTransformE_of_hasNormalCrossings`,
`isTransverse_geoTransformE_of_hasNormalCrossings`, `geoStrictTransform_inter_eq`); the coordinate
helpers of `HironakaActualProtectedGammaMaximumWindow` are private there and copied verbatim. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34ProtectionNCCentre
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  NormalCrossingsInvariance SimultaneousNormalCrossings BlowupStrictSubmanifold
  BlowupSNCTransform MemberInterAlong BoundaryCount BlowupFlatCoordinates
  HironakaActualProtectedOtherRowLocalStep HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalProductTraceOrder
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualTraceIncidence HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4ResidualInductionInputs HironakaG4ActiveMonomialSharpBad
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder MonomialPartAlong
  MonomialCaseAlong MonomialCase MonomialInvariant MonomialStepAlong
  DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionDriver
  HomogenizedGlueingTower IdealWeightPowers

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Reused private source-coordinate argument; zero separate achievement credit. -/
private theorem transverse_stratum_omitted (hn : 0 < n) {N H : Set X}
    {F : List (Set X)} (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F)) (S : Finset (Fin F.length)) :
    IsTransverse n (N ∩ memberInter F S) [H] := by
  intro x hx
  obtain ⟨_kC,kN,Φ,s,_hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hE hTr hTr.hasNormalCrossings hx.1
  let z : Fin (H :: F).length := ⟨0,by simp⟩
  let c : Fin F.length → Fin (H :: F).length := fun a =>
    ⟨a.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using a.isLt⟩
  have hz : (H :: F).get z=H := rfl
  have hc (a : Fin F.length) : (H :: F).get (c a)=F.get a := by
    simp [c,List.get_eq_getElem]
  let QN : Finset (Fin n) := Finset.univ.filter fun t => kN ≤ t.val
  let QF : Finset (Fin n) := S.biUnion fun a => {s (c a)}
  refine ⟨QN ∪ QF,fun _ => {s z},?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | a) hxa y hy hyΦ
    · change y ∈ N ∩ memberInter F S ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (QN ∪ QF)
      rw [ExceptionalPushforwardAlong.coordSubspace_union]
      change (y ∈ N ∧ ∀ b ∈ S,y ∈ F.get b) ↔
        (Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QN ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QF)
      refine and_congr ?_ ?_
      · rw [show coordSubspace QN=complexCoordinatePlane n kN by
          simp only [QN,coordSubspace_eq_complexCoordinatePlane]]
        simpa only [complexChartAt] using (hflat hy hyΦ).2.1
      · rw [show coordSubspace QF=coordSubspace (S.biUnion fun b => {s (c b)}) by rfl,
          BoundaryCount.mem_coordSubspace_biUnion]
        apply forall₂_congr
        intro b hb
        rw [BlowupSNCTransform.mem_coordSubspace_singleton]
        have hxb : x ∈ (H :: F).get (c b) := by rw [hc];exact hx.2 b hb
        simpa only [hc,complexChartAt] using (hflat hy hyΦ).2.2 (c b) hxb
    · have ha : [H].get a=H := by fin_cases a;rfl
      change x ∈ [H].get a at hxa
      change (y ∈ [H].get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s z})
      rw [ha] at hxa ⊢
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have hxh : x ∈ (H :: F).get z := by rw [hz];exact hxa
      simpa only [hz,complexChartAt] using (hflat hy hyΦ).2.2 z hxh
  · intro a hxa
    have ha : [H].get a=H := by fin_cases a;rfl
    rw [ha] at hxa
    have hxh : x ∈ (H :: F).get z := by rw [hz];exact hxa
    refine ⟨by simp,Finset.disjoint_singleton_left.mpr ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hQN | hQF
    · have hge := (Finset.mem_filter.mp hQN).2
      exact Nat.not_lt_of_ge hge (hs z hxh)
    · obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp hQF
      have hxb : x ∈ (H :: F).get (c b) := by rw [hc];exact hx.2 b hb
      have hidx := hinj hxh hxb (Finset.mem_singleton.mp he)
      have hv := congrArg Fin.val hidx
      dsimp [z,c] at hv
      omega

private theorem embedded_memberInter {E F : List (Set X)}
    (e : Fin E.length ↪ Fin F.length) (hGet : ∀ i,F.get (e i)=E.get i)
    (S : Finset (Fin E.length)) : memberInter F (S.map e)=memberInter E S := by
  ext y
  constructor
  · intro hy i hi
    rw [←hGet i]
    exact hy (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · intro hy i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    rw [hGet]
    exact hy j hj

private theorem union_memberInter (F : List (Set X)) (Q S : Finset (Fin F.length)) :
    memberInter F (Q ∪ S)=memberInter F Q ∩ memberInter F S := by
  ext y
  constructor
  · intro hy
    exact ⟨fun i hi => hy i (Finset.mem_union_left S hi),
      fun i hi => hy i (Finset.mem_union_right Q hi)⟩
  · rintro ⟨hyQ,hyS⟩ i hi
    exact (Finset.mem_union.mp hi).elim (hyQ i) (hyS i)

private theorem stratum_nc_auxiliary {N H : Set X} {F : List (Set X)}
    (hTr : IsTransverse n N (H :: F)) (Q : Finset (Fin F.length)) :
    HasNormalCrossings n (N ∩ memberInter F Q) (H :: F) := by
  let e : Fin F.length ↪ Fin (H :: F).length :=
    ⟨Fin.succ,fun a b he => Fin.ext (Nat.succ.inj (congrArg Fin.val he))⟩
  have hGet (i : Fin F.length) : (H :: F).get (e i)=F.get i := rfl
  have hNC := hasNormalCrossings_inter_memberInter hTr (Q.map e)
  rw [embedded_memberInter e hGet Q] at hNC
  exact hNC


/-- **Protection by a normal-crossing centre** (route B of G4K1B). -/
theorem protection_of_nc_centre (hn : 0 < n) {N H C : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F)) (hCN : C ⊆ N)
    (hCNC : HasNormalCrossings n C (H :: F)) (hCH : IsTransverse n C [H])
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    let N' := geoStrictTransform π C N
    let H' := geoStrictTransform π C H
    let F' := F.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    let Z' := geoStrictTransform π C (N ∩ H)
    IsClosedSubmanifold n N' ∧ IsSNCDivisor n (H' :: F') ∧ IsTransverse n N' (H' :: F') ∧
      Z' = N' ∩ H' ∧ IsClosedSubmanifold n Z' ∧
      nextRelativeStrict N (vanishingIdeal (n := n) (N ∩ H)) C π = vanishingIdeal (n := n) Z' ∧
      HasNormalCrossings n Z' F' ∧ Z' ⊆ closure (Z' \ ⋃ K ∈ F', K) := by
  intro N' H' F' Z'
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hE' : IsSNCDivisor n (H' :: F') := by
    simpa only [List.map_cons, List.cons_append] using
      isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hE hCNC
  have hTr' : IsTransverse n N' (H' :: F') := by
    simpa only [List.map_cons, List.cons_append] using
      isTransverse_geoTransformE_of_hasNormalCrossings hπ hN.1 hCN hE hTr hCNC
  have hZeq : Z' = N' ∩ H' := by
    calc Z' = geoStrictTransform π C (H ∩ N) := by
          show geoStrictTransform π C (N ∩ H) = _
          rw [inter_comm N H]
      _ = H' ∩ N' := ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hπ hN.1 hCN hE hTr hCNC
          (0 : Fin (H :: F).length)
      _ = N' ∩ H' := inter_comm _ _
  obtain ⟨hZ, hIdeal, hZNC, hZD⟩ := transverse_slice_step hn hN hE hTr hCN hCNC hCH hπ
  exact ⟨hN', hE', hTr', hZeq, hZ, hIdeal, hZNC, hZD⟩

/-- **Centres that are locally strata of the row's boundary** have normal crossings with `H :: F`
and are transverse to `H` (the "union of strata" criterion of route B). -/
theorem nc_centre_of_local_strata (hn : 0 < n) {N H C : Set X} {F : List (Set X)}
    (hE : IsSNCDivisor n (H :: F)) (hTr : IsTransverse n N (H :: F))
    (hLocal : ∀ x ∈ C, ∃ Q : Finset (Fin F.length), x ∈ N ∩ memberInter F Q ∧
      ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ N ∩ memberInter F Q) :
    C ⊆ N ∧ IsTransverse n C [H] ∧ HasNormalCrossings n C (H :: F) := by
  refine ⟨fun x hx => (hLocal x hx).choose_spec.1.1, ?_, ?_⟩
  · apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
    intro x hx
    obtain ⟨Q, hxQ, hNear⟩ := hLocal x hx
    exact ⟨N ∩ memberInter F Q, hxQ, hNear, transverse_stratum_omitted hn hE hTr Q⟩
  · apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
    intro x hx
    obtain ⟨Q, hxQ, hNear⟩ := hLocal x hx
    exact ⟨N ∩ memberInter F Q, hxQ, hNear, stratum_nc_auxiliary hTr Q⟩

/-- **Protection by a centre that is locally a stratum of the row's boundary.** -/
theorem protection_of_stratum_centre (hn : 0 < n) {N H C : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F))
    (hLocal : ∀ x ∈ C, ∃ Q : Finset (Fin F.length), x ∈ N ∩ memberInter F Q ∧
      ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ N ∩ memberInter F Q)
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    let N' := geoStrictTransform π C N
    let H' := geoStrictTransform π C H
    let F' := F.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    let Z' := geoStrictTransform π C (N ∩ H)
    IsClosedSubmanifold n N' ∧ IsSNCDivisor n (H' :: F') ∧ IsTransverse n N' (H' :: F') ∧
      Z' = N' ∩ H' ∧ IsClosedSubmanifold n Z' ∧
      nextRelativeStrict N (vanishingIdeal (n := n) (N ∩ H)) C π = vanishingIdeal (n := n) Z' ∧
      HasNormalCrossings n Z' F' ∧ Z' ⊆ closure (Z' \ ⋃ K ∈ F', K) := by
  obtain ⟨hCN, hCH, hCNC⟩ := nc_centre_of_local_strata hn hE hTr hLocal
  exact protection_of_nc_centre hn hN hE hTr hCN hCNC hCH hπ

end
end Hironaka.HironakaG34ProtectionNCCentre
