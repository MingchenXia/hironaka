import Hironaka.Resolution.HironakaG8ClassStepHistory
/-! # Common domain open along a test tower -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8PairDomainOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  DivisorExponentAlong HironakaG8DomainExponents ResolutionInvariantSpec HironakaG8LocalHistory HironakaG8ClassStepHistory

/-- Nonvanishing along a transformed carrier descends through an entire
actual geometric test tower. -/
theorem isNonzeroAlongAt_of_geoTransformAlong
    {n : ℕ} {X : CMfd.{u} n} (P : MarkedIdeal n X) (hP : P.IsWellFormed) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      ∀ {y : Y}, IsNonzeroAlongAt (geoTransformAlong P T).N (geoTransformAlong P T).ideal y →
        IsNonzeroAlongAt P.N P.ideal (T.proj y)
  | _, .refl, _, _, h => h
  | _, .step T C π hπ, hT, y, h => by
    obtain ⟨hTT,hC⟩ := (isGeoTestTower_step_iff P T C π hπ).mp hT
    have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hP T hTT
    have hy : IsNonzeroAlongAt ((geoTransformAlong P T).geoTransform C π).N
        ((geoTransformAlong P T).geoTransform C π).ideal y := h
    have hn := isNonzeroAlongAt_of_geoTransform hπ (geoTransformAlong P T)
      hw.isClosedSubmanifold_N hw.isCoherent hC hy
    exact isNonzeroAlongAt_of_geoTransformAlong P hP T hTT hn

/-- At a point nonzero along both actual transformed carriers, one common
source open contains its projection, puts both records in the invariant
domain, and retains the restricted test tower for each record. -/
theorem exists_common_domain_open_of_test
    {n : ℕ} {X Y : CMfd.{u} n} (P Q : MarkedIdeal n X)
    (hP : P.IsWellFormed) (hQ : Q.IsWellFormed) (hdP : 1 ≤ P.d) (hdQ : 1 ≤ Q.d)
    (T : BlowupTower X Y) (hTP : IsGeoTestTower P T) (hTQ : IsGeoTestTower Q T)
    {y : Y} (hyP : y ∈ (geoTransformAlong P T).N) (hyQ : y ∈ (geoTransformAlong Q T).N)
    (hnP : IsNonzeroAlongAt (geoTransformAlong P T).N (geoTransformAlong P T).ideal y)
    (hnQ : IsNonzeroAlongAt (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal y) :
    ∃ G : Opens X, T.proj y ∈ G ∧
      IsInvDomain n (MarkedIdeal.pullback (Subtype.val : G → X) P) ∧
      IsInvDomain n (MarkedIdeal.pullback (Subtype.val : G → X) Q) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G → X) P) (restrict G T) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G → X) Q) (restrict G T) := by
  let G := domOpen P hP.isClosedSubmanifold_N ⊓ domOpen Q hQ.isClosedSubmanifold_N
  have hyBaseP : T.proj y ∈ P.N := by
    apply MemberInterTowerAlong.strictAlong_subset_preimage T hP.isClosedSubmanifold_N.1
    simpa only [N_geoTransformAlong] using hyP
  have hyBaseQ : T.proj y ∈ Q.N := by
    apply MemberInterTowerAlong.strictAlong_subset_preimage T hQ.isClosedSubmanifold_N.1
    simpa only [N_geoTransformAlong] using hyQ
  have hnBaseP := isNonzeroAlongAt_of_geoTransformAlong P hP T hTP hnP
  have hnBaseQ := isNonzeroAlongAt_of_geoTransformAlong Q hQ T hTQ hnQ
  have hyG : T.proj y ∈ G :=
    ⟨(mem_domOpen_iff hP.isClosedSubmanifold_N hP.isCoherent hdP hyBaseP).mpr hnBaseP,
      (mem_domOpen_iff hQ.isClosedSubmanifold_N hQ.isCoherent hdQ hyBaseQ).mpr hnBaseQ⟩
  exact ⟨G,hyG,isInvDomain_pullback_val_of_le_domOpen hP hdP inf_le_left,
    isInvDomain_pullback_val_of_le_domOpen hQ hdQ inf_le_right,
    isGeoTestTower_restrict G hP.isClosedSubmanifold_N hP.isCoherent T hTP,
    isGeoTestTower_restrict G hQ.isClosedSubmanifold_N hQ.isCoherent T hTQ⟩


/-- A prefixed locally equivalent pair admits a common native-domain open at
the projection of every point where both test transforms are nonzero. The
literal prefix and prefixed test are retained on that open. -/
theorem exists_common_domain_open_of_prefixed_test
    {n : ℕ} {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X) (F : List (Set X))
    (hP : P.IsWellFormed) (hQ : Q.IsWellFormed) (hdP : 1 ≤ P.d) (hdQ : 1 ≤ Q.d)
    (hE : Q.E = P.E)
    (hrel : LocWPEquiv {P with E := F ++ P.E} {Q with E := F ++ P.E})
    (T : BlowupTower X Y) (hT : IsGeoTestTower {P with E := F ++ P.E} T)
    {y : Y} (hyP : y ∈ (geoTransformAlong P T).N) (hyQ : y ∈ (geoTransformAlong Q T).N)
    (hnP : IsNonzeroAlongAt (geoTransformAlong P T).N (geoTransformAlong P T).ideal y)
    (hnQ : IsNonzeroAlongAt (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal y) :
    ∃ G : Opens X, T.proj y ∈ G ∧
      let PG := MarkedIdeal.pullback (Subtype.val : G → X) P
      let QG := MarkedIdeal.pullback (Subtype.val : G → X) Q
      let FG := F.map ((Subtype.val : G → X) ⁻¹' ·)
      IsInvDomain n PG ∧ IsInvDomain n QG ∧
      LocWPEquiv (X := CMfd.of (n := n) G) {PG with E := FG ++ PG.E} {QG with E := FG ++ PG.E} ∧
      IsGeoTestTower PG (restrict G T) ∧ IsGeoTestTower QG (restrict G T) ∧
      IsGeoTestTower {PG with E := FG ++ PG.E} (restrict G T) := by
  have hTP := isGeoTestTower_of_addE P F T hT
  have hFQ : ({Q with E := F ++ P.E} : MarkedIdeal n X) = {Q with E := F ++ Q.E} := by rw [hE]
  have hTQ := isGeoTestTower_of_addE Q F T (hFQ ▸ ((hrel.wEquiv.2 T).1.mp hT))
  obtain ⟨G,hyG,hPG,hQG,hTPG,hTQG⟩ :=
    exists_common_domain_open_of_test P Q hP hQ hdP hdQ T hTP hTQ hyP hyQ hnP hnQ
  let PG := MarkedIdeal.pullback (Subtype.val : G → X) P
  let QG := MarkedIdeal.pullback (Subtype.val : G → X) Q
  let FG := F.map ((Subtype.val : G → X) ⁻¹' ·)
  have hGrel : LocWPEquiv (X := CMfd.of (n := n) G)
      {PG with E := FG ++ PG.E} {QG with E := FG ++ PG.E} := by
    have hr := hrel.restrict G
    dsimp [PG,QG,FG]
    simpa only [MarkedIdeal.pullback, List.map_append] using hr
  have hTG : IsGeoTestTower (X := CMfd.of (n := n) G) {PG with E := FG ++ PG.E} (restrict G T) := by
    have ht := isGeoTestTower_restrict (𝔪 := {P with E := F ++ P.E}) G
      hP.isClosedSubmanifold_N hP.isCoherent T hT
    dsimp [PG,FG]
    simpa only [MarkedIdeal.pullback, List.map_append] using ht
  exact ⟨G,hyG,hPG,hQG,hGrel,hTPG,hTQG,hTG⟩

end
end Hironaka.HironakaG8PairDomainOpen
