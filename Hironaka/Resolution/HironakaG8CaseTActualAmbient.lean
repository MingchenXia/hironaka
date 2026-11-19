import Hironaka.Resolution.HironakaG8CaseTAmbientStage
import Hironaka.Resolution.HironakaG8CaseNPrefix
import Hironaka.Resolution.HironakaG11InvBMLowerDomainSucc

/-! # Actual contact-stage ambient data -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTActualAmbient
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  HomogenizedIdealAlongTower TangentDirectionAlong HironakaG11InvBMLower HironakaG11InvBMStage
  HironakaG8LocalHistory HironakaG8ClassStepCut HironakaG8CaseNPrefix

/-- The actual coefficient record carries the old boundary prefix and is
locally equivalent to the actual previous ambient record. -/
theorem actual_contact_prefix
    {n : ℕ} {X Y : CMfd.{u} n} (A : MarkedIdeal n X)
    (hA : A.IsWellFormed) (hd : 1 ≤ A.d) (U : Opens X) {f : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) :
    let V := openPreimage T U
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
    let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
    let F := (A.E.map (strictAlong T)).map ((Subtype.val : V → Y) ⁻¹' ·)
    LocWPEquiv (X := CMfd.of (n := n) V) { C with E := F ++ C.E } R := by
  let V := openPreimage T U
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
  let D := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong (emptyBoundary A) T)
  let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
  let F := (A.E.map (strictAlong T)).map ((Subtype.val : V → Y) ⁻¹' ·)
  have hDC : LocWPEquiv (X := CMfd.of (n := n) V) D C :=
    HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM hA hd U hf T hT
  have hrel := locEquiv_addE (κ := Kinds.wp) rfl hDC F
  have hpref : geoTransformAlong A T =
      { geoTransformAlong (emptyBoundary A) T with E := A.E.map (strictAlong T) ++ (geoTransformAlong (emptyBoundary A) T).E } := by
    simpa [emptyBoundary] using geoTransformAlong_prefix (emptyBoundary A) A.E T
  have hR : R = { D with E := F ++ D.E } := by
    dsimp [R, D, F]
    rw [hpref]
    simp only [MarkedIdeal.pullback, List.map_append]
  change LocWPEquiv (X := CMfd.of (n := n) V) { C with E := F ++ C.E } R
  rw [hR]
  have hCE : C.E = D.E := hDC.E_eq
  rw [hCE]
  exact hrel.symm


/-- The coefficient stage and the previous native stage have their actual
well-formed carriers and the contact carrier is a hypersurface of the native
carrier at each of its points, including when the carrier is empty. -/
theorem actual_contact_ambient
    {n : ℕ} {X Y : CMfd.{u} n} (A : MarkedIdeal n X)
    (hA : A.IsWellFormed) (hd : 1 ≤ A.d) (U : Opens X) {f : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) :
    let V := openPreimage T U
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
    let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
    C.IsWellFormed ∧ R.IsWellFormed ∧ C.N ⊆ R.N ∧
      ∀ x ∈ C.N, ∃ m, RegularAtDim (n := n) R.N x (m+1) ∧
        RegularAtDim (n := n) C.N x m := by
  let V := openPreimage T U
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
  let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
  have hk : ResolutionInvariantSpec.DimLE n A.N n := by
    intro x hx
    obtain ⟨k, hk⟩ := hA.isClosedSubmanifold_N.2 x hx
    exact ⟨k, hk.1, hk⟩
  have hbar := (coeff_homAlong_wEquiv A hA.isClosedSubmanifold_N hA.isCoherent hd).2 T
  have hC : C.IsWellFormed :=
    (HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le
      hA hd U hf T hk (hbar.1.mpr hT) V Subset.rfl).1
  have hR : R.IsWellFormed := IsWellFormed.pullback_val
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA T hT) V
  have hsub : C.N ⊆ R.N := by
    intro x hx
    change x.val ∈ strictAlong T (A.N ∩ {x | f x = 0}) at hx
    change x.val ∈ (geoTransformAlong A T).N
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono T inter_subset_left hx
  change C.IsWellFormed ∧ R.IsWellFormed ∧ C.N ⊆ R.N ∧ _
  refine ⟨hC, hR, hsub, ?_⟩
  intro x hx
  have ha := HironakaG8ContactStageAmbient.contact_stage_ambient_hypersurface
    A hA hd U hf T hT x hx
  exact ha.2.2.2


/-- Every test tower of the actual prefixed coefficient stage has a literal
previous ambient stage with matching full boundary and contact hypersurface. -/
theorem actual_contact_ambient_along_test
    {n : ℕ} {X Y : CMfd.{0} n} (A : MarkedIdeal n X)
    (hA : A.IsWellFormed) (hd : 1 ≤ A.d) (U : Opens X) {f : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) :
    let V := openPreimage T U
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
    let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
    let F := (A.E.map (strictAlong T)).map ((Subtype.val : V → Y) ⁻¹' ·)
    ∀ {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) V) Z),
      IsGeoTestTower { C with E := F ++ C.E } S →
      ∀ {z : Z}, z ∈ (geoTransformAlong C S).N →
        (geoTransformAlong R S).IsWellFormed ∧
        (geoTransformAlong C S).N ⊆ (geoTransformAlong R S).N ∧
        (geoTransformAlong R S).E = (geoTransformAlong { C with E := F ++ C.E } S).E ∧
        ∃ m, RegularAtDim (n := n) (geoTransformAlong R S).N z (m+1) ∧
          RegularAtDim (n := n) (geoTransformAlong C S).N z m := by
  let V := openPreimage T U
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
  let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
  let F := (A.E.map (strictAlong T)).map ((Subtype.val : V → Y) ⁻¹' ·)
  have h := actual_contact_ambient A hA hd U hf T hT
  have hrel := actual_contact_prefix A hA hd U hf T hT
  change ∀ {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) V) Z),
      IsGeoTestTower { C with E := F ++ C.E } S →
      ∀ {z : Z}, z ∈ (geoTransformAlong C S).N → _
  intro Z S hS z hz
  exact HironakaG8CaseTAmbientStage.ambient_hypersurface_along_prefixed_test
    C R h.1 h.2.1 h.2.2.1 F hrel h.2.2.2 S hS hz

end
end Hironaka.HironakaG8CaseTActualAmbient
