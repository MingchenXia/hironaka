import Hironaka.Resolution.HironakaG8CaseTActualAmbient

/-! # Pairwise actual contact-stage data -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTContactPair
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HomogenizedGlueingTower HomogenizedIdealAlongTower TangentDirectionAlong
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaG8CaseTActualAmbient

/-- Equal ambient dimensions and genuine contact hypersurfaces give equal
contact dimensions on their common cosupport. -/
theorem same_contact_dimension
    {n : ℕ} {X : CMfd.{u} n} (C D R S : MarkedIdeal n X) (F : List (Set X))
    (hCR : LocWPEquiv {C with E := F ++ C.E} R)
    (hDS : LocWPEquiv {D with E := F ++ D.E} S)
    (hrel : LocWPEquiv R S) (hRS : SameCarrierDim R S)
    (hC : ∀ x ∈ C.N, ∃ m, RegularAtDim (n := n) R.N x (m+1) ∧ RegularAtDim (n := n) C.N x m)
    (hD : ∀ x ∈ D.N, ∃ m, RegularAtDim (n := n) S.N x (m+1) ∧ RegularAtDim (n := n) D.N x m) :
    SameCarrierDim C D := by
  intro x hx j
  have hxR : x ∈ R.cosupp := hCR.cosupp_eq_base ▸ hx
  have hxS : x ∈ S.cosupp := by
    exact hrel.cosupp_eq_base ▸ hxR
  have hxD : x ∈ D.N := D.cosupp_subset_N (hDS.cosupp_eq_base.symm ▸ hxS)
  obtain ⟨m, hmR, hmC⟩ := hC x (C.cosupp_subset_N hx)
  obtain ⟨m', hmS, hmD⟩ := hD x hxD
  have heq : m = m' := by
    have hs : RegularAtDim (n := n) S.N x (m+1) := (hRS x hxR (m+1)).mp hmR
    have := RegularPointDimension.eq_of_regularAtDim hs hmS
    omega
  subst m'
  constructor <;> intro hj
  · rw [← RegularPointDimension.eq_of_regularAtDim hmC hj]; exact hmD
  · rw [← RegularPointDimension.eq_of_regularAtDim hmD hj]; exact hmC


/-- Two actual coefficient stages inherit both local equivalence after
restoring the common ordered old boundary and the same carrier dimension. -/
theorem actual_contact_pair
    {n : ℕ} {X Y : CMfd.{u} n} (A B : MarkedIdeal n X)
    (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hAB : LocWPEquiv A B) (hdim : SameCarrierDim A B)
    (U : Opens X) {f g : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (hg : IsTangentDirectionAlong B.N B.ideal B.d U g)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) :
    let V := openPreimage T U
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
    let D := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B g T)
    let F := (A.E.map (strictAlong T)).map ((Subtype.val : V → Y) ⁻¹' ·)
    LocWPEquiv (X := CMfd.of (n := n) V) {C with E := F ++ C.E} {D with E := F ++ D.E} ∧
      SameCarrierDim (X := CMfd.of (n := n) V) C D := by
  let V := openPreimage T U
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
  let D := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B g T)
  let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
  let S := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong B T)
  let F := (A.E.map (strictAlong T)).map ((Subtype.val : V → Y) ⁻¹' ·)
  have hTB : IsGeoTestTower B T := (hAB.wEquiv.2 T).1.mp hT
  have hCR : LocWPEquiv (X := CMfd.of (n := n) V) {C with E := F ++ C.E} R :=
    actual_contact_prefix A hA hdA U hf T hT
  have hDS : LocWPEquiv (X := CMfd.of (n := n) V) {D with E := F ++ D.E} S := by
    have h := actual_contact_prefix B hB hdB U hg T hTB
    have hE : B.E = A.E := hAB.E_eq
    simpa only [hE] using h
  have hRS : LocWPEquiv (X := CMfd.of (n := n) V) R S := (hAB.geoTransformAlong T hT).restrict V
  have hstage := HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hA hB hAB.wEquiv hdim T hT
  have hRwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA T hT
  have hdimRS : SameCarrierDim (X := CMfd.of (n := n) V) R S :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hRwf.isCoherent) hstage V
  have hC := actual_contact_ambient A hA hdA U hf T hT
  have hD := actual_contact_ambient B hB hdB U hg T hTB
  change LocWPEquiv (X := CMfd.of (n := n) V) {C with E := F ++ C.E} {D with E := F ++ D.E} ∧
    SameCarrierDim (X := CMfd.of (n := n) V) C D
  exact ⟨hCR.trans (hRS.trans hDS.symm), same_contact_dimension (X := CMfd.of (n := n) V) C D R S F hCR hDS hRS hdimRS hC.2.2.2 hD.2.2.2⟩

end
end Hironaka.HironakaG8CaseTContactPair
