import Hironaka.Resolution.HironakaG11ContactVanishingFill
import Hironaka.Resolution.HironakaG8CaseTContactPair
import Hironaka.Invariant.StepOneUSC

set_option autoImplicit false

/-! The vanishing-coefficient carrier filling applies to the actual pair of
contact stages and transfers to the ambient endpoint. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualContactVanishing
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedIdealAlong
  TangentDirectionAlong GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG8CaseTContactPair HironakaG8CaseTActualAmbient
  HironakaG11InvBMLower HironakaG11ContactVanishingFill HironakaG11InvBMClass
  HironakaG8SpecialLoci MarkedIdealOperationsAlong.MarkedIdeal
  HironakaStepOneZeroContactRemainderGlueing

/-- On the actual common tangent open, if either coefficient ideal vanishes
along its carrier germ at a common cosupport point, the two contact carrier
germs coincide in the ambient stage. -/
theorem actual_contact_carriers_equal_of_vanishes
    {n : ℕ} {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (h : LocWPEquiv A B) (hdim : SameCarrierDim A B)
    (U : Opens X) {f g : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (hg : IsTangentDirectionAlong B.N B.ideal B.d U g)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y} (hyU : y ∈ openPreimage T U)
    (hyC : y ∈ (contactCoeffBM A f T).cosupp)
    (hzero : ¬ IsNonzeroAlongAt (contactCoeffBM A f T).N (contactCoeffBM A f T).ideal y ∨
      ¬ IsNonzeroAlongAt (contactCoeffBM B g T).N (contactCoeffBM B g T).ideal y) :
    ∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A f T).N ↔ z ∈ (contactCoeffBM B g T).N := by
  let V := openPreimage T U
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f T)
  let D := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B g T)
  let p : V := ⟨y,hyU⟩
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hT
  have hwfC : C.IsWellFormed := (actual_contact_ambient A hA hdA U hf T hT).1
  have hwfD : D.IsWellFormed := (actual_contact_ambient B hB hdB U hg T hTB).1
  have hpair := actual_contact_pair A B hA hB hdA hdB h hdim U hf hg T hT
  have hcos : C.cosupp = D.cosupp := hpair.1.cosupp_eq_base
  have hdimCD : SameCarrierDim (X := CMfd.of (n := n) V) C D := hpair.2
  have hcA := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA).isClosedSubmanifold_N
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA).isCoherent T
    (HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hA hdA T
      (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A T hT))).2
  have hcB := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hB).isClosedSubmanifold_N
    (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hB).isCoherent T
    (HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hB hdB T
      (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary B T hTB))).2
  have hcCA : (contactCoeffBM A f T).ideal.IsCoherent := hcA
  have hpC : p ∈ C.cosupp := by
    rw [cosupp_pullback_val (contactCoeffBM A f T) (hol_of_isCoherent hcCA) V]
    exact hyC
  have hcar : ∀ᶠ q in 𝓝 p, q ∈ C.N ↔ q ∈ D.N := by
    rcases hzero with hzero | hzero
    · have hzero' : ¬ IsNonzeroAlongAt C.N C.ideal p := fun hnz =>
        hzero ((isNonzeroAlongAt_pullback_val_iff hcA V p).mp hnz)
      exact eventually_carriers_equal_of_coefficient_vanishes (X := CMfd.of (n := n) V) C D hwfC hcos hdimCD hpC hzero'
    · have hzero' : ¬ IsNonzeroAlongAt D.N D.ideal p := fun hnz =>
        hzero ((isNonzeroAlongAt_pullback_val_iff hcB V p).mp hnz)
      have hdimDC := SameCarrierDim.symm_of_cosupp_eq hcos hdimCD
      exact (eventually_carriers_equal_of_coefficient_vanishes (X := CMfd.of (n := n) V) D C hwfD hcos.symm hdimDC (hcos ▸ hpC) hzero').mono
        (fun _ h => h.symm)
  have hpush := StepOneUSC.eventually_forall_mem_of_eventually V hyU hcar
  filter_upwards [hpush,V.isOpen.mem_nhds hyU] with z hz hzV
  exact hz hzV

end Hironaka.HironakaG11ActualContactVanishing
