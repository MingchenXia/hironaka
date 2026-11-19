import Hironaka.Resolution.HironakaG8CoefficientBoundaryLocal
import Hironaka.Resolution.HironakaActualOriginalLowerHeadProjectionTests

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8HomStable
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers GermIdealOrder GermIdealPullbackCalculus IdealOrderArithmetic
  RestrictedIdealWeight RestrictedIdealExtension RestrictLeCalculus
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower HomogenizedGlueing MarkedIdealBiholomorphism
  HomogenizedIdealAlong HomogenizedIdealAlongTower DerivativeIdealAlong DerivativeIdealAlongCoherent
  CoefficientIdeal CoefficientIdealRestriction TangentDirectionAlong
  ResolutionInvariantSpec InvDomainTowerAlong MarkedIdealRestrictOpen
  HironakaActualOriginalHistoricalBarWeightedThreshold
  HironakaG8LocalHistory HironakaG8LocalStable HironakaG8MixedEquiv
  HironakaActualProjectionTestRecord StepOneValue HironakaG8CoefficientBoundaryLocal
open scoped ProductComplexManifold

structure HomSandwich {m : ℕ} {Y : CMfd.{0} m} (P Q : MarkedIdeal m Y) : Prop where
  inv : ∃ r, IsInvDomain r P
  coh : Q.ideal.IsCoherent
  N : P.N = Q.N
  E : P.E = Q.E
  d : P.d = Q.d
  low : RestrictLe P.N P.ideal Q.ideal
  high : RestrictLe P.N Q.ideal (homMarkedAlong P).ideal

 theorem homSandwich_cosupp {m : ℕ} {Y : CMfd.{0} m} {P Q : MarkedIdeal m Y}
    (h : HomSandwich P Q) : P.cosupp = Q.cosupp := by
  obtain ⟨r,hP⟩ := h.inv
  have hH : (homMarkedAlong P).cosupp = P.cosupp := by
    have he := homAlong_wEquiv P hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hP.one_le_d
    simpa using ((he.2 (.refl : BlowupTower Y Y)).2 trivial)
  apply Subset.antisymm
  · intro x hx
    have hxH : x ∈ (homMarkedAlong P).cosupp := hH.symm ▸ hx
    have := cosupport_subset_of_restrictLe h.high P.d hxH
    simpa [MarkedIdeal.cosupp, h.N, h.d] using this
  · intro x hx
    have : x ∈ cosupport m P.N Q.ideal P.d := by simpa [MarkedIdeal.cosupp, h.N, h.d] using hx
    exact cosupport_subset_of_restrictLe h.low P.d this

 theorem homSandwich_step {m : ℕ} {Y : CMfd.{0} m} {P Q : MarkedIdeal m Y}
    (h : HomSandwich P Q) (C : Set Y) {Z : CMfd.{0} m} (π : Z → Y)
    (hπ : IsBlowupAlong m C π) (hC : P.IsAdmissibleCentre C) :
    HomSandwich (P.geoTransform C π) (Q.geoTransform C π) := by
  obtain ⟨r,hP⟩ := h.inv
  have hCQ : Q.IsAdmissibleCentre C :=
    (isAdmissibleCentre_congr h.E (homSandwich_cosupp h) C).mp hC
  let H := homMarkedAlong P
  have hPH : IsGeoTestTower P (.step .refl C π hπ) := ⟨trivial,hC⟩
  have hs := original_homogenization_history_sandwich P hP (.step .refl C π hπ) hPH
  have hCH : H.IsAdmissibleCentre C := hs.1.2
  have hHcoh : H.ideal.IsCoherent :=
    isCoherent_homMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  have hUpper := restrictLe_geoTransform_of_restrictLe (𝔫₁ := Q) (𝔫₂ := H)
    (h.N ▸ hP.isWellFormed.isClosedSubmanifold_N) h.N.symm (by simpa [H, homMarkedAlong] using h.d.symm)
    h.coh hHcoh hCQ hCH hπ (by simpa [← h.N, H] using h.high)
  refine ⟨⟨r, isInvDomain_geoTransformAlong hP (.step .refl C π hπ) hPH⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
      (h.N ▸ hP.isWellFormed.isClosedSubmanifold_N) h.coh hCQ hπ
  · simp only [geoTransform_N, h.N]
  · simp only [geoTransform_E, h.E]
  · exact h.d
  · exact restrictLe_geoTransform_of_restrictLe hP.isWellFormed.isClosedSubmanifold_N
      h.N h.d hP.isWellFormed.isCoherent h.coh hC hCQ hπ h.low
  · have hTop := hs.2.2.2.2.2.2.2
    change RestrictLe (P.geoTransform C π).N (H.geoTransform C π).ideal
      (homMarkedAlong (P.geoTransform C π)).ideal at hTop
    rw [show (Q.geoTransform C π).N = (P.geoTransform C π).N by simp only [geoTransform_N, h.N]] at hUpper
    exact RestrictLeCalculus.RestrictLe.trans hUpper hTop

 theorem homSandwich_projection {m : ℕ} {Y : CMfd.{0} m} {P Q : MarkedIdeal m Y}
    (h : HomSandwich P Q) : HomSandwich (projectionTest P) (projectionTest Q) := by
  obtain ⟨r,hP⟩ := h.inv
  have hφ := ProductComplexManifold.contMDiff_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)
  have hHcoh := isCoherent_homMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  refine ⟨⟨r+1, projection_test_isInvDomain P hP⟩, isCoherent_pullback hφ h.coh, ?_, ?_, h.d, ?_, ?_⟩
  · change Prod.fst ⁻¹' P.N = Prod.fst ⁻¹' Q.N
    rw [h.N]
  · change P.E.map _ ++ [_] = Q.E.map _ ++ [_]
    rw [h.E]
  · exact HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hφ (fun _ hz => hz)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem h.coh hg) h.low
  · have hp := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hφ (fun _ hz => hz)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hHcoh hg) h.high
    have heq := congrArg (fun A => A.ideal)
      (HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_homMarkedAlong (X := Y)
        (Y := projectionAmbient Y)
        (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1))
        P hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N)
    change GermIdeal.pullback (m := m+1) Prod.fst (homMarkedAlong P).ideal =
      (homMarkedAlong (projectionTest P)).ideal at heq
    rw [heq] at hp
    exact hp

 theorem homSandwich_restrict {m : ℕ} {Y : CMfd.{0} m} {P Q : MarkedIdeal m Y}
    (h : HomSandwich P Q) (U : Opens Y) :
    HomSandwich (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P)
      (MarkedIdeal.pullback (Subtype.val : U → Y) Q) := by
  obtain ⟨r,hP⟩ := h.inv
  have hHcoh := isCoherent_homMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  refine ⟨⟨r, isInvDomain_pullback_val U hP⟩, isCoherent_pullback contMDiff_subtype_val h.coh, ?_, ?_, h.d, ?_, ?_⟩
  · change (Subtype.val : U → Y) ⁻¹' P.N = (Subtype.val : U → Y) ⁻¹' Q.N
    rw [h.N]
  · change P.E.map _ = Q.E.map _
    rw [h.E]
  · exact HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe contMDiff_subtype_val (fun _ hz => hz)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem h.coh hg) h.low
  · have hp : RestrictLe ((Subtype.val : U → Y) ⁻¹' P.N)
        (GermIdeal.pullback (m := m) (Subtype.val : U → Y) Q.ideal)
        (GermIdeal.pullback (m := m) (Subtype.val : U → Y) (homMarkedAlong P).ideal) :=
      HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe contMDiff_subtype_val (fun _ hz => hz)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hHcoh hg) h.high
    have heq := congrArg (fun A => A.ideal)
      (pullback_val_homMarkedAlong U P hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N hP.one_le_d)
    change GermIdeal.pullback (m := m) (Subtype.val : U → Y) (homMarkedAlong P).ideal =
      (homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → Y) P)).ideal at heq
    rw [heq] at hp
    exact hp

 theorem homSandwich_stable (κ : Kinds) :
    IsLocStable.{0} κ (fun {m} {Y} P Q => HomSandwich (m := m) (Y := Y) P Q) where
  E_eq h := h.E.symm
  cosupp_eq h := homSandwich_cosupp h
  controlled := by
    intro m Y P Q h C Z π hπ hC
    exact homSandwich_step h C π hπ hC
  projection := by
    intro hp m Y P Q h
    exact homSandwich_projection h
  restrict := by
    intro m Y P Q h U
    exact homSandwich_restrict h U

 theorem hom_local_any_boundary {n : ℕ} {X : CMfd.{0} n} {r : ℕ}
    (P : MarkedIdeal n X) (hP : IsInvDomain r P) : LocWPEquiv P (homMarkedAlong P) := by
  apply LocEquiv.of_isLocStable (homSandwich_stable Kinds.wp) rfl
  have hHcoh := isCoherent_homMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  refine ⟨⟨r,hP⟩,hHcoh,rfl,rfl,rfl,?_,?_⟩
  · exact restrictLe_of_le hHcoh (le_homogenizedIdealAlong
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg) hP.one_le_d)
  · exact DerivativeIdealAlongTransform.restrictLe_refl (fun _ _ hg => hg.1)

 theorem hom_isInvDomain {n : ℕ} {X : CMfd.{0} n} {r : ℕ}
    (P : MarkedIdeal n X) (hP : IsInvDomain r P) : IsInvDomain r (homMarkedAlong P) where
  isWellFormed := ⟨hP.isWellFormed.isClosedSubmanifold_N,
    isCoherent_homMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N,
    hP.isWellFormed.isSNCDivisor, hP.isWellFormed.isTransverse⟩
  dimLE := hP.dimLE
  one_le_d := hP.one_le_d
  isNonzeroAlongAt := by
    intro x hx
    obtain ⟨f,hf,hfreq⟩ := hP.isNonzeroAlongAt x hx
    exact ⟨f, le_homogenizedIdealAlong
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg)
      hP.one_le_d x f hf, hfreq⟩

 theorem bar_local_any_boundary {n : ℕ} {X : CMfd.{0} n} {r : ℕ}
    (P : MarkedIdeal n X) (hP : IsInvDomain r P) : LocWPEquiv P (barMarked P) :=
  (hom_local_any_boundary P hP).trans
    (coefficient_local_any_boundary (homMarkedAlong P) (hom_isInvDomain P hP))

end
end Hironaka.HironakaG8HomStable
