import Hironaka.Resolution.HironakaG8SubmersionSurfaceResolution
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalLocallyFiniteHistory
import Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CartesianSingularPrefix

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters NormalCrossings
  HironakaG8SubmersionSingularHistory HironakaG8SingularTestBoundaryTransfer
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionOriginalLocallyFiniteHistory
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSpec ResolutionInvariantSeq

variable {n m : ℕ} {X D : CMfd.{0} n} {Y D' : CMfd.{0} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private abbrev original {r : ℕ} {A : CMfd.{0} r} (W : Set A) (E : List (Set A)) :
    MarkedIdeal r A := ⟨univ,E,vanishingIdeal (n := r) W,1⟩

/-- The Cartesian square gives equality of projected centre images,
including the reverse inclusion over every source point. -/
theorem projected_centre_image_eq (h : IsActualTowerPullback f Q T g) (C : Set D) :
    Q.proj '' (g ⁻¹' C) = f ⁻¹' (T.proj '' C) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨g x,hx,h.proj_comm x⟩
  · rintro ⟨z,hz,he⟩
    let A := CMfd.of (n := 0) (ComplexModel 0)
    obtain ⟨w,hw,_⟩ := h.universal 0 A (fun _ => y) (fun _ => z)
      contMDiff_const contMDiff_const (fun _ => he.symm)
    refine ⟨w 0,?_,hw.2.1 0⟩
    change g (w 0) ∈ C
    simpa only [hw.2.2 0] using hz

/-- Every already chosen Cartesian prefix transfers the entire singular
history and original mark-one TEST, with its literal input boundary. -/
theorem pulled_singular_prefix_test (h : IsActualTowerPullback f Q T g)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hTest : IsGeoTestTower (original W E) T) :
    StageCentres (fun P C => C ⊆ singularSet (n := m)
      (strictTransform m P.proj (f ⁻¹' W))) Q ∧
    IsGeoTestTower (original (f ⁻¹' W) (E.map (f ⁻¹' ·))) Q := by
  let M := original W E
  have hM : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW,
      hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hQStage := actual_pullback_singular_stages hf W hW h hStage
  have hY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf.contMDiff hW
  have hYE := isSNCDivisor_preimage_submersion hf E hE
  exact ⟨hQStage,singular_auxiliary_test_is_original_test (f ⁻¹' W) hY _ hYE
    (markedPullback (m := m) f M) rfl Q (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary h M hM hTest).1 hQStage⟩

/-- Adjoin the next actual blowup to the supplied source prefix. The
existing prefix is kept literally, and the new centre projects to the
inverse image of the base centre's footprint. -/
theorem extend_pulled_singular_prefix (h : IsActualTowerPullback f Q T g)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (β : SmoothBlowupChoices.{0} m)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    {Z : CMfd.{0} n} (C : Set D) (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hStage : StageCentres (fun P L => L ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (.step T C π hπ))
    (hTest : IsGeoTestTower (original W E) (.step T C π hπ)) :
    ∃ (Z' : CMfd.{0} m) (ρ : Z' → D') (hρ : IsBlowupAlong m (g ⁻¹' C) ρ)
      (g' : Z' → Z),
      let Q' := BlowupTower.step Q (g ⁻¹' C) ρ hρ
      IsActualTowerPullback f Q' (.step T C π hπ) g' ∧
      StageCentres (fun P L => L ⊆ singularSet (n := m)
        (strictTransform m P.proj (f ⁻¹' W))) Q' ∧
      IsGeoTestTower (original (f ⁻¹' W) (E.map (f ⁻¹' ·))) Q' ∧
      Q.proj '' (g ⁻¹' C) = f ⁻¹' (T.proj '' C) := by
  have hC := actual_source_centre h.isSubmersion hπ
  obtain ⟨Z',ρ,hρ⟩ := β.choose hC.1 hC.2
  have hPull := IsActualTowerPullback.step h h.isSubmersion hπ hρ
  obtain ⟨hSing,hOrig⟩ := pulled_singular_prefix_test hPull hf W hW E hE hStage hTest
  exact ⟨Z',ρ,hρ,_,hPull,hSing,hOrig,projected_centre_image_eq h C⟩

private theorem singleton_hits_iff {A B : Type*} (p : A → B) (C : Set A) (x : B) :
    (C ∩ p ⁻¹' {x}).Nonempty ↔ x ∈ p '' C := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact ⟨y,hy,he⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y,hy,rfl⟩

/-- Exact singleton counts are preserved by a Cartesian tower. -/
theorem pulled_singleton_centre_count (h : IsActualTowerPullback f Q T g) (y : Y) :
    countCentresMeeting {y} Q = countCentresMeeting {f y} T := by
  classical
  induction h with
  | refl => rfl
  | @step A B Z' Z Q T g h hg C π hπ ρ hρ ih =>
    simp only [countCentresMeeting,ih,singleton_hits_iff,projected_centre_image_eq h C,mem_preimage]

/-- Each chronological projected source centre is exactly the inverse
image of the corresponding projected base centre. -/
theorem actualSourceGrowing_centreImage_eq (β : SmoothBlowupChoices.{0} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (s : GrowingSeq X) (i : ℕ) :
    centreImage (actualSourceGrowing β hf s) i = f ⁻¹' centreImage s i := by
  classical
  ext y
  let q := actualSourceGrowing β hf s
  have hCount (j : ℕ) : countCentresMeeting {y} (q.stage j).2 =
      countCentresMeeting {f y} (s.stage j).2 :=
    pulled_singleton_centre_count (chosenActualTower β hf (s.stage j).2).2.2.property y
  have h := hCount (i+1)
  rw [countCentresMeeting_step, countCentresMeeting_step, hCount i] at h
  have hIf := Nat.add_left_cancel h
  simp only [inter_singleton_nonempty] at hIf
  change y ∈ centreImage q i ↔ f y ∈ centreImage s i
  by_cases hq : y ∈ centreImage q i <;> by_cases hs : f y ∈ centreImage s i <;>
    simp_all

/-- Actual growing pullbacks preserve every original TEST prefix and
literal intrinsic centre, and local finiteness follows by continuity. -/
theorem actualSourceGrowing_singular_test_and_footprints
    (β : SmoothBlowupChoices.{0} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj W)) (s.stage i).2)
    (hTest : ∀ i, IsGeoTestTower (original W E) (s.stage i).2) :
    let q := actualSourceGrowing β hf s
    (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := m)
        (strictTransform m P.proj (f ⁻¹' W))) (q.stage i).2 ∧
      IsGeoTestTower (original (f ⁻¹' W) (E.map (f ⁻¹' ·))) (q.stage i).2) ∧
    (∀ i, centreImage q i = f ⁻¹' centreImage s i) ∧
    LocallyFinite (centreImage q) := by
  intro q
  have hEq := actualSourceGrowing_centreImage_eq β hf s
  refine ⟨fun i => pulled_singular_prefix_test
    (chosenActualTower β hf (s.stage i).2).2.2.property hf W hW E hE (hStage i) (hTest i),
    hEq,?_⟩
  rw [show centreImage q = (fun i => f ⁻¹' centreImage s i) from funext hEq]
  exact hLF.preimage_continuous hf.contMDiff.continuous

#print axioms actualSourceGrowing_singular_test_and_footprints
#print axioms actualSourceGrowing_centreImage_eq
#print axioms extend_pulled_singular_prefix
#print axioms projected_centre_image_eq
end Hironaka.HironakaG8CartesianSingularPrefix
