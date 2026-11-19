import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
import Hironaka.Resolution.HironakaG8WholeSingularCentreTest
import Hironaka.MarkedIdeal.MarkedIdealEquivalence

/-! A TEST on an analytic subset of the singular locus induces a TEST
for the original carrier along the same physical towers. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SingularStratumTestLift

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaG8WholeSingularCentreTest MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal NormalCrossings
  HironakaAdmissibleCalculus

variable {n : ℕ} {X Y : CMfd.{0} n} {W A : Set X}

private abbrev original (V : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ,E,vanishingIdeal (n := n) V,1⟩

/-- The strict transform of a subset of the original singular locus
lies in the singular locus of the strict transform, along the same tower. -/
theorem strictTransform_stratum_subset_singular
    (f : Y → X) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hW : IsClosed W) (hA : A ⊆ singularSet (n := n) W) :
    strictTransform n f A ⊆ singularSet (n := n) (strictTransform n f W) := by
  change closure (f ⁻¹' A \ exceptionalLocus n f) ⊆ _
  apply closure_minimal _ (isClosed_singularSet isClosed_closure)
  rintro y ⟨hy,hyExc⟩
  obtain ⟨hyW,hySing⟩ := mem_singularSet_iff.mp (hA hy)
  have hOpen : IsOpen (exceptionalLocus n f)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hf
  have hRead : ∀ z ∈ (exceptionalLocus n f)ᶜ,
      z ∈ strictTransform n f W ↔ f z ∈ W := fun z hz =>
    mem_strictTransform_iff_of_notMem hf.continuous hW hz
  refine mem_singularSet_iff.mpr ⟨(hRead y hyExc).mpr hyW,?_⟩
  intro k hk
  exact hySing k (HironakaEmbeddedExceptional.regularAtDim_of_regularAtDim_preimage
    hf hyExc hOpen hyExc hRead hk)

/-- A whole TEST for the auxiliary stratum, with centres contained in its
current strict transform, is a singular-centred original TEST for W. -/
theorem test_of_singular_stratum_test
    (hW : IsComplexAnalyticSubset (n := n) W) (hA : A ⊆ singularSet (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower (original A E) T)
    (hCentres : StageCentres (fun P C => C ⊆ strictTransform n P.proj A) T) :
    IsGeoTestTower (original W E) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T := by
  induction T with
  | refl => exact ⟨trivial,trivial⟩
  | @step B D P C π hπ ih =>
    obtain ⟨hPrefix,hSing⟩ := ih hTest.1 hCentres.1
    have hCSing := hCentres.2.trans (strictTransform_stratum_subset_singular P.proj P.contMDiff_proj hW.isClosed hA)
    have hEq : (geoTransformAlong (original A E) P).E = (geoTransformAlong (original W E) P).E :=
      E_geoTransformAlong_eq (𝔪 := original A E) (𝔫 := original W E) rfl P
    have hNC : HasNormalCrossings n C (geoTransformAlong (original W E) P).E := by
      rw [← hEq]
      exact hTest.2.2.2
    exact ⟨⟨hPrefix,whole_singular_subcentre_admissible W hW E hE P hPrefix hSing
      hπ.1 hCSing hNC⟩,⟨hSing,hCSing⟩⟩

/-- Once a singular subvariety has been made smooth and meets the
accumulated boundary normally, its entire strict transform can be blown up
as the next step of the original TEST. -/
theorem exists_test_step_along_resolved_singular_stratum
    (hW : IsComplexAnalyticSubset (n := n) W) (hA : A ⊆ singularSet (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower (original A E) T)
    (hCentres : StageCentres (fun P C => C ⊆ strictTransform n P.proj A) T)
    (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj A))
    (hNC : HasNormalCrossings n (strictTransform n T.proj A) (geoTransformAlong (original A E) T).E) :
    ∃ (Z : CMfd.{0} n) (π : Z → Y)
      (hπ : IsBlowupAlong n (strictTransform n T.proj A) π),
      IsGeoTestTower (original W E) (.step T _ π hπ) ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (.step T _ π hπ) := by
  obtain ⟨hTestW,hStageW⟩ := test_of_singular_stratum_test hW hA E hE T hTest hCentres
  have hEq : (geoTransformAlong (original A E) T).E = (geoTransformAlong (original W E) T).E :=
    E_geoTransformAlong_eq (𝔪 := original A E) (𝔫 := original W E) rfl T
  exact exists_whole_singular_subcentre_test_step W hW E hE T hTestW hStageW
    hSmooth (strictTransform_stratum_subset_singular T.proj T.contMDiff_proj hW.isClosed hA) (hEq ▸ hNC)

open ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms

attribute [local instance] limitChartedSpace
local instance (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- The same locally finite growing TEST can be used for the original
carrier, and the transformed auxiliary stratum remains singular there. -/
theorem growing_test_of_singular_stratum_test
    (hW : IsComplexAnalyticSubset (n := n) W) (hA : A ⊆ singularSet (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hTest : ∀ i, IsGeoTestTower (original A E) (s.stage i).2)
    (hCentres : ∀ i, StageCentres (fun P C => C ⊆ strictTransform n P.proj A) (s.stage i).2) :
    (∀ i, IsGeoTestTower (original W E) (s.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (s.stage i).2) ∧
      strictTransform n (gluedProjection s hLF) A ⊆
        singularSet (n := n) (strictTransform n (gluedProjection s hLF) W) := by
  have hStage (i : ℕ) := test_of_singular_stratum_test hW hA E hE (s.stage i).2
    (hTest i) (hCentres i)
  exact ⟨fun i => (hStage i).1,fun i => (hStage i).2,
    strictTransform_stratum_subset_singular (Y := CMfd.of (n := n) (limitManifold s hLF))
      (gluedProjection s hLF) (gluedProjection_contMDiff s hLF) hW.isClosed hA⟩

end Hironaka.HironakaG8SingularStratumTestLift
