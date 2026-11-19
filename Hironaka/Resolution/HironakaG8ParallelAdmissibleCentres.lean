import Hironaka.Resolution.HironakaG3RSimultaneousBlowup
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Resolution.HironakaResolutionSpace
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Resolution.HironakaStageCenters

/-! One physical marked TEST step at locally finite disjoint centres. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ParallelAdmissibleCentres
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantDriver
  HironakaG3RSimultaneousBlowup HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaResolutionSpace MarkedIdealOpenBiholomorphism

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- There is no common label requirement for the union of a locally
finite pairwise disjoint family of admissible centres. -/
theorem admissible_iUnion_of_locallyFinite_disjoint
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    {ι : Type*} (C : ι → Set X) (hLF : LocallyFinite C) (hDisj : Pairwise (Disjoint on C))
    (hC : ∀ i, M.IsAdmissibleCentre (C i)) :
    M.IsAdmissibleCentre (⋃ i, C i) := by
  have hHol := hol_of_isCoherent hI
  apply isAdmissibleCentre_of_forall_exists_opens hHol
  intro x
  by_cases hx : x ∈ ⋃ i, C i
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    obtain ⟨O,hO,hxO,hEq⟩ := exists_open_iUnion_inter_eq hLF (fun i => (hC i).1.1) hDisj hj
    let U : Opens X := ⟨O,hO⟩
    refine ⟨U,hxO,?_⟩
    have hTrace : (Subtype.val : U → X) ⁻¹' (⋃ i, C i) = (Subtype.val : U → X) ⁻¹' C j := by
      ext z
      constructor
      · intro hz
        have hz' : z.val ∈ (⋃ i, C i) ∩ O := ⟨hz,z.property⟩
        rw [hEq] at hz'
        exact hz'.1
      · exact fun hz => mem_iUnion.mpr ⟨j,hz⟩
    rw [hTrace]
    exact IsAdmissibleCentre.pullback_val hHol (hC j) U
  · let U : Opens X := ⟨(⋃ i, C i)ᶜ,(hLF.isClosed_iUnion (fun i => (hC i).1.1)).isOpen_compl⟩
    refine ⟨U,hx,?_⟩
    have hTrace : (Subtype.val : U → X) ⁻¹' (⋃ i, C i) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun z => z.property
    rw [hTrace]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- A locally finite disjoint family of admissible singular centres on the
actual current stage advances the original marked TEST by one real step. -/
theorem exists_parallel_singular_test_step
    (M : MarkedIdeal n X) (W : Set X) (P : BlowupTower X Y)
    (hTest : IsGeoTestTower M P)
    (hM : M.IsWellFormed)
    (hStages : StageCentres (fun T D => D ⊆ singularSet (n := n) (strictTransform n T.proj W)) P)
    {ι : Type*} (C : ι → Set Y) (hLF : LocallyFinite C) (hDisj : Pairwise (Disjoint on C))
    (hC : ∀ i, (geoTransformAlong M P).IsAdmissibleCentre (C i))
    (hSing : ∀ i, C i ⊆ singularSet (n := n) (strictTransform n P.proj W)) :
    ∃ (Z : CMfd.{0} n) (π : Z → Y) (hπ : IsBlowupAlong n (⋃ i, C i) π),
      IsGeoTestTower M (.step P (⋃ i, C i) π hπ) ∧
      StageCentres (fun T D => D ⊆ singularSet (n := n) (strictTransform n T.proj W))
        (.step P (⋃ i, C i) π hπ) := by
  have hI := (isWellFormed_geoTransformAlong hM P hTest).isCoherent
  have hInterior (i : ι) : interior (C i) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact disjoint_left.mp (disjoint_interior_singularSet (strictTransform n P.proj W))
      (interior_mono ((hSing i).trans (singularSet_subset _)) hx) (hSing i (interior_subset hx))
  obtain ⟨Z,tZ,cZ,mZ,π,hπ⟩ := exists_isBlowupAlong_iUnion hLF hDisj
    (fun i => (hC i).1) hInterior
  let : TopologicalSpace Z := tZ
  let : ChartedSpace (ComplexModel n) Z := cZ
  let : IsComplexManifold n Z := mZ
  let Z₀ : CMfd.{0} n := ⟨Z⟩
  let π₀ : Z₀ → Y := π
  have hπ₀ : IsBlowupAlong n (⋃ i, C i) π₀ := hπ
  refine ⟨Z₀,π₀,hπ₀,?_,⟨hStages,iUnion_subset hSing⟩⟩
  exact (isGeoTestTower_step_iff M P _ π₀ hπ₀).mpr
    ⟨hTest,admissible_iUnion_of_locallyFinite_disjoint _ hI C hLF hDisj hC⟩

end Hironaka.HironakaG8ParallelAdmissibleCentres
