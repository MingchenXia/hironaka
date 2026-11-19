import Hironaka.Resolution.HironakaG8DisjointMarkedSwap
import Hironaka.Resolution.HironakaG3RSimultaneousBlowup
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS

/-! Physical grouping of disjoint singular steps and the intrinsic label obstruction. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointCentreGrouping
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  HironakaEmbeddedAnalytic HironakaG8DisjointMarkedSwap HironakaG3RSimultaneousBlowup
  HironakaStageCenters HironakaLocalPrincipalization ResolutionInvariantDriver
  MarkedIdealOperationsAlong.MarkedIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualBlowupOffCentreIntrinsicHS

variable {n : ℕ} {X Y Z : CMfd.{0} n}

theorem admissible_union_of_disjoint
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) {C D : Set X}
    (hC : M.IsAdmissibleCentre C) (hD : M.IsAdmissibleCentre D) (hCD : Disjoint C D) :
    M.IsAdmissibleCentre (C ∪ D) := by
  have hHol := hol_of_isCoherent hM.isCoherent
  apply isAdmissibleCentre_of_forall_exists_opens hHol
  intro x
  by_cases hx : x ∈ C
  · let U : Opens X := ⟨Dᶜ,hD.1.1.isOpen_compl⟩
    refine ⟨U,fun hd => disjoint_left.mp hCD hx hd,?_⟩
    have hTrace : (Subtype.val : U → X) ⁻¹' (C ∪ D) = (Subtype.val : U → X) ⁻¹' C := by
      ext z
      exact ⟨fun h => h.resolve_right z.property,Or.inl⟩
    rw [hTrace]
    exact IsAdmissibleCentre.pullback_val hHol hC U
  · let U : Opens X := ⟨Cᶜ,hC.1.1.isOpen_compl⟩
    refine ⟨U,hx,?_⟩
    have hTrace : (Subtype.val : U → X) ⁻¹' (C ∪ D) = (Subtype.val : U → X) ⁻¹' D := by
      ext z
      exact ⟨fun h => h.resolve_left z.property,Or.inr⟩
    rw [hTrace]
    exact IsAdmissibleCentre.pullback_val hHol hD U

/-- Two actual projected-disjoint TEST/singular steps can be grouped into
one genuine blowup. Its total map is literally the old composite. -/
theorem group_disjoint_actual_steps
    (A : Set X) (hA : IsClosed A) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C : Set X} {D : Set Y} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q)
    (hCD : Disjoint C (π '' D))
    (hTest : IsGeoTestTower M (.step (.step .refl C π hπ) D q hq))
    (hCSing : C ⊆ singularSet (n := n) A)
    (hDSing : D ⊆ singularSet (n := n) (strictTransform n π A)) :
    ∃ h : IsBlowupAlong n (C ∪ π '' D) (π ∘ q),
      IsGeoTestTower M (.step .refl (C ∪ π '' D) (π ∘ q) h) ∧
      C ∪ π '' D ⊆ singularSet (n := n) A := by
  let F := π '' D
  have hF : π ⁻¹' F = D := preimage_image_eq_of_disjoint_centre hπ D hCD
  have hq' : IsBlowupAlong n (π ⁻¹' F) q := hF.symm ▸ hq
  have hInterior : interior F = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y,rfl⟩ := surjective_of_isBlowupAlong hπ x
    have hOpen : IsOpen (π ⁻¹' interior F) := isOpen_interior.preimage hπ.contMDiff.continuous
    have hSub : π ⁻¹' interior F ⊆ D := (preimage_mono interior_subset).trans hF.subset
    have hy := (interior_maximal hSub hOpen) hx
    rw [hq.2.1] at hy
    exact hy
  obtain ⟨hFirst,hSecond⟩ := (isGeoTestTower_step_iff M _ _ _ hq).mp hTest
  have hC := ((isGeoTestTower_step_iff M _ _ _ hπ).mp hFirst).2
  have hSecond' : (M.geoTransform C π).IsAdmissibleCentre (π ⁻¹' F) := by
    rw [hF]
    exact hSecond
  have hD := admissible_of_disjoint_preimage M hM hπ hCD hSecond'
  let hπq := isBlowupAlong_union_comp hπ hD.1 hInterior hCD hq'
  refine ⟨hπq,(isGeoTestTower_step_iff M _ _ _ hπq).mpr
    ⟨trivial,admissible_union_of_disjoint M hM hC hD hCD⟩,?_⟩
  refine union_subset hCSing ?_
  rintro _ ⟨y,hy,rfl⟩
  exact (singularSet_at_disjoint_second_centre hπ hA hCD
    (show y ∈ π ⁻¹' F from ⟨y,hy,rfl⟩)).mp (hDSing hy)

/-- The two intrinsic labels read on the literal grouped centre are the
labels of the two actual old steps. Distinct occupied labels exclude any
single constant intrinsic label for the grouped centre. -/
theorem grouped_centre_profile_partition
    (A : Set X) (hA : IsComplexAnalyticSubset (n := n) A)
    {C : Set X} {D : Set Y} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCD : Disjoint C (π '' D)) (HC HD : ℕ → ℕ)
    (hC : ∀ x ∈ C, (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) A) x ℓ) = HC)
    (hD : ∀ y ∈ D, (fun ℓ => hilbertSamuelAt
      (vanishingIdeal (n := n) (strictTransform n π A)) y ℓ) = HD) :
    (∀ x ∈ π '' D, (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) A) x ℓ) = HD) ∧
    (C.Nonempty → D.Nonempty → HC ≠ HD →
      ¬ ∃ H : ℕ → ℕ, ∀ x ∈ C ∪ π '' D,
        (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) A) x ℓ) = H) := by
  have hPull : ∀ x ∈ π '' D, (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) A) x ℓ) = HD := by
    rintro _ ⟨y,hy,rfl⟩
    have hyOut : π y ∉ C := fun hx => disjoint_left.mp hCD hx ⟨y,hy,rfl⟩
    exact (funext (hilbertSamuelAt_actual_strict_blowup_off_centre hπ hA y hyOut)).symm.trans (hD y hy)
  refine ⟨hPull,?_⟩
  rintro ⟨x,hx⟩ ⟨y,hy⟩ hNe ⟨H,hH⟩
  have hxH := hH x (Or.inl hx)
  have hyH := hH (π y) (Or.inr ⟨y,hy,rfl⟩)
  exact hNe ((hC x hx).symm.trans (hxH.trans (hyH.symm.trans (hPull (π y) ⟨y,hy,rfl⟩))))

end Hironaka.HironakaG8DisjointCentreGrouping
