import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Resolution.HironakaLocalPrincipalization
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u w
namespace Hironaka.HironakaG8CompatibleLocalCentres
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen ResolutionInvariantSeq ResolutionDriver ResolutionInvariantDriver
  MaxLocusLocal
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X : CMfd.{u} n} {J : Type w}

/-- Union of the literal images of local centres. -/
def compatibleCentre (U : J → Opens X) (C : ∀ i, Set (U i)) : Set X :=
  ⋃ i, (Subtype.val : U i → X) '' C i

/-- If the supplied local centres agree on actual overlaps, the global union
restricts to exactly each supplied local centre. -/
theorem preimage_compatibleCentre (U : J → Opens X) (C : ∀ i, Set (U i))
    (hcompat : ∀ (i j : J) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x,hi⟩ : U i) ∈ C i ↔ (⟨x,hj⟩ : U j) ∈ C j) (i : J) :
    (Subtype.val : U i → X) ⁻¹' compatibleCentre U C = C i := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,y,hy,he⟩ := mem_iUnion.mp hx
    have hxj : (x : X) ∈ U j := by simpa only [he] using y.property
    have hyx : y = (⟨x,hxj⟩ : U j) := Subtype.ext he
    exact (hcompat i j x x.property hxj).mpr (by simpa only [hyx] using hy)
  · intro hx
    exact mem_iUnion.mpr ⟨i,x,hx,rfl⟩

/-- Local admissibility for one actual global record glues across a cover;
the local centres can have been produced by different auxiliary records. -/
theorem compatibleCentre_admissible (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent)
    (U : J → Opens X) (C : ∀ i, Set (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hcompat : ∀ (i j : J) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x,hi⟩ : U i) ∈ C i ↔ (⟨x,hj⟩ : U j) ∈ C j)
    (hC : ∀ i, (MarkedIdeal.pullback (Subtype.val : U i → X) M).IsAdmissibleCentre (C i)) :
    M.IsAdmissibleCentre (compatibleCentre U C) := by
  apply isAdmissibleCentre_of_forall_exists_opens
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM hg)
  intro x
  obtain ⟨i,hi⟩ := hcover x
  refine ⟨U i,hi,?_⟩
  rw [preimage_compatibleCentre U C hcompat i]
  exact hC i

/-- The glued admissible centre admits an actual proper blowup, whose
restriction to each window has exactly the prescribed centre. -/
theorem exists_blowup_compatibleCentre {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (U : J → Opens X) (C : ∀ i, Set (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hcompat : ∀ (i j : J) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x,hi⟩ : U i) ∈ C i ↔ (⟨x,hj⟩ : U j) ∈ C j)
    (hC : ∀ i, (MarkedIdeal.pullback (Subtype.val : U i → X) M).IsAdmissibleCentre (C i)) :
    ∃ (Y : CMfd.{u} n) (π : Y → X) (_ : IsBlowupAlong n (compatibleCentre U C) π),
      IsProperMap π ∧ M.IsAdmissibleCentre (compatibleCentre U C) ∧
      ∀ i, (Subtype.val : U i → X) ⁻¹' compatibleCentre U C = C i := by
  have ha := compatibleCentre_admissible M hM.isWellFormed.isCoherent U C hcover hcompat hC
  have hint : interior (compatibleCentre U C)=∅ :=
    eq_empty_of_subset_empty ((interior_mono ha.2.1).trans (interior_cosupp_eq_empty hM).subset)
  obtain ⟨Y,π,hπ⟩ := exists_blowup (compatibleCentre U C) ha.1 hint
  exact ⟨Y,π,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,ha,
    fun i => preimage_compatibleCentre U C hcompat i⟩
end
end Hironaka.HironakaG8CompatibleLocalCentres
