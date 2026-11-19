import Hironaka.Resolution.HironakaG8SingularFootprintExtension
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaG3FiniteDisjointTowerMerge
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixTests
import Hironaka.Resolution.HironakaG3EmptyAwareSymmetry
set_option autoImplicit false
open Set Filter Function Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8FiniteSingularTowerMerge
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaResolutionSpaceLocal
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaG3EmptyAwareHistory
  HironakaG8SingularFootprintExtension HironakaG8EmptyAwareTestTransport
  HironakaG3FiniteDisjointTowerMerge HironakaSharpActualCurveGlobalPrefixTests
  MarkedIdealTowerTransport ResolutionInvariantExt
  HironakaNormalCrossingsSeparationChoiceComparison HironakaHolomorphicJetChartInvariance
  HironakaActualVanishingIntrinsicHSTransport

/-- Singular-centre positions restrict to the actual tower over any open. -/
theorem singular_stages_restrict {n : ℕ} {X : CMfd.{0} n} (W : Set X) (U : Opens X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hs => by
      refine ⟨singular_stages_restrict W U T hs.1,?_⟩
      intro c hc
      have hcS := hs.2 hc
      rw [strictTransform_restricted_tower U T W, singularSet_preimage_val]
      exact hcS

/-- The literal singular-centre condition is local on an actual open cover. -/
theorem singular_stages_of_open_cover {n : ℕ} {X : CMfd.{0} n} {J : Type}
    (W : Set X) (U : J → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (restrict (U i) T)) →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hs => by
      refine ⟨singular_stages_of_open_cover W U hcover T (fun i => (hs i).1),?_⟩
      intro c hc
      obtain ⟨i,hi⟩ := hcover (T.proj c)
      let z : openPreimage T (U i) := ⟨c,hi⟩
      have hz := (hs i).2 (show z ∈ (Subtype.val : openPreimage T (U i) → _) ⁻¹' C from hc)
      rw [strictTransform_restricted_tower (U i) T W, singularSet_preimage_val] at hz
      exact hz

/-- Empty restricted towers satisfy the singular-centre condition. -/
theorem singular_stages_of_empty {n : ℕ} {X : CMfd.{0} n} (W : Set X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), ResolutionInvariantExt.IsEmptyTower T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, he => by
      refine ⟨singular_stages_of_empty W T he.1,?_⟩
      rw [he.2]
      exact empty_subset _

/-- Finitely many actual disjoint-footprint test towers with singular centres
merge to one physical global test tower retaining all singular positions. -/
theorem finite_disjoint_singular_test_towers_merge {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (W : Set X) (hW : IsClosed W)
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i)) (U : ι → Opens X)
    (hFU : ∀ i, F i ⊆ U i) (hdisj : ∀ i j, i ≠ j → Disjoint (U i : Set X) (F j))
    (Y : ι → CMfd.{0} n) (T : ∀ i, BlowupTower X (Y i))
    (hOver : ∀ i, CentresOver (F i) (T i))
    (hTest : ∀ i, IsGeoTestTower M (T i))
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (T i))
    (s : Finset ι) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z),
      IsGeoTestTower M Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver (finiteSupport F s) Q ∧
      ∀ i ∈ s, ∃ φ : (CMfd.of (n := n) (openPreimage Q (U i))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          (CMfd.of (n := n) (openPreimage (T i) (U i))),
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (U i)) ∞)
          (restrict (U i) Q) (restrict (U i) (T i)) φ := by
  obtain ⟨Z,Q,hQ,hCompare⟩ := finite_disjoint_towers_physical_comparisons F hF U hFU hdisj Y T hOver s
  let K := finiteSupport F s
  have hK : IsClosed K := s.finite_toSet.isClosed_biUnion (fun i _ => hF i)
  let V : Opens X := ⟨Kᶜ,hK.isOpen_compl⟩
  let C : Option {i // i ∈ s} → Opens X := fun j => match j with
    | none => V
    | some i => U i.val
  have hcover : ∀ x : X, ∃ j, x ∈ C j := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
      exact ⟨some ⟨i,hi⟩,hFU i hxi⟩
    · exact ⟨none,hx⟩
  have hLocal (i : ι) (hi : i ∈ s) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (restrict (U i) Q) ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (restrict (U i) Q) := by
    obtain ⟨φ,hφ⟩ := hCompare i hi
    let A : MarkedIdeal n (CMfd.of (n := n) (U i)) := MarkedIdeal.pullback (Subtype.val : U i → X) M
    have hA : A.IsWellFormed := IsWellFormed.pullback_val hM (U i)
    have ht := isGeoTestTower_restrict (U i) hM.isClosedSubmanifold_N hM.isCoherent (T i) (hTest i)
    have heq := isGeoTestTower_iff_of_emptyAware (n := n)
      (X₁ := CMfd.of (n := n) (U i)) (X₂ := CMfd.of (n := n) (U i))
      (Y₁ := CMfd.of (n := n) (openPreimage Q (U i)))
      (Y₂ := CMfd.of (n := n) (openPreimage (T i) (U i)))
      (T₁ := restrict (U i) Q) (T₂ := restrict (U i) (T i)) (ψ := φ) A hA
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (U i)) ∞) hφ
    simp only [Diffeomorph.coe_refl] at heq
    rw [ContactCanonicalAlong.pullback_id A hA.isCoherent] at heq
    have hs := singular_stages_restrict W (U i) (T i) (hStage i)
    have hs' := singular_stages_of_emptyAware (n := n)
      (X' := CMfd.of (n := n) (U i)) (X := CMfd.of (n := n) (U i))
      (T' := restrict (U i) (T i)) (T := restrict (U i) Q) (χ := φ.symm)
      ((Subtype.val : U i → X) ⁻¹' W) (hW.preimage continuous_subtype_val)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (U i)) ∞).symm
      (HironakaG3EmptyAwareSymmetry.symm hφ)
    simp only [Diffeomorph.symm_refl, Diffeomorph.coe_refl, preimage_id] at hs'
    exact ⟨heq.mpr ht,hs' hs⟩
  have hEmpty : ResolutionInvariantExt.IsEmptyTower (restrict V Q) :=
    isEmptyTower_restrict_of_centresOver V (disjoint_compl_left : Disjoint (Kᶜ) K) Q hQ
  have hLocalTest : ∀ j, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : C j → X) M) (restrict (C j) Q) := by
    intro j
    cases j with
    | none => exact ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower _ _ hEmpty
    | some i => exact (hLocal i.val i.property).1
  have hLocalStage : ∀ j, StageCentres (fun P C' => C' ⊆ singularSet (n := n)
        (strictTransform n P.proj ((Subtype.val : C j → X) ⁻¹' W))) (restrict (C j) Q) := by
    intro j
    cases j with
    | none => exact singular_stages_of_empty _ _ hEmpty
    | some i => exact (hLocal i.val i.property).2
  exact ⟨Z,Q,isGeoTestTower_of_open_cover M hM.isClosedSubmanifold_N hM.isCoherent C hcover Q hLocalTest,
    singular_stages_of_open_cover W C hcover Q hLocalStage,hQ,hCompare⟩

/-- The actual endpoint comparison transports the whole local
Hilbert--Samuel profile drop from the supplied tower to the merged tower. -/
theorem profile_drop_of_emptyAware_open_overlap {n : ℕ} {X Y Z : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W) (U : Opens X) (H : ℕ → ℕ)
    (Q : BlowupTower X Y) (T : BlowupTower X Z)
    (φ : (CMfd.of (n := n) (openPreimage Q U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (CMfd.of (n := n) (openPreimage T U)))
    (hφ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U Q) (restrict U T) φ)
    (hDrop : ∀ z : openPreimage T U, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n T.proj W)) z.val ℓ ≤ H ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z.val ℓ < H ℓ) :
    ∀ y : openPreimage Q U, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n Q.proj W)) y.val ℓ ≤ H ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ < H ℓ := by
  have hst := strictTransform_preimage_of_square
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) φ
    (restrict U Q).contMDiff_proj (restrict U T).contMDiff_proj
    ((Subtype.val : U → X) ⁻¹' W) (hW.preimage continuous_subtype_val)
    (emptyAware_proj_comm hφ)
  simp only [Diffeomorph.coe_refl, preimage_id] at hst
  rw [strictTransform_restricted_tower U Q W, strictTransform_restricted_tower U T W] at hst
  intro y
  have hHS (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) (φ y).val ℓ := by
    calc
      _ = hilbertSamuelAt (vanishingIdeal (n := n)
          ((Subtype.val : openPreimage Q U → Y) ⁻¹' strictTransform n Q.proj W)) y ℓ :=
        (hilbertSamuelAt_vanishing_actual_open_any (openPreimage Q U) (strictTransform n Q.proj W) y ℓ).symm
      _ = hilbertSamuelAt (vanishingIdeal (n := n)
          (φ ⁻¹' ((Subtype.val : openPreimage T U → Z) ⁻¹' strictTransform n T.proj W))) y ℓ := by rw [hst]
      _ = hilbertSamuelAt (vanishingIdeal (n := n)
          ((Subtype.val : openPreimage T U → Z) ⁻¹' strictTransform n T.proj W)) (φ y) ℓ :=
        hilbertSamuelAt_vanishing_actual_biholomorphic_any φ _ y ℓ
      _ = _ := hilbertSamuelAt_vanishing_actual_open_any (openPreimage T U) (strictTransform n T.proj W) (φ y) ℓ
  obtain ⟨hle,ℓ,hlt⟩ := hDrop (φ y)
  exact ⟨fun ℓ => (hHS ℓ).symm ▸ hle ℓ,⟨ℓ,(hHS ℓ).symm ▸ hlt⟩⟩
end
end Hironaka.HironakaG8FiniteSingularTowerMerge
