import Hironaka.Analytic.Unibranch.HironakaG11StrictTransformTowers
import Hironaka.Analytic.Unibranch.IntrinsicAnalyticCentreFiniteType
import Hironaka.Resolution.HironakaG1CanonicalPrefixCentreTransport
import Hironaka.Resolution.HironakaContainedCentrePulledIdeal

/-!
# The whole intrinsic canonical centre ideal at an actual finite stage

Initial whole presentation class data derive record transport. Genuine initial
native point presentations derive incidence at the SAME current prefix. The
existing stage centre engine then constructs the actual compatible support;
the held intrinsic ideal dictionaries provide its full native ideal comparisons.
No input supplies RecordsTransport, centre compatibility or a global ideal.

Blueprint FIRST: `hironaka-g1-canonical-stage-centre-ideal.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageCentreIdeal

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalPrefixCentreTransport
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealStalk HironakaActualAnalyticSubspace
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))

/-- Only ordinary INITIAL whole presentation class data on the actual native
overlap maps. There is no current/future value, centre, history or gluing field. -/
def InitialClassData : Prop :=
  ∀ i j (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U),
    mapAdm w i j U U' Φ →
      LocWPEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → (w i).ambient) (M i)))
        (MarkedIdeal.pullback (Subtype.val : U' → (w j).ambient) (M j)) ∧
      (M i).d = (M j).d ∧
      (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → (w i).ambient) (M i))).E =
        (MarkedIdeal.pullback (Subtype.val : U' → (w j).ambient) (M j)).E ∧
      SameCarrierDim
        (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → (w i).ambient) (M i)))
        (MarkedIdeal.pullback (Subtype.val : U' → (w j).ambient) (M j)) ∧
      ExpAgree
        (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → (w i).ambient) (M i)))
        (MarkedIdeal.pullback (Subtype.val : U' → (w j).ambient) (M j))

variable (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)

include hD hClass in
/-- Genuine class functoriality derives the entire record-transport premise
used by the existing current-stage engine, with the full initial boundaries. -/
theorem recordsTransport : RecordsTransport B.toResolutionInvariant M (mapAdm w) := by
  intro i j U U' Φ hadm Y Y' T T' hcan hcan' χ hiso p
  obtain ⟨hEq, hd, hE, hdim, hexp⟩ := hClass i j U U' Φ hadm
  exact cosupp_value_transport B U U' Φ (hD i) (hD j) hEq hd hE hdim hexp hcan hcan' χ hiso p

variable (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))

include hState in
private theorem initial_cosupp_subset (i : ι) : (M i).cosupp ⊆ (w i).carrier := by
  exact ((hState i).hsTowerState (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i))
    (by trivial)).2.1

variable (K : ∀ i, Set (w i).ambient)
  (hCover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)

include hD hState in
private theorem current_cosupp_subset (i : ι) : rcos M s.T i ⊆ xs.carrier i := by
  rw [xs.carrier_eq i]
  exact ((hState i).hsTowerState (s.T i).2
    (B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (hD i) (s.T i).2
      (s.canonical i))).2.1

include hD hState in
private theorem current_centre_subset (i : ι) :
    gcentre B.toResolutionInvariant M K s.T i ⊆ xs.carrier i := by
  intro y hy
  exact current_cosupp_subset w M B hD H hState s xs i hy.1

/-- The actual local canonical centres, with compatibility and current
carrier incidence internally derived from the genuine initial presentations. -/
def localCentres : ManifoldSmoothCentres xs.Y ι :=
  xs.centres hD (initial_cosupp_subset w M H hState) hCover
    (recordsTransport w M B hD hClass) s (current_centre_subset w M B hD H hState K s xs)

/-- The internally constructed SAME canonical support in the current original space. -/
def support : Set xs.Y.obj.left := (localCentres w M B hD hClass H hState K hCover s xs).support

private theorem compatible : (localCentres w M B hD hClass H hState K hCover s xs).Compatible :=
  xs.centres_compatible hD (initial_cosupp_subset w M H hState) hCover
    (recordsTransport w M B hD hClass) s (current_centre_subset w M B hD H hState K s xs)

variable [Finite ι] (hK : ∀ i, IsCompact (K i))

include hK in
/-- The SAME canonical support is closed by actual compact footprint control. -/
theorem support_isClosed : IsClosed (support w M B hD hClass H hState K hCover s xs) :=
  xs.isClosed_support hD (initial_cosupp_subset w M H hState) hCover
    (recordsTransport w M B hD hClass) hK s (current_centre_subset w M B hD H hState K s xs)

include hK in
/-- Actual analytic gluing of the SAME current canonical centres. -/
theorem support_isAnalyticSubset :
    xs.Y.IsAnalyticSubset (support w M B hD hClass H hState K hCover s xs) :=
  (localCentres w M B hD hClass H hState K hCover s xs).isAnalyticSubset_support
    (compatible w M B hD hClass H hState K hCover s xs)
    (support_isClosed w M B hD hClass H hState K hCover s xs hK)

include hK in
/-- The ENTIRE intrinsic ideal of the constructed current canonical centre
is genuinely finite type on the original source, not supplied by a caller. -/
theorem centreIdeal_isFiniteType :
    (intrinsicReducedCentreIdealModule xs.Y.obj.left
      (support w M B hD hClass H hState K hCover s xs)).IsFiniteType :=
  IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType xs.Y _
    (support_isAnalyticSubset w M B hD hClass H hState K hCover s xs hK)

omit [Finite ι]

local notation "F" => localCentres w M B hD hClass H hState K hCover s xs
local notation "C" => support w M B hD hClass H hState K hCover s xs
local notation "J" => intrinsicReducedCentreIdealModule xs.Y.obj.left C
local notation "bJ" => intrinsicReducedCentreIdealInclusion xs.Y.obj.left C

include hD hClass hState hCover in
/-- The coherent ambient ideal of the SAME actual local canonical centre. -/
theorem localCentreIdeal_isCoherent (i : ι) :
    (vanishingIdeal (n := N) (gcentre B.toResolutionInvariant M K s.T i)).IsCoherent :=
  VanishingIdealCoherent.isCoherent_vanishingIdeal
    ((gnextMap_isBlowup hD (initial_cosupp_subset w M H hState) hCover (adm_exists_map w)
      (recordsTransport w M B hD hClass) s i).1)

/-- The inverse image of the constructed support is the SAME canonical trace. -/
theorem window_trace_eq (i : ι) :
    (xs.map i).hom.left.base ⁻¹' C = (F).trace i :=
  (F).preimage_support (compatible w M B hD hClass H hState K hCover s xs) i

/-- The actual native unit submodules agree in their full original scalars. -/
theorem window_submodule_eq (i : ι) :
    nativePulledIdealSubmodule (xs.map i).hom.left J bJ =
      intrinsicReducedCentreSubmodule
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left ((F).trace i) := by
  have : LocallyRingedSpace.IsOpenImmersion (xs.map i).hom.left := xs.isOpenImmersion i
  rw [openImmersion_pulled_submodule_eq]
  exact congrArg (intrinsicReducedCentreSubmodule
    (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left)
      (window_trace_eq w M B hD hClass H hState K hCover s xs i)

/-- Full original-window pullback comparison of the ENTIRE global ideal. -/
def windowIdealIso (i : ι) :
    nativePulledIdealModule (xs.map i).hom.left J bJ ≅
      intrinsicReducedCentreIdealModule
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left ((F).trace i) := by
  let h := window_submodule_eq w M B hD hClass H hState K hCover s xs i
  exact
    { hom := ⟨PresheafOfModules.Submodule.homOfLE h.le⟩
      inv := ⟨PresheafOfModules.Submodule.homOfLE h.ge⟩
      hom_inv_id := by ext V z; rfl
      inv_hom_id := by ext V z; rfl }

/-- The FULL forward inclusion/scalar triangle on the actual original window. -/
theorem windowIdealIso_hom_comp_inclusion (i : ι) :
    (windowIdealIso w M B hD hClass H hState K hCover s xs i).hom ≫
      intrinsicReducedCentreIdealInclusion
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left ((F).trace i) =
      nativePulledIdealInclusion (xs.map i).hom.left J bJ := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι
    (window_submodule_eq w M B hD hClass H hState K hCover s xs i).le

/-- The FULL inverse inclusion/scalar triangle on that SAME original window. -/
theorem windowIdealIso_inv_comp_inclusion (i : ι) :
    (windowIdealIso w M B hD hClass H hState K hCover s xs i).inv ≫
      nativePulledIdealInclusion (xs.map i).hom.left J bJ =
      intrinsicReducedCentreIdealInclusion
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left ((F).trace i) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι
    (window_submodule_eq w M B hD hClass H hState K hCover s xs i).ge

/-- EVERY original section on EVERY actual window open has the same ideal. -/
theorem window_sectionIdeal_eq (i : ι)
    (V : Opens (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left.toTopCat) :
    nativePulledIdealSectionIdeal (xs.map i).hom.left J bJ V =
      intrinsicReducedCentreSectionIdeal
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left ((F).trace i) V := by
  have : LocallyRingedSpace.IsOpenImmersion (xs.map i).hom.left := xs.isOpenImmersion i
  rw [openImmersion_pulled_sectionIdeal_eq]
  exact congrArg (fun D => intrinsicReducedCentreSectionIdeal
    (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left D V)
      (window_trace_eq w M B hD hClass H hState K hCover s xs i)

/-- The entire original stalk-image ideal, with no support-only comparison. -/
theorem window_stalkIdeal_eq (i : ι)
    (p : (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left) :
    nativePulledIdealStalkIdeal (xs.map i).hom.left J bJ p =
      intrinsicCentreStalkRange
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left ((F).trace i) p := by
  have : LocallyRingedSpace.IsOpenImmersion (xs.map i).hom.left := xs.isOpenImmersion i
  rw [openImmersion_pulled_stalkIdeal_eq]
  exact congrArg (fun D => intrinsicCentreStalkRange
    (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left D p)
      (window_trace_eq w M B hD hClass H hState K hCover s xs i)

/-- The SAME stalk image is the entire ambient canonical vanishing-ideal
image under the original closed-model inclusion, including every generator. -/
theorem window_ambient_stalkIdeal_eq (i : ι)
    (p : (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left) :
    nativePulledIdealStalkIdeal (xs.map i).hom.left J bJ p =
      Ideal.map ((actualSubspaceInclusion (n := N) (xs.carrier i)).stalkMap p).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := N)
          (gcentre B.toResolutionInvariant M K s.T i)) p.val) := by
  rw [window_stalkIdeal_eq w M B hD hClass H hState K hCover s xs i p]
  exact intrinsicReducedCentreStalkInclusion_range_model
    (current_centre_subset w M B hD H hState K s xs i) p

end
end Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageCentreIdeal
