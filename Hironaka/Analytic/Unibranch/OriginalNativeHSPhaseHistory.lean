import Hironaka.Analytic.Unibranch.HironakaG11PresReduction
import Hironaka.Analytic.Unibranch.SourceMorphismExt
import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial

/-! The SAME physical native history of one compact original HS phase.
The ordinary windows and common powers are constructed internally; the
invariant is fixed, including the literal ORIGINAL-family instance.
Blueprint FIRST: original-native-hs-phase-history.tex.
No outer algorithm or smooth/independent-presentation comparison is claimed. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSPhaseHistory
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11CompatibleCanonicalTowers
  HironakaG11StrictTransformTowers HironakaG11HSPhaseInduction HironakaG11HSMinimalWindows
  HironakaG11PresWindows HironakaG11PresReduction HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaActualPowerBoundaryExponents HironakaG11SingularCentreModification
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq CanonicalCentres HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Ordinary actual native windows, before powers or a choice of invariant. -/
structure Windows (X : SourceReducedComplexSpace) (H : ℕ → ℕ) (N : ℕ) where
  ι : Type
  finite : Finite ι
  window : ι → DimEmbedding X N
  rawRecord : ∀ i, MarkedIdeal N (Amb window i)
  footprint : ∀ i, Set (window i).ambient
  footprint_compact : ∀ i, IsCompact (footprint i)
  native : ∀ i, IsNativeWindowRecord (window i) (rawRecord i) H
  cover : ∀ x ∈ hsStratum X H, ∃ i, ∃ c : (window i).carrier,
    c.val ∈ footprint i ∧ (window i).toLocalEmbedding.toPoint c = x

attribute [instance] Windows.finite

namespace Windows
variable {X : SourceReducedComplexSpace} {H : ℕ → ℕ} {N : ℕ} (W : Windows X H N)

def commonMark : ℕ := by
  letI : Fintype W.ι := Fintype.ofFinite W.ι
  exact ∏ i, (W.rawRecord i).d

def exponent (i : W.ι) : ℕ := W.commonMark / (W.rawRecord i).d

def record (i : W.ι) : MarkedIdeal N (Amb W.window i) :=
  powerMarked (W.rawRecord i) (W.exponent i)

theorem exponent_pos (i : W.ι) : 1 ≤ W.exponent i := by
  let : Fintype W.ι := Fintype.ofFinite W.ι
  have hp : 0 < W.commonMark :=
    HironakaG11InvCommonMark.prodMark_pos (fun j => (W.rawRecord j).d)
      (fun j => (W.native j).1.one_le_d)
  exact HironakaG11InvCommonMark.one_le_div_of_dvd hp
    (HironakaG11InvCommonMark.dvd_prodMark (fun j => (W.rawRecord j).d) i)

theorem record_mark (i : W.ι) : (W.record i).d = W.commonMark := by
  let : Fintype W.ι := Fintype.ofFinite W.ι
  exact HironakaG11InvCommonMark.powerMarked_div_d (W.rawRecord i)
    (HironakaG11InvCommonMark.dvd_prodMark (fun j => (W.rawRecord j).d) i)

theorem record_hs (i : W.ι) : IsHSWindowRecord (W.window i) (W.record i) H :=
  (W.native i).isHSWindowRecord.powerMarked (W.exponent_pos i)

theorem domain (i : W.ι) : IsInvDomain N (W.record i) := (W.record_hs i).1

variable {Λ : Type} [LinearOrder Λ]
  (B : BMInvariant.{0,0} N (fun {Y} A A' => LocWPEquiv (X := Y) A A') N Λ)

theorem presentation (i : W.ι) : HSPresentation B.toResolutionInvariant (W.window i) (W.record i) H :=
  (W.record_hs i).hsPresentation B.toResolutionInvariant

theorem transport : RecordsTransport B.toResolutionInvariant W.record (mapAdm W.window) :=
  recordsTransport_of_native HironakaG11PresLineStable.nativeLineStability B W.window W.rawRecord H
    W.native W.exponent W.exponent_pos (fun i j => (W.record_mark i).trans (W.record_mark j).symm)

include B in
theorem cosupp_subset (i : W.ι) : (W.record i).cosupp ⊆ (W.window i).carrier :=
  HSPresentation.cosupp_subset (W.presentation B) i

include B in
theorem cosupp_cover (i : W.ι) (c : (W.window i).carrier) (hc : c.val ∈ (W.record i).cosupp) :
    ∃ j, ∃ c' : (W.window j).carrier, c'.val ∈ W.footprint j ∧
      (W.window j).toLocalEmbedding.toPoint c' = (W.window i).toLocalEmbedding.toPoint c := by
  have hHS := (HSPresentation.mem_cosupp_iff (W.presentation B) i c).mp hc
  have hs : (W.window i).toLocalEmbedding.toPoint c ∈ intrinsicSingularLocus X.obj := by
    have h := ((W.presentation B i BlowupTower.refl trivial).2 (W.window i).analytic c).2.2 hc
    have h2 : c ∈ (EmbeddedBlowupOverlap.chartMorphism (W.window i).toLocalEmbedding).hom.left.base ⁻¹'
        intrinsicSingularLocus X.obj := by
      rw [HironakaG11CompatibleAnalyticCover.preimage_intrinsicSingularLocus_of_isOpenImmersion
        (EmbeddedBlowupOverlap.chartMorphism (W.window i).toLocalEmbedding) (W.window i).isOpenImmersion]
      exact h
    exact h2
  exact W.cover _ ⟨hs, hHS⟩

theorem stratum_cover (x : X.obj.left) (hx : x ∈ intrinsicSingularLocus X.obj)
    (hH : originalStalkHS X x = H) : ∃ i, x ∈ range (W.window i).toLocalEmbedding.toPoint := by
  obtain ⟨i, c, -, hc⟩ := W.cover x ⟨hx, hH⟩
  exact ⟨i, c, hc⟩

/-- The actual ambient driver, not an independently chosen resolving endpoint. -/
def ambientStage (m : ℕ) : GStage B.toResolutionInvariant W.record (mapAdm W.window) m :=
  gstage B.toResolutionInvariant W.record (mapAdm W.window) W.footprint W.domain
    (W.cosupp_subset B) (W.cosupp_cover B) (adm_exists_map W.window) (W.transport B) m

/-- Every actual native prefix of that same driver. -/
def nativeStage (m : ℕ) : XStage W.window (W.ambientStage B m).T :=
  xstage W.footprint W.domain (W.cosupp_subset B) (W.cosupp_cover B) (W.transport B)
    W.footprint_compact (HSPresentation.cosuppInStrictSing (W.presentation B)) m

/-- Choose the genuine physical native successor supplied by the held recursion. -/
def step (m : ℕ) : (W.nativeStage B (m + 1)).Y ⟶ (W.nativeStage B m).Y :=
  (xstage_succ W.domain (W.cosupp_subset B) (W.cosupp_cover B) (W.transport B)
    W.footprint_compact (HSPresentation.cosuppInStrictSing (W.presentation B)) m).choose

theorem step_projection (m : ℕ) :
    (W.nativeStage B (m + 1)).q = W.step B m ≫ (W.nativeStage B m).q :=
  (xstage_succ W.domain (W.cosupp_subset B) (W.cosupp_cover B) (W.transport B)
    W.footprint_compact (HSPresentation.cosuppInStrictSing (W.presentation B)) m).choose_spec.1

theorem step_singular (m : ℕ) : IsSingularCentreStep (W.step B m) :=
  (xstage_succ W.domain (W.cosupp_subset B) (W.cosupp_cover B) (W.transport B)
    W.footprint_compact (HSPresentation.cosuppInStrictSing (W.presentation B)) m).choose_spec.2.1

/-- Literal recursive composition of the actual physical arrows. -/
def finiteComposite : (m : ℕ) → (W.nativeStage B m).Y ⟶ X
  | 0 => 𝟙 X
  | m + 1 => W.step B m ≫ finiteComposite m

theorem finiteComposite_eq : ∀ m, W.finiteComposite B m = (W.nativeStage B m).q
  | 0 => rfl
  | m + 1 => by
      change W.step B m ≫ W.finiteComposite B m = _
      rw [finiteComposite_eq m, W.step_projection B m]

/-- The actual WHOLE quotient projection of the same ambient prefix. -/
def prefixProjection (m : ℕ) (i : W.ι) :
    ofClosedAnalytic ((W.nativeStage B m).carrier i) ((W.nativeStage B m).analytic i) ⟶
      ofClosedAnalytic (W.window i).carrier (W.window i).analytic :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (n := N) (m := N) ((W.ambientStage B m).T i).2.contMDiff_proj
      (fun y hy => (W.nativeStage B m).proj_mem i ⟨y, hy⟩))
    (actualSubspaceMap_point ((W.ambientStage B m).T i).2.contMDiff_proj
      (fun y hy => (W.nativeStage B m).proj_mem i ⟨y, hy⟩)))

theorem prefix_square (m : ℕ) (i : W.ι) :
    (W.nativeStage B m).map i ≫ (W.nativeStage B m).q =
      W.prefixProjection B m i ≫ EmbeddedBlowupOverlap.chartMorphism (W.window i).toLocalEmbedding := by
  apply morphism_eq_of_pointwise_eq
  intro c
  exact (W.nativeStage B m).square i c ((W.nativeStage B m).proj_mem i c)

theorem prefix_scalar (m : ℕ) (i : W.ι) :
    (W.prefixProjection B m i).hom.left ≫ (ofClosedAnalytic (W.window i).carrier
      (W.window i).analytic).obj.hom =
    (ofClosedAnalytic ((W.nativeStage B m).carrier i) ((W.nativeStage B m).analytic i)).obj.hom :=
  Over.w (W.prefixProjection B m i).hom

theorem prefix_carrier (m : ℕ) (i : W.ι) :
    (W.nativeStage B m).carrier i = strictAlong ((W.ambientStage B m).T i).2 (W.window i).carrier :=
  (W.nativeStage B m).carrier_eq i

theorem prefix_openImmersion (m : ℕ) (i : W.ι) :
    LocallyRingedSpace.IsOpenImmersion ((W.nativeStage B m).map i).hom.left :=
  (W.nativeStage B m).isOpenImmersion i

theorem prefix_range (m : ℕ) (i : W.ι) :
    range ((W.nativeStage B m).map i).hom.left.base =
      (W.nativeStage B m).q.hom.left.base ⁻¹' range (W.window i).toLocalEmbedding.toPoint :=
  (W.nativeStage B m).range_map i

theorem prefix_canonical (m : ℕ) (i : W.ι) :
    IsCanonical (W.record i) (B.toResolutionInvariant.inv (W.record i)) ((W.ambientStage B m).T i).2 :=
  (W.ambientStage B m).canonical i

theorem prefix_length (m : ℕ) (i : W.ι) : ((W.ambientStage B m).T i).2.length = m :=
  (W.ambientStage B m).length i

theorem prefix_compatible (m : ℕ) : AdmCompatible (mapAdm W.window) (W.ambientStage B m).T :=
  (W.ambientStage B m).compatible

theorem prefix_isoOver (m : ℕ) :
    IsIsoOver (W.nativeStage B m).q (cosuppImage W.window W.record)ᶜ :=
  isIsoOver_xstage W.domain (W.cosupp_subset B) (W.cosupp_cover B) (W.transport B)
    W.footprint_compact (HSPresentation.cosuppInStrictSing (W.presentation B)) m

variable [WellFoundedLT Λ]

theorem exit_exists : ∃ m, ∀ i, (geoTransformAlong (W.record i) ((W.ambientStage B m).T i).2).cosupp = ∅ :=
  exists_gstage_cosupp_eq_empty W.domain (W.cosupp_subset B) (W.cosupp_cover B)
    (adm_exists_map W.window) (W.transport B) W.footprint_compact

def clock : ℕ := by
  classical
  exact Nat.find (W.exit_exists B)

theorem clock_exhausted (i : W.ι) :
    (geoTransformAlong (W.record i) ((W.ambientStage B (W.clock B)).T i).2).cosupp = ∅ := by
  classical
  exact Nat.find_spec (W.exit_exists B) i

theorem before_clock (m : ℕ) (hm : m < W.clock B) :
    ∃ i, (geoTransformAlong (W.record i) ((W.ambientStage B m).T i).2).cosupp.Nonempty := by
  classical
  by_contra h
  have he : ∀ i, (geoTransformAlong (W.record i) ((W.ambientStage B m).T i).2).cosupp = ∅ :=
    fun i => Set.not_nonempty_iff_eq_empty.mp (fun hi => h ⟨i, hi⟩)
  exact (Nat.not_le_of_gt hm) (Nat.find_min' (W.exit_exists B) he)

theorem terminal_resolution (i : W.ι) :
    IsGeoResolution (W.record i) ((W.ambientStage B (W.clock B)).T i).2 :=
  ⟨B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (W.domain i) _
    (W.prefix_canonical B (W.clock B) i), W.clock_exhausted B i⟩

theorem terminal_hs (y : (W.nativeStage B (W.clock B)).Y.obj.left)
    (hy : y ∈ intrinsicSingularLocus (W.nativeStage B (W.clock B)).Y.obj) :
    ((W.nativeStage B (W.clock B)).q.hom.left.base y ∈ intrinsicSingularLocus X.obj ∧
      originalStalkHS (W.nativeStage B (W.clock B)).Y y =
        originalStalkHS X ((W.nativeStage B (W.clock B)).q.hom.left.base y) ∧
      originalStalkHS X ((W.nativeStage B (W.clock B)).q.hom.left.base y) ≠ H) ∨
      originalStalkHS (W.nativeStage B (W.clock B)).Y y < H :=
  hsValue_after_phase (W.presentation B) W.stratum_cover (W.nativeStage B (W.clock B))
    (W.prefix_canonical B (W.clock B)) (W.clock_exhausted B) (W.prefix_isoOver B (W.clock B)) y hy

theorem terminal_compact [CompactSpace X.obj.left] :
    CompactSpace (W.nativeStage B (W.clock B)).Y.obj.left :=
  (W.nativeStage B (W.clock B)).isSingularCentreModification.source_compact

theorem terminal_drop [CompactSpace X.obj.left] (a : X.obj.left)
    (ha : a ∈ intrinsicSingularLocus X.obj) (hH : originalStalkHS X a = H) :
    letI := W.terminal_compact B
    Multiset.IsDershowitzMannaLT
      (singHSValues (W.nativeStage B (W.clock B)).Y).val (singHSValues X).val := by
  classical
  let := W.terminal_compact B
  refine isDershowitzMannaLT_of_replace (h := hsValue X a) (mem_singHSValues.mpr ⟨a, ha, rfl⟩) ?_
  intro v hv
  obtain ⟨y, hy, rfl⟩ := mem_singHSValues.mp hv
  rcases W.terminal_hs B y hy with ⟨hs, heq, hne⟩ | hlt
  · left
    refine ⟨mem_singHSValues.mpr ⟨_, hs, Subtype.ext heq.symm⟩, fun h => hne ?_⟩
    exact heq.symm.trans ((congrArg Subtype.val h).trans hH)
  · right
    change originalStalkHS (W.nativeStage B (W.clock B)).Y y < originalStalkHS X a
    rwa [hH]

end Windows

variable (X : SourceReducedComplexSpace) [CompactSpace X.obj.left]
  (a : X.obj.left) (ha : a ∈ intrinsicSingularLocus X.obj)
  (hmax : ∀ x ∈ intrinsicSingularLocus X.obj,
    toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X a))

include ha hmax in
theorem maximal_stratum_compact : IsCompact (hsStratum X (originalStalkHS X a)) := by
  have hns : ¬ X.IsSmooth := by
    intro hs
    have he := OriginalIntrinsicSingularLocus.isSmooth_iff_intrinsicSingularLocus_eq_empty X |>.mp hs
    rw [he] at ha
    exact ha
  obtain ⟨a', ha', hmax', hDEq, -, -, -, hDc, -⟩ :=
    OriginalIntrinsicHSSuperlevels.exists_original_compact_singular_hs_maximal_stratum X hns
  have hHH : originalStalkHS X a = originalStalkHS X a' :=
    toLex.injective (le_antisymm (hmax' a ha) (hmax a' ha'))
  rw [hHH, show hsStratum X (originalStalkHS X a') =
    OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold X (originalStalkHS X a') from hDEq.symm]
  exact hDc

include ha hmax in
theorem exists_windows : Nonempty (Windows X (originalStalkHS X a) (originalStalkHS X a 1 - 1)) := by
  obtain ⟨ι, hf, w, M, K, hK, -, hfoot, hrec⟩ := exists_native_state_phase_windows X
    (originalStalkHS X a) (maximal_stratum_compact X a ha hmax)
    (fun _ => univ) (fun _ _ => ⟨isOpen_univ, trivial⟩)
  exact ⟨⟨ι, hf, w, M, K, hK, hrec, hfoot⟩⟩

/-- All ordinary geometric data are generated before any phase execution. -/
def windows : Windows X (originalStalkHS X a) (originalStalkHS X a 1 - 1) :=
  (exists_windows X a ha hmax).some

include ha hmax in
/-- Ordinary compact factory for the FIXED actual invariant supplied as parameter. -/
theorem exists_phase_history {Λ : Type} [LinearOrder Λ] [WellFoundedLT Λ]
    (B : BMInvariant.{0,0} (originalStalkHS X a 1 - 1)
      (fun {Y} A A' => LocWPEquiv (X := Y) A A') (originalStalkHS X a 1 - 1) Λ) :
    ∃ W : Windows X (originalStalkHS X a) (originalStalkHS X a 1 - 1),
      (∀ m, W.finiteComposite B m = (W.nativeStage B m).q) ∧
      (∀ m, IsSingularCentreStep (W.step B m)) ∧
      (∀ i, IsGeoResolution (W.record i) ((W.ambientStage B (W.clock B)).T i).2) ∧
      (letI := W.terminal_compact B
       Multiset.IsDershowitzMannaLT
         (singHSValues (W.nativeStage B (W.clock B)).Y).val (singHSValues X).val) := by
  let W := windows X a ha hmax
  exact ⟨W, W.finiteComposite_eq B, W.step_singular B, W.terminal_resolution B, W.terminal_drop B a ha rfl⟩

/-- The LITERAL original invariant with its proved original class theorem. -/
def originalInvariant (N : ℕ) :
    BMInvariant.{0,0} N (fun {Y} A B => LocWPEquiv (X := Y) A B) N (ValTy N) where
  toResolutionInvariant := canonicalInvariant N
  classFunctorial := HironakaG1OriginalInvariantClassFunctorial.classFunctorialFor_canonicalInvariant N

theorem originalInvariant_toResolutionInvariant (N : ℕ) :
    (originalInvariant N).toResolutionInvariant = canonicalInvariant N := rfl

theorem originalInvariant_positive (N : ℕ) (hN : 0 < N) :
    (originalInvariant N).toResolutionInvariant = invFamily hN N := by
  cases N with
  | zero => exact False.elim (Nat.not_lt_zero _ hN)
  | succ N => rfl

include ha hmax in
/-- Raw chosen window/clock/prefix data remain available for later outer induction. -/
theorem exists_original_phase_history :
    ∃ W : Windows X (originalStalkHS X a) (originalStalkHS X a 1 - 1),
      let B := originalInvariant (originalStalkHS X a 1 - 1)
      (∀ m, W.finiteComposite B m = (W.nativeStage B m).q) ∧
      (∀ m, IsSingularCentreStep (W.step B m)) ∧
      (∀ i, IsGeoResolution (W.record i) ((W.ambientStage B (W.clock B)).T i).2) ∧
      (letI := W.terminal_compact B
       Multiset.IsDershowitzMannaLT
         (singHSValues (W.nativeStage B (W.clock B)).Y).val (singHSValues X).val) := by
  exact exists_phase_history X a ha hmax (originalInvariant (originalStalkHS X a 1 - 1))

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSPhaseHistory
