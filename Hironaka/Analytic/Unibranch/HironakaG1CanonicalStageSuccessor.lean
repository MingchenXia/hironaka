import Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageCentreIdeal
import Hironaka.Analytic.Unibranch.HironakaG11PresPresentation

/-!
# One actual intrinsic canonical successor, with full native window squares

The initial class/native data derive the current singular centre internally.
The held prescribed-blowup engine then constructs ONE genuine global successor,
retaining the whole centre ideal and the actual native strict-window squares.
The original canonical records and ordered births are never reselected.

Blueprint FIRST: `hironaka-g1-canonical-stage-successor.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageSuccessor

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11SingularCentreModification SmoothCentreModification EmbeddedBlowup
  HironakaIntrinsicReducedCentreIdealSheaf HironakaG11PresPresentation
open ResolutionInvariantSpec (IsInvDomain)
open HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (K : ∀ i, Set (w i).ambient)
  (hCover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)

local notation "F" => localCentres w M B hD hClass H hState K hCover s xs
local notation "C" => support w M B hD hClass H hState K hCover s xs

include hState in
private theorem initial_cosupp_subset (i : ι) : (M i).cosupp ⊆ (w i).carrier :=
  ((hState i).hsTowerState (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i))
    (by trivial)).2.1

include hD hState in
/-- The SAME actual canonical centre consists of intrinsic singular points
of the SAME current original strict window, derived from initial native data. -/
theorem current_centre_singular (i : ι) (c : xs.carrier i)
    (hc : c.val ∈ gcentre B.toResolutionInvariant M K s.T i) :
    c ∈ intrinsicSingularLocus
      (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj := by
  have ht := (hState i).hsTowerState (s.T i).2
    (B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (hD i) (s.T i).2
      (s.canonical i))
  apply (mem_intrinsicSingularLocus_ofClosedAnalytic_iff (xs.analytic i) c).mpr
  exact (Set.ext_iff.mp
    (congrArg (HironakaEmbeddedAnalytic.singularSet (n := N)) (xs.carrier_eq i)) c.val).mpr
      (ht.2.2.2.2 hc.1)

/-- The internally derived global support lies in the current intrinsic singular locus. -/
theorem support_subset_singular : C ⊆ intrinsicSingularLocus xs.Y.obj :=
  (F).support_subset_intrinsicSingularLocus_iff.mpr fun i c hc =>
    current_centre_singular w M B hD H hState K s xs i c hc

/-- Protection of the ORIGINAL regular site, before the given finite prefix. -/
theorem support_disjoint_originalRegular :
    Disjoint C (xs.q.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  rw [disjoint_left]
  intro y hy hyReg
  exact support_subset_singular w M B hD hClass H hState K hCover s xs hy
    (xs.isSingularCentreModification.preimage_intrinsicRegularLocus_subset hyReg)

/-- The literal existing next canonical ambient stage, with the SAME initial records. -/
def nextStage : GStage B.toResolutionInvariant M (mapAdm w) (m + 1) :=
  s.next hD (initial_cosupp_subset w M H hState) hCover (adm_exists_map w)
    (recordsTransport w M B hD hClass)

/-- The prescribed actual next ambient, not a reselected presentation. -/
def nextAmbient (i : ι) : CMfd.{0} N :=
  gnextSpace hD (initial_cosupp_subset w M H hState) hCover (adm_exists_map w)
    (recordsTransport w M B hD hClass) s i

/-- The prescribed actual canonical local blowup map. -/
def nextProjection (i : ι) : nextAmbient w M B hD hClass H hState K hCover s i → (s.T i).1 :=
  gnextMap hD (initial_cosupp_subset w M H hState) hCover (adm_exists_map w)
    (recordsTransport w M B hD hClass) s i

theorem nextProjection_isBlowup (i : ι) :
    IsBlowupAlong N (gcentre B.toResolutionInvariant M K s.T i)
      (nextProjection w M B hD hClass H hState K hCover s i) :=
  gnextMap_isBlowup hD (initial_cosupp_subset w M H hState) hCover (adm_exists_map w)
    (recordsTransport w M B hD hClass) s i

/-- The SAME native strict-transform window for the prescribed canonical local step. -/
def nextWindow (i : ι) : SourceReducedComplexSpace :=
  ofClosedAnalytic
    (strictTransform N (nextProjection w M B hD hClass H hState K hCover s i) (xs.carrier i))
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (nextProjection_isBlowup w M B hD hClass H hState K hCover s i) (xs.analytic i))

/-- The full native strict-transform projection, including all sheaf/scalar maps. -/
def nextWindowProjection (i : ι) : nextWindow w M B hD hClass H hState K hCover s xs i ⟶
    ofClosedAnalytic (xs.carrier i) (xs.analytic i) :=
  strictTransformMorphism (nextProjection_isBlowup w M B hD hClass H hState K hCover s i)
    (xs.analytic i)

variable [Finite ι] (hK : ∀ i, IsCompact (K i))

/-- The actual objects and full original morphisms of ONE constructed successor.
This is an output, never a caller's centre-compatibility or future-history premise. -/
structure Successor where
  Y : SourceReducedComplexSpace
  p : Y ⟶ xs.Y
  isSmoothCentreBlowup : IsSmoothCentreBlowup p
    (OriginalAnalyticClosedSubspace.inclusion xs.Y C
      (support_isAnalyticSubset w M B hD hClass H hState K hCover s xs hK))
  isSingularCentreStep : IsSingularCentreStep p
  surjective : Function.Surjective p.hom.left.base
  isIsoOver : IsIsoOver p Cᶜ
  map : ∀ i, nextWindow w M B hD hClass H hState K hCover s xs i ⟶ Y
  isOpenImmersion : ∀ i, LocallyRingedSpace.IsOpenImmersion (map i).hom.left
  square : ∀ i, map i ≫ p =
    nextWindowProjection w M B hD hClass H hState K hCover s xs i ≫ xs.map i
  range_map : ∀ i, range (map i).hom.left.base = p.hom.left.base ⁻¹' range (xs.map i).hom.left.base

/-- Construction from ordinary initial class/native data; all missing current
centre/incidence/compatibility premises are derived internally. -/
theorem exists_successor :
    Nonempty (Successor w M B hD hClass H hState K hCover s xs hK) := by
  have hc : (F).Compatible := by
    intro i j a b hab ha
    have hai : (xs.map i).hom.left.base a ∈ C := by
      rw [← window_trace_eq w M B hD hClass H hState K hCover s xs i] at ha
      exact ha
    rw [← window_trace_eq w M B hD hClass H hState K hCover s xs j]
    change (xs.map j).hom.left.base b ∈ C
    change (xs.map i).hom.left.base a = (xs.map j).hom.left.base b at hab
    rw [← hab]
    exact hai
  obtain ⟨hS, Y, p, hblow, hstep, -, hsurj, hiso, L, hL⟩ :=
    HironakaG11GluedWindowSteps.exists_singularCentreBlowup_given_blowups F hc
      (support_isClosed w M B hD hClass H hState K hCover s xs hK)
      (support_subset_singular w M B hD hClass H hState K hCover s xs)
      (nextAmbient w M B hD hClass H hState K hCover s)
      (nextProjection w M B hD hClass H hState K hCover s)
      (nextProjection_isBlowup w M B hD hClass H hState K hCover s)
  exact ⟨⟨Y, p, hblow, hstep, hsurj, hiso, L,
    fun i => (hL i).1, fun i => (hL i).2.1, fun i => (hL i).2.2⟩⟩

namespace Successor

variable (a : Successor w M B hD hClass H hState K hCover s xs hK)

/-- The global map is the blowup of the SAME ENTIRE internally constructed ideal. -/
theorem isIdealBlowup : IsIdealBlowup a.p
    (intrinsicReducedCentreIdealModule xs.Y.obj.left C)
    (intrinsicReducedCentreIdealInclusion xs.Y.obj.left C) := by
  have h := a.isSmoothCentreBlowup.2.2.2.2.2.1
  have hr := OriginalAnalyticClosedSubspace.inclusion_range xs.Y C
    (support_isAnalyticSubset w M B hD hClass H hState K hCover s xs hK)
  rw [hr] at h
  exact h

/-- The actual produced successor map is proper. -/
theorem isProperMap : IsProperMap a.p.hom.left.base :=
  a.isSingularCentreStep.isSingularCentreModification.isProperMap

/-- The successor supplies the ACTUAL original strict-space stage over the
literal canonical next ambient towers, retaining the prescribed whole squares. -/
def toXStage : XStage w (nextStage w M B hD hClass H hState K hCover s).T where
  Y := a.Y
  q := a.p ≫ xs.q
  isSingularCentreModification := .cons a.p xs.q a.isSingularCentreStep
    xs.isSingularCentreModification
  carrier i := strictTransform N (nextProjection w M B hD hClass H hState K hCover s i)
    (xs.carrier i)
  analytic i :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (nextProjection_isBlowup w M B hD hClass H hState K hCover s i) (xs.analytic i)
  map := a.map
  isOpenImmersion := a.isOpenImmersion
  carrier_eq i := by
    change _ = BlowupStrictSubmanifold.geoStrictTransform
      (nextProjection w M B hD hClass H hState K hCover s i)
      (gcentre B.toResolutionInvariant M K s.T i) (strictAlong (s.T i).2 (w i).carrier)
    rw [← xs.carrier_eq i]
    exact (BlowupStrictIdeal.geoStrictTransform_eq_strictTransform
      (nextProjection_isBlowup w M B hD hClass H hState K hCover s i)
      (HironakaG11WindowTowers.ManifoldSmoothCentres.carrier_subset_closure_diff F
        (support_subset_singular w M B hD hClass H hState K hCover s xs) i)).symm
  square i c hc := by
    have h1 := congrArg (fun f => f.hom.left.base c) (a.square i)
    change xs.q.hom.left.base (a.p.hom.left.base ((a.map i).hom.left.base c)) = _
    change a.p.hom.left.base ((a.map i).hom.left.base c) =
      (xs.map i).hom.left.base
        ((nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left.base c) at h1
    rw [h1]
    exact xs.square i
      ((nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left.base c) hc
  range_map i := by
    refine (a.range_map i).trans ?_
    ext y
    change a.p.hom.left.base y ∈ range (xs.map i).hom.left.base ↔
      xs.q.hom.left.base (a.p.hom.left.base y) ∈ range (w i).toLocalEmbedding.toPoint
    rw [xs.range_map i]
    rfl

/-- The actual composite protects the ORIGINAL regular locus, not only
the regular locus of the intermediate space. -/
theorem isIsoOver_originalRegular :
    IsIsoOver (a.p ≫ xs.q) (intrinsicRegularLocus X.obj) :=
  a.toXStage.isSingularCentreModification.isIsoOver_intrinsicRegularLocus

end Successor

omit [Finite ι]

/-- The entire actual record is retained at the prescribed next step. -/
theorem next_record_eq (i : ι) :
    geoTransformAlong (M i) ((nextStage w M B hD hClass H hState K hCover s).T i).2 =
      (geoTransformAlong (M i) (s.T i).2).geoTransform
        (gcentre B.toResolutionInvariant M K s.T i)
        (nextProjection w M B hD hClass H hState K hCover s i) := rfl

/-- The FULL ordered boundary, including empty old and born members. -/
theorem next_boundary_eq (i : ι) :
    (geoTransformAlong (M i) ((nextStage w M B hD hClass H hState K hCover s).T i).2).E =
      (geoTransformAlong (M i) (s.T i).2).E.map
        (BlowupStrictSubmanifold.geoStrictTransform
          (nextProjection w M B hD hClass H hState K hCover s i)
          (gcentre B.toResolutionInvariant M K s.T i)) ++
      [(nextProjection w M B hD hClass H hState K hCover s i) ⁻¹'
        gcentre B.toResolutionInvariant M K s.T i] := rfl

end
end Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageSuccessor
