import Hironaka.Resolution.HironakaDisjointFiniteControlledHistory
import Hironaka.MarkedIdeal.CoefficientIdealRestriction

/-!
# Strict transforms of arbitrary subsets through a constructed coupled history

The ambient history and its chronological boundary already exist in
`HironakaDisjointFiniteControlledHistory`. This module does not reconstruct
them. It derives the image of every original subset through the same history,
and derives that every ambient centre lies in the strict contact.

The history lemma applies to each actual coupled prefix. The final existence
theorem obtains the history from the existing ordinary-input constructor;
it does not assume a new all-future transport certificate. The source-facing
constructor remains explicitly in universe zero.
-/

set_option autoImplicit false

open Set Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3ControlledHistorySubsetTransport

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings SubmanifoldChartedSpace CoefficientIdealRestriction
  HironakaDisjointFiniteControlledHistory

/-- A closed strict-contact embedding transports the strict transform of
every subset. Only the contact range, the actual centre image, and the
projection square are used; no subset-transform equality is assumed. -/
theorem geoStrictTransform_image_of_square
    {P Q X Y : Type*} [TopologicalSpace Q] [TopologicalSpace Y]
    (ι : P → X) (η : Q → Y) (ρ : Q → P) (π : Y → X)
    (hι : Injective ι) (hη : IsClosedEmbedding η)
    (hsquare : π ∘ η = ι ∘ ρ) (C : Set P)
    (hrange : range η = geoStrictTransform π (ι '' C) (range ι))
    (V : Set P) :
    η '' geoStrictTransform ρ C V = geoStrictTransform π (ι '' C) (ι '' V) := by
  have hcomm (q : Q) : π (η q) = ι (ρ q) := congrFun hsquare q
  have hraw : η '' (ρ ⁻¹' (V \ C)) = π ⁻¹' ((ι '' V) \ (ι '' C)) := by
    ext y
    constructor
    · rintro ⟨q, ⟨hqV, hqC⟩, rfl⟩
      change π (η q) ∈ ι '' V ∧ π (η q) ∉ ι '' C
      rw [hcomm q]
      refine ⟨⟨ρ q, hqV, rfl⟩, ?_⟩
      rintro ⟨p, hp, he⟩
      exact hqC (hι he ▸ hp)
    · rintro ⟨⟨p, hpV, hpy⟩, hyC⟩
      have hyRange : y ∈ range η := by
        rw [hrange]
        exact subset_closure ⟨⟨p, hpy⟩, hyC⟩
      obtain ⟨q, rfl⟩ := hyRange
      refine ⟨q, ?_, rfl⟩
      have hqp : ρ q = p := hι ((hcomm q).symm.trans hpy.symm)
      constructor
      · rw [hqp]
        exact hpV
      · intro hqC
        exact hyC ⟨ρ q, hqC, (hcomm q).symm⟩
  unfold geoStrictTransform
  calc
    η '' closure (ρ ⁻¹' (V \ C)) = closure (η '' (ρ ⁻¹' (V \ C))) :=
      (hη.closure_image_eq _).symm
    _ = closure (π ⁻¹' ((ι '' V) \ (ι '' C))) := congrArg closure hraw

/-- The existing endpoint comparison is a closed embedding onto the actual
strict contact. This is extracted from its primitive biholomorphism. -/
theorem endpoint_closedEmbedding_range
    {d t : ℕ} {X : CMfd (d+t)} {N : Set X}
    {B : List (Set X)} {J : GermIdeal (d+t) X}
    {P Q : CMfd d} {ι : P → X} {M : MarkedIdeals.MarkedIdeal d P}
    {T : BlowupTower P Q} {Y : CMfd (d+t)} {U : BlowupTower X Y} {η : Q → Y}
    (h : Endpoint N B J ι M T U η) :
    IsClosedEmbedding η ∧ range η = contactAlong N U := by
  obtain ⟨hc, hr, _hI, _hNormal, _hE, _hTrans, F, hFη, _hproj, _hIdeal, _hBoundary⟩ := h
  let := chartedSpace (Nat.le_add_right d t) hr
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
  constructor
  · rw [← hFη]
    exact hc.isClosedEmbedding_subtypeVal.comp F.toHomeomorph.isClosedEmbedding
  · rw [← hFη]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact (F q).property
    · intro hy
      exact ⟨F.symm ⟨y, hy⟩, congrArg Subtype.val (F.apply_symm_apply ⟨y, hy⟩)⟩

/-- Every coupled physical prefix retains its endpoint assertion. -/
theorem endpoint_of_coupledHistory
    {d t : ℕ} {X : CMfd (d+t)} {P : CMfd d}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeals.MarkedIdeal d P}
    {Q : CMfd d} {Y : CMfd (d+t)}
    {T : BlowupTower P Q} {U : BlowupTower X Y} {η : Q → Y}
    (h : CoupledHistory N B J ι M T U η) : Endpoint N B J ι M T U η := by
  cases h with
  | refl hEnd => exact hEnd
  | step _previous _centre _square hEnd => exact hEnd

/-- The contact used by the controlled-history constructor is the ordinary
iterated centre-relative strict transform, with no extra geometric input. -/
theorem contactAlong_eq_strictAlong {n : ℕ} {X : CMfd n} (N : Set X) :
    {Y : CMfd n} → (U : BlowupTower X Y) → contactAlong N U = strictAlong U N
  | _, .refl => rfl
  | _, .step U C π _ =>
    congrArg (geoStrictTransform π C) (contactAlong_eq_strictAlong N U)

/-- Every original subset has its literal strict image on the same actual
coupled endpoint. The statement applies to every represented physical prefix. -/
theorem strictAlong_image_of_coupledHistory
    {d t : ℕ} {X : CMfd (d+t)} {P : CMfd d}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeals.MarkedIdeal d P}
    {Q : CMfd d} {Y : CMfd (d+t)}
    {T : BlowupTower P Q} {U : BlowupTower X Y} {η : Q → Y}
    (h : CoupledHistory N B J ι M T U η) (V : Set P) :
    η '' strictAlong T V = strictAlong U (ι '' V) := by
  induction h with
  | refl _hEnd => rfl
  | @step Q R Y Z T U η η' C C' ρ π hρ hπ previous hcentre hsquare hEnd ih =>
    have hPrevious := endpoint_of_coupledHistory previous
    obtain ⟨hη, hηRange⟩ := endpoint_closedEmbedding_range hPrevious
    obtain ⟨hη', hη'Range⟩ := endpoint_closedEmbedding_range hEnd
    have hRange : range η' = geoStrictTransform π (η '' C) (range η) := by
      rw [hη'Range, hηRange]
      change geoStrictTransform π C' (contactAlong N U) = _
      rw [hcentre]
    change η' '' geoStrictTransform ρ C (strictAlong T V) =
      geoStrictTransform π C' (strictAlong U (ι '' V))
    rw [hcentre, ← ih]
    exact geoStrictTransform_image_of_square η η' ρ π hη.injective hη'
      hsquare C hRange (strictAlong T V)

/-- Ambient centres in the existing coupled history lie in the strict
contact, so containing initial members can be reattached by `DropMembers`. -/
theorem centresIn_of_coupledHistory
    {d t : ℕ} {X : CMfd (d+t)} {P : CMfd d}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeals.MarkedIdeal d P}
    {Q : CMfd d} {Y : CMfd (d+t)}
    {T : BlowupTower P Q} {U : BlowupTower X Y} {η : Q → Y}
    (h : CoupledHistory N B J ι M T U η) : CentresIn N U := by
  induction h with
  | refl _hEnd => trivial
  | @step Q R Y Z T U η η' C C' ρ π hρ hπ previous hcentre _hsquare _hEnd ih =>
    refine ⟨ih, ?_⟩
    rintro y hy
    rw [hcentre] at hy
    obtain ⟨q, _hq, rfl⟩ := hy
    rw [← contactAlong_eq_strictAlong N U,
      ← (endpoint_closedEmbedding_range (endpoint_of_coupledHistory previous)).2]
    exact ⟨q, rfl⟩

/-- From the original coherent ideal and an actual intrinsic test tower,
reuse the existing finite ambient constructor and derive strict-image
transport for every original subset on its same endpoint. -/
theorem exists_actual_finite_history_with_subset_transport
    {d t : ℕ} {X : CMfd (d+t)} {N : Set X} (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) (ht : 0 < t)
    {B : List (Set X)} (hB : IsSNCDivisor (d+t) B)
    (hTrans : IsTransverse (d+t) N B)
    (J : GermIdeal (d+t) X) (hJ : J.IsCoherent)
    (hNormal : (vanishingIdeal (n := d+t) N).Le J) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    let M := fullMarked (B.map fun H => (Subtype.val : N → X) ⁻¹' H)
      (GermIdeal.pullback (m := d) (Subtype.val : N → X) J)
    ∀ {Q : CMfd d} (T : BlowupTower (CMfd.of N) Q), IsGeoTestTower M T →
      ∃ (Y : CMfd (d+t)) (U : BlowupTower X Y) (η : Q → Y),
        IsGeoTestTower (fullMarked B J) U ∧ U.length = T.length ∧
        CoupledHistory N B J (Subtype.val : N → X) M T U η ∧
        Endpoint N B J (Subtype.val : N → X) M T U η ∧ CentresIn N U ∧
        ∀ V : Set N, η '' strictAlong T V = strictAlong U ((Subtype.val : N → X) '' V) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  dsimp only
  intro Q T hTest
  obtain ⟨Y, U, η, hU, hLength, hHistory, hEnd⟩ :=
    exists_actual_finite_controlled_history hNc hN ht hB hTrans J hJ hNormal T hTest
  exact ⟨Y, U, η, hU, hLength, hHistory, hEnd, centresIn_of_coupledHistory hHistory,
    fun V => strictAlong_image_of_coupledHistory hHistory V⟩

end

end Hironaka.HironakaG3ControlledHistorySubsetTransport
