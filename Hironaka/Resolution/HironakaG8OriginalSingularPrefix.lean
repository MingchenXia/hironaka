import Hironaka.Resolution.HironakaG8NativeCommonMarkRank
import Hironaka.Resolution.HironakaG8NativeSimultaneousCentre
import Hironaka.Resolution.HironakaG8NativePrefixOriginalCanonical

/-! Read a physical singular centre on the original, unpowered native records. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8OriginalSingularPrefix

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaG8NativeSimultaneousCentre
  HironakaG8NativeCommonMarkRank HironakaActualPowerBoundaryExponents
  HironakaActualOriginalPowerTransform HironakaG1OriginalUnequalMarkCanonical
  NonmonomialOrderLocal GeneralValue HironakaStageCenters

variable {n : ℕ} {X Y : CMfd.{0} n} {I : Type}

/-- A chart meeting the physical centre computes its trace as the maximum of
the original invariant of its own raw native record. Other charts may have
nonempty cosupport and miss the common powered maximum. -/
theorem raw_maxLocus_eq_centre_trace
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (e : I → ℕ) (T : BlowupTower X Y) (C : Set Y) (m : ValTy n)
    (hCentre : NativeSimultaneousCentre (canonicalInvariant n) U
      (fun i => powerMarked (P i) (e i)) T C m)
    (i : I) (hP : IsInvDomain n (P i)) (he : 1 ≤ e i)
    (hCan : IsCanonical (powerMarked (P i) (e i))
      ((canonicalInvariant n).inv (powerMarked (P i) (e i))) (restrict (U i) T))
    (hMeet : ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' C).Nonempty) :
    maxLocus ((canonicalInvariant n).inv (P i) (restrict (U i) T))
        (geoTransformAlong (P i) (restrict (U i) T)).cosupp =
      (Subtype.val : openPreimage T (U i) → Y) ⁻¹' C := by
  let S := restrict (U i) T
  let Q := P i
  let R := canonicalInvariant n
  have hRaw := (canonicalInvariant_isCanonical_power_iff Q hP (e i) he S).mpr hCan
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hP S hRaw
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP S hTest
  have hCos := (original_power_transform Q hP (e i) he S hTest).2.cosupp_eq.trans
    (powerMarked_cosupp (geoTransformAlong Q S) hCurrent he)
  have hTrace := hCentre.trace i
  rw [hCos] at hTrace
  obtain ⟨a,ha⟩ := hMeet
  have ha' : a ∈ (geoTransformAlong Q S).cosupp ∧
      R.inv (powerMarked Q (e i)) S a = m := by
    rw [hTrace] at ha
    exact ha
  have hlt {x y : openPreimage T (U i)}
      (hx : x ∈ (geoTransformAlong Q S).cosupp) (hy : y ∈ (geoTransformAlong Q S).cosupp) :
      R.inv Q S x < R.inv Q S y ↔
        R.inv (powerMarked Q (e i)) S x < R.inv (powerMarked Q (e i)) S y :=
    canonical_common_mark_power_lt_iff Q Q hP hP rfl (e i) he S S hRaw hRaw hx hy
  ext y
  change (y ∈ (geoTransformAlong Q S).cosupp ∧
    ∀ x ∈ (geoTransformAlong Q S).cosupp, R.inv Q S x ≤ R.inv Q S y) ↔ _
  rw [hTrace]
  change _ ↔ y ∈ (geoTransformAlong Q S).cosupp ∧ R.inv (powerMarked Q (e i)) S y = m
  constructor
  · rintro ⟨hy,hyMax⟩
    refine ⟨hy,le_antisymm (hCentre.upper i y (hCos.symm ▸ hy)) ?_⟩
    rw [← ha'.2]
    exact not_lt.mp (fun h => (not_lt.mpr (hyMax a ha'.1)) ((hlt hy ha'.1).mpr h))
  · rintro ⟨hy,hyVal⟩
    refine ⟨hy,fun x hx => not_lt.mp ?_⟩
    intro h
    exact (not_lt.mpr (hCentre.upper i x (hCos.symm ▸ hx))) (hyVal ▸ (hlt hy hx).mp h)


/-- The raw local maximum loci on charts meeting the physical centre,
viewed in its ambient stage. -/
def rawMaximaAlongCentre
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (T : BlowupTower X Y) (C : Set Y) : Set Y :=
    ⋃ i : {i : I // ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' C).Nonempty},
      (Subtype.val : openPreimage T (U i.val) → Y) ''
        maxLocus ((canonicalInvariant n).inv (P i.val) (restrict (U i.val) T))
          (geoTransformAlong (P i.val) (restrict (U i.val) T)).cosupp

/-- The physical next centre can be recovered from all occupied chart
maxima after removing their numerical common-mark powers. -/
theorem centre_eq_union_raw_maxLocus
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (e : I → ℕ) (T : BlowupTower X Y) (C : Set Y) (m : ValTy n)
    (hCentre : NativeSimultaneousCentre (canonicalInvariant n) U
      (fun i => powerMarked (P i) (e i)) T C m)
    (hP : ∀ i, IsInvDomain n (P i)) (he : ∀ i, 1 ≤ e i)
    (hCan : ∀ i, IsCanonical (powerMarked (P i) (e i))
      ((canonicalInvariant n).inv (powerMarked (P i) (e i))) (restrict (U i) T)) :
    C = rawMaximaAlongCentre U P T C := by
  unfold rawMaximaAlongCentre
  ext y
  constructor
  · intro hy
    obtain ⟨i,hi⟩ := hCentre.covered y hy
    let z : openPreimage T (U i) := ⟨y,hi⟩
    have hz : z ∈ (Subtype.val : openPreimage T (U i) → Y) ⁻¹' C := hy
    have hMeet : ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' C).Nonempty := ⟨z,hz⟩
    refine mem_iUnion.mpr ⟨⟨i,hMeet⟩,z,?_,rfl⟩
    rw [raw_maxLocus_eq_centre_trace U P e T C m hCentre i (hP i) (he i) (hCan i) hMeet]
    exact hz
  · intro hy
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hy
    rw [raw_maxLocus_eq_centre_trace U P e T C m hCentre i.val
      (hP i.val) (he i.val) (hCan i.val) i.property] at hz
    exact hz

/-- Read the unpowered original rank on every nonempty physical centre of
a simultaneous native phase, using its terminal canonical histories. -/
theorem raw_centre_maxima_stages
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (e : I → ℕ) (T : BlowupTower X Y)
    (hP : ∀ i, IsInvDomain n (P i)) (he : ∀ i, 1 ≤ e i)
    (hStages : NativeSimultaneousStages (canonicalInvariant n) U
      (fun i => powerMarked (P i) (e i)) T)
    (hCan : ∀ i, IsCanonical (powerMarked (P i) (e i))
      ((canonicalInvariant n).inv (powerMarked (P i) (e i))) (restrict (U i) T)) :
    StageCentres (fun S C => C = ∅ ∨ C = rawMaximaAlongCentre U P S C) T := by
  induction T with
  | refl => trivial
  | step S C π hπ ih =>
    have hBefore := fun i => (hCan i).1
    refine ⟨ih hStages.1 hBefore,?_⟩
    rcases hStages.2 with hEmpty | ⟨m,hm⟩
    · exact Or.inl hEmpty
    · exact Or.inr (centre_eq_union_raw_maxLocus U P e S C m hm hP he hBefore)

/-- The simultaneous maximum certificates already suffice to recover every
physical centre from the unpowered native maxima. -/
theorem raw_centre_maxima_of_simultaneous_stages
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (e : I → ℕ) (T : BlowupTower X Y)
    (hP : ∀ i, IsInvDomain n (P i)) (he : ∀ i, 1 ≤ e i)
    (hStages : NativeSimultaneousStages (canonicalInvariant n) U
      (fun i => powerMarked (P i) (e i)) T) :
    StageCentres (fun S C => C = ∅ ∨ C = rawMaximaAlongCentre U P S C) T :=
  raw_centre_maxima_stages U P e T hP he hStages fun i =>
    HironakaG8NativePrefixOriginalCanonical.simultaneous_stages_original_canonical
      (canonicalInvariant n) U (fun i => powerMarked (P i) (e i)) T hStages i

/-- The whole mark-one maximum at an actual prefix is determined by the
first order stratum and strict separation inside that stratum. Regular
points in the transformed cosupport are included in the competitors. -/
theorem original_maxLocus_iff_first_order_and_ties
    {X Y : CMfd.{0} (n+1)} (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (C : Set Y) (c : Y)
    (hc : c ∈ C)
    (hSub : C ⊆ (geoTransformAlong
      (⟨univ,E,vanishingIdeal (n := n+1) W,1⟩ : MarkedIdeal (n+1) X) T).cosupp) :
    let P : MarkedIdeal (n+1) X := ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩
    let S := (geoTransformAlong P T).cosupp
    let o := nmOrd (geoTransformAlong P T)
    let v := (canonicalInvariant (n+1)).inv P T
    C = maxLocus v S ↔
      (∀ y ∈ S, o y ≤ o c) ∧
      (∀ y ∈ C, o y = o c ∧ v y = v c) ∧
      (∀ y ∈ S, y ∉ C → o y = o c → v y < v c) := by
  let P : MarkedIdeal (n+1) X := ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩
  let S := (geoTransformAlong P T).cosupp
  let o := nmOrd (geoTransformAlong P T)
  let v := (canonicalInvariant (n+1)).inv P T
  change C = maxLocus v S ↔
    (∀ y ∈ S, o y ≤ o c) ∧
    (∀ y ∈ C, o y = o c ∧ v y = v c) ∧
    (∀ y ∈ S, y ∉ C → o y = o c → v y < v c)
  have hlt {y z : Y} (h : o y < o z) : v y < v z := by
    change genInv _ P T y < genInv _ P T z
    exact genInv_lt_of_nmOrd_lt _ P h
  constructor
  · intro h
    have hc' : c ∈ maxLocus v S := h ▸ hc
    refine ⟨?_,?_,?_⟩
    · intro y hy
      exact not_lt.mp (fun h => (not_lt.mpr (hc'.2 y hy)) (hlt h))
    · intro y hy
      have hy' : y ∈ maxLocus v S := h ▸ hy
      have hv : v y = v c := le_antisymm (hc'.2 y hy'.1) (hy'.2 c hc'.1)
      refine ⟨?_,hv⟩
      exact le_antisymm
        (not_lt.mp fun h => (not_lt.mpr (hc'.2 y hy'.1)) (hlt h))
        (not_lt.mp fun h => (not_lt.mpr (hy'.2 c hc'.1)) (hlt h))
    · intro y hy hyOutside _
      refine lt_of_le_of_ne (hc'.2 y hy) ?_
      intro he
      apply hyOutside
      rw [h]
      exact ⟨hy,fun z hz => he.symm ▸ hc'.2 z hz⟩
  · rintro ⟨hBound,hTie,hBelow⟩
    have hcMax : c ∈ maxLocus v S := by
      refine ⟨hSub hc,fun y hy => ?_⟩
      by_cases hyC : y ∈ C
      · exact le_of_eq (hTie y hyC).2
      by_cases hEq : o y = o c
      · exact le_of_lt (hBelow y hy hyC hEq)
      · exact le_of_lt (hlt (lt_of_le_of_ne (hBound y hy) hEq))
    ext y
    constructor
    · intro hy
      exact ⟨hSub hy,fun z hz => (hTie y hy).2.symm ▸ hcMax.2 z hz⟩
    · intro hy
      by_contra hyC
      have hlt' : v y < v c := by
        by_cases hEq : o y = o c
        · exact hBelow y hy.1 hyC hEq
        · exact hlt (lt_of_le_of_ne (hBound y hy.1) hEq)
      exact (not_lt.mpr (hy.2 c hcMax.1)) hlt'

/-- At a genuine next blowup the test history supplies centre inclusion.
Extending the whole mark-one canonical prefix is equivalent to the three
first-order and tie conditions, all evaluated on that physical prefix. -/
theorem original_next_canonical_iff_first_order_and_ties
    {X Y Z : CMfd.{0} (n+1)} (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (C : Set Y) (c : Y) (hc : c ∈ C)
    (π : Z → Y) (hπ : IsBlowupAlong (n+1) C π) :
    let P : MarkedIdeal (n+1) X := ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩
    let S := (geoTransformAlong P T).cosupp
    let o := nmOrd (geoTransformAlong P T)
    let v := (canonicalInvariant (n+1)).inv P T
    IsGeoTestTower P (.step T C π hπ) →
    IsCanonical P ((canonicalInvariant (n+1)).inv P) T →
    (IsCanonical P ((canonicalInvariant (n+1)).inv P) (.step T C π hπ) ↔
      (∀ y ∈ S, o y ≤ o c) ∧
      (∀ y ∈ C, o y = o c ∧ v y = v c) ∧
      (∀ y ∈ S, y ∉ C → o y = o c → v y < v c)) := by
  dsimp only
  intro hTest hBefore
  have hMax := original_maxLocus_iff_first_order_and_ties W E T C c hc hTest.2.2.1
  dsimp only at hMax
  constructor
  · intro hCan
    rcases hCan.2 with hEmpty | hMaximum
    · exact False.elim (Set.notMem_empty c (hEmpty ▸ hc))
    · exact hMax.mp hMaximum
  · exact fun hCriteria => ⟨hBefore,Or.inr (hMax.mpr hCriteria)⟩

end
end Hironaka.HironakaG8OriginalSingularPrefix
