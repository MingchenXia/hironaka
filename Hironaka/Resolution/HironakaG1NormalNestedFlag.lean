import Hironaka.Resolution.HironakaG1NormalNestedOrderMap
import Hironaka.Resolution.HironakaActualNativeSectionOriginalCuts

/-!
# Finite flags of nested Step One recodings

Every successor inserts its own nonmonomial and level-zero companion letters
at the current recursion depth. The flag composes the resulting embeddings.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NormalNestedFlag

open CanonicalCentres ResolutionDriver HironakaG1NormalNestedOrderMap

noncomputable section

/-- A finite sequence of adjacent-depth recodings. Both the fixed order at
each outer level and the recoding of the next inner value may vary by step. -/
inductive NestedOrderFlag : ℕ → ℕ → Type
  | refl (d : ℕ) : NestedOrderFlag d d
  | step {q d : ℕ} (F : NestedOrderFlag q d) (orderAtLevel : ℕ → ℕ)
      (inner : ValTy d ↪o ValTy d) : NestedOrderFlag q (d + 1)

/-- The actual composition of all nested maps in the flag. -/
def NestedOrderFlag.embedding {q d : ℕ} (F : NestedOrderFlag q d) :
    (ℕ ×ₗ WithTop (ValTy q)) ↪o (ℕ ×ₗ WithTop (ValTy d)) :=
  match F with
  | .refl _ => OrderEmbedding.ofStrictMono id strictMono_id
  | .step F o inner => F.embedding.trans (nestedStepEmbedding o inner.strictMono)

@[simp] theorem NestedOrderFlag.embedding_refl (q : ℕ) (w : ℕ ×ₗ WithTop (ValTy q)) :
    (NestedOrderFlag.refl q).embedding w = w :=
  rfl

@[simp] theorem NestedOrderFlag.embedding_step {q d : ℕ} (F : NestedOrderFlag q d)
    (o : ℕ → ℕ) (inner : ValTy d ↪o ValTy d) (w : ℕ ×ₗ WithTop (ValTy q)) :
    (F.step o inner).embedding w = nestedStep o inner (F.embedding w) :=
  rfl

/-- Concatenate finite flags without changing intermediate recursion depths. -/
def NestedOrderFlag.append {q d e : ℕ}
    (F : NestedOrderFlag q d) (G : NestedOrderFlag d e) : NestedOrderFlag q e :=
  match G with
  | .refl _ => F
  | .step G o inner => (F.append G).step o inner

theorem NestedOrderFlag.embedding_append {q d e : ℕ}
    (F : NestedOrderFlag q d) (G : NestedOrderFlag d e) (w : ℕ ×ₗ WithTop (ValTy q)) :
    (F.append G).embedding w = G.embedding (F.embedding w) := by
  induction G with
  | refl => rfl
  | step G o inner ih =>
    simpa only [NestedOrderFlag.append, NestedOrderFlag.embedding_step] using
      congrArg (nestedStep o inner) ih

def NestedOrderFlag.length {q d : ℕ} (F : NestedOrderFlag q d) : ℕ :=
  match F with
  | .refl _ => 0
  | .step F _ _ => F.length + 1

theorem NestedOrderFlag.depth_eq {q d : ℕ} (F : NestedOrderFlag q d) :
    d = q + F.length := by
  induction F with
  | refl => rfl
  | step F o inner ih =>
    change _ + 1 = q + (F.length + 1)
    rw [← Nat.add_assoc, ← ih]

/-- A nonempty flag leaves every image lower entry finite at its outermost
depth, while each inserted companion retains its own inner value. -/
theorem NestedOrderFlag.outer_ne_top {q d : ℕ} (F : NestedOrderFlag q d)
    (hF : 0 < F.length) (w : ℕ ×ₗ WithTop (ValTy q)) :
    (ofLex (F.embedding w)).2 ≠ ⊤ := by
  cases F with
  | refl => exact (Nat.not_lt_zero _ hF).elim
  | step F o inner => exact nestedLower_ne_top _ inner _

theorem NestedOrderFlag.maxLocus_comp {q d : ℕ} {A : Type*} (F : NestedOrderFlag q d)
    (g : A → ℕ ×ₗ WithTop (ValTy q)) (S : Set A) :
    maxLocus (F.embedding ∘ g) S = maxLocus g S :=
  MaxLocusLocal.maxLocus_comp_strictMono F.embedding.strictMono g S

open Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG1NormalCentreComparison
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG8HomStable
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionStepOneHistory
  HironakaActualNativeSectionOriginalCuts
  RelativePrincipalizationSpan StepOneValue

/-- An actual marked record and its Step One history at the given lower depth. -/
structure StepOneHistory (q : ℕ) where
  dim : ℕ
  positive : 0 < dim
  source : CMfd.{0} dim
  target : CMfd.{0} dim
  record : MarkedIdeal dim source
  tower : BlowupTower source target

abbrev StepOneHistory.read {q : ℕ} (H : StepOneHistory q) :
    H.target → ℕ ×ₗ WithTop (ValTy q) :=
  Seq.StepOneValueMasked.stepOneInvM (invFamily H.positive q) H.record H.tower

abbrev StepOneHistory.cosupp {q : ℕ} (H : StepOneHistory q) : Set H.target :=
  (geoTransformAlong H.record H.tower).cosupp

abbrev StepOneHistory.canonical {q : ℕ} (H : StepOneHistory q) : Prop :=
  IsCanonical H.record (Seq.StepOneValueMasked.stepOneInvM (invFamily H.positive q) H.record) H.tower

abbrev StepOneHistory.headCanonical {q : ℕ} (H : StepOneHistory q) (j : ℕ) : Prop :=
  IsCanonical H.record (Seq.StepOneValueMasked.stepOneInvM (invFamily H.positive q) H.record)
    (head H.tower j)

private theorem recastTarget_canonical_iff {m : ℕ} {Λ : Type} [LinearOrder Λ]
    {X Y Z : CMfd.{0} m} (M : MarkedIdeal m X)
    (f : ∀ {W : CMfd.{0} m}, BlowupTower X W → W → Λ)
    (T : BlowupTower X Y) (e : Y = Z) :
    IsCanonical M f (recastTarget e T) ↔ IsCanonical M f T := by
  cases e
  exact Iff.rfl

private theorem recast_append {m : ℕ} {A B C D : CMfd.{0} m}
    (T : BlowupTower A B) (S : BlowupTower B C) (e : B = D) :
    (recastTarget e T).append (recastSource e S) = T.append S := by
  cases e
  rfl

private theorem StepOneHistory.read_level {q : ℕ} (H : StepOneHistory q) (x : H.target) :
    (ofLex (H.read x)).1 = level H.record H.tower x :=
  Seq.StepOneValueMasked.stepOneInvL_fst (invFamily H.positive q) H.record
    (StepOneValueMasked.lowerMarkedM H.record) H.tower x

/-- A certified adjacent pair. The records and histories are part of the
type so that the same intermediate history is used when composing pairs. -/
structure NestedStepComparison {q : ℕ} (L : StepOneHistory q) (H : StepOneHistory (q + 1)) where
  dim_succ : H.dim = L.dim + 1
  pointMap : L.target → H.target
  pointMap_injective : Function.Injective pointMap
  cosupp_image : pointMap '' L.cosupp = H.cosupp
  orderAtLevel : ℕ → ℕ
  inner : ValTy q ↪o ValTy q
  read_eq : ∀ x ∈ L.cosupp, H.read (pointMap x) = nestedStep orderAtLevel inner (L.read x)
  canonical_iff : L.canonical ↔ H.canonical
  canonical_head_iff : ∀ j, L.headCanonical j ↔ H.headCanonical j

/-- A finite chain of certified comparisons of actual Step One histories. -/
inductive ActualNestedFlag : {q d : ℕ} → StepOneHistory q → StepOneHistory d → Type 1
  | refl {q : ℕ} (L : StepOneHistory q) : ActualNestedFlag L L
  | step {q d : ℕ} {L : StepOneHistory q} {H : StepOneHistory d}
      {P : StepOneHistory (d + 1)} (F : ActualNestedFlag L H)
      (E : NestedStepComparison H P) : ActualNestedFlag L P

/-- The endpoint map and typed value flag obtained from finite composition. -/
structure NestedFlagComparison {q d : ℕ} (L : StepOneHistory q) (H : StepOneHistory d) where
  flag : NestedOrderFlag q d
  dim_eq : H.dim = L.dim + flag.length
  pointMap : L.target → H.target
  pointMap_injective : Function.Injective pointMap
  cosupp_image : pointMap '' L.cosupp = H.cosupp
  read_eq : ∀ x ∈ L.cosupp, H.read (pointMap x) = flag.embedding (L.read x)
  canonical_iff : L.canonical ↔ H.canonical
  canonical_head_iff : ∀ j, L.headCanonical j ↔ H.headCanonical j

/-- Compose the actual endpoint maps, all raw reads, and canonicality
equivalences, including histories with empty centres. -/
def ActualNestedFlag.compare {q d : ℕ} {L : StepOneHistory q} {H : StepOneHistory d}
    (F : ActualNestedFlag L H) : NestedFlagComparison L H := by
  induction F with
  | refl L =>
    exact ⟨.refl _, rfl, id, Function.injective_id, image_id _, fun _ _ => rfl, Iff.rfl, fun _ => Iff.rfl⟩
  | step F E ih =>
    have hDim := E.dim_succ.trans (congrArg (· + 1) ih.dim_eq)
    refine ⟨ih.flag.step E.orderAtLevel E.inner, hDim.trans (Nat.add_assoc ..),
      E.pointMap ∘ ih.pointMap,
      E.pointMap_injective.comp ih.pointMap_injective, ?_, ?_,
      ih.canonical_iff.trans E.canonical_iff, fun j => (ih.canonical_head_iff j).trans (E.canonical_head_iff j)⟩
    · calc
        _ = E.pointMap '' (ih.pointMap '' _) := (image_image E.pointMap ih.pointMap _).symm
        _ = _ := by rw [ih.cosupp_image, E.cosupp_image]
    · intro x hx
      change _ = nestedStep E.orderAtLevel E.inner (ih.flag.embedding _)
      exact (E.read_eq _ (ih.cosupp_image ▸ mem_image_of_mem ih.pointMap hx)).trans
        (congrArg (nestedStep E.orderAtLevel E.inner) (ih.read_eq x hx))

/-- The endpoint map reflects and preserves both strict and weak order and
equality on actual cosupport. -/
theorem NestedFlagComparison.comparisons {q d : ℕ} {L : StepOneHistory q} {H : StepOneHistory d}
    (E : NestedFlagComparison L H) (x : L.target) (hx : x ∈ L.cosupp)
    (y : L.target) (hy : y ∈ L.cosupp) :
    (H.read (E.pointMap x) < H.read (E.pointMap y) ↔ L.read x < L.read y) ∧
      (H.read (E.pointMap x) ≤ H.read (E.pointMap y) ↔ L.read x ≤ L.read y) ∧
      (H.read (E.pointMap x) = H.read (E.pointMap y) ↔ L.read x = L.read y) := by
  rw [E.read_eq x hx, E.read_eq y hy]
  exact ⟨E.flag.embedding.strictMono.lt_iff_lt, E.flag.embedding.strictMono.le_iff_le,
    E.flag.embedding.injective.eq_iff⟩

/-- Exact image and preimage of maxima at the ends of the flag. -/
theorem NestedFlagComparison.max_loci {q d : ℕ} {L : StepOneHistory q} {H : StepOneHistory d}
    (E : NestedFlagComparison L H) :
    E.pointMap '' maxLocus L.read L.cosupp = maxLocus H.read H.cosupp ∧
      E.pointMap ⁻¹' maxLocus H.read H.cosupp = maxLocus L.read L.cosupp := by
  have hImage : E.pointMap '' maxLocus L.read L.cosupp = maxLocus H.read H.cosupp := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
      refine ⟨E.cosupp_image ▸ mem_image_of_mem _ hx, fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := E.cosupp_image.symm ▸ hy
      exact (E.comparisons z hz x hx).2.1.mpr (hmax z hz)
    · rintro ⟨hy, hmax⟩
      obtain ⟨x, hx, rfl⟩ := E.cosupp_image.symm ▸ hy
      exact ⟨x, ⟨hx, fun z hz => (E.comparisons z hz x hx).2.1.mp
        (hmax _ (E.cosupp_image ▸ mem_image_of_mem _ hz))⟩, rfl⟩
  exact ⟨hImage, hImage ▸ preimage_image_eq _ E.pointMap_injective⟩

section LiteralEdge

variable {n q : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
  {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
  (hn : 0 < n)
  (N : BlowupTower (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
    (nativeManifold (Nat.le_succ n) V hV))

local notation "X" => CMfd.of (n := n + 1) (productOpen U)
local notation "A" => nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
local notation "B" => nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U)
  (zeroPlane_regular U) (sectionMarked Q)
local notation "P" => properNormalMarked Q
local notation "Z" => nativeManifold (Nat.le_succ n) V hV

/-- The actual padded Step One record and tower at the upper depth. -/
abbrev paddedHistory (q : ℕ) : StepOneHistory (q + 1) :=
  ⟨n + 1, Nat.succ_pos n, X, Y, P, T⟩

/-- The literal section record and tower at the adjacent native depth. -/
abbrev literalSectionHistory (q : ℕ) : StepOneHistory q :=
  ⟨n, hn, A, Z, B, N⟩

set_option backward.isDefEq.respectTransparency false in
private theorem literal_cosupp_image (hQ : IsInvDomain (q + 1) Q)
    (hT : IsGeoTestTower P T) {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (sectionMarked Q).E T V hVc hV N) :
    (Subtype.val : Z → Y) '' (literalSectionHistory Q hn N q).cosupp = (paddedHistory Q T q).cosupp := by
  let Sec := sectionMarked Q
  have hSec : IsInvDomain (q + 1) Sec := section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hCos : (paddedHistory Q T q).cosupp = (geoTransformAlong Sec T).cosupp :=
    ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 T).2 hT
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : NormalCrossings.IsTransverse (n + 1) (zeroPlane U) Sec.E := by
    change NormalCrossings.IsTransverse (n + 1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier _ _
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hPre : (literalSectionHistory Q hn N q).cosupp = (Subtype.val : Z → Y) ⁻¹' (geoTransformAlong Sec T).cosupp :=
    HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift
      (Nat.succ_pos n) hSec.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSec.isWellFormed.isCoherent hg)
  have hRange := (geoTransformAlong Sec T).cosupp_subset_N.trans
    (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift Sec hSupport)
  rw [hPre, hCos, image_preimage_eq_inter_range, Subtype.range_coe]
  exact inter_eq_left.mpr hRange

set_option backward.isDefEq.respectTransparency false in
private theorem literal_read_level (hQ : IsInvDomain (q + 1) Q)
    {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (sectionMarked Q).E T V hVc hV N) (x : Z) :
    (ofLex ((paddedHistory Q T q).read x.val)).1 =
      (ofLex ((literalSectionHistory Q hn N q).read x)).1 := by
  let Sec := sectionMarked Q
  have hSec : IsInvDomain (q + 1) Sec := section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hChron := actual_section_step_one_chronology U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d hLift
  rw [StepOneHistory.read_level, StepOneHistory.read_level]
  exact (HironakaG8MemberLoci.level_eq_of_E_eq (show MarkedIdeal.E P = Sec.E from rfl) T x.val).trans
    (hChron.2.2.1 x).1

set_option backward.isDefEq.respectTransparency false in
/-- Construct a flag edge from an actual literal lift. The endpoint raw
formula supplies its read, and raw lower equations on the actual proper
paired prefixes supply its canonicality equivalence. -/
def literalNestedStepComparison (hQ : IsInvDomain (q + 1) Q)
    (hT : IsGeoTestTower P T) {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (sectionMarked Q).E T V hVc hV N)
    (orderAtLevel : ℕ → ℕ) (inner : ValTy q ↪o ValTy q)
    (hRead : ∀ x ∈ (literalSectionHistory Q hn N q).cosupp,
      (ofLex ((paddedHistory Q T q).read x.val)).2 =
        nestedLower (orderAtLevel (ofLex ((literalSectionHistory Q hn N q).read x)).1)
          inner (ofLex ((literalSectionHistory Q hn N q).read x)).2)
    (hPrefix : ∀ {Y' : CMfd.{0} (n + 1)} (T' : BlowupTower X Y')
      {V' : Set Y'} {hV'c : IsClosed V'} {hV' : ∀ y ∈ V', RegularAtDim (n := n + 1) V' y n}
      (N' : BlowupTower A (nativeManifold (Nat.le_succ n) V' hV')),
      Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (sectionMarked Q).E T' V' hV'c hV' N' →
      (∃ S : BlowupTower Y' Y, T'.append S = T ∧ 0 < S.length) →
      (∃ R : BlowupTower (nativeManifold (Nat.le_succ n) V' hV') Z, N'.append R = N) →
      ∃ (o' : ℕ → ℕ) (inner' : ValTy q ↪o ValTy q),
        ∀ x ∈ (literalSectionHistory Q hn N' q).cosupp,
          (ofLex ((paddedHistory Q T' q).read x.val)).2 =
            nestedLower (o' (ofLex ((literalSectionHistory Q hn N' q).read x)).1)
              inner' (ofLex ((literalSectionHistory Q hn N' q).read x)).2) :
    NestedStepComparison (literalSectionHistory Q hn N q) (paddedHistory Q T q) where
  dim_succ := rfl
  pointMap := Subtype.val
  pointMap_injective := Subtype.val_injective
  cosupp_image := literal_cosupp_image Q T hn N hQ hT hLift
  orderAtLevel := orderAtLevel
  inner := inner
  read_eq := by
    intro x hx
    exact congrArg toLex (Prod.ext (literal_read_level Q T hn N hQ hLift x) (hRead x hx))
  canonical_iff := by
    refine (positive_normal_canonical_iff_of_prefix_branch_comparisons hn Q hQ T hT hLift ?_).symm
    intro Y' T' V' hV'c hV' N' hLift' hTail hNativeTail
    obtain ⟨o', inner', hRaw⟩ := hPrefix T' N' hLift' hTail hNativeTail
    exact ⟨lowerBranchComparison_of_nestedLower o' inner'.strictMono
      (paddedHistory Q T' q).read (literalSectionHistory Q hn N' q).read
      Subtype.val _ hRaw⟩

  canonical_head_iff := by
    intro j
    obtain ⟨V₀, hV₀c, hV₀, e, hHead, _⟩ := Lift.original_head_tails hLift j
    let N₀ := recastTarget e (head N j)
    let R₀ := recastSource e (tail N j)
    have hNativeAppend : N₀.append R₀ = N :=
      (recast_append (head N j) (tail N j) e).trans (head_append_tail N j)
    have hTest₀ : IsGeoTestTower P (head T j) :=
      ((isGeoTestTower_iff_head_tail P T j).mp hT).1
    have hCompare := positive_normal_canonical_iff_of_prefix_branch_comparisons
      hn Q hQ (head T j) hTest₀ (N := N₀) hHead (by
        intro Y' T' V' hV'c hV' N' hLift' hTail hNativeTail
        obtain ⟨S, hS, hSpos⟩ := hTail
        obtain ⟨R, hR⟩ := hNativeTail
        have hAmbient : ∃ U : BlowupTower Y' Y, T'.append U = T ∧ 0 < U.length := by
          refine ⟨S.append (tail T j), ?_, ?_⟩
          · rw [← BlowupTower.append_assoc, hS, head_append_tail]
          · rw [BlowupTower.length_append]
            exact Nat.lt_of_lt_of_le hSpos (Nat.le_add_right _ _)
        have hNative : ∃ U : BlowupTower (nativeManifold (Nat.le_succ n) V' hV') Z,
            N'.append U = N :=
          ⟨R.append R₀, by rw [← BlowupTower.append_assoc, hR, hNativeAppend]⟩
        obtain ⟨o', inner', hRaw⟩ := hPrefix T' N' hLift' hAmbient hNative
        exact ⟨lowerBranchComparison_of_nestedLower o' inner'.strictMono
          (paddedHistory Q T' q).read (literalSectionHistory Q hn N' q).read
          Subtype.val _ hRaw⟩)
    exact (recastTarget_canonical_iff B _ (head N j) e).symm.trans hCompare.symm

end LiteralEdge

end

end Hironaka.HironakaG1NormalNestedFlag
