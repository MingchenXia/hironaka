import Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageSuccessor
import Hironaka.Analytic.Unibranch.RIsoAModification

/-!
# Cover independence at the SAME actual canonical prefix

The common prefix atlas is the union of two ordinary finite presentations.
Initial whole class data and actual prefix isomorphisms derive current full
value transport, hence equality of actual footprint values and whole centres.
The native successors are then uniquely isomorphic, naturally under actual
open refinements. No desired centre comparison is a caller premise.

Blueprint FIRST: `hironaka-g1-canonical-stage-choice-independence.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageChoiceIndependence

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaG11BlowupLocality SmoothCentreModification
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι κ ν ρ : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)

/-- Actual original windows of one subcover of the common prefix atlas. -/
abbrev windows (f : κ → ι) : κ → DimEmbedding X N := fun i => w (f i)

/-- The SAME actual original records, not records reselected on transformed spaces. -/
abbrev records (f : κ → ι) : ∀ i, MarkedIdeal N (Amb (windows w f) i) := fun i => M (f i)

/-- Reindex the actual finite canonical prefixes, retaining all existing steps. -/
def reindexStage (f : κ → ι) :
    GStage B.toResolutionInvariant (records w M f) (mapAdm (windows w f)) m where
  T i := s.T (f i)
  length i := s.length (f i)
  canonical i := s.canonical (f i)
  compatible i j := s.compatible (f i) (f j)

/-- Reindex the SAME original current space, map and complete native window maps. -/
abbrev reindexOriginal (f : κ → ι) : XStage (windows w f) (reindexStage w M B s f).T where
  Y := xs.Y
  q := xs.q
  isSingularCentreModification := xs.isSingularCentreModification
  carrier i := xs.carrier (f i)
  analytic i := xs.analytic (f i)
  map i := xs.map (f i)
  isOpenImmersion i := xs.isOpenImmersion (f i)
  carrier_eq i := xs.carrier_eq (f i)
  square i := xs.square (f i)
  range_map i := xs.range_map (f i)

include hClass in
/-- Ordinary initial whole class data restrict to any actual subcover. -/
theorem reindexClass (f : κ → ι) : InitialClassData (windows w f) (records w M f) :=
  fun i j => hClass (f i) (f j)

/-- Only ordinary footprint/cover data on the actual native prefix windows.
There is no invariant-value, centre, ideal or future-history comparison field. -/
structure Cover (f : κ → ι) where
  K : ∀ i, Set (w (f i)).ambient
  cosuppCover : ∀ i (c : (w (f i)).carrier), c.val ∈ (M (f i)).cosupp →
    ∃ j, ∃ c' : (w (f j)).carrier, c'.val ∈ K j ∧
      (w (f j)).toLocalEmbedding.toPoint c' = (w (f i)).toLocalEmbedding.toPoint c
  compact : ∀ i, IsCompact (K i)
  covers : ∀ y : xs.Y.obj.left, ∃ i, ∃ c : xs.carrier (f i),
    (xs.map (f i)).hom.left.base c = y

include hD hState in
private theorem current_cosupp_subset (i : ι) : rcos M s.T i ⊆ xs.carrier i := by
  rw [xs.carrier_eq i]
  exact ((hState i).hsTowerState (s.T i).2
    (B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (hD i) (s.T i).2
      (s.canonical i))).2.1

include hD hClass in
/-- The full original current values and cosupports agree at the SAME native
point, derived from initial class data and genuine current-prefix isomorphisms. -/
theorem cosupp_value_of_map_eq {i j : ι} (y : xs.carrier i) (z : xs.carrier j)
    (hyz : (xs.map i).hom.left.base y = (xs.map j).hom.left.base z) :
    (y.val ∈ rcos M s.T i ↔ z.val ∈ rcos M s.T j) ∧
      (y.val ∈ rcos M s.T i → rvalue B.toResolutionInvariant M s.T j z.val =
        rvalue B.toResolutionInvariant M s.T i y.val) := by
  have hyp := xs.proj_mem i y
  have hzp := xs.proj_mem j z
  have hX : (w j).toLocalEmbedding.toPoint ⟨_, hzp⟩ =
      (w i).toLocalEmbedding.toPoint ⟨_, hyp⟩ := by
    rw [← xs.square j z hzp, ← xs.square i y hyp, hyz]
  obtain ⟨U, U', Φ, hc', -, -, hadm⟩ := adm_exists_map w i j ⟨_, hyp⟩ ⟨_, hzp⟩ hX
  obtain ⟨χ, hiso⟩ := s.compatible i j U U' Φ hadm
  have hzU : z.val ∈ openPreimage (s.T j).2 U' := hc'
  have hmem := (xs.mem_carrier_iff hadm hiso ⟨z.val, hzU⟩).mpr z.property
  have hpt := xs.map_lift hadm hiso z hzU hmem
  have hχz : ((χ ⟨z.val, hzU⟩ : openPreimage (s.T i).2 U) : (s.T i).1) = y.val :=
    congrArg Subtype.val (xs.map_injective i (hpt.trans hyz.symm))
  have h := recordsTransport w M B hD hClass i j U U' Φ hadm
    (s.T i).2 (s.T j).2 (s.canonical i) (s.canonical j) χ hiso ⟨z.val, hzU⟩
  constructor
  · simpa only [hχz] using h.1
  · intro hy
    have hv := h.2 (by simpa only [hχz] using hy)
    simpa only [hχz] using hv

variable {f : κ → ι} {g : ν → ι} {r : ρ → ι}
  (P : Cover w M B s xs f) (Q : Cover w M B s xs g)

/-- The ACTUAL footprint-value set of this ordinary reindexed cover. -/
def footValues : Set Λ :=
  gfootValues B.toResolutionInvariant (records w M f) P.K (reindexStage w M B s f).T

/-- Its internally constructed actual local canonical centres. -/
def localCentres : ManifoldSmoothCentres xs.Y κ :=
  HironakaG1CanonicalStageCentreIdeal.localCentres (windows w f) (records w M f) B
    (fun i => hD (f i)) (reindexClass w M hClass f) (fun i => H (f i))
    (fun i => hState (f i)) P.K P.cosuppCover (reindexStage w M B s f)
    (reindexOriginal w M B s xs f)

/-- The SAME centre support actually constructed from this reindexed cover. -/
def support : Set xs.Y.obj.left := (localCentres w M B hD hClass H hState s xs P).support

include hD hClass hState in
private theorem footValues_subset : footValues w M B s xs P ⊆ footValues w M B s xs Q := by
  intro v hv
  obtain ⟨i, y, ⟨hy, -⟩, rfl⟩ := mem_iUnion.mp hv
  have hyc : y ∈ xs.carrier (f i) := current_cosupp_subset w M B hD H hState s xs (f i) hy
  obtain ⟨j, z, hzy⟩ := Q.covers ((xs.map (f i)).hom.left.base ⟨y, hyc⟩)
  have h := cosupp_value_of_map_eq w M B hD hClass s xs ⟨y, hyc⟩ z hzy.symm
  have hz : z.val ∈ rcos M s.T (g j) := h.1.mp hy
  have hcos : ∀ i, (M (g i)).cosupp ⊆ (w (g i)).carrier := fun i =>
    ((hState (g i)).hsTowerState (BlowupTower.refl : BlowupTower (Amb w (g i)) (Amb w (g i)))
      (by trivial)).2.1
  have hv := rvalue_mem_gfootValues (fun i => hD (g i)) hcos Q.cosuppCover
    (adm_exists_map (windows w g))
    (recordsTransport (windows w g) (records w M g) B (fun i => hD (g i))
      (reindexClass w M hClass g)) (reindexStage w M B s g) j z.val hz
  change rvalue B.toResolutionInvariant M s.T (g j) z.val ∈ footValues w M B s xs Q at hv
  rw [h.2 hy] at hv
  exact hv

include hD hClass hState in
/-- No common bound/maximum packet is assumed: the actual footprint values agree. -/
theorem footValues_eq : footValues w M B s xs P = footValues w M B s xs Q :=
  Set.Subset.antisymm (footValues_subset w M B hD hClass H hState s xs P Q)
    (footValues_subset w M B hD hClass H hState s xs Q P)

/-- Actual canonical centre transport between the two different ordinary covers. -/
theorem centre_of_map_eq (i : κ) (j : ν) (y : xs.carrier (f i)) (z : xs.carrier (g j))
    (hyz : (xs.map (f i)).hom.left.base y = (xs.map (g j)).hom.left.base z)
    (hy : y.val ∈ (localCentres w M B hD hClass H hState s xs P).centre i) :
    z.val ∈ (localCentres w M B hD hClass H hState s xs Q).centre j := by
  have h := cosupp_value_of_map_eq w M B hD hClass s xs y z hyz
  refine ⟨h.1.mp hy.1, ?_⟩
  change rvalue B.toResolutionInvariant M s.T (g j) z.val ∈ upperBounds (footValues w M B s xs Q)
  rw [h.2 hy.1, ← footValues_eq w M B hD hClass H hState s xs P Q]
  exact hy.2

private theorem support_subset : support w M B hD hClass H hState s xs P ⊆
    support w M B hD hClass H hState s xs Q := by
  intro x hx
  obtain ⟨i, y, hy, rfl⟩ := (localCentres w M B hD hClass H hState s xs P).mem_support.mp hx
  obtain ⟨j, z, hzy⟩ := Q.covers ((xs.map (f i)).hom.left.base y)
  exact (localCentres w M B hD hClass H hState s xs Q).mem_support.mpr
    ⟨j, z, centre_of_map_eq w M B hD hClass H hState s xs P Q i j y z hzy.symm hy, hzy⟩

/-- Equality of the actually constructed global centres, derived from ordinary data. -/
theorem support_eq : support w M B hD hClass H hState s xs P =
    support w M B hD hClass H hState s xs Q :=
  Set.Subset.antisymm (support_subset w M B hD hClass H hState s xs P Q)
    (support_subset w M B hD hClass H hState s xs Q P)

local notation "CP" => support w M B hD hClass H hState s xs P
local notation "CQ" => support w M B hD hClass H hState s xs Q
local notation "JP" => intrinsicReducedCentreIdealModule xs.Y.obj.left CP
local notation "JQ" => intrinsicReducedCentreIdealModule xs.Y.obj.left CQ
local notation "bP" => intrinsicReducedCentreIdealInclusion xs.Y.obj.left CP
local notation "bQ" => intrinsicReducedCentreIdealInclusion xs.Y.obj.left CQ

/-- Literal equality of the ENTIRE actual intrinsic unit submodules. -/
theorem wholeSubmodule_eq : intrinsicReducedCentreSubmodule xs.Y.obj.left CP =
    intrinsicReducedCentreSubmodule xs.Y.obj.left CQ :=
  congrArg (intrinsicReducedCentreSubmodule xs.Y.obj.left)
    (support_eq w M B hD hClass H hState s xs P Q)

/-- The whole ideal comparison on the SAME original scalar sheaf. -/
def wholeIdealIso : JP ≅ JQ :=
  { hom := ⟨PresheafOfModules.Submodule.homOfLE
      (wholeSubmodule_eq w M B hD hClass H hState s xs P Q).le⟩
    inv := ⟨PresheafOfModules.Submodule.homOfLE
      (wholeSubmodule_eq w M B hD hClass H hState s xs P Q).ge⟩
    hom_inv_id := by ext V z; rfl
    inv_hom_id := by ext V z; rfl }

theorem wholeIdealIso_hom_comp_inclusion :
    (wholeIdealIso w M B hD hClass H hState s xs P Q).hom ≫ bQ = bP := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι
    (wholeSubmodule_eq w M B hD hClass H hState s xs P Q).le

theorem wholeIdealIso_inv_comp_inclusion :
    (wholeIdealIso w M B hD hClass H hState s xs P Q).inv ≫ bP = bQ := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι
    (wholeSubmodule_eq w M B hD hClass H hState s xs P Q).ge

/-- Every whole section ideal, in the original scalar ring on every original open. -/
theorem sectionIdeal_eq (V : Opens xs.Y.obj.left.toTopCat) :
    intrinsicReducedCentreSectionIdeal xs.Y.obj.left CP V =
      intrinsicReducedCentreSectionIdeal xs.Y.obj.left CQ V :=
  congrArg (fun C => intrinsicReducedCentreSectionIdeal xs.Y.obj.left C V)
    (support_eq w M B hD hClass H hState s xs P Q)

/-- Every entire original stalk-image ideal. -/
theorem stalkIdeal_eq (y : xs.Y.obj.left) :
    intrinsicCentreStalkRange xs.Y.obj.left CP y = intrinsicCentreStalkRange xs.Y.obj.left CQ y :=
  congrArg (fun C => intrinsicCentreStalkRange xs.Y.obj.left C y)
    (support_eq w M B hD hClass H hState s xs P Q)

/-- The actual prescribed next strict window of this ordinary cover. -/
abbrev nextWindow (i : κ) : SourceReducedComplexSpace :=
  HironakaG1CanonicalStageSuccessor.nextWindow (windows w f) (records w M f) B
    (fun i => hD (f i)) (reindexClass w M hClass f) (fun i => H (f i))
    (fun i => hState (f i)) P.K P.cosuppCover (reindexStage w M B s f)
    (reindexOriginal w M B s xs f) i

/-- Its actual full native strict-transform projection. -/
abbrev windowProjection (i : κ) : nextWindow w M B hD hClass H hState s xs P i ⟶
    ofClosedAnalytic (xs.carrier (f i)) (xs.analytic (f i)) :=
  HironakaG1CanonicalStageSuccessor.nextWindowProjection (windows w f) (records w M f) B
    (fun i => hD (f i)) (reindexClass w M hClass f) (fun i => H (f i))
    (fun i => hState (f i)) P.K P.cosuppCover (reindexStage w M B s f)
    (reindexOriginal w M B s xs f) i

section Successors

variable [Finite κ] [Finite ν] [Finite ρ]

/-- Actual output objects of the ordinary-data successor construction. -/
abbrev SuccessorOf : Type _ :=
  HironakaG1CanonicalStageSuccessor.Successor (windows w f) (records w M f) B
    (fun i => hD (f i)) (reindexClass w M hClass f) (fun i => H (f i))
    (fun i => hState (f i)) P.K P.cosuppCover (reindexStage w M B s f)
    (reindexOriginal w M B s xs f) P.compact

/-- An actual successor is constructed internally; no blowup predicate is a caller input. -/
def constructedSuccessor : SuccessorOf w M B hD hClass H hState s xs P :=
  Classical.choice (HironakaG1CanonicalStageSuccessor.exists_successor (windows w f) (records w M f) B
    (fun i => hD (f i)) (reindexClass w M hClass f) (fun i => H (f i))
    (fun i => hState (f i)) P.K P.cosuppCover (reindexStage w M B s f)
    (reindexOriginal w M B s xs f) P.compact)

variable (a : SuccessorOf w M B hD hClass H hState s xs P)
  (b : SuccessorOf w M B hD hClass H hState s xs Q)

omit [Finite κ] in
private theorem other_isIdealBlowup : IsIdealBlowup b.p JP bP := by
  have h := b.isIdealBlowup
  change IsIdealBlowup b.p JQ bQ at h
  rw [← support_eq w M B hD hClass H hState s xs P Q] at h
  exact h

private theorem comparison_exists : ∃ e : a.Y ≅ b.Y,
    e.hom ≫ b.p = a.p ∧ ∀ t : a.Y ⟶ b.Y, t ≫ b.p = a.p → t = e.hom :=
  RIsoAModification.isIdealBlowup_exists_unique_iso a.isIdealBlowup
    (other_isIdealBlowup w M B hD hClass H hState s xs P Q b)

/-- The actual cover comparison, AFTER deriving equality of the whole centres. -/
def successorIso : a.Y ≅ b.Y :=
  (comparison_exists w M B hD hClass H hState s xs P Q a b).choose

/-- The comparison preserves the FULL native projection. -/
theorem successorIso_projection :
    (successorIso w M B hD hClass H hState s xs P Q a b).hom ≫ b.p = a.p :=
  (comparison_exists w M B hD hClass H hState s xs P Q a b).choose_spec.1

/-- Native uniqueness applies to every full morphism, not only point maps. -/
theorem successorHom_unique (t : a.Y ⟶ b.Y) (ht : t ≫ b.p = a.p) :
    t = (successorIso w M B hD hClass H hState s xs P Q a b).hom :=
  (comparison_exists w M B hD hClass H hState s xs P Q a b).choose_spec.2 t ht

/-- EVERY prescribed actual strict window retains its full native projection square. -/
theorem successorIso_window_square (i : κ) :
    a.map i ≫ (successorIso w M B hD hClass H hState s xs P Q a b).hom ≫ b.p =
      windowProjection w M B hD hClass H hState s xs P i ≫ xs.map (f i) := by
  rw [successorIso_projection]
  exact a.square i

/-- Naturality on genuine open native refinements. All morphisms and the
refinement's base equation are on the SAME original strict-window spaces. -/
theorem successorIso_refinement {T : SourceReducedComplexSpace} (i : κ) (j : ν)
    (u : T ⟶ nextWindow w M B hD hClass H hState s xs P i)
    (v : T ⟶ nextWindow w M B hD hClass H hState s xs Q j)
    [LocallyRingedSpace.IsOpenImmersion u.hom.left]
    (huv : u ≫ windowProjection w M B hD hClass H hState s xs P i ≫ xs.map (f i) =
      v ≫ windowProjection w M B hD hClass H hState s xs Q j ≫ xs.map (g j)) :
    u ≫ a.map i ≫ (successorIso w M B hD hClass H hState s xs P Q a b).hom =
      v ≫ b.map j := by
  let : LocallyRingedSpace.IsOpenImmersion (a.map i).hom.left := a.isOpenImmersion i
  let : LocallyRingedSpace.IsOpenImmersion (u ≫ a.map i).hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (u.hom.left ≫ (a.map i).hom.left)
    infer_instance
  have hU := hasRankOneData_comp_openImmersion (u ≫ a.map i).hom.left a.p.hom.left
    JP bP a.isIdealBlowup.1
  have hU' : HasRankOneData (nativePulledIdealModule ((u ≫ a.map i) ≫ a.p).hom.left JP bP) := hU
  obtain ⟨_, _, huniq⟩ := (other_isIdealBlowup w M B hD hClass H hState s xs P Q b).2
    T ((u ≫ a.map i) ≫ a.p) hU'
  apply (huniq _ ?_).trans (huniq _ ?_).symm
  · simp only [Category.assoc]
    rw [successorIso_projection w M B hD hClass H hState s xs P Q a b]
  · simp only [Category.assoc]
    rw [b.square j, a.square i]
    exact huv.symm

/-- Triple cocycle for ANY three actual cover outputs, proved by native uniqueness. -/
theorem successorIso_cocycle (R : Cover w M B s xs r)
    (c : SuccessorOf w M B hD hClass H hState s xs R) :
    (successorIso w M B hD hClass H hState s xs P Q a b).trans
        (successorIso w M B hD hClass H hState s xs Q R b c) =
      successorIso w M B hD hClass H hState s xs P R a c := by
  apply Iso.ext
  apply successorHom_unique w M B hD hClass H hState s xs P R a c
  change ((successorIso w M B hD hClass H hState s xs P Q a b).hom ≫
    (successorIso w M B hD hClass H hState s xs Q R b c).hom) ≫ c.p = a.p
  rw [Category.assoc, successorIso_projection w M B hD hClass H hState s xs Q R b c]
  exact successorIso_projection w M B hD hClass H hState s xs P Q a b

end Successors

end
end Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageChoiceIndependence
