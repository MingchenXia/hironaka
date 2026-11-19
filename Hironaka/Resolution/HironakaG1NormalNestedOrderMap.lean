import Hironaka.Resolution.HironakaG1NormalCentreComparison
import Hironaka.Invariant.MaxLocusLocal

/-!
# Nested order recoding for the original Step One types

The extra general letter has a fixed nonmonomial order and a finite companion
whose Step One level is zero. The incoming lower value is read inside that
companion. An incoming top becomes a finite value with an inner level-zero top.
-/

set_option autoImplicit false

open Set

namespace Hironaka.HironakaG1NormalNestedOrderMap

open CanonicalCentres ResolutionDriver HironakaG1NormalCentreComparison
open Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
open scoped Topology Manifold ContDiff

noncomputable section

/-- Insert the nonmonomial order and the finite level-zero companion. -/
def nestedValue {q : ℕ} (o : ℕ) (u : WithTop (ValTy q)) : ValTy (q + 1) :=
  toLex (o, toLex (Sum.inr ((toLex (0, u) : ℕ ×ₗ WithTop (ValTy q)) :
    WithTop (ℕ ×ₗ WithTop (ValTy q)))))

theorem strictMono_nestedValue {q : ℕ} (o : ℕ) : StrictMono (nestedValue (q := q) o) := by
  intro u v huv
  apply Prod.Lex.toLex_lt_toLex.mpr
  refine Or.inr ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr ?_)⟩
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, huv⟩)

/-- Recode the inner finite letters by `δ`, keeping the incoming top inside
the inserted companion. Every output is finite in the outer `WithTop`. -/
def nestedLower {q : ℕ} (o : ℕ) (δ : ValTy q → ValTy q) (u : WithTop (ValTy q)) :
    WithTop (ValTy (q + 1)) :=
  (nestedValue o (WithTop.map δ u) : WithTop (ValTy (q + 1)))

@[simp] theorem nestedLower_coe {q : ℕ} (o : ℕ) (δ : ValTy q → ValTy q) (u : ValTy q) :
    nestedLower o δ (u : WithTop (ValTy q)) =
      (nestedValue o ((δ u : ValTy q) : WithTop (ValTy q)) : WithTop (ValTy (q + 1))) := by
  simp [nestedLower]

@[simp] theorem nestedLower_top {q : ℕ} (o : ℕ) (δ : ValTy q → ValTy q) :
    nestedLower o δ ⊤ = (nestedValue o (⊤ : WithTop (ValTy q)) : WithTop (ValTy (q + 1))) := by
  simp [nestedLower]

theorem nestedLower_ne_top {q : ℕ} (o : ℕ) (δ : ValTy q → ValTy q) (u : WithTop (ValTy q)) :
    nestedLower o δ u ≠ ⊤ :=
  WithTop.coe_ne_top

theorem strictMono_nestedLower {q : ℕ} (o : ℕ) {δ : ValTy q → ValTy q} (hδ : StrictMono δ) :
    StrictMono (nestedLower o δ) :=
  fun _ _ h => WithTop.coe_lt_coe.mpr (strictMono_nestedValue o (hδ.withTop_map h))

/-- Retain the original Step One level. The inserted nonmonomial order is
fixed within each level. -/
def nestedStep {q : ℕ} (o : ℕ → ℕ) (δ : ValTy q → ValTy q)
    (u : ℕ ×ₗ WithTop (ValTy q)) : ℕ ×ₗ WithTop (ValTy (q + 1)) :=
  toLex ((ofLex u).1, nestedLower (o (ofLex u).1) δ (ofLex u).2)

theorem strictMono_nestedStep {q : ℕ} (o : ℕ → ℕ) {δ : ValTy q → ValTy q} (hδ : StrictMono δ) :
    StrictMono (nestedStep o δ) := by
  intro u v huv
  rcases Prod.Lex.lt_iff.mp huv with hlt | ⟨heq, hlt⟩
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
  · apply Prod.Lex.toLex_lt_toLex.mpr
    refine Or.inr ⟨heq, ?_⟩
    change nestedLower (o (ofLex u).1) δ (ofLex u).2 <
      nestedLower (o (ofLex v).1) δ (ofLex v).2
    rw [heq]
    exact strictMono_nestedLower _ hδ hlt

/-- The full nested recoding reflects and preserves both strict and weak order. -/
def nestedStepEmbedding {q : ℕ} (o : ℕ → ℕ) {δ : ValTy q → ValTy q} (hδ : StrictMono δ) :
    (ℕ ×ₗ WithTop (ValTy q)) ↪o (ℕ ×ₗ WithTop (ValTy (q + 1))) :=
  OrderEmbedding.ofStrictMono (nestedStep o δ) (strictMono_nestedStep o hδ)

theorem maxLocus_nestedStep {A : Type*} {q : ℕ} (o : ℕ → ℕ) {δ : ValTy q → ValTy q}
    (hδ : StrictMono δ) (g : A → ℕ ×ₗ WithTop (ValTy q)) (S : Set A) :
    maxLocus (nestedStep o δ ∘ g) S = maxLocus g S :=
  MaxLocusLocal.maxLocus_comp_strictMono (strictMono_nestedStep o hδ) g S

/-- When the actual lower reads satisfy the nested formula, the branch
comparison uses its finite and top values. The formula is an input to this
order-theoretic result. -/
def lowerBranchComparison_of_nestedLower {A B : Type*} {q : ℕ}
    (o : ℕ → ℕ) {δ : ValTy q → ValTy q} (hδ : StrictMono δ)
    (f : A → ℕ ×ₗ WithTop (ValTy (q + 1))) (g : B → ℕ ×ₗ WithTop (ValTy q))
    (i : B → A) (S : Set B)
    (hRaw : ∀ x ∈ S, (ofLex (f (i x))).2 =
      nestedLower (o (ofLex (g x)).1) δ (ofLex (g x)).2) :
    LowerBranchComparison f g i S where
  finiteMap s v := nestedLower (o s) δ (v : WithTop (ValTy q))
  topValue s := nestedLower (o s) δ ⊤
  strictMono_finiteMap s := fun _ _ h => strictMono_nestedLower (o s) hδ (WithTop.coe_lt_coe.mpr h)
  finite_eq x hx _ hv := (hRaw x hx).trans (congrArg (nestedLower (o (ofLex (g x)).1) δ) hv)
  top_eq x hx hv := (hRaw x hx).trans (congrArg (nestedLower (o (ofLex (g x)).1) δ) hv)
  finite_lt_top x _ y _ hxy v _ _ := by
    rw [hxy]
    exact strictMono_nestedLower (o (ofLex (g y)).1) hδ (WithTop.coe_lt_top v)

/-- Literal image and preimage of the maximum locus for reads on paired
cosupports. The top branch of the native read can have a finite padded read. -/
theorem max_loci_of_nestedLower {A B : Type*} {q : ℕ}
    (o : ℕ → ℕ) {δ : ValTy q → ValTy q} (hδ : StrictMono δ)
    (f : A → ℕ ×ₗ WithTop (ValTy (q + 1))) (g : B → ℕ ×ₗ WithTop (ValTy q))
    (i : B → A) (hi : Function.Injective i) (S : Set B) (T : Set A) (hImage : i '' S = T)
    (hLevel : ∀ x ∈ S, (ofLex (f (i x))).1 = (ofLex (g x)).1)
    (hRaw : ∀ x ∈ S, (ofLex (f (i x))).2 =
      nestedLower (o (ofLex (g x)).1) δ (ofLex (g x)).2) :
    i '' maxLocus g S = maxLocus f T ∧ i ⁻¹' maxLocus f T = maxLocus g S :=
  (lowerBranchComparison_of_nestedLower o hδ f g i S hRaw).max_loci hLevel hi hImage

set_option backward.isDefEq.respectTransparency false in
/-- The nested raw lower formula on the actual padded and literal native
Step One records implies the centre image and preimage on their actual
current cosupports. The upper levels and cosupport matching come from the
lift and the padded test hypothesis. -/
theorem positive_normal_max_loci_of_nestedLower {n q : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (q + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T)
    {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
    {N : BlowupTower (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
      (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Nat.le_succ n) V hV)}
    {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc
      (zeroPlane_regular U) (sectionMarked Q).E T V hVc hV N)
    (o : ℕ → ℕ) {δ : ValTy q → ValTy q} (hδ : StrictMono δ) :
    let P := properNormalMarked Q
    let B := nativePullback (Y := CMfd.of (n := n + 1) (productOpen U)) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionMarked Q)
    let i : nativeManifold (Nat.le_succ n) V hV → Y := Subtype.val
    let S := (geoTransformAlong P T).cosupp
    let Sₙ := (geoTransformAlong B N).cosupp
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q + 1)) P T
    let g := Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) B N
    (∀ x ∈ Sₙ, (ofLex (f (i x))).2 = nestedLower (o (ofLex (g x)).1) δ (ofLex (g x)).2) →
      i '' maxLocus g Sₙ = maxLocus f S ∧ i ⁻¹' maxLocus f S = maxLocus g Sₙ := by
  intro P B i S Sₙ f g hRaw
  exact positive_normal_max_loci_of_lower_branch_comparison hn Q hQ T hT hLift
    (lowerBranchComparison_of_nestedLower o hδ f g i Sₙ hRaw)

end

end Hironaka.HironakaG1NormalNestedOrderMap
