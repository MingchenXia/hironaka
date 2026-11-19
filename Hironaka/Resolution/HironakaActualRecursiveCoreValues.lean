import Hironaka.Resolution.HironakaActualPositiveCoreOrderPresentation
import Hironaka.Resolution.HironakaOriginalAnyTestCurveFullValue

/-! Recursive core values of the REAL native formula on arbitrary towers.
Every terminal monomial tie is forgotten; all orders, counts, branch and
infinity markers remain. Retaining the original native tie gives EXACT
native prescribed centres. The ANYTEST curve formula supplies a genuine
semantic base and whole fixed-companion core-cut comparison. -/
set_option autoImplicit false
open Set Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualRecursiveCoreValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CompanionRebase
  NonmonomialOrderLocal NonmonomialOrderTail CanonicalCentres HomogenizedIdealAlong
  HironakaActualPositiveCoreOrderPresentation HironakaOriginalAnyTestCurveFullValue
  HironakaStageCenters
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus)

private def coreStepMap {α : Type} (f : α → α) (v : ℕ ×ₗ WithTop α) : ℕ ×ₗ WithTop α :=
  toLex ((ofLex v).1,WithTop.map f (ofLex v).2)

private def coreGeneralMap {α : Type} (f : α → α)
    (v : ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop α)) :
    ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop α) :=
  toLex ((ofLex v).1,toLex (Sum.map (fun _ : WithBot MonomialInvariant.Val=>(⊥ : WithBot MonomialInvariant.Val))
    (WithTop.map f) (ofLex (ofLex v).2)))

/-- Forget every terminal Gamma tie recursively on the UNCHANGED native
value type. This is not an assertion about the actual native Gamma. -/
def eraseGamma : (k : ℕ) → ValTy k → ValTy k
  | 0 => id
  | k+1 => coreGeneralMap (coreStepMap (eraseGamma k))

/-- The projected core of the ACTUAL native formula, without a CAN gate. -/
def coreInv {n : ℕ} (hn : 0<n) (k : ℕ) {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) : ValTy k :=
  eraseGamma k ((invFamily hn k).inv M T y)

private theorem coreStepMap_monotone {α : Type} [LinearOrder α] {f : α → α}
    (hf : Monotone f) : Monotone (coreStepMap f) := by
  intro a b hab
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases Prod.Lex.toLex_le_toLex.mp hab with h | ⟨h,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,hf.withTop_map h'⟩

private theorem coreGeneralMap_monotone {α : Type} [LinearOrder α] {f : α → α}
    (hf : Monotone f) : Monotone (coreGeneralMap f) := by
  have hs : ∀a b : WithBot MonomialInvariant.Val ⊕ WithTop α,toLex a≤toLex b →
      toLex (Sum.map (fun _ : WithBot MonomialInvariant.Val=>(⊥ : WithBot MonomialInvariant.Val)) (WithTop.map f) a)≤
        toLex (Sum.map (fun _ : WithBot MonomialInvariant.Val=>(⊥ : WithBot MonomialInvariant.Val)) (WithTop.map f) b) := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact le_rfl
      | inr b => exact Sum.Lex.inl_le_inr _ _
    | inr a =>
      cases b with
      | inl b => exact False.elim (Sum.Lex.not_inr_le_inl hab)
      | inr b => exact Sum.Lex.inr_le_inr_iff.mpr (hf.withTop_map (Sum.Lex.inr_le_inr_iff.mp hab))
  intro a b hab
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases Prod.Lex.toLex_le_toLex.mp hab with h | ⟨h,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,hs _ _ h'⟩

/-- Genuine recursive monotonicity, used to retain original native
centre choice by pairing the projected core with the original value. -/
theorem eraseGamma_monotone : ∀k : ℕ,Monotone (eraseGamma k)
  | 0 => monotone_id
  | k+1 => coreGeneralMap_monotone (coreStepMap_monotone (eraseGamma_monotone k))

/-- Retain the ACTUAL native value as tie after the projected core. -/
def coreNativeKey (k : ℕ) (v : ValTy k) : ValTy k ×ₗ ValTy k :=
  toLex (eraseGamma k v,v)

theorem coreNativeKey_strictMono (k : ℕ) : StrictMono (coreNativeKey k) := by
  intro a b hab
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases lt_or_eq_of_le ((eraseGamma_monotone k) hab.le) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h,hab⟩

/-- EXACT equality of prescribed native centres on ANY actual target
subset, in particular the given protected-open cosupport trace. -/
theorem actual_core_key_maximum_eq_native
    {n : ℕ} (hn : 0<n) (k : ℕ) {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (S : Set Y) :
    maxLocus (fun y=>coreNativeKey k ((invFamily hn k).inv M T y)) S=
      maxLocus ((invFamily hn k).inv M T) S :=
  MaxLocusLocal.maxLocus_comp_strictMono (coreNativeKey_strictMono k) _ S

/-- The semantic projected curve branch at an ACTUAL nonmonomial order. -/
def curveCoreValue (k q : ℕ) : ValTy (k+1) :=
  toLex (q,if q=0 then toLex (Sum.inl ⊥) else toLex (Sum.inr
    ((toLex (0,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) :
      WithTop (ℕ ×ₗ WithTop (ValTy k)))))

theorem curveCoreValue_strictMono (k : ℕ) : StrictMono (curveCoreValue k) := by
  intro a b hab
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)

/-- Genuine ANYTEST curve geometry computes the actual recursive core
at EVERY depth; no native or lower CAN/reference certificate is assumed. -/
theorem actual_curve_core_value {n : ℕ} (hn : 0<n) (k : ℕ) {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) :
    coreInv hn (k+1) M T y=curveCoreValue k (nmOrd (geoTransformAlong M T) y) := by
  rw [coreInv,original_curve_any_test_full_value_formula hn k M hM T hT y hy]
  by_cases hz : nmOrd (geoTransformAlong M T) y=0
  · simp only [hz,if_pos,eraseGamma,coreGeneralMap,ofLex_toLex,Sum.map_inl,curveCoreValue]
    rfl
  · simp only [if_neg hz,eraseGamma,coreGeneralMap,coreStepMap,ofLex_toLex,
      Sum.map_inr,WithTop.map_coe,WithTop.map_top,curveCoreValue]
    rfl

/-- The internally constructed fixed companion presents the ENTIRE
ACTUAL curve core cut, with its genuine domain/maximal order/tests. -/
theorem actual_curve_core_masked_whole_presentation
    {n : ℕ} (hn : 0<n) (k : ℕ) {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (q : ℕ) (hq : 1≤q)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hCuts : StageCentres (fun S C=>C⊆ordGe (geoTransformAlong M S) q) T) :
    let W:=ordMask M q
    let A:=MarkedIdeal.pullback (Subtype.val : W→X) M
    let O:=companionOf n (M:=CMfd.of (n:=n) W) A q
    IsInvDomain 1 O ∧ IsMaximalOrderAlong O.N O.ideal O.d ∧
      IsGeoTestTower O (restrict W T) ∧
      (geoTransformAlong O (restrict W T)).cosupp=
        (Subtype.val : openPreimage T W→Y) ⁻¹'
          {y | y∈(geoTransformAlong M T).cosupp ∧ curveCoreValue k q≤coreInv hn (k+1) M T y} := by
  dsimp only
  obtain ⟨hO,hMax,hTO,hCos,_hE,_hUpper⟩:=
    actual_positive_order_masked_whole_presentation hn M hM q hq T hT hCuts
  refine ⟨hO,hMax,hTO,?_⟩
  rw [hCos]
  apply congrArg (fun S : Set Y=>(Subtype.val : openPreimage T (ordMask M q)→Y) ⁻¹' S)
  ext y
  have hCurrent:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  constructor
  · rintro ⟨hyq,hy⟩
    refine ⟨hy,?_⟩
    rw [actual_curve_core_value hn k M hM T hT y hy]
    exact (curveCoreValue_strictMono k).monotone
      ((mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
        ((geoTransformAlong M T).cosupp_subset_N hy) q).mp hyq)
  · rintro ⟨hy,hCore⟩
    refine ⟨?_,hy⟩
    rw [actual_curve_core_value hn k M hM T hT y hy] at hCore
    exact (mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
      ((geoTransformAlong M T).cosupp_subset_N hy) q).mpr
        ((curveCoreValue_strictMono k).le_iff_le.mp hCore)

end
end Hironaka.HironakaActualRecursiveCoreValues
