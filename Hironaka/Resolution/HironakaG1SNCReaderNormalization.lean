import Hironaka.Resolution.HironakaG1RelativeBoundaryUnitLifts
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Actual independent SNC reader normalization

Full original native old-slot ideal maps derive the common active labels.
Actual coordinate complements and genuine reader biholomorphisms produce
the independent coordinate opens; no normalized-reader packet is input.
BP FIRST: `hironaka-g1-snc-reader-normalization.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1SNCReaderNormalization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings BlowupFlatCoordinates HolGerm
  HironakaActualAnalyticSubspace HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaG1QuotientLabelledBoundaryFrame HironakaG1RelativeBoundaryUnitLifts

noncomputable section

/-- The ACTUAL missing coordinate subtype of an active-coordinate injection. -/
def complementSize {r n : ℕ} (α : Fin r → Fin n) : ℕ := Fintype.card {j : Fin n // j ∉ Set.range α}

/-- Extend the active coordinate injection by its genuine complementary coordinates. -/
def completeIndexEquiv {r n : ℕ} (α : Fin r → Fin n) (hα : Function.Injective α) :
    Fin (r+complementSize α) ≃ Fin n := by
  classical
  exact finSumFinEquiv.symm.trans
    (((Equiv.ofInjective α hα).sumCongr (Fintype.equivFin {j : Fin n // j ∉ Set.range α}).symm).trans
      (Equiv.Set.sumCompl (Set.range α)))

theorem completeIndexEquiv_active {r n : ℕ} (α : Fin r → Fin n) (hα : Function.Injective α) (i : Fin r) :
    completeIndexEquiv α hα (i.castAdd (complementSize α)) = α i := by
  classical
  change (Equiv.Set.sumCompl (Set.range α))
    (((Equiv.ofInjective α hα).sumCongr (Fintype.equivFin {j : Fin n // j ∉ Set.range α}).symm)
      (finSumFinEquiv.symm (i.castAdd (Fintype.card {j : Fin n // j ∉ Set.range α})))) = α i
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem completeIndexEquiv_dimension {r n : ℕ} (α : Fin r → Fin n) (hα : Function.Injective α) :
    n = r+complementSize α := by
  have h := Fintype.card_congr (completeIndexEquiv α hα)
  simpa only [Fintype.card_fin] using h.symm

/-- The genuine canonical model map retains the entire original coordinate order. -/
def coordinateReindex {n r a : ℕ} (σ : Fin (r+a) ≃ Fin n) : ComplexModel n ≃L[ℂ] ComplexModel (r+a) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm).toContinuousLinearEquiv

@[simp] theorem coordinateReindex_apply {n r a : ℕ} (σ : Fin (r+a) ≃ Fin n)
    (v : ComplexModel n) (j : Fin (r+a)) : coordinateReindex σ v j = v (σ j) := rfl

variable {n r a : ℕ} {M : CMfd.{0} n} {p : M}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
  (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) p).target)
  (σ : Fin (r+a) ≃ Fin n)

/-- The ACTUAL original reader domain, without extending the reader map. -/
def readerSource : Opens M := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩

/-- The ACTUAL target after the genuine index reordering. -/
def readerTarget : Opens (ComplexModel (r+a)) :=
  ⟨coordinateReindex σ '' Φ.target,(coordinateReindex σ).toHomeomorph.isOpenMap _ Φ.isOpen_target⟩

private def readerForward (x : readerSource Φ) : readerTarget Φ σ :=
  ⟨coordinateReindex σ (Φ.toFun (chartAt (ComplexModel n) p x.val)),
    ⟨Φ.toFun (chartAt (ComplexModel n) p x.val),Φ.mapsTo_toFun x.property.2,rfl⟩⟩

private theorem readerTarget_mem (y : readerTarget Φ σ) : (coordinateReindex σ).symm y.val ∈ Φ.target := by
  obtain ⟨v,hv,hvy⟩ := y.property
  have he := congrArg (coordinateReindex σ).symm hvy
  rw [ContinuousLinearEquiv.symm_apply_apply] at he
  exact he ▸ hv

private def readerInverse (y : readerTarget Φ σ) : readerSource Φ :=
  ⟨(chartAt (ComplexModel n) p).symm (Φ.invFun ((coordinateReindex σ).symm y.val)),
    (flatInverse_mem Φ (readerTarget_mem Φ σ y) hsrc).1⟩

private theorem readerForward_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+a)) ∞ (readerForward Φ σ) := by
  apply (ContMDiff.subtypeVal_comp_iff (readerTarget Φ σ) _).mp
  apply (coordinateReindex σ).contDiff.contMDiff.comp
  intro x
  have hΦ : ContDiffOn ℂ ∞ Φ.toFun Φ.source :=
    contDiffOn_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
  exact (hΦ.contDiffAt (Φ.isOpen_source.mem_nhds x.property.2)).contMDiffAt.comp x
    (((contMDiffOn_chart (n := ∞)).contMDiffAt
      ((chartAt (ComplexModel n) p).open_source.mem_nhds x.property.1)).comp x contMDiff_subtype_val.contMDiffAt)

private theorem readerInverse_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel n) ∞ (readerInverse Φ hsrc σ) := by
  apply (ContMDiff.subtypeVal_comp_iff (readerSource Φ) _).mp
  change ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel n) ∞
    (fun y : readerTarget Φ σ => (chartAt (ComplexModel n) p).symm (Φ.invFun ((coordinateReindex σ).symm y.val)))
  intro y
  have hy := readerTarget_mem Φ σ y
  have hΦ : ContDiffOn ℂ ∞ Φ.invFun Φ.target :=
    contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target
  have hin : Φ.invFun ((coordinateReindex σ).symm y.val) ∈ (chartAt (ComplexModel n) p).target :=
    hsrc (Φ.mapsTo_invFun hy)
  exact ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
      ((chartAt (ComplexModel n) p).open_target.mem_nhds hin)).comp y
    ((hΦ.contDiffAt (Φ.isOpen_target.mem_nhds hy)).contMDiffAt.comp y
      ((coordinateReindex σ).symm.contDiff.contMDiff.comp contMDiff_subtype_val).contMDiffAt)

/-- Both actual model structures and both ENTIRE inverse functions are retained. -/
def readerDiffeomorph : readerSource Φ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel (r+a))⟯ readerTarget Φ σ where
  toFun := readerForward Φ σ
  invFun := readerInverse Φ hsrc σ
  left_inv x := by
    apply Subtype.ext
    change (chartAt (ComplexModel n) p).symm (Φ.invFun
      ((coordinateReindex σ).symm (coordinateReindex σ (Φ.toFun (chartAt (ComplexModel n) p x.val))))) = x.val
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact flatInverse_flat Φ x.property
  right_inv y := by
    apply Subtype.ext
    have h := (flatInverse_mem Φ (readerTarget_mem Φ σ y) hsrc).2
    exact (congrArg (coordinateReindex σ) h).trans ((coordinateReindex σ).apply_symm_apply y.val)
  contMDiff_toFun := readerForward_holomorphic Φ σ
  contMDiff_invFun := readerInverse_holomorphic Φ hsrc σ

theorem readerDiffeomorph_active (x : readerSource Φ) (i : Fin r) :
    (readerDiffeomorph Φ hsrc σ x).val (i.castAdd a) = flatCoord Φ (σ (i.castAdd a)) x.val := rfl

theorem readerDiffeomorph_center (hzero : Φ.toFun (chartAt (ComplexModel n) p p) = 0) :
    (readerDiffeomorph Φ hsrc σ ⟨p,mem_flatDomain_self Φ⟩).val = 0 := by
  change coordinateReindex σ (Φ.toFun (chartAt (ComplexModel n) p p)) = 0
  rw [hzero,map_zero]

private theorem selector_none_of_inactive {n : ℕ} {M : CMfd.{0} n} {p : M}
    {E : List (Set M)} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    (κ : Fin E.length → Option (Fin n))
    (hz : Φ.toFun (chartAt (ComplexModel n) p p) = 0)
    (hm : ∀ x ∈ flatDomain Φ, ∀ i : Fin E.length,
      x ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j x = 0)
    (i : Fin E.length) (hi : p ∉ E.get i) : κ i = none := by
  cases hκ : κ i with
  | none => rfl
  | some j =>
    exfalso
    apply hi
    apply (hm p (mem_flatDomain_self Φ) i).mpr
    refine ⟨j,hκ,?_⟩
    change Φ.toFun (chartAt (ComplexModel n) p p) j = 0
    rw [hz]
    rfl

/-- OUTPUT of ordinary full old-slot comparison, retaining the original readers
and every original label. No such frame is a caller hypothesis. -/
structure RelativeReaders {n₁ n₂ : ℕ} {M₁ : CMfd.{0} n₁} {M₂ : CMfd.{0} n₂}
    (p₁ : M₁) (p₂ : M₂) (E₁ : List (Set M₁)) (E₂ : List (Set M₂))
    (τ : Fin E₁.length ≃ Fin E₂.length) where
  r : ℕ
  a : ℕ
  b : ℕ
  Φ₁ : LocalHolomorphicEquivAt (n := n₁) (chartAt (ComplexModel n₁) p₁ p₁)
  Φ₂ : LocalHolomorphicEquivAt (n := n₂) (chartAt (ComplexModel n₂) p₂ p₂)
  hsrc₁ : Φ₁.source ⊆ (chartAt (ComplexModel n₁) p₁).target
  hsrc₂ : Φ₂.source ⊆ (chartAt (ComplexModel n₂) p₂).target
  zero₁ : Φ₁.toFun (chartAt (ComplexModel n₁) p₁ p₁) = 0
  zero₂ : Φ₂.toFun (chartAt (ComplexModel n₂) p₂ p₂) = 0
  σ₁ : Fin (r+a) ≃ Fin n₁
  σ₂ : Fin (r+b) ≃ Fin n₂
  dimension₁ : n₁ = r+a
  dimension₂ : n₂ = r+b
  active_card : r = Nat.card {i : Fin E₁.length // p₁ ∈ E₁.get i}
  slot : Fin E₁.length → Option (Fin r)
  slot_surjective : ∀ j : Fin r, ∃ i : Fin E₁.length, slot i = some j
  slot_injective : Set.InjOn slot {i | p₁ ∈ E₁.get i}
  member₁ : ∀ x ∈ flatDomain Φ₁, ∀ i : Fin E₁.length,
    x ∈ E₁.get i ↔ ∃ j, slot i = some j ∧ flatCoord Φ₁ (σ₁ (j.castAdd a)) x = 0
  member₂ : ∀ y ∈ flatDomain Φ₂, ∀ i : Fin E₁.length,
    y ∈ E₂.get (τ i) ↔ ∃ j, slot i = some j ∧ flatCoord Φ₂ (σ₂ (j.castAdd b)) y = 0

private theorem member_of_selector {n r a : ℕ} {M : CMfd.{0} n} {p : M}
    {E : List (Set M)} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    (κ : Fin E.length → Option (Fin n)) (σ : Fin (r+a) ≃ Fin n)
    {ι : Type} (label : ι → Fin E.length) (slot : ι → Option (Fin r))
    (hm : ∀ x ∈ flatDomain Φ, ∀ i : Fin E.length,
      x ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j x = 0)
    (hκ : ∀ i, κ (label i) = (slot i).map (fun j => σ (j.castAdd a))) :
    ∀ x ∈ flatDomain Φ, ∀ i,
      x ∈ E.get (label i) ↔ ∃ j, slot i = some j ∧ flatCoord Φ (σ (j.castAdd a)) x = 0 := by
  intro x hx i
  rw [hm x hx (label i),hκ i]
  cases hs : slot i with
  | none => simp only [Option.map_none,reduceCtorEq,false_and,exists_false]
  | some j =>
    simp only [Option.map_some,Option.some.injEq]
    constructor
    · rintro ⟨_,rfl,hz⟩
      exact ⟨j,rfl,hz⟩
    · rintro ⟨_,rfl,hz⟩
      exact ⟨σ (j.castAdd a),rfl,hz⟩

/-- GENUINE actual native overlap and WHOLE original old-slot ideals derive
the common active enumeration and BOTH independent coordinate readers. -/
theorem exists_relative_readers {n₁ n₂ : ℕ} {M₁ : CMfd.{0} n₁} {M₂ : CMfd.{0} n₂}
    (C₁ : Set M₁) (C₂ : Set M₂)
    (e : actualSubspaceLocallyRingedSpace (n := n₁) C₁ ≅ actualSubspaceLocallyRingedSpace (n := n₂) C₂)
    (p₁ : C₁) {E₁ : List (Set M₁)} {E₂ : List (Set M₂)}
    (hE₁ : IsSNCDivisor n₁ E₁) (hE₂ : IsSNCDivisor n₂ E₂)
    (τ : Fin E₁.length ≃ Fin E₂.length)
    (hI : ∀ i : Fin E₁.length, Ideal.map (e.hom.stalkMap p₁).hom
      (actualLabelledBoundaryTraceIdeal C₂ E₂ (τ i) (e.hom.base p₁)) =
        actualLabelledBoundaryTraceIdeal C₁ E₁ i p₁) :
    Nonempty (RelativeReaders p₁.val (e.hom.base p₁).val E₁ E₂ τ) := by
  classical
  let p₂ := e.hom.base p₁
  let ε := (asIso (e.hom.stalkMap p₁)).commRingCatIsoToRingEquiv
  obtain ⟨Φ₁,κ₁,Φ₂,κ₂,hsrc₁,hsrc₂,hz₁,hz₂,hinj₁,hinj₂,hm₁,hm₂,hact,_hu⟩ :=
    exists_relative_labelled_unit_lifts C₁ C₂ p₁ p₂ hE₁ hE₂ τ ε hI
  let A := {i : Fin E₁.length // p₁.val ∈ E₁.get i}
  let r := Fintype.card A
  let en : Fin r ≃ A := (Fintype.equivFin A).symm
  choose α₁ hκ₁ _hz₁ using fun j : Fin r => (hm₁ p₁.val (mem_flatDomain_self Φ₁) (en j).val).mp (en j).property
  choose α₂ hκ₂ _hz₂ using fun j : Fin r =>
    (hm₂ p₂.val (mem_flatDomain_self Φ₂) (τ (en j).val)).mp ((hact (en j).val).mp (en j).property)
  have hα₁ : Function.Injective α₁ := by
    intro i j hij
    apply en.injective
    apply Subtype.ext
    apply hinj₁ (en i).property (en j).property
    rw [hκ₁ i,hκ₁ j,hij]
  have hα₂ : Function.Injective α₂ := by
    intro i j hij
    apply en.injective
    apply Subtype.ext
    apply τ.injective
    apply hinj₂ ((hact (en i).val).mp (en i).property) ((hact (en j).val).mp (en j).property)
    rw [hκ₂ i,hκ₂ j,hij]
  let a := complementSize α₁
  let b := complementSize α₂
  let σ₁ := completeIndexEquiv α₁ hα₁
  let σ₂ := completeIndexEquiv α₂ hα₂
  let slot : Fin E₁.length → Option (Fin r) := fun i =>
    if hi : p₁.val ∈ E₁.get i then some (en.symm ⟨i,hi⟩) else none
  have hs₁ (i : Fin E₁.length) : κ₁ i = (slot i).map (fun j => σ₁ (j.castAdd a)) := by
    by_cases hi : p₁.val ∈ E₁.get i
    · let j := en.symm ⟨i,hi⟩
      have hj : (en j).val = i := congrArg Subtype.val (en.apply_symm_apply ⟨i,hi⟩)
      change κ₁ i = Option.map _ (if h : p₁.val ∈ E₁.get i then some (en.symm ⟨i,h⟩) else none)
      rw [dif_pos hi,Option.map_some,completeIndexEquiv_active]
      exact (congrArg κ₁ hj.symm).trans (hκ₁ j)
    · rw [show slot i = none from dif_neg hi,Option.map_none]
      exact selector_none_of_inactive Φ₁ κ₁ hz₁ hm₁ i hi
  have hs₂ (i : Fin E₁.length) : κ₂ (τ i) = (slot i).map (fun j => σ₂ (j.castAdd b)) := by
    by_cases hi : p₁.val ∈ E₁.get i
    · let j := en.symm ⟨i,hi⟩
      have hj : (en j).val = i := congrArg Subtype.val (en.apply_symm_apply ⟨i,hi⟩)
      change κ₂ (τ i) = Option.map _ (if h : p₁.val ∈ E₁.get i then some (en.symm ⟨i,h⟩) else none)
      rw [dif_pos hi,Option.map_some,completeIndexEquiv_active]
      exact (congrArg (fun v => κ₂ (τ v)) hj.symm).trans (hκ₂ j)
    · rw [show slot i = none from dif_neg hi,Option.map_none]
      exact selector_none_of_inactive Φ₂ κ₂ hz₂ hm₂ (τ i) (fun h => hi ((hact i).mpr h))
  exact ⟨{
    r := r
    a := a
    b := b
    Φ₁ := Φ₁
    Φ₂ := Φ₂
    hsrc₁ := hsrc₁
    hsrc₂ := hsrc₂
    zero₁ := hz₁
    zero₂ := hz₂
    σ₁ := σ₁
    σ₂ := σ₂
    dimension₁ := completeIndexEquiv_dimension α₁ hα₁
    dimension₂ := completeIndexEquiv_dimension α₂ hα₂
    active_card := by rw [Nat.card_eq_fintype_card]
    slot := slot
    slot_surjective := by
      intro j
      refine ⟨(en j).val,?_⟩
      change (if h : p₁.val ∈ E₁.get (en j).val then some (en.symm ⟨(en j).val,h⟩) else none) = some j
      rw [dif_pos (en j).property]
      exact congrArg Option.some (en.symm_apply_apply j)
    slot_injective := by
      intro i hi j hj hij
      have hsi : slot i = some (en.symm ⟨i,hi⟩) := dif_pos hi
      have hsj : slot j = some (en.symm ⟨j,hj⟩) := dif_pos hj
      have heq : en.symm ⟨i,hi⟩ = en.symm ⟨j,hj⟩ := Option.some.inj (hsi.symm.trans (hij.trans hsj))
      exact congrArg Subtype.val (en.symm.injective heq)
    member₁ := member_of_selector Φ₁ κ₁ σ₁ id slot hm₁ hs₁
    member₂ := member_of_selector Φ₂ κ₂ σ₂ τ slot hm₂ hs₂ }⟩

namespace RelativeReaders

variable {n₁ n₂ : ℕ} {M₁ : CMfd.{0} n₁} {M₂ : CMfd.{0} n₂}
  {p₁ : M₁} {p₂ : M₂} {E₁ : List (Set M₁)} {E₂ : List (Set M₂)}
  {τ : Fin E₁.length ≃ Fin E₂.length} (R : RelativeReaders p₁ p₂ E₁ E₂ τ)

/-- The genuine first canonical coordinate open produced by the original SNC reader. -/
def sourceCoordinateOpen : Opens (ComplexModel (R.r+R.a)) := readerTarget R.Φ₁ R.σ₁

/-- The genuine independent second coordinate open; its complement size may differ. -/
def targetCoordinateOpen : Opens (ComplexModel (R.r+R.b)) := readerTarget R.Φ₂ R.σ₂

def sourceDiffeomorph : readerSource R.Φ₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n₁),𝓘(ℂ,ComplexModel (R.r+R.a))⟯ R.sourceCoordinateOpen :=
  readerDiffeomorph R.Φ₁ R.hsrc₁ R.σ₁

def targetDiffeomorph : readerSource R.Φ₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n₂),𝓘(ℂ,ComplexModel (R.r+R.b))⟯ R.targetCoordinateOpen :=
  readerDiffeomorph R.Φ₂ R.hsrc₂ R.σ₂

theorem source_zero_mem : (0 : ComplexModel (R.r+R.a)) ∈ R.sourceCoordinateOpen := by
  have hp := (R.sourceDiffeomorph ⟨p₁,mem_flatDomain_self R.Φ₁⟩).property
  change (readerDiffeomorph R.Φ₁ R.hsrc₁ R.σ₁ ⟨p₁,mem_flatDomain_self R.Φ₁⟩).val ∈ R.sourceCoordinateOpen at hp
  rw [readerDiffeomorph_center R.Φ₁ R.hsrc₁ R.σ₁ R.zero₁] at hp
  exact hp

theorem target_zero_mem : (0 : ComplexModel (R.r+R.b)) ∈ R.targetCoordinateOpen := by
  have hp := (R.targetDiffeomorph ⟨p₂,mem_flatDomain_self R.Φ₂⟩).property
  change (readerDiffeomorph R.Φ₂ R.hsrc₂ R.σ₂ ⟨p₂,mem_flatDomain_self R.Φ₂⟩).val ∈ R.targetCoordinateOpen at hp
  rw [readerDiffeomorph_center R.Φ₂ R.hsrc₂ R.σ₂ R.zero₂] at hp
  exact hp

/-- Every original slot reads the actual first normalized coordinates on ALL ambient points. -/
theorem source_slot_member (x : readerSource R.Φ₁) (i : Fin E₁.length) :
    x.val ∈ E₁.get i ↔ ∃ j, R.slot i = some j ∧ (R.sourceDiffeomorph x).val (j.castAdd R.a) = 0 := by
  change x.val ∈ E₁.get i ↔ ∃ j, R.slot i = some j ∧ flatCoord R.Φ₁ (R.σ₁ (j.castAdd R.a)) x.val = 0
  exact R.member₁ x.val x.property i

/-- The GIVEN full label bijection reads the SAME selector on the independent target. -/
theorem target_slot_member (y : readerSource R.Φ₂) (i : Fin E₁.length) :
    y.val ∈ E₂.get (τ i) ↔ ∃ j, R.slot i = some j ∧ (R.targetDiffeomorph y).val (j.castAdd R.b) = 0 := by
  change y.val ∈ E₂.get (τ i) ↔ ∃ j, R.slot i = some j ∧ flatCoord R.Φ₂ (R.σ₂ (j.castAdd R.b)) y.val = 0
  exact R.member₂ y.val y.property i

theorem slot_none_iff (i : Fin E₁.length) : R.slot i = none ↔ p₁ ∉ E₁.get i := by
  constructor
  · intro hs hp
    obtain ⟨j,hj,_⟩ := (R.member₁ p₁ (mem_flatDomain_self R.Φ₁) i).mp hp
    have hbad : (none : Option (Fin R.r)) = some j := hs.symm.trans hj
    cases hbad
  · intro hp
    cases hs : R.slot i with
    | none => rfl
    | some j =>
      exfalso
      apply hp
      apply (R.member₁ p₁ (mem_flatDomain_self R.Φ₁) i).mpr
      refine ⟨j,hs,?_⟩
      change R.Φ₁.toFun (chartAt (ComplexModel n₁) p₁ p₁) (R.σ₁ (j.castAdd R.a)) = 0
      rw [R.zero₁]
      rfl

theorem active_le_source : R.r ≤ n₁ := by
  calc
    R.r ≤ R.r+R.a := Nat.le_add_right _ _
    _ = n₁ := R.dimension₁.symm

theorem active_le_target : R.r ≤ n₂ := by
  calc
    R.r ≤ R.r+R.b := Nat.le_add_right _ _
    _ = n₂ := R.dimension₂.symm

end RelativeReaders

end
end Hironaka.HironakaG1SNCReaderNormalization
