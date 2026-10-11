/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance

/-! # Genuine whole fixed-q quotient frames from internally selected actual pivots

The rank image of the ORIGINAL finite holomorphic Macaulay matrix is bounded
and internally attains its maximum. A real nonzero minor and that global bound
produce a genuine nonempty open constant-rank patch. Its original inverse-pivot
projection has holomorphic coefficients and the ENTIRE ideal scalar image as
kernel. Actual whole maximal-ideal-power jets give the ENTIRE original quotient
coordinates in a fixed finite model. Original coherence internally supplies all
Cartan and chart dictionaries and preferred-chart quotient transports.

The patch can miss the initial base point. No density, maximal-Hilbert--Samuel
centre or full relative normal-flatness is claimed. Those still require actual
smooth-centre relative filtrations, all grades and true HS blowup descent.
-/

set_option autoImplicit false
open Set Filter Module
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaHolomorphicJetQuotientFrames
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
open Hironaka

noncomputable section
variable {n : ℕ}

/-- The actual entire scalar-coordinate jet at fixed truncation order. -/
def scalarJet (q : ℕ) : HolGerm (ComplexModel n) →ₗ[ℂ] (monomialIndex n q → ℂ) :=
  (finiteCoordinateArray q).comp (finiteJet q)

/-- The fixed genuine whole-jet range; repeated word coordinates are not assumed independent. -/
def scalarJetRange (n q : ℕ) : Submodule ℂ (monomialIndex n q → ℂ) :=
  LinearMap.range (scalarJet (n := n) q)

/-- Faithful actual coordinate evaluation preserves the ENTIRE maximal-ideal-power kernel. -/
theorem ker_scalarJet (q : ℕ) :
    LinearMap.ker (scalarJet (n := n) q) =
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q).restrictScalars ℂ := by
  rw [← ker_finiteJet q]
  ext g
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change finiteCoordinateArray q (finiteJet q g) = 0 ↔ finiteJet q g = 0
  constructor
  · intro h
    apply finiteCoordinateArray_injective q
    rwa [map_zero]
  · intro h
    rw [h, map_zero]

/-- Finite linear combination of genuine selected original Macaulay columns. -/
def columnMap (q : ℕ) {ι : Type*} (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    {k : ℕ} (cols : Fin k → monomialIndex n q × ι) :
    (Fin k → ℂ) →ₗ[ℂ] (monomialIndex n q → ℂ) :=
  Fintype.linearCombination ℂ (fun j a => originalMacaulayMatrix q G p a (cols j))

/-- Genuine selection of original word rows, independent of the actual point. -/
def rowMap (q : ℕ) {k : ℕ} (rows : Fin k → monomialIndex n q) :
    (monomialIndex n q → ℂ) →ₗ[ℂ] (Fin k → ℂ) where
  toFun v i := v (rows i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual square submatrix of the unmodified original Macaulay matrix. -/
def pivotMatrix (q : ℕ) {ι : Type*} (G : ι → ComplexModel n → ℂ)
    {k : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (p : ComplexModel n) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => originalMacaulayMatrix q G p (rows i) (cols j)

/-- True row evaluation of genuine selected columns is exactly the actual original pivot matrix. -/
theorem rowMap_columnMap (q : ℕ) {ι : Type*} (G : ι → ComplexModel n → ℂ)
    {k : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (p : ComplexModel n) (v : Fin k → ℂ) :
    rowMap q rows (columnMap q G p cols v) = (pivotMatrix q G rows cols p).mulVec v := by
  funext i
  change (∑ j : Fin k, v j • (fun a => originalMacaulayMatrix q G p a (cols j))) (rows i) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    pivotMatrix, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- ALL actual original Macaulay columns belong to the genuine fixed whole-jet range. -/
theorem original_columns_mem_scalarJetRange (q : ℕ) {ι : Type*}
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) (b : monomialIndex n q × ι) :
    (fun a => originalMacaulayMatrix q G p a b) ∈ scalarJetRange n q := by
  refine ⟨wordMonomial b.1 * translatedGerm p (G b.2) (hG b.2), ?_⟩
  funext a
  exact finiteCoordinateArray_original_macaulay_column b.1 a p (hG b.2)

/-- The unmodified original matrix image is the entire true original ideal scalar-jet image. -/
theorem range_originalMacaulay_eq_whole_scalar_image (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    LinearMap.range (originalMacaulayLinearMap q G p) =
      ((translatedIdeal G p hG).restrictScalars ℂ).map (scalarJet q) := by
  rw [originalMacaulayLinearMap_eq q G p hG, LinearMap.range_comp, range_macaulayMap]
  ext v
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨finiteJet q g, ⟨g, hg, rfl⟩, rfl⟩

/-- The real bounded rank image internally supplies its attained maximum and nonempty open constant-rank pivot patch. -/
theorem exists_maximal_rank_open_pivot_patch (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hUn : U.Nonempty) (hG : ∀ i, DifferentiableOn ℂ (G i) U) :
    ∃ (k : ℕ) (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
      (P : Set (ComplexModel n)), IsOpen P ∧ P ⊆ U ∧ P.Nonempty ∧
      (∀ p ∈ U, Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p)) ≤ k) ∧
      ∀ p ∈ P, (pivotMatrix q G rows cols p).det ≠ 0 ∧
        Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p)) = k := by
  classical
  let R : ComplexModel n → ℕ := fun p => Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p))
  have hbound (p : ComplexModel n) : R p ≤ Fintype.card (monomialIndex n q) := by
    simpa only [R, finrank_pi] using (LinearMap.range (originalMacaulayLinearMap q G p)).finrank_le
  have hfin : (R '' U).Finite := (Set.finite_Iic _).subset fun v ⟨p, _, hp⟩ => hp ▸ hbound p
  obtain ⟨a, haU⟩ := hUn
  obtain ⟨k, ⟨p, hpU, hpk⟩, hmax⟩ := Set.exists_max_image (R '' U) id hfin
    ⟨R a, Set.mem_image_of_mem _ haU⟩
  have hmaxR : ∀ y ∈ U, R y ≤ k := fun y hy => hmax _ (Set.mem_image_of_mem _ hy)
  have hnot : ¬ R p < k := by rw [hpk]; exact lt_irrefl _
  have hminor : ¬ ∀ (rows : Fin k → monomialIndex n q)
      (cols : Fin k → monomialIndex n q × ι),
      (Matrix.of fun i j => originalMacaulayMatrix q G p (rows i) (cols j)).det = 0 := by
    exact mt (finite_column_rank_lt_iff_minors_eq_zero (originalMacaulayMatrix q G p) k).mpr hnot
  push Not at hminor
  obtain ⟨rows, cols, hpdet⟩ := hminor
  let f : ComplexModel n → ℂ := originalMacaulayMinor q G rows cols
  let P : Set (ComplexModel n) := U ∩ f ⁻¹' ({0} : Set ℂ)ᶜ
  have hPo : IsOpen P := (differentiableOn_originalMacaulayMinor q G hU hG rows cols).continuousOn.isOpen_inter_preimage
    hU isClosed_singleton.isOpen_compl
  refine ⟨k, rows, cols, P, hPo, inter_subset_left, ⟨p, hpU, hpdet⟩, hmaxR, ?_⟩
  intro y hy
  have hydet : (pivotMatrix q G rows cols y).det ≠ 0 := hy.2
  refine ⟨hydet, (hmaxR y hy.1).antisymm ?_⟩
  by_contra hlt
  have hr : R y < k := by omega
  have hz := (finite_column_rank_lt_iff_minors_eq_zero (originalMacaulayMatrix q G y) k).mp hr rows cols
  exact hydet hz

variable (q : ℕ) {ι : Type*} (G : ι → ComplexModel n → ℂ)
  {k : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
  (p : ComplexModel n)

/-- The genuine original inverse-pivot projection on the whole actual scalar array. -/
def pivotProjection : (monomialIndex n q → ℂ) →ₗ[ℂ] (monomialIndex n q → ℂ) :=
  LinearMap.id - (columnMap q G p cols).comp
    ((pivotMatrix q G rows cols p)⁻¹.mulVecLin.comp (rowMap q rows))

/-- The actual inverse identity kills all selected original rows. -/
theorem rowMap_pivotProjection_eq_zero (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (v : monomialIndex n q → ℂ) :
    rowMap q rows (pivotProjection q G rows cols p v) = 0 := by
  change rowMap q rows (v - columnMap q G p cols
    ((pivotMatrix q G rows cols p)⁻¹.mulVec (rowMap q rows v))) = 0
  rw [map_sub, rowMap_columnMap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec, sub_self]

/-- The genuine projection is identity on its actual fixed row kernel. -/
theorem pivotProjection_eq_self (v : monomialIndex n q → ℂ) (hv : rowMap q rows v = 0) :
    pivotProjection q G rows cols p v = v := by
  change v - columnMap q G p cols ((pivotMatrix q G rows cols p)⁻¹.mulVec (rowMap q rows v)) = v
  rw [hv, Matrix.mulVec_zero, map_zero, sub_zero]

/-- The actual inverse identity kills every genuine selected original column combination. -/
theorem pivotProjection_columnMap_eq_zero (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (v : Fin k → ℂ) : pivotProjection q G rows cols p (columnMap q G p cols v) = 0 := by
  change columnMap q G p cols v - columnMap q G p cols
    ((pivotMatrix q G rows cols p)⁻¹.mulVec (rowMap q rows (columnMap q G p cols v))) = 0
  rw [rowMap_columnMap, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec, sub_self]

/-- The complete original scalar-array kernel is exactly the actual selected column image. -/
theorem ker_pivotProjection_eq_selected_image (hdet : (pivotMatrix q G rows cols p).det ≠ 0) :
    LinearMap.ker (pivotProjection q G rows cols p) = LinearMap.range (columnMap q G p cols) := by
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv
    change v - columnMap q G p cols ((pivotMatrix q G rows cols p)⁻¹.mulVec (rowMap q rows v)) = 0 at hv
    exact ⟨_, (sub_eq_zero.mp hv).symm⟩
  · rintro ⟨w, rfl⟩
    exact LinearMap.mem_ker.mpr (pivotProjection_columnMap_eq_zero q G rows cols p hdet w)

/-- Genuine inverse row recovery makes the actual selected-column map injective. -/
theorem columnMap_injective_of_det_ne_zero (hdet : (pivotMatrix q G rows cols p).det ≠ 0) :
    Function.Injective (columnMap q G p cols) := by
  intro v w h
  have he : (pivotMatrix q G rows cols p).mulVec v = (pivotMatrix q G rows cols p).mulVec w := by
    rw [← rowMap_columnMap, ← rowMap_columnMap, h]
  have hi := congrArg ((pivotMatrix q G rows cols p)⁻¹.mulVec) he
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec] using hi

/-- Genuine selected columns lie in the image of the actual FULL original matrix. -/
theorem range_columnMap_le_entire_image [Fintype ι] :
    LinearMap.range (columnMap q G p cols) ≤ LinearMap.range (originalMacaulayLinearMap q G p) := by
  rw [columnMap, originalMacaulayLinearMap, Fintype.range_linearCombination, Fintype.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span ⟨cols j, rfl⟩

/-- The true selected original columns have exactly their actual pivot size as dimension. -/
theorem finrank_range_columnMap (hdet : (pivotMatrix q G rows cols p).det ≠ 0) :
    Module.finrank ℂ (LinearMap.range (columnMap q G p cols)) = k := by
  simpa only [finrank_pi, Fintype.card_fin] using LinearMap.finrank_range_of_inj
    (columnMap_injective_of_det_ne_zero q G rows cols p hdet)

variable [Fintype ι]

/-- Equal actual dimensions identify selected columns with the ENTIRE unmodified original image. -/
theorem range_columnMap_eq_entire_image (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p)) = k) :
    LinearMap.range (columnMap q G p cols) = LinearMap.range (originalMacaulayLinearMap q G p) := by
  apply Submodule.eq_of_le_of_finrank_eq (range_columnMap_le_entire_image q G cols p)
  rw [finrank_range_columnMap q G rows cols p hdet, hrank]

/-- The genuine projection kernel is ALL actual ideal columns, on actual constant-rank pivot data. -/
theorem ker_pivotProjection_eq_entire_image (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p)) = k) :
    LinearMap.ker (pivotProjection q G rows cols p) = LinearMap.range (originalMacaulayLinearMap q G p) := by
  rw [ker_pivotProjection_eq_selected_image q G rows cols p hdet,
    range_columnMap_eq_entire_image q G rows cols p hdet hrank]

/-- The ENTIRE genuine original ideal scalar image stays in the actual fixed whole-jet range. -/
theorem range_originalMacaulay_le_scalarJetRange
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    LinearMap.range (originalMacaulayLinearMap q G p) ≤ scalarJetRange n q := by
  rw [originalMacaulayLinearMap, Fintype.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  exact original_columns_mem_scalarJetRange q G p hG b

/-- The genuine fixed frame model inside the actual whole scalar-jet range. -/
def fixedQuotientModel : Submodule ℂ (monomialIndex n q → ℂ) :=
  scalarJetRange n q ⊓ LinearMap.ker (rowMap q rows)

/-- The actual pivot projection maps the entire whole-jet range to the same fixed model. -/
theorem pivotProjection_mem_fixed_model (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z)
    (v : monomialIndex n q → ℂ) (hv : v ∈ scalarJetRange n q) :
    pivotProjection q G rows cols p v ∈ fixedQuotientModel q rows := by
  constructor
  · change v - columnMap q G p cols ((pivotMatrix q G rows cols p)⁻¹.mulVec (rowMap q rows v)) ∈ scalarJetRange n q
    apply Submodule.sub_mem _ hv
    apply range_originalMacaulay_le_scalarJetRange q G p hG
    apply range_columnMap_le_entire_image q G cols p
    exact ⟨_, rfl⟩
  · exact LinearMap.mem_ker.mpr (rowMap_pivotProjection_eq_zero q G rows cols p hdet v)

/-- Whole ORIGINAL germ coordinates in the internally fixed true quotient model. -/
def wholeQuotientCoordinates (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    HolGerm (ComplexModel n) →ₗ[ℂ] fixedQuotientModel q rows :=
  ((pivotProjection q G rows cols p).comp (scalarJet q)).codRestrict _
    (fun g => pivotProjection_mem_fixed_model q G rows cols p hdet hG (scalarJet q g) ⟨g, rfl⟩)

/-- The entire whole-germ coordinates surject onto the genuine fixed frame model. -/
theorem wholeQuotientCoordinates_surjective (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    Function.Surjective (wholeQuotientCoordinates q G rows cols p hdet hG) := by
  intro v
  obtain ⟨g, hg⟩ := v.2.1
  refine ⟨g, Subtype.ext ?_⟩
  change pivotProjection q G rows cols p (scalarJet q g) = (v : monomialIndex n q → ℂ)
  rw [hg]
  exact pivotProjection_eq_self q G rows cols p v (LinearMap.mem_ker.mp v.2.2)

/-- The entire true germ coordinate kernel is exactly the original whole ideal plus the genuine point power. -/
theorem ker_wholeQuotientCoordinates (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p)) = k)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    LinearMap.ker (wholeQuotientCoordinates q G rows cols p hdet hG) =
      (translatedIdeal G p hG ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q).restrictScalars ℂ := by
  ext g
  constructor
  · intro hg
    rw [LinearMap.mem_ker] at hg
    have hzero : pivotProjection q G rows cols p (scalarJet q g) = 0 := congrArg Subtype.val hg
    have him : scalarJet q g ∈ LinearMap.range (originalMacaulayLinearMap q G p) := by
      rw [← ker_pivotProjection_eq_entire_image q G rows cols p hdet hrank]
      exact LinearMap.mem_ker.mpr hzero
    rw [range_originalMacaulay_eq_whole_scalar_image q G p hG] at him
    obtain ⟨a, ha, he⟩ := him
    have hrem : g - a ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
      have hz : scalarJet q (g - a) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr he.symm
      have hh := LinearMap.mem_ker.mpr hz
      rw [ker_scalarJet] at hh
      exact hh
    exact Submodule.mem_sup.mpr ⟨a, ha, g - a, hrem, by abel⟩
  · intro hg
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hg
    have haim : scalarJet q a ∈ LinearMap.range (originalMacaulayLinearMap q G p) := by
      rw [range_originalMacaulay_eq_whole_scalar_image q G p hG]
      exact ⟨a, ha, rfl⟩
    have hza : pivotProjection q G rows cols p (scalarJet q a) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_pivotProjection_eq_entire_image q G rows cols p hdet hrank]
      exact haim
    have hzb : scalarJet q b = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_scalarJet]
      exact hb
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change pivotProjection q G rows cols p (scalarJet q g) = 0
    rw [← he, map_add, map_add, hza, hzb, map_zero, add_zero]

/-- Genuine fixed coordinates for the literal ENTIRE original point quotient. -/
def wholeQuotientFrame (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p)) = k)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    (HolGerm (ComplexModel n) ⧸ (translatedIdeal G p hG ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) ≃ₗ[ℂ] fixedQuotientModel q rows := by
  have e := (wholeQuotientCoordinates q G rows cols p hdet hG).quotKerEquivOfSurjective
    (wholeQuotientCoordinates_surjective q G rows cols p hdet hG)
  rw [ker_wholeQuotientCoordinates q G rows cols p hdet hrank hG] at e
  exact e

/-- Genuine pivot columns internally surject the restricted row map onto its full actual coordinate space. -/
theorem rowMap_scalarJetRange_surjective (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    Function.Surjective ((rowMap q rows).comp (scalarJetRange n q).subtype) := by
  intro v
  let w := columnMap q G p cols ((pivotMatrix q G rows cols p)⁻¹.mulVec v)
  have hw : w ∈ scalarJetRange n q :=
    range_originalMacaulay_le_scalarJetRange q G p hG
      (range_columnMap_le_entire_image q G cols p ⟨_, rfl⟩)
  refine ⟨⟨w, hw⟩, ?_⟩
  change rowMap q rows w = v
  rw [rowMap_columnMap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-- The actual fixed whole quotient model has true whole-jet dimension minus actual pivot size. -/
theorem finrank_fixed_model (hdet : (pivotMatrix q G rows cols p).det ≠ 0)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    Module.finrank ℂ (fixedQuotientModel q rows) = Module.finrank ℂ (scalarJetRange n q) - k := by
  let S := scalarJetRange n q
  let F := (rowMap q rows).comp S.subtype
  have hmap : (LinearMap.ker F).map S.subtype = fixedQuotientModel q rows := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · intro hv
      exact ⟨⟨v, hv.1⟩, hv.2, rfl⟩
  have hdim := ((LinearMap.ker F).equivMapOfInjective S.subtype Subtype.val_injective).finrank_eq
  rw [hmap] at hdim
  have hrange : LinearMap.range F = ⊤ :=
    LinearMap.range_eq_top.mpr (rowMap_scalarJetRange_surjective q G rows cols p hdet hG)
  have hs := F.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_pi, Fintype.card_fin, hdim] at hs
  change Module.finrank ℂ (fixedQuotientModel q rows) = Module.finrank ℂ S - k
  omega

private theorem differentiableOn_matrix_det {a : Type*} [Fintype a] [DecidableEq a]
    {D : Set (ComplexModel n)} (M : ComplexModel n → Matrix a a ℂ)
    (hM : ∀ i j, DifferentiableOn ℂ (fun p => M p i j) D) :
    DifferentiableOn ℂ (fun p => (M p).det) D := by
  have he : (fun p => (M p).det) = fun p => ∑ σ : Equiv.Perm a,
      Equiv.Perm.sign σ • ∏ i : a, M p (σ i) i := by
    funext p
    exact Matrix.det_apply _
  rw [he]
  have hs : DifferentiableOn ℂ (∑ σ : Equiv.Perm a, fun p =>
      Equiv.Perm.sign σ • ∏ i : a, M p (σ i) i) D := by
    refine DifferentiableOn.sum (𝕜 := ℂ) (E := ComplexModel n) (F := ℂ)
      (u := Finset.univ) (A := fun σ p => Equiv.Perm.sign σ • ∏ i : a, M p (σ i) i) fun σ _ => ?_
    exact (PureDimension.differentiableOn_finset_prod Finset.univ
      (fun i p => M p (σ i) i) D (fun i _ => hM _ _)).const_smul _
  exact hs.congr fun p _ => (Finset.sum_apply p Finset.univ
    (fun σ : Equiv.Perm a => fun p => Equiv.Perm.sign σ • ∏ i : a, M p (σ i) i)).symm

private theorem differentiableOn_matrix_adjugate {a : Type*} [Fintype a] [DecidableEq a]
    {D : Set (ComplexModel n)} (M : ComplexModel n → Matrix a a ℂ)
    (hM : ∀ i j, DifferentiableOn ℂ (fun p => M p i j) D) (i j : a) :
    DifferentiableOn ℂ (fun p => (M p).adjugate i j) D := by
  have he : (fun p => (M p).adjugate i j) =
      fun p => ((M p).updateRow j (Pi.single i 1)).det :=
    funext fun p => Matrix.adjugate_apply _ _ _
  rw [he]
  apply differentiableOn_matrix_det
  intro b c
  by_cases hb : b = j
  · subst b
    simp [Matrix.updateRow, Matrix.of_apply, Function.update]
  · simpa [Matrix.updateRow, Matrix.of_apply, Function.update, hb, Ne.symm hb] using hM b c

private theorem differentiableOn_matrix_inverse {a : Type*} [Fintype a] [DecidableEq a]
    {D : Set (ComplexModel n)} (M : ComplexModel n → Matrix a a ℂ)
    (hM : ∀ i j, DifferentiableOn ℂ (fun p => M p i j) D)
    (hdet : ∀ p ∈ D, (M p).det ≠ 0) (i j : a) :
    DifferentiableOn ℂ (fun p => (M p)⁻¹ i j) D := by
  have he : (fun p => (M p)⁻¹ i j) = fun p => (M p).det⁻¹ * (M p).adjugate i j := by
    funext p
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  rw [he]
  exact ((differentiableOn_matrix_det M hM).inv hdet).mul
    (differentiableOn_matrix_adjugate M hM i j)

private theorem differentiableOn_finite_sum {a : Type*} [Fintype a]
    {D : Set (ComplexModel n)} (F : a → ComplexModel n → ℂ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) D) :
    DifferentiableOn ℂ (fun p => ∑ i : a, F i p) D := by
  have hs : DifferentiableOn ℂ (∑ i : a, F i) D :=
    DifferentiableOn.sum (𝕜 := ℂ) (E := ComplexModel n) (F := ℂ)
      (u := Finset.univ) (A := F) (fun i _ => hF i)
  exact hs.congr fun p _ => (Finset.sum_apply p Finset.univ F).symm

omit [Fintype ι] in
/-- The unmodified original inverse-pivot projection has actual holomorphic finite entries. -/
theorem pivotProjection_holomorphic_entries {U D : Set (ComplexModel n)}
    (hU : IsOpen U) (hG : ∀ i, DifferentiableOn ℂ (G i) U) (hDU : D ⊆ U)
    (hdet : ∀ p ∈ D, (pivotMatrix q G rows cols p).det ≠ 0)
    (v : monomialIndex n q → ℂ) (a : monomialIndex n q) :
    DifferentiableOn ℂ (fun p => pivotProjection q G rows cols p v a) D := by
  have hC (b : monomialIndex n q) (c : monomialIndex n q × ι) :
      DifferentiableOn ℂ (fun p => originalMacaulayMatrix q G p b c) D :=
    (differentiableOn_originalMacaulayMatrix_entry q G hU hG b c).mono hDU
  have hK (i j : Fin k) : DifferentiableOn ℂ (fun p => pivotMatrix q G rows cols p i j) D := hC _ _
  have hInv (i j : Fin k) := differentiableOn_matrix_inverse (pivotMatrix q G rows cols) hK hdet i j
  have he : (fun p => pivotProjection q G rows cols p v a) = fun p =>
      v a - ∑ i : Fin k, (∑ j : Fin k, (pivotMatrix q G rows cols p)⁻¹ i j * v (rows j)) *
        originalMacaulayMatrix q G p a (cols i) := by
    funext p
    change v a - (∑ i : Fin k, ((pivotMatrix q G rows cols p)⁻¹.mulVec (rowMap q rows v)) i •
      (fun b => originalMacaulayMatrix q G p b (cols i))) a = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, rowMap,
      LinearMap.coe_mk, AddHom.coe_mk]
  rw [he]
  apply (differentiableOn_const (v a)).sub
  apply differentiableOn_finite_sum
  intro i
  apply DifferentiableOn.mul _ (hC _ _)
  apply differentiableOn_finite_sum
  intro j
  exact (hInv i j).mul_const _

/-- ORIGINAL holomorphic data alone internally produce holomorphic coordinates for the ENTIRE fixed-q quotient on a nonempty actual open. -/
theorem exists_original_whole_quotient_frames {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hUn : U.Nonempty) (hG : ∀ i, DifferentiableOn ℂ (G i) U) :
    ∃ (k : ℕ) (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
      (P : Set (ComplexModel n)), IsOpen P ∧ P ⊆ U ∧ P.Nonempty ∧
      (∀ (v : monomialIndex n q → ℂ) (a : monomialIndex n q),
        DifferentiableOn ℂ (fun p => pivotProjection q G rows cols p v a) P) ∧
      ∀ p ∈ P, ∃ hGp : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z,
        Nonempty ((HolGerm (ComplexModel n) ⧸ (translatedIdeal G p hGp ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) ≃ₗ[ℂ] fixedQuotientModel q rows) ∧
        Module.finrank ℂ (HolGerm (ComplexModel n) ⧸ (translatedIdeal G p hGp ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) =
          Module.finrank ℂ (scalarJetRange n q) - k := by
  obtain ⟨k, rows, cols, P, hP, hPU, hPn, _, hpk⟩ := exists_maximal_rank_open_pivot_patch q G hU hUn hG
  refine ⟨k, rows, cols, P, hP, hPU, hPn, ?_, ?_⟩
  · intro v a
    exact pivotProjection_holomorphic_entries q G rows cols hU hG hPU (fun p hp => (hpk p hp).1) v a
  · intro p hp
    have hGp (i : ι) : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z :=
      (show ∀ᶠ z in 𝓝 p, z ∈ U from hU.mem_nhds (hPU hp)).mono
        fun z hz => (hG i).differentiableAt (hU.mem_nhds hz)
    let e := wholeQuotientFrame q G rows cols p (hpk p hp).1 (hpk p hp).2 hGp
    refine ⟨hGp, ⟨e⟩, ?_⟩
    rw [e.finrank_eq]
    exact finrank_fixed_model q G rows cols p (hpk p hp).1 hGp

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
open HolomorphicIdealSheaves

/-- Original coherence alone internally supplies true holomorphic projection entries and ENTIRE preferred-chart quotient frames on a genuine nonempty open subpatch. -/
theorem exists_coherent_whole_quotient_frames (𝔞 : GermIdeal n M) (h𝔞 : 𝔞.IsCoherent)
    (x : M) (q : ℕ) :
    ∃ (s : ℕ) (G : Fin s → M → ℂ) (U : Set M), IsOpen U ∧ x ∈ U ∧
      U ⊆ (chartAt (ComplexModel n) x).source ∧
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) U) ∧
      ∃ (k : ℕ) (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × Fin s)
        (D : Set (ComplexModel n)) (P : Set M), IsOpen D ∧
        D ⊆ (chartAt (ComplexModel n) x).target ∩ (chartAt (ComplexModel n) x).symm ⁻¹' U ∧
        IsOpen P ∧ P ⊆ U ∧ P.Nonempty ∧
        (∀ y ∈ P, (chartAt (ComplexModel n) x) y ∈ D) ∧
        (∀ (v : monomialIndex n q → ℂ) (a : monomialIndex n q),
          DifferentiableOn ℂ (fun p => pivotProjection q
            (fun i z => G i ((chartAt (ComplexModel n) x).symm z)) rows cols p v a) D) ∧
        ∀ y ∈ P, Nonempty ((HolGerm (ComplexModel n) ⧸
          (wholeChartStalkIdeal 𝔞 y y (mem_chart_source _ y) ⊔
            IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) ≃ₗ[ℂ] fixedQuotientModel q rows) := by
  classical
  obtain ⟨U, hU, hxU, s, G, hsource, hG, hwhole⟩ := exists_coherent_whole_stalk_original_columns 𝔞 h𝔞 x
  let e := complexChartAt (n := n) x
  let H : Fin s → ComplexModel n → ℂ := fun i z => G i (e.val.symm z)
  let W : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U
  have hW : IsOpen W := e.val.isOpen_inter_preimage_symm hU
  have hxsource : x ∈ e.val.source := mem_complexChartAt_source x
  have hWn : W.Nonempty := ⟨e.val x, e.val.map_source hxsource, by
    change e.val.symm (e.val x) ∈ U
    rw [e.val.left_inv hxsource]
    exact hxU⟩
  have hH (i : Fin s) : DifferentiableOn ℂ (H i) W := fun z hz =>
    (StokesSingularLocusAnalytic.differentiableAt_chart e hz.1
      ((hG i).mdifferentiableAt (hU.mem_nhds hz.2))).differentiableWithinAt
  obtain ⟨k, rows, cols, D, hD, hDW, hDn, hhol, hframes⟩ := exists_original_whole_quotient_frames q H hW hWn hH
  let P : Set M := e.val.source ∩ e.val ⁻¹' D
  have hP : IsOpen P := e.val.continuousOn.isOpen_inter_preimage e.val.open_source hD
  have hPU : P ⊆ U := by
    intro y hy
    have hys := (hDW hy.2).2
    change e.val.symm (e.val y) ∈ U at hys
    rwa [e.val.left_inv hy.1] at hys
  have hPn : P.Nonempty := by
    obtain ⟨z, hz⟩ := hDn
    have hzt := (hDW hz).1
    exact ⟨e.val.symm z, e.val.map_target hzt, by
      change e.val (e.val.symm z) ∈ D
      rw [e.val.right_inv hzt]
      exact hz⟩
  refine ⟨s, G, U, hU, hxU, hsource, hG, k, rows, cols, D, P, hD, hDW, hP, hPU, hPn,
    fun y hy => hy.2, hhol, ?_⟩
  intro y hy
  have hyU := hPU hy
  obtain ⟨hHy, _, hIy⟩ := hwhole y hyU
  obtain ⟨hGp, ⟨ef⟩, _⟩ := hframes (e.val y) hy.2
  let hy₀ := mem_chart_source (ComplexModel n) y
  have et := (quotientAlgEquiv
    (translatedChartTransition x y y hy.1 hy₀)
    (translatedChartTransition_zero x y y hy.1 hy₀)
    (wholeChartStalkIdeal 𝔞 y y hy₀) q).toLinearEquiv
  have hmap := map_wholeChartStalkIdeal 𝔞 x y y hy.1 hy₀
  rw [hmap] at et
  rw [hIy] at et
  exact ⟨et.trans ef⟩

end Manifold

end
end Hironaka.HironakaHolomorphicJetQuotientFrames
