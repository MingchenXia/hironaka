/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.SectionsLocal
import DeJongAlterations.StableModification.Projectivity.LineBundleOps

/-!
# The divisor `∑ P̄ᵢ` through finitely many smooth points (Temkin, Prop. 4.4.6)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6 (T:3207–3210): for smooth closed points `p₁, …, p_r` of the closed fibre of a proper
nodal curve `q : Y → Spec V` over a henselian local ring with algebraically closed residue field,
"`∪ P̄ᵢ` is a Cartier divisor". Here (`exists_localEquations`) we construct line-bundle data with
local equations (OM3A's `Projectivity.LocalEquations`) whose canonical section `s` vanishes
exactly on a closed set `T = ⋃ Tᵢ` with

* `T ∩ Y_{s₀} = {p₁, …, p_r}` (`mem_nonvanishingLocus_iff_of_closedFibre`), and
* every point of `T` specializes to some `pᵢ`.

Each `Tᵢ` is the closed zero locus of the local equation of `SectionsLocal.exists_localEquation`;
the `Tᵢ` are pairwise disjoint because a point of `Tᵢ ∩ Tⱼ` would specialize, inside the closed
set `Tᵢ ∩ Tⱼ`, to a point of the closed fibre (`exists_specializes_closedPoint`, `q` proper over a
local base). The charts are `Y ∖ T` (equation `1`) and `Uᵢ ∖ ⋃_{j ≠ i} Tⱼ` (equation `tᵢ`),
glued by `LocalEquations.ofNonZeroDivisors` (`Y` integral). Blueprint
`sm-blow-down-contracting.tex`, `lem:sm-bdc-divisor`.
-/

namespace DeJongAlterations.StableModification.BlowDown.SectionsDivisor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace IsLocalRing
open DeJongAlterations.StableModification.Projectivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Proper

variable {V : Type u} [CommRing V] [IsLocalRing V] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (.of V))

/-- Over a local base, the closure of every point of a universally closed scheme meets the
closed fibre. -/
theorem exists_specializes_closedPoint [UniversallyClosed q] (y : Y) :
    ∃ z, y ⤳ z ∧ q z = closedPoint V := by
  have hcl : IsClosed (q '' closure {y}) := q.isClosedMap _ isClosed_closure
  have hmem : closedPoint V ∈ q '' closure {y} :=
    (IsLocalRing.specializes_closedPoint (q y)).mem_closed hcl ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨z, hz, hqz⟩ := hmem
  exact ⟨z, specializes_iff_mem_closure.mpr hz, hqz⟩

end Proper

section Divisor

variable {V : Type u} [CommRing V] [HenselianLocalRing V] [IsAlgClosed (ResidueField V)]
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of V)) [IsSeparated q] [LocallyOfFinitePresentation q]
  [UniversallyClosed q] [IsIntegral Y]

/-- A function on an open `W` whose basic open contains `W` is a unit. -/
lemma isUnit_res_of_le {U W : Y.Opens} (h : W ≤ U) (t : Γ(Y, U)) (hW : W ≤ Y.basicOpen t) :
    IsUnit (res h t) := by
  apply isUnit_of_basicOpen_eq
  change Y.basicOpen (Y.presheaf.map (homOfLE h).op t) = W
  rw [Scheme.basicOpen_res]
  exact inf_eq_left.mpr hW

/-- **The divisor through finitely many smooth points** (T:3207–3210): line-bundle data with local
equations whose canonical section vanishes on the closed fibre exactly at the given smooth closed
points, and such that every zero specializes to one of them. The point `y₀` of the closed fibre
outside `P` excludes the degenerate case of a closed fibre consisting of points of `P`. -/
theorem exists_localEquations (hpure : Curves.SemistableOpen.PureOneDimensionalFibres q)
    (P : Finset Y) (hsm : ∀ p ∈ P, p ∈ q.smoothLocus) (hcl : ∀ p ∈ P, IsClosed ({p} : Set Y))
    (hs : ∀ p ∈ P, q p = closedPoint V) (y₀ : Y) (hy₀ : q y₀ = closedPoint V) (hy₀P : y₀ ∉ P) :
    ∃ D : LocalEquations Y,
      (∀ y, q y = closedPoint V → (y ∈ D.canonicalSection.nonvanishingLocus ↔ y ∉ P)) ∧
      ∀ y, y ∉ D.canonicalSection.nonvanishingLocus → ∃ p ∈ P, y ⤳ p := by
  classical
  have hloc : ∀ p : P, ∃ (U : Y.Opens) (t : Γ(Y, U)), (p : Y) ∈ U ∧ (p : Y) ∉ Y.basicOpen t ∧
      IsClosed ((U : Set Y) \ Y.basicOpen t) ∧
      ∀ y ∈ (U : Set Y) \ Y.basicOpen t, q y = closedPoint V → y = p := fun p =>
    SectionsLocal.exists_localEquation q hpure (hsm p p.2) (hcl p p.2) (hs p p.2)
  choose U t hpU hpt hTcl hTs using hloc
  let T : P → Set Y := fun p => (U p : Set Y) \ Y.basicOpen (t p)
  have hpT : ∀ p : P, (p : Y) ∈ T p := fun p => ⟨hpU p, hpt p⟩
  -- every point of `T p` specializes to `p`
  have hspec : ∀ (p : P) (y : Y), y ∈ T p → y ⤳ p := by
    intro p y hy
    obtain ⟨z, hyz, hz⟩ := exists_specializes_closedPoint q y
    have hzT : z ∈ T p := hyz.mem_closed (hTcl p) hy
    rwa [hTs p z hzT hz] at hyz
  -- the `T p` are pairwise disjoint
  have hdisj : ∀ p p' : P, p ≠ p' → ∀ y, y ∈ T p → y ∉ T p' := by
    intro p p' hne y hy hy'
    obtain ⟨z, hyz, hz⟩ := exists_specializes_closedPoint q y
    have h1 := hTs p z (hyz.mem_closed (hTcl p) hy) hz
    have h2 := hTs p' z (hyz.mem_closed (hTcl p') hy') hz
    exact hne (Subtype.ext (h1.symm.trans h2))
  -- the generic point is not on any `T p`
  have hgen : ∀ p : P, genericPoint Y ∉ T p := by
    intro p hη
    have hy₀T : y₀ ∈ T p :=
      ((genericPoint_spec Y).specializes (Set.mem_univ y₀)).mem_closed (hTcl p) hη
    exact hy₀P (hTs p y₀ hy₀T hy₀ ▸ p.2)
  -- the charts
  let Tall : Set Y := ⋃ p : P, T p
  have hTall : IsClosed Tall := isClosed_iUnion_of_finite hTcl
  let Bad : P → Set Y := fun p => ⋃ p' : {p' : P // p' ≠ p}, T p'
  have hBad : ∀ p, IsClosed (Bad p) := fun p => isClosed_iUnion_of_finite fun p' => hTcl p'.1
  let ι : Type u := Option P
  let UU : ι → Y.Opens := fun i => match i with
    | none => ⟨Tallᶜ, hTall.isOpen_compl⟩
    | some p => ⟨(U p : Set Y) ∩ (Bad p)ᶜ, (U p).isOpen.inter (hBad p).isOpen_compl⟩
  let ff : ∀ i, Γ(Y, UU i) := fun i => match i with
    | none => 1
    | some p => res (show UU (some p) ≤ U p from fun y hy => hy.1) (t p)
  have hmemUU : ∀ (p : P) (y : Y), y ∈ UU (some p) ↔ y ∈ U p ∧ ∀ p' : P, p' ≠ p → y ∉ T p' := by
    intro p y
    change y ∈ (U p : Set Y) ∩ (Bad p)ᶜ ↔ _
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Bad, Set.mem_iUnion, not_exists]
    exact ⟨fun h => ⟨h.1, fun p' hp' => h.2 ⟨p', hp'⟩⟩, fun h => ⟨h.1, fun p' => h.2 p'.1 p'.2⟩⟩
  have hmem0 : ∀ y : Y, y ∈ UU none ↔ ∀ p : P, y ∉ T p := by
    intro y
    change y ∈ Tallᶜ ↔ _
    simp only [Tall, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  -- on `UU (some p)` minus `T p` the equation is a unit
  have hbasic : ∀ (p : P) (W : Y.Opens) (hW : W ≤ UU (some p)), (∀ y ∈ W, y ∉ T p) →
      IsUnit (res hW (ff (some p))) := by
    intro p W hW hWT
    have e : res hW (ff (some p)) = res (hW.trans fun y hy => hy.1) (t p) := by
      change res hW (res _ (t p)) = _
      exact res_res _ _ _ _
    rw [e]
    apply isUnit_res_of_le
    intro y hy
    by_contra hyt
    exact hWT y hy ⟨(hW hy).1, hyt⟩
  have hcover : ⨆ i, UU i = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    rw [Opens.mem_iSup]
    by_cases hy : ∃ p : P, y ∈ T p
    · obtain ⟨p, hyp⟩ := hy
      refine ⟨some p, (hmemUU p y).mpr ⟨hyp.1, fun p' hp' hy' => hdisj p p' hp'.symm y hyp hy'⟩⟩
    · push Not at hy
      exact ⟨none, (hmem0 y).mpr hy⟩
  -- transition units
  have hres_some : ∀ (p : P) {W : Y.Opens} (hW : W ≤ UU (some p)),
      res hW (ff (some p)) = res (hW.trans fun y hy => hy.1) (t p) := by
    intro p W hW
    change res hW (res _ (t p)) = _
    exact res_res _ _ _ _
  have hunit : ∀ i j, ∃ v : Γ(Y, UU i ⊓ UU j)ˣ,
      res (inf_le_left : UU i ⊓ UU j ≤ UU i) (ff i) =
        (v : Γ(Y, UU i ⊓ UU j)) * res (inf_le_right : UU i ⊓ UU j ≤ UU j) (ff j) := by
    rintro (_ | p) (_ | p')
    · exact ⟨1, by simp [ff]⟩
    · have hu := hbasic p' (UU none ⊓ UU (some p')) inf_le_right
        (fun y hy => (hmem0 y).mp hy.1 p')
      refine ⟨hu.unit⁻¹, ?_⟩
      change res _ (1 : Γ(Y, UU none)) = _
      rw [map_one, IsUnit.val_inv_mul]
    · have hu := hbasic p (UU (some p) ⊓ UU none) inf_le_left
        (fun y hy => (hmem0 y).mp hy.2 p)
      refine ⟨hu.unit, ?_⟩
      change _ = _ * res _ (1 : Γ(Y, UU none))
      rw [map_one, mul_one, IsUnit.unit_spec]
    · by_cases hpp : p = p'
      · subst hpp
        refine ⟨1, ?_⟩
        rw [Units.val_one, one_mul, hres_some]
      · have hu := hbasic p (UU (some p) ⊓ UU (some p')) inf_le_left
          (fun y hy => ((hmemUU p' y).mp hy.2).2 p hpp)
        have hu' := hbasic p' (UU (some p) ⊓ UU (some p')) inf_le_right
          (fun y hy => ((hmemUU p y).mp hy.1).2 p' (Ne.symm hpp))
        refine ⟨hu.unit * hu'.unit⁻¹, ?_⟩
        rw [Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]
  have hnzd : ∀ i j k, res (inf_le_right : UU i ⊓ UU j ⊓ UU k ≤ UU k) (ff k) ∈
      nonZeroDivisors Γ(Y, UU i ⊓ UU j ⊓ UU k) := by
    intro i j k
    set W := UU i ⊓ UU j ⊓ UU k with hWdef
    by_cases hW : (W : Set Y).Nonempty
    · have : Nonempty W := ⟨⟨hW.some, hW.some_mem⟩⟩
      apply mem_nonZeroDivisors_of_ne_zero
      intro h0
      have hη : genericPoint Y ∈ W := by
        obtain ⟨y, hy⟩ := hW
        exact ((genericPoint_spec Y).specializes (Set.mem_univ y)).mem_open W.isOpen hy
      rcases k with _ | p
      · exact one_ne_zero (h0 ▸ (map_one _).symm : (1 : Γ(Y, W)) = 0)
      · rw [hres_some] at h0
        have hb := congrArg Y.basicOpen h0
        rw [Scheme.basicOpen_res, Scheme.basicOpen_zero] at hb
        have hηT : genericPoint Y ∈ T p := by
          refine ⟨(inf_le_right : W ≤ UU (some p)) hη |>.1, fun hηb => ?_⟩
          have : genericPoint Y ∈ (W ⊓ Y.basicOpen (t p) : Y.Opens) := ⟨hη, hηb⟩
          rw [hb] at this
          exact this
        exact hgen p hηT
    · have hbot : W = ⊥ := by
        ext y
        simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hy => hW ⟨y, hy⟩
      have e : Γ(Y, W) ≃+* Γ(Y, ⊥) :=
        (Y.presheaf.mapIso (eqToIso hbot).op).commRingCatIsoToRingEquiv.symm
      have : Subsingleton Γ(Y, W) := e.toEquiv.subsingleton
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun x _ => Subsingleton.elim _ _, fun x _ => Subsingleton.elim _ _⟩
  let D : LocalEquations Y := LocalEquations.ofNonZeroDivisors UU hcover ff hunit hnzd
  -- the non-vanishing locus of the canonical section is the complement of `⋃ T p`
  have hnv : ∀ y, y ∈ D.canonicalSection.nonvanishingLocus ↔ ∀ p : P, y ∉ T p := by
    intro y
    constructor
    · intro hy p hyp
      have hyU : y ∈ UU (some p) :=
        (hmemUU p y).mpr ⟨hyp.1, fun p' hp' hy' => hdisj p p' (Ne.symm hp') y hyp hy'⟩
      have h := D.nonvanishingLocus_canonicalSection_inf (some p)
      have hmem : y ∈ D.canonicalSection.nonvanishingLocus ⊓ D.U (some p) := ⟨hy, hyU⟩
      rw [h] at hmem
      change y ∈ Y.basicOpen (res _ (t p)) at hmem
      rw [Scheme.basicOpen_res] at hmem
      exact hyp.2 hmem.2
    · intro hy
      have hyU : y ∈ UU none := (hmem0 y).mpr hy
      have h := D.nonvanishingLocus_canonicalSection_inf none
      have hmem : y ∈ Y.basicOpen (D.f none) := by
        change y ∈ Y.basicOpen (1 : Γ(Y, UU none))
        rw [Scheme.basicOpen_one]
        exact hyU
      rw [← h] at hmem
      exact hmem.1
  refine ⟨D, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hnv]
    constructor
    · intro h hyP
      exact h ⟨y, hyP⟩ (hpT ⟨y, hyP⟩)
    · intro hyP p hyp
      exact hyP (hTs p y hyp hy ▸ p.2)
  · rw [hnv] at hy
    push Not at hy
    obtain ⟨p, hyp⟩ := hy
    exact ⟨p, p.2, hspec p y hyp⟩

end Divisor

end

end DeJongAlterations.StableModification.BlowDown.SectionsDivisor
