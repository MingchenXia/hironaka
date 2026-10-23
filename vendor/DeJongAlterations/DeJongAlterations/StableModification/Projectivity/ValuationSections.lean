/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3F)
-/
import DeJongAlterations.StableModification.Projectivity.StableFibre
import DeJongAlterations.StableModification.BlowDown.SectionsDivisor
import DeJongAlterations.StableModification.BlowDown.ContractionStep
import DeJongAlterations.StableModification.BlowDown.StabilityCriterion
import DeJongAlterations.StableModification.BlowDown.NodalReduced
import DeJongAlterations.StableModification.Omega.BaseChangeFibre
import DeJongAlterations.StableModification.CurvesField.StableDownGeometric
import DeJongAlterations.Geometry.RegularSmoothConverse

/-!
# Sections through smooth points of the closed fibre (`thm:sm-val-proj`, the divisor)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`), Theorem 1.1 at the level of a
valuation ring (T:1713–1749, "relative ampleness can be checked separately on each fiber", and the
sections `P̄ᵢ` of the proof of Prop. 4.4.6, T:3203–3210); PLAN-OM3 §3 "V-level (M7)", ERRATA
DJA-O37. Blueprint `sm-projectivity-valuation.tex` (restating the nodes `lem:sm-val-section-smooth`
and `lem:sm-val-section-divisor` of `sm-projectivity-relative.tex`).

Let `V` be a henselian local ring (in the application a valuation ring) whose residue field is
algebraically closed, `s` its closed point, `pY : Y ⟶ Spec V` and `β : X ⟶ Y` proper with
`q = β ≫ pY` a nodal curve. We construct line-bundle data on `X` with a global section `σ` which on
the closed fibre `X_s` vanishes exactly at a finite set `P` of closed `q`-smooth points meeting
every irreducible component of `X_s`. Its consequence `Valuation.exists_fiberSections` is the
section hypothesis of the local-to-global theorem
(`isRelativelyProjective_of_fiberSections_valuation`, lane OM3C) at every closed point of `Y`.

## Main results

* `LocalEquations.ofUnits`: local equations of an effective Cartier divisor from functions `fᵢ`
  on a cover such that `fᵢ` is a unit on `Uᵢ ∩ Uⱼ` for `i ≠ j`; the transition units are the
  quotients `fᵢ / fⱼ`, and no non-zero-divisor condition (hence no integrality of `X`) is needed.
* `isSmoothAt_of_mem_genericPoints_of_isReduced`: the generic points of a reduced scheme locally of
  finite type over a perfect field are smooth points (their local rings are fields, and finitely
  generated field extensions of a perfect field are formally smooth).
* `Valuation.exists_smooth_closedPoint` (`lem:sm-val-section-smooth`): every generic point of the
  closed fibre of a nodal curve over `V` specializes to a closed `q`-smooth point (the generic
  point of the fibre is smooth, the smooth locus of the fibre is the preimage of the smooth locus
  of `q` (`Omega.preimage_smoothLocus_eq_of_isNodalCurve`), and the fibre is a Jacobson space).
* `Valuation.exists_localEquations_of_smooth`: the divisor `∑ P̄ᵢ` through finitely many closed
  smooth points of the closed fibre (T44F's `BlowDown.SectionsDivisor.exists_localEquations`
  without the hypothesis `IsIntegral X`, using `LocalEquations.ofUnits`).
* `Valuation.exists_fiberSections` (`lem:sm-val-section-divisor`): line-bundle data `L` on `X`
  with `HasFiberSection β L y` at every closed point `y` of `Y`.

## Remarks on the route

Compared with the plan (PLAN-OM3 §3, M7), no Hensel section through a contracted component of a
non-closed fibre is needed, and neither the smoothness of the generic fibre nor the finiteness of
`Spec V` is used (ERRATA DJA-O37). Compared with the planned proof of `lem:sm-val-section-smooth`
(nodes are isolated in the non-smooth locus), the smoothness of the generic points of the closed
fibre is obtained from the reducedness of the fibres of a nodal curve
(`DeJong.IsNodalCurve.isReduced_fiber`) and the perfectness of the residue field; this avoids the
étale local structure at the nodes and the projectivity of the closed fibre (used by the
integrated `BlowDown.NoClosedExc.isSmoothAt_of_mem_genericPoints`). Integrality of `X`, needed by
`LocalEquations.ofNonZeroDivisors`, is avoided by `LocalEquations.ofUnits`: in the cover used for
`∑ P̄ᵢ`, every local equation is a unit on the overlaps with the other charts.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Projectivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ### Local equations which are units on the overlaps -/

namespace LocalEquations

variable {X : Scheme.{u}} {ι : Type u} [DecidableEq ι] (U : ι → X.Opens) (f : ∀ i, Γ(X, U i))
  (hunit : ∀ i j, i ≠ j → IsUnit (res (inf_le_left : U i ⊓ U j ≤ U i) (f i)))

omit [DecidableEq ι] in
include hunit in
/-- Under the hypothesis of `ofUnits`, `fⱼ` is also a unit on `Uᵢ ∩ Uⱼ` for `i ≠ j`. -/
lemma isUnit_res_right {i j : ι} (h : i ≠ j) :
    IsUnit (res (inf_le_right : U i ⊓ U j ≤ U j) (f j)) := by
  have hle : U i ⊓ U j ≤ U j ⊓ U i := le_of_eq (inf_comm _ _)
  have e : res hle (res (inf_le_left : U j ⊓ U i ≤ U j) (f j)) =
      res (inf_le_right : U i ⊓ U j ≤ U j) (f j) := res_res _ _ _ _
  rw [← e]
  exact (hunit j i (Ne.symm h)).map _

/-- The transition unit `fᵢ / fⱼ` on `Uᵢ ∩ Uⱼ` (and `1` for `i = j`). -/
def unitOfUnits (i j : ι) : Γ(X, U i ⊓ U j)ˣ :=
  if h : i = j then 1 else (hunit i j h).unit * (isUnit_res_right U f hunit h).unit⁻¹

/-- `fᵢ = (fᵢ / fⱼ) · fⱼ` on `Uᵢ ∩ Uⱼ`. -/
lemma unitOfUnits_spec (i j : ι) :
    res (inf_le_left : U i ⊓ U j ≤ U i) (f i) =
      (unitOfUnits U f hunit i j : Γ(X, U i ⊓ U j)) *
        res (inf_le_right : U i ⊓ U j ≤ U j) (f j) := by
  unfold unitOfUnits
  split_ifs with h
  · subst h
    rw [Units.val_one, one_mul]
  · rw [Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]

/-- **Local equations from functions which are units on the overlaps** (blueprint
`lem:sm-pv-units`): if `fᵢ ∈ Γ(Uᵢ, 𝒪_X)` restricts to a unit on `Uᵢ ∩ Uⱼ` for all `i ≠ j`, the
quotients `fᵢ / fⱼ` form a cocycle and the `fᵢ` are local equations of an effective Cartier
divisor (supported in the parts of the `Uᵢ` not met by the other charts). -/
def ofUnits (hU : ⨆ i, U i = ⊤) : LocalEquations X where
  ι := ι
  U := U
  iSup_eq_top := hU
  u := unitOfUnits U f hunit
  cocycle i j k := by
    have hT₁ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
    have hT₂ : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hT₃ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hTi : U i ⊓ U j ⊓ U k ≤ U i := inf_le_left.trans inf_le_left
    have hTj : U i ⊓ U j ⊓ U k ≤ U j := inf_le_left.trans inf_le_right
    have hTk : U i ⊓ U j ⊓ U k ≤ U k := inf_le_right
    by_cases hall : i = j ∧ j = k
    · obtain ⟨rfl, rfl⟩ := hall
      simp only [unitOfUnits, dite_true, Units.val_one, map_one, one_mul]
    have e₁ : res hTi (f i) = res hT₁ (unitOfUnits U f hunit i j : Γ(X, U i ⊓ U j)) *
        res hTj (f j) := by
      have := congrArg (res hT₁) (unitOfUnits_spec U f hunit i j)
      rwa [res_res_trans, map_mul, res_res_trans] at this
    have e₂ : res hTj (f j) = res hT₂ (unitOfUnits U f hunit j k : Γ(X, U j ⊓ U k)) *
        res hTk (f k) := by
      have := congrArg (res hT₂) (unitOfUnits_spec U f hunit j k)
      rwa [res_res_trans, map_mul, res_res_trans] at this
    have e₃ : res hTi (f i) = res hT₃ (unitOfUnits U f hunit i k : Γ(X, U i ⊓ U k)) *
        res hTk (f k) := by
      have := congrArg (res hT₃) (unitOfUnits_spec U f hunit i k)
      rwa [res_res_trans, map_mul, res_res_trans] at this
    -- `f k` is a unit on the triple overlap
    have hk : IsUnit (res hTk (f k)) := by
      by_cases hik : i = k
      · subst hik
        have hji : j ≠ i := fun h => hall ⟨h.symm, h⟩
        have hle : U i ⊓ U j ⊓ U i ≤ U i ⊓ U j := hT₁
        have e : res hle (res (inf_le_left : U i ⊓ U j ≤ U i) (f i)) = res hTk (f i) :=
          res_res _ _ _ _
        rw [← e]
        exact (hunit i j (Ne.symm hji)).map _
      · have hle : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := hT₃
        have e : res hle (res (inf_le_right : U i ⊓ U k ≤ U k) (f k)) = res hTk (f k) :=
          res_res _ _ _ _
        rw [← e]
        exact (isUnit_res_right U f hunit hik).map _
    have key : (res hT₁ (unitOfUnits U f hunit i j : Γ(X, U i ⊓ U j)) *
        res hT₂ (unitOfUnits U f hunit j k : Γ(X, U j ⊓ U k)) -
        res hT₃ (unitOfUnits U f hunit i k : Γ(X, U i ⊓ U k))) * res hTk (f k) = 0 := by
      rw [sub_mul, mul_assoc, ← e₂, ← e₁, ← e₃, sub_self]
    exact sub_eq_zero.mp ((hk.mul_left_eq_zero).mp key)
  f := f
  f_eq i j := unitOfUnits_spec U f hunit i j

end LocalEquations

/-! ### Generic points of reduced schemes over perfect fields are smooth -/

section GenericSmooth

variable {k : Type u} [Field k] {F : Scheme.{u}}

/-- The local ring of a reduced scheme at a generic point (of an irreducible component) is a
field: it is reduced of dimension zero. -/
theorem isField_stalk_of_mem_genericPoints [IsReduced F] {w : F} (hw : w ∈ genericPoints F) :
    IsField (F.presheaf.stalk w) := by
  have hm : IsMax w := by
    intro z hwz
    have hzw : z ⤳ w := hwz
    have := (CurvesField.Genus.mem_genericPoints_iff w).mp hw z hzw
    rw [this]
  have hco : Order.coheight w = 0 := Order.coheight_eq_zero.mpr hm
  have : Ring.KrullDimLE 0 (F.presheaf.stalk w) := krullDimLE_of_coheight_le hco.le
  exact Ring.KrullDimLE.isField_of_isReduced

/-- **The generic points of a reduced scheme over a perfect field are smooth points**
(blueprint `lem:sm-pv-generic-smooth`): the local ring at a generic point `w` is a field, finitely
generated (essentially of finite type) over the perfect field `k`, hence formally smooth over `k`
(`Algebra.FormallySmooth.of_perfectField`). -/
theorem isSmoothAt_of_mem_genericPoints_of_isReduced [PerfectField k]
    (p : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [IsReduced F] {w : F}
    (hw : w ∈ genericPoints F) : DeJong.IsSmoothAt p w := by
  let B := Geometry.RegularSmoothConverse.specFieldStalk (p w)
  let : Field B := (Geometry.RegularSmoothConverse.specFieldStalk_isField (p w)).toField
  let : PerfectField B := Geometry.RegularSmoothConverse.specFieldStalk_perfect (p w)
  let : Field (F.presheaf.stalk w) := (isField_stalk_of_mem_genericPoints hw).toField
  let : Algebra B (F.presheaf.stalk w) := (p.stalkMap w).hom.toAlgebra
  let : Algebra.EssFiniteType B (F.presheaf.stalk w) := LocallyOfFiniteType.stalkMap p w
  have : Algebra.FormallySmooth B (F.presheaf.stalk w) := Algebra.FormallySmooth.of_perfectField
  exact this

end GenericSmooth

namespace Valuation

/-! ### Smooth closed points on the components of the closed fibre -/

section ClosedFibre

variable {V : Type u} [CommRing V] [IsLocalRing V] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of V)) [DeJong.IsNodalCurve q]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (closedPoint V))]

/-- **Smooth closed points on the components of the closed fibre** (blueprint
`lem:sm-val-section-smooth`, `lem:sm-pv-closed-smooth`): let `q : X ⟶ Spec V` be a nodal curve
over a local ring whose residue field is algebraically closed. Every generic point `w` of the
closed fibre `X_s` specializes to a closed point `p` of `X` at which `q` is smooth. (The fibre is
reduced, so `w` is a smooth point of `X_s → Spec κ(s)`; the smooth locus of `X_s` is the preimage
of the smooth locus of `q`; and a non-empty locally closed subset `closure {w} ∩ Sm(X_s)` of the
Jacobson space `X_s` contains a closed point.) -/
theorem exists_smooth_closedPoint {w : q.fiber (closedPoint V)}
    (hw : w ∈ genericPoints (q.fiber (closedPoint V))) :
    ∃ p : X, IsClosed ({p} : Set X) ∧ p ∈ q.smoothLocus ∧ q p = closedPoint V ∧
      q.fiberι (closedPoint V) w ⤳ p := by
  have : LocallyOfFinitePresentation (q.fiberToSpecResidueField (closedPoint V)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  have hsm : w ∈ (q.fiberToSpecResidueField (closedPoint V)).smoothLocus :=
    isSmoothAt_of_mem_genericPoints_of_isReduced
      (k := (Spec (CommRingCat.of V)).residueField (closedPoint V))
      (q.fiberToSpecResidueField (closedPoint V)) hw
  have : JacobsonSpace (q.fiber (closedPoint V)) :=
    LocallyOfFiniteType.jacobsonSpace (q.fiberToSpecResidueField (closedPoint V))
  obtain ⟨z, ⟨hzw, hzs⟩, hzc⟩ := nonempty_inter_closedPoints
    (Z := closure {w} ∩ ((q.fiberToSpecResidueField (closedPoint V)).smoothLocus :
      Set (q.fiber (closedPoint V)))) ⟨w, subset_closure rfl, hsm⟩
    (isClosed_closure.isLocallyClosed.inter
      (q.fiberToSpecResidueField (closedPoint V)).smoothLocus.isOpen.isLocallyClosed)
  have e := Omega.preimage_smoothLocus_eq_of_isNodalCurve (f := q)
    ((Spec (CommRingCat.of V)).residueField (closedPoint V))
    ((Spec (CommRingCat.of V)).fromSpecResidueField (closedPoint V))
  have hz' : z ∈ (pullback.snd q
      ((Spec (CommRingCat.of V)).fromSpecResidueField (closedPoint V))).smoothLocus := hzs
  rw [← e] at hz'
  refine ⟨q.fiberι (closedPoint V) z, ?_, hz', BlowDown.apply_fiberι q (closedPoint V) z, ?_⟩
  · rw [← Set.image_singleton]
    exact (BlowDown.isClosedEmbedding_fiberι_closedPoint q).isClosedMap _
      (mem_closedPoints_iff.mp hzc)
  · exact (specializes_iff_mem_closure.mpr hzw).map (q.fiberι (closedPoint V)).continuous

end ClosedFibre

/-! ### The divisor through finitely many smooth points, without integrality -/

section Divisor

variable {V : Type u} [CommRing V] [HenselianLocalRing V] [IsAlgClosed (ResidueField V)]
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of V)) [IsSeparated q] [LocallyOfFinitePresentation q]
  [UniversallyClosed q]

omit [HenselianLocalRing V] [IsAlgClosed (ResidueField V)] in
/-- A function on an open `U` whose basic open contains `W ≤ U` restricts to a unit on `W`. -/
lemma isUnit_res_of_le_basicOpen {U W : Y.Opens} (h : W ≤ U) (t : Γ(Y, U))
    (hW : W ≤ Y.basicOpen t) : IsUnit (res h t) := by
  apply isUnit_of_basicOpen_eq
  change Y.basicOpen (Y.presheaf.map (homOfLE h).op t) = W
  rw [Scheme.basicOpen_res]
  exact inf_eq_left.mpr hW

/-- **The divisor `∑ P̄ᵢ` through finitely many smooth points** (Temkin, T:3207–3210; blueprint
`lem:sm-pv-divisor`): T44F's `BlowDown.SectionsDivisor.exists_localEquations` without the
hypothesis that `Y` is integral (and without the auxiliary point of the closed fibre outside `P`).
There is line-bundle data with local equations whose canonical section vanishes on the closed
fibre exactly at the given closed smooth points, and every zero of which specializes to one of
them. The charts are those of T44F (`Y ∖ ⋃ Tᵢ` with equation `1`, `Uᵢ ∖ ⋃_{j ≠ i} Tⱼ` with
equation `tᵢ`); the transition units come from `LocalEquations.ofUnits`. -/
theorem exists_localEquations_of_smooth
    (hpure : Curves.SemistableOpen.PureOneDimensionalFibres q)
    (P : Finset Y) (hsm : ∀ p ∈ P, p ∈ q.smoothLocus) (hcl : ∀ p ∈ P, IsClosed ({p} : Set Y))
    (hs : ∀ p ∈ P, q p = closedPoint V) :
    ∃ D : LocalEquations Y,
      (∀ y, q y = closedPoint V → (y ∈ D.canonicalSection.nonvanishingLocus ↔ y ∉ P)) ∧
      ∀ y, y ∉ D.canonicalSection.nonvanishingLocus → ∃ p ∈ P, y ⤳ p := by
  classical
  have hloc : ∀ p : P, ∃ (U : Y.Opens) (t : Γ(Y, U)), (p : Y) ∈ U ∧ (p : Y) ∉ Y.basicOpen t ∧
      IsClosed ((U : Set Y) \ Y.basicOpen t) ∧
      ∀ y ∈ (U : Set Y) \ Y.basicOpen t, q y = closedPoint V → y = p := fun p =>
    BlowDown.SectionsLocal.exists_localEquation q hpure (hsm p p.2) (hcl p p.2) (hs p p.2)
  choose U t hpU hpt hTcl hTs using hloc
  let T : P → Set Y := fun p => (U p : Set Y) \ Y.basicOpen (t p)
  have hpT : ∀ p : P, (p : Y) ∈ T p := fun p => ⟨hpU p, hpt p⟩
  -- every point of `T p` specializes to `p`
  have hspec : ∀ (p : P) (y : Y), y ∈ T p → y ⤳ p := by
    intro p y hy
    obtain ⟨z, hyz, hz⟩ := BlowDown.SectionsDivisor.exists_specializes_closedPoint q y
    have hzT : z ∈ T p := hyz.mem_closed (hTcl p) hy
    rwa [hTs p z hzT hz] at hyz
  -- the `T p` are pairwise disjoint
  have hdisj : ∀ p p' : P, p ≠ p' → ∀ y, y ∈ T p → y ∉ T p' := by
    intro p p' hne y hy hy'
    obtain ⟨z, hyz, hz⟩ := BlowDown.SectionsDivisor.exists_specializes_closedPoint q y
    have h1 := hTs p z (hyz.mem_closed (hTcl p) hy) hz
    have h2 := hTs p' z (hyz.mem_closed (hTcl p') hy') hz
    exact hne (Subtype.ext (h1.symm.trans h2))
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
    apply isUnit_res_of_le_basicOpen
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
  -- every equation is a unit on the overlaps with the other charts
  have hunit : ∀ i j, i ≠ j → IsUnit (res (inf_le_left : UU i ⊓ UU j ≤ UU i) (ff i)) := by
    rintro (_ | p) j hij
    · change IsUnit (res _ (1 : Γ(Y, UU none)))
      rw [map_one]
      exact isUnit_one
    · rcases j with _ | p'
      · exact hbasic p (UU (some p) ⊓ UU none) inf_le_left (fun y hy => (hmem0 y).mp hy.2 p)
      · have hpp : p ≠ p' := fun h => hij (congrArg some h)
        exact hbasic p (UU (some p) ⊓ UU (some p')) inf_le_left
          (fun y hy => ((hmemUU p' y).mp hy.2).2 p hpp)
  let D : LocalEquations Y := LocalEquations.ofUnits UU ff hunit hcover
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

/-! ### Fibre sections at the closed points of the target -/

section ClosedPoints

variable {V : Type u} [CommRing V] [IsLocalRing V] {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of V))
  [UniversallyClosed pY]

/-- The closed points of a scheme universally closed over a local ring lie over the closed
point. -/
theorem apply_eq_closedPoint_of_isClosed {y : Y} (hy : IsClosed ({y} : Set Y)) :
    pY y = closedPoint V := by
  have hcl : IsClosed ({pY y} : Set (Spec (.of V))) := by
    rw [← Set.image_singleton]
    exact pY.isClosedMap _ hy
  have hmax : (pY y).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcl
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

end ClosedPoints

section FiberSections

variable {V : Type u} [CommRing V] [HenselianLocalRing V] [IsAlgClosed (ResidueField V)]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (closedPoint V))]
  {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of V)) [IsProper pY] (β : X ⟶ Y) [IsProper β]
  [DeJong.IsNodalCurve (β ≫ pY)]

include pY in
/-- **Fibre sections from the divisor `∑ P̄ᵢ`** (blueprint `lem:sm-val-section-divisor`,
`lem:sm-pv-fiber-sections`): let `V` be a henselian local ring with algebraically closed residue
field, `pY : Y ⟶ Spec V` and `β : X ⟶ Y` proper with `β ≫ pY` a nodal curve. There is line-bundle
data `L` on `X` with a fibre section (`HasFiberSection β L y`) at every closed point `y` of `Y`.

Choose a closed smooth point `p_w` below every generic point `w` of the closed fibre `X_s`
(`exists_smooth_closedPoint`) and take `L = 𝒪(∑ P̄ᵢ)` with its canonical section `σ`
(`exists_localEquations_of_smooth`). A closed `y` lies over `s`; a non-closed point `x` of `X_y` is
a non-closed point of the one-dimensional `X_s`, hence a generic point of `X_s`, so `σ(x) ≠ 0`
(`x` is not one of the closed points `p_w`) and `x ⤳ p_x` with `σ(p_x) = 0`, `p_x ∈ X_y`. -/
theorem exists_fiberSections :
    ∃ L : LineBundleData X, ∀ y : Y, IsClosed ({y} : Set Y) → HasFiberSection β L y := by
  classical
  have hdim : topologicalKrullDim ((β ≫ pY).fiber (closedPoint V)) ≤ 1 :=
    BlowDown.topologicalKrullDim_fiber_le_one_of_nodal (β ≫ pY) (closedPoint V)
  have : CompactSpace ((β ≫ pY).fiber (closedPoint V)) :=
    BlowDown.compactSpace_of_quasiCompact ((β ≫ pY).fiberToSpecResidueField (closedPoint V))
  have : NoetherianSpace ((β ≫ pY).fiber (closedPoint V)) :=
    BlowDown.noetherianSpace_fiber (β ≫ pY) (closedPoint V)
  have hG : (genericPoints ((β ≫ pY).fiber (closedPoint V))).Finite := Set.toFinite _
  have hex : ∀ w ∈ genericPoints ((β ≫ pY).fiber (closedPoint V)), ∃ p : X,
      IsClosed ({p} : Set X) ∧ p ∈ (β ≫ pY).smoothLocus ∧ (β ≫ pY) p = closedPoint V ∧
        (β ≫ pY).fiberι (closedPoint V) w ⤳ p :=
    fun w hw => exists_smooth_closedPoint (β ≫ pY) hw
  choose pt hptc hpts hpt0 hptsp using hex
  let P : Finset X := hG.toFinset.attach.image fun w => pt w.1 (hG.mem_toFinset.mp w.2)
  have hmemP : ∀ p, p ∈ P ↔ ∃ (w : (β ≫ pY).fiber (closedPoint V))
      (hw : w ∈ genericPoints ((β ≫ pY).fiber (closedPoint V))), pt w hw = p := by
    intro p
    simp only [P, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
      Set.Finite.mem_toFinset]
  have hPc : ∀ p ∈ P, IsClosed ({p} : Set X) := fun p hp => by
    obtain ⟨w, hw, rfl⟩ := (hmemP p).mp hp
    exact hptc w hw
  obtain ⟨D, hD, -⟩ := exists_localEquations_of_smooth (β ≫ pY)
    (DeJong.IsNodalCurve.pureGeometricFibers (g := β ≫ pY)) P
    (fun p hp => by obtain ⟨w, hw, rfl⟩ := (hmemP p).mp hp; exact hpts w hw) hPc
    (fun p hp => by obtain ⟨w, hw, rfl⟩ := (hmemP p).mp hp; exact hpt0 w hw)
  refine ⟨D.toLineBundleData, fun y hy => ?_⟩
  have hys : pY y = closedPoint V := apply_eq_closedPoint_of_isClosed pY hy
  have hfs : ∀ x : β.fiber y, (β ≫ pY) (β.fiberι y x) = closedPoint V := fun x => by
    rw [Scheme.Hom.comp_apply, BlowDown.apply_fiberι β y x, hys]
  -- a point of `X_y` which is closed in `X` is closed in `X_y`
  have hclosed : ∀ x : β.fiber y, IsClosed ({β.fiberι y x} : Set X) →
      IsClosed ({x} : Set (β.fiber y)) := fun x hx => by
    have e : (β.fiberι y) ⁻¹' {β.fiberι y x} = {x} := by
      rw [← Set.image_singleton, (β.fiberι y).isEmbedding.injective.preimage_image]
    rw [← e]
    exact hx.preimage (β.fiberι y).continuous
  refine hasFiberSection_of_section (n := 1) one_pos D.canonicalSection (fun x hx => ?_)
    (fun x hx => ?_)
  · refine (hD _ (hfs x)).mpr fun hxP => hx (hclosed x (hPc _ hxP))
  · -- the point of the closed fibre below `x` is a generic point of the closed fibre
    obtain ⟨w, hw⟩ : β.fiberι y x ∈ Set.range ((β ≫ pY).fiberι (closedPoint V)) := by
      rw [Scheme.Hom.range_fiberι]
      exact hfs x
    have hwg : w ∈ genericPoints ((β ≫ pY).fiber (closedPoint V)) := by
      by_contra hng
      have hwc := CurvesField.Genus.isClosed_singleton_of_not_mem_genericPoints hdim hng
      apply hx
      apply hclosed x
      rw [← hw, ← Set.image_singleton]
      exact (BlowDown.isClosedEmbedding_fiberι_closedPoint (β ≫ pY)).isClosedMap _ hwc
    have hxp : β.fiberι y x ⤳ pt w hwg := hw ▸ hptsp w hwg
    have hpP : pt w hwg ∈ P := (hmemP _).mpr ⟨w, hwg, rfl⟩
    -- `p_w` lies on the fibre `X_y`
    have hpy : pt w hwg ∈ β ⁻¹' {y} := hxp.mem_closed (hy.preimage β.continuous)
      (BlowDown.apply_fiberι β y x)
    obtain ⟨z, hz⟩ : pt w hwg ∈ Set.range (β.fiberι y) := by
      rw [Scheme.Hom.range_fiberι]
      exact hpy
    refine ⟨z, ?_, ?_⟩
    · rw [← (β.fiberι y).isEmbedding.isInducing.specializes_iff, hz]
      exact hxp
    · rw [hz]
      exact fun h => (hD _ (hpt0 w hwg)).mp h hpP

end FiberSections

end Valuation

end

end DeJongAlterations.StableModification.Projectivity
