/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.StableModification.CurvesField.OrdinaryCompletionBranches
import DeJongAlterations.StableModification.CurvesField.GenusReduced
import DeJongAlterations.Geometry.CurveFibrationBaseChangeSmooth
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# The fibres of a nodal curve are reduced (Temkin, proof of Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (`stabcritlem`, T:3119–3121): after replacing `C'` by `Nr_{C'_η}(C')` "`C'` has
geometrically reduced `S`-fibres". For a semi-stable (nodal) curve this needs no normalization: a
nodal curve has reduced geometric fibres, since a smooth point has a regular local ring and an
ordinary double point has completed local ring `K[[u, v]]/(uv)`, which is reduced and contains the
(Noetherian) local ring. Reducedness descends from the geometric fibre to the fibre over any field
point, since `X_L → X_K` is faithfully flat for a field extension `L/K` (blueprint
`lem:sm-bd-nodal-reduced`, chapter `sm-blow-down-criterion.tex`).

## Main results

* `isReduced_stalk_of_mem_smoothLocus`: the local ring at a smooth point of a scheme over a field
  is reduced.
* `isReduced_formalUV`, `isReduced_stalk_of_isGeometricOrdinaryDoublePoint`: the formal node
  `K[[u, v]]/(uv)` is reduced, hence so is the local ring at an ordinary double point of a locally
  Noetherian scheme.
* `isReduced_of_forall_isClosed`: a scheme locally of finite type over an algebraically closed field
  is reduced as soon as its local rings at the closed points are.
* `IsNodalFiber.isReduced`: a nodal curve over an algebraically closed field is reduced.
* `IsNodalCurve.isReduced_pullback_of_isAlgClosed`: the geometric fibres of a nodal curve are
  reduced; `IsNodalCurve.isReduced_pullback`, `IsNodalCurve.isReduced_fiber`: so are its fibres
  over all field points (by descent along `Spec K̄ → Spec K`,
  `isReduced_of_isReduced_pullback`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.BlowDown

open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV

universe u

section Stalks

variable {K : Type u} [Field K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K))

/-- **The local ring at a smooth point is reduced**: the smooth locus of `q : Y → Spec K` is a
smooth `K`-scheme, hence reduced, and its local rings are those of `Y`. -/
theorem isReduced_stalk_of_mem_smoothLocus [LocallyOfFinitePresentation q] {y : Y}
    (hy : y ∈ q.smoothLocus) : _root_.IsReduced (Y.presheaf.stalk y) := by
  set W := q.smoothLocus
  have hW : (W.ι ≫ q).smoothLocus = ⊤ := by
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact top_le_iff.mp fun z _ => z.2
  have : Smooth (W.ι ≫ q) := Scheme.Hom.smoothLocus_eq_top_iff.mp hW
  have : IsReduced W.toScheme :=
    Geometry.CurveFibrationBaseChange.isReduced_of_smooth_field (W.ι ≫ q)
  have : _root_.IsReduced (W.toScheme.presheaf.stalk ⟨y, hy⟩) :=
    isReduced_stalk_of_isReduced (X := W.toScheme) ⟨y, hy⟩
  exact isReduced_of_injective (W.stalkIso ⟨y, hy⟩).inv.hom
    (ConcreteCategory.bijective_of_isIso (W.stalkIso ⟨y, hy⟩).inv).1

variable (K) in
/-- **The formal node `K[[u, v]]/(uv)` is reduced**: it embeds into `K[[t]] × K[[t]]` by
restriction to the two axes (`CurvesField.OrdinaryCompletion.branchMap_injective`). -/
theorem isReduced_formalUV : _root_.IsReduced (FormalUV K) :=
  isReduced_of_injective (CurvesField.OrdinaryCompletion.branchMap K)
    CurvesField.OrdinaryCompletion.branchMap_injective

/-- **The local ring at an ordinary double point is reduced**: it is Noetherian, so it embeds into
its completion (Krull's intersection theorem), which is isomorphic to the reduced ring
`K[[u, v]]/(uv)`. -/
theorem isReduced_stalk_of_isGeometricOrdinaryDoublePoint [IsLocallyNoetherian Y] {y : Y}
    (hy : Geometry.IsGeometricOrdinaryDoublePoint q y) :
    _root_.IsReduced (Y.presheaf.stalk y) := by
  let := Scheme.completedLocalRingAlgebra q y
  obtain ⟨e⟩ := hy
  have : _root_.IsReduced (FormalUV K) := isReduced_formalUV K
  have : _root_.IsReduced (Y.completedLocalRing y) :=
    isReduced_of_injective e.toRingEquiv.toRingHom e.injective
  refine isReduced_of_injective (Y.toCompletedLocalRing y) ?_
  intro a b hab
  rw [Scheme.toCompletedLocalRing_apply, Scheme.toCompletedLocalRing_apply] at hab
  exact AdicCompletion.of_injective _ _ hab

end Stalks

section ClosedPoints

variable {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K))
  [LocallyOfFiniteType q]

include q in
/-- **Reducedness is checked at closed points** for schemes locally of finite type over an
algebraically closed field: on an affine open `U = Spec R`, the localizations of `R` at maximal
ideals are the local rings at points of `U` which are closed in `Y`, so `R` is reduced, and every
local ring of `Y` is a localization of such an `R`. -/
theorem isReduced_of_forall_isClosed
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → _root_.IsReduced (Y.presheaf.stalk y)) :
    IsReduced Y := by
  have hU : ∀ U : Y.Opens, IsAffineOpen U → _root_.IsReduced Γ(Y, U) := by
    intro U hU
    refine isReduced_ofLocalizationMaximal _ fun J hJ => ?_
    let z : Y := hU.fromSpec ⟨J, hJ.isPrime⟩
    have hzU : z ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨_, rfl⟩
    have hprime : hU.primeIdealOf ⟨z, hzU⟩ = ⟨J, hJ.isPrime⟩ :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨z, hzU⟩)
    have hzc : IsClosed ({z} : Set Y) := by
      have hcl : IsClosed ({(⟨J, hJ.isPrime⟩ : PrimeSpectrum Γ(Y, U))} : Set _) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hJ
      have : LocallyOfFiniteType (hU.fromSpec ≫ q) := inferInstance
      exact Curves.isClosed_image_of_isClosed (q := hU.fromSpec ≫ q) (q' := q) hU.fromSpec rfl
        (y := (⟨J, hJ.isPrime⟩ : PrimeSpectrum Γ(Y, U))) hcl
    have hred := h z hzc
    let := Y.presheaf.algebra_section_stalk ⟨z, hzU⟩
    have hloc := hU.isLocalization_stalk ⟨z, hzU⟩
    rw [hprime] at hloc
    let e := IsLocalization.algEquiv J.primeCompl (Localization.AtPrime J) (Y.presheaf.stalk z)
    exact isReduced_of_injective e.toRingEquiv.toRingHom e.injective
  have hst : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨_, ⟨U, hUa, rfl⟩, hyU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    have hR := hU U hUa
    let := Y.presheaf.algebra_section_stalk ⟨y, hyU⟩
    have hloc := hUa.isLocalization_stalk ⟨y, hyU⟩
    exact isReduced_localizationPreserves (hUa.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
      (Y.presheaf.stalk y) hR
  exact isReduced_of_isReduced_stalk Y

/-- **A nodal curve over an algebraically closed field is reduced**: its closed points are smooth
points or ordinary double points, whose local rings are reduced. -/
theorem _root_.DeJongAlterations.StableModification.Curves.IsNodalFiber.isReduced
    (hq : Curves.IsNodalFiber q) : IsReduced Y := by
  have := CurvesField.Genus.isLocallyNoetherian_of_locallyOfFiniteType q
  refine isReduced_of_forall_isClosed q fun y hy => ?_
  rcases hq.nodes y hy with hsm | hnode
  · have : LocallyOfFinitePresentation q := inferInstance
    exact isReduced_stalk_of_mem_smoothLocus q hsm
  · exact isReduced_stalk_of_isGeometricOrdinaryDoublePoint q hnode

end ClosedPoints

section Descent

variable {X : Scheme.{u}} {K : Type u} [Field K] (q : X ⟶ Spec (.of K))

/-- `Spec L → Spec K` is scheme-theoretically dominant for a field extension `L/K`. -/
theorem isSchemeTheoreticallyDominant_specMap_of_field {L : Type u} [Field L] (ι : K →+* L) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom ι)) := by
  have : Surjective (Spec.map (CommRingCat.ofHom ι)) := by
    refine ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- **Reducedness descends along a field extension**: if `X ×_K L` is reduced for a field extension
`L/K`, then `X` is reduced (`X_L → X` is flat, quasi-compact and scheme-theoretically dominant). -/
theorem isReduced_of_isReduced_pullback {L : Type u} [Field L] (ι : K →+* L)
    [IsReduced (pullback q (Spec.map (CommRingCat.ofHom ι)))] : IsReduced X := by
  have := isSchemeTheoreticallyDominant_specMap_of_field ι
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.fst q (Spec.map (CommRingCat.ofHom ι)))

end Descent

section Nodal

variable {C S : Scheme.{u}} (g : C ⟶ S) [DeJong.IsNodalCurve g]

/-- **The geometric fibres of a nodal curve are reduced** (blueprint `lem:sm-bd-nodal-reduced`,
geometric part). -/
theorem
    _root_.DeJongAlterations.StableModification.DeJong.IsNodalCurve.isReduced_pullback_of_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S) :
    IsReduced (pullback g a) := by
  have : LocallyOfFinitePresentation (pullback.snd g a) := inferInstance
  exact (Curves.IsNodalCurve.isNodalFiber g K a).isReduced (pullback.snd g a)

/-- **The fibres of a nodal curve over all field points are reduced** (blueprint
`lem:sm-bd-nodal-reduced`): `C ×_S Spec K` is reduced for every field `K` and `a : Spec K → S`,
by descent from the geometric fibre over an algebraic closure `K̄`. -/
theorem _root_.DeJongAlterations.StableModification.DeJong.IsNodalCurve.isReduced_pullback
    (K : Type u) [Field K] (a : Spec (.of K) ⟶ S) : IsReduced (pullback g a) := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have h := DeJong.IsNodalCurve.isReduced_pullback_of_isAlgClosed g (AlgebraicClosure K)
    (Spec.map (CommRingCat.ofHom ι) ≫ a)
  have : IsReduced (pullback (pullback.snd g a) (Spec.map (CommRingCat.ofHom ι))) :=
    isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso g a _).hom
  exact isReduced_of_isReduced_pullback (pullback.snd g a) ι

/-- **The scheme-theoretic fibres of a nodal curve are reduced** (blueprint
`lem:sm-bd-nodal-reduced`). -/
instance _root_.DeJongAlterations.StableModification.DeJong.IsNodalCurve.isReduced_fiber
    (s : S) : IsReduced (g.fiber s) :=
  DeJong.IsNodalCurve.isReduced_pullback g _ (S.fromSpecResidueField s)

end Nodal

end DeJongAlterations.StableModification.BlowDown
