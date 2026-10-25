/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModification.Global.Statements
import DeJongAlterations.StableModification.Projectivity.StableFibre

/-!
# The algebraically closed closed-fibre input sufficient for stable projectivity

This is a conditional adapter. Both the actual positive line bundle and the
section producer on arbitrary projective curves over algebraically closed
fields remain explicit inputs. The curve may be reducible or nonreduced.
No general geometric-field section descent, marked-dualizing-line construction,
or unconditional stable-modification projectivity is asserted.

Blueprint: `stable-projectivity-closed-fibres.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModificationBridge.StableProjectivityClosedFibres

open StableModification
open StableModification.Projectivity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Positive degree on the actual CANONICAL singleton normalization of every
nonclosed generic component, with unchanged original maps and field coefficients. -/
def PositiveCanonicalComponents {K : Type u} [Field K] {T : Scheme.{u}}
    (p : T ⟶ Spec (.of K)) (hp : IsProjectiveOver p) (L : LineBundleData T) : Prop :=
  letI : IsProper p := hp.isProper
  letI : CompactSpace T := CurvesField.Ample.compactSpace_of_quasiCompact p
  letI : IsAffineHom (pullback.diagonal (terminal.from T)) :=
    CurvesField.Ample.isAffineHom_diagonal_of_isSeparated p
  ∀ η ∈ genericPoints T, ¬ IsClosed ({η} : Set T) →
    let N := CurvesField.Genus.normalizationPoints ({η} : Set T)
    let ν := CurvesField.Genus.normalizationPointsMap ({η} : Set T)
    0 < CurvesField.DualityScheme.eulerCharOf
          ((L.pullback ν).twist (unitModule N) 1) (Cohomology.structureCoeff (ν ≫ p)) -
        CurvesField.Genus.eulerChar N (Cohomology.structureCoeff (ν ≫ p))

/-- The still-unproved curve producer needed here only over algebraically closed
fields, on the actual projective curve itself, including reducible/nonreduced curves. -/
def AlgClosedCurveGoodSection : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (T : Scheme.{u})
    (p : T ⟶ Spec (.of K)) (hp : IsProjectiveOver p), topologicalKrullDim T ≤ 1 →
    ∀ L : LineBundleData T, PositiveCanonicalComponents p hp L →
      ∃ (n : ℕ) (s : L.Sections n ⊤), 0 < n ∧
        (∀ x : T, ¬ IsClosed ({x} : Set T) → x ∈ s.nonvanishingLocus) ∧
        (∀ x : T, ¬ IsClosed ({x} : Set T) →
          ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus)

/-- At an actual closed point of an algebraically closed finite-type scheme, the
native residue field is algebraically closed; no identification is supplied. -/
theorem isAlgClosed_residueField_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) : IsAlgClosed (Y.residueField y) := by
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  let φ : k →+* Y.residueField y := (Spec.preimage (Y.fromSpecResidueField y ≫ pY)).hom
  have hfin : IsFinite (Y.fromSpecResidueField y ≫ pY) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  have hspec : Spec.map (CommRingCat.ofHom φ) = Y.fromSpecResidueField y ≫ pY :=
    Spec.map_preimage _
  have : IsFinite (Spec.map (CommRingCat.ofHom φ)) := hspec.symm ▸ hfin
  have hφ : φ.Finite := (IsFinite.SpecMap_iff (CommRingCat.ofHom φ)).mp this
  let : Algebra k (Y.residueField y) := φ.toAlgebra
  let : Module.Finite k (Y.residueField y) := hφ
  exact IsAlgClosed.of_ringEquiv k (Y.residueField y)
    (RingEquiv.ofBijective φ IsAlgClosed.algebraMap_bijective_of_isIntegral)

/-- A natural curve section producer over algebraically closed fields suffices for
the existing local-to-global criterion, using only actual CLOSED fibres. -/
theorem isRelativelyProjective_of_algClosedCurveGoodSection
    (hsec : AlgClosedCurveGoodSection.{u}) {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) (hY : IsProjectiveOver pY)
    (β : X ⟶ Y) (hloc : LocallyRelativelyProjective pY β) (L : LineBundleData X)
    (hdim : ∀ y : Y, IsClosed ({y} : Set Y) → topologicalKrullDim (β.fiber y) ≤ 1)
    (hpos : ∀ y : Y, IsClosed ({y} : Set Y) →
      PositiveCanonicalComponents (β.fiberToSpecResidueField y)
        (CurvesField.isProjectiveOver_fiber_of_locallyRelativelyProjective hloc y)
        (L.pullback (β.fiberι y))) :
    DeJong.IsRelativelyProjective pY β := by
  let : IsProper pY := hY.isProper
  apply isRelativelyProjective_of_fiberSections pY hY β L hloc hdim
  · intro y hy
    let := isAlgClosed_residueField_of_isClosed pY y hy
    infer_instance
  · intro y hy
    let := isAlgClosed_residueField_of_isClosed pY y hy
    exact hsec (Y.residueField y) (β.fiber y) (β.fiberToSpecResidueField y)
      (CurvesField.isProjectiveOver_fiber_of_locallyRelativelyProjective hloc y)
      (hdim y hy) (L.pullback (β.fiberι y)) (hpos y hy)

/-- The genuine positive-line-bundle input still needed in the exact stable
modification situation. This does not assume sections or relative projectivity. -/
def StableClosedFibrePositiveLineBundle (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) (_ : IsVariety pS), IsNormalScheme S →
    IsProjectiveOver pS →
    ∀ (C : Scheme.{u}) (g : C ⟶ S) (D : C.IdealSheafData),
      IsProjectiveOver (g ≫ pS) → DeJong.IsMultipointedCurve g D →
      Smooth (g.fiberToSpecResidueField (genericPoint S)) →
      DeJong.IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
        (DeJong.fiberMarks g D (genericPoint S)) →
      GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)) →
    ∀ (S' : Scheme.{u}) [IsIntegral S'], IsNormalScheme S' →
    ∀ (ψ : S' ⟶ S) [IsAlteration ψ], IsProjectiveOver (ψ ≫ pS) →
    ∀ (C' : Scheme.{u}) (β : C' ⟶ pullback (C := Scheme.{u}) g ψ) (D' : C'.IdealSheafData),
      Curves.IsStableModification β (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) D' →
      Global.IsNumericallyStable β (pullback.snd g ψ) D' →
      ∀ hloc : LocallyRelativelyProjective (pullback.snd g ψ ≫ ψ ≫ pS) β,
      ∃ L : LineBundleData C', ∀ y : pullback (C := Scheme.{u}) g ψ,
        IsClosed ({y} : Set (pullback (C := Scheme.{u}) g ψ)) →
          PositiveCanonicalComponents (β.fiberToSpecResidueField y)
            (CurvesField.isProjectiveOver_fiber_of_locallyRelativelyProjective hloc y)
            (L.pullback (β.fiberι y))

/-- Conditional adapter only: the two explicit natural producers imply the exact
projectivity input of the final alteration route; neither producer is proved here. -/
theorem stableModificationProjectivity_of_closedFibres
    (hsec : AlgClosedCurveGoodSection.{u}) {k : Type u} [Field k] [IsAlgClosed k]
    (hpos : StableClosedFibrePositiveLineBundle k) : Global.StableModificationProjectivity k := by
  intro S pS hS hSn hSp C g D hC hm hsm hss hgi S' _ hS'n ψ _ hψp C' β D' hst hn hloc
  let := hst.isSemistablePair.nodal
  obtain ⟨L, hL⟩ := hpos S pS hS hSn hSp C g D hC hm hsm hss hgi S' hS'n ψ hψp
    C' β D' hst hn hloc
  exact isRelativelyProjective_of_algClosedCurveGoodSection hsec
    (pullback.snd g ψ ≫ ψ ≫ pS) (isProjectiveOver_pullback_snd_comp hSp hC hψp)
    β hloc L (fun y _ => topologicalKrullDim_fiber_le_one β (pullback.snd g ψ) y) hL

end DeJongAlterations.StableModificationBridge.StableProjectivityClosedFibres
