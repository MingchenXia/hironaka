/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Defs
public import Hironaka.Scheme.BlowUp.Rees.ChartRing
import Hironaka.Scheme.BlowUp.Rees.Irrelevant

/-!
# The charts of the affine blow-up

The affine blow-up `Proj Rees(I)` of `Spec R` along `I` is covered by the affine charts
`Spec R[I/a]`, `a ∈ I`, where `R[I/a] ⊆ R_a` is the subring of fractions `x/aⁿ` with `x ∈ Iⁿ`; for
generators `g₁, …, g_k` of `I` the charts of the `gᵢ` suffice, and over the base the chart of `a`
is `Spec` of the inclusion `R → R[I/a]` [Hau14, Theorem 4.19]; [Sta, Tag 0804].

* `affineBlowUp.chart I a : Spec R[I/a] ⟶ affineBlowUp I`: Mathlib's open immersion `Proj.awayι`
  of the chart `D₊(a t)` composed with `Spec` of the chart ring isomorphism `(Rees(I)_{at})₀ ≅
  R[I/a]` of `Hironaka.Scheme.BlowUp.Rees.ChartRing`.  It is an open immersion with image the basic
  open `D₊(a t)` of `Proj`.
* `affineBlowUp.affineOpenCover I`: the charts for `a ∈ I` cover, from Mathlib's
  `Proj.affineOpenCoverOfIrrelevantLESpan` and the fact that the irrelevant ideal is generated in
  degree one (`reesAlgebra.irrelevant_le_span_degreeOne`); `affineBlowUp.affineOpenCoverOfSpan s
  hs`: the charts of any generating set `s` of `I` cover (Hauser's `g₁, …, g_k`), with the empty
  family for `I = 0`, whence `affineBlowUp ⊥` is empty.
* `affineBlowUp.chart_π`: over the base the chart is `Spec (R → R[I/a])`, by
  `Proj.awayι_toSpecZero` and the constant-map compatibility of the chart ring isomorphism.
* `affineBlowUp.chart_preimage_chart`: inside the chart of `a`, the chart of `b` is the basic
  open `D(b/a) ⊆ Spec R[I/a]` — the identity `D₊(at) ∩ D₊(bt) = D₊(at · bt)` of `Proj`
  (Mathlib's `Proj.awayι_preimage_basicOpen`) transported along the chart ring isomorphism, under
  which Mathlib's localization element `bt/at` is `b/a`. This is the gluing of the charts along
  `R_{g_j}, R_{g_l} ⊆ R_{g_j g_l}` of [Hau14, Definition 4.13].

The underlying scheme is Mathlib's `Proj`; every statement here is a statement about `Proj` and
its `awayι` charts read through the ring isomorphism of `Hironaka.Scheme.BlowUp.Rees.ChartRing`.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Polynomial

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The chart ring isomorphism `(Rees(I)_{at})₀ ≅ R[I/a]` (`reesAlgebra.chartRingEquiv`) as an
isomorphism of `CommRingCat`. -/
noncomputable def _root_.reesAlgebra.chartIso (a : I) :
    CommRingCat.of (Away (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) ≅
      CommRingCat.of (affineBlowUpAlgebra I a) :=
  (reesAlgebra.chartRingEquiv a).toCommRingCatIso

/-- **The chart** of `a ∈ I` [Hau14, Theorem 4.19]; [Sta, Tag 0804]: the open immersion
`Spec R[I/a] ⟶ affineBlowUp I` — Mathlib's chart `Proj.awayι` of `D₊(a t)` composed with `Spec`
of the chart ring isomorphism. -/
noncomputable def affineBlowUp.chart (a : I) :
    Spec (.of (affineBlowUpAlgebra I a)) ⟶ affineBlowUp I :=
  Spec.map (reesAlgebra.chartIso I a).hom ≫
    Proj.awayι (reesAlgebra.grading I) (reesAlgebra.degreeOne I a) (reesAlgebra.degreeOne_mem a)
      one_pos

/-- The charts are open immersions. -/
instance affineBlowUp.isOpenImmersion_chart (a : I) : IsOpenImmersion (affineBlowUp.chart I a) :=
  inferInstanceAs (IsOpenImmersion (Spec.map _ ≫ Proj.awayι _ _ _ _))

/-- The image of the chart of `a` is the basic open `D₊(a t)` of `Proj`. -/
theorem affineBlowUp.opensRange_chart (a : I) :
    (affineBlowUp.chart I a).opensRange =
      Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a) := by
  unfold affineBlowUp.chart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- Every point of the affine blow-up lies in the chart of some `a ∈ I`: the `D₊(a t)` cover
`Proj` because the `a t` generate the irrelevant ideal (`reesAlgebra.irrelevant_le_span_degreeOne`;
Mathlib's `Proj.iSup_basicOpen_eq_top`). -/
theorem affineBlowUp.exists_mem_opensRange_chart (x : affineBlowUp I) :
    ∃ a : I, x ∈ (affineBlowUp.chart I a).opensRange := by
  have h := Proj.iSup_basicOpen_eq_top (reesAlgebra.grading I) (reesAlgebra.degreeOne I)
    (reesAlgebra.irrelevant_le_span_degreeOne I)
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp (h ▸ TopologicalSpace.Opens.mem_top x)
  exact ⟨a, (affineBlowUp.opensRange_chart I a).symm ▸ ha⟩

/-- **The chart cover**: the charts `Spec R[I/a]`, `a ∈ I`, form an affine open cover of the
affine blow-up [Sta, Tag 0804]. -/
noncomputable def affineBlowUp.affineOpenCover : (affineBlowUp I).AffineOpenCover where
  I₀ := I
  X a := .of (affineBlowUpAlgebra I a)
  f a := affineBlowUp.chart I a
  idx x := (affineBlowUp.exists_mem_opensRange_chart I x).choose
  covers x := (affineBlowUp.exists_mem_opensRange_chart I x).choose_spec

/-- The charts cover. -/
theorem affineBlowUp.iSup_opensRange_chart :
    ⨆ a : I, (affineBlowUp.chart I a).opensRange = ⊤ :=
  eq_top_iff.mpr fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr (affineBlowUp.exists_mem_opensRange_chart I x)

section GeneratingSet

variable (s : Set R) (hs : Ideal.span s = I)

/-- Every point lies in the chart of some element of a generating set `s` of `I` (Hauser's
charts of the generators `g₁, …, g_k` [Hau14, Theorem 4.19]). -/
theorem affineBlowUp.exists_mem_opensRange_chart_of_span_eq (x : affineBlowUp I) :
    ∃ y : s, x ∈ (affineBlowUp.chart I ⟨y, hs ▸ Ideal.subset_span y.2⟩).opensRange := by
  have h := Proj.iSup_basicOpen_eq_top (reesAlgebra.grading I)
    (fun y : s => reesAlgebra.degreeOne I ⟨y, hs ▸ Ideal.subset_span y.2⟩)
    (reesAlgebra.irrelevant_le_span_degreeOne_of_span_eq I s hs)
  obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp (h ▸ TopologicalSpace.Opens.mem_top x)
  exact ⟨y, (affineBlowUp.opensRange_chart I _).symm ▸ hy⟩

/-- The charts of a generating set `s` of `I` form an affine open cover; for `I = 0` the empty
family is allowed. -/
noncomputable def affineBlowUp.affineOpenCoverOfSpan : (affineBlowUp I).AffineOpenCover where
  I₀ := s
  X y := .of (affineBlowUpAlgebra I y)
  f y := affineBlowUp.chart I ⟨y, hs ▸ Ideal.subset_span y.2⟩
  idx x := (affineBlowUp.exists_mem_opensRange_chart_of_span_eq I s hs x).choose
  covers x := (affineBlowUp.exists_mem_opensRange_chart_of_span_eq I s hs x).choose_spec

/-- The charts of a generating set cover. -/
theorem affineBlowUp.iSup_opensRange_chart_of_span_eq :
    ⨆ y : s, (affineBlowUp.chart I ⟨y, hs ▸ Ideal.subset_span y.2⟩).opensRange = ⊤ :=
  eq_top_iff.mpr fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr
      (affineBlowUp.exists_mem_opensRange_chart_of_span_eq I s hs x)

end GeneratingSet

/-- The affine blow-up along `I = 0` is empty — the empty generating set gives the empty cover.
Blowing up the zero ideal gives the empty scheme [Sta, Tag 02OS]; the Rees algebra of the zero
ideal is `R` in degree zero alone [Hau14, Definition 4.6]. -/
theorem affineBlowUp.isEmpty_bot : IsEmpty (affineBlowUp (⊥ : Ideal R)) :=
  ⟨fun x => (affineBlowUp.exists_mem_opensRange_chart_of_span_eq (⊥ : Ideal R) ∅
    Ideal.span_empty x).choose.2.elim⟩

/-- **Over the base, the chart of `a` is `Spec` of `R → R[I/a]`** — Hauser's chart expression of
the blow-up map [Hau14, Theorem 4.19] — by `Proj.awayι_toSpecZero` and the constant-map
compatibility of the chart ring isomorphism (`reesAlgebra.chartRingEquiv_fromZeroRingHom`). -/
theorem affineBlowUp.chart_π (a : I) :
    affineBlowUp.chart I a ≫ affineBlowUp.π I =
      Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a))) := by
  unfold affineBlowUp.chart affineBlowUp.π
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    RingEquiv.toCommRingCatIso_hom, reesAlgebra.chartIso, RingEquiv.coe_toRingHom]
  exact reesAlgebra.chartRingEquiv_fromZeroRingHom a r

/-- The fraction `b/a`, `a, b ∈ I`, as an element of `R[I/a]`. -/
noncomputable def affineBlowUpAlgebra.ratio (a b : I) : affineBlowUpAlgebra I a :=
  ⟨awayFrac (a : R) 1 (b : R), awayFrac_mem_affineBlowUpAlgebra 1 (by simp)⟩

/-- Mathlib's localization element `bt/at` of `(R̃_{at})₀` corresponds to `b/a ∈ R[I/a]`. -/
theorem _root_.reesAlgebra.chartRingEquiv_isLocalizationElem (a b : I) :
    reesAlgebra.chartRingEquiv a
        (Away.isLocalizationElem (reesAlgebra.degreeOne_mem a) (reesAlgebra.degreeOne_mem b)) =
      affineBlowUpAlgebra.ratio I a b := by
  refine Subtype.ext ?_
  change (reesAlgebra.chartRingEquiv a (Away.mk _ (reesAlgebra.degreeOne_mem a) 1
    (reesAlgebra.degreeOne I b ^ 1) _) : Localization.Away (a : R)) = awayFrac (a : R) 1 (b : R)
  rw [reesAlgebra.coe_chartRingEquiv_mk]
  congr 1
  rw [pow_one, reesAlgebra.coe_degreeOne, coeff_monomial_same]

/-- **Chart overlaps**: inside the chart of `a`, the chart of `b` is the basic open
`D(b/a) ⊆ Spec R[I/a]` — the identity `D₊(f) ∩ D₊(g) = D₊(fg)` of `Proj` for `f = at`, `g = bt`;
this is how the charts are glued in [Hau14, Definition 4.13]. -/
theorem affineBlowUp.chart_preimage_chart (a b : I) :
    affineBlowUp.chart I a ⁻¹ᵁ (affineBlowUp.chart I b).opensRange =
      PrimeSpectrum.basicOpen (affineBlowUpAlgebra.ratio I a b) := by
  rw [affineBlowUp.opensRange_chart]
  unfold affineBlowUp.chart
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (reesAlgebra.degreeOne_mem a) one_pos
      (reesAlgebra.degreeOne_mem b) one_pos,
    SpecMap_preimage_basicOpen, ← reesAlgebra.chartRingEquiv_isLocalizationElem]
  rfl

end AlgebraicGeometry
