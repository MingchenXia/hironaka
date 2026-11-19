import Hironaka.Analytic.AnalyticComplementConnected
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.ExceptionalFibres

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Connectedness of a blowup

Source: Griffiths--Harris, Ch. 1 §4 (the blowup of a manifold along a smooth centre and its
fibres); Voisin I, §3.3.  Used by CT22, Lemma 4.4 / Copy-4 `lem:resolution`, where the
modification `μ : X̃ → X` is required to be a *connected* compact Kähler manifold.

The classical proof describes the fibres of `π` (points off `C`, projectivised normal spaces
over `C`) and applies the fact that a closed surjection with connected fibres over a connected
base has connected total space.  The workspace characterises the blowup by its universal
property only (`Hironaka.BlowupSequences.IsBlowupAlong`) and has no description of the
exceptional fibres, so the argument used here avoids them entirely:

* `C` is a proper closed analytic subset of `M`, so `M \ C` is connected
  (`Hironaka.AnalyticComplementConnected.isPreconnected_compl`; a connected complex manifold is
  irreducible and an analytic set has real codimension at least two);
* the holomorphic section of `Hironaka.BlowupIsomorphismOff.exists_section_compl` has range
  exactly `π⁻¹(M \ C)`, which is therefore connected;
* `π⁻¹ C` has empty interior (`Hironaka.ExceptionalFibres.interior_preimage_eq_empty`), so
  `π⁻¹(M \ C)` is dense and its closure `Z` is connected.

Everything in this file is proved.
-/

open Set

universe u

namespace Hironaka.BlowupConnected

open Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **The blowup of a connected complex manifold along a nowhere dense closed submanifold is
connected.**

Proof.  `C` is a proper closed analytic subset, so `M \ C` is connected
(`AnalyticComplementConnected.isPreconnected_compl`).  The holomorphic section
`s : M \ C → Z` of `Hironaka.BlowupIsomorphismOff.exists_section_compl` has range exactly
`π⁻¹(M \ C)`, so that preimage is the continuous image of a connected set, hence connected;
and it is dense in `Z` because `π⁻¹ C` has empty interior
(`Hironaka.ExceptionalFibres.interior_preimage_eq_empty`).  A dense connected subset has
connected closure, which is all of `Z`.  No description of the exceptional fibres is needed. -/
theorem connectedSpace_of_isBlowupAlong [ConnectedSpace M] {C : Set M} {π : Z → M}
    (hπ : IsBlowupAlong n C π) : ConnectedSpace Z := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hCanal : IsComplexAnalyticSubset (n := n) C :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  have hCne : C ≠ Set.univ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty M)
    have hx : x ∈ interior C := by rw [h]; simp
    rw [hπ.2.1] at hx
    exact hx
  have hconn : IsPreconnected (Cᶜ : Set M) :=
    AnalyticComplementConnected.isPreconnected_compl hCanal hCne
  have hNpre : PreconnectedSpace
      (↥(⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M)) :=
    Subtype.preconnectedSpace hconn
  have himg : π ⁻¹' Cᶜ = Set.range s := by
    ext z
    refine ⟨fun hz => ⟨⟨π z, hz⟩, hsec z hz⟩, ?_⟩
    rintro ⟨x, rfl⟩
    show π (s x) ∈ Cᶜ
    rw [show π (s x) = (x : M) from congrFun hsπ x]
    exact x.2
  have hrange : IsPreconnected (π ⁻¹' Cᶜ) := by
    rw [himg, ← Set.image_univ]
    exact isPreconnected_univ.image s hs.continuous.continuousOn
  have hdense : closure (π ⁻¹' Cᶜ) = Set.univ := by
    rw [Set.preimage_compl]
    exact (interior_eq_empty_iff_dense_compl.mp
      (ExceptionalFibres.interior_preimage_eq_empty hπ)).closure_eq
  have hne : Nonempty Z := by
    obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hCne
    exact ⟨s ⟨x, hx⟩⟩
  have hpre : PreconnectedSpace Z :=
    preconnectedSpace_iff_univ.mpr (hdense ▸ hrange.closure)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

/-- A modification of a connected complex manifold is connected.  Proved from the one-blowup
statement by induction over `IsBlowupSequence`. -/
theorem connectedSpace_of_isBlowupSequence {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [ConnectedSpace X]
    {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt]
    [IsComplexManifold n Xt] (μ : Xt → X) (hμ : IsBlowupSequence n X Xt μ) :
    ConnectedSpace Xt := by
  induction hμ with
  | refl => infer_instance
  | step f C g _hf hg ih =>
      have := ih
      exact connectedSpace_of_isBlowupAlong hg

end

end Hironaka.BlowupConnected
