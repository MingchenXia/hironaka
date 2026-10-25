import DeJongAlterations.StableModification.Projectivity.RelativeCore
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The actual relative section map near a separating closed fibre

The pointwise argument takes place in the relative projective target. Thus properness of the
original family suffices; no properness of its coefficient-base structure map is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace DeJongAlterations.StableModificationBridge.RelativeSeparatingMap

open StableModification.Projectivity
open Geometry.ProjectiveIdeal

universe u

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- A genuine closed immersion covering the same original fibre may be used without changing
its coefficient field when the family is restricted to a base open. -/
theorem exists_open_quasiFiniteAt_of_closed_fibre
    (β : X ⟶ Y) [IsProper β] (p : Y ⟶ Spec (.of R))
    {N : ℕ} (h : X ⟶ projectiveSpace R N)
    (hh : h ≫ projectiveSpaceStructure R N = β ≫ p)
    (y : Y) {V : Scheme.{u}} [IsNoetherian V]
    (j : V ⟶ X) [IsClosedImmersion j] (hj : Set.range j = β ⁻¹' {y})
    (hdim : topologicalKrullDim V ≤ 1) (D : V.Opens) (a : Fin (N + 1))
    (hcoord : j ⁻¹ᵁ (h ⁻¹ᵁ nativeCoordinateOpen a) = D)
    (hgen : ∀ x : V, ¬ IsClosed ({x} : Set V) → x ∈ D)
    (hzero : ∀ x : V, ¬ IsClosed ({x} : Set V) → ∃ z, x ⤳ z ∧ z ∉ D) :
    ∃ O : Y.Opens, y ∈ O ∧ ∀ x, β x ∈ O →
      (pullback.lift β h hh.symm).QuasiFiniteAt x := by
  let Ψ := pullback.lift β h hh.symm
  have hΨβ : Ψ ≫ pullback.fst p (projectiveSpaceStructure R N) = β :=
    pullback.lift_fst _ _ _
  have hΨh : Ψ ≫ pullback.snd p (projectiveSpaceStructure R N) = h :=
    pullback.lift_snd _ _ _
  have : IsProper (Ψ ≫ pullback.fst p (projectiveSpaceStructure R N)) := by
    rw [hΨβ]
    infer_instance
  have : IsProper Ψ := IsProper.of_comp Ψ (pullback.fst _ _)
  have hdim' := StableModification.CurvesField.Ample.eq_or_eq_of_topologicalKrullDim_le_one hdim
  let P : Scheme.{u} := pullback p (projectiveSpaceStructure R N)
  let g : V → P :=
    fun w => Ψ (j w)
  have hg : Continuous g := Ψ.continuous.comp (j).continuous
  have hgcl : ∀ w, IsClosed ({w} : Set (V)) → IsClosed ({g w} : Set _) := by
    intro w hw
    have h1 := j.isClosedMap _ hw
    rw [Set.image_singleton] at h1
    have h2 := Ψ.isClosedMap _ h1
    rwa [Set.image_singleton] at h2
  have hmemD : ∀ w, w ∈ D ↔
      h (j w) ∈ nativeCoordinateOpen a := by
    intro w
    rw [← hcoord]
    rfl
  have hqf : ∀ x, β x = y → Ψ.QuasiFiniteAt x := by
    intro x hx
    apply quasiFiniteAt_of_finite Ψ x
    have hfin : (g ⁻¹' {Ψ x}).Finite :=
      finite_preimage_of_separating hdim' g hg hgcl (D : Set _)
        (fun w w' hww' => by
          change w ∈ D ↔ w' ∈ D
          rw [hmemD, hmemD]
          have he := congrArg (fun z => pullback.snd p (projectiveSpaceStructure R N) z) hww'
          change (Ψ ≫ pullback.snd p (projectiveSpaceStructure R N)) (j w) =
            (Ψ ≫ pullback.snd p (projectiveSpaceStructure R N)) (j w') at he
          rw [hΨh] at he
          rw [he]) hgen hzero (Ψ x)
    refine (hfin.image (j)).subset ?_
    intro x' hx'
    have he : Ψ x' = Ψ x := hx'
    have hβ : β x' = β x := by
      rw [← hΨβ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he]
    obtain ⟨w, rfl⟩ : x' ∈ Set.range (j) := by
      rw [hj]
      exact hβ.trans hx
    exact ⟨w, he, rfl⟩
  exact exists_open_quasiFiniteAt β Ψ y hqf

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual relative projective map is quasi-finite near a closed curve fibre if one of its
coordinate opens is the nonvanishing open of a genuine separating section of that fibre. -/
theorem exists_open_quasiFiniteAt_of_coordinate
    (β : X ⟶ Y) [IsProper β] (p : Y ⟶ Spec (.of R))
    {N : ℕ} (h : X ⟶ projectiveSpace R N)
    (hh : h ≫ projectiveSpaceStructure R N = β ≫ p)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1)
    {L : LineBundleData X} {m : ℤ}
    (s : (L.pullback (β.fiberι y)).Sections m ⊤) (a : Fin (N + 1))
    (hcoord : β.fiberι y ⁻¹ᵁ (h ⁻¹ᵁ nativeCoordinateOpen a) = s.nonvanishingLocus)
    (hgen : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    ∃ O : Y.Opens, y ∈ O ∧ ∀ x, β x ∈ O →
      (pullback.lift β h hh.symm).QuasiFiniteAt x := by
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  let : IsClosedImmersion (β.fiberι y) := by
    change IsClosedImmersion (pullback.fst β (Y.fromSpecResidueField y))
    infer_instance
  let : IsNoetherian (β.fiber y) := isNoetherian_fiber y
  exact exists_open_quasiFiniteAt_of_closed_fibre β p h hh y (β.fiberι y)
    (Scheme.Hom.range_fiberι β y) hdim s.nonvanishingLocus a hcoord hgen hzero

/-- An actual proper relative map that is quasi-finite over a base open is finite on the
corresponding original target open. The entire morphism is restricted, not reconstructed. -/
theorem isFinite_restrict_of_quasiFiniteAt
    {P : Scheme.{u}} (β : X ⟶ Y) [IsProper β] (f : X ⟶ P)
    (π : P ⟶ Y) [IsSeparated π] (e : f ≫ π = β) (O : Y.Opens)
    (hqf : ∀ x, β x ∈ O → f.QuasiFiniteAt x) : IsFinite (f ∣_ (π ⁻¹ᵁ O)) := by
  have : IsProper (f ≫ π) := by rw [e]; infer_instance
  have : IsProper f := IsProper.of_comp f π
  let V := π ⁻¹ᵁ O
  have hall : ∀ x : (f ⁻¹ᵁ V).toScheme, (f ∣_ V).QuasiFiniteAt x := by
    intro x
    have hx : β ((f ⁻¹ᵁ V).ι x) ∈ O := by
      have hx' : (f ≫ π) ((f ⁻¹ᵁ V).ι x) ∈ O := x.2
      rwa [e] at hx'
    have hc : ((f ⁻¹ᵁ V).ι ≫ f).QuasiFiniteAt x :=
      Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr (hqf _ hx)
    have hc' : (f ∣_ V ≫ V.ι).QuasiFiniteAt x := by
      rwa [morphismRestrict_ι]
    exact quasiFiniteAt_of_comp hc'
  have : LocallyQuasiFinite (f ∣_ V) :=
    (Scheme.Hom.quasiFiniteLocus_eq_top_iff _).mp (top_unique fun x _ => hall x)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (f ∣_ V)

end DeJongAlterations.StableModificationBridge.RelativeSeparatingMap
