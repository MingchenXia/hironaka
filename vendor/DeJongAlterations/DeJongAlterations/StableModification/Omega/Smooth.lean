import DeJongAlterations.StableModification.Omega.Dualizing
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# `Ω¹_{X/S}` and `ω_{X/S}` at smooth points of relative dimension one

The smooth case of `lem:sm-omega-invertible` (M. Temkin, *Stable modification of relative
curves*, §1.2, T:1691–1712; PLAN-SM-GEOM chapter M): if `f : X ⟶ S` is smooth of relative
dimension one near `x`, then `Ω¹_{X/S}` is invertible near `x`; if moreover `x` lies in the smooth
locus (automatic), so is `ω_{X/S}`, since `ω_{X/S} = Ω¹_{X/S}` on the smooth locus.

* `restrict_iso_unit_of_linearEquiv`: if `Ω_{Γ(X,W)/Γ(S,V)} ≅ Γ(X, W)`, then the restriction of
  `Ω¹_{X/S}` to `Spec Γ(X, W)` is `𝒪` (from `restrictIso` and `tildeSelf`).
* `kaehler_linearEquiv_of_isStandardSmoothOfRelativeDimension_one`: for a standard smooth
  algebra of relative dimension one, `Ω` is free of rank one (Mathlib's
  `SubmersivePresentation.basisKaehler`).
* `isInvertibleModule_relativeDifferentials` (`SmoothOfRelativeDimension 1 f`).
* `restrictDualizingSheafIso`: on affine opens inside the smooth locus, `ω_{X/S}` and
  `Ω¹_{X/S}` have isomorphic restrictions; `isInvertibleAt_dualizingSheaf`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- An `𝒪_Y`-module is *invertible at* `y` if `y` has an affine open neighbourhood `W` such that
the restriction of the module to `Spec Γ(Y, W)` is isomorphic to the structure sheaf. -/
def IsInvertibleAt {Y : Scheme.{u}} (M : Y.Modules) (y : Y) : Prop :=
  ∃ (W : Y.Opens) (hW : IsAffineOpen W), y ∈ W ∧
    Nonempty (M.restrict hW.fromSpec ≅ SheafOfModules.unit _)

theorem isInvertibleModule_iff {Y : Scheme.{u}} (M : Y.Modules) :
    IsInvertibleModule M ↔ ∀ y, IsInvertibleAt M y :=
  Iff.rfl

/-- Sections over an open containing a point form a nontrivial ring. -/
theorem nontrivial_sections_of_mem {Y : Scheme.{u}} {W : Y.Opens} {y : Y} (hy : y ∈ W) :
    Nontrivial Γ(Y, W) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h0 : Y.basicOpen (1 : Γ(Y, W)) = ⊥ := by
    rw [Subsingleton.elim (1 : Γ(Y, W)) 0, Y.basicOpen_zero]
  rw [Y.basicOpen_of_isUnit isUnit_one] at h0
  rw [h0] at hy
  exact hy

/-- If `Ω_{Γ(X,W)/Γ(S,V)}` is free of rank one, `Ω¹_{X/S}` is trivial on `Spec Γ(X, W)`. -/
theorem restrict_iso_unit_of_linearEquiv {W : X.Opens} (hW : IsAffineOpen W) {V : S.Opens}
    (hV : IsAffineOpen V) (hWV : W ≤ f ⁻¹ᵁ V)
    (e : CommRingCat.KaehlerDifferential (f.appLE V W hWV) ≃ₗ[Γ(X, W)] Γ(X, W)) :
    Nonempty ((relativeDifferentials f).restrict hW.fromSpec ≅ SheafOfModules.unit _) :=
  ⟨restrictIso f hW hV hWV ≪≫ (tilde.functor _).mapIso
    (e.toModuleIso (X₁ := CommRingCat.KaehlerDifferential (f.appLE V W hWV))
      (X₂ := ModuleCat.of Γ(X, W) Γ(X, W))) ≪≫ tildeSelf⟩

/-- For a standard smooth algebra of relative dimension one, the Kähler differentials are free of
rank one. -/
theorem kaehler_linearEquiv_of_isStandardSmoothOfRelativeDimension_one {R A : CommRingCat.{u}}
    (φ : R ⟶ A) [Nontrivial A] (h : φ.hom.IsStandardSmoothOfRelativeDimension 1) :
    Nonempty (CommRingCat.KaehlerDifferential φ ≃ₗ[A] A) := by
  let := φ.hom.toAlgebra
  have h' : Algebra.IsStandardSmoothOfRelativeDimension 1 R A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := h'.out
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  let b := P.basisKaehler
  have hcard : Fintype.card ((Set.range P.map)ᶜ : Set ι) = 1 := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simpa [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
  let : Unique ((Set.range P.map)ᶜ : Set ι) := { default := i, uniq := hi }
  exact ⟨b.equivFun.trans (LinearEquiv.funUnique _ A A)⟩

/-- **Smooth case of `lem:sm-omega-invertible`.** If `f` is smooth of relative dimension one,
then `Ω¹_{X/S}` is invertible. -/
theorem isInvertibleModule_relativeDifferentials [SmoothOfRelativeDimension 1 f] :
    IsInvertibleModule (relativeDifferentials f) := by
  intro x
  obtain ⟨V, hV, W, hW, hx, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have : Nontrivial Γ(X, W) := nontrivial_sections_of_mem hx
  obtain ⟨eΩ⟩ := kaehler_linearEquiv_of_isStandardSmoothOfRelativeDimension_one _ h
  exact ⟨W, hW, hx, restrict_iso_unit_of_linearEquiv f hW hV e eΩ⟩

section Dualizing

variable [LocallyOfFinitePresentation f]

/-- On an affine open contained in the smooth locus, `ω_{X/S}` and `Ω¹_{X/S}` have isomorphic
restrictions. -/
def restrictDualizingSheafIso {W : X.Opens} (hW : IsAffineOpen W) (hWU : W ≤ f.smoothLocus) :
    (dualizingSheaf f).restrict hW.fromSpec ≅ (relativeDifferentials f).restrict hW.fromSpec :=
  have hrange : Set.range hW.fromSpec ⊆ Set.range f.smoothLocus.ι := by
    rw [hW.range_fromSpec, Scheme.Opens.range_ι]
    exact hWU
  let g := IsOpenImmersion.lift f.smoothLocus.ι hW.fromSpec hrange
  have hg : g ≫ f.smoothLocus.ι = hW.fromSpec := IsOpenImmersion.lift_fac _ _ _
  (Scheme.Modules.restrictFunctorCongr hg.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp g f.smoothLocus.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor g).mapIso (dualizingSheafRestrictIso f) ≪≫
    ((Scheme.Modules.restrictFunctorComp g f.smoothLocus.ι).app _).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hg).app _

/-- **Smooth part of `lem:sm-omega-invertible` for `ω`.** At a point of the smooth locus where
`f` is smooth of relative dimension one, `ω_{X/S}` is invertible. -/
theorem isInvertibleAt_dualizingSheaf {x : X} {V : S.Opens} (hV : IsAffineOpen V)
    {W : X.Opens} (hW : IsAffineOpen W) (hx : x ∈ W) (hWU : W ≤ f.smoothLocus)
    (hWV : W ≤ f ⁻¹ᵁ V) (h : (f.appLE V W hWV).hom.IsStandardSmoothOfRelativeDimension 1) :
    IsInvertibleAt (dualizingSheaf f) x := by
  have : Nontrivial Γ(X, W) := nontrivial_sections_of_mem hx
  obtain ⟨eΩ⟩ := kaehler_linearEquiv_of_isStandardSmoothOfRelativeDimension_one _ h
  obtain ⟨e⟩ := restrict_iso_unit_of_linearEquiv f hW hV hWV eΩ
  exact ⟨W, hW, hx, ⟨restrictDualizingSheafIso f hW hWU ≪≫ e⟩⟩

/-- If `f` is smooth of relative dimension one, `ω_{X/S}` is invertible. -/
theorem isInvertibleModule_dualizingSheaf [SmoothOfRelativeDimension 1 f] :
    IsInvertibleModule (dualizingSheaf f) := by
  intro x
  obtain ⟨V, hV, W, hW, hx, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact isInvertibleAt_dualizingSheaf f hV hW hx (by rw [f.smoothLocus_eq_top]; exact le_top) e h

end Dualizing

end DeJongAlterations.StableModification.Omega
