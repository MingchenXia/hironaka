/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeCore
import DeJongAlterations.StableModification.Projectivity.RelativeCover
import DeJongAlterations.StableModification.Projectivity.RelativeCoverFinite

/-!
# The local-to-global theorem (`thm:sm-ltg`)

Blueprint `sm-projectivity-relative.tex`, `thm:sm-ltg` (PLAN-OM3 §3; M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), Theorem 1.1, `semi-stable.tex`
T:1713–1749: "relative ampleness can be checked separately on each fiber").

Let `Y` be projective over a ring `R` and `β : X ⟶ Y` locally relatively projective (OM3A's
`LocallyRelativelyProjective`). Suppose that over every closed point `y ∈ Y` (with infinite residue
field) the fibre `X_y` has dimension at most one and some power `𝓛^n|_{X_y}`, `n > 0`, of a line
bundle `𝓛` on `X` has a section which does not vanish at the non-closed points of `X_y` and
vanishes at a specialization of each of them (positive degree on every one-dimensional component).
Then `β` is projective relative to `Y ⟶ Spec R`, in two cases:

* (`isRelativelyProjective_of_fiberSections`) `R` Noetherian;
* (`isRelativelyProjective_of_fiberSections_valuation`) `R = V` a valuation ring, `Y` locally of
  finite presentation over `V` and `X` flat over `V`.

The forms with one global section (`..._of_section`) are the ones for the canonical section of
an effective Cartier divisor such as `𝒪(Σ P̄ᵢ)` (`Valuation.lean`).

Fibre-ampleness (OM3A's Serre-form `FiberAmple`) is derived from the sections by OM3B's
`CurvesField.fiberAmple_of_positive`; the two-affine covers around the closed fibres come from
`exists_twoAffines` and the finiteness of the two-term complexes from
`finite_coker_of_noetherian` / `finite_coker_of_valuationRing`; the rest is
`isRelativelyProjective_of_twoAffineCovers`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

open DeJong Cohomology

variable {X Y : Scheme.{u}}

/-! ### Two-affine data in the two cases -/

section TwoAffine

variable {R : Type u} [CommRing R] (pY : Y ⟶ Spec (.of R)) {β : X ⟶ Y} [IsProper β]
  (hloc : LocallyRelativelyProjective pY β) (L : LineBundleData X)

include hloc in
/-- **Two-affine data, Noetherian case** (blueprint `lem:sm-ltg-two-affines`). -/
theorem exists_twoAffineCover_of_noetherian [IsLocallyNoetherian Y] {y : Y}
    (hy : IsClosed ({y} : Set Y)) [Infinite (Y.residueField y)]
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1) : ∃ D : TwoAffineCover β L, y ∈ D.W := by
  obtain ⟨J, _, W', hW'cov, hW'⟩ := hloc
  obtain ⟨j, hj⟩ : ∃ j, y ∈ W' j := Opens.mem_iSup.mp (by rw [hW'cov]; trivial)
  obtain ⟨W, hW, hyW, hle, U₀, U₁, h₀, h₁, h₀₁, hcov⟩ :=
    exists_twoAffines pY β (hW' j) hj hy hdim
  have hp := isProjectiveOver_morphismRestrict_of_le pY β (hW' j) hW hle
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  exact ⟨⟨W, hW, U₀, U₁, h₀, h₁, h₀₁, hcov,
    fun m => finite_coker_of_noetherian L h₀ h₁ h₀₁ hcov hp m⟩, hyW⟩

include hloc in
/-- **Two-affine data, valuation case** (blueprint `lem:sm-ltg-two-affines`). -/
theorem exists_twoAffineCover_of_valuationRing (V : Type u) [CommRing V] [IsDomain V]
    [ValuationRing V] (pV : Y ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation pV]
    [Flat (β ≫ pV)] {y : Y} (hy : IsClosed ({y} : Set Y)) [Infinite (Y.residueField y)]
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1) : ∃ D : TwoAffineCover β L, y ∈ D.W := by
  obtain ⟨J, _, W', hW'cov, hW'⟩ := hloc
  obtain ⟨j, hj⟩ : ∃ j, y ∈ W' j := Opens.mem_iSup.mp (by rw [hW'cov]; trivial)
  obtain ⟨W, hW, hyW, hle, U₀, U₁, h₀, h₁, h₀₁, hcov⟩ :=
    exists_twoAffines pY β (hW' j) hj hy hdim
  have hp := isProjectiveOver_morphismRestrict_of_le pY β (hW' j) hW hle
  exact ⟨⟨W, hW, U₀, U₁, h₀, h₁, h₀₁, hcov,
    fun m => finite_coker_of_valuationRing L h₀ h₁ h₀₁ hcov V pV hW hp m⟩, hyW⟩

end TwoAffine

/-! ### The local-to-global theorem -/

section Main

variable {R : Type u} [CommRing R]

/-- The section hypothesis of the local-to-global theorem at a point `y`: some power `𝓛^n`,
`n > 0`, restricted to the fibre `X_y` has a section which does not vanish at the non-closed points
of `X_y` and vanishes at a specialization of each of them. -/
def HasFiberSection (β : X ⟶ Y) (L : LineBundleData X) (y : Y) : Prop :=
  ∃ (n : ℕ) (s : (L.pullback (β.fiberι y)).Sections n ⊤), 0 < n ∧
    (∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) → x ∈ s.nonvanishingLocus) ∧
    (∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus)

/-- Fibre-ampleness from the section hypothesis (OM3B's `CurvesField.fiberAmple_of_positive`). -/
theorem fiberAmple_of_hasFiberSection {k : Type u} [CommRing k] {pY : Y ⟶ Spec (.of k)}
    {β : X ⟶ Y} (hloc : LocallyRelativelyProjective pY β) (L : LineBundleData X) (y : Y)
    [Infinite (Y.residueField y)] (hdim : topologicalKrullDim (β.fiber y) ≤ 1)
    (h : HasFiberSection β L y) : FiberAmple L β y := by
  obtain ⟨n, s, hn, hgen, hzero⟩ := h
  exact CurvesField.fiberAmple_of_positive L β y
    (CurvesField.isProjectiveOver_fiber_of_locallyRelativelyProjective hloc y) hdim hn s hgen hzero

/-- **The local-to-global theorem, Noetherian case** (blueprint `thm:sm-ltg`). -/
theorem isRelativelyProjective_of_fiberSections [IsNoetherianRing R] (pY : Y ⟶ Spec (.of R))
    (hY : IsProjectiveOver pY) (β : X ⟶ Y) (L : LineBundleData X)
    (hloc : LocallyRelativelyProjective pY β)
    (hdim : ∀ y : Y, IsClosed ({y} : Set Y) → topologicalKrullDim (β.fiber y) ≤ 1)
    (hinf : ∀ y : Y, IsClosed ({y} : Set Y) → Infinite (Y.residueField y))
    (hsec : ∀ y : Y, IsClosed ({y} : Set Y) → HasFiberSection β L y) :
    IsRelativelyProjective pY β := by
  have : IsProper β := hloc.isProper
  have : IsProper pY := hY.isProper
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  refine isRelativelyProjective_of_twoAffineCovers pY hY (fun y hy => ?_) hdim
    (fun y hy => ?_) hsec
  · have := hinf y hy
    exact exists_twoAffineCover_of_noetherian pY hloc L hy (hdim y hy)
  · have := hinf y hy
    exact fiberAmple_of_hasFiberSection hloc L y (hdim y hy) (hsec y hy)

/-- **The local-to-global theorem, valuation case** (blueprint `thm:sm-ltg`): over a valuation
ring `V`, for `Y` projective and locally of finite presentation over `V` and `X` flat over `V`. -/
theorem isRelativelyProjective_of_fiberSections_valuation (V : Type u) [CommRing V] [IsDomain V]
    [ValuationRing V] (pY : Y ⟶ Spec (.of V)) (hY : IsProjectiveOver pY)
    [LocallyOfFinitePresentation pY] (β : X ⟶ Y) [Flat (β ≫ pY)] (L : LineBundleData X)
    (hloc : LocallyRelativelyProjective pY β)
    (hdim : ∀ y : Y, IsClosed ({y} : Set Y) → topologicalKrullDim (β.fiber y) ≤ 1)
    (hinf : ∀ y : Y, IsClosed ({y} : Set Y) → Infinite (Y.residueField y))
    (hsec : ∀ y : Y, IsClosed ({y} : Set Y) → HasFiberSection β L y) :
    IsRelativelyProjective pY β := by
  have : IsProper β := hloc.isProper
  refine isRelativelyProjective_of_twoAffineCovers pY hY (fun y hy => ?_) hdim
    (fun y hy => ?_) hsec
  · have := hinf y hy
    exact exists_twoAffineCover_of_valuationRing pY hloc L V pY hy (hdim y hy)
  · have := hinf y hy
    exact fiberAmple_of_hasFiberSection hloc L y (hdim y hy) (hsec y hy)

/-- The section hypothesis from a global section (e.g. the canonical section of an effective
Cartier divisor). -/
theorem hasFiberSection_of_section {β : X ⟶ Y} {L : LineBundleData X} {y : Y} {n : ℕ}
    (hn : 0 < n) (σ : L.Sections n ⊤)
    (hgen : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      β.fiberι y x ∈ σ.nonvanishingLocus)
    (hzero : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      ∃ z, x ⤳ z ∧ β.fiberι y z ∉ σ.nonvanishingLocus) : HasFiberSection β L y := by
  let s' : (L.pullback (β.fiberι y)).Sections n ⊤ :=
    (σ.pullback (β.fiberι y)).restrict (le_of_eq (Scheme.Hom.preimage_top _).symm)
  have hs' : ∀ x, x ∈ s'.nonvanishingLocus ↔ β.fiberι y x ∈ σ.nonvanishingLocus := by
    intro x
    rw [LineBundleData.Sections.nonvanishingLocus_restrict,
      LineBundleData.Sections.nonvanishingLocus_pullback]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  refine ⟨n, s', hn, fun x hx => (hs' x).mpr (hgen x hx), fun x hx => ?_⟩
  obtain ⟨z, hxz, hz⟩ := hzero x hx
  exact ⟨z, hxz, fun h => hz ((hs' z).mp h)⟩

end Main

end

end DeJongAlterations.StableModification.Projectivity
