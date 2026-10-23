/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechRefinement
import DeJongAlterations.StableModification.Cohomology.CechLongExact
import Mathlib.Topology.Sets.OpenCover

/-!
# Cohomology of quasi-coherent modules through finite affine covers

A `FiniteAffineCover X` is a finite family of opens, indexed by a finite linearly ordered type,
covering `X`, all of whose nonempty finite intersections are affine. On a quasi-compact scheme with
affine diagonal (for instance a quasi-compact separated scheme) such covers exist
(`FiniteAffineCover.nonempty`), and we define the cohomology `cohomology F c p = H^p(X, F)` of a
module `F` as the Čech cohomology of a chosen one. For quasi-coherent `F` every finite affine cover
computes it (`cohomologyIsoCech`), naturally in `F`; `H⁰ = Γ`, `H^p` vanishes on affines and
above the number of opens of a finite affine cover, and short exact sequences of quasi-coherent
modules give long exact sequences (`cohomologyδ`, `cohomology_exact₁/₂/₃`). Blueprint:
`sm-cohomology-cech.tex`, `def:sm-cech-cohomology`.

This is the cover-free entry point for the later cohomology lanes (finiteness of `H^i` for proper
curves, the Mumford complex, cohomology of curves over fields): state results for `cohomology`, and
compute with a convenient cover through `cohomologyIsoCech`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

variable {X : Scheme.{u}}

/-- A finite cover of `X` by opens all of whose nonempty finite intersections are affine, indexed by
a finite linearly ordered type. -/
structure FiniteAffineCover (X : Scheme.{u}) where
  /-- The index type. -/
  ι : Type u
  [linearOrder : LinearOrder ι]
  [finite : Finite ι]
  /-- The opens. -/
  U : ι → X.Opens
  iSup_eq_top : ⨆ i, U i = ⊤
  isAffineOpen_inf : ∀ T : Finset ι, T.Nonempty → IsAffineOpen (T.inf U)

attribute [instance] FiniteAffineCover.linearOrder FiniteAffineCover.finite

namespace FiniteAffineCover

lemma isAffineOpen (𝒰 : FiniteAffineCover X) (i : 𝒰.ι) : IsAffineOpen (𝒰.U i) := by
  simpa using 𝒰.isAffineOpen_inf {i} (Finset.singleton_nonempty i)

variable (X) [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]

/-- On a quasi-compact scheme with affine diagonal, finite affine covers exist (the extraction of
a finite affine subcover follows Codex's `ProperSteinProjectiveCech.finiteAffineFinCover_exists`). -/
theorem nonempty : Nonempty (FiniteAffineCover X) := by
  classical
  have hU : IsOpenCover (fun U : X.affineOpens => U.val) := by
    rw [IsOpenCover, iSup_affineOpens_eq_top]
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let U : ULift.{u} (Fin (Fintype.card s)) → X.Opens := fun i => (e.symm i.down).val.val
  have haff : ∀ i, IsAffineOpen (U i) := fun i => (e.symm i.down).val.property
  refine ⟨@FiniteAffineCover.mk X (ULift.{u} (Fin (Fintype.card s))) inferInstance inferInstance
    U ?_ (fun T hT => ?_)⟩
  · apply top_unique
    intro x _
    have hx : x ∈ ⨆ i : s, i.val.val := by
      change IsOpenCover (fun i : s => i.val.val) at hs
      change (⨆ i : s, i.val.val) = ⊤ at hs
      rw [hs]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨e i⟩, by simpa [U] using hi⟩
  · simpa [Finset.inf_eq_iInf] using
      IsAffineOpen.biInf (T : Set (ULift.{u} (Fin (Fintype.card s)))) T.finite_toSet
        (Finset.coe_nonempty.mpr hT) (fun i _ => haff i)

/-- A chosen finite affine cover. -/
def choose : FiniteAffineCover X := Classical.choice (nonempty X)

end FiniteAffineCover

variable [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  {R : Type u} [CommRing R]

/-- The cohomology `H^p(X, F)` of a module on a quasi-compact scheme with affine diagonal, as an
`R`-module through `c : R →+* Γ(X, ⊤)`: the Čech cohomology of a chosen finite affine cover
(blueprint `def:sm-cech-cohomology`). -/
abbrev cohomology (F : X.Modules) (c : R →+* Γ(X, ⊤)) (p : ℕ) : ModuleCat.{u} R :=
  cechCohomology F (FiniteAffineCover.choose X).U c p

/-- Functoriality of `H^p(X, -)`. -/
def cohomologyMap {F G : X.Modules} (c : R →+* Γ(X, ⊤)) (φ : F ⟶ G) (p : ℕ) :
    cohomology F c p ⟶ cohomology G c p :=
  HomologicalComplex.homologyMap (cechComplexMap (FiniteAffineCover.choose X).U c φ) p

variable (F : X.Modules) [F.IsQuasicoherent] (c : R →+* Γ(X, ⊤))

/-- Every finite affine cover computes `H^p(X, F)` for quasi-coherent `F`. -/
def cohomologyIsoCech (𝒰 : FiniteAffineCover X) (p : ℕ) :
    cohomology F c p ≅ cechCohomology F 𝒰.U c p :=
  cechCohomologyIsoOfAffineCovers F c (FiniteAffineCover.choose X).iSup_eq_top 𝒰.iSup_eq_top
    (FiniteAffineCover.choose X).isAffineOpen 𝒰.isAffineOpen p

/-- The identification `cohomologyIsoCech` is natural in the quasi-coherent module. -/
lemma cohomologyIsoCech_hom_naturality {G : X.Modules} [G.IsQuasicoherent] (φ : F ⟶ G)
    (𝒰 : FiniteAffineCover X) (p : ℕ) :
    cohomologyMap c φ p ≫ (cohomologyIsoCech G c 𝒰 p).hom =
      (cohomologyIsoCech F c 𝒰 p).hom ≫
        HomologicalComplex.homologyMap (cechComplexMap 𝒰.U c φ) p :=
  cechCohomologyIsoOfCovers_hom_naturality F c φ (FiniteAffineCover.choose X).iSup_eq_top
    𝒰.iSup_eq_top (isAffineOpen_inf_sumLexFamily (FiniteAffineCover.choose X).isAffineOpen
      𝒰.isAffineOpen) p

omit [F.IsQuasicoherent] in
/-- `H⁰(X, F) = Γ(X, F)`. -/
def cohomologyZeroIso : sectionsModuleCat F c ⊤ le_top ≅ cohomology F c 0 :=
  cechCohomologyZeroIso F c (FiniteAffineCover.choose X).iSup_eq_top

/-- `H^p(X, F) = 0` for `p > 0` on an affine scheme. -/
theorem isZero_cohomology_of_isAffine [IsAffine X] (p : ℕ) :
    Limits.IsZero (cohomology F c (p + 1)) :=
  isZero_cechCohomology_of_isAffine F (FiniteAffineCover.choose X).U
    (FiniteAffineCover.choose X).iSup_eq_top (FiniteAffineCover.choose X).isAffineOpen_inf c p

/-- `H^p(X, F) = 0` for `p` at least the number of opens of some finite affine cover. -/
theorem isZero_cohomology_of_card_le (𝒰 : FiniteAffineCover X) [Fintype 𝒰.ι] (p : ℕ)
    (hp : Fintype.card 𝒰.ι ≤ p) : Limits.IsZero (cohomology F c p) :=
  (isZero_cechCohomology_of_card_le F 𝒰.U c p hp).of_iso (cohomologyIsoCech F c 𝒰 p)

section LongExact

omit [F.IsQuasicoherent]

variable (S : ShortComplex X.Modules) (hS : S.ShortExact) [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]
include hS

/-- The connecting map `H^p(X, F₃) → H^{p+1}(X, F₁)` of a short exact sequence. -/
def cohomologyδ (p : ℕ) : cohomology S.X₃ c p ⟶ cohomology S.X₁ c (p + 1) :=
  cechδ (FiniteAffineCover.choose X).U c S hS (FiniteAffineCover.choose X).isAffineOpen_inf p

/-- Exactness of `H^p(F₁) → H^p(F₂) → H^p(F₃)`. -/
theorem cohomology_exact₂ (p : ℕ) :
    (ShortComplex.mk (cohomologyMap c S.f p) (cohomologyMap c S.g p)
      (by rw [cohomologyMap, cohomologyMap, ← HomologicalComplex.homologyMap_comp,
        ← cechComplexMap_comp, S.zero, cechComplexMap_zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  cechCohomology_exact₂ _ c S hS (FiniteAffineCover.choose X).isAffineOpen_inf p

/-- Exactness of `H^p(F₂) → H^p(F₃) → H^{p+1}(F₁)`. -/
theorem cohomology_exact₃ (p : ℕ) :
    (ShortComplex.mk (cohomologyMap c S.g p) (cohomologyδ c S hS p)
      ((cechShortComplex_shortExact _ c S hS
        (FiniteAffineCover.choose X).isAffineOpen_inf).comp_δ p (p + 1) (by simp))).Exact :=
  cechCohomology_exact₃ _ c S hS (FiniteAffineCover.choose X).isAffineOpen_inf p

/-- Exactness of `H^p(F₃) → H^{p+1}(F₁) → H^{p+1}(F₂)`. -/
theorem cohomology_exact₁ (p : ℕ) :
    (ShortComplex.mk (cohomologyδ c S hS p) (cohomologyMap c S.f (p + 1))
      ((cechShortComplex_shortExact _ c S hS
        (FiniteAffineCover.choose X).isAffineOpen_inf).δ_comp p (p + 1) (by simp))).Exact :=
  cechCohomology_exact₁ _ c S hS (FiniteAffineCover.choose X).isAffineOpen_inf p

end LongExact

end

end DeJongAlterations.StableModification.Cohomology
