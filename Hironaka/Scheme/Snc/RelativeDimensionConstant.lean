/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
import Hironaka.Algebra.RegularSmooth.Dimension
import Hironaka.Scheme.Snc.RelativeDimension

/-!
# A smooth scheme with preconnected underlying space has one relative dimension

[Kol07, Notation 64 (1)] asks the ambient scheme to be smooth of one relative dimension; the smooth
locus `X^{ns}` of an integral scheme is irreducible, hence preconnected, and so is smooth of a
single relative dimension `d` — the codimension `n − d` of `X^{ns}` in a smooth ambient of relative
dimension `n` is then the same at every closed point, which is what the étale equivalence of two
smooth points of `X` in the proof of [Kol07, Theorem 27] ("any two smooth points of `X` are étale
equivalent", [Kol07, 4.2]) needs. `Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus` and
`Hironaka.Resolution.Algebraic.Hir64.SingleCenter` use it to speak of the relative dimension of the
smooth locus.

* `ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension`: on an affine open `V` whose
  section ring is standard smooth of relative dimension `m` over `k`, every point `x ∈ V` has
  `dim 𝒪_{X,x} + trdeg_k κ(x) = m` (the body of
  `Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension`, with the chart
  given instead of chosen).
* `isLocallyConstant_dimCount`: for `f` smooth, `x ↦ dim 𝒪_{X,x} + trdeg_k κ(x)` is locally constant
  — each point has a standard smooth affine chart, of some relative dimension
  (`exists_affineOpen_isStandardSmoothOfRelativeDimension'`).
* `exists_smoothOfRelativeDimension_of_preconnectedSpace`: a smooth `f : X ⟶ Spec k` with `X`
  preconnected and nonempty is smooth of one relative dimension (a locally constant function on a
  preconnected space is constant; `smoothOfRelativeDimension_of_forall_exists_affineOpen`).

Sources: [Kol07, Notation 64; Theorem 27; 4.2]; [Sta, Tag 0A21].
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- On an affine open `V` whose section ring is standard smooth of relative dimension `m` over `k`
through `f`, every point `x ∈ V` satisfies `dim 𝒪_{X,x} + trdeg_k κ(x) = m` ([Sta, Tag 0A21]; the
body of `Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension` with the
chart given). -/
theorem ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension [PerfectField k]
    (f : X ⟶ Spec (.of k)) (m : ℕ) {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hxV : x ∈ V)
    (hstd : letI := f.sectionsAlgebra V
      Algebra.IsStandardSmoothOfRelativeDimension m k Γ(X, V)) :
    letI := f.stalkAlgebra x
    ringKrullDim (X.presheaf.stalk x) +
      ((Cardinal.toENat (Algebra.trdeg k (ResidueField (X.presheaf.stalk x))) : ℕ∞) :
        WithBot ℕ∞) = m := by
  let := f.stalkAlgebra x
  let := f.sectionsAlgebra V
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := f.isScalarTower_sectionsAlgebra_stalk V hxV
  set 𝔮 := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let e : Localization.AtPrime 𝔮 ≃ₐ[k] X.presheaf.stalk x :=
    (IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮)
      (X.presheaf.stalk x)).restrictScalars k
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    ← (IsLocalRing.ResidueField.mapAlgEquiv e).trdeg_eq]
  exact Algebra.IsStandardSmoothOfRelativeDimension.ringKrullDim_localization_add_trdeg_residueField
    (k := k) m 𝔮

/-- The dimension count `x ↦ dim 𝒪_{X,x} + trdeg_k κ(x)` of a scheme over `k`, as a function to
`WithBot ℕ∞`. -/
noncomputable def dimCount (f : X ⟶ Spec (.of k)) (x : X) : WithBot ℕ∞ :=
  letI := f.stalkAlgebra x
  ringKrullDim (X.presheaf.stalk x) +
    ((Cardinal.toENat (Algebra.trdeg k (ResidueField (X.presheaf.stalk x))) : ℕ∞) : WithBot ℕ∞)

/-- Every point of a scheme smooth over `k` has an affine neighbourhood whose section ring is
standard smooth of SOME relative dimension over `k`. -/
theorem exists_affineOpen_isStandardSmoothOfRelativeDimension' (f : X ⟶ Spec (.of k)) [Smooth f]
    (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (m : ℕ),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmoothOfRelativeDimension m k Γ(X, V) := by
  obtain ⟨V, hV, hxV, hstd⟩ := exists_affineOpen_isStandardSmooth f x
  let := f.sectionsAlgebra V
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd.out
  exact ⟨V, hV, hxV, P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

/-- For `f` smooth over a perfect field the dimension count is locally constant. -/
theorem isLocallyConstant_dimCount [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f] :
    IsLocallyConstant (dimCount f) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  obtain ⟨V, hV, hxV, m, hstd⟩ := exists_affineOpen_isStandardSmoothOfRelativeDimension' f x
  refine ⟨V, V.isOpen, hxV, fun y hyV => ?_⟩
  show dimCount f y = dimCount f x
  unfold dimCount
  rw [ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension f m hV hyV hstd,
    ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension f m hV hxV hstd]

/-- A scheme smooth over a perfect field whose underlying space is preconnected and nonempty is
smooth of ONE relative dimension — the dimension count is locally constant, hence constant, and each
chart's relative dimension is that constant ([Kol07, Notation 64 (1)] for the smooth locus of an
integral scheme). -/
theorem exists_smoothOfRelativeDimension_of_preconnectedSpace [PerfectField k]
    (f : X ⟶ Spec (.of k)) [Smooth f] [PreconnectedSpace X] [Nonempty X] :
    ∃ m : ℕ, SmoothOfRelativeDimension m f := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨V₀, hV₀, hx₀, m₀, hstd₀⟩ := exists_affineOpen_isStandardSmoothOfRelativeDimension' f x₀
  have hD₀ : dimCount f x₀ = m₀ :=
    ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension f m₀ hV₀ hx₀ hstd₀
  refine ⟨m₀, smoothOfRelativeDimension_of_forall_exists_affineOpen f m₀ fun x => ?_⟩
  obtain ⟨V, hV, hxV, m, hstd⟩ := exists_affineOpen_isStandardSmoothOfRelativeDimension' f x
  have hD : dimCount f x = m :=
    ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension f m hV hxV hstd
  have hconst := (isLocallyConstant_dimCount f).apply_eq_of_preconnectedSpace x x₀
  rw [hD, hD₀] at hconst
  have hm : m = m₀ := by exact_mod_cast hconst
  subst hm
  exact ⟨V, hV, hxV, hstd⟩

end AlgebraicGeometry
