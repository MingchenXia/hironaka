/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Hironaka.Scheme.BlowUp.Rees.DegreeZero
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The affine blow-up: separatedness and properness

The affine blow-up `affineBlowUp I = Proj Rees(I)` of `Spec R` along `I`, with its map
`affineBlowUp.π I` to `Spec R` [Hau14, Definition 4.7]; [Sta, Tags 01OF and 0804], is separated,
and proper when `I` is finitely generated [Sta, Tag 02NS]. Both are inherited from Mathlib's
instances on `Proj`, `Scheme.IsSeparated (Proj 𝒜)` and `IsProper (Proj.toSpecZero 𝒜)` under
`Algebra.FiniteType (𝒜 0) A`: the Rees algebra of a finitely generated ideal is of finite type
(`reesAlgebra.finiteType_of_fg`), and the second factor of `π` is an isomorphism. The hypothesis
`I.FG` enters only here: finiteness belongs to properness, not to the construction; for `R`
Noetherian it is automatic.

The blow-up of a general scheme along a closed subscheme is glued from these affine blow-ups over
the affine opens of the base (`blowUpOf`).
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The affine blow-up is a separated scheme, as every `Proj` is [Sta, Tag 01MC]. -/
instance affineBlowUp.isSeparated : Scheme.IsSeparated (affineBlowUp I) :=
  inferInstanceAs (Scheme.IsSeparated (Proj (reesAlgebra.grading I)))

/-- The blow-up map is separated (Mathlib's `IsSeparated (Proj.toSpecZero 𝒜)`). -/
instance affineBlowUp.isSeparated_π : IsSeparated (affineBlowUp.π I) := by
  unfold affineBlowUp.π
  infer_instance

/-- For `I` finitely generated the blow-up map is proper [Sta, Tag 02NS]: `Proj.toSpecZero` is
proper because `reesAlgebra I` is of finite type over its degree-zero part
(`reesAlgebra.finiteType_of_fg`), and the second factor is an isomorphism. -/
theorem affineBlowUp.isProper_π (hI : I.FG) : IsProper (affineBlowUp.π I) := by
  have := reesAlgebra.finiteType_of_fg I hI
  have h₁ : IsProper (Proj.toSpecZero (reesAlgebra.grading I)) := inferInstance
  have h₂ : IsProper (Spec.map (RingEquiv.toCommRingCatIso (R := R)
      (S := reesAlgebra.grading I 0) (reesAlgebra.gradingZeroEquiv I).symm).hom) :=
    inferInstance
  unfold affineBlowUp.π
  infer_instance

/-- Over a Noetherian ring every blow-up map is proper (every ideal is finitely generated). -/
instance affineBlowUp.isProper_π_of_isNoetherianRing [IsNoetherianRing R] :
    IsProper (affineBlowUp.π I) :=
  affineBlowUp.isProper_π I (IsNoetherian.noetherian I)

end AlgebraicGeometry
