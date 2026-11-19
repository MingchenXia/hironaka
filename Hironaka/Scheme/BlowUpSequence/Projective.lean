/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.ProjectiveBundle.Defs
import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp
import Hironaka.Scheme.ProjectiveBundle.BlowUp

/-!
# The composite of a succession of blow-ups is projective

For a Noetherian scheme `X`, the composite `X_r → X` of a finite succession of blow-ups is a single
blow-up of `X` up to isomorphism (`AlgebraicGeometry.exists_blowUp_composite_iso`,
[Sta, Tag 080B]), and a blow-up of a locally Noetherian scheme is projective
(`AlgebraicGeometry.Scheme.IdealSheafData.isProjective_blowUpπ`, [Sta, Tag 02NS]); so the composite
is projective (`AlgebraicGeometry.Scheme.BlowUpSequence.isProjective_composite`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.BlowUpSequence

/-- **The composite of a finite succession of blow-ups of a Noetherian scheme is projective**: it
is a single blow-up up to isomorphism [Sta, Tag 080B], and blow-ups are projective
[Sta, Tag 02NS]. -/
theorem isProjective_composite {X : Scheme.{u}} [IsNoetherian X] (S : BlowUpSequence X) :
    IsProjective S.composite := by
  obtain ⟨K, -, e, he, -⟩ := exists_blowUp_composite_iso S
  rw [← he]
  have := K.isProjective_blowUpπ
  exact IsProjective.isIso_comp e.hom K.blowUpπ

end AlgebraicGeometry.Scheme.BlowUpSequence
