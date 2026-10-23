/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DeJongAlterations.StableModificationBridge.AlterationUnconditional

/-!
# De Jong alterations over an arbitrary field

The public entry points preserve the native scheme-theoretic statement and
complete boundary output of the vendored `DeJongAlterations` proof. No perfectness
or geometric-integrality assumption is required. See `docs/DEJONG.md`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Hironaka

/-- De Jong's alteration theorem over every field, including imperfect fields. -/
theorem deJongAlterationTheorem (k : Type u) [Field k] :
    DeJongAlterations.DeJongAlterationTheorem k :=
  DeJongAlterations.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem k

/-- A genuine alteration with regular projective compactification and the full
strict SNC boundary for any prescribed proper closed subset of a variety. -/
theorem exists_alterationWithBoundary (k : Type u) [Field k]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (hX : DeJongAlterations.IsVariety p)
    (Z : TopologicalSpace.Closeds X) (hZ : Z ≠ ⊤) :
    Nonempty (DeJongAlterations.AlterationWithBoundary p (Z : Set X)) :=
  deJongAlterationTheorem k X p hX Z hZ

end Hironaka
