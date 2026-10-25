/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableProjectivityMarkedOmega
import DeJongAlterations.StableModification.Gluing.UniquenessValFinal

/-!
# The alteration theorem with stable-modification projectivity discharged

Blueprint: `alteration-projectivity-closed.tex`.
-/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.AlterationProjectivityClosed

universe u

/-- The original alteration conclusion now needs only the corrected stability
spreading input over an algebraically closed field. The actual projectivity
input is proved by the original marked dualizing bundle and closed fibres. -/
theorem deJongAlterationTheorem_of_stableOpenConn {k : Type u} [Field k] [IsAlgClosed k]
    (hO : StableModification.Global.StableOpenNbhdConn k) : DeJongAlterationTheorem k :=
  StableModification.Gluing.UniquenessValFinal.deJongAlterationTheorem_conn hO
    StableProjectivityMarkedOmega.stableModificationProjectivity

end DeJongAlterations.StableModificationBridge.AlterationProjectivityClosed
