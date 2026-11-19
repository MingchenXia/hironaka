import Hironaka.Resolution.HironakaClosedFootprintOpenTowerExtension
import Hironaka.Resolution.HironakaCompactOpenBlowupExtension
import Hironaka.Analytic.TowerPreimageCompact
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false

/-! Extend the SAME actual source-open finite tower from genuine compact
original footprints. Native compact-open one-step blowup UP is reused.
Blueprint: hironaka-compact-footprint-open-tower-extension.tex. -/

open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaCompactFootprintOpenTowerExtension

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupRestrictOpen RestrictEmptyTower

variable {n : ℕ} {X : CMfd.{u} n}

/-- Only an actual finite open tower and its native compact-original-footprint
predicate construct the real ambient tower and full actual tower comparison. -/
theorem exists_compact_footprint_extension (U : Opens X) (K : Set X)
    (hK : IsCompact K) (hKU : K ⊆ U) {Z : CMfd.{u} n}
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : CentresOver ((Subtype.val : U → X) ⁻¹' K) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y), CentresOver K Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val :=
  HironakaClosedFootprintOpenTowerExtension.exists_closed_footprint_extension U K hK.isClosed hKU T hT

end
end Hironaka.HironakaCompactFootprintOpenTowerExtension
