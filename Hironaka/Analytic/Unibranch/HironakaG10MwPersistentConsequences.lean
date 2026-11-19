import Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow
import Hironaka.Analytic.Unibranch.HironakaG10HirRoundData
import Hironaka.Analytic.Unibranch.HironakaG10HirFlattenerGluing
import Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
import Hironaka.Analytic.Unibranch.HironakaG10TmTermination

/-!
# Consequences of the persistent local flattener (lane G10MW, run 0081)

`HironakaG10MwNativeWindow.persistentLocalFlattener` proves the former named input
`PersistentLocalFlattener`.  This module discharges it in the existing consumers, which keep their
statements; each corollary is the consumer with the `hP` argument supplied:

* closedness of the non-flat image of a proper morphism and openness of the flat locus over the base;
* `hclosed` for every centre machine and for round data;
* Hironaka Th. 2.4 for a compact `S` (gluing);
* closedness of the relative non-flat set over a closed set;
* `HironakaFlattening` from round data / tracked rounds / smooth-base round data alone.

No named input.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10MwPersistentConsequences

open Hironaka HironakaG10PNIdealFamily HironakaG10ChowCompactBranch
  HironakaG10ChowTrackedRounds
open Hironaka.Analytic.Unibranch
open Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowTowerDomination Hironaka.Analytic.Unibranch.HironakaG10ChowFlatBimeromorphicIso
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowSequenceFibreChain Hironaka.Analytic.Unibranch.HironakaG10MachineFibreKernel
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow

/-- **The flat locus over the base of a proper morphism is open.** -/
theorem isOpen_flatOverAt_bot_of_proper {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) : IsOpen {x : X.obj.left | FlatOverAt f x ⊥} :=
  isOpen_flatOverAt_bot persistentLocalFlattener f hf

/-- **The non-flat image of a proper morphism is closed** (Frisch). -/
theorem isClosed_nonflatImage_of_proper {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) : IsClosed (nonflatImage f) :=
  isClosed_nonflatImage_of_persistent persistentLocalFlattener f hf

/-- `hclosed` for every centre machine. -/
theorem machine_hclosed_of_proper (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀)
    (hf : IsProperMap s₀.f.hom.left.base) (n : ℕ) :
    IsClosed ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n) :=
  machine_hclosed persistentLocalFlattener M s₀ d₀ hf n

/-- **Hironaka Th. 2.4 for a compact `S`**, unconditionally. -/
theorem exists_localFlattener_of_isCompact_of_proper {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (W : Set X.obj.left) (hW : IsOpen W)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : HironakaG10HirIdealGerms.IsLocallyFinitelyGeneratedOn X.obj.left W IS)
    (hS : IsCompact (W ∩ {x | IS x ≠ ⊤}))
    (hflat : ∀ x ∈ W, IS x ≠ ⊤ → FlatOverAt f x (IS x)) :
    ∃ Z : LocalFlattener f, W ∩ {x | IS x ≠ ⊤} ⊆ Z.support ∧
      ∀ x ∈ W, IS x ≠ ⊤ → Z.H x ≤ IS x :=
  HironakaG10HirFlattenerGluing.exists_localFlattener_of_isCompact persistentLocalFlattener f hf W hW
    IS hIS hS hflat

/-- **The relative non-flat set over a closed set is closed**, unconditionally. -/
theorem isClosed_relNonflat_of_proper {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) {B : Set X.obj.left} (hB : IsClosed B) :
    IsClosed (relNonflat f B) :=
  HironakaG10RdRelativeStep.isClosed_relNonflat persistentLocalFlattener f hf hB

/-- **`HironakaFlattening` from a producer of round data alone.** -/
theorem hironakaFlattening_of_roundData_of_proper
    (hR : ∀ s₀ : Stage, CompactSpace s₀.X.obj.left →
      ∀ hf : IsProperMap s₀.f.hom.left.base, Nonempty (RoundData s₀ hf)) :
    HironakaFlattening :=
  HironakaG10TmTermination.hironakaFlattening_of_roundData persistentLocalFlattener hR

/-- **`HironakaFlattening` from tracked rounds alone.** -/
theorem hironakaFlattening_of_trackedRounds_of_proper
    (hT : ∀ s₀ : Stage, CompactSpace s₀.X.obj.left → ∀ hf : IsProperMap s₀.f.hom.left.base,
      ∃ (M : CentreMachine) (d₀ : M.St s₀),
        Nonempty (HironakaG10ChowTrackedRoundData.TrackedRounds M s₀ d₀ hf)) :
    HironakaFlattening :=
  HironakaG10TmTermination.hironakaFlattening_of_trackedRounds persistentLocalFlattener hT

/-- **`HironakaFlattening` from round data over compact smooth initial bases alone.** -/
theorem hironakaFlattening_of_smooth_roundData_of_proper
    (hR : ∀ s₀ : Stage, CompactSpace s₀.X.obj.left → SourceReducedComplexSpace.IsSmooth s₀.X →
      ∀ hf : IsProperMap s₀.f.hom.left.base, Nonempty (RoundData s₀ hf)) :
    HironakaFlattening :=
  HironakaG10TmTermination.hironakaFlattening_of_smooth_roundData persistentLocalFlattener hR

end Hironaka.Analytic.Unibranch.HironakaG10MwPersistentConsequences
