import Hironaka.Resolution.HironakaActualLocallyFiniteBlowupLimitGeometry
import Mathlib.Topology.Compactness.LocallyFinite

/-! Proper composition of GIVEN whole-limit tails and genuine finite serial phases.
Blueprint: `hironaka-actual-given-whole-limit-serial-extension.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Classical Function
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaActualGivenWholeLimitSerial
noncomputable section

/-- Proper WHOLE compact preimages, not a local open inclusion, control all indices. -/
theorem locallyFinite_image_of_proper {P : Type u} {Q : Type v} {ι : Type w}
    [TopologicalSpace P] [TopologicalSpace Q] [WeaklyLocallyCompactSpace Q]
    {f : P→Q} (hf : IsProperMap f) (D : ι→Set P) (hD : LocallyFinite D) :
    LocallyFinite (fun i=>f '' D i) := by
  intro x
  obtain ⟨K,hK,hxK⟩:=exists_compact_mem_nhds x
  refine ⟨K,hxK,?_⟩
  apply (hD.finite_nonempty_inter_compact (hf.isCompact_preimage hK)).subset
  rintro i ⟨y,⟨z,hz,rfl⟩,hzK⟩
  exact ⟨z,hz,hzK⟩

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq
  HironakaActualLocallyFiniteBlowupLimitGeometry
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- This input tower is over the WHOLE actual limit, not a locally produced open. -/
def finiteContinuationProjection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (T : BlowupTower (actualLimitManifold s hLF) Y) : Y→X :=
  actualLimitBaseProjection s hLF ∘ T.proj

theorem finiteContinuationProjection_holomorphic_proper (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (T : BlowupTower (actualLimitManifold s hLF) Y) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (finiteContinuationProjection s hLF T) ∧
      IsProperMap (finiteContinuationProjection s hLF T) :=
  ⟨(actualLimitBaseProjection_contMDiff s hLF).comp T.contMDiff_proj,
    (actualLimitBaseProjection_isProperMap s hLF).comp (HironakaLocalPrincipalization.isProperMap_proj T)⟩

/-- Real disjoint chronological phases: no finite/Nat flattening of an infinite prefix. -/
def serialCentreImage (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (t : GrowingSeq (actualLimitManifold s hLF)) : ℕ⊕ℕ→Set X :=
  Sum.elim (centreImage s) (fun i=>actualLimitBaseProjection s hLF '' centreImage t i)

theorem serialCentreImage_locallyFinite (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (t : GrowingSeq (actualLimitManifold s hLF))
    (hLFt : LocallyFinite (centreImage t)) : LocallyFinite (serialCentreImage s hLF t) := by
  let : LocallyCompactSpace X:=ChartedSpace.locallyCompactSpace (ComplexModel n) X
  exact hLF.sumElim (locallyFinite_image_of_proper (actualLimitBaseProjection_isProperMap s hLF)
    (centreImage t) hLFt)

theorem serialCentreImage_isClosed (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (t : GrowingSeq (actualLimitManifold s hLF))
    (i : ℕ⊕ℕ) : IsClosed (serialCentreImage s hLF t i) := by
  cases i with
  | inl i=>exact isClosed_centreImage s i
  | inr i=>exact (actualLimitBaseProjection_isProperMap s hLF).isClosedMap _ (isClosed_centreImage t i)

def serialLimitProjection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (t : GrowingSeq (actualLimitManifold s hLF)) (hLFt : LocallyFinite (centreImage t)) :
    actualLimitManifold t hLFt→X :=
  actualLimitBaseProjection s hLF ∘ actualLimitBaseProjection t hLFt

theorem serialLimitProjection_holomorphic_proper (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (t : GrowingSeq (actualLimitManifold s hLF))
    (hLFt : LocallyFinite (centreImage t)) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (serialLimitProjection s hLF t hLFt) ∧
      IsProperMap (serialLimitProjection s hLF t hLFt) :=
  ⟨(actualLimitBaseProjection_contMDiff s hLF).comp (actualLimitBaseProjection_contMDiff t hLFt),
    (actualLimitBaseProjection_isProperMap s hLF).comp (actualLimitBaseProjection_isProperMap t hLFt)⟩
end
end Hironaka.HironakaActualGivenWholeLimitSerial
