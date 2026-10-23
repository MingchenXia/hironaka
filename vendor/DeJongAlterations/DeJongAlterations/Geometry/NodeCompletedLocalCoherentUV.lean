/-
The affine-section scalar tower and essential-finite-type stalk proof adapt the minimal
proved cores of the repository's Hironaka/Algebra/RegularSmooth/{SmoothAt,Stalk}.lean
and Hironaka/Scheme/IdealSheaf/Derivative/Pullback.lean, adopted under
EnvelopeProperty/deps/hironaka-ep33. SHA256, respectively:
078d52379d98188888f6605c3be1c444df4d9d0ad19b73c173541aae57e483eb;
07e223c88e5db52624d89c0ebe2bfe80ccfc34ae6505baab8d45e2385e73f44d;
e0cedb571b8054be56a760a7fca40c81d9895730c048eed7c77371160a2a9b97.
Copyright (c) 2026 Resolution; author Chris Elliott (Resolution).
Original Lean formalization by Claude Fable 5.1; Apache License 2.0.
Modified: use the SAME already-adopted Scheme.stalkAlgebra and completedLocalRingAlgebra,
retain only the finite-type field-stalk argument, and consume the original coherent
completion comparison. No Hironaka imports. The Apache License 2.0 is reproduced in
DeJongAlterations/Algebra/AdicCompletionTransport.lean.
-/
import DeJongAlterations.Algebra.NodeGeometricCompletionActualUV
import DeJongAlterations.Geometry.NodeCompletedLocalMap

/-! Actual field-scheme stalks and their ORIGINAL coherent differential completions.
The uv model is of the actual completed FIELD-FIBRE, with its entire original field
coefficient action; no relative total-space normal form or residue separability is input. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalCoherentUV

open Algebra.NodeGeometricCompletionCoherentDifferentials
  Algebra.NodeGeometricCompletionDifferentialTransport
  Algebra.NodeGeometricCompletionFormalUV
  Algebra.NodeGeometricCompletionActualUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of K))

/-- Actual original K-coefficients on any affine chart, through the actual map p. -/
@[instance_reducible]
def sectionsAlgebra (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appLE ⊤ U le_top).hom.toAlgebra

/-- The WHOLE chart coefficient map followed by the actual germ is the adopted native
field-stalk coefficient map. -/
theorem germ_comp_sectionsAlgebra (U : X.Opens) {x : X} (hx : x ∈ U) :
    letI := sectionsAlgebra p U
    letI := Scheme.stalkAlgebra p x
    (X.presheaf.germ U x hx).hom.comp (algebraMap K Γ(X, U)) =
      algebraMap K (X.presheaf.stalk x) := by
  change (X.presheaf.germ U x hx).hom.comp
      ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appLE ⊤ U le_top).hom = (Scheme.baseToStalk p x).hom
  rw [← CommRingCat.hom_comp]
  congr 1
  change (Scheme.ΓSpecIso (.of K)).inv ≫
    (p.app ⊤ ≫ X.presheaf.map (homOfLE _).op) ≫ X.presheaf.germ U x hx = _
  rw [Category.assoc, TopCat.Presheaf.germ_res]
  rfl

/-- Actual coefficient/germ scalar tower, retaining the SAME native stalk algebra. -/
theorem sectionsAlgebra_stalk_tower (U : X.Opens) {x : X} (hx : x ∈ U) :
    letI := sectionsAlgebra p U
    letI := Scheme.stalkAlgebra p x
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    IsScalarTower K Γ(X, U) (X.presheaf.stalk x) := by
  let := sectionsAlgebra p U
  let := Scheme.stalkAlgebra p x
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  exact IsScalarTower.of_algebraMap_eq' (germ_comp_sectionsAlgebra p U hx).symm

variable [LocallyOfFiniteType p]

/-- Finite type of the actual affine-chart coefficient map follows from original LocFT. -/
theorem sectionsAlgebra_finiteType {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra p U
    Algebra.FiniteType K Γ(X, U) := by
  let := sectionsAlgebra p U
  exact (p.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of K)).inv.hom
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)

/-- Essential finite type for the literal adopted native field-stalk algebra, internally
from the original scheme map; no output ring hypothesis is assumed. -/
theorem stalkAlgebra_essFiniteType (x : X) :
    letI := Scheme.stalkAlgebra p x
    Algebra.EssFiniteType K (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let := sectionsAlgebra p U
  let := Scheme.stalkAlgebra p x
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let := sectionsAlgebra_stalk_tower p U hx
  let := hU.isLocalization_stalk ⟨x, hx⟩
  let : Algebra.FiniteType K Γ(X, U) := sectionsAlgebra_finiteType p hU
  let : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp K Γ(X, U) (X.presheaf.stalk x)

include p in
/-- Noetherianity of the literal original field-stalk also follows internally. -/
theorem stalk_isNoetherianRing (x : X) : IsNoetherianRing (X.presheaf.stalk x) :=
  NodeCompletedLocalMap.originalTarget_isNoetherianRing p x

variable (x : X)

/-- The actual completed ORIGINAL coherent Ω at a finite-type field-scheme point is the
literal finite uv continuous-differential cokernel when its ACTUAL completed field-fibre
has that coefficient-compatible model. -/
def coherentUVEquiv :
    letI := Scheme.stalkAlgebra p x
    letI := Scheme.completedLocalRingAlgebra p x
    (e : X.completedLocalRing x ≃ₐ[K] FormalUV K) →
      letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
      letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
      LocalOmega K (X.presheaf.stalk x) ≃ₛₗ[e.toRingHom] DifferentialModule K := by
  letI := Scheme.stalkAlgebra p x
  letI := Scheme.completedLocalRingAlgebra p x
  let := stalk_isNoetherianRing p x
  let := stalkAlgebra_essFiniteType p x
  exact fun e => actualGradientEquiv K (X.presheaf.stalk x) e

/-- The ENTIRE completed original universal derivation is preserved through the SAME
actual coefficient-compatible local uv model, beyond the two coordinate formulas. -/
theorem coherentUVEquiv_derivation :
    letI := Scheme.stalkAlgebra p x
    letI := Scheme.completedLocalRingAlgebra p x
    ∀ (e : X.completedLocalRing x ≃ₐ[K] FormalUV K) (a : X.completedLocalRing x),
      coherentUVEquiv p x e
        (completedUniversalDerivation K (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x)) a) =
      Algebra.NodeGeometricCompletionLocalUV.localOmegaGradientEquiv K
        (completedUniversalDerivation K (Algebra.NodeGeometricCompletionLocalUV.LocalUV K)
          (maximalIdeal (Algebra.NodeGeometricCompletionLocalUV.LocalUV K))
          ((Algebra.NodeGeometricCompletionLocalUV.localCompletionFieldEquiv K).symm (e a))) := by
  let := Scheme.stalkAlgebra p x
  let := Scheme.completedLocalRingAlgebra p x
  let := stalk_isNoetherianRing p x
  let := stalkAlgebra_essFiniteType p x
  exact fun e a => actualGradientEquiv_derivation K (X.presheaf.stalk x) e a

/-- Both original completed coordinate-preimage differentials keep their literal classes. -/
theorem coherentUVEquiv_coordinate :
    let := Scheme.stalkAlgebra p x
    let := Scheme.completedLocalRingAlgebra p x
    ∀ (e : X.completedLocalRing x ≃ₐ[K] FormalUV K) (i : Fin 2),
      coherentUVEquiv p x e
        (completedUniversalDerivation K (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
          (e.symm (coordinate K i))) = Submodule.Quotient.mk (Pi.single i 1) := by
  let := Scheme.stalkAlgebra p x
  let := Scheme.completedLocalRingAlgebra p x
  let := stalk_isNoetherianRing p x
  let := stalkAlgebra_essFiniteType p x
  exact fun e i => actualGradientEquiv_coordinate K (X.presheaf.stalk x) e i

/-- The full completed coefficient action is transported through the SAME actual model e. -/
theorem coherentUVEquiv_smul :
    let := Scheme.stalkAlgebra p x
    let := Scheme.completedLocalRingAlgebra p x
    ∀ (e : X.completedLocalRing x ≃ₐ[K] FormalUV K)
      (a : X.completedLocalRing x) (ω : LocalOmega K (X.presheaf.stalk x)),
      coherentUVEquiv p x e (a • ω) = e a • coherentUVEquiv p x e ω := by
  let := Scheme.stalkAlgebra p x
  let := Scheme.completedLocalRingAlgebra p x
  let := stalk_isNoetherianRing p x
  let := stalkAlgebra_essFiniteType p x
  exact fun e a ω => actualGradientEquiv_smul K (X.presheaf.stalk x) e a ω

end DeJongAlterations.Geometry.NodeCompletedLocalCoherentUV
