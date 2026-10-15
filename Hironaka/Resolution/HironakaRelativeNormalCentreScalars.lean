/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGradedAlgebra
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Canonical centre-ring scalars on actual original normal graded layers
Actual ambient quotient multiplication is defined first. Original J powers
prove annihilation, then the scalar action descends through the actual R/J.
The whole direct sum retains these literal degree actions. The actual plane
trace quotient is used only AFTER scalar descent, to compare with the old
split tangent action. This is not a sheaf normal-flatness or ambient HS theorem.
-/
set_option autoImplicit false
open Set
open scoped DirectSum
namespace Hironaka.HironakaRelativeNormalCentreScalars
noncomputable section
open HironakaRelativeNormalGradedAlgebra
variable (B : Type*) {R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- The OLD layer carrier is an actual ambient submodule by original quotient multiplication. -/
def idealPowerLayerAmbientSubmodule (I J : Ideal R) (q : ℕ) :
    Submodule R (R ⧸ (I ⊔ J ^ (q+1))) where
  carrier := (idealPowerLayer B I J q : Set (R ⧸ (I ⊔ J ^ (q+1))))
  zero_mem' := (idealPowerLayer B I J q).zero_mem
  add_mem' := fun hx hy => (idealPowerLayer B I J q).add_mem hx hy
  smul_mem' := by
    intro r x hx
    obtain ⟨g, hg, rfl⟩ := hx
    refine ⟨r*g, Ideal.mul_mem_left _ r hg, ?_⟩
    change Ideal.Quotient.mk (I ⊔ J ^ (q+1)) (r*g) =
      r • Ideal.Quotient.mk (I ⊔ J ^ (q+1)) g
    rfl

/-- Actual ambient multiplication acts on the EXISTING literal layer, with unchanged addition. -/
@[instance_reducible] def idealPowerLayerAmbientModule (I J : Ideal R) (q : ℕ) :
    Module R (idealPowerLayer B I J q) :=
  inferInstanceAs (Module R (idealPowerLayerAmbientSubmodule B I J q))

attribute [local instance] idealPowerLayerAmbientModule

/-- The ambient action's value is multiplication in the original whole quotient. -/
theorem idealPowerLayerAmbient_smul_val (I J : Ideal R) (q : ℕ) (r : R)
    (x : idealPowerLayer B I J q) :
    (r • x).val = Ideal.Quotient.mk (I ⊔ J ^ (q+1)) r * x.val := rfl

/-- EVERY actual original power representative retains its actual scalar product. -/
theorem idealPowerLayerAmbient_smul_class (I J : Ideal R) (q : ℕ) (r : R)
    (g : powerModule B J q) :
    r • idealPowerLayerMap B I J q g =
      idealPowerLayerMap B I J q ⟨r*g.val, Ideal.mul_mem_left _ r g.property⟩ := by
  apply Subtype.ext
  change Ideal.Quotient.mk _ r * Ideal.Quotient.mk _ g.val =
    Ideal.Quotient.mk _ (r*g.val)
  exact (map_mul (Ideal.Quotient.mk _) _ _).symm

/-- The WHOLE normal ideal annihilates the actual layer; this is derived from true ideal powers. -/
theorem idealPowerLayer_isTorsionBySet (I J : Ideal R) (q : ℕ) :
    Module.IsTorsionBySet R (idealPowerLayer B I J q) J := by
  intro x u
  obtain ⟨g, rfl⟩ := idealPowerLayerMap_surjective B I J q x
  rw [idealPowerLayerAmbient_smul_class]
  apply Subtype.ext
  change Ideal.Quotient.mk (I ⊔ J ^ (q+1)) (u.val*g.val) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (show J ^ (q+1) ≤ I ⊔ J ^ (q+1) from le_sup_right)
  rw [pow_succ']
  exact Ideal.mul_mem_mul u.property g.property

/-- The canonical R/J action is obtained by the proved ambient annihilation, before any split dictionary. -/
@[instance_reducible] def idealPowerLayerCentreModule (I J : Ideal R) (q : ℕ) :
    Module (R ⧸ J) (idealPowerLayer B I J q) :=
  (idealPowerLayer_isTorsionBySet B I J q).module

/-- Every centre scalar representative acts by its ACTUAL ambient product. -/
theorem idealPowerLayerCentre_mk_smul (I J : Ideal R) (q : ℕ) (r : R)
    (x : idealPowerLayer B I J q) :
    letI := idealPowerLayerCentreModule B I J q
    Ideal.Quotient.mk J r • x = r • x := rfl

/-- The full original power-class formula for the canonical centre action. -/
theorem idealPowerLayerCentre_mk_smul_class (I J : Ideal R) (q : ℕ) (r : R)
    (g : powerModule B J q) :
    letI := idealPowerLayerCentreModule B I J q
    Ideal.Quotient.mk J r • idealPowerLayerMap B I J q g =
      idealPowerLayerMap B I J q ⟨r*g.val, Ideal.mul_mem_left _ r g.property⟩ := by
  let := idealPowerLayerCentreModule B I J q
  rw [idealPowerLayerCentre_mk_smul]
  exact idealPowerLayerAmbient_smul_class B I J q r g

/-- The actual ambient module on the OLD whole direct sum is componentwise original multiplication. -/
@[instance_reducible] def idealPowerAssociatedAmbientModule (I J : Ideal R) :
    Module R (⨁ q : ℕ, layerFamily B I J q) := by
  letI : ∀ q, Module R (layerFamily B I J q) := fun q => idealPowerLayerAmbientModule B I J q
  infer_instance

attribute [local instance] idealPowerAssociatedAmbientModule

/-- The WHOLE J annihilates the entire existing direct sum, all degrees simultaneously. -/
theorem idealPowerAssociated_isTorsionBySet (I J : Ideal R) :
    Module.IsTorsionBySet R (⨁ q : ℕ, layerFamily B I J q) J := by
  intro x u
  apply DFinsupp.ext
  intro q
  change (u.val • x) q = 0
  rw [DirectSum.smul_apply]
  exact idealPowerLayer_isTorsionBySet B I J q (x := x q) (a := u)

/-- Canonical whole centre scalars descend from the actual ambient action and internally proved annihilation. -/
@[instance_reducible] def idealPowerAssociatedCentreModule (I J : Ideal R) :
    Module (R ⧸ J) (⨁ q : ℕ, layerFamily B I J q) := by
  letI : ∀ q, Module (R ⧸ J) (layerFamily B I J q) :=
    fun q => idealPowerLayerCentreModule B I J q
  infer_instance

theorem idealPowerAssociatedCentre_mk_smul (I J : Ideal R) (r : R)
    (x : ⨁ q : ℕ, layerFamily B I J q) :
    letI := idealPowerAssociatedCentreModule B I J
    Ideal.Quotient.mk J r • x = r • x := rfl

/-- The descended WHOLE action preserves each literal original degree inclusion. -/
theorem idealPowerAssociatedCentre_mk_smul_of (I J : Ideal R) (q : ℕ) (r : R)
    (x : layerFamily B I J q) :
    letI := idealPowerAssociatedCentreModule B I J
    letI := idealPowerLayerCentreModule B I J q
    Ideal.Quotient.mk J r • DirectSum.of (layerFamily B I J) q x =
      DirectSum.of (layerFamily B I J) q (Ideal.Quotient.mk J r • x) := by
  let := idealPowerAssociatedCentreModule B I J
  let := idealPowerLayerCentreModule B I J q
  rw [idealPowerAssociatedCentre_mk_smul, idealPowerLayerCentre_mk_smul]
  exact (DirectSum.of_smul R q r x).symm

/-- Any quotient scalar, not only a chosen representative, preserves every actual degree. -/
theorem idealPowerAssociatedCentre_smul_of (I J : Ideal R) (q : ℕ) (c : R ⧸ J)
    (x : layerFamily B I J q) :
    letI := idealPowerAssociatedCentreModule B I J
    letI := idealPowerLayerCentreModule B I J q
    c • DirectSum.of (layerFamily B I J) q x =
      DirectSum.of (layerFamily B I J) q (c • x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact idealPowerAssociatedCentre_mk_smul_of B I J q r x

/-- Ambient multiplication by an ACTUAL coefficient pullback agrees with the OLD coefficient action. -/
theorem idealPowerLayerAmbient_algebraMap_smul (I J : Ideal R) (q : ℕ) (b : B)
    (x : idealPowerLayer B I J q) :
    algebraMap B R b • x = b • x := by
  apply Subtype.ext
  change Ideal.Quotient.mk (I ⊔ J ^ (q+1)) (algebraMap B R b) * x.val = b • x.val
  rw [Algebra.smul_def]
  rfl

/-- The actual whole componentwise ambient action retains the OLD coefficient scalar action. -/
theorem idealPowerAssociatedAmbient_algebraMap_smul (I J : Ideal R) (b : B)
    (x : ⨁ q : ℕ, layerFamily B I J q) :
    algebraMap B R b • x = b • x := by
  apply DFinsupp.ext
  intro q
  rw [DirectSum.smul_apply, DirectSum.smul_apply]
  exact idealPowerLayerAmbient_algebraMap_smul B I J q b (x q)

private theorem quotientKerAlgEquivOfEq_mk {S : Type*} [CommRing S] [Algebra B S]
    (J : Ideal R) (f : R →ₐ[B] S) (hJ : J = RingHom.ker f.toRingHom)
    (hf : Function.Surjective f) (r : R) :
    (show (R ⧸ J) ≃ₐ[B] S from by rw [hJ]; exact Ideal.quotientKerAlgEquivOfSurjective hf)
      (Ideal.Quotient.mk J r) = f r := by
  subst J
  rfl

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded

/-- The EXISTING original germ layer inherits literal ambient multiplication. -/
@[instance_reducible] def originalNormalGradedPieceAmbientModule (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    Module (HolGerm (ComplexModel (d+t))) (originalNormalGradedPiece d t I q) :=
  letI := tangentAlgebra d t
  idealPowerLayerAmbientModule (HolGerm (ComplexModel d)) I (normalIdeal d t) q

attribute [local instance] originalNormalGradedPieceAmbientModule

/-- The WHOLE original normal ideal annihilates every ACTUAL original layer internally. -/
theorem originalNormalGradedPiece_isTorsionBy_normalIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    Module.IsTorsionBySet (HolGerm (ComplexModel (d+t)))
      (originalNormalGradedPiece d t I q) (normalIdeal d t) :=
  letI := tangentAlgebra d t
  idealPowerLayer_isTorsionBySet (HolGerm (ComplexModel d)) I (normalIdeal d t) q

/-- Canonical original centre scalars descend from actual ambient action and actual powers. -/
@[instance_reducible] def originalNormalGradedPieceCentreModule (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    Module (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t I q) :=
  letI := tangentAlgebra d t
  idealPowerLayerCentreModule (HolGerm (ComplexModel d)) I (normalIdeal d t) q

/-- Every original centre representative acts by its actual original power product. -/
theorem originalNormalGradedPieceCentre_mk_smul_class (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (r g : HolGerm (ComplexModel (d+t)))
    (hg : g ∈ normalIdeal d t ^ q) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    Ideal.Quotient.mk (normalIdeal d t) r • originalNormalGradedPieceClass d t I q g hg =
      originalNormalGradedPieceClass d t I q (r*g) (Ideal.mul_mem_left _ r hg) := by
  let := tangentAlgebra d t
  exact idealPowerLayerCentre_mk_smul_class (HolGerm (ComplexModel d)) I (normalIdeal d t) q r ⟨g,hg⟩

/-- The OLD literal original direct sum carries its actual componentwise ambient action. -/
@[instance_reducible] def originalNormalAssociatedGradedAmbientModule (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Module (HolGerm (ComplexModel (d+t))) (originalNormalAssociatedGraded d t I) :=
  letI := tangentAlgebra d t
  idealPowerAssociatedAmbientModule (HolGerm (ComplexModel d)) I (normalIdeal d t)

attribute [local instance] originalNormalAssociatedGradedAmbientModule

theorem originalNormalAssociatedGraded_isTorsionBy_normalIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Module.IsTorsionBySet (HolGerm (ComplexModel (d+t)))
      (originalNormalAssociatedGraded d t I) (normalIdeal d t) :=
  letI := tangentAlgebra d t
  idealPowerAssociated_isTorsionBySet (HolGerm (ComplexModel d)) I (normalIdeal d t)

/-- The canonical actual centre quotient acts on ALL old original degrees simultaneously. -/
@[instance_reducible] def originalNormalAssociatedGradedCentreModule (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Module (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalAssociatedGraded d t I) :=
  letI := tangentAlgebra d t
  idealPowerAssociatedCentreModule (HolGerm (ComplexModel d)) I (normalIdeal d t)

/-- Every actual centre scalar preserves every literal original homogeneous inclusion. -/
theorem originalNormalAssociatedGradedCentre_smul_of (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (c : HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (x : originalNormalGradedPiece d t I q) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
    letI := originalNormalAssociatedGradedCentreModule d t I
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    c • DirectSum.of (fun k => (originalNormalGradedPiece d t I k : Type)) q x =
      DirectSum.of (fun k => (originalNormalGradedPiece d t I k : Type)) q (c • x) := by
  let := tangentAlgebra d t
  exact idealPowerAssociatedCentre_smul_of (HolGerm (ComplexModel d)) I (normalIdeal d t) q c x

/-- Actual plane trace representative formula for the EXISTING original quotient algebra equivalence. -/
theorem planeQuotientAlgEquiv_mk (d t : ℕ) (r : HolGerm (ComplexModel (d+t))) :
    planeQuotientAlgEquiv d t (Ideal.Quotient.mk (normalIdeal d t) r) = planeTrace d t r := by
  exact quotientKerAlgEquivOfEq_mk ℂ (normalIdeal d t) (planeTrace d t)
    (normalIdeal_eq_ker_planeTrace d t) (planeTrace_surjective d t) r

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The actual trace decomposition, not a desired scalar dictionary, gives the difference in J. -/
theorem original_minus_tangentTrace_mem (d t : ℕ) (r : HolGerm (ComplexModel (d+t))) :
    r - tangentPullback d t (planeTrace d t r) ∈ normalIdeal d t := by
  rw [normalIdeal_eq_ker_planeTrace]
  change planeTrace d t (r - tangentPullback d t (planeTrace d t r)) = 0
  rw [map_sub, planeTrace_tangentPullback, sub_self]

/-- The canonical action is compared to old tangent scalars ONLY after actual quotient descent. -/
theorem originalNormalGradedPieceCentre_mk_smul_eq_trace (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (r : HolGerm (ComplexModel (d+t)))
    (x : originalNormalGradedPiece d t I q) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    Ideal.Quotient.mk (normalIdeal d t) r • x = planeTrace d t r • x := by
  let := tangentAlgebra d t
  let : SMul (HolGerm (ComplexModel (d+t))) (originalNormalGradedPiece d t I q) :=
    (originalNormalGradedPieceAmbientModule d t I q).toSMul
  let : Module (HolGerm (ComplexModel (d+t))) (originalNormalGradedPiece d t I q) :=
    originalNormalGradedPieceAmbientModule d t I q
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
  let := originalNormalGradedPieceCentreModule d t I q
  change r • x = planeTrace d t r • x
  have h := originalNormalGradedPiece_isTorsionBy_normalIdeal d t I q
    (x := x) (a := ⟨r-tangentPullback d t (planeTrace d t r), original_minus_tangentTrace_mem d t r⟩)
  change (r-tangentPullback d t (planeTrace d t r)) • x = 0 at h
  rw [sub_smul] at h
  have he := sub_eq_zero.mp h
  exact he.trans (idealPowerLayerAmbient_algebraMap_smul (HolGerm (ComplexModel d))
    I (normalIdeal d t) q (planeTrace d t r) x)

/-- EVERY centre scalar acts by its actual OLD plane quotient image on the old original layer. -/
theorem originalNormalGradedPieceCentre_smul_eq_planeQuotient (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (c : HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (x : originalNormalGradedPiece d t I q) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    c • x = planeQuotientAlgEquiv d t c • x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [planeQuotientAlgEquiv_mk]
  exact originalNormalGradedPieceCentre_mk_smul_eq_trace d t q I r x

/-- Actual tangent pullback scalars recover the OLD layer action after canonical descent. -/
theorem originalNormalGradedPieceCentre_tangent_smul (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (b : HolGerm (ComplexModel d))
    (x : originalNormalGradedPiece d t I q) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    Ideal.Quotient.mk (normalIdeal d t) (tangentPullback d t b) • x = b • x := by
  let := tangentAlgebra d t
  simpa only [planeTrace_tangentPullback] using
    originalNormalGradedPieceCentre_mk_smul_eq_trace d t q I (tangentPullback d t b) x

/-- Every canonical centre scalar on the ENTIRE old direct sum is its actual plane quotient scalar. -/
theorem originalNormalAssociatedGradedCentre_smul_eq_planeQuotient (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (c : HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (x : originalNormalAssociatedGraded d t I) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
    letI := originalNormalAssociatedGradedCentreModule d t I
    c • x = planeQuotientAlgEquiv d t c • x := by
  let := tangentAlgebra d t
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
  let := originalNormalAssociatedGradedCentreModule d t I
  apply DFinsupp.ext
  intro q
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
  let := originalNormalGradedPieceCentreModule d t I q
  change c • x q = planeQuotientAlgEquiv d t c • x q
  exact originalNormalGradedPieceCentre_smul_eq_planeQuotient d t q I c (x q)

/-- Every actual ambient representative has its TRUE trace action on the WHOLE original direct sum. -/
theorem originalNormalAssociatedGradedCentre_mk_smul_eq_trace (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (r : HolGerm (ComplexModel (d+t)))
    (x : originalNormalAssociatedGraded d t I) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
    letI := originalNormalAssociatedGradedCentreModule d t I
    Ideal.Quotient.mk (normalIdeal d t) r • x = planeTrace d t r • x := by
  let := tangentAlgebra d t
  simpa only [planeQuotientAlgEquiv_mk] using
    originalNormalAssociatedGradedCentre_smul_eq_planeQuotient d t I
      (Ideal.Quotient.mk (normalIdeal d t) r) x

/-- Actual tangent pullback acts as the old tangent scalar on ALL original degrees simultaneously. -/
theorem originalNormalAssociatedGradedCentre_tangent_smul (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (b : HolGerm (ComplexModel d))
    (x : originalNormalAssociatedGraded d t I) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
    letI := originalNormalAssociatedGradedCentreModule d t I
    Ideal.Quotient.mk (normalIdeal d t) (tangentPullback d t b) • x = b • x := by
  let := tangentAlgebra d t
  simpa only [planeTrace_tangentPullback] using
    originalNormalAssociatedGradedCentre_mk_smul_eq_trace d t I (tangentPullback d t b) x

end
end Hironaka.HironakaRelativeNormalCentreScalars
