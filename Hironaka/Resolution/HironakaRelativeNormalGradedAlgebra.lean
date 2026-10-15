/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalLocalizedAssociatedGraded
import Mathlib.Algebra.DirectSum.Algebra

/-! # Intrinsic algebra of the literal original normal associated graded

The existing original normal layers are the true images of the normal ideal
powers in the whole next-power quotient. Their multiplication is defined by
actual original representatives, and the whole remainder ideal proves that
it is independent of representatives. Genuine original power-class maps then
prove the graded ring and tangent-algebra laws on the existing literal direct
sum. The old entire polynomial symbol map has this intrinsic multiplication,
and its complete old initial ideal gives a quotient algebra isomorphism.

The quotient comparison is proved after constructing the intrinsic operations;
it does not define them. The algebra comparison retains the previous linear
map, homogeneous degree inclusions, and original quotient-module dictionary.
Uniform graded ranks, intrinsic smooth-centre sheaf normal flatness, higher
Hilbert--Samuel descent, and the singular driver remain subsequent producers.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff DirectSum

namespace Hironaka.HironakaRelativeNormalGradedAlgebra
noncomputable section

variable (B : Type*) {R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- The actual original power family inside the original ring. -/
abbrev powerModule (J : Ideal R) (q : ℕ) : Submodule B R := (J ^ q).restrictScalars B

abbrev powerFamily (J : Ideal R) : ℕ → Type _ := fun q => powerModule B J q

instance powerModuleGradedMonoid (J : Ideal R) : SetLike.GradedMonoid (powerModule B J) where
  one_mem := by change (1 : R) ∈ J ^ 0; simp
  mul_mem := by
    intro p q g h hg hh
    change g * h ∈ J ^ (p + q)
    rw [pow_add]
    exact Ideal.mul_mem_mul hg hh

/-- The genuine image of the qth power in the whole original next-power quotient. -/
def idealPowerLayer (I J : Ideal R) (q : ℕ) : Submodule B (R ⧸ (I ⊔ J ^ (q+1))) :=
  (powerModule B J q).map (Ideal.Quotient.mkₐ B (I ⊔ J ^ (q+1))).toLinearMap

abbrev layerFamily (I J : Ideal R) : ℕ → Type _ := fun q => idealPowerLayer B I J q

/-- The actual original power-to-layer class map. -/
def idealPowerLayerMap (I J : Ideal R) (q : ℕ) :
    powerModule B J q →ₗ[B] idealPowerLayer B I J q :=
  (((Ideal.Quotient.mkₐ B (I ⊔ J ^ (q+1))).toLinearMap).comp
    (powerModule B J q).subtype).codRestrict (idealPowerLayer B I J q)
      (fun g => ⟨g.val, g.property, rfl⟩)

@[simp] theorem idealPowerLayerMap_val (I J : Ideal R) (q : ℕ) (g : powerModule B J q) :
    (idealPowerLayerMap B I J q g).val = Ideal.Quotient.mk (I ⊔ J ^ (q+1)) g.val := rfl

theorem idealPowerLayerMap_surjective (I J : Ideal R) (q : ℕ) :
    Function.Surjective (idealPowerLayerMap B I J q) := by
  rintro ⟨z, hz⟩
  obtain ⟨g, hg, he⟩ := hz
  exact ⟨⟨g, hg⟩, Subtype.ext he⟩

theorem idealPowerLayer_exists_representative (I J : Ideal R) (q : ℕ)
    (x : idealPowerLayer B I J q) :
    ∃ g : R, g ∈ J ^ q ∧ Ideal.Quotient.mk (I ⊔ J ^ (q+1)) g = x.val := by
  obtain ⟨g, hg, he⟩ := x.property
  exact ⟨g, hg, he⟩

def idealPowerLayerRepresentative (I J : Ideal R) (q : ℕ)
    (x : idealPowerLayer B I J q) : R :=
  Classical.choose (idealPowerLayer_exists_representative B I J q x)

theorem idealPowerLayerRepresentative_mem (I J : Ideal R) (q : ℕ)
    (x : idealPowerLayer B I J q) : idealPowerLayerRepresentative B I J q x ∈ J ^ q :=
  (Classical.choose_spec (idealPowerLayer_exists_representative B I J q x)).1

theorem idealPowerLayerRepresentative_spec (I J : Ideal R) (q : ℕ)
    (x : idealPowerLayer B I J q) :
    Ideal.Quotient.mk (I ⊔ J ^ (q+1)) (idealPowerLayerRepresentative B I J q x) = x.val :=
  (Classical.choose_spec (idealPowerLayer_exists_representative B I J q x)).2

/-- Genuine representative multiplication; no polynomial quotient structure is used. -/
def idealPowerLayerMul (I J : Ideal R) {p q : ℕ}
    (x : idealPowerLayer B I J p) (y : idealPowerLayer B I J q) : idealPowerLayer B I J (p+q) :=
  idealPowerLayerMap B I J (p+q)
    ⟨idealPowerLayerRepresentative B I J p x * idealPowerLayerRepresentative B I J q y, by
      change _ ∈ J ^ (p+q)
      rw [pow_add]
      exact Ideal.mul_mem_mul (idealPowerLayerRepresentative_mem B I J p x)
        (idealPowerLayerRepresentative_mem B I J q y)⟩

theorem original_remainder_mul_mem (I J : Ideal R) (p q : ℕ) {v w : R}
    (hv : v ∈ I ⊔ J ^ (p+1)) (hw : w ∈ J ^ q) : v*w ∈ I ⊔ J ^ (p+q+1) := by
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hv
  rw [← he, add_mul]
  apply (I ⊔ J ^ (p+q+1)).add_mem
  · exact (show I ≤ I ⊔ J ^ (p+q+1) from le_sup_left) (I.mul_mem_right _ ha)
  · apply (show J ^ (p+q+1) ≤ I ⊔ J ^ (p+q+1) from le_sup_right)
    have hmul := Ideal.mul_mem_mul hb hw
    simpa only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmul

/-- Every supplied genuine original representative gives the same actual layer product. -/
theorem idealPowerLayerMul_map (I J : Ideal R) {p q : ℕ}
    (g : powerModule B J p) (h : powerModule B J q) :
    idealPowerLayerMul B I J (idealPowerLayerMap B I J p g) (idealPowerLayerMap B I J q h) =
      idealPowerLayerMap B I J (p+q) (GradedMonoid.GMul.mul (A := powerFamily B J) g h) := by
  let x := idealPowerLayerMap B I J p g
  let y := idealPowerLayerMap B I J q h
  let gx := idealPowerLayerRepresentative B I J p x
  let hy := idealPowerLayerRepresentative B I J q y
  have hg : gx-g.val ∈ I ⊔ J ^ (p+1) := by
    apply Ideal.Quotient.eq.mp
    exact idealPowerLayerRepresentative_spec B I J p x
  have hh : hy-h.val ∈ I ⊔ J ^ (q+1) := by
    apply Ideal.Quotient.eq.mp
    exact idealPowerLayerRepresentative_spec B I J q y
  have hfirst := original_remainder_mul_mem I J p q hg (idealPowerLayerRepresentative_mem B I J q y)
  have hsecond : g.val*(hy-h.val) ∈ I ⊔ J ^ (p+q+1) := by
    simpa only [mul_comm, Nat.add_comm] using original_remainder_mul_mem I J q p hh g.property
  apply Subtype.ext
  change Ideal.Quotient.mk (I ⊔ J ^ (p+q+1)) (gx*hy) =
    Ideal.Quotient.mk (I ⊔ J ^ (p+q+1)) (g.val*h.val)
  apply Ideal.Quotient.eq.mpr
  have hsum := (I ⊔ J ^ (p+q+1)).add_mem hfirst hsecond
  convert hsum using 1; ring

instance idealPowerLayerGMul (I J : Ideal R) : GradedMonoid.GMul (layerFamily B I J) where
  mul := idealPowerLayerMul B I J

instance idealPowerLayerGOne (I J : Ideal R) : GradedMonoid.GOne (layerFamily B I J) where
  one := idealPowerLayerMap B I J 0 (GradedMonoid.GOne.one (A := powerFamily B J))

/-- Genuine original class maps on the actual graded original power family. -/
def powerToLayer (I J : Ideal R) :
    GradedMonoid (powerFamily B J) → GradedMonoid (layerFamily B I J) :=
  fun x => GradedMonoid.mk x.fst (idealPowerLayerMap B I J x.fst x.snd)

theorem powerToLayer_surjective (I J : Ideal R) : Function.Surjective (powerToLayer B I J) := by
  rintro ⟨q, x⟩
  obtain ⟨g, hg⟩ := idealPowerLayerMap_surjective B I J q x
  exact ⟨GradedMonoid.mk q g, Sigma.ext rfl (heq_of_eq hg)⟩

theorem powerToLayer_mul (I J : Ideal R)
    (g h : GradedMonoid (powerFamily B J)) :
    powerToLayer B I J (g*h) = powerToLayer B I J g * powerToLayer B I J h := by
  cases g with | mk p g =>
    cases h with | mk q h =>
      exact Sigma.ext rfl (heq_of_eq (idealPowerLayerMul_map B I J g h).symm)

theorem powerToLayer_one (I J : Ideal R) : powerToLayer B I J 1 = 1 := rfl

instance idealPowerLayerGCommMonoid (I J : Ideal R) :
    GradedMonoid.GCommMonoid (layerFamily B I J) where
  one_mul x := by
    obtain ⟨g, rfl⟩ := powerToLayer_surjective B I J x
    rw [← powerToLayer_one B I J, ← powerToLayer_mul, one_mul]
  mul_one x := by
    obtain ⟨g, rfl⟩ := powerToLayer_surjective B I J x
    rw [← powerToLayer_one B I J, ← powerToLayer_mul, mul_one]
  mul_assoc x y z := by
    obtain ⟨g, rfl⟩ := powerToLayer_surjective B I J x
    obtain ⟨h, rfl⟩ := powerToLayer_surjective B I J y
    obtain ⟨k, rfl⟩ := powerToLayer_surjective B I J z
    rw [← powerToLayer_mul, ← powerToLayer_mul, ← powerToLayer_mul, ← powerToLayer_mul, mul_assoc]
  mul_comm x y := by
    obtain ⟨g, rfl⟩ := powerToLayer_surjective B I J x
    obtain ⟨h, rfl⟩ := powerToLayer_surjective B I J y
    rw [← powerToLayer_mul, ← powerToLayer_mul, mul_comm]

instance idealPowerLayerGNonUnitalNonAssocSemiring (I J : Ideal R) :
    DirectSum.GNonUnitalNonAssocSemiring (layerFamily B I J) where
  mul_zero x := by
    obtain ⟨g, rfl⟩ := idealPowerLayerMap_surjective B I J _ x
    change idealPowerLayerMul B I J (idealPowerLayerMap B I J _ g) 0 = 0
    simpa only [LinearMap.map_zero, DirectSum.GNonUnitalNonAssocSemiring.mul_zero] using
      idealPowerLayerMul_map B I J g (0 : powerModule B J _)
  zero_mul y := by
    obtain ⟨h, rfl⟩ := idealPowerLayerMap_surjective B I J _ y
    change idealPowerLayerMul B I J 0 (idealPowerLayerMap B I J _ h) = 0
    simpa only [LinearMap.map_zero, DirectSum.GNonUnitalNonAssocSemiring.zero_mul] using
      idealPowerLayerMul_map B I J (0 : powerModule B J _) h
  mul_add x y z := by
    obtain ⟨g, rfl⟩ := idealPowerLayerMap_surjective B I J _ x
    obtain ⟨h, rfl⟩ := idealPowerLayerMap_surjective B I J _ y
    obtain ⟨k, rfl⟩ := idealPowerLayerMap_surjective B I J _ z
    change idealPowerLayerMul B I J _ _ = idealPowerLayerMul B I J _ _ + idealPowerLayerMul B I J _ _
    have he := idealPowerLayerMul_map B I J g (h+k)
    rw [map_add, DirectSum.GNonUnitalNonAssocSemiring.mul_add, map_add] at he
    simpa only [idealPowerLayerMul_map] using he
  add_mul x y z := by
    obtain ⟨g, rfl⟩ := idealPowerLayerMap_surjective B I J _ x
    obtain ⟨h, rfl⟩ := idealPowerLayerMap_surjective B I J _ y
    obtain ⟨k, rfl⟩ := idealPowerLayerMap_surjective B I J _ z
    change idealPowerLayerMul B I J _ _ = idealPowerLayerMul B I J _ _ + idealPowerLayerMul B I J _ _
    have he := idealPowerLayerMul_map B I J (g+h) k
    rw [map_add, DirectSum.GNonUnitalNonAssocSemiring.add_mul, map_add] at he
    simpa only [idealPowerLayerMul_map] using he

instance idealPowerLayerGSemiring (I J : Ideal R) : DirectSum.GSemiring (layerFamily B I J) where
  natCast n := idealPowerLayerMap B I J 0 (DirectSum.GSemiring.natCast (A := powerFamily B J) n)
  natCast_zero := by rw [DirectSum.GSemiring.natCast_zero, map_zero]
  natCast_succ n := by rw [DirectSum.GSemiring.natCast_succ, map_add]; rfl

instance idealPowerLayerGCommSemiring (I J : Ideal R) :
    DirectSum.GCommSemiring (layerFamily B I J) where

instance idealPowerLayerGRing (I J : Ideal R) : DirectSum.GRing (layerFamily B I J) where
  intCast n := idealPowerLayerMap B I J 0 (DirectSum.GRing.intCast (A := powerFamily B J) n)
  intCast_ofNat n := by rw [DirectSum.GRing.intCast_ofNat]; rfl
  intCast_negSucc_ofNat n := by rw [DirectSum.GRing.intCast_negSucc_ofNat, map_neg]; rfl

instance idealPowerLayerGCommRing (I J : Ideal R) : DirectSum.GCommRing (layerFamily B I J) where

theorem powerToLayer_smul (I J : Ideal R) (r : B)
    (g : GradedMonoid (powerFamily B J)) :
    powerToLayer B I J (r • g) = r • powerToLayer B I J g := by
  cases g with
  | mk q g =>
    exact Sigma.ext rfl (heq_of_eq ((idealPowerLayerMap B I J q).map_smul r g))

/-- The original quotient's scalar action is the given original algebra action. -/
instance idealPowerLayerGAlgebra (I J : Ideal R) : DirectSum.GAlgebra B (layerFamily B I J) where
  toFun := (idealPowerLayerMap B I J 0).toAddMonoidHom.comp
    (DirectSum.GAlgebra.toFun (R := B) (A := powerFamily B J))
  map_one := by
    change idealPowerLayerMap B I J 0
        (DirectSum.GAlgebra.toFun (R := B) (A := powerFamily B J) (1 : B)) =
      idealPowerLayerMap B I J 0 (GradedMonoid.GOne.one (A := powerFamily B J))
    rw [DirectSum.GAlgebra.map_one]
  map_mul r s := by
    have hs := congrArg (powerToLayer B I J)
      (DirectSum.GAlgebra.map_mul (R := B) (A := powerFamily B J) r s)
    change powerToLayer B I J (GradedMonoid.mk 0 (DirectSum.GAlgebra.toFun (r*s))) =
      powerToLayer B I J (GradedMonoid.mk 0 (DirectSum.GAlgebra.toFun r) *
        GradedMonoid.mk 0 (DirectSum.GAlgebra.toFun s)) at hs
    rw [powerToLayer_mul] at hs
    exact hs
  commutes r x := mul_comm _ _
  smul_def r x := by
    obtain ⟨g, rfl⟩ := powerToLayer_surjective B I J x
    have hs := congrArg (powerToLayer B I J)
      (DirectSum.GAlgebra.smul_def (R := B) (A := powerFamily B J) r g)
    rw [powerToLayer_smul, powerToLayer_mul] at hs
    exact hs

@[instance_reducible] def idealPowerAssociatedCommRing (I J : Ideal R) :
    CommRing (⨁ q : ℕ, layerFamily B I J q) := inferInstance

attribute [local instance] idealPowerAssociatedCommRing

@[instance_reducible] def idealPowerAssociatedAlgebra (I J : Ideal R) :
    letI := idealPowerAssociatedCommRing B I J
    Algebra B (⨁ q : ℕ, layerFamily B I J q) :=
  letI := idealPowerAssociatedCommRing B I J
  inferInstance


attribute [local instance] idealPowerAssociatedAlgebra

theorem idealPowerAssociated_of_mul_of (I J : Ideal R) (p q : ℕ)
    (x : layerFamily B I J p) (y : layerFamily B I J q) :
    DirectSum.of (layerFamily B I J) p x * DirectSum.of (layerFamily B I J) q y =
      DirectSum.of (layerFamily B I J) (p+q) (idealPowerLayerMul B I J x y) :=
  DirectSum.of_mul_of x y

theorem idealPowerAssociated_algebraMap (I J : Ideal R) (r : B) :
    algebraMap B (⨁ q : ℕ, layerFamily B I J q) r =
      DirectSum.of (layerFamily B I J) 0
        (idealPowerLayerMap B I J 0 ⟨algebraMap B R r, by simp⟩) := rfl

/-- A true homogeneous evaluation class in the intrinsic power layer. -/
def polynomialPowerHomogeneousSymbolMap {σ : Type*} (I J : Ideal R)
    (E : MvPolynomial σ B →ₐ[B] R)
    (hE : ∀ q P, P.IsHomogeneous q → E P ∈ J ^ q) (q : ℕ) :
    MvPolynomial.homogeneousSubmodule σ B q →ₗ[B] layerFamily B I J q :=
  (idealPowerLayerMap B I J q).comp
    ((E.toLinearMap.comp (MvPolynomial.homogeneousSubmodule σ B q).subtype).codRestrict
      (powerModule B J q) (fun P => hE q P.val P.property))

/-- Actual homogeneous decomposition followed by genuine evaluation classes. -/
def polynomialPowerSymbolMap {σ : Type*} (I J : Ideal R)
    (E : MvPolynomial σ B →ₐ[B] R)
    (hE : ∀ q P, P.IsHomogeneous q → E P ∈ J ^ q) :
    MvPolynomial σ B →ₗ[B] (⨁ q : ℕ, layerFamily B I J q) :=
  let : DirectSum.Decomposition (MvPolynomial.homogeneousSubmodule σ B) :=
    MvPolynomial.decomposition
  (DirectSum.lmap (fun q => polynomialPowerHomogeneousSymbolMap B I J E hE q)).comp
    (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule σ B)).toLinearMap

theorem polynomialPowerSymbolMap_homogeneous {σ : Type*} (I J : Ideal R)
    (E : MvPolynomial σ B →ₐ[B] R)
    (hE : ∀ q P, P.IsHomogeneous q → E P ∈ J ^ q) (q : ℕ)
    (P : MvPolynomial.homogeneousSubmodule σ B q) :
    polynomialPowerSymbolMap B I J E hE P.val =
      DirectSum.lof B ℕ (layerFamily B I J) q
        (polynomialPowerHomogeneousSymbolMap B I J E hE q P) := by
  let : DirectSum.Decomposition (MvPolynomial.homogeneousSubmodule σ B) :=
    MvPolynomial.decomposition
  exact (congrArg (DirectSum.lmap (fun k => polynomialPowerHomogeneousSymbolMap B I J E hE k))
    (DirectSum.decomposeLinearEquiv_apply_coe
      (MvPolynomial.homogeneousSubmodule σ B) q P)).trans
        (DirectSum.lmap_lof (fun k => polynomialPowerHomogeneousSymbolMap B I J E hE k) q P)

theorem polynomialPowerSymbolMap_mul_homogeneous {σ : Type*} (I J : Ideal R)
    (E : MvPolynomial σ B →ₐ[B] R)
    (hE : ∀ q P, P.IsHomogeneous q → E P ∈ J ^ q) (p q : ℕ)
    (P : MvPolynomial.homogeneousSubmodule σ B p)
    (Q : MvPolynomial.homogeneousSubmodule σ B q) :
    polynomialPowerSymbolMap B I J E hE (P.val * Q.val) =
      polynomialPowerSymbolMap B I J E hE P.val * polynomialPowerSymbolMap B I J E hE Q.val := by
  have hPQ := polynomialPowerSymbolMap_homogeneous B I J E hE (p+q)
    ⟨P.val * Q.val, P.property.mul Q.property⟩
  rw [hPQ, polynomialPowerSymbolMap_homogeneous B I J E hE p P,
    polynomialPowerSymbolMap_homogeneous B I J E hE q Q]
  simp only [DirectSum.lof_eq_of, DirectSum.of_mul_of]
  congr 1
  change idealPowerLayerMap B I J (p+q) ⟨E (P.val*Q.val), _⟩ =
    idealPowerLayerMul B I J (idealPowerLayerMap B I J p ⟨E P.val, _⟩)
      (idealPowerLayerMap B I J q ⟨E Q.val, _⟩)
  rw [idealPowerLayerMul_map]
  apply Subtype.ext
  change Ideal.Quotient.mk _ (E (P.val * Q.val)) = Ideal.Quotient.mk _ (E P.val * E Q.val)
  rw [map_mul]

theorem polynomialPowerSymbolMap_mul {σ : Type*} (I J : Ideal R)
    (E : MvPolynomial σ B →ₐ[B] R)
    (hE : ∀ q P, P.IsHomogeneous q → E P ∈ J ^ q) (P Q : MvPolynomial σ B) :
    polynomialPowerSymbolMap B I J E hE (P*Q) =
      polynomialPowerSymbolMap B I J E hE P * polynomialPowerSymbolMap B I J E hE Q := by
  induction P using MvPolynomial.induction_on' with
  | monomial α a =>
    induction Q using MvPolynomial.induction_on' with
    | monomial β b =>
      exact polynomialPowerSymbolMap_mul_homogeneous B I J E hE α.degree β.degree
        ⟨MvPolynomial.monomial α a, MvPolynomial.isHomogeneous_monomial a rfl⟩
        ⟨MvPolynomial.monomial β b, MvPolynomial.isHomogeneous_monomial b rfl⟩
    | add Q Q' hQ hQ' => rw [mul_add, map_add, hQ, hQ', map_add, mul_add]
  | add P P' hP hP' => rw [add_mul, map_add, hP, hP', map_add, add_mul]

theorem polynomialPowerSymbolMap_one {σ : Type*} (I J : Ideal R)
    (E : MvPolynomial σ B →ₐ[B] R)
    (hE : ∀ q P, P.IsHomogeneous q → E P ∈ J ^ q) :
    polynomialPowerSymbolMap B I J E hE 1 = 1 := by
  rw [polynomialPowerSymbolMap_homogeneous B I J E hE 0
    ⟨1, MvPolynomial.isHomogeneous_one σ B⟩, DirectSum.lof_eq_of, DirectSum.one_def]
  congr 1
  apply Subtype.ext
  change Ideal.Quotient.mk _ (E 1) = Ideal.Quotient.mk _ 1
  rw [map_one]

/-- Multiplicativity and the actual degree-zero unit package the genuine symbol into an algebra map. -/
def polynomialPowerSymbolAlgHom {σ : Type*} (I J : Ideal R)
    (E : MvPolynomial σ B →ₐ[B] R)
    (hE : ∀ q P, P.IsHomogeneous q → E P ∈ J ^ q) :
    MvPolynomial σ B →ₐ[B] (⨁ q : ℕ, layerFamily B I J q) where
  toFun := polynomialPowerSymbolMap B I J E hE
  map_zero' := (polynomialPowerSymbolMap B I J E hE).map_zero
  map_add' := (polynomialPowerSymbolMap B I J E hE).map_add
  map_one' := polynomialPowerSymbolMap_one B I J E hE
  map_mul' := polynomialPowerSymbolMap_mul B I J E hE
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      (polynomialPowerSymbolMap B I J E hE).map_smul, polynomialPowerSymbolMap_one]

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalLocalizedAssociatedGraded HironakaRelativeNormalMonomialBasis

/-- The actual original qth power class in its literal original layer. -/
def originalNormalGradedPieceClass (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ q) :
    letI := tangentAlgebra d t
    originalNormalGradedPiece d t I q :=
  letI := tangentAlgebra d t
  idealPowerLayerMap (HolGerm (ComplexModel d)) I (normalIdeal d t) q ⟨g, hg⟩

/-- Intrinsic multiplication of actual original classes by their genuine power representatives. -/
def originalNormalGradedPieceMul (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) {p q : ℕ} :
    letI := tangentAlgebra d t
    originalNormalGradedPiece d t I p → originalNormalGradedPiece d t I q →
      originalNormalGradedPiece d t I (p+q) :=
  letI := tangentAlgebra d t
  idealPowerLayerMul (HolGerm (ComplexModel d)) I (normalIdeal d t)

theorem originalNormalGradedPieceMul_of_representatives (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (p q : ℕ)
    (g h : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ p)
    (hh : h ∈ normalIdeal d t ^ q) :
    letI := tangentAlgebra d t
    originalNormalGradedPieceMul d t I
      (originalNormalGradedPieceClass d t I p g hg) (originalNormalGradedPieceClass d t I q h hh) =
        originalNormalGradedPieceClass d t I (p+q) (g*h)
          (by rw [pow_add]; exact Ideal.mul_mem_mul hg hh) := by
  let := tangentAlgebra d t
  exact idealPowerLayerMul_map (HolGerm (ComplexModel d)) I (normalIdeal d t) ⟨g, hg⟩ ⟨h, hh⟩

/-- The existing literal original direct sum has the intrinsic actual original graded ring laws. -/
@[instance_reducible] def originalNormalAssociatedGradedCommRing (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    CommRing (originalNormalAssociatedGraded d t I) :=
  letI := tangentAlgebra d t
  idealPowerAssociatedCommRing (HolGerm (ComplexModel d)) I (normalIdeal d t)

attribute [local instance] originalNormalAssociatedGradedCommRing

/-- The intrinsic original algebra retains its pre-existing genuine tangent scalar action. -/
@[instance_reducible] def originalNormalAssociatedGradedAlgebra (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI := originalNormalAssociatedGradedCommRing d t I
    Algebra (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t I) :=
  letI := tangentAlgebra d t
  letI := originalNormalAssociatedGradedCommRing d t I
  idealPowerAssociatedAlgebra (HolGerm (ComplexModel d)) I (normalIdeal d t)

attribute [local instance] originalNormalAssociatedGradedAlgebra

/-- The original whole direct-sum product has precisely the independently constructed layer multiplication. -/
theorem originalNormalAssociatedGraded_lof_mul_lof (d t p q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (x : originalNormalGradedPiece d t I p) (y : originalNormalGradedPiece d t I q) :
    let := tangentAlgebra d t
    DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun k => (originalNormalGradedPiece d t I k : Type)) p x *
        DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun k => (originalNormalGradedPiece d t I k : Type)) q y =
      DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun k => (originalNormalGradedPiece d t I k : Type)) (p+q)
        (originalNormalGradedPieceMul d t I x y) := by
  let := tangentAlgebra d t
  exact idealPowerAssociated_of_mul_of (HolGerm (ComplexModel d)) I (normalIdeal d t) p q x y

/-- The intrinsic algebra's scalar map is the original tangent-pullback class in degree zero. -/
theorem originalNormalAssociatedGraded_algebraMap (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (r : HolGerm (ComplexModel d)) :
    let := tangentAlgebra d t
    algebraMap (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t I) r =
      DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun k => (originalNormalGradedPiece d t I k : Type)) 0
        (originalNormalGradedPieceClass d t I 0
          (algebraMap (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) r) (by simp)) := by
  let := tangentAlgebra d t
  exact idealPowerAssociated_algebraMap (HolGerm (ComplexModel d)) I (normalIdeal d t) r

/-- The original symbol's actual intrinsic algebra map, using genuine normal evaluation. -/
def normalAssociatedSymbolAlgHom (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      originalNormalAssociatedGraded d t I :=
  letI := tangentAlgebra d t
  polynomialPowerSymbolAlgHom (HolGerm (ComplexModel d)) I (normalIdeal d t)
    (normalPolynomialEval d t) (normalPolynomialEval_mem_pow_of_homogeneous d t)

/-- The intrinsic algebra map is the pre-existing entire original linear symbol map. -/
theorem normalAssociatedSymbolAlgHom_toLinearMap (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    (normalAssociatedSymbolAlgHom d t I).toLinearMap = normalAssociatedSymbolMap d t I := by
  let := tangentAlgebra d t
  rfl

@[simp] theorem normalAssociatedSymbolAlgHom_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    normalAssociatedSymbolAlgHom d t I P = normalAssociatedSymbolMap d t I P := by
  let := tangentAlgebra d t
  exact congrArg (fun F => F P) (normalAssociatedSymbolAlgHom_toLinearMap d t I)

/-- Its complete algebra kernel is precisely the whole original initial ideal. -/
theorem normalAssociatedSymbolAlgHom_ker (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    RingHom.ker (normalAssociatedSymbolAlgHom d t I).toRingHom = originalNormalInitialIdeal d t I := by
  let := tangentAlgebra d t
  apply Ideal.ext
  intro P
  change normalAssociatedSymbolAlgHom d t I P = 0 ↔ normalAssociatedSymbolMap d t I P = 0
  rw [normalAssociatedSymbolAlgHom_apply]

/-- Genuine first-isomorphism dictionary for the independently constructed intrinsic original algebra. -/
def originalNormalAssociatedGradedQuotientAlgEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ originalNormalInitialIdeal d t I)
      ≃ₐ[HolGerm (ComplexModel d)] originalNormalAssociatedGraded d t I :=
  letI := tangentAlgebra d t
  (Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d))
    (normalAssociatedSymbolAlgHom_ker d t I).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (show Function.Surjective (normalAssociatedSymbolAlgHom d t I) from by
          intro z
          obtain ⟨P, hP⟩ := normalAssociatedSymbolMap_surjective d t I z
          exact ⟨P, (normalAssociatedSymbolAlgHom_apply d t I P).trans hP⟩))

/-- Every original polynomial numerator retains exactly its pre-existing entire original symbol. -/
theorem originalNormalAssociatedGradedQuotientAlgEquiv_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    originalNormalAssociatedGradedQuotientAlgEquiv d t I
      (Ideal.Quotient.mk (originalNormalInitialIdeal d t I) P) = normalAssociatedSymbolMap d t I P := by
  let := tangentAlgebra d t
  exact normalAssociatedSymbolAlgHom_apply d t I P

/-- The algebra dictionary has exactly the old literal original quotient-module dictionary. -/
theorem originalNormalAssociatedGradedQuotientAlgEquiv_toLinearEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    (originalNormalAssociatedGradedQuotientAlgEquiv d t I).toLinearEquiv =
      originalNormalAssociatedGradedQuotientEquiv d t I := by
  let := tangentAlgebra d t
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (originalNormalAssociatedGradedQuotientAlgEquiv_mk d t I P).trans
    (originalNormalAssociatedGradedQuotientEquiv_mk d t I P).symm

/-- Every homogeneous polynomial numerator lands in its same actual original degree. -/
theorem originalNormalAssociatedGradedQuotientAlgEquiv_homogeneous (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d)) q) :
    let := tangentAlgebra d t
    originalNormalAssociatedGradedQuotientAlgEquiv d t I
      (Ideal.Quotient.mk (originalNormalInitialIdeal d t I) P.val) =
      DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun k => (originalNormalGradedPiece d t I k : Type)) q
        (homogeneousNormalSymbolMap d t I q P) := by
  let := tangentAlgebra d t
  exact (originalNormalAssociatedGradedQuotientAlgEquiv_mk d t I P.val).trans
    (normalAssociatedSymbolMap_homogeneous d t q I P)

end
end Hironaka.HironakaRelativeNormalGradedAlgebra
