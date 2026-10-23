/-
Adapted from StacksAndModuli/API/SurjectiveAdicCompletion.lean, commit
b3699d1342bfd3344b69d5299bf4b905c1e40afb.
SHA256: c3f80de869ce1b5fd9266282cb51517c3bdf719d358a735c5de07a34e3224280.
Original Lean code: StacksAndModuli contributors, Apache License 2.0.
Modified for DeJongAlterations: omit the local-ring specialization, use only
local Mathlib and the local transport module (Lean 4.33.1), and add the
actual quotient algebra isomorphism. No external dependency is imported.
The Apache License 2.0 is reproduced in AdicCompletionTransport.lean.
-/
import DeJongAlterations.Algebra.AdicCompletionTransport
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Actual ring maps on adic completions and completion of a quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AdicCompletion

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The `A`-submodule filtration on an `A`-algebra is the restriction of the
ideal filtration defined by the extended ideal. -/
lemma pow_smul_top_eq_restrictScalars_map (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A B)) =
      ((I.map (algebraMap A B)) ^ n : Ideal B).restrictScalars A := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]

/-- The quotient map at level `n` induced by an algebra map. -/
def quotientMapOfAlgebraMap (I : Ideal A) (n : ℕ) :
    A ⧸ (I ^ n • (⊤ : Ideal A)) →+*
      B ⧸ ((I.map (algebraMap A B)) ^ n • (⊤ : Ideal B)) :=
  Ideal.quotientMap _ (algebraMap A B) (by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] using
      (Ideal.le_comap_map : I ^ n ≤
        Ideal.comap (algebraMap A B)
          (Ideal.map (algebraMap A B) (I ^ n))))

/-- The levelwise quotient map sends a residue class to the residue class of
its image. -/
@[simp]
lemma quotientMapOfAlgebraMap_mk (I : Ideal A) (n : ℕ) (a : A) :
    quotientMapOfAlgebraMap I n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap A B a) := by
  exact Ideal.quotientMap_mk

/-- The levelwise quotient maps commute with the transition maps defining the
adic completions. -/
lemma transitionMap_quotientMapOfAlgebraMap (I : Ideal A) {m n : ℕ}
    (hmn : m ≤ n) (a : A ⧸ (I ^ n • (⊤ : Ideal A))) :
    transitionMap (I.map (algebraMap A B)) B hmn
        (quotientMapOfAlgebraMap I n a) =
      quotientMapOfAlgebraMap I m (transitionMap I A hmn a) := by
  induction a using Quotient.inductionOn' with
  | _ a => rfl

/-- An algebra map induces a ring map from the `I`-adic completion to the
completion for the extended ideal. -/
def mapRingHom (I : Ideal A) :
    AdicCompletion I A →+*
      AdicCompletion (I.map (algebraMap A B)) B where
  toFun a :=
    ⟨fun n ↦ quotientMapOfAlgebraMap I n (a.val n), fun {_ _} hmn ↦ by
      rw [transitionMap_quotientMapOfAlgebraMap, a.property hmn]⟩
  map_one' := by
    ext n
    exact (quotientMapOfAlgebraMap (B := B) I n).map_one
  map_mul' a b := by
    ext n
    exact (quotientMapOfAlgebraMap (B := B) I n).map_mul
      (a.val n) (b.val n)
  map_zero' := by
    ext n
    exact (quotientMapOfAlgebraMap (B := B) I n).map_zero
  map_add' a b := by
    ext n
    exact (quotientMapOfAlgebraMap (B := B) I n).map_add
      (a.val n) (b.val n)

/-- Evaluation of the map on completions is the corresponding finite-level
quotient map. -/
@[simp]
lemma mapRingHom_val (I : Ideal A) (a : AdicCompletion I A) (n : ℕ) :
    (mapRingHom (B := B) I a).val n =
      quotientMapOfAlgebraMap (B := B) I n (a.val n) :=
  rfl

/-- The map on completions commutes with the canonical maps from the original
rings. -/
@[simp]
lemma mapRingHom_of (I : Ideal A) (a : A) :
    mapRingHom (B := B) I (AdicCompletion.of I A a) =
      AdicCompletion.of (I.map (algebraMap A B)) B
        (algebraMap A B a) := by
  ext n
  exact quotientMapOfAlgebraMap_mk I n a

/-- Vanishing after the ring map to the extended-ideal completion is equivalent
to vanishing after the ordinary module completion map. -/
lemma quotientMapOfAlgebraMap_eq_zero_iff (I : Ideal A) (n : ℕ)
    (a : A ⧸ (I ^ n • (⊤ : Submodule A A))) :
    quotientMapOfAlgebraMap (B := B) I n a = 0 ↔
      (Algebra.linearMap A B).reduceModIdeal (I ^ n) a = 0 := by
  induction a using Quotient.inductionOn' with
  | _ a =>
      simp only [Submodule.Quotient.mk''_eq_mk]
      have hmk : quotientMapOfAlgebraMap (B := B) I n
          (Submodule.Quotient.mk a) =
          Ideal.Quotient.mk _ (algebraMap A B a) := by
        rw [Ideal.Quotient.mk_eq_mk]
        exact quotientMapOfAlgebraMap_mk I n a
      rw [hmk, Ideal.Quotient.eq_zero_iff_mem,
        LinearMap.reduceModIdeal_apply,
        Submodule.Quotient.mk_eq_zero]
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      change algebraMap A B a ∈ (I.map (algebraMap A B)) ^ n ↔
        algebraMap A B a ∈ (I ^ n • (⊤ : Submodule A B))
      exact (SetLike.ext_iff.mp (pow_smul_top_eq_restrictScalars_map
        (A := A) (B := B) I n) (algebraMap A B a)).symm

/-- The ring map on completions and the module completion map have the same
kernel. -/
lemma mapRingHom_eq_zero_iff_map (I : Ideal A) (a : AdicCompletion I A) :
    mapRingHom (B := B) I a = 0 ↔
      AdicCompletion.map I (Algebra.linearMap A B) a = 0 := by
  constructor
  · intro h
    ext n
    have hn := congrArg (fun x ↦ x.val n) h
    rw [mapRingHom_val, val_zero_apply,
      quotientMapOfAlgebraMap_eq_zero_iff] at hn
    exact hn
  · intro h
    ext n
    have hn := congrArg (fun x ↦ x.val n) h
    rw [AdicCompletion.map_val_apply, val_zero_apply] at hn
    rw [mapRingHom_val, val_zero_apply,
      quotientMapOfAlgebraMap_eq_zero_iff]
    exact hn

section Surjective

variable (I : Ideal A) (hf : Function.Surjective (algebraMap A B))
  (b : AdicCauchySequence (I.map (algebraMap A B)) B)

/-- One inductive lifting step for a Cauchy sequence through a surjective algebra
map, chosen compatibly modulo the `n`-th power of the adic ideal. -/
noncomputable def cauchyPreimageStep (n : ℕ)
    (a : {a : A // algebraMap A B a = b n}) :
    {a' : A // algebraMap A B a' = b (n + 1) ∧
      (a : A) ≡ a' [SMOD (I ^ n • (⊤ : Submodule A A))]} := by
  let r : A := (hf (b (n + 1))).choose
  have hr : algebraMap A B r = b (n + 1) :=
    (hf (b (n + 1))).choose_spec
  have hd : algebraMap A B ((a : A) - r) ∈
      (I ^ n).map (algebraMap A B) := by
    rw [map_sub, a.property, hr, Ideal.map_pow]
    simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using
      b.property (Nat.le_succ n)
  let hcdata :=
    (Ideal.mem_map_iff_of_surjective (algebraMap A B) hf).mp hd
  let c : A := hcdata.choose
  have hc : c ∈ I ^ n := hcdata.choose_spec.1
  have hfc : algebraMap A B c = algebraMap A B ((a : A) - r) :=
    hcdata.choose_spec.2
  refine ⟨(a : A) - c, ?_, ?_⟩
  · rw [map_sub, hfc, map_sub, a.property, hr]
    abel
  · rw [SModEq.sub_mem]
    simpa [Ideal.smul_eq_mul] using hc

/-- Compatible chosen preimages of all terms of a Cauchy sequence under a
surjective algebra map. -/
noncomputable def cauchyPreimage :
    (n : ℕ) → {a : A // algebraMap A B a = b n}
  | 0 => ⟨(hf (b 0)).choose, (hf (b 0)).choose_spec⟩
  | n + 1 =>
      ⟨cauchyPreimageStep I hf b n (cauchyPreimage n),
        (cauchyPreimageStep I hf b n (cauchyPreimage n)).property.1⟩

/-- Consecutive chosen preimages are congruent modulo the prescribed adic
filtration step. -/
lemma cauchyPreimage_smodEq (n : ℕ) :
    (cauchyPreimage I hf b n : A) ≡
      (cauchyPreimage I hf b (n + 1) : A)
        [SMOD (I ^ n • (⊤ : Submodule A A))] := by
  exact (cauchyPreimageStep I hf b n
    (cauchyPreimage I hf b n)).property.2

/-- The Cauchy sequence obtained by lifting a target Cauchy sequence through a
surjective algebra map. -/
noncomputable def cauchySequencePreimage :
    AdicCauchySequence I A :=
  AdicCauchySequence.mk I A
    (fun n ↦ (cauchyPreimage I hf b n : A))
    (cauchyPreimage_smodEq I hf b)

/-- Mapping the lifted Cauchy sequence recovers the original sequence term by
term. -/
lemma cauchySequencePreimage_map (n : ℕ) :
    algebraMap A B (cauchySequencePreimage I hf b n) = b n :=
  (cauchyPreimage I hf b n).property

include hf

/-- If the original ring map is surjective, the induced ring map on adic
completions is surjective. -/
theorem mapRingHom_surjective :
    Function.Surjective (mapRingHom (B := B) I) := by
  intro y
  obtain ⟨b, rfl⟩ :=
    AdicCompletion.mk_surjective (I.map (algebraMap A B)) B y
  refine ⟨AdicCompletion.mk I A (cauchySequencePreimage I hf b), ?_⟩
  ext n
  simp only [mapRingHom_val, AdicCompletion.mk_apply_coe]
  let a := cauchySequencePreimage I hf b
  change quotientMapOfAlgebraMap (B := B) I n
      (Submodule.Quotient.mk (a n)) = Submodule.Quotient.mk (b n)
  have hmk : quotientMapOfAlgebraMap (B := B) I n
      (Submodule.Quotient.mk (a n)) =
      Ideal.Quotient.mk _ (algebraMap A B (a n)) := by
    rw [Ideal.Quotient.mk_eq_mk]
    exact quotientMapOfAlgebraMap_mk I n (a n)
  rw [hmk, show algebraMap A B (a n) = b n by
    exact cauchySequencePreimage_map I hf b n]
  exact (Ideal.Quotient.mk_eq_mk (b n)).symm

end Surjective

section Kernel

variable [IsNoetherianRing A]

/-- The range of the completed inclusion of the original kernel is contained
in the extended kernel ideal. -/
lemma range_map_ker_le_idealMap (I : Ideal A) :
    LinearMap.range (AdicCompletion.map I
      (LinearMap.ker (Algebra.linearMap A B)).subtype) ≤
      ((RingHom.ker (algebraMap A B)).map
        (algebraMap A (AdicCompletion I A)) :
          Ideal (AdicCompletion I A)) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨t, rfl⟩ :=
    AdicCompletion.ofTensorProduct_surjective_of_finite I
      (LinearMap.ker (Algebra.linearMap A B)) x
  rw [show AdicCompletion.map I
      (LinearMap.ker (Algebra.linearMap A B)).subtype
        (AdicCompletion.ofTensorProduct I _ t) =
      AdicCompletion.ofTensorProduct I A
        (TensorProduct.AlgebraTensorModule.map LinearMap.id
          (LinearMap.ker (Algebra.linearMap A B)).subtype t) by
    exact LinearMap.congr_fun
      (AdicCompletion.ofTensorProduct_naturality I
        (LinearMap.ker (Algebra.linearMap A B)).subtype) t]
  induction t with
  | zero =>
      simp
  | tmul c a =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul,
        LinearMap.id_apply, AdicCompletion.ofTensorProduct_tmul]
      rw [smul_eq_mul]
      apply Ideal.mul_mem_left
      apply Ideal.mem_map_of_mem
      rw [RingHom.mem_ker]
      exact a.property
  | add x y hx hy =>
      simpa only [map_add] using Ideal.add_mem _ hx hy

/-- Over a Noetherian source, the kernel of the completed map is exactly the
extension of the original kernel. -/
theorem ker_mapRingHom_eq_idealMap (I : Ideal A)
    (hf : Function.Surjective (algebraMap A B)) :
    RingHom.ker (mapRingHom (B := B) I) =
      (RingHom.ker (algebraMap A B)).map
        (algebraMap A (AdicCompletion I A)) := by
  apply le_antisymm
  · intro x hx
    have hxzero : mapRingHom (B := B) I x = 0 := hx
    have hxmap : AdicCompletion.map I (Algebra.linearMap A B) x = 0 :=
      (mapRingHom_eq_zero_iff_map I x).mp hxzero
    have hexact : Function.Exact
        (AdicCompletion.map I
          (LinearMap.ker (Algebra.linearMap A B)).subtype)
        (AdicCompletion.map I (Algebra.linearMap A B)) :=
      AdicCompletion.map_exact
        (Submodule.injective_subtype _)
        (Algebra.linearMap A B).exact_subtype_ker_map
        hf
    exact range_map_ker_le_idealMap I ((hexact x).mp hxmap)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change mapRingHom (B := B) I
      (AdicCompletion.of I A a) = 0
    rw [mapRingHom_of, RingHom.mem_ker.mp ha]
    exact (AdicCompletion.of (I.map (algebraMap A B)) B).map_zero

end Kernel


/-- The actual ring map on completions preserves the original coefficient ring. -/
def mapAlgHom (I : Ideal A) :
    AdicCompletion I A →ₐ[A] AdicCompletion (I.map (algebraMap A B)) B :=
  { mapRingHom I with
    commutes' := fun a => by
      rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      exact mapRingHom_of I a }

/-- The actual completion of a quotient is the quotient of the actual completion. -/
def quotientAlgEquiv [IsNoetherianRing A] (I J : Ideal A) :
    ((AdicCompletion I A) ⧸ J.map (algebraMap A (AdicCompletion I A))) ≃ₐ[A]
      AdicCompletion (I.map (Ideal.Quotient.mk J)) (A ⧸ J) := by
  have hk : RingHom.ker (mapAlgHom (B := A ⧸ J) I).toRingHom =
      J.map (algebraMap A (AdicCompletion I A)) := by
    change RingHom.ker (mapRingHom (B := A ⧸ J) I) = _
    rw [ker_mapRingHom_eq_idealMap I Ideal.Quotient.mk_surjective]
    rw [show algebraMap A (A ⧸ J) = Ideal.Quotient.mk J from rfl, Ideal.mk_ker]
  exact (Ideal.quotientEquivAlgOfEq A hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := mapAlgHom (B := A ⧸ J) I)
      (mapRingHom_surjective I Ideal.Quotient.mk_surjective))

@[simp]
theorem quotientAlgEquiv_of [IsNoetherianRing A] (I J : Ideal A) (a : A) :
    quotientAlgEquiv I J (Ideal.Quotient.mk _ (AdicCompletion.of I A a)) =
      AdicCompletion.of (I.map (Ideal.Quotient.mk J)) (A ⧸ J) (Ideal.Quotient.mk J a) := by
  change mapRingHom (B := A ⧸ J) I (AdicCompletion.of I A a) = _
  exact mapRingHom_of I a

end AdicCompletion
