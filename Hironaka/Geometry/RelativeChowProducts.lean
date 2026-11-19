import Hironaka.Geometry.RelativeChowProjectiveSpace
import Hironaka.Geometry.Segre

/-!
# Actual relative Segre embeddings and finite projective products

The native product of two actual relative projective spaces is identified
by its actual pullback universal properties with the native base change
of their integer-coefficient product. Base change of the actual Segre
closed immersion gives the actual relative Segre closed immersion.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (S : Scheme.{u}) (m n : ℕ)

/-- The actual product of the two relative projective spaces over the original base. -/
abbrev relativeProduct := pullback (relativeStructure S m) (relativeStructure S n)

/-- The native base change of the actual integer Segre source. -/
abbrev integerProductBaseChange :=
  pullback (integerStructure S)
    (Segre.segre IntegerRing m n ≫ projectiveSpaceStructure IntegerRing
      (Algebra.Segre.dimension m n))

/-- The actual integer-coordinate pair of a point of the native relative product. -/
def productIntegerMap : relativeProduct S m n ⟶ Segre.projectiveProduct IntegerRing m n :=
  pullback.lift
    (pullback.fst _ _ ≫ integerProjection S m)
    (pullback.snd _ _ ≫ integerProjection S n)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The actual comparison of native product and native base change. -/
def productBaseChangeHom : relativeProduct S m n ⟶ integerProductBaseChange S m n :=
  pullback.lift (pullback.fst _ _ ≫ relativeStructure S m)
    (productIntegerMap S m n) (specULiftZIsTerminal.hom_ext _ _)

/-- The actual inverse comparison is constructed using all four native projections. -/
def productBaseChangeInv : integerProductBaseChange S m n ⟶ relativeProduct S m n :=
  pullback.lift
    (pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ pullback.fst _ _) (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ pullback.snd _ _) (specULiftZIsTerminal.hom_ext _ _))
    (by simp [relativeStructure])

/-- The actual product/base-change isomorphism, with both inverse laws proved
from the actual native projections rather than supplied by a caller. -/
def productBaseChangeIso : relativeProduct S m n ≅ integerProductBaseChange S m n where
  hom := productBaseChangeHom S m n
  inv := productBaseChangeInv S m n
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [productBaseChangeHom, productBaseChangeInv, productIntegerMap,
          relativeStructure, integerProjection, Category.assoc]
    · apply pullback.hom_ext
      · simp [productBaseChangeHom, productBaseChangeInv,
          relativeStructure, Category.assoc, pullback.condition]
      · simp [productBaseChangeHom, productBaseChangeInv, productIntegerMap,
          integerProjection, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [productBaseChangeHom, productBaseChangeInv, relativeStructure, Category.assoc]
    · apply pullback.hom_ext <;>
        simp [productBaseChangeHom, productBaseChangeInv, productIntegerMap,
          integerProjection, Category.assoc]

/-- The actual base change of the native integer-coefficient Segre closed immersion. -/
def segreBaseChange : integerProductBaseChange S m n ⟶
    relativeSpace S (Algebra.Segre.dimension m n) :=
  pullback.map (integerStructure S)
    (Segre.segre IntegerRing m n ≫
      projectiveSpaceStructure IntegerRing (Algebra.Segre.dimension m n))
    (integerStructure S) (projectiveSpaceStructure IntegerRing (Algebra.Segre.dimension m n))
    (𝟙 S) (Segre.segre IntegerRing m n) (𝟙 _)
    (by simp) (by simp)

instance segreBaseChange_isClosedImmersion :
    IsClosedImmersion (segreBaseChange S m n) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
    (by simp) (by simp)

/-- The actual native relative Segre morphism. -/
def relativeSegre : relativeProduct S m n ⟶ relativeSpace S (Algebra.Segre.dimension m n) :=
  (productBaseChangeIso S m n).hom ≫ segreBaseChange S m n

instance relativeSegre_isClosedImmersion : IsClosedImmersion (relativeSegre S m n) := by
  unfold relativeSegre
  infer_instance

@[reassoc (attr := simp)]
theorem relativeSegre_structure :
    relativeSegre S m n ≫ relativeStructure S (Algebra.Segre.dimension m n) =
      pullback.fst _ _ ≫ relativeStructure S m := by
  simp [relativeSegre, segreBaseChange, productBaseChangeIso,
    productBaseChangeHom, relativeStructure, pullback.map, Category.assoc]

variable {S} {X Y : Scheme.{u}}

/-- Two actual relative closed presentations give a genuine actual product
presentation by the native product embedding followed by native relative Segre. -/
theorem exists_product_embedding
    (p : X ⟶ S) (q : Y ⟶ S)
    (i : X ⟶ relativeSpace S m) (j : Y ⟶ relativeSpace S n)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ relativeStructure S m = p) (hj : j ≫ relativeStructure S n = q) :
    ∃ (d : ℕ) (e : pullback p q ⟶ relativeSpace S d),
      IsClosedImmersion e ∧ e ≫ relativeStructure S d = pullback.fst p q ≫ p := by
  let b : pullback p q ⟶ relativeProduct S m n :=
    pullback.map p q (relativeStructure S m) (relativeStructure S n)
      i j (𝟙 S) (by simpa using hi.symm) (by simpa using hj.symm)
  let : IsClosedImmersion b :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      inferInstance inferInstance hi.symm hj.symm
  refine ⟨Algebra.Segre.dimension m n, b ≫ relativeSegre S m n, inferInstance, ?_⟩
  rw [Category.assoc, relativeSegre_structure, ← Category.assoc]
  simp [b, pullback.map, Category.assoc, hi]

/-- The actual finite product over the original scheme, using native pullbacks. -/
def relativeProductOver (S : Scheme.{u}) : List (Over S) → Over S
  | [] => Over.mk (𝟙 S)
  | A :: L => Over.mk (pullback.fst A.hom (relativeProductOver S L).hom ≫ A.hom)

/-- The actual coordinate projections, preserving each original base map. -/
def relativeProjection :
    (L : List (Over S)) → (i : Fin L.length) → relativeProductOver S L ⟶ L.get i
  | [], i => Fin.elim0 i
  | A :: L, i => Fin.cases
      (Over.homMk (pullback.fst A.hom (relativeProductOver S L).hom) rfl)
      (fun j => Over.homMk (pullback.snd A.hom (relativeProductOver S L).hom)
        pullback.condition.symm ≫ relativeProjection L j) i

/-- The actual simultaneous map into the original finite native product. -/
def relativeLift (Z : Over S) :
    (L : List (Over S)) → (∀ i : Fin L.length, Z ⟶ L.get i) → (Z ⟶ relativeProductOver S L)
  | [], _ => Over.homMk Z.hom (Category.comp_id Z.hom)
  | A :: L, f =>
      let t := relativeLift Z L (fun i => f i.succ)
      Over.homMk (pullback.lift (f 0).left t.left ((f 0).w.trans t.w.symm))
        (by
          change pullback.lift (f 0).left t.left _ ≫
            pullback.fst A.hom (relativeProductOver S L).hom ≫ A.hom = Z.hom
          rw [pullback.lift_fst_assoc]
          exact (f 0).w)

@[simp]
theorem relativeLift_projection (Z : Over S) (L : List (Over S))
    (f : ∀ i : Fin L.length, Z ⟶ L.get i) (i : Fin L.length) :
    relativeLift Z L f ≫ relativeProjection L i = f i := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons A L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · ext1
      simp [relativeLift, relativeProjection]
    · ext1
      simpa [relativeLift, relativeProjection, Over.comp_left, Category.assoc] using
        congrArg (fun h => h.left) (ih (fun k => f k.succ) j)

/-- The actual indexed finite product over the original scheme. -/
def relativeIndexedProduct {r : ℕ} (A : Fin r → Over S) : Over S :=
  relativeProductOver S (List.ofFn A)

/-- Its actual indexed coordinate morphism. -/
def relativeIndexedProjection {r : ℕ} (A : Fin r → Over S) (i : Fin r) :
    relativeIndexedProduct A ⟶ A i :=
  relativeProjection (List.ofFn A) ⟨i.val, by simp⟩ ≫ eqToHom (by simp)

/-- Its actual simultaneous morphism. -/
def relativeIndexedLift {r : ℕ} (Z : Over S) (A : Fin r → Over S)
    (f : ∀ i, Z ⟶ A i) : Z ⟶ relativeIndexedProduct A :=
  relativeLift Z (List.ofFn A)
    (fun i => f ⟨i.val, by simpa using i.isLt⟩ ≫ eqToHom (by simp))

@[simp]
theorem relativeIndexedLift_projection {r : ℕ} (Z : Over S) (A : Fin r → Over S)
    (f : ∀ i, Z ⟶ A i) (i : Fin r) :
    relativeIndexedLift Z A f ≫ relativeIndexedProjection A i = f i := by
  dsimp only [relativeIndexedLift, relativeIndexedProjection]
  rw [← Category.assoc, relativeLift_projection]
  simp

/-- Actual closed projective presentations of every factor produce an
actual closed projective presentation of their native finite product. -/
theorem exists_relativeProductOver_embedding (L : List (Over S))
    (hL : ∀ A ∈ L, ∃ (d : ℕ) (e : A.left ⟶ relativeSpace S d),
      IsClosedImmersion e ∧ e ≫ relativeStructure S d = A.hom) :
    ∃ (d : ℕ) (e : (relativeProductOver S L).left ⟶ relativeSpace S d),
      IsClosedImmersion e ∧ e ≫ relativeStructure S d = (relativeProductOver S L).hom := by
  induction L with
  | nil =>
    let : IsIso (relativeStructure S 0) := relativeZeroStructure_isIso S
    exact ⟨0, inv (relativeStructure S 0), inferInstance, IsIso.inv_hom_id _⟩
  | cons A L ih =>
    obtain ⟨m, i, hi, hpi⟩ := hL A (by simp)
    obtain ⟨n, j, hj, hqj⟩ := ih (fun B hB => hL B (by simp [hB]))
    let := hi
    let := hj
    exact exists_product_embedding m n A.hom (relativeProductOver S L).hom i j hpi hqj

/-- The actual indexed finite product has an internally constructed
relative closed presentation, including the empty indexed product. -/
theorem exists_relativeIndexedProduct_embedding {r : ℕ} (A : Fin r → Over S)
    (hA : ∀ i, ∃ (d : ℕ) (e : (A i).left ⟶ relativeSpace S d),
      IsClosedImmersion e ∧ e ≫ relativeStructure S d = (A i).hom) :
    ∃ (d : ℕ) (e : (relativeIndexedProduct A).left ⟶ relativeSpace S d),
      IsClosedImmersion e ∧ e ≫ relativeStructure S d = (relativeIndexedProduct A).hom := by
  apply exists_relativeProductOver_embedding
  intro B hB
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
  exact hA i

end Hironaka.Geometry.RelativeChow
