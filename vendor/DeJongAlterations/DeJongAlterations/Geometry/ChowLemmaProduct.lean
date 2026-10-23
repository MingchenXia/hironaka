import DeJongAlterations.Geometry.Segre
import DeJongAlterations.Geometry.ProjectiveIdentity
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Data.List.OfFn

/-!
# Actual finite products of projective schemes for the Chow graph construction

The products are native recursive pullbacks over the original coefficient
scheme. Their actual projective presentation is produced from the native
Segre closed immersion, rather than supplied as product data.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace DeJongAlterations.Geometry.ChowLemmaProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- The actual map of native products induced by two actual projective embeddings. -/
def productEmbedding {n m : ℕ}
    (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
    (i : X ⟶ projectiveSpace R n) (j : Y ⟶ projectiveSpace R m)
    (hi : i ≫ projectiveSpaceStructure R n = p)
    (hj : j ≫ projectiveSpaceStructure R m = q) :
    pullback p q ⟶ Segre.projectiveProduct R n m :=
  pullback.map p q (projectiveSpaceStructure R n) (projectiveSpaceStructure R m)
    i j (𝟙 _) (by simpa using hi.symm) (by simpa using hj.symm)

instance productEmbedding_isClosedImmersion {n m : ℕ}
    (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
    (i : X ⟶ projectiveSpace R n) (j : Y ⟶ projectiveSpace R m)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ projectiveSpaceStructure R n = p)
    (hj : j ≫ projectiveSpaceStructure R m = q) :
    IsClosedImmersion (productEmbedding p q i j hi hj) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance hi.symm hj.symm

/-- Binary projectivity is constructed by the actual product closed immersion and native Segre map. -/
theorem isProjectiveOver_product
    (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
    (hp : IsProjectiveOver p) (hq : IsProjectiveOver q) :
    IsProjectiveOver (pullback.fst p q ≫ p) := by
  obtain ⟨n, i, hi, hpi⟩ := hp
  obtain ⟨m, j, hj, hqj⟩ := hq
  let := hi
  let := hj
  refine ⟨Algebra.Segre.dimension n m,
    productEmbedding p q i j hpi hqj ≫ Segre.segre R n m, inferInstance, ?_⟩
  rw [Category.assoc, Segre.segre_structure, ← Category.assoc]
  dsimp [productEmbedding]
  simp only [pullback.map, pullback.lift_fst, Category.assoc, hpi]

/-- The actual finite product, retaining every original coefficient morphism. -/
def productOver (R : Type u) [CommRing R] :
    List (Over (Spec (CommRingCat.of R))) → Over (Spec (CommRingCat.of R))
  | [] => Over.mk (𝟙 _)
  | A :: L => Over.mk (pullback.fst A.hom (productOver R L).hom ≫ A.hom)

/-- Every native coordinate projection retains its actual original coefficient map. -/
def projection :
    (L : List (Over (Spec (CommRingCat.of R)))) →
      (i : Fin L.length) → productOver R L ⟶ L.get i
  | [], i => Fin.elim0 i
  | A :: L, i => Fin.cases
      (Over.homMk (pullback.fst A.hom (productOver R L).hom) rfl)
      (fun j => Over.homMk (pullback.snd A.hom (productOver R L).hom)
        (pullback.condition.symm) ≫ projection L j) i

/-- The actual simultaneous map into the native finite product. -/
def lift (Z : Over (Spec (CommRingCat.of R))) :
    (L : List (Over (Spec (CommRingCat.of R)))) →
      (∀ i : Fin L.length, Z ⟶ L.get i) → (Z ⟶ productOver R L)
  | [], _ => Over.homMk Z.hom (Category.comp_id Z.hom)
  | A :: L, f =>
      let t := lift Z L (fun i => f i.succ)
      Over.homMk (pullback.lift (f 0).left t.left ((f 0).w.trans t.w.symm))
        (by
          change pullback.lift (f 0).left t.left _ ≫
            pullback.fst A.hom (productOver R L).hom ≫ A.hom = Z.hom
          rw [pullback.lift_fst_assoc]
          exact (f 0).w)

/-- The simultaneous native product map has exactly the prescribed coordinate morphisms. -/
@[simp]
theorem lift_projection (Z : Over (Spec (CommRingCat.of R)))
    (L : List (Over (Spec (CommRingCat.of R))))
    (f : ∀ i : Fin L.length, Z ⟶ L.get i) (i : Fin L.length) :
    lift Z L f ≫ projection L i = f i := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons A L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · ext1
      simp [lift, projection]
    · ext1
      simpa [lift, projection, Over.comp_left, Category.assoc] using
        congrArg (fun h => h.left) (ih (fun k => f k.succ) j)

/-- An indexed form of the same actual finite product. -/
def indexedProduct {n : ℕ} (A : Fin n → Over (Spec (CommRingCat.of R))) :
    Over (Spec (CommRingCat.of R)) := productOver R (List.ofFn A)

/-- The actual indexed coordinate projection, with the finite-list reindexing carried internally. -/
def indexedProjection {n : ℕ} (A : Fin n → Over (Spec (CommRingCat.of R))) (i : Fin n) :
    indexedProduct A ⟶ A i :=
  projection (List.ofFn A) ⟨i.val, by simp⟩ ≫
    eqToHom (by simp)

/-- The actual indexed simultaneous map with every coefficient triangle native. -/
def indexedLift {n : ℕ} (Z : Over (Spec (CommRingCat.of R)))
    (A : Fin n → Over (Spec (CommRingCat.of R))) (f : ∀ i, Z ⟶ A i) :
    Z ⟶ indexedProduct A :=
  lift Z (List.ofFn A) (fun i =>
    f ⟨i.val, by simpa using i.isLt⟩ ≫ eqToHom (by simp))

@[simp]
theorem indexedLift_projection {n : ℕ} (Z : Over (Spec (CommRingCat.of R)))
    (A : Fin n → Over (Spec (CommRingCat.of R))) (f : ∀ i, Z ⟶ A i) (i : Fin n) :
    indexedLift Z A f ≫ indexedProjection A i = f i := by
  dsimp only [indexedLift, indexedProjection]
  rw [← Category.assoc, lift_projection]
  simp

/-- Every finite product of actual projective schemes has a constructed native projective presentation. -/
theorem productOver_isProjective
    (L : List (Over (Spec (CommRingCat.of R))))
    (hL : ∀ A ∈ L, IsProjectiveOver A.hom) :
    IsProjectiveOver (productOver R L).hom := by
  induction L with
  | nil => exact ProjectiveIdentity.isProjectiveOver_id_spec R
  | cons A L ih =>
    exact isProjectiveOver_product A.hom (productOver R L).hom
      (hL A (by simp)) (ih (fun B hB => hL B (by simp [hB])))

/-- Indexed actual finite products inherit the constructed projective presentation. -/
theorem indexedProduct_isProjective {n : ℕ}
    (A : Fin n → Over (Spec (CommRingCat.of R))) (hA : ∀ i, IsProjectiveOver (A i).hom) :
    IsProjectiveOver (indexedProduct A).hom := by
  apply productOver_isProjective
  intro B hB
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
  exact hA i

end DeJongAlterations.Geometry.ChowLemmaProduct
