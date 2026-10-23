import DeJongAlterations.Geometry.FiniteProjectiveTwisted
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.FiniteType

/-!
# Actual finite generating projective tuples

Finite algebra generators of the actual inverse coordinate charts extend to
compatible sections in one positive degree. The tuple includes the original
coordinate powers, and its actual values generate every entire chart ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n : ℕ}

/-- The actual degree-D coordinate power, in every original trivialization. -/
def coordinatePower (g : Y ⟶ projectiveSpace R n) (i : Fin (n + 1)) (D : ℕ) :
    TwistedSection g D where
  val j := chartRatio g j i ^ D
  compatible j k x hj hk := by
    rw [map_pow, map_pow]
    have h := (coordinateTwisted g i).compatible j k x hj hk
    simp only [coordinateTwisted, pow_one] at h
    rw [h, mul_pow]

/-- A finite collection of original chart sections extends in one positive degree. -/
theorem exists_common_twisted_extensions (g : Y ⟶ projectiveSpace R n) [IsAffineHom g]
    {ι : Type u} [Fintype ι] (i : ι → Fin (n + 1))
    (b : ∀ a, Γ(Y, chartOpen g (i a))) :
    ∃ (D : ℕ), 0 < D ∧ ∃ t : ι → TwistedSection g D, ∀ a, (t a).val (i a) = b a := by
  classical
  choose d s hs using fun a => exists_twisted_extension g (i a) (b a)
  let D := max 1 (Finset.univ.sup d)
  have hd (a : ι) : d a ≤ D :=
    (Finset.le_sup (f := d) (Finset.mem_univ a)).trans (le_max_right _ _)
  refine ⟨D, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _),
    fun a => (s a).raise (i a) D (hd a), ?_⟩
  intro a
  rw [TwistedSection.raise_val_self, hs]

/-- The coefficient map of the original structure morphism on an actual chart. -/
def chartCoefficientMap (p : Y ⟶ Spec (.of R)) (g : Y ⟶ projectiveSpace R n)
    (i : Fin (n + 1)) : R →+* Γ(Y, chartOpen g i) :=
  (p.appLE ⊤ (chartOpen g i) (by simp)).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- Local finite type supplies finite algebra generation on each actual affine chart. -/
theorem chartCoefficientMap_finiteType (p : Y ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    (g : Y ⟶ projectiveSpace R n) [IsAffineHom g] (i : Fin (n + 1)) :
    (chartCoefficientMap p g i).FiniteType := by
  apply (p.finiteType_appLE (isAffineOpen_top _) (chartOpen_isAffine g i) (by simp)).comp
  exact RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2

/-- A real finite tuple, including marker coordinates and entire affine-ring generation. -/
structure GeneratingTuple (p : Y ⟶ Spec (.of R)) (g : Y ⟶ projectiveSpace R n) where
  degree : ℕ
  degree_pos : 0 < degree
  Index : Type u
  indexFintype : Fintype Index
  sections : Index → TwistedSection g degree
  marker : Fin (n + 1) → Index
  marker_val : ∀ i j, (sections (marker i)).val j = chartRatio g j i ^ degree
  generates : ∀ i, letI := (chartCoefficientMap p g i).toAlgebra
    Algebra.adjoin R (Set.range (fun a => (sections a).val i)) = ⊤

attribute [instance] GeneratingTuple.indexFintype

/-- The marker coordinates make the actual finite tuple nonempty. -/
theorem GeneratingTuple.index_card_pos {p : Y ⟶ Spec (.of R)}
    {g : Y ⟶ projectiveSpace R n} (T : GeneratingTuple p g) : 0 < Fintype.card T.Index := by
  let : Nonempty T.Index := ⟨T.marker 0⟩
  exact Fintype.card_pos

/-- The actual target projective dimension of the finite tuple. -/
def GeneratingTuple.dimension {p : Y ⟶ Spec (.of R)}
    {g : Y ⟶ projectiveSpace R n} (T : GeneratingTuple p g) : ℕ := Fintype.card T.Index - 1

/-- Relabel the actual finite nonempty tuple by the native finite projective coordinates. -/
def GeneratingTuple.indexEquiv {p : Y ⟶ Spec (.of R)}
    {g : Y ⟶ projectiveSpace R n} (T : GeneratingTuple p g) :
    T.Index ≃ Fin (T.dimension + 1) :=
  (Fintype.equivFin T.Index).trans (finCongr (Nat.sub_add_cancel T.index_card_pos).symm)

/-- The same actual sections indexed by the genuine native target coordinates. -/
def GeneratingTuple.finSections {p : Y ⟶ Spec (.of R)}
    {g : Y ⟶ projectiveSpace R n} (T : GeneratingTuple p g)
    (a : Fin (T.dimension + 1)) : TwistedSection g T.degree :=
  T.sections (T.indexEquiv.symm a)

/-- The actual output coordinate associated with an original projective coordinate. -/
def GeneratingTuple.finMarker {p : Y ⟶ Spec (.of R)}
    {g : Y ⟶ projectiveSpace R n} (T : GeneratingTuple p g)
    (i : Fin (n + 1)) : Fin (T.dimension + 1) := T.indexEquiv (T.marker i)

/-- Relabeling retains the entire actual coordinate-power marker. -/
theorem GeneratingTuple.finMarker_val {p : Y ⟶ Spec (.of R)}
    {g : Y ⟶ projectiveSpace R n} (T : GeneratingTuple p g) (i j : Fin (n + 1)) :
    (T.finSections (T.finMarker i)).val j = chartRatio g j i ^ T.degree := by
  simp only [GeneratingTuple.finSections, GeneratingTuple.finMarker, Equiv.symm_apply_apply]
  exact T.marker_val i j

/-- Relabeling retains generation of the entire original affine chart algebra. -/
theorem GeneratingTuple.finSections_generate {p : Y ⟶ Spec (.of R)}
    {g : Y ⟶ projectiveSpace R n} (T : GeneratingTuple p g) (i : Fin (n + 1)) :
    letI := (chartCoefficientMap p g i).toAlgebra
    Algebra.adjoin R (Set.range (fun a => (T.finSections a).val i)) = ⊤ := by
  have h : Set.range (fun a => (T.finSections a).val i) =
      Set.range (fun a => (T.sections a).val i) := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨T.indexEquiv.symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨T.indexEquiv a, by simp [GeneratingTuple.finSections]⟩
  rw [h]
  exact T.generates i

/-- The original affine morphism and finite-type coefficient structure internally
produce an actual finite generating projective tuple; no generators are supplied. -/
theorem exists_generatingTuple (p : Y ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    (g : Y ⟶ projectiveSpace R n) [IsAffineHom g] :
    Nonempty (GeneratingTuple p g) := by
  classical
  have hf (i : Fin (n + 1)) : ∃ S : Finset Γ(Y, chartOpen g i),
      letI := (chartCoefficientMap p g i).toAlgebra
      Algebra.adjoin R (S : Set Γ(Y, chartOpen g i)) = ⊤ := by
    let := (chartCoefficientMap p g i).toAlgebra
    let : Algebra.FiniteType R Γ(Y, chartOpen g i) := chartCoefficientMap_finiteType p g i
    exact Algebra.FiniteType.out
  choose S hS using hf
  let B := Σ i : Fin (n + 1), {b : Γ(Y, chartOpen g i) // b ∈ S i}
  obtain ⟨D, hD, t, ht⟩ := exists_common_twisted_extensions g
    (fun a : B => a.1) (fun a : B => a.2.1)
  let T : Fin (n + 1) ⊕ B → TwistedSection g D :=
    Sum.elim (fun i => coordinatePower g i D) t
  refine ⟨⟨D, hD, Fin (n + 1) ⊕ B, inferInstance, T, Sum.inl, fun _ _ => rfl, ?_⟩⟩
  intro i
  let := (chartCoefficientMap p g i).toAlgebra
  apply top_unique
  rw [← hS i]
  apply Algebra.adjoin_mono
  intro b hb
  refine ⟨Sum.inr (⟨i, ⟨b, hb⟩⟩ : B), ?_⟩
  exact ht ⟨i, ⟨b, hb⟩⟩

end DeJongAlterations.Geometry.FiniteProjective
