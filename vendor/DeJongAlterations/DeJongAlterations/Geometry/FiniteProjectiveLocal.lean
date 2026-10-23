import DeJongAlterations.Geometry.FiniteProjectiveTuple
import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingLocal

/-!
# Whole affine restrictions of the actual twisted generating tuple

Restrictions retain their literal germs, satisfy the genuine whole-ring unit
transition, and generate the entire unit ideal on every subordinate affine open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal BlowupGluing BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n d : ℕ}

/-- Restrict the actual trivialized twisted section to a genuine subordinate affine open. -/
def localValue {g : Y ⟶ projectiveSpace R n} (s : TwistedSection g d)
    (U : Y.affineOpens) (i : Fin (n + 1)) (hi : U.1 ≤ chartOpen g i) : Γ(Y, U.1) :=
  Y.presheaf.map (homOfLE hi).op (s.val i)

/-- The original germ is retained by the actual restriction. -/
theorem localValue_germ {g : Y ⟶ projectiveSpace R n} (s : TwistedSection g d)
    (U : Y.affineOpens) (i : Fin (n + 1)) (hi : U.1 ≤ chartOpen g i)
    (x : Y) (hx : x ∈ U.1) :
    Y.presheaf.germ U.1 x hx (localValue s U i hi) =
      Y.presheaf.germ (chartOpen g i) x (hi hx) (s.val i) :=
  Y.presheaf.germ_res_apply (homOfLE hi) x hx (s.val i)

/-- The original transition ratio restricted to the entire subordinate affine open. -/
def localRatio (g : Y ⟶ projectiveSpace R n) (U : Y.affineOpens)
    (i j : Fin (n + 1)) (hi : U.1 ≤ chartOpen g i) : Γ(Y, U.1) :=
  localValue (coordinateTwisted g j) U i hi

/-- Actual twisted transition holds in the entire affine section ring. -/
theorem localValue_transition {g : Y ⟶ projectiveSpace R n} (s : TwistedSection g d)
    (U : Y.affineOpens) (i j : Fin (n + 1))
    (hi : U.1 ≤ chartOpen g i) (hj : U.1 ≤ chartOpen g j) :
    localValue s U i hi = localValue s U j hj * localRatio g U i j hi ^ d := by
  apply TopCat.Presheaf.section_ext Y.sheaf U.1
  intro x hx
  change Y.presheaf.germ U.1 x hx (localValue s U i hi) =
    Y.presheaf.germ U.1 x hx (localValue s U j hj * localRatio g U i j hi ^ d)
  simp only [map_mul, map_pow, localRatio, localValue_germ, coordinateTwisted]
  exact s.compatible i j x (hi hx) (hj hx)

/-- The actual transition ratio is a genuine unit on the whole common affine open. -/
theorem localRatio_isUnit (g : Y ⟶ projectiveSpace R n) (U : Y.affineOpens)
    (i j : Fin (n + 1)) (hi : U.1 ≤ chartOpen g i) (hj : U.1 ≤ chartOpen g j) :
    IsUnit (localRatio g U i j hi) := by
  apply AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ Y.toSheafedSpace U.1
  intro x hx
  rw [localRatio, localValue_germ]
  change IsUnit (Y.presheaf.germ (chartOpen g i) x (hi hx) (chartRatio g i j))
  rw [chartRatio, chartForm_germ]
  exact ((nativeFormSection_X_unit_iff i j (g x) (hi hx)).mpr (hj hx)).map (g.stalkMap x).hom

/-- Actual affine-site restriction preserves every local twisted section. -/
theorem localValue_restrict {g : Y ⟶ projectiveSpace R n} (s : TwistedSection g d)
    {U V : Y.AffineZariskiSite} (h : U ⟶ V) (i : Fin (n + 1))
    (hi : V.1 ≤ chartOpen g i) :
    coefficientMap h (localValue s ⟨V.1, V.2⟩ i hi) =
      localValue s ⟨U.1, U.2⟩ i
        ((Scheme.AffineZariskiSite.toOpens_mono h.le).trans hi) := by
  exact (ConcreteCategory.congr_hom
    (Y.presheaf.map_comp (homOfLE hi).op
      ((Scheme.AffineZariskiSite.toOpensFunctor Y).map h).op) (s.val i)).symm

/-- An original marker remains the unit section on every subordinate affine open. -/
theorem GeneratingTuple.localMarker {p : Y ⟶ Spec (.of R)} {g : Y ⟶ projectiveSpace R n}
    (T : GeneratingTuple p g) (U : Y.affineOpens) (i : Fin (n + 1))
    (hi : U.1 ≤ chartOpen g i) :
    localValue (T.finSections (T.finMarker i)) U i hi = 1 := by
  unfold localValue
  rw [T.finMarker_val, chartRatio_self, one_pow, map_one]

/-- The actual restricted tuple generates the whole unit ideal, including on empty affines. -/
theorem GeneratingTuple.localSpan {p : Y ⟶ Spec (.of R)} {g : Y ⟶ projectiveSpace R n}
    (T : GeneratingTuple p g) (U : Y.affineOpens) (i : Fin (n + 1))
    (hi : U.1 ≤ chartOpen g i) :
    Ideal.span (Set.range (fun a => localValue (T.finSections a) U i hi)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← T.localMarker U i hi]
  exact Ideal.subset_span ⟨T.finMarker i, rfl⟩

end DeJongAlterations.Geometry.FiniteProjective
