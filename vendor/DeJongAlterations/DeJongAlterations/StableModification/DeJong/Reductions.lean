import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.StableModification.DeJong.Dimension
import DeJongAlterations.Geometry.NormalProjectiveReduction
import DeJongAlterations.Geometry.QuasiProjectiveCompactification

/-!
# Dimension-indexed reductions of de Jong 4.1 to the normal projective Cartier case

de Jong 4.4–4.10 (`dejong96-alterations:page-0017`, `page-0018`) reduce Theorem 4.1 for a
pair `(X, Z)` to the case where `X` is a normal projective variety and `Z` is the support of
an effective Cartier divisor. Every step replaces `X` by an alteration (4.6 Chow, 4.8 the
blowup in `Z`, 4.10 the normalization) or by a projective compactification in which `X` is
dense open (4.7), so the dimension is unchanged (`Dimension.lean`). Codex's packaged
reductions (`Geometry.ProjectiveReduction.reduce_to_projective_cartier_case`,
`Geometry.NormalProjectiveReduction.reduce_normal_projective_cartier_case`) assume the
Cartier case for all varieties; inside the induction on `d = dim X` (de Jong 4.3) the Cartier
case is available only up to dimension `d`, so the same producers are re-chained here with
dimension bookkeeping.

## Main results

* `cartierCase_of_normal`: `CartierCaseUpTo k d` gives the projective Cartier case without
  normality (4.10).
* `projectiveCase_of_cartierCaseUpTo`: the projective case with arbitrary proper closed
  boundary (4.8, 4.9).
* `theoremUpTo_of_cartierCaseUpTo`: `CartierCaseUpTo k d → TheoremUpTo k d` (4.6, 4.7).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

open Geometry


variable {k : Type u} [Field k]

/-- de Jong 4.10 with dimension bookkeeping: the normal projective Cartier case up to
dimension `d` gives the projective Cartier case up to dimension `d`, via the normalization. -/
theorem cartierCase_of_normal {d : ℕ} (h : CartierCaseUpTo k d)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ d) (D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤) :
    Nonempty (AlterationWithBoundary p (D.support : Set X)) := by
  obtain ⟨hv, hproj, hn, -, hm, -, hE, hEp⟩ :=
    NormalProjectiveReduction.normalization_preparation p hp D hD hproper
  let : IsModification (NormalizationGluing.normalizationStructure X) := hm
  have hdimN : topologicalKrullDim (NormalizationGluing.normalization X) ≤ d := by
    rw [topologicalKrullDim_eq_of_isModification p
      (NormalizationGluing.normalizationStructure X)]
    exact hdim
  obtain ⟨e⟩ := h (NormalizationGluing.normalization X)
    (NormalizationGluing.normalizationStructure X ≫ p) hv hproj hn hdimN
    (D.comap (NormalizationGluing.normalizationStructure X)) hE hEp
  exact ⟨ProjectiveReduction.compOutput (NormalizationGluing.normalizationStructure X)
    (by simp only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]) e⟩

/-- de Jong 4.8 with dimension bookkeeping: the normal projective Cartier case up to
dimension `d` gives 4.1 for projective varieties of dimension at most `d`, via the blowup in
the reduced boundary. -/
theorem projectiveCase_of_cartierCaseUpTo {d : ℕ} (h : CartierCaseUpTo k d)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ d) (Z : Closeds X) (hZ : Z ≠ ⊤) :
    Nonempty (AlterationWithBoundary p (Z : Set X)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨Y, f, E, hproj, hf, _hge, hE, hs⟩ :=
    BlowupProjective.exists_projective_genericallyEtale_alteration_cartierPreimage p hp Z hZ
  let := hf
  let : IsIntegral Y := hf.sourceIntegral
  have hv : IsVariety (f ≫ p) := {}
  have hproper : E.support ≠ ⊤ := by
    rw [hs]
    exact ProjectiveReduction.alteration_preimage_ne_top f Z hZ
  have hdimY : topologicalKrullDim Y ≤ d := by
    rw [topologicalKrullDim_eq_of_isAlteration p f]
    exact hdim
  obtain ⟨e⟩ := cartierCase_of_normal h (f ≫ p) hproj hdimY E hE hproper
  have hset : (E.support : Set Y) = f ⁻¹' (Z : Set X) :=
    congrArg (fun W : Closeds Y => (W : Set Y)) hs
  exact ⟨ProjectiveReduction.compOutput f hset e⟩

/-- de Jong 4.6 and 4.7 with dimension bookkeeping (IF-3, `thm:sm-dj-reduce-dim`): the
normal projective Cartier case up to dimension `d` implies Theorem 4.1 for all varieties of
dimension at most `d`. -/
theorem theoremUpTo_of_cartierCaseUpTo {d : ℕ} (h : CartierCaseUpTo k d) :
    TheoremUpTo k d := by
  intro X p hp hdim Z hZ
  let := hp
  obtain ⟨Y, π, hπ, hv, hqp⟩ := ChowLemma.exists_quasiProjective_modification p
  let := hπ
  let := hv
  let W := Z.preimage π.continuous
  have hW : W ≠ ⊤ := ProjectiveReduction.alteration_preimage_ne_top π Z hZ
  obtain ⟨Yb, q, j, Db, hq, hproj, hj, _hdom, hbase, hsupport, hcomap, hproper⟩ :=
    QuasiProjectiveCompactification.exists_compactification_with_boundary (π ≫ p) hqp W
  let := hj
  let := hq
  have hdimY : topologicalKrullDim Y ≤ d := by
    rw [topologicalKrullDim_eq_of_isModification p π]
    exact hdim
  have hdimYb : topologicalKrullDim Yb ≤ d := by
    rw [← FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion q j]
    exact hdimY
  obtain ⟨e⟩ := projectiveCase_of_cartierCaseUpTo h q hproj hdimYb Db.support (hproper hW)
  have hpre : j ⁻¹' (Db.support : Set Yb) = (W : Set Y) := by
    simpa only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] using
      congrArg (fun T : Closeds Y => (T : Set Y)) hcomap
  have hdiscard : (Set.range j)ᶜ ⊆ (Db.support : Set Yb) := by
    intro y hy
    rw [hsupport]
    exact Or.inr hy
  exact ⟨ProjectiveReduction.compOutput π rfl
    (QuasiProjectiveCompactification.restrictToOriginal j hbase hpre hdiscard e)⟩

/-- `TheoremUpTo` is monotone in the dimension bound. -/
theorem TheoremUpTo.mono {d e : ℕ} (h : TheoremUpTo k e) (hde : d ≤ e) : TheoremUpTo k d :=
  fun X p hp hdim Z hZ ↦ h X p hp (hdim.trans (by exact_mod_cast hde)) Z hZ

/-- The Cartier case is a special case of the theorem. -/
theorem TheoremUpTo.cartierCaseUpTo {d : ℕ} (h : TheoremUpTo k d) : CartierCaseUpTo k d :=
  fun X p hp _ _ hdim D _ hD ↦ h X p hp hdim D.support hD

end DeJongAlterations.StableModification.DeJong
