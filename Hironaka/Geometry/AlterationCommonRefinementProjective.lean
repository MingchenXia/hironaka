import Hironaka.Geometry.AlterationCommonRefinement
import Hironaka.Geometry.ChowLemma

/-!
# Actual relative projective common refinements over varieties

The genuine Chow modification of the genuine finite-family component
refinement has an actual closed embedding into the product of the
original base with projective space. Relative projectivity is derived
from the actual pair map, rather than inferred from absolute
quasi-projectivity alone.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.AlterationCommonRefinement

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X W : Scheme.{u}}

/-- An actual quasi-projective immersion and a proper map yield an actual
relative closed projective embedding with its literal first projection. -/
theorem exists_relative_projective_embedding
    (p : X ⟶ Spec (CommRingCat.of R)) (h : W ⟶ X) [IsProper h]
    (hq : IsQuasiProjectiveOver (h ≫ p)) :
    ∃ (n : ℕ) (e : W ⟶ pullback p (projectiveSpaceStructure R n)),
      IsClosedImmersion e ∧ e ≫ pullback.fst _ _ = h := by
  obtain ⟨n, e, he, hbase⟩ := hq
  let := he
  let a := pullback.lift h e hbase.symm
  have ha₁ : a ≫ pullback.fst p (projectiveSpaceStructure R n) = h := by simp [a]
  have ha₂ : a ≫ pullback.snd p (projectiveSpaceStructure R n) = e := by simp [a]
  let : IsImmersion (a ≫ pullback.snd p (projectiveSpaceStructure R n)) := by
    rw [ha₂]
    infer_instance
  let : IsImmersion a :=
    IsImmersion.of_comp a (pullback.snd p (projectiveSpaceStructure R n))
  let : IsProper (a ≫ pullback.fst p (projectiveSpaceStructure R n)) := by
    rw [ha₁]
    infer_instance
  let : IsProper a :=
    IsProper.of_comp a (pullback.fst p (projectiveSpaceStructure R n))
  exact ⟨n, a, IsClosedImmersion.of_isPreimmersion a a.isClosedMap.isClosed_range, ha₁⟩

variable {k : Type u} [Field k]

/-- The actual finite-family field-variety case of source 5.4. The actual
refinement has alteration comparison maps and a genuinely derived relative
closed embedding over the original base. -/
theorem exists_projective_finite_common_refinement
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] (n : ℕ)
    (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsAlteration (f i)) :
    ∃ (W : Scheme.{u}) (q : W ⟶ X) (a : ∀ i, W ⟶ Y i)
      (d : ℕ) (e : W ⟶ pullback p (projectiveSpaceStructure k d)),
      IsAlteration q ∧ (∀ i, IsAlteration (a i)) ∧ (∀ i, a i ≫ f i = q) ∧
      IsVariety (q ≫ p) ∧ IsClosedImmersion e ∧ e ≫ pullback.fst _ _ = q := by
  obtain ⟨V, r, b, hr, hb, htri⟩ := exists_finite_common_refinement n Y f hf
  let := hr
  let := hr.sourceIntegral
  let : IsVariety (r ≫ p) := {}
  obtain ⟨W, π, hπ, hvar, hQP⟩ := ChowLemma.exists_quasiProjective_modification (r ≫ p)
  let := hπ
  let := hvar
  have hq : IsQuasiProjectiveOver ((π ≫ r) ≫ p) := by
    simpa only [Category.assoc] using hQP
  obtain ⟨d, e, he, heq⟩ := exists_relative_projective_embedding p (π ≫ r) hq
  refine ⟨W, π ≫ r, fun i => π ≫ b i, d, e,
    IsAlteration.comp π r, ?_, ?_, ?_, he, heq⟩
  · intro i
    let := hb i
    exact IsAlteration.comp π (b i)
  · intro i
    rw [Category.assoc, htri]
  · simpa only [Category.assoc] using hvar

/-- The two-alteration form, with both actual comparison maps, the actual
common alteration, its exact triangle, and its relative projective embedding. -/
theorem exists_projective_common_refinement
    {Y₁ Y₂ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) [hf : IsAlteration f] [hg : IsAlteration g] :
    ∃ (W : Scheme.{u}) (a : W ⟶ Y₁) (b : W ⟶ Y₂)
      (d : ℕ) (e : W ⟶ pullback p (projectiveSpaceStructure k d)),
      IsAlteration a ∧ IsAlteration b ∧ IsAlteration (a ≫ f) ∧
      a ≫ f = b ≫ g ∧ IsVariety ((a ≫ f) ≫ p) ∧
      IsClosedImmersion e ∧ e ≫ pullback.fst _ _ = a ≫ f := by
  obtain ⟨V, r, s, hr, hs, hrs⟩ := exists_common_refinement f g
  let := hr
  let := hs
  let : IsAlteration (r ≫ f) := IsAlteration.comp r f
  let := hr.sourceIntegral
  let : IsVariety ((r ≫ f) ≫ p) := {}
  obtain ⟨W, π, hπ, hvar, hQP⟩ :=
    ChowLemma.exists_quasiProjective_modification ((r ≫ f) ≫ p)
  let := hπ
  have hq : IsQuasiProjectiveOver (((π ≫ r) ≫ f) ≫ p) := by
    simpa only [Category.assoc] using hQP
  obtain ⟨d, e, he, heq⟩ := exists_relative_projective_embedding p ((π ≫ r) ≫ f) hq
  have ha : IsAlteration (π ≫ r) := IsAlteration.comp π r
  let := ha
  refine ⟨W, π ≫ r, π ≫ s, d, e, ha, IsAlteration.comp π s,
    IsAlteration.comp (π ≫ r) f, ?_, ?_, he, heq⟩
  · rw [Category.assoc, hrs, Category.assoc]
  · simpa only [Category.assoc] using hvar

end Hironaka.Geometry.AlterationCommonRefinement
