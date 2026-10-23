import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.Geometry.ChowLemmaProduct

/-!
# Projectivity in the base step

de Jong's Theorem 4.1 asks for a *projective* regular compactification
(`dejong96-alterations:page-0017`). In the base step 4.22 the family produced by Temkin's
stable modification theorem is projective over `C ×_S S'` (Temkin Thm 1.1,
`semi-stable.tex` l.1713–1716: `ω` is relatively ample), and it is pulled back along
projective alterations of the base. This file proves the projectivity bookkeeping
(`lem:sm-dj-projective-composite`), using Codex's Segre embedding
(`Geometry.ChowLemmaProduct.isProjectiveOver_product`):

* `IsProjectiveOver.comp_isClosedImmersion`: closed subschemes of projective schemes are
  projective;
* `isProjectiveOver_pullback`: a fibre product over a separated base of two projective
  `k`-schemes is projective (it is closed in the product);
* `IsRelativelyProjective.isProjectiveOver`: a relatively projective scheme over a projective
  `k`-scheme is projective (`ℙⁿ_T ⊆ T ×_k ℙⁿ_k` and Segre);
* `IsRelativelyProjective.pullback_snd`: relative projectivity is stable under base change.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [CommRing k] {X Y S T T' : Scheme.{u}}

/-- A closed subscheme of a projective `k`-scheme is projective. -/
theorem IsProjectiveOver.comp_isClosedImmersion {q : Y ⟶ Spec (.of k)}
    (hq : IsProjectiveOver q) (i : X ⟶ Y) [IsClosedImmersion i] : IsProjectiveOver (i ≫ q) := by
  obtain ⟨n, j, hj, hjq⟩ := hq
  let := hj
  exact ⟨n, i ≫ j, inferInstance, by rw [Category.assoc, hjq]⟩

/-- **Fibre products of projective schemes.** If `X` and `Y` are projective over `k` and
`S` is separated over `k`, then `X ×_S Y` is projective over `k`. -/
theorem isProjectiveOver_pullback (f : X ⟶ S) (g : Y ⟶ S) (pS : S ⟶ Spec (.of k))
    [IsSeparated pS] (hX : IsProjectiveOver (f ≫ pS)) (hY : IsProjectiveOver (g ≫ pS)) :
    IsProjectiveOver (pullback.fst f g ≫ f ≫ pS) := by
  have H := (Geometry.ChowLemmaProduct.isProjectiveOver_product (f ≫ pS) (g ≫ pS) hX hY)
  have H' := IsProjectiveOver.comp_isClosedImmersion H (pullback.mapDesc f g pS)
  simpa using H'

/-- **Relatively projective over projective is projective.** -/
theorem IsRelativelyProjective.isProjectiveOver {pT : T ⟶ Spec (.of k)} {f : X ⟶ T}
    (hT : IsProjectiveOver pT) (h : IsRelativelyProjective pT f) :
    IsProjectiveOver (f ≫ pT) := by
  obtain ⟨n, i, hi, rfl⟩ := h
  let := hi
  have H := Geometry.ChowLemmaProduct.isProjectiveOver_product pT (projectiveSpaceStructure k n)
    hT (isProjectiveOver_projectiveSpaceStructure k n)
  simpa using IsProjectiveOver.comp_isClosedImmersion H i

/-- **Base change of relative projectivity.** If `β : X → T` is projective relative to
`pT`, then its base change along `t : T' → T` is projective relative to `t ≫ pT`. -/
theorem IsRelativelyProjective.pullback_snd {pT : T ⟶ Spec (.of k)} {β : X ⟶ T}
    (h : IsRelativelyProjective pT β) (t : T' ⟶ T) :
    IsRelativelyProjective (t ≫ pT) (pullback.snd β t) := by
  obtain ⟨n, i, hi, hiβ⟩ := h
  let := hi
  let P := projectiveSpaceStructure k n
  let m : pullback (t ≫ pT) P ⟶ pullback pT P :=
    pullback.map (t ≫ pT) P pT P t (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hmfst : m ≫ pullback.fst pT P = pullback.fst (t ≫ pT) P ≫ t := by simp [m]
  have hmsnd : m ≫ pullback.snd pT P = pullback.snd (t ≫ pT) P := by simp [m]
  -- the bottom square is cartesian
  have Hbot : IsPullback m (pullback.fst (t ≫ pT) P) (pullback.fst pT P) t := by
    refine IsPullback.of_right (h₁₂ := pullback.snd pT P) (h₂₂ := pT) (v₁₃ := P) ?_ hmfst
      (IsPullback.of_hasPullback pT P).flip
    rw [hmsnd]
    exact (IsPullback.of_hasPullback (t ≫ pT) P).flip
  let i' : Limits.pullback β t ⟶ Limits.pullback (t ≫ pT) P :=
    pullback.lift (pullback.snd β t) (pullback.fst β t ≫ i ≫ pullback.snd pT P) (by
      rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hiβ,
        pullback.condition_assoc])
  have hi'fst : i' ≫ pullback.fst (t ≫ pT) P = pullback.snd β t := pullback.lift_fst _ _ _
  have hsq : pullback.fst β t ≫ i = i' ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hmfst, reassoc_of% hi'fst, hiβ, pullback.condition]
    · rw [Category.assoc, Category.assoc, hmsnd]
      simp [i', P]
  have Htot : IsPullback (pullback.fst β t) (i' ≫ pullback.fst (t ≫ pT) P)
      (i ≫ pullback.fst pT P) t := by
    rw [hi'fst, hiβ]
    exact IsPullback.of_hasPullback β t
  have H := IsPullback.of_bot Htot hsq Hbot
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H hi
  exact ⟨n, i', this, hi'fst⟩

end DeJongAlterations.StableModification.DeJong
