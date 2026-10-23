import DeJongAlterations.Composition
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Genuine reduced-component common refinements

The source is the actual reduced induced closed subscheme of an actual
irreducible component of the native fibre product. Both comparison
alterations, including their generic finiteness, are produced internally.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.AlterationCommonRefinement

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y₁ Y₂ W : Scheme.{u}}

/-- Quasi-finiteness on one factor forces quasi-finiteness of the opposite
projection of an actual locally quasi-finite map into the fibre product. -/
theorem quasiFiniteAt_fst
    (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) [LocallyOfFiniteType g]
    (j : W ⟶ pullback f g) [LocallyQuasiFinite j]
    (x : W) (hx : g.QuasiFiniteAt ((j ≫ pullback.snd f g) x)) :
    (j ≫ pullback.fst f g).QuasiFiniteAt x := by
  let a := j ≫ pullback.fst f g
  let b := j ≫ pullback.snd f g
  let V := g.quasiFiniteLocus
  let U := b ⁻¹ᵁ V
  have h : a ≫ f = b ≫ g := by
    dsimp [a, b]
    rw [Category.assoc, pullback.condition, Category.assoc]
  let c : U.toScheme ⟶ pullback f (V.ι ≫ g) :=
    pullback.lift (U.ι ≫ a) (b ∣_ V) (by
      rw [Category.assoc, morphismRestrict_ι_assoc, ← h])
  let t : pullback f (V.ι ≫ g) ⟶ pullback f g :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ V.ι) (by
      rw [Category.assoc, pullback.condition])
  have hct : c ≫ t = U.ι ≫ j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, c, t, pullback.lift_fst]
      rfl
    · rw [Category.assoc, show t ≫ pullback.snd f g =
          pullback.snd f (V.ι ≫ g) ≫ V.ι by simp [t],
        ← Category.assoc, show c ≫ pullback.snd f (V.ι ≫ g) = b ∣_ V by simp [c],
        morphismRestrict_ι]
      rfl
  let : LocallyQuasiFinite (c ≫ t) := by rw [hct]; infer_instance
  let : LocallyQuasiFinite c := LocallyQuasiFinite.of_comp c t
  have hca : c ≫ pullback.fst f (V.ι ≫ g) = U.ι ≫ a := by simp [c]
  let : LocallyQuasiFinite (U.ι ≫ a) := by rw [← hca]; infer_instance
  have hxU : x ∈ U := hx
  exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := U.ι) (g := a) (x := ⟨x, hxU⟩)).mp
      ((U.ι ≫ a).quasiFiniteAt ⟨x, hxU⟩)

/-- A proper dominating component of the genuine fibre product has a
generically finite first projection; the finite open is produced internally. -/
theorem first_isGenericallyFinite
    (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) [hf : IsAlteration f] [hg : IsAlteration g]
    (j : W ⟶ pullback f g) [IsIntegral W] [IsClosedImmersion j]
    [IsDominant (j ≫ pullback.snd f g)] :
    IsGenericallyFinite (j ≫ pullback.fst f g) := by
  let := hf.targetIntegral
  let := hf.sourceIntegral
  let := hg.sourceIntegral
  have hx : g.QuasiFiniteAt ((j ≫ pullback.snd f g) (genericPoint W)) := by
    rw [genericPoint_map_of_isDominant (j ≫ pullback.snd f g)]
    exact hg.genericallyFinite.quasiFiniteAt_genericPoint g
  exact isGenericallyFinite_of_quasiFiniteAt_genericPoint _
    (quasiFiniteAt_fst f g j (genericPoint W) hx)

private theorem dominant_of_generic_mem_range
    (a : W ⟶ Y₁) [IsIntegral Y₁]
    (h : genericPoint Y₁ ∈ Set.range a) : IsDominant a := by
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec Y₁).def]
  exact closure_mono (Set.singleton_subset_iff.mpr h)

/-- Two actual alterations have an actual common reduced-component refinement.
No Noetherian, field, component, or generic-finiteness certificate is supplied. -/
theorem exists_common_refinement
    (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) [hf : IsAlteration f] [hg : IsAlteration g] :
    ∃ (W : Scheme.{u}) (a : W ⟶ Y₁) (b : W ⟶ Y₂),
      IsAlteration a ∧ IsAlteration b ∧ a ≫ f = b ≫ g := by
  let := hf.sourceIntegral
  let := hg.sourceIntegral
  let := hf.targetIntegral
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := g) (genericPoint Y₁) (genericPoint Y₂)
    ((genericPoint_map_of_isDominant f).trans (genericPoint_map_of_isDominant g).symm)
  let C : Closeds (pullback f g : Scheme.{u}) :=
    ⟨irreducibleComponent z, isClosed_irreducibleComponent⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  let W := I.subscheme
  let j : W ⟶ pullback f g := I.subschemeι
  let a : W ⟶ Y₁ := j ≫ pullback.fst f g
  let b : W ⟶ Y₂ := j ≫ pullback.snd f g
  let : IsReduced W := ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme C
  let : IrreducibleSpace W :=
    Subtype.irreducibleSpace isIrreducible_irreducibleComponent
  let : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  let w : W := ⟨z, mem_irreducibleComponent⟩
  have ha : a w = genericPoint Y₁ := hz₁
  have hb : b w = genericPoint Y₂ := hz₂
  let : IsDominant a := dominant_of_generic_mem_range a ⟨w, ha⟩
  let : IsDominant b := dominant_of_generic_mem_range b ⟨w, hb⟩
  have haf : IsGenericallyFinite a := first_isGenericallyFinite f g j
  let j' := j ≫ (pullbackSymmetry f g).hom
  have hj' : j' ≫ pullback.fst g f = b := by simp [j', b]
  have hj'' : j' ≫ pullback.snd g f = a := by simp [j', a]
  let : IsDominant (j' ≫ pullback.snd g f) := by rw [hj'']; infer_instance
  have hbf : IsGenericallyFinite b := by
    rw [← hj']
    exact first_isGenericallyFinite g f j'
  let : IsAlteration a := {
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    genericallyFinite := haf }
  let : IsAlteration b := {
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    genericallyFinite := hbf }
  refine ⟨W, a, b, inferInstance, inferInstance, ?_⟩
  dsimp [a, b]
  rw [Category.assoc, pullback.condition, Category.assoc]

/-- An actual finite family of alterations has an actual common alteration,
with actual alteration comparisons and literal triangles. The empty family
uses the identity of the integral base. -/
theorem exists_finite_common_refinement [IsIntegral X] (n : ℕ)
    (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsAlteration (f i)) :
    ∃ (W : Scheme.{u}) (q : W ⟶ X) (a : ∀ i, W ⟶ Y i),
      IsAlteration q ∧ (∀ i, IsAlteration (a i)) ∧ (∀ i, a i ≫ f i = q) := by
  induction n with
  | zero =>
    exact ⟨X, 𝟙 X, fun i => Fin.elim0 i, inferInstance,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨W, q, a, hq, ha, htri⟩ :=
      ih (fun i => Y i.succ) (fun i => f i.succ) (fun i => hf i.succ)
    let := hq
    let := hf 0
    obtain ⟨V, r, s, hr, hs, hrs⟩ := exists_common_refinement q (f 0)
    let := hr
    let := hs
    let b (i : Fin (n + 1)) : V ⟶ Y i :=
      Fin.cases s (fun j => r ≫ a j) i
    refine ⟨V, r ≫ q, b, IsAlteration.comp r q, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hs
      · let := ha j
        exact IsAlteration.comp r (a j)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hrs.symm
      · change (r ≫ a j) ≫ f j.succ = r ≫ q
        rw [Category.assoc, htri]

end DeJongAlterations.Geometry.AlterationCommonRefinement
