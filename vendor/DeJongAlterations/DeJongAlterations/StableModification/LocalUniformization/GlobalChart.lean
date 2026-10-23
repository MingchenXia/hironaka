import DeJongAlterations.StableModification.Blowups.Transport
import DeJongAlterations.Geometry.NodeFamilySmoothDensityBaseChange
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Strict semi-stability over an open of the base

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (T:2972–2975) replaces the base `R` by its localization beneath the centre. For
the stalk-local base change used here (an open subscheme of `Spec R`, `lem:sm-cofinal-base`)
one needs that a strictly semi-stable curve `g : X → S` stays strictly semi-stable over every open
`S' ⊆ S` (`IsStrictlySemistable.restrictBase`). The charts of `X` live over opens `Spec A ⊆ S`
which need not lie in `S'`; they are shrunk to a basic open `D(c) ⊆ Spec A` inside `S'` and the
standard models are base-changed along `A → A_c` (`smoothModelBaseChangeIso`,
`nodeModelBaseChangeIso`, `exists_etale_smoothModel_baseChange`,
`exists_etale_nodeModel_baseChange`). Blueprint `lem:sm-cofinal-restrict`
(`sm-local-uniformization.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Polynomial
open scoped TensorProduct

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open Curves Blowups Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section BaseChange

variable (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']

/-- The base change of the smooth model: `Spec A[T] ×_A Spec A' ≅ Spec A'[T]`. -/
def smoothModelBaseChangeIso :
    pullback (smoothModel A) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≅
      Spec (.of A'[X]) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A A' A[X] ≪≫
    Scheme.Spec.mapIso (polyEquivTensor' A A').symm.toRingEquiv.toCommRingCatIso.symm.op

/-- The base change isomorphism of the smooth model commutes with the projections. -/
theorem smoothModelBaseChangeIso_hom_comp :
    (smoothModelBaseChangeIso A A').hom ≫ smoothModel A' = pullback.snd _ _ := by
  have h := Geometry.NodeFamilySmoothDensityBaseChange.specAlgEquiv_structure (R := A')
    (S := A' ⊗[A] A[X]) (T := A'[X]) (polyEquivTensor' A A').symm
  dsimp only [smoothModelBaseChangeIso, Iso.trans_hom, smoothModel]
  rw [Category.assoc, Category.assoc, h, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

/-- The base change of the node model:
`Spec A[u,v]/(uv - a) ×_A Spec A' ≅ Spec A'[u,v]/(uv - a)`. -/
def nodeModelBaseChangeIso (a : A) :
    pullback (nodeModel a) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≅
      Spec (.of (Node A' (algebraMap A A' a))) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A A' (Node A a) ≪≫
    Scheme.Spec.mapIso
      (Algebra.NodeFamilyBaseChange.nodeBaseChangeEquiv A' a).toRingEquiv.toCommRingCatIso.symm.op

/-- The base change isomorphism of the node model commutes with the projections. -/
theorem nodeModelBaseChangeIso_hom_comp (a : A) :
    (nodeModelBaseChangeIso A A' a).hom ≫ nodeModel (algebraMap A A' a) = pullback.snd _ _ := by
  have h := Geometry.NodeFamilySmoothDensityBaseChange.specAlgEquiv_structure (R := A')
    (S := A' ⊗[A] Node A a) (T := Node A' (algebraMap A A' a))
    (Algebra.NodeFamilyBaseChange.nodeBaseChangeEquiv A' a)
  dsimp only [nodeModelBaseChangeIso, Iso.trans_hom, nodeModel,
    Geometry.NodeFamilyFlat.nodeMorphism]
  rw [Category.assoc, Category.assoc, h, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

variable {A A'}

/-- **Base change of a smooth chart**: an étale `e : U → Spec A[T]` base-changes along `A → A'` to
an étale map from `U ×_A Spec A'` to `Spec A'[T]` over `Spec A'`. -/
theorem exists_etale_smoothModel_baseChange {U : Scheme.{u}} (e : U ⟶ Spec (.of A[X]))
    [Etale e] :
    ∃ e' : pullback (e ≫ smoothModel A) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⟶
      Spec (.of A'[X]), Etale e' ∧ e' ≫ smoothModel A' = pullback.snd _ _ := by
  refine ⟨(pullbackRightPullbackFstIso (smoothModel A) _ e).inv ≫
    pullback.snd e (pullback.fst (smoothModel A) _) ≫ (smoothModelBaseChangeIso A A').hom,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, smoothModelBaseChangeIso_hom_comp,
    pullbackRightPullbackFstIso_inv_snd_snd]

/-- **Base change of a node chart.** -/
theorem exists_etale_nodeModel_baseChange {U : Scheme.{u}} (a : A)
    (e : U ⟶ Spec (.of (Node A a))) [Etale e] :
    ∃ e' : pullback (e ≫ nodeModel a) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⟶
      Spec (.of (Node A' (algebraMap A A' a))),
      Etale e' ∧ e' ≫ nodeModel (algebraMap A A' a) = pullback.snd _ _ := by
  refine ⟨(pullbackRightPullbackFstIso (nodeModel a) _ e).inv ≫
    pullback.snd e (pullback.fst (nodeModel a) _) ≫ (nodeModelBaseChangeIso A A' a).hom,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, nodeModelBaseChangeIso_hom_comp,
    pullbackRightPullbackFstIso_inv_snd_snd]

end BaseChange

/-- **Strict semi-stability over an open of the base** (`lem:sm-cofinal-restrict`). Let
`(X, ∅)` be strictly semi-stable over `S`, `j : S' → S` an open immersion and `V = g⁻¹(S')`, with
`g' : V → S'` the restriction. Then `(V, ∅)` is strictly semi-stable over `S'`. -/
theorem IsStrictlySemistable.restrictBase {X S S' : Scheme.{u}} {g : X ⟶ S}
    (hg : IsStrictlySemistable g ⊤) (j : S' ⟶ S) [IsOpenImmersion j] (V : X.Opens)
    (hV : (V : Set X) = g ⁻¹' Set.range j) (g' : V.toScheme ⟶ S') (hg' : g' ≫ j = V.ι ≫ g) :
    IsStrictlySemistable g' ⊤ := by
  -- a chart of `V` through every point
  have key : ∀ v : V.toScheme, ∃ (Y : Scheme.{u}) (k : Y ⟶ V.toScheme) (_ : IsOpenImmersion k),
      v ∈ Set.range k ∧ IsStrictlySemistable (k ≫ g') ⊤ := by
    intro v
    obtain ⟨U, hxU, A, _, ι, _, h, hh, hcase⟩ := hg (V.ι v)
    set y₀ : U.toScheme := ⟨V.ι v, hxU⟩
    -- a basic open `D(c) ∋ h y₀` of `Spec A` inside `ι⁻¹(S')`
    have hmem : h y₀ ∈ ι ⁻¹' Set.range j := by
      have hv : V.ι v ∈ (V : Set X) := v.2
      rw [hV] at hv
      change ι (h y₀) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, hh]
      exact hv
    have hopen : IsOpen (ι ⁻¹' Set.range j) :=
      j.isOpenEmbedding.isOpen_range.preimage ι.continuous
    obtain ⟨_, ⟨c, rfl⟩, hcmem', hcsub'⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem hopen
    have hcmem : h y₀ ∈ (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum A)) := hcmem'
    have hcsub : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum A)) ⊆ ι ⁻¹' Set.range j :=
      hcsub'
    let A' := Localization.Away c
    let s : Spec (.of A') ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A A'))
    have : IsOpenImmersion s := IsOpenImmersion.of_isLocalization c
    have hsrange : Set.range s = (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum A)) :=
      PrimeSpectrum.localization_away_comap_range A' c
    -- the open immersion `Spec A_c → S'`
    have hιs : Set.range (s ≫ ι) ⊆ Set.range j := by
      rintro _ ⟨z, rfl⟩
      have hz : s z ∈ (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum A)) :=
        hsrange ▸ ⟨z, rfl⟩
      exact hcsub hz
    let ι' : Spec (.of A') ⟶ S' := IsOpenImmersion.lift j (s ≫ ι) hιs
    have hι' : ι' ≫ j = s ≫ ι := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion ι' := by
      have : IsOpenImmersion (ι' ≫ j) := by rw [hι']; infer_instance
      exact IsOpenImmersion.of_comp ι' j
    -- the chart domain `Y = U ×_{Spec A} Spec A_c` and its open immersion into `V`
    let Y := pullback h s
    have heq : pullback.fst h s ≫ U.ι ≫ g = pullback.snd h s ≫ ι' ≫ j := by
      rw [← hh, ← Category.assoc, pullback.condition, Category.assoc, hι']
    have hYrange : Set.range (pullback.fst h s ≫ U.ι) ⊆ Set.range V.ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι, hV]
      have hy := congrArg (fun φ : Y ⟶ S ↦ φ y) heq
      simp only [Scheme.Hom.comp_apply] at hy
      change g (U.ι (pullback.fst h s y)) ∈ Set.range j
      rw [hy]
      exact ⟨_, rfl⟩
    let k : Y ⟶ V.toScheme := IsOpenImmersion.lift V.ι (pullback.fst h s ≫ U.ι) hYrange
    have hk : k ≫ V.ι = pullback.fst h s ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion k := by
      have : IsOpenImmersion (k ≫ V.ι) := by rw [hk]; infer_instance
      exact IsOpenImmersion.of_comp k V.ι
    have hkg : k ≫ g' = pullback.snd h s ≫ ι' := by
      rw [← cancel_mono j, Category.assoc, hg', ← Category.assoc, hk, Category.assoc, ← hh,
        ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hι']
    refine ⟨Y, k, inferInstance, ?_, ?_⟩
    · obtain ⟨w, hw⟩ : h y₀ ∈ Set.range s := by rw [hsrange]; exact hcmem
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback y₀ w hw.symm
      refine ⟨z, V.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hk, Scheme.Hom.comp_apply, hz1]
      rfl
    · rw [hkg]
      rcases hcase with ⟨e, he, rfl, -⟩ | ⟨a, e, he, rfl, -⟩
      · obtain ⟨e', he', hcomm⟩ := exists_etale_smoothModel_baseChange (A' := A') e
        rw [← hcomm, Category.assoc]
        have h1 : IsStrictlySemistable (e' ≫ smoothModel A') ⊤ := by
          have := (isStrictlySemistable_smoothModel A').etale_comp e'
          rwa [Scheme.IdealSheafData.comap_top] at this
        exact Blowups.IsStrictlySemistable.comp_isOpenImmersion h1 ι'
      · obtain ⟨e', he', hcomm⟩ := exists_etale_nodeModel_baseChange (A' := A') a e
        rw [← hcomm, Category.assoc]
        have h1 : IsStrictlySemistable (e' ≫ nodeModel (algebraMap A A' a)) ⊤ := by
          have := (isStrictlySemistable_nodeModel (algebraMap A A' a)).etale_comp e'
          rwa [Scheme.IdealSheafData.comap_top] at this
        exact Blowups.IsStrictlySemistable.comp_isOpenImmersion h1 ι'
  choose Y k hk hmem hss using key
  refine IsStrictlySemistable.of_isOpenImmersion_cover k (fun v ↦ ⟨v, hmem v⟩) fun v ↦ ?_
  rw [Scheme.IdealSheafData.comap_top]
  exact hss v

end DeJongAlterations.StableModification.LocalUniformization
