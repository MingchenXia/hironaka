import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceFactorization
import Hironaka.Analytic.Unibranch.SmoothCentreModification

/-!
# Ordinary given smooth windows in the same actual original closed subspace

The full given window map, whole native kernels and actual stalk transports
derive an open immersion into the SAME original analytic-subspace factory.
Ordinary local smooth-centre geometry then gives its native smooth charts.
Blueprint FIRST: `original-analytic-closed-subspace-smooth-centres.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceSmoothCentres

open Hironaka Hironaka.BlowupSequences
  Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction
  HironakaIntrinsicReducedCentreOpenPullback HironakaNativePulledIdealStalk
  SourceReducedComplexSpace OriginalAnalyticClosedSubspaceStalkQuotient
  EmbeddedBlowupOpenRestriction

noncomputable section

variable {X : SourceReducedComplexSpace}

/-- The actual original ambient-open quotient window, followed by the GIVEN chart. -/
def givenWindowMorphism (e : LocalEmbedding X) (O : Opens e.ambient) :
    ofClosedAnalytic ((Subtype.val : O → e.ambient) ⁻¹' e.carrier)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O) ⟶ X :=
  ambientOpenInclusion e.analytic O ≫ EmbeddedBlowupOverlap.chartMorphism e

instance givenWindowMorphism_isOpenImmersion (e : LocalEmbedding X) (O : Opens e.ambient) :
    LocallyRingedSpace.IsOpenImmersion (givenWindowMorphism e O).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    (actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ e.map)
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  infer_instance

/-- The SAME actual contained centre inclusion, followed by the given window map. -/
def givenCentreMorphism (e : LocalEmbedding X) (O : Opens e.ambient)
    (C : Set O) (hC : IsClosedSubmanifold e.dim C)
    (hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier) :
    ofClosedAnalytic C (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC) ⟶ X :=
  OriginalClosedSubspaceFactorization.inclusion
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O) hCW ≫
      givenWindowMorphism e O

/-- Surjectivity of the actual native centre map, not an incoming stalk packet. -/
theorem givenCentreMorphism_stalk_surjective (e : LocalEmbedding X) (O : Opens e.ambient)
    (C : Set O) (hC : IsClosedSubmanifold e.dim C)
    (hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier) (c : C) :
    Function.Surjective ((givenCentreMorphism e O C hC hCW).hom.left.stalkMap c) := by
  let u : actualSubspaceLocallyRingedSpace (n := e.dim) C ⟶
      actualSubspaceLocallyRingedSpace (n := e.dim) ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) :=
    (OriginalClosedSubspaceFactorization.inclusion
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O) hCW).hom.left
  let j : actualSubspaceLocallyRingedSpace (n := e.dim)
      ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) ⟶ X.obj.left :=
    (givenWindowMorphism e O).hom.left
  let : LocallyRingedSpace.IsOpenImmersion j := givenWindowMorphism_isOpenImmersion e O
  have hu : Function.Surjective (u.stalkMap c) :=
    SmoothCentreModification.contained_inclusion_stalk_surjective
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O) hCW c
  have hj : Function.Surjective (j.stalkMap (u.base c)) :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap (u.base c))).2
  change Function.Surjective ((u ≫ j).stalkMap c)
  rw [LocallyRingedSpace.stalkMap_comp]
  exact hu.comp hj

/-- The ENTIRE original intrinsic kernel, from the exact ordinary trace. -/
theorem givenCentreMorphism_stalk_kernel (S : Set X.obj.left)
    (e : LocalEmbedding X) (O : Opens e.ambient)
    (C : Set O) (hC : IsClosedSubmanifold e.dim C)
    (hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier)
    (htrace : (givenWindowMorphism e O).hom.left.base ⁻¹' S =
      (Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C) (c : C) :
    RingHom.ker (((givenCentreMorphism e O C hC hCW).hom.left.stalkMap c).hom) =
      intrinsicCentreStalkRange X.obj.left S ((givenCentreMorphism e O C hC hCW).hom.left.base c) := by
  let u : actualSubspaceLocallyRingedSpace (n := e.dim) C ⟶
      actualSubspaceLocallyRingedSpace (n := e.dim) ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) :=
    (OriginalClosedSubspaceFactorization.inclusion
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O) hCW).hom.left
  let j : actualSubspaceLocallyRingedSpace (n := e.dim)
      ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) ⟶ X.obj.left :=
    (givenWindowMorphism e O).hom.left
  change RingHom.ker ((u ≫ j).stalkMap c).hom = _
  rw [LocallyRingedSpace.stalkMap_comp]
  change RingHom.ker (((u.stalkMap c).hom).comp
    (j.stalkMap (u.base c)).hom) = _
  rw [← RingHom.comap_ker,
    contained_inclusion_stalk_kernel_eq_intrinsicCentreStalkRange]
  have hp := openImmersion_pulled_stalkIdeal_eq j S (u.base c)
  change Ideal.map (j.stalkMap (u.base c)).hom
      (intrinsicCentreStalkRange X.obj.left S (j.base (u.base c))) =
    intrinsicCentreStalkRange _ (j.base ⁻¹' S) (u.base c) at hp
  change j.base ⁻¹' S = _ at htrace
  rw [htrace] at hp
  change Ideal.comap (j.stalkMap (u.base c)).hom
      (intrinsicCentreStalkRange
        (actualSubspaceLocallyRingedSpace (n := e.dim) ((Subtype.val : O → e.ambient) ⁻¹' e.carrier))
        ((Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C) (u.base c)) =
    intrinsicCentreStalkRange X.obj.left S (j.base (u.base c))
  rw [← hp, Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

private theorem intrinsicCentreStalkRange_comap_eqToHom (Y : LocallyRingedSpace.{0})
    (S : Set Y) (p q : Y) (hpq : p = q) :
    Ideal.comap (eqToHom (congrArg (fun t => Y.presheaf.stalk t) hpq)).hom
      (intrinsicCentreStalkRange Y S q) = intrinsicCentreStalkRange Y S p := by
  subst q
  rfl

private theorem bijective_of_surjective_same_kernel
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    (a : R →+* A) (b : A →+* B) (ha : Function.Surjective a)
    (hab : Function.Surjective (b.comp a))
    (hk : RingHom.ker (b.comp a) = RingHom.ker a) : Function.Bijective b := by
  constructor
  · intro s t hst
    obtain ⟨r, hr⟩ := ha (s - t)
    have hz : (b.comp a) r = 0 := by
      change b (a r) = 0
      rw [hr, map_sub, hst, sub_self]
    have hmem : r ∈ RingHom.ker (b.comp a) := hz
    rw [hk] at hmem
    exact sub_eq_zero.mp (hr.symm.trans hmem)
  · intro t
    obtain ⟨r, hr⟩ := hab t
    exact ⟨a r, hr⟩

/-- The given smooth centre is an actual open window of the SAME global factory. -/
theorem exists_given_window_factor_isOpenImmersion (S : Set X.obj.left)
    (hS : X.IsAnalyticSubset S) (e : LocalEmbedding X) (O : Opens e.ambient)
    (C : Set O) (hC : IsClosedSubmanifold e.dim C)
    (hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier)
    (htrace : (givenWindowMorphism e O).hom.left.base ⁻¹' S =
      (Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C) :
    ∃ f : ofClosedAnalytic C
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC) ⟶
        OriginalAnalyticClosedSubspace.sourceObject X S hS,
      f ≫ OriginalAnalyticClosedSubspace.inclusion X S hS = givenCentreMorphism e O C hC hCW ∧
      LocallyRingedSpace.IsOpenImmersion f.hom.left ∧
      range f.hom.left.base = (OriginalAnalyticClosedSubspace.inclusion X S hS).hom.left.base ⁻¹'
        range (givenWindowMorphism e O).hom.left.base := by
  classical
  let A := ofClosedAnalytic C
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)
  let Z := OriginalAnalyticClosedSubspace.sourceObject X S hS
  let i : Z ⟶ X := OriginalAnalyticClosedSubspace.inclusion X S hS
  let j := givenCentreMorphism e O C hC hCW
  let w := givenWindowMorphism e O
  have hland (c : A.obj.left) : j.hom.left.base c ∈ S := by
    change w.hom.left.base ⟨c.val, hCW c.property⟩ ∈ S
    exact (Set.ext_iff.mp htrace ⟨c.val, hCW c.property⟩).mpr c.property
  obtain ⟨f, hfac, _⟩ :=
    OriginalAnalyticClosedSubspaceFactorization.exists_unique_factorization X S hS A j hland
  have hiinj : Function.Injective i.hom.left.base :=
    (OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding X S hS).injective
  have hraw : f.hom.left ≫ i.hom.left = j.hom.left :=
    congrArg (fun H => H.hom.left) hfac
  have hrange : range f.hom.left.base = i.hom.left.base ⁻¹' range w.hom.left.base := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨⟨c.val, hCW c.property⟩, (congrArg (fun H => H.hom.left.base c) hfac).symm⟩
    · rintro ⟨d, hd⟩
      have hiz : i.hom.left.base z ∈ S := by
        rw [← OriginalAnalyticClosedSubspace.inclusion_range X S hS]
        exact ⟨z, rfl⟩
      have hdS : w.hom.left.base d ∈ S := hd.symm ▸ hiz
      have hdC : d.val ∈ C := (Set.ext_iff.mp htrace d).mp hdS
      let c : C := ⟨d.val, hdC⟩
      refine ⟨c, hiinj ?_⟩
      exact (congrArg (fun H => H.hom.left.base c) hfac).trans hd
  have hjemb : Topology.IsEmbedding j.hom.left.base := by
    exact (givenWindowMorphism_isOpenImmersion e O).base_open.isEmbedding.comp
      (SmoothCentreModification.contained_inclusion_isClosedEmbedding
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)
        (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O) hCW).isEmbedding
  have hfemb : Topology.IsEmbedding f.hom.left.base := by
    apply Topology.IsEmbedding.of_comp f.hom.left.base.hom.continuous i.hom.left.base.hom.continuous
    change Topology.IsEmbedding (f.hom.left ≫ i.hom.left).base
    rw [hraw]
    exact hjemb
  have hopen : IsOpen (range f.hom.left.base) := by
    rw [hrange]
    exact (givenWindowMorphism_isOpenImmersion e O).base_open.isOpen_range.preimage
      i.hom.left.base.hom.continuous
  have hbij (c : A.obj.left) : Function.Bijective (f.hom.left.stalkMap c) := by
    let p : X.obj.left := i.hom.left.base (f.hom.left.base c)
    let q : X.obj.left := j.hom.left.base c
    have hpq : p = q := congrArg (fun H => H.base c) hraw
    let epsilon : X.obj.left.presheaf.stalk p ≅ X.obj.left.presheaf.stalk q :=
      eqToIso (congrArg (fun t => X.obj.left.presheaf.stalk t) hpq)
    have hs : i.hom.left.stalkMap (f.hom.left.base c) ≫ f.hom.left.stalkMap c =
        epsilon.hom ≫ j.hom.left.stalkMap c := by
      rw [← LocallyRingedSpace.stalkMap_comp]
      exact PresheafedSpace.stalkMap.congr_hom
        (f.hom.left ≫ i.hom.left).toHom j.hom.left.toHom
        (congrArg LocallyRingedSpace.Hom.toHom hraw) c
    let a := (i.hom.left.stalkMap (f.hom.left.base c)).hom
    let b := (f.hom.left.stalkMap c).hom
    let g := (j.hom.left.stalkMap c).hom
    have hsR : b.comp a = g.comp epsilon.hom.hom := congrArg CommRingCat.Hom.hom hs
    have ha : Function.Surjective a :=
      OriginalAnalyticClosedSubspace.inclusion_stalk_surjective X S hS (f.hom.left.base c)
    have hg : Function.Surjective g := givenCentreMorphism_stalk_surjective e O C hC hCW c
    have he : Function.Surjective epsilon.hom.hom :=
      (ConcreteCategory.bijective_of_isIso epsilon.hom).2
    have hab : Function.Surjective (b.comp a) := by
      rw [hsR]
      exact hg.comp he
    have hk : RingHom.ker (b.comp a) = RingHom.ker a := by
      calc
        RingHom.ker (b.comp a) = RingHom.ker (g.comp epsilon.hom.hom) := congrArg RingHom.ker hsR
        _ = Ideal.comap epsilon.hom.hom (RingHom.ker g) := (RingHom.comap_ker _ _).symm
        _ = Ideal.comap epsilon.hom.hom (intrinsicCentreStalkRange X.obj.left S q) := by
          rw [givenCentreMorphism_stalk_kernel S e O C hC hCW htrace c]
        _ = intrinsicCentreStalkRange X.obj.left S p :=
          intrinsicCentreStalkRange_comap_eqToHom X.obj.left S p q hpq
        _ = RingHom.ker a :=
          (OriginalAnalyticClosedSubspace.inclusion_stalk_kernel X S hS (f.hom.left.base c)).symm
    exact bijective_of_surjective_same_kernel a b ha hab hk
  let : ∀ c : A.obj.left, IsIso (f.hom.left.stalkMap c) := fun c =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij c)
  have hf : LocallyRingedSpace.IsOpenImmersion f.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f.hom.left ⟨hfemb, hopen⟩
  exact ⟨f, hfac, hf, hrange⟩

/-- Native restriction along the ACTUAL f.base, with both FULL complex triangles. -/
theorem exists_given_window_native_restriction (S : Set X.obj.left)
    (hS : X.IsAnalyticSubset S) (e : LocalEmbedding X) (O : Opens e.ambient)
    (C : Set O) (hC : IsClosedSubmanifold e.dim C)
    (hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier)
    (htrace : (givenWindowMorphism e O).hom.left.base ⁻¹' S =
      (Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C) :
    ∃ (f : ofClosedAnalytic C
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC) ⟶
        OriginalAnalyticClosedSubspace.sourceObject X S hS)
      (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left),
      f ≫ OriginalAnalyticClosedSubspace.inclusion X S hS = givenCentreMorphism e O C hC hCW ∧
      range f.hom.left.base = (OriginalAnalyticClosedSubspace.inclusion X S hS).hom.left.base ⁻¹'
        range (givenWindowMorphism e O).hom.left.base ∧
      ∃ E : (ofClosedAnalytic C
          (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)).obj.left ≅
          (OriginalAnalyticClosedSubspace.sourceObject X S hS).obj.left.restrict hf.base_open,
        E.hom ≫ (OriginalAnalyticClosedSubspace.sourceObject X S hS).obj.left.ofRestrict hf.base_open =
          f.hom.left ∧
        E.inv ≫ f.hom.left =
          (OriginalAnalyticClosedSubspace.sourceObject X S hS).obj.left.ofRestrict hf.base_open ∧
        E.hom ≫ ((OriginalAnalyticClosedSubspace.sourceObject X S hS).obj.left.ofRestrict hf.base_open ≫
          (OriginalAnalyticClosedSubspace.sourceObject X S hS).obj.hom) =
          (ofClosedAnalytic C
            (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)).obj.hom ∧
        E.inv ≫ (ofClosedAnalytic C
            (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC)).obj.hom =
          (OriginalAnalyticClosedSubspace.sourceObject X S hS).obj.left.ofRestrict hf.base_open ≫
            (OriginalAnalyticClosedSubspace.sourceObject X S hS).obj.hom := by
  obtain ⟨f, hfac, hf, hr⟩ := exists_given_window_factor_isOpenImmersion S hS e O C hC hCW htrace
  let : LocallyRingedSpace.IsOpenImmersion f.hom.left := hf
  let E := LocallyRingedSpace.IsOpenImmersion.isoRestrict f.hom.left
  have he := LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.hom.left
  have hei := LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict f.hom.left
  refine ⟨f, hf, hfac, hr, E, he, hei, ?_, ?_⟩
  · rw [← Category.assoc, he, Over.w f.hom]
  · rw [← Over.w f.hom, ← Category.assoc, hei]

/-- Ordinary local smooth-centre geometry makes the SAME actual factory smooth. -/
theorem sourceObject_isSmooth_of_local_smooth_centres (S : Set X.obj.left)
    (hS : X.IsAnalyticSubset S)
    (hGeom : ∀ (x : X.obj.left), x ∈ S →
      ∃ (e : LocalEmbedding X) (O : Opens e.ambient) (C : Set O)
        (_hC : IsClosedSubmanifold e.dim C)
        (_hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier)
        (d : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier)),
        (givenWindowMorphism e O).hom.left.base d = x ∧
        (givenWindowMorphism e O).hom.left.base ⁻¹' S =
          (Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C) :
    (OriginalAnalyticClosedSubspace.sourceObject X S hS).IsSmooth := by
  intro z
  let i := OriginalAnalyticClosedSubspace.inclusion X S hS
  have hzS : i.hom.left.base z ∈ S := by
    exact (Set.ext_iff.mp (OriginalAnalyticClosedSubspace.inclusion_range X S hS)
      (i.hom.left.base z)).mp ⟨z, rfl⟩
  obtain ⟨e, O, C, hC, hCW, d, hd, htrace⟩ := hGeom (i.hom.left.base z) hzS
  have hdS : (givenWindowMorphism e O).hom.left.base d ∈ S := hd.symm ▸ hzS
  have hdC : d.val ∈ C := (Set.ext_iff.mp htrace d).mp hdS
  let c : C := ⟨d.val, hdC⟩
  obtain ⟨f, hfac, hf, _⟩ := exists_given_window_factor_isOpenImmersion S hS e O C hC hCW htrace
  have hfc : f.hom.left.base c = z := by
    apply (OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding X S hS).injective
    exact (congrArg (fun H => H.hom.left.base c) hfac).trans hd
  obtain ⟨k, V, j, hj, hp, hc⟩ := isSmooth_ofClosedAnalytic_of_isClosedSubmanifold hC c
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let : LocallyRingedSpace.IsOpenImmersion f.hom.left := hf
  refine ⟨k, V, j ≫ f.hom.left, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, Over.w f.hom]
    exact hp
  · obtain ⟨v, hv⟩ := hc
    exact ⟨v, (congrArg f.hom.left.base hv).trans hfc⟩

end

end Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceSmoothCentres
