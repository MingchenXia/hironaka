import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier

/-!
# Whole contained-centre ideal transport under the ORIGINAL intrinsic iso

All ideal images use the SAME original inclusion and actual structure-sheaf
stalk maps. An original scalar-compatible morphism pulls each original
vanishing germ to a genuine local ambient representative vanishing on the
contained source centre. The original inverse gives equality of whole ideals.
No radical, trace-centre replacement or incoming ideal equality is used.

Applications use analytic reduced centres; the full vanishing-ideal argument
only needs the two explicit containments of centres in the original carriers.
Blueprint: `embedded-centre-ideal-iso.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedCentreIdealIso

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceLocalFunctions
  HironakaActualAnalyticSubspaceResidue HironakaReducedComplexAnalyticSpaces
  HironakaSingularSubspaceBlowupCartier SourceReducedComplexSpace

private theorem idealFamily_map_specializes {X : LocallyRingedSpace}
    (I : ∀ x : X, Ideal (X.presheaf.stalk x).carrier) {x y : X} (h : x = y) :
    Ideal.map (X.presheaf.stalkSpecializes (specializes_of_eq h)).hom (I y) = I x := by
  cases h
  simp only [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.map_id]

private theorem idealFamily_map_eq_of_iso {X Z : LocallyRingedSpace} (E : X ≅ Z)
    (I : ∀ x : X, Ideal (X.presheaf.stalk x).carrier)
    (J : ∀ z : Z, Ideal (Z.presheaf.stalk z).carrier)
    (hf : ∀ x, Ideal.map (E.hom.stalkMap x).hom (J (E.hom.base x)) ≤ I x)
    (hg : ∀ z, Ideal.map (E.inv.stalkMap z).hom (I (E.inv.base z)) ≤ J z)
    (x : X) : Ideal.map (E.hom.stalkMap x).hom (J (E.hom.base x)) = I x := by
  apply le_antisymm (hf x)
  have hx : x = E.inv.base (E.hom.base x) :=
    (congrArg (fun H => H.base x) E.hom_inv_id).symm
  have hs : (E.hom.stalkMap x).hom.comp (E.inv.stalkMap (E.hom.base x)).hom =
      (X.presheaf.stalkSpecializes (specializes_of_eq hx)).hom := by
    simpa only [CommRingCat.hom_comp] using
      congrArg (fun H => H.hom) (LocallyRingedSpace.stalkMap_inv_hom E x)
  have hround' : Ideal.map (E.hom.stalkMap x).hom
      (Ideal.map (E.inv.stalkMap (E.hom.base x)).hom (I (E.inv.base (E.hom.base x)))) =
        I x := by
    rw [Ideal.map_map, hs]
    exact idealFamily_map_specializes I hx
  exact hround'.ge.trans (Ideal.map_mono (hg (E.hom.base x)))

variable {n₀ n₁ : ℕ} {M₀ M₁ : Type}
  [TopologicalSpace M₀] [ChartedSpace (ComplexModel n₀) M₀] [IsComplexManifold n₀ M₀]
  [TopologicalSpace M₁] [ChartedSpace (ComplexModel n₁) M₁] [IsComplexManifold n₁ M₁]
  {W₀ C₀ : Set M₀} {W₁ C₁ : Set M₁}

/-- The ORIGINAL full scalar-compatible morphism respects the whole centre
ideal image when the original source centre is CONTAINED in its carrier. -/
theorem map_centreIdeal_le
    (F : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶
      actualSubspaceLocallyRingedSpace (n := n₁) W₁)
    (hF : F ≫ subspacePointMap (n := n₁) W₁ = subspacePointMap (n := n₀) W₀)
    (hC₀W₀ : C₀ ⊆ W₀)
    (hcentre : ∀ y : W₀, y.val ∈ C₀ → (F.base y).val ∈ C₁) (x : W₀) :
    Ideal.map (F.stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) (F.base x).val)) ≤
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) x.val) := by
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, hvan, rfl⟩
  change F.stalkMap x (((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base x))
      (actualOriginalFunctionGerm (F.base x).val f hf)) ∈
    Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap x).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) x.val)
  obtain ⟨V, hxV, s, hs⟩ := exists_actual_section_of_original_holomorphicAt (F.base x).val f hf
  let K := F ≫ actualSubspaceInclusion (n := n₁) W₁
  let R := (Opens.map K.base).obj V
  let a := K.c.app (op V) s
  have hxR : x ∈ R := hxV
  obtain ⟨O, hxO, t, hOR, ht⟩ := actualSubspaceSection_local_ambient W₀ R a x hxR
  have hvalue (y : W₀) (hyO : y.val ∈ O) :
      t ⟨y.val, hyO⟩ = s ⟨(F.base y).val, hOR y hyO⟩ := by
    let r := (actualComplexStructureSheaf (n := n₁) M₁).presheaf.germ V
      (F.base y).val (hOR y hyO) s
    calc
      _ = actualSubspaceStalkEval (n := n₀) W₀ y
          ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y
            ((actualComplexStructureSheaf (n := n₀) M₀).presheaf.germ O y.val hyO t)) :=
        (actualSubspaceStalkEval_inclusion_germ W₀ O t y hyO).symm
      _ = actualSubspaceStalkEval (n := n₀) W₀ y
          ((actualSubspaceSheaf (n := n₀) W₀).presheaf.germ R y (hOR y hyO) a) :=
        congrArg (actualSubspaceStalkEval (n := n₀) W₀ y) (ht y hyO).symm
      _ = actualSubspaceStalkEval (n := n₀) W₀ y (K.stalkMap y r) :=
        congrArg (actualSubspaceStalkEval (n := n₀) W₀ y)
          (LocallyRingedSpace.stalkMap_germ_apply K V y (hOR y hyO) s).symm
      _ = actualSubspaceStalkEval (n := n₀) W₀ y
          (F.stalkMap y ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base y) r)) :=
        congrArg (actualSubspaceStalkEval (n := n₀) W₀ y)
          (ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp F
            (actualSubspaceInclusion (n := n₁) W₁) y) r)
      _ = actualSubspaceStalkEval (n := n₁) W₁ (F.base y)
          ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base y) r) :=
        actualSubspaceMap_eval_of_point_compatible F hF y _
      _ = _ := actualSubspaceStalkEval_inclusion_germ W₁ V s (F.base y) (hOR y hyO)
  let u := sectionExtension O t
  have hu : HolomorphicAt n₀ u x.val := sectionExtension_holomorphicAt O t x.val hxO
  have hcont : Continuous (fun y : W₀ => (F.base y).val) :=
    continuous_subtype_val.comp F.base.hom.continuous
  have hevent : ∀ᶠ y : W₀ in 𝓝 x,
      sectionExtension V s (F.base y).val = f (F.base y).val ∧
        ((F.base y).val ∈ C₁ → f (F.base y).val = 0) :=
    hcont.continuousAt.tendsto.eventually (hs.and hvan.2)
  rw [nhds_subtype W₀ x] at hevent
  obtain ⟨N, hN, hNP⟩ := Filter.mem_comap.mp hevent
  have huvan : (vanishingIdeal (n := n₀) C₀).mem x.val u := by
    refine ⟨hu, ?_⟩
    filter_upwards [hN, O.isOpen.mem_nhds hxO] with z hzN hzO
    intro hzC
    let y : W₀ := ⟨z, hC₀W₀ hzC⟩
    have hy := hNP (show y ∈ (Subtype.val : W₀ → M₀) ⁻¹' N from hzN)
    calc
      u z = t ⟨z, hzO⟩ := sectionExtension_apply O t z hzO
      _ = s ⟨(F.base y).val, hOR y hzO⟩ := hvalue y hzO
      _ = sectionExtension V s (F.base y).val :=
        (sectionExtension_apply V s (F.base y).val (hOR y hzO)).symm
      _ = f (F.base y).val := hy.1
      _ = 0 := hy.2 (hcentre y hzC)
  have hmem : actualOriginalFunctionGerm x.val u hu ∈
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) x.val :=
    (actualOriginalGerm_mem_vanishingIdeal_iff C₀ x.val u hu).mpr huvan
  have htarget := actualOriginalFunctionGerm_eq_section V (F.base x).val hxV s f hf hs
  have hsource : (actualSubspaceInclusion (n := n₀) W₀).stalkMap x
      (actualOriginalFunctionGerm x.val u hu) =
        F.stalkMap x ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base x)
          (actualOriginalFunctionGerm (F.base x).val f hf)) := by
    have hg := actualOriginalFunctionGerm_eq_section O x.val hxO t u hu Filter.EventuallyEq.rfl
    calc
      _ = (actualSubspaceInclusion (n := n₀) W₀).stalkMap x
          ((actualComplexStructureSheaf (n := n₀) M₀).presheaf.germ O x.val hxO t) :=
        congrArg ((actualSubspaceInclusion (n := n₀) W₀).stalkMap x) hg
      _ = (actualSubspaceSheaf (n := n₀) W₀).presheaf.germ R x hxR a := (ht x hxO).symm
      _ = K.stalkMap x ((actualComplexStructureSheaf (n := n₁) M₁).presheaf.germ V
          (F.base x).val hxV s) := (LocallyRingedSpace.stalkMap_germ_apply K V x hxV s).symm
      _ = F.stalkMap x ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base x)
          ((actualComplexStructureSheaf (n := n₁) M₁).presheaf.germ V (F.base x).val hxV s)) :=
        ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp F
          (actualSubspaceInclusion (n := n₁) W₁) x) _
      _ = _ := congrArg (fun r => F.stalkMap x
        ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base x) r)) htarget.symm
  rw [← hsource]
  exact Ideal.mem_map_of_mem ((actualSubspaceInclusion (n := n₀) W₀).stalkMap x).hom hmem

/-- An ORIGINAL over-complex-point iso transporting explicitly CONTAINED
centres transports their WHOLE original actual stalk ideals, at every x.
Applications take analytic/reduced centres; no radical or ideal certificate. -/
theorem map_centreIdeal_eq_of_iso
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (hW₁ : IsComplexAnalyticSubset (n := n₁) W₁)
    (e : ofClosedAnalytic W₀ hW₀ ≅ ofClosedAnalytic W₁ hW₁)
    (hC₀W₀ : C₀ ⊆ W₀) (hC₁W₁ : C₁ ⊆ W₁)
    (hcentres : ∀ x : W₀, x.val ∈ C₀ ↔ (e.hom.hom.left.base x).val ∈ C₁) (x : W₀) :
    Ideal.map (e.hom.hom.left.stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap
            (e.hom.hom.left.base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁)
            (e.hom.hom.left.base x).val)) =
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) x.val) := by
  let E : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ≅
      actualSubspaceLocallyRingedSpace (n := n₁) W₁ := SourceReducedComplexSpace.isoLeft e
  have hp : E.hom ≫ subspacePointMap (n := n₁) W₁ = subspacePointMap (n := n₀) W₀ :=
    Over.w e.hom.hom
  have hpi : E.inv ≫ subspacePointMap (n := n₀) W₀ = subspacePointMap (n := n₁) W₁ :=
    Over.w e.inv.hom
  have hmap : ∀ y : W₀, y.val ∈ C₀ → (E.hom.base y).val ∈ C₁ :=
    fun y hy => (hcentres y).mp hy
  have hmapi : ∀ y : W₁, y.val ∈ C₁ → (E.inv.base y).val ∈ C₀ := by
    intro y hy
    apply (hcentres (E.inv.base y)).mpr
    have hpoint : E.hom.base (E.inv.base y) = y :=
      congrArg (fun H => H.base y) E.inv_hom_id
    change (E.hom.base (E.inv.base y)).val ∈ C₁
    rwa [hpoint]
  let J₀ := fun z : W₀ =>
    Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap z).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) z.val)
  let J₁ := fun z : W₁ =>
    Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap z).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) z.val)
  change Ideal.map (E.hom.stalkMap x).hom (J₁ (E.hom.base x)) = J₀ x
  exact idealFamily_map_eq_of_iso E J₀ J₁
    (fun z => map_centreIdeal_le E.hom hp hC₀W₀ hmap z)
    (fun z => map_centreIdeal_le E.inv hpi hC₁W₁ hmapi z) x

end

end Hironaka.Analytic.Unibranch.EmbeddedCentreIdealIso
