import Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
import Hironaka.Resolution.HironakaG10HirChartFlattener

/-!
# The graph-quotient test-ideal criterion is the chart criterion of the graph row (G10-01-08, part)

Lane G10MW, run 0081.  For every ideal `J` of the parameter germ ring `R = 𝒪_{ℂ^d,0}` (nonreduced,
zero divisors allowed):

* `flat_quotMap_ringEquiv_comp_iff`, `flat_quotMap_comp_surjective_iff`,
  `flat_quotMap_algebraMap_iff_moduleFlat`: per-ideal algebra (post-composition with a ring isomorphism;
  a surjection of base rings with the comap test ideal; ring-map flatness as module flatness of the
  base change of a linearly isomorphic module);
* `chartFlat_iff_structureMapAt`: the chart cokernel criterion `ChartFlat` of a one-row matrix is
  flatness of the literal quotient map of the structure map `R → A ⧸ idealAt`;
* `graphChart_flat_iff_chartFlat`: at every graph point of a Cartan window, flatness over `V(J)` of the
  ambient relative graph chart `R → 𝒪_{ℂ^{d+m},0} ⧸ nativeRelativeGraphIdeal` is `ChartFlat` of the
  graph row at `(ψ x − c, x)`.

Together with lane G10SB's native dictionary (`quotMap_fibre_flat_iff_graph`, G10-02-04: native fibre
flatness over `V(J)` ⟺ graph-chart flatness over the lifted ideal) this reads the chart criteria of
`HironakaG10MwWindowFamily` on the actual morphism.  No named input.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10MwGraphChartFlat

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm OkaRelationSheaf OkaGermBridge
  HironakaRelativeNormalIdeal HironakaHolomorphicJetRankLoci HironakaChowRelativeGraphPresentation
  HironakaG10HirFlatQuotient HironakaG10HirChartFlattener
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen Hironaka.Analytic.Unibranch.HironakaG10MwGraphRow
  Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily

/-! ### Per-ideal algebra -/

/-- Post-composition with a ring isomorphism does not change flatness over `V(J)`. -/
theorem flat_quotMap_ringEquiv_comp_iff {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    (φ : A →+* B) (e : B ≃+* B') (J : Ideal A) :
    (quotMap (e.toRingHom.comp φ) J).Flat ↔ (quotMap φ J).Flat := by
  have hJ : J.map (e.toRingHom.comp φ) = (J.map φ).map e.toRingHom := by
    rw [Ideal.map_map]
  let e' := Ideal.quotientEquiv (J.map φ) (J.map (e.toRingHom.comp φ)) e hJ
  have hsq : e'.toRingHom.comp (quotMap φ J) = quotMap (e.toRingHom.comp φ) J := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← hsq, RingHom.Flat.comp_iff_of_bijective_left (g := e'.toRingHom) e'.bijective]

/-- **Test ideals through a surjection of base rings.** For `π : R ↠ S`, flatness of `φ : S → B` over
`V(J)` is flatness of `φ ∘ π` over `V(π⁻¹ J)`. -/
theorem flat_quotMap_comp_surjective_iff {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    (π : R →+* S) (hπ : Function.Surjective π) (φ : S →+* B) (J : Ideal S) :
    (quotMap (φ.comp π) (J.comap π)).Flat ↔ (quotMap φ J).Flat := by
  have hJ' : (J.comap π).map π = J := Ideal.map_comap_of_surjective π hπ J
  have hmap : (J.comap π).map (φ.comp π) = J.map φ := by
    rw [← Ideal.map_map, hJ']
  let e₁ : R ⧸ J.comap π ≃+* S ⧸ J := RingEquiv.ofBijective (Ideal.quotientMap J π le_rfl)
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hπ⟩
  let e₂ := Ideal.quotEquivOfEq hmap
  have hsq : e₂.toRingHom.comp (quotMap (φ.comp π) (J.comap π)) =
      (quotMap φ J).comp e₁.toRingHom := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← RingHom.Flat.comp_iff_of_bijective_left (g := e₂.toRingHom) e₂.bijective, hsq,
    RingHom.Flat.comp_iff_of_bijective_right (g := e₁.toRingHom) e₁.bijective]

/-- Ring-map flatness over `V(I)` is module flatness of the base change of any linearly isomorphic
module. -/
theorem flat_quotMap_algebraMap_iff_moduleFlat {R C M : Type} [CommRing R] [CommRing C]
    [Algebra R C] [AddCommGroup M] [Module R M] (E : M ≃ₗ[R] C) (I : Ideal R) :
    (quotMap (algebraMap R C) I).Flat ↔ Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) := by
  let T := R ⧸ I
  let H := Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I
  have heq : quotMap (algebraMap R C) I = algebraMap T (C ⧸ I.map (algebraMap R C)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  rw [heq, RingHom.flat_algebraMap_iff, Module.Flat.equiv_iff H.toLinearEquiv,
    Module.Flat.equiv_iff (E.baseChange R T M C).symm]

/-! ### The one-row chart cokernel -/

/-- The image of the column space of a one-row matrix under `Fin 1 → A ≃ A` is the entry ideal. -/
theorem map_range_mulVecLin_funUnique {A : Type*} [CommRing A] {b : ℕ} (G : Matrix (Fin 1) (Fin b) A) :
    (LinearMap.range (Matrix.mulVecLin G)).map
        (LinearEquiv.funUnique (Fin 1) A A : (Fin 1 → A) →ₗ[A] A) =
      Ideal.span (Set.range (G 0)) := by
  ext a
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    refine ⟨c, ?_⟩
    change _ = (Matrix.mulVecLin G c) default
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
    refine ⟨Matrix.mulVecLin G c, ⟨c, rfl⟩, ?_⟩
    change (Matrix.mulVecLin G c) default = a
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    rw [← hc]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

local instance (d : ℕ) : Algebra ℂ (HolGerm (ComplexModel d)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel d)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

/-- **The chart cokernel criterion is the literal structure-map criterion.** -/
theorem chartFlat_iff_structureMapAt (d t : ℕ) {b : ℕ}
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ) (q : ComplexModel d × ComplexModel t)
    (I : Ideal (HolGerm (ComplexModel d))) :
    ChartFlat d t F q I ↔ (quotMap (structureMapAt d t F q) I).Flat := by
  let R := HolGerm (ComplexModel d)
  let A := HolGerm (ComplexModel d × ComplexModel t)
  let G : Matrix (Fin 1) (Fin b) A := fun i j => germAt q (F i j)
  let C := A ⧸ idealAt d t F q
  let _ : Algebra R C := (structureMapAt d t F q).toAlgebra
  let EA : chartModule d t F q ≃ₗ[A] C :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.funUnique (Fin 1) A A)
      (map_range_mulVecLin_funUnique G)
  let E : chartModule d t F q ≃ₗ[R] C :=
    { EA.toAddEquiv with
      map_smul' := by
        intro r x
        change EA (basePullback d t r • x) = structureMapAt d t F q r * EA x
        rw [EA.map_smul]
        rfl }
  exact (flat_quotMap_algebraMap_iff_moduleFlat E I).symm

/-- **The graph-quotient criterion is the chart criterion of the graph row.**  At every graph point of a
Cartan window, flatness of the ambient relative graph chart `R → 𝒪_{ℂ^{d+m},0} ⧸ K` (whose target is the
native source stalk, `nativeRelativeGraphEquiv`) over `V(J)` is `ChartFlat` of the ONE graph row at
`(ψ x − c, x)`, for EVERY ideal `J` of `R`. -/
theorem graphChart_flat_iff_chartFlat {d m r : ℕ}
    {U : Opens (ComplexModel m)} {V : Opens (ComplexModel d)} (φ : U → V)
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ φ) (C : Set U) (x : C)
    (ψ : ComplexModel m → ComplexModel d) (hψ : ∀ y (hy : y ∈ U), ψ y = (φ ⟨y, hy⟩).val)
    (hψhol : ∀ k, HolAt (fun w => ψ w k) x.val.val)
    (c : ComplexModel d) (g : Fin r → ComplexModel m → ℂ) (hg : ∀ j, HolAt (g j) x.val.val)
    (hgen : wholeChartStalkIdeal (vanishingIdeal (n := m) C) x.val x.val (mem_chart_source _ x.val) =
      Ideal.span (Set.range fun j => germAt x.val.val (g j)))
    (J : Ideal (HolGerm (ComplexModel d))) :
    (quotMap (chartMap d m (nativeRelativeGraphIdeal hφ C x)) J).Flat ↔
      ChartFlat d m (graphRow ψ c g) (ψ x.val.val - c, x.val.val) J := by
  have hid := map_nativeRelativeGraphIdeal_eq_idealAt φ hφ C x ψ hψ hψhol c g hg hgen
  let I' := nativeRelativeGraphIdeal hφ C x
  let q : ComplexModel d × ComplexModel m := (ψ x.val.val - c, x.val.val)
  let e₂ := Ideal.quotientEquiv I' (idealAt d m (graphRow ψ c g) q) (ambientGermEquiv d m) hid.symm
  have h2 : e₂.toRingHom.comp (chartMap d m I') = structureMapAt d m (graphRow ψ c g) q := by
    ext a
    change Ideal.Quotient.mk _ (ambientGermEquiv d m (tangentPullback d m a)) =
      Ideal.Quotient.mk _ (basePullback d m a)
    rw [ambientGermEquiv_tangentPullback]
  rw [← flat_quotMap_ringEquiv_comp_iff (chartMap d m I') e₂ J, h2, chartFlat_iff_structureMapAt]

end

end Hironaka.Analytic.Unibranch.HironakaG10MwGraphChartFlat
