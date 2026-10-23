import DeJongAlterations.StableModification.Curves.SemistableOpenLocal
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.Geometry.NodeCompletedLocalSpecLocalization
import DeJongAlterations.Geometry.RegularSmoothConverse
import DeJongAlterations.StableModification.Resolution.LocalSmoothPoint

/-!
# The semi-stable locus is open

Let `g : C → S` be flat and locally of finite presentation with geometric fibres of pure dimension
one (an `S`-curve in the sense of Temkin). If a closed point `y` of a geometric fibre
`C ×_S Spec K` is a smooth point or an ordinary double point, then the image of `y` in `C` has an
open neighbourhood `U` such that `U → S` is a nodal curve (`exists_isNodalCurve_nbhd`). Hence the
union `nodalLocus g` of all open `U ⊆ C` with `U → S` nodal is the largest such open
(`isNodalCurve_nodalLocus`), it contains every geometric fibre which is a nodal curve
(`fst_mem_nodalLocus_of_isNodalFiber`), and `g` is a nodal curve iff `nodalLocus g = ⊤`. For
universally closed `g`, the points of `S` whose fibre lies in the nodal locus form an open
`nodalBase g` over which `g` is a nodal curve; it contains every point with a nodal geometric fibre
and only such points (`isNodalFiber_of_mem_nodalBase`, `mem_nodalBase_of_isNodalFiber`).

This is M. Temkin, *Stable modification of relative curves*, Lemma 5.1(i) (T:3282–3292: "it is well
known that the semi-stable locus of `C' → S` is open (e.g. use the local description from
[dJ, 2.23])"), for the curve `C'` alone (Temkin deduces the pointed version from the openness of
the étale locus and of the smooth locus; that step is not formalized here). Temkin's reference to de Jong 2.23 is not enough: 2.23 describes
the completed local rings at a node, and openness needs a presentation of the family on a Zariski
neighbourhood. We prove it through the hypersurface presentation of `SemistableOpenNode`
(blueprint `sm-semistable-curves.tex`, `prop:sm-semistable-open`).

The scheme-theoretic part: affine charts `Spec (K ⊗_R B) → C ×_S Spec K` over affine opens
`Spec B → C` and `Spec R → S` (`tensorChart`), the comparison of smooth points and nodes of
`Spec A → Spec K` with the local algebra of `A` (`mem_smoothLocus_spec_iff`,
`isGeometricOrdinaryDoublePoint_spec_iff`), and the affine criterion `isNodalCurve_spec`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TensorProduct

namespace DeJongAlterations.StableModification.Curves.SemistableOpen

open Geometry Geometry.NodeCompletedLocalAffineBaseChangeUV
open DeJong (IsNodalCurve IsSmoothAt)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section SpecPoints

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- **Nodes of an affine scheme over a field** are the primes at which the completed local ring is
the formal node. -/
theorem isGeometricOrdinaryDoublePoint_spec_iff (z : PrimeSpectrum A) :
    IsGeometricOrdinaryDoublePoint (Spec.map (CommRingCat.ofHom (algebraMap K A))) z ↔
      IsFormalNode K z.asIdeal := by
  let := Scheme.completedLocalRingAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K A))) z
  let ε := NodeCompletedLocalSpecLocalization.completedEquiv K A z
  constructor
  · rintro ⟨e⟩
    exact ⟨ε.symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨ε.trans e⟩

variable [IsAlgClosed K] [Algebra.FiniteType K A]

omit [IsAlgClosed K] in
/-- `Spec A → Spec K` is locally of finite presentation for a finitely generated `K`-algebra. -/
theorem locallyOfFinitePresentation_spec :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr
    (Algebra.FinitePresentation.of_finiteType.mp inferInstance))

attribute [local instance] locallyOfFinitePresentation_spec

/-- **Smooth points of a curve over an algebraically closed field.** At a point of `Spec A` whose
local ring is one-dimensional, `Spec A → Spec K` is smooth iff the maximal ideal of the local ring
is principal. -/
theorem mem_smoothLocus_spec_iff (z : PrimeSpectrum A)
    (hdim : ringKrullDim ((Spec (.of A)).presheaf.stalk z) = 1) :
    z ∈ (Spec.map (CommRingCat.ofHom (algebraMap K A))).smoothLocus ↔
      (maximalIdeal (Localization.AtPrime z.asIdeal)).spanFinrank ≤ 1 := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  rw [RegularSmoothConverse.mem_smoothLocus_iff_isRegularLocalRing]
  let := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K A))) z
  let ε := (NodeCompletedLocalSpecLocalization.stalkEquiv K A z).toRingEquiv
  have hdimL : ringKrullDim (Localization.AtPrime z.asIdeal) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv ε]
    exact hdim
  constructor
  · intro h
    have := h
    have := IsRegularLocalRing.of_ringEquiv ε
    have h' := (isRegularLocalRing_iff (Localization.AtPrime z.asIdeal)).mp this
    rw [hdimL] at h'
    exact_mod_cast h'.le
  · intro h
    have : IsRegularLocalRing (Localization.AtPrime z.asIdeal) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by rw [hdimL]; exact_mod_cast h)
    exact IsRegularLocalRing.of_ringEquiv ε.symm

end SpecPoints

section Components

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Irreducible components of the source of an étale map into a scheme of pure dimension one over
`K` have dimension one. -/
theorem pure_of_etale {Y Y' : Scheme.{u}} (e : Y ⟶ Y') [Etale e] {q' : Y' ⟶ Spec (.of K)}
    [LocallyOfFiniteType q'] (h : ∀ Z ∈ irreducibleComponents Y', topologicalKrullDim Z = 1) :
    ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = 1 := fun _ hZ =>
  component_dimension_of_etale (q' := q') e hZ
    (h _ (genericPoint_image_mem_irreducibleComponents e hZ))

end Components

section Chart

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {C S : Scheme.{u}} (g : C ⟶ S) {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  {jV : Spec (.of R) ⟶ S} [IsOpenImmersion jV] {jB : Spec (.of B) ⟶ C} [IsOpenImmersion jB]
  (hsq : jB ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jV)
  {K : Type u} [Field K] [Algebra R K] {a : Spec (.of K) ⟶ S}
  (ha : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ jV = a)

/-- The chart `Spec B ×_{Spec R} Spec K → C ×_S Spec K` of a geometric fibre over affine opens
`Spec B → C` and `Spec R → S`. -/
def chartMap : ActualBaseChange R B K ⟶ pullback g a :=
  pullback.lift (pullback.fst _ _ ≫ jB) (pullback.snd _ _) (by
    rw [Category.assoc, hsq, pullback.condition_assoc, ha])

omit [IsOpenImmersion jV] [IsOpenImmersion jB] in
@[reassoc (attr := simp)]
theorem chartMap_fst :
    chartMap g hsq ha ≫ pullback.fst g a = pullback.fst _ _ ≫ jB :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion jV] [IsOpenImmersion jB] in
@[reassoc (attr := simp)]
theorem chartMap_snd : chartMap g hsq ha ≫ pullback.snd g a = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

omit [IsOpenImmersion jB] in
/-- The chart is the base change of `Spec B → C`. -/
theorem chartMap_isPullback :
    IsPullback (chartMap g hsq ha) (pullback.fst _ _) (pullback.fst g a) jB := by
  let β := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let γ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hr : IsPullback (𝟙 (Spec (.of B))) β (jB ≫ g) jV :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hsq⟩
  have hb : IsPullback (pullback.fst β γ) (pullback.snd β γ) (jB ≫ g) a := by
    have h := (IsPullback.of_hasPullback β γ).paste_horiz hr
    rw [Category.comp_id, ha] at h
    exact h
  have ho : IsPullback (pullback.fst β γ) (chartMap g hsq ha ≫ pullback.snd g a) (jB ≫ g) a := by
    rw [chartMap_snd]
    exact hb
  exact (IsPullback.of_bot ho (chartMap_fst g hsq ha).symm
    (IsPullback.of_hasPullback g a)).flip

instance chartMap_isOpenImmersion : IsOpenImmersion (chartMap g hsq ha) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (chartMap_isPullback g hsq ha).flip inferInstance

omit [IsOpenImmersion jB] in
theorem range_chartMap :
    Set.range (chartMap g hsq ha) = (pullback.fst g a) ⁻¹' Set.range jB := by
  let H := chartMap_isPullback g hsq ha
  calc
    Set.range (chartMap g hsq ha) =
        Set.range (pullback.fst (pullback.fst g a) jB) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        refine ⟨H.isoPullback.hom z, ?_⟩
        change (H.isoPullback.hom ≫ pullback.fst _ _) z = _
        rw [H.isoPullback_hom_fst]
      · rintro ⟨p, hp⟩
        refine ⟨H.isoPullback.inv p, ?_⟩
        change (H.isoPullback.inv ≫ chartMap g hsq ha) p = _
        rw [H.isoPullback_inv_fst]
        exact hp
    _ = _ := by rw [Scheme.Pullback.range_fst]

/-- The chart `Spec (K ⊗_R B) → C ×_S Spec K` of a geometric fibre. -/
def tensorChart : Spec (.of (K ⊗[R] B)) ⟶ pullback g a :=
  (actualTensorIso R B K).inv ≫ chartMap g hsq ha

instance tensorChart_isOpenImmersion : IsOpenImmersion (tensorChart g hsq ha) := by
  unfold tensorChart
  infer_instance

omit [IsOpenImmersion jV] [IsOpenImmersion jB] in
@[reassoc]
theorem tensorChart_snd :
    tensorChart g hsq ha ≫ pullback.snd g a =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B))) := by
  rw [tensorChart, Category.assoc, chartMap_snd, Iso.inv_comp_eq, actualTensorIso_hom_field]

omit [IsOpenImmersion jV] [IsOpenImmersion jB] in
@[reassoc]
theorem tensorChart_fst :
    tensorChart g hsq ha ≫ pullback.fst g a =
      Spec.map (CommRingCat.ofHom (algebraMap B (K ⊗[R] B))) ≫ jB := by
  rw [tensorChart, Category.assoc, chartMap_fst, Iso.inv_comp_eq, ← Category.assoc,
    actualTensorIso_hom_original]

omit [IsOpenImmersion jB] in
theorem range_tensorChart :
    Set.range (tensorChart g hsq ha) = (pullback.fst g a) ⁻¹' Set.range jB := by
  rw [← range_chartMap g hsq ha, tensorChart, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr (actualTensorIso R B K).inv.surjective, Set.image_univ]

end Chart

section ChartPoints

attribute [local instance] Algebra.TensorProduct.rightAlgebra locallyOfFinitePresentation_spec

variable {C S : Scheme.{u}} (g : C ⟶ S) [LocallyOfFinitePresentation g]
  {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {jV : Spec (.of R) ⟶ S} [IsOpenImmersion jV] {jB : Spec (.of B) ⟶ C} [IsOpenImmersion jB]
  (hsq : jB ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jV)
  {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K] {a : Spec (.of K) ⟶ S}
  (ha : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ jV = a)

include hsq ha in
omit [LocallyOfFinitePresentation g] [Algebra.FiniteType R B] [IsAlgClosed K] in
/-- A closed point of the geometric fibre lying over `Spec B ⊆ C` is the image of a closed point
of `Spec (K ⊗_R B)` under the chart. -/
theorem exists_tensorChart_eq (y : pullback (C := Scheme.{u}) g a) (hy : IsClosed ({y} : Set (pullback (C := Scheme.{u}) g a)))
    (hx : pullback.fst g a y ∈ Set.range jB) :
    ∃ z : PrimeSpectrum (K ⊗[R] B), tensorChart g hsq ha z = y ∧
      IsClosed ({z} : Set (Spec (.of (K ⊗[R] B)))) := by
  have hy' : y ∈ Set.range (tensorChart g hsq ha) := by
    rw [range_tensorChart]
    exact hx
  obtain ⟨z, rfl⟩ := hy'
  refine ⟨z, rfl, ?_⟩
  have : ({z} : Set (Spec (.of (K ⊗[R] B)))) = tensorChart g hsq ha ⁻¹' {tensorChart g hsq ha z} := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ (tensorChart g hsq ha).isOpenEmbedding.injective h⟩
  rw [this]
  exact hy.preimage (tensorChart g hsq ha).continuous

omit [IsAlgClosed K] in
/-- Smooth points of the geometric fibre give smooth points of the chart. -/
theorem mem_smoothLocus_of_tensorChart (z : PrimeSpectrum (K ⊗[R] B))
    (h : tensorChart g hsq ha z ∈ (pullback.snd g a).smoothLocus) :
    z ∈ (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B)))).smoothLocus := by
  have h0 : IsSmoothAt (pullback.snd g a) (tensorChart g hsq ha z) := h
  have h1 : IsSmoothAt (tensorChart g hsq ha) z := isSmoothAt_of_smooth (tensorChart g hsq ha) z
  have h' := isSmoothAt_comp h1 h0
  rw [tensorChart_snd] at h'
  exact h'

omit [Algebra.FiniteType R B] in
/-- Ordinary double points of the geometric fibre give nodes of the chart. -/
theorem isGeometricOrdinaryDoublePoint_of_tensorChart (z : PrimeSpectrum (K ⊗[R] B))
    (hz : IsClosed ({z} : Set (Spec (.of (K ⊗[R] B)))))
    (h : IsGeometricOrdinaryDoublePoint (pullback.snd g a) (tensorChart g hsq ha z)) :
    IsGeometricOrdinaryDoublePoint (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B)))) z := by
  have := isIso_residueFieldMap_of_isClosed (K := K)
    (q := tensorChart g hsq ha ≫ pullback.snd g a) (q' := pullback.snd g a)
    (tensorChart g hsq ha) rfl hz
  have h' := isGeometricOrdinaryDoublePoint_of_etale (tensorChart g hsq ha) (pullback.snd g a) z h
  rwa [tensorChart_snd] at h'

omit [LocallyOfFinitePresentation g] [Algebra.FiniteType R B] [IsAlgClosed K]
  [IsOpenImmersion jV] [IsOpenImmersion jB] in
/-- The chart point lies over the point `comap z` of `Spec B`. -/
theorem jB_comap_eq (z : PrimeSpectrum (K ⊗[R] B)) :
    jB (PrimeSpectrum.comap (algebraMap B (K ⊗[R] B)) z) =
      pullback.fst g a (tensorChart g hsq ha z) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap B (K ⊗[R] B))) ≫ jB) z =
    (tensorChart g hsq ha ≫ pullback.fst g a) z
  rw [tensorChart_fst]

end ChartPoints

section Affine

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

attribute [local instance] locallyOfFinitePresentation_spec

/-- **The affine criterion.** Let `B` be a flat, finitely presented `R`-algebra whose geometric
fibres have pure dimension one. If every closed point of every geometric fibre `K ⊗_R B` is at most a
node, then `Spec B → Spec R` is a nodal curve. -/
theorem isNodalCurve_spec [Module.Flat R B] [Algebra.FinitePresentation R B]
    (hpure : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (.of R))
      (Z : Set (pullback (C := Scheme.{u}) (Spec.map (CommRingCat.ofHom (algebraMap R B))) a)),
      Z ∈ irreducibleComponents
        (pullback (C := Scheme.{u}) (Spec.map (CommRingCat.ofHom (algebraMap R B))) a) →
        topologicalKrullDim Z = 1)
    (hB : GeometricallyAtMostNodal R B) :
    IsNodalCurve (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  refine ⟨hpure, fun K _ _ a y hy => ?_⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = a := ⟨_, Spec.map_preimage a⟩
  let : Algebra R K := ψ.hom.toAlgebra
  have key : ∀ y : ActualBaseChange R B K, IsClosed ({y} : Set (ActualBaseChange R B K)) →
      y ∈ (pullback.snd (originalFamily R B)
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).smoothLocus ∨
      IsGeometricOrdinaryDoublePoint (pullback.snd (originalFamily R B)
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) y := by
    intro y hy
    let e := actualTensorIso R B K
    let q' := Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B)))
    have hsnd : e.hom ≫ q' = pullback.snd _ _ := actualTensorIso_hom_field R B K
    have hz : IsClosed ({e.hom y} : Set (Spec (.of (K ⊗[R] B)))) := by
      have : ({e.hom y} : Set (Spec (.of (K ⊗[R] B)))) = e.inv ⁻¹' {y} := by
        ext w
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro rfl
          change (e.hom ≫ e.inv) y = y
          rw [e.hom_inv_id]
          rfl
        · rintro rfl
          change w = (e.inv ≫ e.hom) w
          rw [e.inv_hom_id]
          rfl
      rw [this]
      exact hy.preimage e.inv.continuous
    have : (e.hom y).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hz
    have hpureT : ∀ W ∈ irreducibleComponents (Spec (.of (K ⊗[R] B))), topologicalKrullDim W = 1 :=
      pure_of_etale (q' := pullback.snd (originalFamily R B)
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) e.inv (hpure K _)
    have hdim := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT (e.hom y) hz
    rcases hB K (e.hom y).asIdeal with h1 | hnode
    · left
      have hs : e.hom y ∈ q'.smoothLocus := (mem_smoothLocus_spec_iff (e.hom y) hdim).mpr h1
      have h' : IsSmoothAt (e.hom ≫ q') y := isSmoothAt_comp (isSmoothAt_of_smooth e.hom y) hs
      rw [hsnd] at h'
      exact h'
    · right
      have hn := (isGeometricOrdinaryDoublePoint_spec_iff (e.hom y)).mpr hnode
      have h' := isGeometricOrdinaryDoublePoint_of_etale e.hom q' y hn
      rwa [hsnd] at h'
  exact key y hy

end Affine

section Finish

variable {C S : Scheme.{u}} (g : C ⟶ S) [LocallyOfFiniteType g]
  (hpure : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    (Z : Set (pullback (C := Scheme.{u}) g a)), Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) g a) → topologicalKrullDim Z = 1)
  {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  {jV : Spec (.of R) ⟶ S} [IsOpenImmersion jV] {jB : Spec (.of B) ⟶ C} [IsOpenImmersion jB]
  (hsq : jB ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jV)

include hpure hsq in
/-- Over an affine chart `Spec B → C` of a curve with pure one-dimensional geometric fibres, if
`B` is flat, finitely presented and geometrically at most nodal over `R`, then `Spec B → S` is a
nodal curve. -/
theorem isNodalCurve_comp_of_geometricallyAtMostNodal [Module.Flat R B]
    [Algebra.FinitePresentation R B] (hB : GeometricallyAtMostNodal R B) :
    IsNodalCurve (jB ≫ g) := by
  rw [hsq]
  have : IsNodalCurve (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    apply isNodalCurve_spec _ hB
    intro K _ _ a Z hZ
    obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = a := ⟨_, Spec.map_preimage a⟩
    let : Algebra R K := ψ.hom.toAlgebra
    exact pure_of_etale (q' := pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ jV))
      (chartMap g hsq rfl) (hpure K _) Z hZ
  exact IsNodalCurve.comp_isOpenImmersion _ jV

include hpure hsq in
/-- The open image of such a chart is a nodal neighbourhood. -/
theorem exists_opens_of_geometricallyAtMostNodal [Module.Flat R B]
    [Algebra.FinitePresentation R B] (hB : GeometricallyAtMostNodal R B) (x : C)
    (hx : x ∈ Set.range jB) : ∃ U : C.Opens, x ∈ U ∧ IsNodalCurve (U.ι ≫ g) := by
  refine ⟨jB.opensRange, hx, ?_⟩
  have h := isNodalCurve_comp_of_geometricallyAtMostNodal g hpure hsq hB
  have hι : jB.opensRange.ι = jB.isoOpensRange.inv ≫ jB := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  rw [hι, Category.assoc]
  exact IsNodalCurve.etale_comp _ _

omit [IsOpenImmersion jV] [IsOpenImmersion jB] [LocallyOfFiniteType g] in
include hsq in
/-- The chart restricted to a basic open `D(f) ⊆ Spec B`. -/
theorem localization_chart_sq (f : B) :
    (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f))) ≫ jB) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) ≫ jV := by
  rw [Category.assoc, hsq, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

omit [IsOpenImmersion jB] in
/-- Points of `D(f)`. -/
theorem mem_range_localization_chart (f : B) (p : PrimeSpectrum B) (hf : f ∉ p.asIdeal) :
    jB p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f))) ≫ jB) := by
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hf
  obtain ⟨p', hp'⟩ := hp
  exact ⟨p', by rw [← hp']; rfl⟩

end Finish

section Main

attribute [local instance] Algebra.TensorProduct.rightAlgebra locallyOfFinitePresentation_spec

variable {C S : Scheme.{u}} (g : C ⟶ S)

/-- The geometric fibres of `g` have pure dimension one (Temkin's `S`-curves, T:1672). -/
def PureOneDimensionalFibres : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    (Z : Set (pullback (C := Scheme.{u}) g a)),
    Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) g a) → topologicalKrullDim Z = 1

variable [Flat g] [LocallyOfFinitePresentation g]

/-- **The semi-stable locus is open** (Temkin, Lemma 5.1(i), T:3282–3292). Let `g : C → S` be flat,
locally of finite presentation, with geometric fibres of pure dimension one. If a closed point `y`
of a geometric fibre `C ×_S Spec K` is a smooth point or an ordinary double point, then its image
in `C` has an open neighbourhood `U` with `U → S` a nodal curve. -/
theorem exists_isNodalCurve_nbhd (hpure : PureOneDimensionalFibres g) (K : Type u) [Field K]
    [IsAlgClosed K] (a : Spec (.of K) ⟶ S) (y : pullback (C := Scheme.{u}) g a)
    (hy : IsClosed ({y} : Set (pullback (C := Scheme.{u}) g a)))
    (hny : y ∈ (pullback.snd g a).smoothLocus ∨
      IsGeometricOrdinaryDoublePoint (pullback.snd g a) y) :
    ∃ U : C.Opens, pullback.fst g a y ∈ U ∧ IsNodalCurve (U.ι ≫ g) := by
  set x := pullback.fst g a y with hxdef
  -- affine charts `Spec B = W ⊆ C` over `Spec R = V ⊆ S`
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := g ⁻¹ᵁ V) hxV
  have hle : W ≤ g ⁻¹ᵁ V := hWV
  let : Algebra Γ(S, V) Γ(C, W) := (g.appLE V W hle).hom.toAlgebra
  have : Module.Flat Γ(S, V) Γ(C, W) :=
    HasRingHomProperty.appLE @Flat g inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have : Algebra.FinitePresentation Γ(S, V) Γ(C, W) :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation g inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have hsq : hW.fromSpec ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(C, W))) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g hV hW hle).symm
  -- the geometric point factors through `V`
  have hrange : Set.range a ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨t, rfl⟩
    rw [hV.range_fromSpec]
    have ht : t = pullback.snd g a y := Subsingleton.elim _ _
    rw [ht, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hxV
  obtain ⟨ψ, hψ⟩ : ∃ ψ, Spec.map ψ = IsOpenImmersion.lift hV.fromSpec a hrange :=
    ⟨_, Spec.map_preimage _⟩
  let : Algebra Γ(S, V) K := ψ.hom.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec = a := by
    change Spec.map ψ ≫ _ = _
    rw [hψ, IsOpenImmersion.lift_fac]
  -- the point on the chart `Spec (K ⊗_R B)`
  have hxB : x ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact hxW
  obtain ⟨z, hzy, hzc⟩ := exists_tensorChart_eq g hsq ha y hy hxB
  have : z.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mp hzc
  have hxz : hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(C, W) (K ⊗[Γ(S, V)] Γ(C, W))) z) = x := by
    rw [jB_comap_eq g hsq ha z, hzy]
  rcases hny with hs | hn
  · -- a smooth point: `B_f` has principal geometric maximal ideals
    have hpureT : ∀ Z ∈ irreducibleComponents (Spec (.of (K ⊗[Γ(S, V)] Γ(C, W)))),
        topologicalKrullDim Z = 1 :=
      pure_of_etale (q' := pullback.snd g a) (tensorChart g hsq ha) (hpure K a)
    have hdim := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT z hzc
    have hzs := mem_smoothLocus_of_tensorChart g hsq ha z (hzy ▸ hs)
    have h1 := (mem_smoothLocus_spec_iff z hdim).mp hzs
    obtain ⟨f, hf, hgeo⟩ := exists_away_of_spanFinrank_le_one z.asIdeal h1
    have : Module.Flat Γ(S, V) (Localization.Away f) := Module.Flat.trans _ Γ(C, W) _
    have : Algebra.FinitePresentation Γ(S, V) (Localization.Away f) :=
      Algebra.FinitePresentation.trans _ Γ(C, W) _
    refine exists_opens_of_geometricallyAtMostNodal g hpure (localization_chart_sq g hsq f)
      (fun K' _ _ _ y' _ => Or.inl (hgeo K' y')) x ?_
    rw [← hxz]
    exact mem_range_localization_chart f _ hf
  · -- a node: the hypersurface presentation of `B_f`
    have hzn := isGeometricOrdinaryDoublePoint_of_tensorChart g hsq ha z hzc (hzy ▸ hn)
    obtain ⟨f, hf, hnext⟩ :=
      exists_away_of_node z.asIdeal ((isGeometricOrdinaryDoublePoint_spec_iff z).mp hzn)
    have : Module.Flat Γ(S, V) (Localization.Away f) := Module.Flat.trans _ Γ(C, W) _
    have : Algebra.FinitePresentation Γ(S, V) (Localization.Away f) :=
      Algebra.FinitePresentation.trans _ Γ(C, W) _
    have hsq₁ := localization_chart_sq g hsq f
    have hxB₁ : x ∈ Set.range
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) (Localization.Away f))) ≫ hW.fromSpec) := by
      rw [← hxz]
      exact mem_range_localization_chart f _ hf
    obtain ⟨z₁, hz₁y, hz₁c⟩ := exists_tensorChart_eq g hsq₁ ha y hy hxB₁
    have : z₁.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₁).mp hz₁c
    have hz₁n := isGeometricOrdinaryDoublePoint_of_tensorChart g hsq₁ ha z₁ hz₁c (hz₁y ▸ hn)
    obtain ⟨s, hs, hgeo⟩ :=
      hnext K z₁.asIdeal ((isGeometricOrdinaryDoublePoint_spec_iff z₁).mp hz₁n)
    have : Module.Flat Γ(S, V) (Localization.Away s) :=
      Module.Flat.trans _ (Localization.Away f) _
    have : Algebra.FinitePresentation Γ(S, V) (Localization.Away s) :=
      Algebra.FinitePresentation.trans _ (Localization.Away f) _
    have hxz₁ : (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) (Localization.Away f))) ≫
        hW.fromSpec) (PrimeSpectrum.comap (algebraMap (Localization.Away f)
          (K ⊗[Γ(S, V)] Localization.Away f)) z₁) = x := by
      rw [jB_comap_eq g hsq₁ ha z₁, hz₁y]
    refine exists_opens_of_geometricallyAtMostNodal g hpure (localization_chart_sq g hsq₁ s)
      hgeo x ?_
    rw [← hxz₁]
    exact mem_range_localization_chart s _ hs

end Main

section Locus

variable {C S : Scheme.{u}} (g : C ⟶ S)

/-- The *nodal locus* of `g : C → S`: the union of all open `U ⊆ C` such that `U → S` is a nodal
curve. -/
def nodalLocus : C.Opens := sSup {U : C.Opens | IsNodalCurve (U.ι ≫ g)}

theorem le_nodalLocus {U : C.Opens} (hU : IsNodalCurve (U.ι ≫ g)) : U ≤ nodalLocus g :=
  le_sSup hU

/-- **`g` is a nodal curve over its nodal locus**, which is therefore the largest open of `C` over
which `g` is a nodal curve. -/
theorem isNodalCurve_nodalLocus : IsNodalCurve ((nodalLocus g).ι ≫ g) := by
  apply IsNodalCurve.of_openCover
  intro x
  obtain ⟨U, hU, hxU⟩ : ∃ U : C.Opens, U ∈ {U : C.Opens | IsNodalCurve (U.ι ≫ g)} ∧
      (nodalLocus g).ι x ∈ U :=
    TopologicalSpace.Opens.mem_sSup.mp x.2
  let U' : (nodalLocus g : Scheme).Opens := (nodalLocus g).ι ⁻¹ᵁ U
  refine ⟨U', hxU, ?_⟩
  have hrange : Set.range (U'.ι ≫ (nodalLocus g).ι) ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact w.2
  let e := IsOpenImmersion.lift U.ι (U'.ι ≫ (nodalLocus g).ι) hrange
  have he : e ≫ U.ι = U'.ι ≫ (nodalLocus g).ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (e ≫ U.ι) := by rw [he]; infer_instance
  have : IsOpenImmersion e := IsOpenImmersion.of_comp e U.ι
  have : IsNodalCurve (U.ι ≫ g) := hU
  rw [← Category.assoc, ← he, Category.assoc]
  exact IsNodalCurve.etale_comp e (U.ι ≫ g)

/-- `g` is a nodal curve iff its nodal locus is all of `C`. -/
theorem isNodalCurve_iff_nodalLocus_eq_top : IsNodalCurve g ↔ nodalLocus g = ⊤ := by
  constructor
  · intro h
    exact top_unique (le_nodalLocus g (IsNodalCurve.etale_comp _ g))
  · intro h
    apply IsNodalCurve.of_openCover
    intro x
    exact ⟨nodalLocus g, by rw [h]; trivial, isNodalCurve_nodalLocus g⟩

variable [Flat g] [LocallyOfFinitePresentation g]

/-- Closed smooth points and ordinary double points of geometric fibres lie over the nodal
locus. -/
theorem fst_mem_nodalLocus (hpure : PureOneDimensionalFibres g) (K : Type u) [Field K]
    [IsAlgClosed K] (a : Spec (.of K) ⟶ S) (y : pullback (C := Scheme.{u}) g a)
    (hy : IsClosed ({y} : Set (pullback (C := Scheme.{u}) g a)))
    (hny : y ∈ (pullback.snd g a).smoothLocus ∨
      IsGeometricOrdinaryDoublePoint (pullback.snd g a) y) :
    pullback.fst g a y ∈ nodalLocus g := by
  obtain ⟨U, hxU, hU⟩ := exists_isNodalCurve_nbhd g hpure K a y hy hny
  exact le_nodalLocus g hU hxU

/-- **A nodal geometric fibre lies over the nodal locus**: if the geometric fibre of `g` at
`a : Spec K → S` is a nodal curve over `K`, then every point of it maps into `nodalLocus g`. -/
theorem fst_mem_nodalLocus_of_isNodalFiber (hpure : PureOneDimensionalFibres g) (K : Type u)
    [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S) (h : IsNodalFiber (pullback.snd g a))
    (y : pullback (C := Scheme.{u}) g a) : pullback.fst g a y ∈ nodalLocus g := by
  have : JacobsonSpace (pullback (C := Scheme.{u}) g a) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd g a)
  obtain ⟨y₀, hy₀, hy₀c⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty y).closure
    isClosed_closure.isLocallyClosed
  have hsp : y ⤳ y₀ := specializes_iff_mem_closure.mpr hy₀
  have h₀ := fst_mem_nodalLocus g hpure K a y₀ hy₀c (by
    rcases h.nodes y₀ hy₀c with h' | h'
    · exact Or.inl h'
    · exact Or.inr h')
  exact (hsp.map (pullback.fst g a).continuous).mem_open (nodalLocus g).isOpen h₀

end Locus

section Restrict

variable {C S : Scheme.{u}} (g : C ⟶ S)

/-- Every open of the nodal locus is a nodal curve over `S`. -/
theorem isNodalCurve_of_le_nodalLocus {U : C.Opens} (hU : U ≤ nodalLocus g) :
    IsNodalCurve (U.ι ≫ g) := by
  have hrange : Set.range U.ι ⊆ Set.range (nodalLocus g).ι := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hU
  let e := IsOpenImmersion.lift (nodalLocus g).ι U.ι hrange
  have he : e ≫ (nodalLocus g).ι = U.ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (e ≫ (nodalLocus g).ι) := by rw [he]; infer_instance
  have : IsOpenImmersion e := IsOpenImmersion.of_comp e (nodalLocus g).ι
  have := isNodalCurve_nodalLocus g
  rw [← he, Category.assoc]
  exact IsNodalCurve.etale_comp e ((nodalLocus g).ι ≫ g)

end Restrict

section Proper

variable {C S : Scheme.{u}} (g : C ⟶ S) [UniversallyClosed g]

/-- For a universally closed `g`, the open set of points of `S` whose whole fibre lies in the
nodal locus of `g`. -/
def nodalBase : S.Opens :=
  ⟨(g '' ((nodalLocus g : Set C)ᶜ))ᶜ,
    (g.isClosedMap _ (nodalLocus g).isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_nodalBase_iff (s : S) : s ∈ nodalBase g ↔ ∀ x : C, g x = s → x ∈ nodalLocus g := by
  change s ∉ g '' ((nodalLocus g : Set C)ᶜ) ↔ _
  constructor
  · intro h x hx
    by_contra hxN
    exact h ⟨x, hxN, hx⟩
  · rintro h ⟨x, hxN, hx⟩
    exact hxN (h x hx)

/-- `g` is a nodal curve over `nodalBase g`. -/
theorem isNodalCurve_preimage_nodalBase : IsNodalCurve ((g ⁻¹ᵁ nodalBase g).ι ≫ g) :=
  isNodalCurve_of_le_nodalLocus g fun x hx => (mem_nodalBase_iff g (g x)).mp hx x rfl

/-- **Geometric fibres over `nodalBase g` are nodal curves.** -/
theorem isNodalFiber_of_mem_nodalBase (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (ha : a (IsLocalRing.closedPoint K) ∈ nodalBase g) :
    IsNodalFiber (pullback.snd g a) := by
  have := isNodalCurve_nodalLocus g
  let F := pullbackCompMap (nodalLocus g).ι g a
  have hF : Function.Surjective F := by
    intro y
    have hy : y ∈ Set.range F := by
      rw [range_pullbackCompMap, Scheme.Opens.range_ι]
      apply (mem_nodalBase_iff g _).mp ha
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      congr 1
      exact Subsingleton.elim _ _
    exact hy
  have : IsIso F := (isIso_iff_isOpenImmersion_and_surjective F).mpr ⟨inferInstance, ⟨hF⟩⟩
  have h := (IsNodalCurve.isNodalFiber ((nodalLocus g).ι ≫ g) K a).of_etale (inv F)
  have hc : inv F ≫ pullback.snd ((nodalLocus g).ι ≫ g) a = pullback.snd g a := by
    rw [IsIso.inv_comp_eq, pullbackCompMap_snd]
  rwa [hc] at h

/-- **A nodal geometric fibre lies over `nodalBase g`.** -/
theorem mem_nodalBase_of_isNodalFiber [Flat g] [LocallyOfFinitePresentation g]
    (hpure : PureOneDimensionalFibres g) (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (h : IsNodalFiber (pullback.snd g a)) :
    a (IsLocalRing.closedPoint K) ∈ nodalBase g := by
  rw [mem_nodalBase_iff]
  intro x hx
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := a) x
    (IsLocalRing.closedPoint K : Spec (.of K)) hx
  rw [← hy]
  exact fst_mem_nodalLocus_of_isNodalFiber g hpure K a h y

end Proper

end DeJongAlterations.StableModification.Curves.SemistableOpen
