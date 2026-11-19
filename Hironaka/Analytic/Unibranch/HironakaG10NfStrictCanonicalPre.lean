import Hironaka.Analytic.Unibranch.HironakaG10NfChartStalk
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreDescent
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreGlue
import Hironaka.Analytic.Unibranch.HironakaG10NfJointPivotCanonical
import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare
import Hironaka.Analytic.Unibranch.HironakaG10NfStrictMembership
import Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport

/-!
# H3.4 (`strict` on the canonical chart, preamble): builders, readouts and the fibre conjunct

Lane G10H3, run 0081 (fields `strict`, `strict₀` of `HironakaG10NfGeoFibreModel.GeoFibreModel`).  Canonical setting of
`HironakaG10SbCanonicalStrictTorsion`.  The fast part of the strict field (the canonical instantiation of
`strict_builder` is assembled piece by piece in a later module):

* `jointTorsionQuotientEquiv_symm_strict` — the inverse torsion readout on the joint strict stalk map;
* `fibre_native_generic`, `fibre_native` — the native fibre identity: `β(χ^♯ r) ∈ ψ(𝔪) ⇒ r ∈ F^♯(𝔪)`;
* `strict_builder` — the fibre conjunct `q^{♯-1}(ind^♯ 𝔪) ⊆ F^♯ 𝔪` from the two readouts (generic builder);
* `strict0_builder`, `flat_quotMap_equiv_comp` — the flatness transfer of `strict₀` (generic builder);
* `sourceProjection`, `sourceReadout`, `betaC`, `graphSquare` — the canonical source readout data;
* `pivotTorsion_ne_top` — a proper torsion bound `Tors_w ⊆ ψ(𝔪)` forces `Tors_w ≠ ⊤`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar BlowupConstruction BlowupStrictSubmanifold
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion

section TorsionEquiv

variable (d' t' : ℕ) (j' : Fin t') (b' : Fin (d'+t') → ℂ) (U' : Opens (ComplexModel (d'+t'))) (W' : Set U')
  {n' : ℕ} {Y' : Type} [TopologicalSpace Y'] [ChartedSpace (ComplexModel n') Y']
  (f' : realOpenChartDomain d' t' j' b' U' → Y') (V' : Set Y')
  (h0' : (0 : ComplexModel (d'+t')) ∈ U') (hW' : IsComplexAnalyticSubset (n := d'+t') W')
  (hf' : Continuous f') (hland' : realOpenStrictTransform d' t' j' b' U' W' ⊆ f' ⁻¹' V')

/-- The inverse of the torsion-quotient equivalence on the joint strict stalk map. -/
theorem jointTorsionQuotientEquiv_symm_strict (y : realOpenChartDomain d' t' j' b' U')
    (hy : y ∈ localDomain d' t' j' b' U' W' h0' hW') (hyS : y ∈ realOpenStrictTransform d' t' j' b' U' W')
    (s' : JointQuotient (n := n') d' t' j' b' U' W' f' V' y) :
    (jointTorsionQuotientEquiv (n := n') d' t' j' b' U' W' f' V' h0' hW' hf' hland' y hy hyS).symm
        (jointStrictStalkMap (n := n') d' t' j' b' U' W' f' V' h0' hW' hf' hland' y hy hyS s') =
      Ideal.Quotient.mk (pivotTorsion (n := n') d' t' j' b' U' W' f' V' y) s' :=
  (RingEquiv.symm_apply_eq _).mpr
    (jointTorsionQuotientEquiv_mk (n := n') d' t' j' b' U' W' f' V' h0' hW' hf' hland' y hy hyS s').symm

end TorsionEquiv

section Generic

open Hironaka.Analytic.Unibranch.HironakaG10NfChartStalk

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r)) (j : Fin r)
  (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)
  {m : ℕ} {Yt : Type} [TopologicalSpace Yt] [ChartedSpace (ComplexModel m) Yt] [IsComplexManifold m Yt]
  (f : domG a j v → Yt) (V : Set Yt) (hf : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel m) ∞ f)
  (hV : IsComplexAnalyticSubset (n := m) V)
  (hraw : ∀ y : domG a j v, Ideal.map ((ChartedSpace.locallyRingedSpaceMap (projG a j v hvj)
      (projG_contMDiff a j v hvj)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) W) (projG a j v hvj y)) ≤
    rawAnalyticIdeal n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) y)
  {k' : ℕ} {MT : Type} [TopologicalSpace MT] [ChartedSpace (ComplexModel k') MT] [IsComplexManifold k' MT]
  {Pm : P × ComplexModel r → MT} (hPm : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel k') ∞ Pm)
  {WT : Set MT} (hmaps : ∀ z ∈ W, Pm z ∈ WT)
  {Xc Yc : LocallyRingedSpace.{0}}
  (chartX : actualSubspaceLocallyRingedSpace (n := n+r) W ⟶ Xc)
  (chartY : actualSubspaceLocallyRingedSpace (n := k') WT ⟶ Yc)
  [LocallyRingedSpace.IsOpenImmersion chartX] [LocallyRingedSpace.IsOpenImmersion chartY]
  (Fm : Xc ⟶ Yc) (hsq : actualSubspaceMap hPm hmaps ≫ chartY = chartX ≫ Fm)

include hsq in
/-- **The fibre identity on native stalks (generic).** -/
theorem fibre_native_generic (w : domG a j v) (hΓ : projG a j v hvj w ∈ W) (hwV : f w ∈ V)
    {A : Type*} [CommRing A] [IsLocalRing A] (φ : A →+* TargetStalk (n := m) n r j (fun i => v i)
      (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) f V w hwV) [IsLocalHom φ]
    (hFI : ∀ h : actualComplexStructureStalk (n := n+r) (projG a j v hvj w),
      ((ChartedSpace.locallyRingedSpaceMap (projG a j v hvj) (projG_contMDiff a j v hvj)).stalkMap w).hom h ∈
        jointIdeal (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
          (WG a W j v) f V w ⊔
        Ideal.map ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap w).hom
          (IsLocalRing.maximalIdeal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel m) Yt).presheaf.stalk (f w))) →
      h ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) W) (projG a j v hvj w) ⊔
        Ideal.map ((ChartedSpace.locallyRingedSpaceMap Pm hPm).stalkMap (projG a j v hvj w)).hom
          (IsLocalRing.maximalIdeal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel k') MT).presheaf.stalk
            (Pm (projG a j v hvj w)))))
    (rr : Xc.presheaf.stalk (chartX.base ⟨projG a j v hvj w, hΓ⟩))
    (hr : betaG a W j v hvj f V hraw w hΓ ((chartX.stalkMap ⟨projG a j v hvj w, hΓ⟩).hom rr) ∈
      Ideal.map ((targetStalkToJoint (n := m) n r j (fun i => v i)
        (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V hf hV w hwV).comp φ)
        (IsLocalRing.maximalIdeal A)) :
    rr ∈ Ideal.map (Fm.stalkMap (chartX.base ⟨projG a j v hvj w, hΓ⟩)).hom (IsLocalRing.maximalIdeal _) := by
  have hsurj : Function.Surjective
      ((actualSubspaceInclusion (n := n+r) W).stalkMap ⟨projG a j v hvj w, hΓ⟩).hom :=
    actualSubspaceInclusionRingedHom_stalk_surjective (n := n+r) W ⟨projG a j v hvj w, hΓ⟩
  obtain ⟨h, hh⟩ := hsurj ((chartX.stalkMap ⟨projG a j v hvj w, hΓ⟩).hom rr)
  refine HironakaG10NfFibreDescent.mem_map_of_graph_descent hPm hmaps chartX chartY Fm hsq
    ⟨projG a j v hvj w, hΓ⟩ rr h hh.symm (hFI h ?_)
  have h1 := HironakaG10NfFibreDescent.map_targetStalkToJoint_comp_le_ambient n r j (fun i => v i)
    (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V hf hV w hwV φ hr
  rw [← hh, betaG_incl] at h1
  have h2 := Ideal.mem_comap.mpr h1
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker] at h2
  rwa [sup_comm] at h2

/-- Transport of membership in the fibre ideal along an equality of points. -/
theorem mem_fibre_transport {A₀ B₀ : LocallyRingedSpace.{0}} (Fm₀ : A₀ ⟶ B₀) {P₁ P₂ : A₀} (h : P₁ = P₂)
    (r : A₀.presheaf.stalk P₁)
    (hr : (eqToHom (congrArg A₀.presheaf.stalk h)).hom r ∈
      Ideal.map (Fm₀.stalkMap P₂).hom (IsLocalRing.maximalIdeal _)) :
    r ∈ Ideal.map (Fm₀.stalkMap P₁).hom (IsLocalRing.maximalIdeal _) := by
  subst h
  simpa using hr

/-- The maximal ideal transported along an equality of points. -/
theorem map_maximal_transport {A₀ : LocallyRingedSpace.{0}} {R : Type*} [CommRing R] {P₁ P₂ : A₀}
    (h : P₁ = P₂) (φ : A₀.presheaf.stalk P₂ →+* R) :
    Ideal.map (φ.comp (eqToHom (congrArg A₀.presheaf.stalk h)).hom) (IsLocalRing.maximalIdeal _) =
      Ideal.map φ (IsLocalRing.maximalIdeal _) := by
  subst h
  simp


/-- **The fibre conjunct from the two readouts (generic builder).**  All the canonical objects enter as variables;
the two readouts are taken literally in the forms of `HironakaG10NfChartStalk.readout_generic` (source) and
`HironakaG10GlCanonicalBaseSquare.canonical_square_joint` (target), the two chart presentations being identified by
the equations `hci`, `hsc`, `hjS` (definitional on the canonical chart). -/
theorem strict_builder {S C Ys Xc Bl Yc : LocallyRingedSpace.{0}}
    (ci₁ ci₂ : S ⟶ C) (hci : ci₁ = ci₂) [LocallyRingedSpace.IsOpenImmersion ci₂]
    (sc₁ sc₂ : C ⟶ Ys) (hsc : sc₁ = sc₂) [LocallyRingedSpace.IsOpenImmersion sc₂]
    (πA : Ys ⟶ Xc) (ind : Ys ⟶ Bl) (Fm : Xc ⟶ Yc) (w' : S)
    {Bq : Type} [CommRing Bq] (T : Ideal Bq) (jS₁ jS₂ : Bq →+* S.presheaf.stalk w') (hjS : jS₁ = jS₂)
    (E : Bq ⧸ T ≃+* S.presheaf.stalk w') (hE : ∀ s, E (Ideal.Quotient.mk T s) = jS₂ s)
    {RΓ : Type} [CommRing RΓ] {Pq : Xc} (hs : Pq = πA.base (sc₁.base (ci₁.base w')))
    (χ : Xc.presheaf.stalk Pq →+* RΓ) (β₀ : RΓ →+* Bq)
    (hq_raw : ∀ rr, (ci₁.stalkMap w').hom ((sc₁.stalkMap (ci₁.base w')).hom
        ((πA.stalkMap (sc₁.base (ci₁.base w'))).hom rr)) =
      jS₁ (β₀ (χ ((eqToHom (congrArg Xc.presheaf.stalk hs.symm)).hom rr))))
    (Ψ : Bl.presheaf.stalk (ind.base (sc₂.base (ci₂.base w'))) → Bq)
    (hf_raw : ∀ a, (ci₂.stalkMap w').hom ((sc₂.stalkMap (ci₂.base w')).hom
        ((ind.stalkMap (sc₂.base (ci₂.base w'))).hom a)) = jS₂ (Ψ a))
    (ψ : Bl.presheaf.stalk (ind.base (sc₂.base (ci₂.base w'))) →+* Bq) (hΨ : ∀ a, Ψ a = ψ a)
    (hT : T ≤ Ideal.map ψ (IsLocalRing.maximalIdeal _))
    (hFI : ∀ r : Xc.presheaf.stalk Pq, β₀ (χ r) ∈ Ideal.map ψ (IsLocalRing.maximalIdeal _) →
      r ∈ Ideal.map (Fm.stalkMap Pq).hom (IsLocalRing.maximalIdeal _)) :
    Ideal.comap (πA.stalkMap (sc₂.base (ci₂.base w'))).hom
        (Ideal.map (ind.stalkMap (sc₂.base (ci₂.base w'))).hom (IsLocalRing.maximalIdeal _)) ≤
      Ideal.map (Fm.stalkMap (πA.base (sc₂.base (ci₂.base w')))).hom (IsLocalRing.maximalIdeal _) := by
  subst hci hsc hjS
  let e : Ys.presheaf.stalk (sc₁.base (ci₁.base w')) ≃+* Bq ⧸ T :=
    (Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv sc₁ (ci₁.base w')).trans
      ((Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv ci₁ w').trans E.symm)
  have hEs : ∀ s, E.symm (jS₁ s) = Ideal.Quotient.mk T s := fun s =>
    (RingEquiv.symm_apply_eq _).mpr (hE s).symm
  refine HironakaG10NfFibreGlue.comap_fibre_le (πA.stalkMap (sc₁.base (ci₁.base w'))).hom
    (ind.stalkMap (sc₁.base (ci₁.base w'))).hom (Fm.stalkMap (πA.base (sc₁.base (ci₁.base w')))).hom ψ
    (β₀.comp (χ.comp (eqToHom (congrArg Xc.presheaf.stalk hs.symm)).hom)) T e ?_ ?_ _ _ hT ?_
  · intro rr
    exact (congrArg E.symm (hq_raw rr)).trans (hEs _)
  · intro a
    exact (congrArg E.symm ((hf_raw a).trans (congrArg jS₁ (hΨ a)))).trans (hEs _)
  · intro rr hrr
    have h1 := hFI _ hrr
    subst hs
    simpa using h1

/-- Flatness of a quotient map is preserved by composing with a ring isomorphism on the target. -/
theorem flat_quotMap_equiv_comp {A R R' : Type} [CommRing A] [CommRing R] [CommRing R'] (e : R ≃+* R')
    (φ : A →+* R) (J : Ideal A) (h : (HironakaG10HirFlatQuotient.quotMap φ J).Flat) : (HironakaG10HirFlatQuotient.quotMap (e.toRingHom.comp φ) J).Flat := by
  refine HironakaG10NfFlatTransport.flat_quotMap_of_equiv_comp e.symm (e.toRingHom.comp φ) J ?_
  have he : e.symm.toRingHom.comp (e.toRingHom.comp φ) = φ := RingHom.ext fun a => e.symm_apply_apply (φ a)
  rw [he]
  exact h

/-- **The flatness transfer at a strict chart point (generic builder for `strict₀`)**: from the strict square
`ci^♯ sc^♯ ind^♯ = jS ∘ Ψ`, `Ψ = ψ` and the torsion readout `E`, flatness of the fibre stalk map of `ind` over `J₁`
gives flatness of `mk_T ∘ ψ` over `J₁`. -/
theorem strict0_builder {S C Ys Bl : LocallyRingedSpace.{0}}
    (ci : S ⟶ C) [LocallyRingedSpace.IsOpenImmersion ci] (sc : C ⟶ Ys) [LocallyRingedSpace.IsOpenImmersion sc]
    (ind : Ys ⟶ Bl) (w' : S)
    {Bq : Type} [CommRing Bq] (T : Ideal Bq) (jS : Bq →+* S.presheaf.stalk w')
    (E : Bq ⧸ T ≃+* S.presheaf.stalk w') (hE : ∀ s, E (Ideal.Quotient.mk T s) = jS s)
    (Ψ : Bl.presheaf.stalk (ind.base (sc.base (ci.base w'))) → Bq)
    (hf_raw : ∀ a, (ci.stalkMap w').hom ((sc.stalkMap (ci.base w')).hom
        ((ind.stalkMap (sc.base (ci.base w'))).hom a)) = jS (Ψ a))
    {P : Bl} (hp : ind.base (sc.base (ci.base w')) = P) (ψ : Bl.presheaf.stalk P →+* Bq)
    (hΨ : ∀ a, Ψ a = ψ ((eqToHom (congrArg Bl.presheaf.stalk hp)).hom a))
    (J₁ : Ideal (Bl.presheaf.stalk P))
    (h : (HironakaG10HirFlatQuotient.quotMap ((ind.stalkMap (sc.base (ci.base w'))).hom.comp
      (eqToHom (congrArg Bl.presheaf.stalk hp.symm)).hom) J₁).Flat) :
    (HironakaG10HirFlatQuotient.quotMap ((Ideal.Quotient.mk T).comp ψ) J₁).Flat := by
  subst hp
  let e : Ys.presheaf.stalk (sc.base (ci.base w')) ≃+* Bq ⧸ T :=
    (Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv sc (ci.base w')).trans
      ((Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv ci w').trans E.symm)
  have hEs : ∀ s, E.symm (jS s) = Ideal.Quotient.mk T s := fun s =>
    (RingEquiv.symm_apply_eq _).mpr (hE s).symm
  have hfac : (Ideal.Quotient.mk T).comp ψ = e.toRingHom.comp ((ind.stalkMap (sc.base (ci.base w'))).hom.comp
      (eqToHom (congrArg Bl.presheaf.stalk (rfl : ind.base (sc.base (ci.base w')) = _).symm)).hom) := by
    refine RingHom.ext fun a => ?_
    have h1 := hΨ a
    rw [eqToHom_refl, CommRingCat.hom_id, RingHom.id_apply] at h1
    change Ideal.Quotient.mk T (ψ a) = E.symm ((ci.stalkMap w').hom ((sc.stalkMap (ci.base w')).hom
      ((ind.stalkMap (sc.base (ci.base w'))).hom ((eqToHom (congrArg Bl.presheaf.stalk
        (rfl : ind.base (sc.base (ci.base w')) = _).symm)).hom a))))
    rw [eqToHom_refl, CommRingCat.hom_id, RingHom.id_apply, hf_raw a, hEs, h1]
  rw [hfac]
  exact flat_quotMap_equiv_comp e _ J₁ h

end Generic

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)
  (M : AllAmbientMonomialLiftData B b F x t c g d E)
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)
  (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)

/-- The projection law of the explicit source model, on the underlying locally ringed spaces. -/
theorem sourceProjection :
    (sourceCanonicalMap B b F x t c g E.source).hom.left ≫
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).hom.left =
      geometricProjection (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive)
          c.analytic.isClosed ≫ c.chart.hom.left :=
  congrArg (fun φ => φ.hom.left) E.source_maps.projection

set_option linter.defProp false in
/-- **The source readout on the canonical chart** (instance of `readout_generic`, type inferred). -/
def sourceReadout (w : sourceDomain B b F x t c g d E j v)
    (hwS : w ∈ HironakaG10NfSourceSquare.strict B b F x t c g d E j v)
    (hw : w ∈ localDomain c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
      (originalGraph B b F x t c g d E j v) h0 (originalGraph_analytic B b F x t c g d E j v))
    (rr : X.obj.left.presheaf.stalk
      ((OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
          ((sourceChartMap B b F x t c g d E j).base ((chartIso B b F x t c g d E j v hvj).hom.base ⟨w, hwS⟩)))) :=
  HironakaG10NfChartStalk.readout_generic (m := t.embedding.dim+t.rank) E.source.charts t.positive
    (sourceGraphSet B b F x t c) j v hvj
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
    (actualMap_holomorphic B b F x t c g d E M j v hvj).continuous c.analytic h0
    (actual_landing B b F x t c g d E M j v hvj)
    (HironakaG10NfFibreGlue.map_source_le_raw B b F x t c g d E j v hvj)
    (sourceCanonicalMap B b F x t c g E.source).hom.left
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).hom.left c.chart.hom.left
    (sourceProjection B b F x t c g d E) ⟨w, hwS⟩ hw
    (HironakaG10NfSourceSquare.chart_q_point B b F x t c g d E j v hvj w hwS) rr

/-- The source map `β` on the canonical chart (`HironakaG10NfChartStalk.betaG` instance). -/
abbrev betaC (w : sourceDomain B b F x t c g d E j v)
    (hΓ : HironakaG10NfFibreCover.proj B b F x t c g d E j v hvj w ∈ sourceGraphSet B b F x t c) :=
  HironakaG10NfChartStalk.betaG (m := t.embedding.dim+t.rank) E.source.charts (sourceGraphSet B b F x t c) j v hvj
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
    (HironakaG10NfFibreGlue.map_source_le_raw B b F x t c g d E j v hvj) w hΓ

/-- The graph-normal square of the canonical source data, on locally ringed spaces. -/
theorem graphSquare :
    actualSubspaceMap (HironakaG10NfFibreIdentityCanonical.baseMap_prod_contMDiff B b F x t c)
        (fun _ hz => ⟨c.landing hz.1, hz.2⟩ :
          ∀ z ∈ sourceGraphSet B b F x t c, Prod.map c.baseMap id z ∈ targetGraphSet B b t) ≫
      chartGraphMap t.embedding t.domain t.functions t.holomorphic =
      c.chart.hom.left ≫ F.hom.left :=
  congrArg (fun φ => φ.hom.left) c.graph_square

/-- **The fibre identity on native stalks** (G10FI's `fibreIdentityAt_of_W`, read through `c.chart` and the graph
charts): if `β (c.chart^♯ r) ∈ ψ(𝔪)·B` then `r ∈ F^♯(𝔪)·𝒪_X`. -/
theorem fibre_native (w : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (r : X.obj.left.presheaf.stalk (c.chart.hom.left.base ⟨HironakaG10NfFibreCover.proj B b F x t c g d E j v hvj w.1,
      w.2.2.1⟩))
    (hr : betaC B b F x t c g d E j v hvj w.1 w.2.2.1
        ((c.chart.hom.left.stalkMap ⟨HironakaG10NfFibreCover.proj B b F x t c g d E j v hvj w.1, w.2.2.1⟩).hom r) ∈
      Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2)
        (IsLocalRing.maximalIdeal _)) :
    r ∈ Ideal.map (F.hom.left.stalkMap (c.chart.hom.left.base
      ⟨HironakaG10NfFibreCover.proj B b F x t c g d E j v hvj w.1, w.2.2.1⟩)).hom (IsLocalRing.maximalIdeal _) := by
  have : LocallyRingedSpace.IsOpenImmersion c.chart.hom.left := c.chart_open
  exact fibre_native_generic E.source.charts (sourceGraphSet B b F x t c) j v hvj
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
    (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j)
    (HironakaG10NfFibreGlue.map_source_le_raw B b F x t c g d E j v hvj)
    (HironakaG10NfFibreIdentityCanonical.baseMap_prod_contMDiff B b F x t c)
    (fun _ hz => ⟨c.landing hz.1, hz.2⟩ :
      ∀ z ∈ sourceGraphSet B b F x t c, Prod.map c.baseMap id z ∈ targetGraphSet B b t) c.chart.hom.left
    (chartGraphMap t.embedding t.domain t.functions t.holomorphic) F.hom.left
    (graphSquare B b F x t c) w.1 w.2.2.1 w.2.2.2
    ((targetChartMap B b F x t c g d E j).stalkMap ⟨actualMap B b F x t c g d E j v hvj w.1, w.2.2.2⟩).hom
    (HironakaG10NfFibreIdentityCanonical.fibreIdentityAt_of_W B b F x t c g d E M j v hvj h0 w) r hr

/-- **The exceptional torsion at a point of the fibre-product locus is proper** when it lies in `ψ(𝔪)·B`. -/
theorem pivotTorsion_ne_top (w : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (hT : pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1 ≤
      Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2)
        (IsLocalRing.maximalIdeal _)) :
    pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1 ≠ ⊤ := by
  intro htop
  have h1 := fibre_native B b F x t c g d E M j v hvj h0 w 1 ((htop.symm.le.trans hT) Submodule.mem_top)
  have h2 : Ideal.map (F.hom.left.stalkMap (c.chart.hom.left.base
      ⟨HironakaG10NfFibreCover.proj B b F x t c g d E j v hvj w.1, w.2.2.1⟩)).hom (IsLocalRing.maximalIdeal _) ≤
      IsLocalRing.maximalIdeal _ :=
    IsLocalRing.map_maximalIdeal_le _
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr (h2 h1))

end

end Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical
