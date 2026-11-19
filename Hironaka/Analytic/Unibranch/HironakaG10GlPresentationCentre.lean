import Hironaka.Analytic.Unibranch.HironakaG10GlPresentationPivot
import Hironaka.Analytic.Unibranch.HironakaG10GlPresentationTransport
import Hironaka.Analytic.HolomorphicGermNoetherian

/-!
# Pulled torsion presentations at the canonical chart points over the centre

Lane G10HP, run 0081 (continuing lane G10GL, item GL-3b, the `hpres` assembly).  Setting of
`HironakaG10SbCanonicalStrictTorsion` (`F : X ⟶ Y`, `b : B ⟶ 𝒪_Y`, the geometric blowup `Bl_B Y`, the strict transform
`Bl_{F*B} X`, the induced map `inducedMorphism`).  At a canonical chart point `w` (local saturation domain, strict
transform), with the native chart point `nativePoint … w` and the target chart point `targetPoint … w`:

* `canonicalPresentation` — a generic pulled torsion presentation
  (`HironakaG10GlPresentationTransport.GenPresentation`) of the strict transform over `Bl_B Y`:
  the joint quotient `JointQuotient … w` (the local ring of the fibre product, noetherian), the canonical base map
  `canonicalPsi` (G10GL N2(b–c)), the canonical centre generator with `ψ g = pivotClass` (N2(d),
  `HironakaG10GlPresentationPivot`), `β` from `nativeStrictStalkTorsionEquiv` (G10SB), `comm` from
  `canonical_square_joint` (G10GL), and the flattener field from an explicit hypothesis `hfl` in the exact form of
  G10N34's `isFlattenerIdeal_canonical` (Hironaka 1975, Th. 2.5);
* `exists_genPresentation` — every point of the strict transform over the centre carries such a presentation (N1
  coverage `HironakaG10GlCanonicalCoverage.exists_nativePoint_eq`, the canonical data of
  `exists_same_canonical_allambient_monomial_lift`).

No named input: the flattener field is an explicit binder.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlPresentationCentre

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaG10HirFlatQuotient
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap HironakaG10JointNativeScalar
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
  Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalCoverage
  Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare
  Hironaka.Analytic.Unibranch.HironakaG10GlPresentationPivot
  Hironaka.Analytic.Unibranch.HironakaG10GlPresentationTransport
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform

/-! ### Generic lemmas -/

/-- Ambient germ rings of complex manifolds are noetherian. -/
theorem ambientStalk_noetherian {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (y : M) : IsNoetherianRing (actualComplexStructureStalk (n := n) y) := by
  have := isNoetherianRing_holGerm_euclidean n
  exact isNoetherianRing_of_ringEquiv _ (actualStalkChartEquiv (n := n) y).symm

/-- The `a`-power torsion of a ring is the saturation of `⊥` by `a`. -/
theorem powerSat_bot_eq_torsion' {Q : Type*} [CommRing Q] (a : Q) :
    powerSat (⊥ : Ideal Q) a = Submodule.torsion' Q Q (Submonoid.powers a) := by
  ext s
  rw [mem_powerSat, Submodule.mem_torsion'_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨⟨a ^ m, m, rfl⟩, (Submodule.mem_bot Q).mp hm⟩
  · rintro ⟨⟨u, m, rfl⟩, hu⟩
    exact ⟨m, (Submodule.mem_bot Q).mpr hu⟩

/-- Unwinding a composite of three ring isomorphisms (pointwise). -/
theorem trans_trans_symm_apply_eq {R S T U : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [NonAssocSemiring T] [NonAssocSemiring U] (e₁ : R ≃+* S) (e₂ : S ≃+* T) (e₃ : U ≃+* T) (r : R) (u : U)
    (h : e₂ (e₁ r) = e₃ u) : (e₁.trans (e₂.trans e₃.symm)) r = u := by
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h, RingEquiv.symm_apply_apply]

/-- A pointed flattener over `x₀ = f y` is a pointed flattener over `f y` (transport of the base point). -/
theorem isPointFlattenerAt_rfl {X₀ Y₀ : SourceReducedComplexSpace} (f : Y₀ ⟶ X₀) {x₀ : X₀.obj.left}
    (y₀ : Y₀.obj.left) (h : f.hom.left.base y₀ = x₀) (P : Ideal (X₀.obj.left.presheaf.stalk x₀))
    (hP : IsPointFlattenerAt f x₀ y₀ h P) :
    IsPointFlattenerAt f (f.hom.left.base y₀) y₀ rfl
      (Ideal.map (eqToHom (congrArg X₀.obj.left.presheaf.stalk h.symm)).hom P) := by
  subst h
  simpa [eqToHom_refl] using hP

theorem map_comp_eqToHom_map {X₀ : SourceReducedComplexSpace} {R : Type*} [CommRing R] {a b : X₀.obj.left}
    (h : a = b) (φ : X₀.obj.left.presheaf.stalk b →+* R) (P : Ideal (X₀.obj.left.presheaf.stalk b)) :
    Ideal.map (φ.comp (eqToHom (congrArg X₀.obj.left.presheaf.stalk h)).hom)
        (Ideal.map (eqToHom (congrArg X₀.obj.left.presheaf.stalk h.symm)).hom P) = Ideal.map φ P := by
  subst h
  simp [eqToHom_refl]

/-- The flattener field of a generic presentation from its form at the base point `f y₀` (G10N34's form). -/
theorem flattener_of_rfl {X₀ Y₀ G : SourceReducedComplexSpace} (f : Y₀ ⟶ X₀) (π : G ⟶ X₀) (z : G.obj.left)
    (y₀ : Y₀.obj.left) {B₀ : Type*} [CommRing B₀] (ψ : G.obj.left.presheaf.stalk z →+* B₀)
    (H : ∀ (hbase : f.hom.left.base y₀ = π.hom.left.base z)
      (P : Ideal (X₀.obj.left.presheaf.stalk (f.hom.left.base y₀))),
      IsPointFlattenerAt f (f.hom.left.base y₀) y₀ rfl P →
        IsFlattenerIdeal ψ (Ideal.map ((π.hom.left.stalkMap z).hom.comp
          (eqToHom (congrArg X₀.obj.left.presheaf.stalk hbase)).hom) P))
    (h : f.hom.left.base y₀ = π.hom.left.base z) (P : Ideal (X₀.obj.left.presheaf.stalk (π.hom.left.base z)))
    (hP : IsPointFlattenerAt f _ y₀ h P) :
    IsFlattenerIdeal ψ (Ideal.map (π.hom.left.stalkMap z).hom P) := by
  have H' := H h _ (isPointFlattenerAt_rfl f y₀ h P hP)
  rw [map_comp_eqToHom_map h] at H'
  exact H'

/-! ### A builder from a chart square -/

/-- **A generic presentation from a chart square at a chart point** `i₂ (i₁ s)` (two open immersions into the
source), given the readout `e₃` of the stalk at `s` as a torsion quotient (`e₃ (mk q) = J q`) and the stalk square
`hsq`; the base map `τ ∘ κ`, its generator and its flattener field live at a second base point `z'` equal to
`p (i₂ (i₁ s))`.  (Stated so that the canonical square `canonical_square_joint` is literally `hsq`.) -/
def GenPresentation.ofChart {X₀ Y₀ G S : SourceReducedComplexSpace} (σ : G ⟶ X₀) (p : S ⟶ G) (q : S ⟶ Y₀)
    (f : Y₀ ⟶ X₀) (D : ∀ x : X₀.obj.left, Ideal (X₀.obj.left.presheaf.stalk x))
    {T A : LocallyRingedSpace.{0}} (i₁ : T ⟶ A) [LocallyRingedSpace.IsOpenImmersion i₁]
    (i₂ : A ⟶ S.obj.left) [LocallyRingedSpace.IsOpenImmersion i₂] (s : T)
    {Q : Type} [CommRing Q] [IsNoetherianRing Q] (K : Ideal Q) (e₃ : Q ⧸ K ≃+* T.presheaf.stalk s)
    (J : Q →+* T.presheaf.stalk s) (hJ : ∀ u, e₃ (Ideal.Quotient.mk K u) = J u)
    (z' : G.obj.left) (hzz : p.hom.left.base (i₂.base (i₁.base s)) = z')
    {R₂ : Type} [CommRing R₂] (κ : G.obj.left.presheaf.stalk z' →+* R₂) (τ : R₂ →+* Q)
    (g' : G.obj.left.presheaf.stalk z')
    (hK : powerSat (⊥ : Ideal Q) ((τ.comp κ) g') = K)
    (hspan : Ideal.map (σ.hom.left.stalkMap z').hom (D (σ.hom.left.base z')) = Ideal.span {g'})
    (hsq : ∀ a, (i₁.stalkMap s).hom ((i₂.stalkMap (i₁.base s)).hom
        ((p.hom.left.stalkMap (i₂.base (i₁.base s))).hom a)) =
      J (τ (κ ((eqToHom (congrArg G.obj.left.presheaf.stalk hzz)).hom a))))
    (hfl : ∀ (hbase : f.hom.left.base (q.hom.left.base (i₂.base (i₁.base s))) = σ.hom.left.base z')
      (P : Ideal (X₀.obj.left.presheaf.stalk (f.hom.left.base (q.hom.left.base (i₂.base (i₁.base s)))))),
      IsPointFlattenerAt f _ (q.hom.left.base (i₂.base (i₁.base s))) rfl P →
        IsFlattenerIdeal (τ.comp κ) (Ideal.map ((σ.hom.left.stalkMap z').hom.comp
          (eqToHom (congrArg X₀.obj.left.presheaf.stalk hbase)).hom) P))
    (hnonunit : ∀ b : Q, ¬ IsUnit b → b ∈ (⊥ : Ideal Q).jacobson) :
    GenPresentation σ p q f D (i₂.base (i₁.base s)) (p.hom.left.base (i₂.base (i₁.base s))) rfl := by
  subst hzz
  exact
    { B := Q
      ψ := τ.comp κ
      g := g'
      span_g := hspan
      β := (Ideal.quotEquivOfEq hK).trans ((openImmersionStalkEquiv i₂ (i₁.base s)).trans
        ((openImmersionStalkEquiv i₁ s).trans e₃.symm)).symm
      comm := fun a => by
        rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.symm_apply_eq]
        symm
        apply trans_trans_symm_apply_eq
        rw [openImmersionStalkEquiv_apply, openImmersionStalkEquiv_apply, hJ]
        simpa using hsq a
      flattener := flattener_of_rfl f σ _ _ (τ.comp κ) hfl
      nonunit := hnonunit }

/-- **A generic presentation from the ingredients of a chart square**: the square of locally ringed spaces
`i₁ ≫ i₂ ≫ p = m ≫ tc` at a point `s`, the torsion readout `e₃` of the stalk at `s`, and the strict square
`J ∘ τ = m^♯` (every hypothesis is an instance of a generic lemma, so that no large unification is needed). -/
def GenPresentation.ofSquare {X₀ Y₀ G S : SourceReducedComplexSpace} (σ : G ⟶ X₀) (p : S ⟶ G) (q : S ⟶ Y₀)
    (f : Y₀ ⟶ X₀) (D : ∀ x : X₀.obj.left, Ideal (X₀.obj.left.presheaf.stalk x))
    {T A Dsp : LocallyRingedSpace.{0}} (i₁ : T ⟶ A) [LocallyRingedSpace.IsOpenImmersion i₁]
    (i₂ : A ⟶ S.obj.left) [LocallyRingedSpace.IsOpenImmersion i₂] (m : T ⟶ Dsp) (tc : Dsp ⟶ G.obj.left)
    (H : i₁ ≫ (i₂ ≫ p.hom.left) = m ≫ tc) (s : T)
    (hs : tc.base (m.base s) = p.hom.left.base (i₂.base (i₁.base s)))
    {Q : Type} [CommRing Q] [IsNoetherianRing Q] (K : Ideal Q) (e₃ : Q ⧸ K ≃+* T.presheaf.stalk s)
    (J : Q →+* T.presheaf.stalk s) (hJ : ∀ u, e₃ (Ideal.Quotient.mk K u) = J u)
    (τ : Dsp.presheaf.stalk (m.base s) →+* Q) (hstrict : ∀ r, J (τ r) = (m.stalkMap s).hom r)
    (g' : G.obj.left.presheaf.stalk (tc.base (m.base s)))
    (hK : powerSat (⊥ : Ideal Q) ((τ.comp (tc.stalkMap (m.base s)).hom) g') = K)
    (hspan : Ideal.map (σ.hom.left.stalkMap (tc.base (m.base s))).hom
      (D (σ.hom.left.base (tc.base (m.base s)))) = Ideal.span {g'})
    (hfl : ∀ (hbase : f.hom.left.base (q.hom.left.base (i₂.base (i₁.base s))) =
        σ.hom.left.base (tc.base (m.base s)))
      (P : Ideal (X₀.obj.left.presheaf.stalk (f.hom.left.base (q.hom.left.base (i₂.base (i₁.base s)))))),
      IsPointFlattenerAt f _ (q.hom.left.base (i₂.base (i₁.base s))) rfl P →
        IsFlattenerIdeal (τ.comp (tc.stalkMap (m.base s)).hom) (Ideal.map
          ((σ.hom.left.stalkMap (tc.base (m.base s))).hom.comp
            (eqToHom (congrArg X₀.obj.left.presheaf.stalk hbase)).hom) P))
    (hnonunit : ∀ b : Q, ¬ IsUnit b → b ∈ (⊥ : Ideal Q).jacobson) :
    GenPresentation σ p q f D (i₂.base (i₁.base s)) (p.hom.left.base (i₂.base (i₁.base s))) rfl :=
  GenPresentation.ofChart σ p q f D i₁ i₂ s K e₃ J hJ (tc.base (m.base s)) hs.symm
    (tc.stalkMap (m.base s)).hom τ g' hK hspan
    (fun a => (HironakaG10GlCanonicalBaseSquare.square_apply i₁ i₂ p.hom.left m tc H s hs a).trans
      (hstrict _).symm)
    hfl hnonunit

/-! ### The canonical presentation -/

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
  (w : sourceDomain B b F x t c g d E j v)
  (hw : w ∈ localDomain c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) h0
      (originalGraph_analytic B b F x t c g d E j v))
  (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))

/-- The canonical base map at a chart point on the strict transform, in the form of `canonical_square_joint`
(target stalk map at the actual subspace point). -/
theorem canonicalPsi_generator_square :
    ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
      (actual_landing B b F x t c g d E M j v hvj hwS)).comp ((targetChartMap B b F x t c g d E j).stalkMap
        ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
          (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
            (strictPt B b F x t c g d E j v w hwS))).hom)
      (canonicalGenerator B b F x t c g d E j v hvj w (actual_landing B b F x t c g d E M j v hvj hwS)) =
    pivotClass (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w :=
  canonicalPsi_generator B b F x t c g d E M j v hvj w (actual_landing B b F x t c g d E M j v hvj hwS)

/-- The exceptional torsion of the joint quotient is the power torsion of the image of the canonical generator. -/
theorem canonical_hK :
    powerSat (⊥ : Ideal _)
      (((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
      (actual_landing B b F x t c g d E M j v hvj hwS)).comp ((targetChartMap B b F x t c g d E j).stalkMap
        ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
          (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
            (strictPt B b F x t c g d E j v w hwS))).hom)
      (canonicalGenerator B b F x t c g d E j v hvj w (actual_landing B b F x t c g d E M j v hvj hwS))) =
    pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w :=
  (congrArg (powerSat (⊥ : Ideal _)) (canonicalPsi_generator_square B b F x t c g d E M j v hvj w hwS)).trans
    (powerSat_bot_eq_torsion' _)

/-- The canonical generator generates the pulled centre, at the target chart point written as in the square. -/
theorem canonical_hspan :
    Ideal.map ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
        ((targetChartMap B b F x t c g d E j).base ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
          (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
            (strictPt B b F x t c g d E j v w hwS)))).hom
      ((fun z => (LinearMap.range (stalkInclusionLinearMap Y.obj.left.toSheafedSpace.sheaf B b z) : Ideal _))
        ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
          ((targetChartMap B b F x t c g d E j).base ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
          (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
            (strictPt B b F x t c g d E j v w hwS))))) =
      Ideal.span {canonicalGenerator B b F x t c g d E j v hvj w (actual_landing B b F x t c g d E M j v hvj hwS)} :=
  span_canonicalGenerator B b F x t c g d E j v hvj w (actual_landing B b F x t c g d E M j v hvj hwS)

include M hw in
/-- **The pulled torsion presentation at a canonical chart point** over the geometric blowup `Bl_B Y`, given the
flattener field at this chart point (G10N34's `isFlattenerIdeal_canonical`, in the form of the builder). -/
def canonicalPresentation
    (hfl : ∀ (hbase : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (chartPoint B b F x t c g d E j v hvj w hwS)) =
          (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
            ((targetChartMap B b F x t c g d E j).base
              ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
              (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
                (strictPt B b F x t c g d E j v w hwS))))
        (P : Ideal (Y.obj.left.presheaf.stalk (F.hom.left.base
          ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
            (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
              (chartPoint B b F x t c g d E j v hvj w hwS))))),
        IsPointFlattenerAt F _ ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
            (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
              (chartPoint B b F x t c g d E j v hvj w hwS)) rfl P →
        IsFlattenerIdeal ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
      (actual_landing B b F x t c g d E M j v hvj hwS)).comp ((targetChartMap B b F x t c g d E j).stalkMap
          ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
          (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
            (strictPt B b F x t c g d E j v w hwS))).hom)
          (Ideal.map (((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
            ((targetChartMap B b F x t c g d E j).base
              ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
              (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
                (strictPt B b F x t c g d E j v w hwS)))).hom.comp
              (eqToHom (congrArg Y.obj.left.presheaf.stalk hbase)).hom) P)) :
    GenPresentation (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b)
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F)
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)) F
      (fun z => (LinearMap.range (stalkInclusionLinearMap Y.obj.left.toSheafedSpace.sheaf B b z) : Ideal _))
      (chartPoint B b F x t c g d E j v hvj w hwS)
      ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
        (chartPoint B b F x t c g d E j v hvj w hwS)) rfl :=
  haveI := ambientStalk_noetherian (n := c.embedding.dim+t.rank) w
  GenPresentation.ofSquare (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b)
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F)
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)) F
    (fun z => (LinearMap.range (stalkInclusionLinearMap Y.obj.left.toSheafedSpace.sheaf B b z) : Ideal _))
    (chartIso B b F x t c g d E j v hvj).hom (sourceChartMap B b F x t c g d E j)
    (actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
      (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx))
    (targetChartMap B b F x t c g d E j) (chart_square B b F x t c g d E M j v hvj)
    (strictPt B b F x t c g d E j v w hwS)
    (targetChartMap_targetPoint B b F x t c g d E M j v hvj w hwS)
    (pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w)
    (jointTorsionQuotientEquiv (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) h0
      (originalGraph_analytic B b F x t c g d E j v)
      (actualMap_holomorphic B b F x t c g d E M j v hvj).continuous
      (actual_landing B b F x t c g d E M j v hvj) w hw hwS)
    (jointStrictStalkMap (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) h0
      (originalGraph_analytic B b F x t c g d E j v)
      (actualMap_holomorphic B b F x t c g d E M j v hvj).continuous
      (actual_landing B b F x t c g d E M j v hvj) w hw hwS)
    (jointTorsionQuotientEquiv_mk (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) h0
      (originalGraph_analytic B b F x t c g d E j v)
      (actualMap_holomorphic B b F x t c g d E M j v hvj).continuous
      (actual_landing B b F x t c g d E M j v hvj) w hw hwS)
    (targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
      (actual_landing B b F x t c g d E M j v hvj hwS))
    (targetStalkToJoint_strict_square (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) h0
      (originalGraph_analytic B b F x t c g d E j v) (actual_landing B b F x t c g d E M j v hvj) w hw hwS)
    (canonicalGenerator B b F x t c g d E j v hvj w (actual_landing B b F x t c g d E M j v hvj hwS))
    (canonical_hK B b F x t c g d E M j v hvj w hwS)
    (canonical_hspan B b F x t c g d E M j v hvj w hwS)
    hfl
    (quotient_nonunit_mem_jacobson _)

/-! ### Coverage: every strict point over the centre -/

section Coverage

/-- Over the centre, the pulled centre of the strict transform is a proper ideal. -/
theorem pulled_ne_top
    (y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    (hc : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'') ∈
        nonunitLocus B b) :
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) y'' ≠ ⊤ := by
  intro htop
  have h1 := (OriginalFiniteIdealGraphDensity.nativePulledIdealStalkIdeal_eq_top_iff
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).hom.left _ _ y'').mp htop
  exact (mem_pulledUnitLocus_iff B b F _).mp (fun h => h h1) hc

/-- **Every point of the strict transform over the centre carries a generic pulled torsion presentation** over the
geometric blowup, given the flattener field at all canonical chart points (G10N34's `isFlattenerIdeal_canonical`). -/
theorem exists_genPresentation
    (hfl : ∀ (x : X.obj.left) {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
      (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d) (M : AllAmbientMonomialLiftData B b F x t c g d E)
      (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank)) (hvj : v (j.natAdd c.embedding.dim) = 0)
      (w : sourceDomain B b F x t c g d E j v)
      (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))
      (hbase : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) =
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
          ((targetChartMap B b F x t c g d E j).base
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩))
      (P : Ideal (Y.obj.left.presheaf.stalk (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))))
      (_hP : IsPointFlattenerAt F (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))
        ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) rfl P),
      IsFlattenerIdeal
        ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
            (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
            (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
            (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
            (actual_landing B b F x t c g d E M j v hvj hwS)).comp
          ((targetChartMap B b F x t c g d E j).stalkMap
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩).hom)
        (Ideal.map (((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
            ((targetChartMap B b F x t c g d E j).base
              ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩)).hom.comp
          (eqToHom (congrArg Y.obj.left.presheaf.stalk hbase)).hom) P))
    (y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    (hc : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'') ∈
        nonunitLocus B b) :
    ∃ (z : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
      (hz : (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base y'' = z),
      Nonempty (GenPresentation (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b)
        (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F)
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)) F
        (fun z => (LinearMap.range (stalkInclusionLinearMap Y.obj.left.toSheafedSpace.sheaf B b z) : Ideal _))
        y'' z hz) := by
  have hcent := pulled_ne_top B b F y'' hc
  have hsq : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'') =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
        ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base y'') :=
    (congrArg (fun k => k.hom.left.base y'') (OriginalFiniteIdealBlowupSquare.inducedMorphism_square B b F)).symm
  refine (⟨_, rfl⟩ : ∃ x₀, (OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'' = x₀).elim
    fun x₀ hx => ?_
  refine (⟨_, rfl⟩ : ∃ y₀, (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base y'' = y₀).elim
    fun y₀ hy => ?_
  have hxy : F.hom.left.base x₀ = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y₀ := by
    rw [← hx, ← hy]
    exact hsq
  refine (exists_same_canonical_allambient_monomial_lift B b F x₀ y₀ hxy).elim fun t ht => ?_
  refine ht.elim fun c hc' => hc'.elim fun g hg => hg.elim fun d hd => hd.elim fun E hE => hE.elim fun M => ?_
  refine (exists_nativePoint_eq B b F x₀ t c g d E y'' hx hcent).elim fun j hj => ?_
  refine hj.elim fun v hv => hv.elim fun hvj h1 => h1.elim fun h0 h2 => h2.elim fun w h3 => h3.elim
    fun hwS h4 => ?_
  have hw := h4.1
  have hnp := h4.2
  subst hnp
  exact ⟨_, rfl, ⟨canonicalPresentation B b F x₀ t c g d E M j v hvj h0 w hw hwS
    (fun hbase P hP => hfl x₀ t c g d E M j v hvj w hwS hbase P hP)⟩⟩

end Coverage

end

end Hironaka.Analytic.Unibranch.HironakaG10GlPresentationCentre
