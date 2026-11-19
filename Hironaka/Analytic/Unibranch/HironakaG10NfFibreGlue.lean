import Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentityCanonical

/-!
# H3 (3), glue: the source map is defined on the graph stalk, and the fibre conjunct from the readouts

Lane G10FI, run 0081 (H3 item (3), for G10H3's `strict` field).

* `map_source_le_raw` — the pull-back of the vanishing ideal of the source graph `Γ_X` by the source blow-down `proj`
  lies in the raw (total) ideal of the real-open chart, hence in `jointIdeal w`: the source map
  `β = mk ∘ proj^♯ : 𝒪_{Γ_X, proj w} = 𝒪^{amb}/I(Γ_X) → JointQuotient w` is well defined;
* `comap_fibre_le` — pure algebra: if the strict stalk `𝒪_{Y',y''} ≅ B/T` intertwines `q^♯` with `β` and `f'^♯`
  with `ψ`, the torsion `T` lies in `ψ(𝔪_{X'})B`, and `comap β (ψ(𝔪_{X'})B) ⊆ F^♯(𝔪_Y)` (the fibre identity), then
  `comap q^♯ (f'^♯(𝔪_{X'})) ⊆ F^♯(𝔪_Y)` — the fibre conjunct of `HironakaG10NfFibreModel.FibreModel.strict`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreGlue

noncomputable section

/-- **The fibre conjunct from the readouts** (pure algebra). -/
theorem comap_fibre_le {OX OY' OX' OY B : Type*} [CommRing OX] [CommRing OY'] [CommRing OX'] [CommRing OY]
    [CommRing B] (q : OX →+* OY') (f' : OX' →+* OY') (Fs : OY →+* OX) (ψ : OX' →+* B) (β : OX →+* B)
    (T : Ideal B) (e : OY' ≃+* B ⧸ T)
    (hq : ∀ r, e (q r) = Ideal.Quotient.mk T (β r)) (hf' : ∀ a, e (f' a) = Ideal.Quotient.mk T (ψ a))
    (mX' : Ideal OX') (mY : Ideal OY) (hT : T ≤ Ideal.map ψ mX')
    (hFI : Ideal.comap β (Ideal.map ψ mX') ≤ Ideal.map Fs mY) :
    Ideal.comap q (Ideal.map f' mX') ≤ Ideal.map Fs mY := by
  intro r hr
  apply hFI
  have h1 : e (q r) ∈ Ideal.map (e.toRingHom.comp f') mX' := by
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hr
  have h2 : Ideal.map (e.toRingHom.comp f') mX' = Ideal.map (Ideal.Quotient.mk T) (Ideal.map ψ mX') := by
    rw [Ideal.map_map]
    congr 1
    ext a
    exact hf' a
  rw [h2, hq] at h1
  have h3 := Ideal.mem_comap.mpr h1
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hT] at h3
  exact h3


open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaSmoothCentreRealDomainActualSheafStalk BlowupConstruction BlowupMonomialCharts
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel HironakaG10JointStrictTorsion
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
  Hironaka.Analytic.Unibranch.HironakaG10NfFibreGerm Hironaka.Analytic.Unibranch.HironakaG10NfFibreCover
  Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentity Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentityCanonical

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
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

/-- The inverse of the recentred product-chart coordinates. -/
def kappaInv (z : targetOpen B b F x t c g d E j v) : c.subdomain × ComplexModel t.rank :=
  (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).symm (z.val + (monomial c.embedding.dim (j.natAdd c.embedding.dim) v))

theorem kappaInv_kappa (q : c.subdomain × ComplexModel t.rank) :
    kappaInv B b F x t c g d E j v (kappa B b F x t c g d E j v q) = q := by
  change (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).symm ((chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) q - (monomial c.embedding.dim (j.natAdd c.embedding.dim) v) + (monomial c.embedding.dim (j.natAdd c.embedding.dim) v)) = q
  rw [sub_add_cancel]
  exact (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).left_inv (dom_mem B b F x t c g d E j q).1

theorem kappaInv_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) ∞
      (kappaInv B b F x t c g d E j v) := by
  have hg : ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) ∞
      (fun z : targetOpen B b F x t c g d E j v => z.val + (monomial c.embedding.dim (j.natAdd c.embedding.dim) v)) :=
    contMDiff_subtype_val.add contMDiff_const
  exact (contMDiffOn_chart_symm (x := ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank))).comp_contMDiff
    hg (fun z => z.property)

theorem proj_eq_kappaInv (s : sourceDomain B b F x t c g d E j v) :
    proj B b F x t c g d E j v hvj s =
      kappaInv B b F x t c g d E j v
        (realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) s) := by
  rw [← kappa_proj B b F x t c g d E j v hvj s, kappaInv_kappa]

theorem kappaInv_mem (z : targetOpen B b F x t c g d E j v) (hz : z ∈ originalGraph B b F x t c g d E j v) :
    kappaInv B b F x t c g d E j v z ∈ sourceGraphSet B b F x t c :=
  hz

/-- **The source map is defined on the graph stalk**: `proj^♯ I(Γ_X) ⊆ raw ⊆ jointIdeal`. -/
theorem map_source_le_raw (s : sourceDomain B b F x t c g d E j v) :
    Ideal.map (sm (proj_contMDiff B b F x t c g d E j v hvj) s)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := c.embedding.dim+t.rank) (sourceGraphSet B b F x t c))
          (proj B b F x t c g d E j v hvj s)) ≤
      rawAnalyticIdeal c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
        (originalGraph B b F x t c g d E j v) s := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨k, hk, hmem, rfl⟩
  apply Ideal.mem_comap.mpr
  have hkp : HolomorphicAt (c.embedding.dim+t.rank) (k ∘ proj B b F x t c g d E j v hvj) s :=
    hk.comp_contMDiff (Eventually.of_forall fun _ => (proj_contMDiff B b F x t c g d E j v hvj).contMDiffAt)
  have hkI : HolomorphicAt (c.embedding.dim+t.rank) (k ∘ kappaInv B b F x t c g d E j v)
      (realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) s) := by
    have hk' : HolomorphicAt (c.embedding.dim+t.rank) k (kappaInv B b F x t c g d E j v
        (realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) s)) := by
      rw [← proj_eq_kappaInv]
      exact hk
    exact hk'.comp_contMDiff (Eventually.of_forall fun _ => (kappaInv_contMDiff B b F x t c g d E j v).contMDiffAt)
  have hvan : ∀ᶠ z in 𝓝 (realOpenProjection c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) s), z ∈ originalGraph B b F x t c g d E j v →
        (k ∘ kappaInv B b F x t c g d E j v) z = 0 := by
    have hT : Tendsto (kappaInv B b F x t c g d E j v)
        (𝓝 (realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) s))
        (𝓝 (proj B b F x t c g d E j v hvj s)) := by
      rw [proj_eq_kappaInv B b F x t c g d E j v hvj s]
      exact (kappaInv_contMDiff B b F x t c g d E j v).continuous.tendsto _
    filter_upwards [hT.eventually hmem.2] with z hz hzW
    exact hz (kappaInv_mem B b F x t c g d E j v z hzW)
  have hspan : IsInSpanAt (n := c.embedding.dim+t.rank)
      (fun f => ∃ a, (vanishingIdeal (n := c.embedding.dim+t.rank) (originalGraph B b F x t c g d E j v)).mem
        (realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) s) a ∧
          f = a ∘ realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v))
      s (k ∘ proj B b F x t c g d E j v hvj) :=
    ⟨hkp, 1, fun _ => (k ∘ kappaInv B b F x t c g d E j v) ∘
        realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v),
      fun _ _ => 1, fun _ => ⟨_, ⟨hkI, hvan⟩, rfl⟩, fun _ => holomorphicAt_const 1,
      Eventually.of_forall fun s' => by
        simp only [Function.comp_apply, Finset.univ_unique, Finset.sum_singleton, one_mul]
        rw [proj_eq_kappaInv B b F x t c g d E j v hvj s']⟩
  exact (congrArg (· ∈ rawAnalyticIdeal c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
      (originalGraph B b F x t c g d E j v) s)
    (sm_germ (proj_contMDiff B b F x t c g d E j v hvj) s k hk hkp)).mpr (germ_mem_whole _ s hkp hspan)

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreGlue
