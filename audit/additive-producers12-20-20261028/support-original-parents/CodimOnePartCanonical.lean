import TranscendentalNakamaye.Pending.CodimOneSupportAlong
import TranscendentalNakamaye.Pending.MarkedIdealTowerTransport
import TranscendentalNakamaye.Pending.MarkedIdealRestrictOpen
import TranscendentalNakamaye.Pending.MarkedIdealEquivalence
import TranscendentalNakamaye.Pending.HomogenizedGlueingTower
import TranscendentalNakamaye.Pending.BoundaryCount
import TranscendentalNakamaye.Pending.AnalyticSubsetOpens

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Canonicity of the codimension-one part along `N` and of the boundary count

Hironaka phase H2 (TN3), for TN-CLASSICAL's Step 1 inside `N` (`hir:maximal-order-step`, "Properties":
"(4)--(7) hold since every ingredient (`𝓗`, `𝓒`, `s`, tangent directions, restriction to `S` and to
`V(w)`) commutes with restriction to open sets and with biholomorphisms, and is unchanged by empty
steps"; claim I-0977 C-0097).  Blueprint `bcalc:regular-point-transport`,
`bcalc:codim-one-part-canonical`, `bcalc:codim-one-part-off-centre`, `bcalc:boundary-count-canonical`
(chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`) §2.4 (the
invariants are functorial for étale maps, here open embeddings and biholomorphisms) and Proposition
`pr:resol` (3)(b) (off the centre the invariants do not change); Bierstone--Milman 2008, the
paragraph after Theorem 1.3 (restriction to open sets, trivial blowings-up).

The two ingredients of Step 1 inside `N` that the blowup calculus provides are the codimension-one
part `Z₁ = codimOnePartAlong N 𝔞 μ` of `cosupp(𝔞|_N, μ)` (value `(0, ∞)` in Step 1ba; TN3's
`CodimOneSupportAlong`) and the boundary count `s(x)` of the original members through `x`
(`BoundaryCount.boundaryCount` of the first `#E` members of the transformed divisor).

## Regular points

* `regularAtDim_preimage_iff`: for a biholomorphism `Φ : M' ≅ M`, `x` is a regular point of
  `Φ⁻¹ A` of dimension `k` iff `Φ x` is one of `A`;
* `regularAtDim_preimage_iff_of_section`: the same for a holomorphic `π : Y → X` at a point `z` over
  an open `W` on which `π` has a holomorphic section `s` with `s (π z) = z` (a blowup off its centre).

## The codimension-one part

* `mem_codimOnePartAlong_iff_of_eventually`, `mem_codimOnePartAlong_congr`, `codimOnePartAlong_congr`:
  membership at `x` depends only on the germs at `x` of `N` and of the cosupport;
* `codimOnePartAlong_pullback`: `Z₁(Φ⁻¹N, Φ^*𝔞, μ) = Φ⁻¹ Z₁(N, 𝔞, μ)` (biholomorphisms);
* `codimOnePartAlong_pullback_val`: `Z₁(N ∩ U, 𝔞|_U, μ) = Z₁(N, 𝔞, μ) ∩ U` (open sets);
* `mem_codimOnePartAlong_geoTransform_iff`: off the centre of a blowup `π`, `z ∈ Z₁` of the transform
  iff `π z ∈ Z₁`; `codimOnePartAlong_geoTransform_empty`: a blowup along `∅` pulls `Z₁` back;
* along towers: `codimOnePartAlong_geoTransformAlong_transport` (property (6): along the transported
  tower `Z₁` is the preimage under the last-stage biholomorphism),
  `codimOnePartAlong_geoTransformAlong_restrict` (property (5): along the restriction of a multiple
  test blow-up `Z₁` is the trace on the open preimage), `mem_codimOnePartAlong_geoTransformAlong_step_iff`
  (property (3) "equal otherwise", and (4)), `codimOnePartAlong_geoTransformAlong_of_restrictEquiv`,
  `codimOnePartAlong_geoTransformAlong_of_wEquiv` (property (7): restricted-equivalent marked ideals,
  and equivalent marked ideals with the same `N`, have the same `Z₁` at every stage).

## The boundary count

* `boundaryCount_map_preimage`: `s(E.map (f⁻¹ ·))(z) = s(E)(f z)`;
* `boundaryCount_map_geoStrictTransform_of_notMem`, `boundaryCount_take_E_geoTransformAlong_step_of_notMem`:
  off the centre of a blowup the count of the original members does not change;
* `boundaryCount_take_E_geoTransformAlong_transport`, `boundaryCount_take_E_geoTransformAlong_restrict`:
  it corresponds along transported and restricted towers.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.CodimOnePartCanonical

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.MarkedIdeals TranscendentalNakamaye.Pending.MarkedIdeals.MarkedIdeal
  TranscendentalNakamaye.Pending.BlowupTowers TranscendentalNakamaye.Pending.BlowupTowerTransforms
  TranscendentalNakamaye.Pending.HomogenizedGlueingTower TranscendentalNakamaye.Pending.MarkedIdealRestrictOpen
  TranscendentalNakamaye.Pending.CodimOneSupportAlong TranscendentalNakamaye.Pending.MarkedIdealBiholomorphism
  TranscendentalNakamaye.Pending.MarkedIdealTowerTransport TranscendentalNakamaye.Pending.BoundaryCount
  TranscendentalNakamaye.Pending.BlowupStrictSubmanifold TranscendentalNakamaye.Pending.GermIdealOrder
  TranscendentalNakamaye.Pending.MarkedIdealEquivalence

noncomputable section

variable {n : ℕ}

/-! ### Regular points under biholomorphisms and local sections -/

section Regular

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Regular points correspond under a biholomorphism**: `x` is a regular point of `Φ⁻¹ A` of
dimension `k` iff `Φ x` is a regular point of `A` of dimension `k`. -/
theorem regularAtDim_preimage_iff (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {A : Set M} {x : M'} {k : ℕ} :
    RegularAtDim (n := n) (Φ ⁻¹' A) x k ↔ RegularAtDim (n := n) A (Φ x) k := by
  constructor
  · intro h
    refine RegularAtDimTransport.regularAtDim_of_preimage (g := Φ.symm) Φ.symm.contMDiff
      (MarkedIdealTowerTransport.notMem_exceptionalLocus Φ.symm (Φ x)) (A' := A) (A := Φ ⁻¹' A)
      isOpen_univ (mem_univ _) (fun u _ => ?_) ?_
    · rw [mem_preimage, Diffeomorph.apply_symm_apply]
    · rwa [Diffeomorph.symm_apply_apply]
  · intro h
    exact RegularAtDimTransport.regularAtDim_of_preimage Φ.contMDiff
      (MarkedIdealTowerTransport.notMem_exceptionalLocus Φ x) (A' := Φ ⁻¹' A) (A := A) isOpen_univ
      (mem_univ _) (fun _ _ => Iff.rfl) h

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Regular points pull back and push forward through a local section**: if the holomorphic map
`π : Y → X` has a holomorphic section `s` over an open `W ∋ π z` with `s (π z) = z`, then `z` is a
regular point of `π⁻¹ A` of dimension `k` iff `π z` is one of `A` (a blowup off its centre,
`BlowupIsomorphismOff.exists_section_compl`). -/
theorem regularAtDim_preimage_iff_of_section {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) (W : Opens X) (s : W → Y)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s) (hsπ : π ∘ s = Subtype.val)
    {z : Y} (hzW : π z ∈ W) (hsz : s ⟨π z, hzW⟩ = z) {A : Set X} {k : ℕ} :
    RegularAtDim (n := n) (π ⁻¹' A) z k ↔ RegularAtDim (n := n) A (π z) k := by
  set x : W := ⟨π z, hzW⟩ with hx
  have hπd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π (s x) :=
    (hπ (s x)).mdifferentiableAt (by simp)
  have hsd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s x :=
    (hs x).mdifferentiableAt (by simp)
  have h1 := mfderiv_comp x hπd hsd
  rw [hsπ, BlowupIsomorphismOff.mfderiv_subtype_val] at h1
  have h1' : ∀ v, mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π (s x)
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s x v) = v := fun v =>
    (DFunLike.congr_fun h1 v).symm
  -- the differential of `s` at `x` is bijective
  have hsinj : Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s x) :=
    fun a b hab => by rw [← h1' a, ← h1' b, hab]
  set Ls : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (show ComplexModel n →L[ℂ] ComplexModel n from
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s x).toLinearMap
  have hsx : x ∉ exceptionalLocus n s := fun hexc =>
    hexc ⟨hsinj, LinearMap.injective_iff_surjective (V := ComplexModel n) (f := Ls) |>.mp hsinj⟩
  -- the differential of `π` at `z = s x` is bijective
  have hπsurj : Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π (s x)) :=
    fun v => ⟨_, h1' v⟩
  set Lπ : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (show ComplexModel n →L[ℂ] ComplexModel n from
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π (s x)).toLinearMap
  have hπz : s x ∉ exceptionalLocus n π := fun hexc =>
    hexc ⟨LinearMap.injective_iff_surjective (V := ComplexModel n) (f := Lπ) |>.mpr hπsurj, hπsurj⟩
  rw [hsz] at hπz
  constructor
  · intro h
    have h' := RegularAtDimTransport.regularAtDim_of_preimage (g := s) hs hsx
      (A' := ((↑) ⁻¹' A : Set W)) (A := π ⁻¹' A) isOpen_univ (mem_univ x) (fun u _ => by
        change (u : X) ∈ A ↔ π (s u) ∈ A
        rw [show π (s u) = u from congrFun hsπ u]) (by rwa [hsz])
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp h'
  · intro h
    exact RegularAtDimTransport.regularAtDim_of_preimage hπ hπz (A' := π ⁻¹' A) (A := A) isOpen_univ
      (mem_univ _) (fun _ _ => Iff.rfl) h

end Regular

/-! ### The codimension-one part: locality, biholomorphisms, open sets -/

section CodimOne

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

omit [IsComplexManifold n M] in
/-- **The codimension-one part is local**: if near `x` the set `N` agrees with `A` and the cosupport
agrees with `S`, then `x ∈ Z₁(N, 𝔞, μ)` iff `A` is regular of dimension `k + 1` and `S` regular of
dimension `k` at `x` for some `k`. -/
theorem mem_codimOnePartAlong_iff_of_eventually {N A S : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {x : M}
    (hN : ∀ᶠ y in 𝓝 x, y ∈ N ↔ y ∈ A) (hS : ∀ᶠ y in 𝓝 x, y ∈ cosupport n N 𝔞 μ ↔ y ∈ S) :
    x ∈ codimOnePartAlong N 𝔞 μ ↔
      ∃ k, RegularAtDim (n := n) A x (k + 1) ∧ RegularAtDim (n := n) S x k := by
  constructor
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, CodimOneSupport.regularAtDim_of_eventually_mem_iff hN h1,
      CodimOneSupport.regularAtDim_of_eventually_mem_iff hS h2⟩
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, CodimOneSupport.regularAtDim_of_eventually_mem_iff (hN.mono fun _ h => h.symm) h1,
      CodimOneSupport.regularAtDim_of_eventually_mem_iff (hS.mono fun _ h => h.symm) h2⟩

omit [IsComplexManifold n M] in
/-- **Membership in the codimension-one part depends only on germs**: of `N` and of the cosupport. -/
theorem mem_codimOnePartAlong_congr {N N' : Set M} {𝔞 𝔟 : GermIdeal n M} {μ ν : ℕ} {x : M}
    (hN : ∀ᶠ y in 𝓝 x, y ∈ N ↔ y ∈ N')
    (hS : ∀ᶠ y in 𝓝 x, y ∈ cosupport n N 𝔞 μ ↔ y ∈ cosupport n N' 𝔟 ν) :
    x ∈ codimOnePartAlong N 𝔞 μ ↔ x ∈ codimOnePartAlong N' 𝔟 ν :=
  mem_codimOnePartAlong_iff_of_eventually hN hS

omit [IsComplexManifold n M] in
/-- **Equal supports have equal codimension-one parts** (the same `N`). -/
theorem codimOnePartAlong_congr {N N' : Set M} {𝔞 𝔟 : GermIdeal n M} {μ ν : ℕ} (hN : N = N')
    (hS : cosupport n N 𝔞 μ = cosupport n N' 𝔟 ν) :
    codimOnePartAlong N 𝔞 μ = codimOnePartAlong N' 𝔟 ν := by
  ext x
  exact mem_codimOnePartAlong_congr (Eventually.of_forall fun _ => by rw [hN])
    (Eventually.of_forall fun _ => by rw [hS])

/-- **The support along `N` is invariant under biholomorphisms**:
`cosupp((Φ^*𝔞)|_{Φ⁻¹N}, μ) = Φ⁻¹ cosupp(𝔞|_N, μ)` (ideal of holomorphic germs). -/
theorem cosupport_pullback (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M) {N : Set M}
    {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (μ : ℕ) :
    cosupport n (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ = Φ ⁻¹' cosupport n N 𝔞 μ :=
  MarkedIdeal.cosupp_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply
    (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) h𝔞

/-- **The codimension-one part along `N` is invariant under biholomorphisms**:
`Z₁(Φ⁻¹N, Φ^*𝔞, μ) = Φ⁻¹ Z₁(N, 𝔞, μ)` (ideal of holomorphic germs). -/
theorem codimOnePartAlong_pullback (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {N : Set M} {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (μ : ℕ) :
    codimOnePartAlong (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ =
      Φ ⁻¹' codimOnePartAlong N 𝔞 μ := by
  ext x
  change (∃ k, RegularAtDim (n := n) (Φ ⁻¹' N) x (k + 1) ∧
      RegularAtDim (n := n) (cosupport n (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ) x k) ↔
    ∃ k, RegularAtDim (n := n) N (Φ x) (k + 1) ∧ RegularAtDim (n := n) (cosupport n N 𝔞 μ) (Φ x) k
  rw [cosupport_pullback Φ h𝔞 μ]
  simp only [regularAtDim_preimage_iff Φ]

/-- **The codimension-one part along `N` restricts to open sets**:
`Z₁(N ∩ U, 𝔞|_U, μ) = Z₁(N, 𝔞, μ) ∩ U` (ideal of holomorphic germs). -/
theorem codimOnePartAlong_pullback_val (U : Opens M) {N : Set M} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (μ : ℕ) :
    codimOnePartAlong ((↑) ⁻¹' N : Set U) (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) μ =
      (↑) ⁻¹' codimOnePartAlong N 𝔞 μ := by
  have hc : cosupport n ((↑) ⁻¹' N : Set U) (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) μ =
      (↑) ⁻¹' cosupport n N 𝔞 μ :=
    cosupp_pullback_val (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) h𝔞 U
  ext x
  change (∃ k, RegularAtDim (n := n) ((↑) ⁻¹' N : Set U) x (k + 1) ∧
      RegularAtDim (n := n) (cosupport n ((↑) ⁻¹' N : Set U)
        (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) μ) x k) ↔
    ∃ k, RegularAtDim (n := n) N (x : M) (k + 1) ∧ RegularAtDim (n := n) (cosupport n N 𝔞 μ) (x : M) k
  rw [hc]
  simp only [AnalyticSubsetOpens.regularAtDim_preimage_val_iff]

end CodimOne

/-! ### The codimension-one part off the centre of a blowup -/

section OffCentre

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- **Off the centre the codimension-one part does not change**: for the blowup `π` along `C` and
`π z ∉ C`, `z` lies in the codimension-one part of the transform iff `π z` lies in that of `𝔪`
(`N` closed, ideal of holomorphic germs). -/
theorem mem_codimOnePartAlong_geoTransform_iff (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : π z ∉ C) :
    z ∈ codimOnePartAlong (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal (𝔪.geoTransform C π).d ↔
      π z ∈ codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hO : π ⁻¹' Cᶜ ∈ 𝓝 z :=
    (hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hz
  have hNz : ∀ᶠ y in 𝓝 z, y ∈ (𝔪.geoTransform C π).N ↔ y ∈ π ⁻¹' 𝔪.N :=
    TransformOffCentre.eventually_mem_geoStrictTransform_iff hN hπ.1.1 hπ.contMDiff.continuous hz
  have hSz : ∀ᶠ y in 𝓝 z, y ∈ cosupport n (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal
      (𝔪.geoTransform C π).d ↔ y ∈ π ⁻¹' cosupport n 𝔪.N 𝔪.ideal 𝔪.d := by
    filter_upwards [hO] with y hy
    exact TransformOffCentre.mem_cosupp_geoTransform_iff 𝔪 hN h𝔞 hπ hy
  rw [mem_codimOnePartAlong_iff_of_eventually hNz hSz]
  have hreg : ∀ (A : Set X) (k : ℕ),
      RegularAtDim (n := n) (π ⁻¹' A) z k ↔ RegularAtDim (n := n) A (π z) k := fun _ _ =>
    regularAtDim_preimage_iff_of_section hπ.contMDiff _ s hs hsπ hz (hsec z hz)
  exact exists_congr fun k => and_congr (hreg _ _) (hreg _ _)

/-- **A blowup along `∅` pulls the codimension-one part back** (property (4), empty steps). -/
theorem codimOnePartAlong_geoTransform_empty (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n ∅ π) :
    codimOnePartAlong (𝔪.geoTransform ∅ π).N (𝔪.geoTransform ∅ π).ideal (𝔪.geoTransform ∅ π).d =
      π ⁻¹' codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d :=
  Set.ext fun _ => mem_codimOnePartAlong_geoTransform_iff 𝔪 hN h𝔞 hπ (Set.notMem_empty _)

end OffCentre

/-! ### The codimension-one part along towers -/

section Tower

variable {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Off the centre of the last blowup of a tower the codimension-one part does not change**
(properties (3) "equal otherwise" and (4)): along a multiple test blow-up `T` followed by the blowup
`π` along `C`, for `π z ∉ C`, `z ∈ Z₁` of the transform iff `π z ∈ Z₁` of the transform along `T`. -/
theorem mem_codimOnePartAlong_geoTransformAlong_step_iff (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z} (hz : π z ∉ C) :
    z ∈ codimOnePartAlong (geoTransformAlong 𝔪 (.step T C π hπ)).N
        (geoTransformAlong 𝔪 (.step T C π hπ)).ideal (geoTransformAlong 𝔪 (.step T C π hπ)).d ↔
      π z ∈ codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
        (geoTransformAlong 𝔪 T).d := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  exact mem_codimOnePartAlong_geoTransform_iff (geoTransformAlong 𝔪 T) hNT.1
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hπ hz

/-- **The codimension-one part along transported towers** (property (6)): along the transport of a
tower `T` by a biholomorphism `Φ : X' ≅ X` of the base, the codimension-one part of the transform of
`Φ^*𝔪` is the preimage under the last-stage biholomorphism of that of the transform of `𝔪`. -/
theorem codimOnePartAlong_geoTransformAlong_transport
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      codimOnePartAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).N
          (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).ideal
          (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).d =
        (transport Φ T).back ⁻¹' codimOnePartAlong (geoTransformAlong 𝔪 T).N
          (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d
  | _, .refl => codimOnePartAlong_pullback Φ
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) 𝔪.d
  | _, .step T C π hπ => by
      rw [geoTransformAlong_transport_step Φ h𝔞 T C π hπ]
      rfl

/-- **The codimension-one part along restricted towers** (property (5)): along the restriction to an
open `U` of a multiple test blow-up `T`, the codimension-one part of the transform of `𝔪|_U` is the
trace on the open preimage of `U` of that of the transform of `𝔪`. -/
theorem codimOnePartAlong_geoTransformAlong_restrict (U : Opens X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    codimOnePartAlong (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).N
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).ideal
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).d =
      ((↑) : openPreimage T U → Y) ⁻¹' codimOnePartAlong (geoTransformAlong 𝔪 T).N
        (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_restrict U hN h𝔞 T hT]
  exact codimOnePartAlong_pullback_val (openPreimage T U)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) _

/-- **Restricted-equivalent marked ideals have the same codimension-one part at every stage**
(property (7); closed `N`, coherent ideals). -/
theorem codimOnePartAlong_geoTransformAlong_of_restrictEquiv {𝔫 : MarkedIdeal n X}
    (h : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d =
        codimOnePartAlong (geoTransformAlong 𝔫 T).N (geoTransformAlong 𝔫 T).ideal (geoTransformAlong 𝔫 T).d
  | _, .refl => codimOnePartAlong_congr h.N_eq h.cosupp_eq
  | _, .step T C π hπ => by
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C π hπ]

/-- **Equivalent marked ideals with the same `N` have the same codimension-one part along every
multiple test blow-up** (property (7) for the replacement of `𝔪` by `𝓒(𝓗(𝔪))`). -/
theorem codimOnePartAlong_geoTransformAlong_of_wEquiv {𝔫 : MarkedIdeal n X}
    (h : MarkedIdealEquivalence.MarkedIdeal.WEquiv 𝔪 𝔫)
    (hN : 𝔪.N = 𝔫.N) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d =
      codimOnePartAlong (geoTransformAlong 𝔫 T).N (geoTransformAlong 𝔫 T).ideal
        (geoTransformAlong 𝔫 T).d :=
  codimOnePartAlong_congr (by rw [N_geoTransformAlong, N_geoTransformAlong, hN]) ((h.2 T).2 hT)

end Tower

/-! ### The boundary count -/

section Boundary

open Classical in
/-- **Re-indexing by preimages**: `s(E.map (f⁻¹ ·))(z) = s(E)(f z)`. -/
theorem boundaryCount_map_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → X) (E : List (Set X)) (z : Y) :
    boundaryCount (E.map (f ⁻¹' ·)) z = boundaryCount E (f z) := by
  rw [boundaryCount_map]
  unfold boundaryCount
  exact congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  {Y : Type u} [TopologicalSpace Y] {C : Set X} {π : Y → X}

open Classical in
/-- **Off the centre the boundary count does not change**: for closed members and `π z ∉ C`
(`C` closed), `z` lies on as many strict transforms as `π z` lies on members. -/
theorem boundaryCount_map_geoStrictTransform_of_notMem (hC : IsClosed C) (hπc : Continuous π)
    {E : List (Set X)} (hE : ∀ H ∈ E, IsClosed H) {z : Y} (hz : π z ∉ C) :
    boundaryCount (E.map (geoStrictTransform π C)) z = boundaryCount E (π z) := by
  rw [boundaryCount_map]
  unfold boundaryCount
  exact congrArg Finset.card (Finset.filter_congr fun i _ =>
    (TransformOffCentre.eventually_mem_geoStrictTransform_iff (hE _ (List.get_mem _ _)) hC hπc
      hz).self_of_nhds)

end Boundary

section BoundaryTower

variable {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Off the centre of the last blowup the count of the original members does not change**
(properties (3) "equal otherwise" and (4) for `s`): along `T` followed by the blowup `π` along `C`,
for `π z ∉ C`, `s(z) = s(π z)`. -/
theorem boundaryCount_take_E_geoTransformAlong_step_of_notMem (hE : ∀ H ∈ 𝔪.E, IsClosed H)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : π z ∉ C) :
    boundaryCount ((geoTransformAlong 𝔪 (.step T C π hπ)).E.take 𝔪.E.length) z =
      boundaryCount ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length) (π z) := by
  have hlen : 𝔪.E.length ≤ ((geoTransformAlong 𝔪 T).E.map (geoStrictTransform π C)).length := by
    rw [List.length_map, MarkedIdeal.length_E_geoTransformAlong]; omega
  rw [MarkedIdeal.geoTransformAlong_step, MarkedIdeal.geoTransform_E, List.take_append_of_le_length hlen,
    ← List.map_take]
  exact boundaryCount_map_geoStrictTransform_of_notMem hπ.1.1 hπ.contMDiff.continuous
    (isClosed_of_mem_take_E_geoTransformAlong 𝔪 hE T) hz

/-- **The count of the original members along transported towers** (property (6) for `s`). -/
theorem boundaryCount_take_E_geoTransformAlong_transport
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → ∀ p : (transport Φ T).target,
      boundaryCount ((geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).E.take
          𝔪.E.length) p =
        boundaryCount ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length) ((transport Φ T).back p)
  | _, .refl, p => by
      change boundaryCount ((𝔪.E.map (Φ ⁻¹' ·)).take 𝔪.E.length) p =
        boundaryCount (𝔪.E.take 𝔪.E.length) (Φ p)
      rw [List.take_of_length_le (by rw [List.length_map]), List.take_of_length_le le_rfl]
      exact boundaryCount_map_preimage Φ 𝔪.E p
  | _, .step T C π hπ, p => by
      rw [geoTransformAlong_transport_step Φ h𝔞 T C π hπ, transport_step_back]
      rfl

/-- **The count of the original members along restricted towers** (property (5) for `s`): along the
restriction to an open `U` of a multiple test blow-up `T`, `s` of `𝔪|_U` is the restriction of `s` of
`𝔪`. -/
theorem boundaryCount_take_E_geoTransformAlong_restrict (U : Opens X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (p : openPreimage T U) :
    boundaryCount ((geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).E.take
        𝔪.E.length) p =
      boundaryCount ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length) (p : Y) := by
  rw [geoTransformAlong_restrict U hN h𝔞 T hT]
  change boundaryCount (((geoTransformAlong 𝔪 T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·)).take
    𝔪.E.length) p = _
  rw [← List.map_take]
  exact boundaryCount_map_preimage _ _ p

end BoundaryTower

end

end TranscendentalNakamaye.Pending.CodimOnePartCanonical
