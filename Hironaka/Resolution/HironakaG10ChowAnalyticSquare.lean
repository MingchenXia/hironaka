import Hironaka.Resolution.HironakaG10ChowFibreTorsionWitness
import Hironaka.Resolution.HironakaNonreducedQuotientGermLifting
import Hironaka.Resolution.HironakaG10FlatSimultaneousFlattener

/-!
# Lemma 1.18 for a commutative square of analytic local rings (route step M6, ring level)

The native form of Rydh's Lemma 1.18 / Hironaka's (2.4.3)+(2.5) (Hironaka 1975, printed pp. 526,
529–530) without any geometric chart data: only a commutative square of local rings
```
  A_X --u--> A_Y
   |σ         |q
   v          v
  A_X' --p--> B
```
each with an *analytic presentation* (a surjection from the germs of some `ℂ^n` that is the given
structure map on constants), all maps local and compatible with the structure maps.  Every such map
is induced by a germ of holomorphic map (`exists_lift`; coordinates + Taylor + Krull,
`HironakaNonreducedQuotientGermLifting.local_algHom_ext_coordinates`), so the square is presented by
germ maps and the germ-level Lemma 1.18 (`HironakaG10ChowFibreTorsionWitness`) applies.

* `GermPresentation`, `exists_lift`;
* `graphHom` — the graph presentation of `A_Y` over the base germs (`T(g) = π_Y(g(F w, w))`);
* `flat_iff_graphFlattener_le`, `exists_pointFlattener` — **the pointed flattener of `u`**: an
  ideal `I` of `A_X` with `A_X/J → A_Y/J A_Y` flat iff `I ≤ J` (Hironaka (1.14.1)/(1.14.2) at a point;
  `I` = image of the canonical flattener ideal of the graph presentation);
* `exists_fibre_decrease_of_square` — **Lemma 1.18**: if the pointed flattener pulls back to `A_X'`
  as `(a)`, `a` regular, and `p a` is regular in `B`, some element of `A_Y` outside the fibre ideal
  `m_X A_Y` is sent into the fibre ideal `m_X' B`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.HironakaG10ChowAnalyticSquare

open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualAnalyticBaseChangeCoefficients
  HironakaActualJointBaseFibre HironakaActualCentreJointJets HironakaRelativeNormalFibreHilbertSamuel
  HironakaChowPresentationIndependentFlattener HironakaG10FlatSimultaneousFlattener
  HironakaG10ChowFibreTorsionWitness HironakaNonreducedQuotientGermLifting

noncomputable section

/-! ### Germ maps -/

/-- Composition of germ pull-backs. -/
theorem compAlgHom_compAlgHom {k m n : ℕ} (η : ComplexModel k → ComplexModel m)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel k), DifferentiableAt ℂ η z) (hη0 : η 0 = 0)
    (ζ : ComplexModel m → ComplexModel n)
    (hζ : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ ζ z) (hζ0 : ζ 0 = 0)
    (θ : ComplexModel k → ComplexModel n)
    (hθ : ∀ᶠ z in 𝓝 (0 : ComplexModel k), DifferentiableAt ℂ θ z) (hθ0 : θ 0 = 0)
    (h : ∀ z, θ z = ζ (η z)) (g : HolGerm (ComplexModel n)) :
    compAlgHom η hη hη0 (compAlgHom ζ hζ hζ0 g) = compAlgHom θ hθ hθ0 g := by
  obtain rfl : θ = ζ ∘ η := funext h
  induction g using HolGerm.induction_on with
  | h F hF => rfl

/-- Germ pull-backs are local. -/
theorem isLocalHom_compAlgHom {m n : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z) (hη0 : η 0 = 0) :
    IsLocalHom (compAlgHom η hη hη0).toRingHom := by
  refine ⟨fun g hg => ?_⟩
  apply (HolGerm.isUnit_iff_eval_ne_zero g).mpr
  have h := (HolGerm.isUnit_iff_eval_ne_zero (compAlgHom η hη hη0 g)).mp hg
  rwa [eval_compAlgHom'] at h

theorem holomorphic_comp' {k m n : ℕ} (η : ComplexModel k → ComplexModel m)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel k), DifferentiableAt ℂ η z) (hη0 : η 0 = 0)
    (ζ : ComplexModel m → ComplexModel n)
    (hζ : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ ζ z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel k), DifferentiableAt ℂ (fun z => ζ (η z)) z := by
  have ht : Tendsto η (𝓝 0) (𝓝 0) := by
    simpa only [hη0] using hη.self_of_nhds.continuousAt.tendsto
  filter_upwards [hη, ht.eventually hζ] with z hz hz'
  exact hz'.comp z hz

/-! ### Analytic presentations and lifts -/

/-- An **analytic presentation** of a ring `A` with structure map `κ : ℂ →+* A`: a surjection from
the germs of `ℂ^dim` which is `κ` on constants. -/
structure GermPresentation (A : Type*) [CommRing A] (κ : ℂ →+* A) where
  dim : ℕ
  π : HolGerm (ComplexModel dim) →+* A
  surjective : Function.Surjective π
  const : ∀ c : ℂ, π (algebraMap ℂ (HolGerm (ComplexModel dim)) c) = κ c

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  {κA : ℂ →+* A} {κB : ℂ →+* B}

theorem GermPresentation.isLocalHom (P : GermPresentation A κA) : IsLocalHom P.π :=
  IsLocalHom.of_surjective P.π P.surjective

omit [IsLocalRing A] in
theorem GermPresentation.isNoetherianRing (P : GermPresentation A κA) : IsNoetherianRing A :=
  have : IsNoetherianRing (HolGerm (ComplexModel P.dim)) := isNoetherianRing_holGerm_euclidean _
  isNoetherianRing_of_surjective _ _ P.π P.surjective

theorem GermPresentation.map_mem_maximalIdeal (P : GermPresentation A κA)
    {g : HolGerm (ComplexModel P.dim)} (hg : g ∈ IsLocalRing.maximalIdeal _) :
    P.π g ∈ IsLocalRing.maximalIdeal A := by
  have := P.isLocalHom
  exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hg (isUnit_of_map_unit P.π g hu)

theorem GermPresentation.map_maximalIdeal (P : GermPresentation A κA) :
    Ideal.map P.π (IsLocalRing.maximalIdeal (HolGerm (ComplexModel P.dim))) =
      IsLocalRing.maximalIdeal A := by
  have := P.isLocalHom
  exact IsLocalRing.map_maximalIdeal_of_surjective P.π P.surjective

/-- **Every local map of presented analytic rings is induced by a germ of holomorphic map.** -/
theorem exists_lift (PA : GermPresentation A κA) (PB : GermPresentation B κB) (u : A →+* B)
    [IsLocalHom u] (hu : ∀ c, u (κA c) = κB c) :
    ∃ (F : ComplexModel PB.dim → ComplexModel PA.dim)
      (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel PB.dim), DifferentiableAt ℂ F z) (hF0 : F 0 = 0),
      ∀ g, u (PA.π g) = PB.π (compAlgHom F hF hF0 g) := by
  let _ : Algebra ℂ B := κB.toAlgebra
  have := PB.isNoetherianRing
  have := PA.isLocalHom
  have := PB.isLocalHom
  choose v hv using fun i : Fin PA.dim => PB.surjective (u (PA.π (coordinateGerm i)))
  have hv0 (i : Fin PA.dim) : eval (v i) = 0 := by
    have hc : coordinateGerm i ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel PA.dim)) :=
      (HolGerm.mem_maximalIdeal_iff _).mpr rfl
    have hm : u (PA.π (coordinateGerm i)) ∈ IsLocalRing.maximalIdeal B :=
      (IsLocalRing.mem_maximalIdeal _).mpr fun hu' =>
        (IsLocalRing.mem_maximalIdeal _).mp (PA.map_mem_maximalIdeal hc) (isUnit_of_map_unit u _ hu')
    by_contra he
    have hu' := PB.π.isUnit_map ((HolGerm.isUnit_iff_eval_ne_zero (v i)).mpr he)
    rw [hv i] at hu'
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hu'
  choose G hG hrep using fun i : Fin PA.dim => HolGerm.exists_eq_mk (v i)
  let F : ComplexModel PB.dim → ComplexModel PA.dim := fun z =>
    (EuclideanSpace.equiv (Fin PA.dim) ℂ).symm (fun i => G i z)
  have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel PB.dim), DifferentiableAt ℂ F z := by
    filter_upwards [eventually_all.mpr hG] with z hz
    exact (differentiableAt_piLp 2).mpr hz
  have hF0 : F 0 = 0 := by
    ext i
    change G i 0 = 0
    have he : eval (v i) = G i 0 := by rw [hrep i]; rfl
    exact he.symm.trans (hv0 i)
  have hCoord (i : Fin PA.dim) : compAlgHom F hF hF0 (coordinateGerm i) = v i := by
    rw [hrep i, coordinateGerm, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun _ => rfl
  let a : HolGerm (ComplexModel PA.dim) →ₐ[ℂ] B :=
    { toRingHom := u.comp PA.π
      commutes' := fun c => by
        change u (PA.π (algebraMap ℂ _ c)) = κB c
        rw [PA.const, hu] }
  let b : HolGerm (ComplexModel PA.dim) →ₐ[ℂ] B :=
    { toRingHom := PB.π.comp (compAlgHom F hF hF0).toRingHom
      commutes' := fun c => by
        change PB.π (compAlgHom F hF hF0 (algebraMap ℂ _ c)) = κB c
        rw [AlgHom.commutes, PB.const] }
  have : IsLocalHom a.toRingHom := by
    change IsLocalHom (u.comp PA.π)
    infer_instance
  have : IsLocalHom (compAlgHom F hF hF0).toRingHom := isLocalHom_compAlgHom F hF hF0
  have : IsLocalHom b.toRingHom := by
    change IsLocalHom (PB.π.comp (compAlgHom F hF hF0).toRingHom)
    infer_instance
  have hab : a = b := local_algHom_ext_coordinates PA.dim a b (fun i => by
    change u (PA.π (coordinateGerm i)) = PB.π (compAlgHom F hF hF0 (coordinateGerm i))
    rw [hCoord i, hv i])
  exact ⟨F, hF, hF0, fun g => congrArg (fun φ : HolGerm (ComplexModel PA.dim) →ₐ[ℂ] B => φ g) hab⟩

/-! ### The graph presentation -/

section Graph

variable {d t : ℕ}

/-- The graph map `w ↦ (F w, w)`, base coordinates first. -/
def graphMap (F : ComplexModel t → ComplexModel d) (w : ComplexModel t) : ComplexModel (d+t) :=
  tangentInclusion d t (F w) + actualJointNormalInclusion d t w

theorem graphMap_holomorphic (F : ComplexModel t → ComplexModel d)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ F z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ (graphMap F) z := by
  filter_upwards [hF] with w hw
  exact ((tangentInclusion d t).differentiableAt.comp w hw).add
    (actualJointNormalInclusion d t).differentiableAt

theorem graphMap_zero (F : ComplexModel t → ComplexModel d) (hF0 : F 0 = 0) : graphMap F 0 = 0 := by
  simp only [graphMap, hF0, map_zero, add_zero]

@[simp] theorem tangentProjection_graphMap (F : ComplexModel t → ComplexModel d) (w : ComplexModel t) :
    tangentProjection d t (graphMap F w) = F w := by
  simp only [graphMap, map_add, tangentProjection_tangentInclusion,
    tangentProjection_actualJointNormalInclusion, add_zero]

@[simp] theorem actualJointNormalProjection_graphMap (F : ComplexModel t → ComplexModel d)
    (w : ComplexModel t) : actualJointNormalProjection d t (graphMap F w) = w := by
  simp only [graphMap, map_add, actualJointNormalProjection_tangent,
    actualJointNormalProjection_inclusion, zero_add]

variable {AY : Type*} [CommRing AY] {κY : ℂ →+* AY}

/-- The graph presentation `T(g) = π_Y(g(F w, w))`. -/
def graphHom (PY : GermPresentation AY κY) (F : ComplexModel PY.dim → ComplexModel d)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel PY.dim), DifferentiableAt ℂ F z) (hF0 : F 0 = 0) :
    HolGerm (ComplexModel (d+PY.dim)) →+* AY :=
  PY.π.comp (compAlgHom (graphMap F) (graphMap_holomorphic F hF) (graphMap_zero F hF0)).toRingHom

variable (PY : GermPresentation AY κY) (F : ComplexModel PY.dim → ComplexModel d)
  (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel PY.dim), DifferentiableAt ℂ F z) (hF0 : F 0 = 0)

theorem graphHom_tangentPullback (g : HolGerm (ComplexModel d)) :
    graphHom PY F hF hF0 (tangentPullback d PY.dim g) = PY.π (compAlgHom F hF hF0 g) := by
  change PY.π (compAlgHom _ _ _ (compAlgHom _ _ _ g)) = _
  rw [compAlgHom_compAlgHom _ _ _ _ _ _ F hF hF0 (fun w => (tangentProjection_graphMap F w).symm)]

theorem graphHom_jointNormalPullback (g : HolGerm (ComplexModel PY.dim)) :
    graphHom PY F hF hF0 (jointNormalPullback d PY.dim g) = PY.π g := by
  change PY.π (compAlgHom _ _ _ (compAlgHom _ _ _ g)) = _
  rw [compAlgHom_compAlgHom _ _ _ _ _ _ id (Eventually.of_forall fun _ => differentiableAt_id) rfl
    (fun w => (actualJointNormalProjection_graphMap F w).symm)]
  congr 1
  induction g using HolGerm.induction_on with
  | h G hG => rfl

theorem graphHom_surjective : Function.Surjective (graphHom PY F hF hF0) := by
  intro r
  obtain ⟨g, rfl⟩ := PY.surjective r
  exact ⟨jointNormalPullback d PY.dim g, graphHom_jointNormalPullback PY F hF hF0 g⟩

theorem graphHom_const (c : ℂ) :
    graphHom PY F hF hF0 (algebraMap ℂ _ c) = κY c := by
  change PY.π (compAlgHom _ _ _ (algebraMap ℂ _ c)) = _
  rw [AlgHom.commutes, PY.const]

end Graph

/-! ### The pointed flattener -/

section Flattener

variable {AX AY : Type*} [CommRing AX] [CommRing AY] [IsLocalRing AX] [IsLocalRing AY]
  {κX : ℂ →+* AX} {κY : ℂ →+* AY}

local instance (d n : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) := tangentAlgebra d n

omit [IsLocalRing AX] [IsLocalRing AY] in
/-- **The pointed flattener through the graph presentation**: for any lift `F` of `u`, the image of
the canonical flattener ideal of the graph presentation characterizes flatness after every base
change to a quotient `A_X/J`. -/
theorem flat_iff_graphFlattener_le (PX : GermPresentation AX κX) (PY : GermPresentation AY κY)
    (u : AX →+* AY) (F : ComplexModel PY.dim → ComplexModel PX.dim)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel PY.dim), DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hlift : ∀ g, u (PX.π g) = PY.π (compAlgHom F hF hF0 g)) (J : Ideal AX) :
    (Ideal.quotientMap (J.map u) u Ideal.le_comap_map).Flat ↔
      Ideal.map PX.π (canonicalFlattenerIdeal PX.dim PY.dim (RingHom.ker (graphHom PY F hF hF0))) ≤ J := by
  set T := graphHom PY F hF hF0 with hT
  set Jt := Ideal.comap PX.π J with hJt
  set K := RingHom.ker T ⊔ Ideal.map (tangentPullback PX.dim PY.dim).toRingHom Jt with hK
  have hTt : ∀ g, T (tangentPullback PX.dim PY.dim g) = u (PX.π g) := fun g =>
    (graphHom_tangentPullback PY F hF hF0 g).trans (hlift g).symm
  have hle1 : Jt ≤ Ideal.comap (tangentPullback PX.dim PY.dim).toRingHom K := fun g hg =>
    Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hg)
  have hcomp : T.comp (tangentPullback PX.dim PY.dim).toRingHom = u.comp PX.π := RingHom.ext hTt
  have hmapJ : Ideal.map u J = Ideal.map T (Ideal.map (tangentPullback PX.dim PY.dim).toRingHom Jt) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hJt, Ideal.map_comap_of_surjective _ PX.surjective]
  have hK' : Ideal.comap T (Ideal.map u J) = K := by
    rw [hmapJ, Ideal.comap_map_of_surjective _ (graphHom_surjective PY F hF hF0), hK, sup_comm]
    rfl
  -- the quotient maps
  let g1 := Ideal.quotientMap K (tangentPullback PX.dim PY.dim).toRingHom hle1
  let e1 := Ideal.quotientMap J PX.π (le_refl Jt)
  have he1 : Function.Bijective e1 :=
    ⟨Ideal.quotientMap_injective' (le_refl _), Ideal.quotientMap_surjective PX.surjective⟩
  let e2 := Ideal.quotientMap (Ideal.map u J) T hK'.ge
  have he2 : Function.Bijective e2 :=
    ⟨Ideal.quotientMap_injective' hK'.le,
      Ideal.quotientMap_surjective (graphHom_surjective PY F hF hF0)⟩
  have hsq : e2.comp g1 = (Ideal.quotientMap (J.map u) u Ideal.le_comap_map).comp e1 := by
    apply Ideal.Quotient.ringHom_ext
    ext g
    change Ideal.Quotient.mk _ (T (tangentPullback PX.dim PY.dim g)) =
      Ideal.Quotient.mk _ (u (PX.π g))
    rw [hTt]
  have hflat : (Module.Flat (HolGerm (ComplexModel PX.dim) ⧸ Jt)
      (HolGerm (ComplexModel (PX.dim + PY.dim)) ⧸ K)) ↔ g1.Flat := by
    rw [← RingHom.flat_algebraMap_iff]
    have : algebraMap (HolGerm (ComplexModel PX.dim) ⧸ Jt)
        (HolGerm (ComplexModel (PX.dim + PY.dim)) ⧸ K) = g1 := by
      apply Ideal.Quotient.ringHom_ext
      ext g
      rfl
    rw [this]
  rw [← RingHom.Flat.comp_iff_of_bijective_right he1, ← hsq,
    RingHom.Flat.comp_iff_of_bijective_left he2, ← hflat]
  exact (flat_iff_canonicalFlattenerIdeal_le PX.dim PY.dim (RingHom.ker T) Jt).trans
    Ideal.map_le_iff_le_comap.symm

/-- **Pointed flatteners exist** for every local map of presented analytic rings. -/
theorem exists_pointFlattener (PX : GermPresentation AX κX) (PY : GermPresentation AY κY)
    (u : AX →+* AY) [IsLocalHom u] (hu : ∀ c, u (κX c) = κY c) :
    ∃ I : Ideal AX, ∀ J : Ideal AX,
      (Ideal.quotientMap (J.map u) u Ideal.le_comap_map).Flat ↔ I ≤ J := by
  obtain ⟨F, hF, hF0, hlift⟩ := exists_lift PX PY u hu
  exact ⟨_, flat_iff_graphFlattener_le PX PY u F hF hF0 hlift⟩

/-- Pointed flatteners are unique. -/
theorem pointFlattener_unique {R : Type*} [CommRing R] (P : Ideal R → Prop) (I I' : Ideal R)
    (hI : ∀ J, P J ↔ I ≤ J) (hI' : ∀ J, P J ↔ I' ≤ J) : I = I' :=
  le_antisymm ((hI I').mp ((hI' I').mpr le_rfl)) ((hI' I).mp ((hI I).mpr le_rfl))

end Flattener

/-! ### Lemma 1.18 for an analytic square -/

section Square

theorem isRegular_of_map {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {x : R}
    (h : IsRegular (e x)) : IsRegular x := by
  refine ⟨fun y z hyz => e.injective (h.1 ?_), fun y z hyz => e.injective (h.2 ?_)⟩
  · change e x * e y = e x * e z
    rw [← map_mul, ← map_mul]
    exact congrArg e hyz
  · change e y * e x = e z * e x
    rw [← map_mul, ← map_mul]
    exact congrArg e hyz

theorem coordinateGerm_castAdd (d t : ℕ) (i : Fin d) :
    coordinateGerm (Fin.castAdd t i) = tangentPullback d t (coordinateGerm i) := by
  unfold tangentPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp

theorem coordinateGerm_natAdd (d t : ℕ) (i : Fin t) :
    coordinateGerm (Fin.natAdd d i) = jointNormalPullback d t (coordinateGerm i) := by
  unfold jointNormalPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp

theorem isLocalHom_jointBasePullback (d e t : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0) :
    IsLocalHom (jointBasePullback d e t φ hφ hφ0).toRingHom := by
  unfold jointBasePullback
  exact isLocalHom_compAlgHom _ _ _

variable {AX AY AX' B : Type*} [CommRing AX] [CommRing AY] [CommRing AX'] [CommRing B]
  [IsLocalRing AX] [IsLocalRing AY] [IsLocalRing AX'] [IsLocalRing B]
  {κX : ℂ →+* AX} {κY : ℂ →+* AY} {κX' : ℂ →+* AX'} {κB : ℂ →+* B}

/-- **Lemma 1.18 for a commutative square of analytic local rings** (Rydh, Lemma 1.18; Hironaka
(2.4.3), (2.5), Lemma 3.1; HLT Th. 2′).  If the pointed flattener `I` of `u : A_X → A_Y` pulls back
along `σ` to a principal ideal `(a)` with `a` regular, and `p a` is regular in `B`, then some
element of `A_Y` outside the fibre ideal `m_X A_Y` is sent by `q` into the fibre ideal `m_X' B`. -/
theorem exists_fibre_decrease_of_square (PX : GermPresentation AX κX)
    (PY : GermPresentation AY κY) (PX' : GermPresentation AX' κX') (PB : GermPresentation B κB)
    (u : AX →+* AY) (σ : AX →+* AX') (p : AX' →+* B) (q : AY →+* B)
    [IsLocalHom u] [IsLocalHom σ] [IsLocalHom p] [IsLocalHom q]
    (hu : ∀ c, u (κX c) = κY c) (hσ : ∀ c, σ (κX c) = κX' c) (hp : ∀ c, p (κX' c) = κB c)
    (hq : ∀ c, q (κY c) = κB c) (hsq : ∀ r, p (σ r) = q (u r))
    (I : Ideal AX)
    (hI : ∀ J : Ideal AX, (Ideal.quotientMap (J.map u) u Ideal.le_comap_map).Flat ↔ I ≤ J)
    (a : AX') (ha : IsRegular a) (hRR : Ideal.map σ I = Ideal.span {a}) (hpa : IsRegular (p a)) :
    ∃ h : AY, h ∉ Ideal.map u (IsLocalRing.maximalIdeal AX) ∧
      q h ∈ Ideal.map p (IsLocalRing.maximalIdeal AX') := by
  obtain ⟨F, hF, hF0, hFl⟩ := exists_lift PX PY u hu
  obtain ⟨φ, hφ, hφ0, hφl⟩ := exists_lift PX PX' σ hσ
  obtain ⟨P, hP, hP0, hPl⟩ := exists_lift PX' PB p hp
  obtain ⟨Q, hQ, hQ0, hQl⟩ := exists_lift PY PB q hq
  have := PX.isLocalHom
  have := PY.isLocalHom
  have := PX'.isLocalHom
  have := PB.isLocalHom
  set T := graphHom PY F hF hF0 with hT
  have hTs := graphHom_surjective PY F hF hF0
  set Ik := RingHom.ker T with hIk
  have hIeq : I = Ideal.map PX.π (canonicalFlattenerIdeal PX.dim PY.dim Ik) :=
    pointFlattener_unique _ _ _ hI (flat_iff_graphFlattener_le PX PY u F hF hF0 hFl)
  let eA : (HolGerm (ComplexModel (PX.dim + PY.dim)) ⧸ Ik) ≃+* AY :=
    RingHom.quotientKerEquivOfSurjective hTs
  have heA : ∀ g, eA (Ideal.Quotient.mk Ik g) = T g := fun g => rfl
  set q0 := RingHom.ker PX'.π with hq0
  obtain ⟨a0, rfl⟩ := PX'.surjective a
  let eX' : (HolGerm (ComplexModel PX'.dim) ⧸ q0) ≃+* AX' :=
    RingHom.quotientKerEquivOfSurjective PX'.surjective
  have heX' : (eX' : _ →+* AX').comp (Ideal.Quotient.mk q0) = PX'.π := RingHom.ext fun _ => rfl
  -- the joint map `ψ`
  let Θ : ComplexModel PB.dim → ComplexModel (PX'.dim + PY.dim) := fun z =>
    tangentInclusion PX'.dim PY.dim (P z) + actualJointNormalInclusion PX'.dim PY.dim (Q z)
  have hΘ : ∀ᶠ z in 𝓝 (0 : ComplexModel PB.dim), DifferentiableAt ℂ Θ z := by
    filter_upwards [hP, hQ] with z h1 h2
    exact ((tangentInclusion PX'.dim PY.dim).differentiableAt.comp z h1).add
      ((actualJointNormalInclusion PX'.dim PY.dim).differentiableAt.comp z h2)
  have hΘ0 : Θ 0 = 0 := by simp only [Θ, hP0, hQ0, map_zero, add_zero]
  let ψ : HolGerm (ComplexModel (PX'.dim + PY.dim)) →+* B :=
    PB.π.comp (compAlgHom Θ hΘ hΘ0).toRingHom
  have hα : ∀ c, ψ (tangentPullback PX'.dim PY.dim c) = p (PX'.π c) := by
    intro c
    change PB.π (compAlgHom _ _ _ (compAlgHom _ _ _ c)) = _
    rw [compAlgHom_compAlgHom _ _ _ _ _ _ P hP hP0 (fun z => by
      simp only [Θ, map_add, tangentProjection_tangentInclusion,
        tangentProjection_actualJointNormalInclusion, add_zero]), hPl]
  have hN : ∀ g, ψ (jointNormalPullback PX'.dim PY.dim g) = q (PY.π g) := by
    intro g
    change PB.π (compAlgHom _ _ _ (compAlgHom _ _ _ g)) = _
    rw [compAlgHom_compAlgHom _ _ _ _ _ _ Q hQ hQ0 (fun z => by
      simp only [Θ, map_add, actualJointNormalProjection_tangent,
        actualJointNormalProjection_inclusion, zero_add]), hQl]
  have hβ : ∀ g, ψ (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0 g) = q (T g) := by
    let _ : Algebra ℂ B := κB.toAlgebra
    have := PB.isNoetherianRing
    have : IsLocalHom (compAlgHom Θ hΘ hΘ0).toRingHom := isLocalHom_compAlgHom _ _ _
    have := isLocalHom_jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0
    have : IsLocalHom (compAlgHom (graphMap F) (graphMap_holomorphic F hF)
      (graphMap_zero F hF0)).toRingHom := isLocalHom_compAlgHom _ _ _
    let L : HolGerm (ComplexModel (PX.dim + PY.dim)) →ₐ[ℂ] B :=
      { toRingHom := ψ.comp (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0).toRingHom
        commutes' := fun c => by
          change PB.π (compAlgHom _ _ _ (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0
            (algebraMap ℂ _ c))) = κB c
          rw [AlgHom.commutes, AlgHom.commutes, PB.const] }
    let R : HolGerm (ComplexModel (PX.dim + PY.dim)) →ₐ[ℂ] B :=
      { toRingHom := q.comp T
        commutes' := fun c => by
          change q (T (algebraMap ℂ _ c)) = κB c
          rw [hT, graphHom_const, hq] }
    have : IsLocalHom L.toRingHom := by
      change IsLocalHom (ψ.comp (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0).toRingHom)
      infer_instance
    have : IsLocalHom R.toRingHom := by
      change IsLocalHom (q.comp (PY.π.comp (compAlgHom (graphMap F) (graphMap_holomorphic F hF)
        (graphMap_zero F hF0)).toRingHom))
      infer_instance
    have hLR : L = R := by
      apply local_algHom_ext_coordinates
      intro j
      change ψ (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0 (coordinateGerm j)) =
        q (T (coordinateGerm j))
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [coordinateGerm_castAdd, jointBasePullback_tangentPullback, hα, ← hφl, hsq, hT,
          graphHom_tangentPullback, ← hFl]
      · rw [coordinateGerm_natAdd, jointBasePullback_jointNormalPullback, hN, hT,
          graphHom_jointNormalPullback]
    intro g
    exact congrArg (fun φ' : HolGerm (ComplexModel (PX.dim + PY.dim)) →ₐ[ℂ] B => φ' g) hLR
  -- (RR) in chart form
  have hRRc : Ideal.map (Ideal.Quotient.mk q0)
      (Ideal.map (compAlgHom φ hφ hφ0).toRingHom (canonicalFlattenerIdeal PX.dim PY.dim Ik)) =
        Ideal.span {Ideal.Quotient.mk q0 a0} := by
    have hkey : Ideal.map (eX' : _ →+* AX') (Ideal.map (Ideal.Quotient.mk q0)
        (Ideal.map (compAlgHom φ hφ hφ0).toRingHom (canonicalFlattenerIdeal PX.dim PY.dim Ik))) =
        Ideal.map (eX' : _ →+* AX') (Ideal.span {Ideal.Quotient.mk q0 a0}) := by
      rw [Ideal.map_map, heX', Ideal.map_map, Ideal.map_span, Set.image_singleton]
      have hc : PX'.π.comp (compAlgHom φ hφ hφ0).toRingHom = σ.comp PX.π :=
        RingHom.ext fun g => (hφl g).symm
      rw [hc, ← Ideal.map_map, ← hIeq, hRR]
      rfl
    have h1 := congrArg (fun J => Ideal.map
      (eX'.symm : AX' →+* (HolGerm (ComplexModel PX'.dim) ⧸ q0)) J) hkey
    simpa only [Ideal.map_of_equiv] using h1
  have hreg0 : IsRegular (Ideal.Quotient.mk q0 a0) := isRegular_of_map eX' ha
  have hne0 : Ideal.Quotient.mk q0 a0 ≠ 0 := by
    intro h0
    have : PX'.π a0 = 0 := by
      change eX' (Ideal.Quotient.mk q0 a0) = 0
      rw [h0, map_zero]
    exact ha.ne_zero this
  have hψ : ∀ r ∈ Ideal.map (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0).toRingHom Ik ⊔
      Ideal.map (tangentPullback PX'.dim PY.dim).toRingHom q0, ψ r = 0 := by
    intro r hr
    have hle : Ideal.map (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0).toRingHom Ik ⊔
        Ideal.map (tangentPullback PX'.dim PY.dim).toRingHom q0 ≤ RingHom.ker ψ := by
      refine sup_le (Ideal.map_le_iff_le_comap.mpr fun g hg => ?_)
        (Ideal.map_le_iff_le_comap.mpr fun g hg => ?_)
      · change ψ (jointBasePullback PX.dim PX'.dim PY.dim φ hφ hφ0 g) = 0
        rw [hβ, RingHom.mem_ker.mp hg, map_zero]
      · change ψ (tangentPullback PX'.dim PY.dim g) = 0
        rw [hα, RingHom.mem_ker.mp hg, map_zero]
    exact hle hr
  obtain ⟨h, hh, hqh⟩ := exists_fibre_decrease_of_presentation PX.dim PY.dim PX'.dim Ik φ hφ hφ0
    q0 a0 hne0 hreg0 hRRc eA q (Ideal.map p (IsLocalRing.maximalIdeal AX')) ψ hψ
    (by rw [hα]; exact hpa) (fun g => (hβ g).trans (congrArg q (heA g).symm))
    (fun c hc => by rw [hα]; exact Ideal.mem_map_of_mem p (PX'.map_mem_maximalIdeal hc))
  refine ⟨h, ?_, hqh⟩
  have hc : eA.toRingHom.comp ((Ideal.Quotient.mk Ik).comp
      (tangentPullback PX.dim PY.dim).toRingHom) = u.comp PX.π :=
    RingHom.ext fun g => (graphHom_tangentPullback PY F hF hF0 g).trans (hFl g).symm
  rwa [hc, ← Ideal.map_map, PX.map_maximalIdeal] at hh

end Square

end

end Hironaka.HironakaG10ChowAnalyticSquare
