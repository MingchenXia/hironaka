import Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
import Hironaka.Resolution.HironakaG10ChowTrackedRounds
import Hironaka.Resolution.HironakaG10ChowArtinReesCentre

/-!
# Leaving a tracked flattener, and the rounds that give frequent decrease (Phase C, start)

Hironaka 1975, Lemma 4.6.1 (printed pp. 544–545) and its use of permissibility (Def. 4.4.3 (3),
p. 537), Lemma 3.2 (p. 531) and Th. 2.4/2.5 (pp. 526, 529).  Lane G10H's Phase C plan
(`work/hironaka-resume-20261111/G10H/HIRONAKA75-GLOBAL-STEP.md` §§2.3, 3.1, 4).

* `germFlattener`, `isGermFlattenerAt_germFlattener`, `eq_germFlattener` — **whole-fibre flatteners
  exist at every point** (the sum of the pointed flatteners; no compactness needed), and are unique;
* `PrincipalPullbackAt` — the condition at a point where a branch leaves a tracked flattener: the
  flattener pulls back to a principal ideal `(g)`, `g` regular, `p^♯ g` regular on the strict
  transform;
* `exists_fibre_decrease_of_principal`, `stepFibreDecreasesAt_of_principalPullback` — Lemma 4.6.1's
  decrease at such a point, for any commutative square / any flattening sequence (generalizes M6);
* `principalPullbackAt_of_sumCentre` — **at a step with centre `I_S^β + I_Z` (`β ≥` an Artin–Rees
  number, `I_Z` the flattener stalk), every point off the strict transform of `Z` satisfies the
  leaving condition** (Lemma 3.2, Case 1; `g` = the exceptional generator);
* `frequentDecrease_of_rounds` — **`hfreq` from rounds** (M3): start covers the non-flat locus,
  leaving points satisfy `PrincipalPullbackAt`, at the end no non-flat point is tracked;
* `RoundData`, `exists_flattening_of_roundData` — the conclusion of `HironakaFlattening` from a
  centre machine with such rounds, closed non-flat images and coherent fibre kernels.  The existence
  of `RoundData` is the content of Hironaka's Theorems `I_n`/`II_n` (target, not assumed here).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds

open Hironaka Hironaka
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaG10ChowFibreAlgebra HironakaG10ChowAnalyticSquare HironakaG10ChowFibreTorsionWitness
  SourceReducedComplexSpace HironakaG10ChowOneStepStrictTransform HironakaG10ChowStrictTorsionFree
  HironakaG10ChowProductCentre HironakaG10ChowFlatteningDriver HironakaG10ChowFibreChain
  HironakaG10ChowFlattenerDecrease HironakaG10ChowStrictTransformCalculus
  HironakaG10ChowCompactBranch HironakaG10ChowTrackedRounds HironakaG10ChowArtinReesCentre
  HironakaG10ChowFlatteningReduction HironakaG10ChowTowerDomination
  HironakaG10ChowFlatBimeromorphicIso HironakaG10PNIdealFamily

noncomputable section

variable {X Y X' Y' : SourceReducedComplexSpace}

/-! ### Whole-fibre flatteners exist at every point -/

/-- The whole-fibre flattener of `f` at `x`: the sum of the pointed flatteners over the fibre. -/
def germFlattener (f : Y ⟶ X) (x : X.obj.left) : Ideal (X.obj.left.presheaf.stalk x) :=
  ⨆ k : {y : Y.obj.left // f.hom.left.base y = x},
    Classical.choose (exists_isPointFlattenerAt f x k.1 k.2)

/-- **Whole-fibre flatteners exist at every point** (Hironaka (1.14.2), HLT Th. 1′). -/
theorem isGermFlattenerAt_germFlattener (f : Y ⟶ X) (x : X.obj.left) :
    IsGermFlattenerAt f x (germFlattener f x) := by
  intro J
  rw [germFlattener, iSup_le_iff]
  exact ⟨fun H k => (Classical.choose_spec (exists_isPointFlattenerAt f x k.1 k.2) J).mp
      (H k.1 k.2),
    fun H y h => (Classical.choose_spec (exists_isPointFlattenerAt f x y h) J).mpr (H ⟨y, h⟩)⟩

theorem eq_germFlattener (f : Y ⟶ X) (x : X.obj.left) (I : Ideal (X.obj.left.presheaf.stalk x))
    (hI : IsGermFlattenerAt f x I) : I = germFlattener f x :=
  pointFlattener_unique _ _ _ hI (isGermFlattenerAt_germFlattener f x)

/-! ### The leaving condition and the decrease at leaving points -/

/-- **The leaving condition** at `x'` for a square over `σ` with strict transform `p` (Hironaka,
Lemma 4.6.1 with Def. 4.4.3 (3)): the whole-fibre flattener at `σ x'` pulls back to `(g)` with `g`
regular, and `p^♯ g` is regular at every point of `Y'` over `x'`. -/
def PrincipalPullbackAt (f : Y ⟶ X) (σ : X' ⟶ X) (p : Y' ⟶ X') (x' : X'.obj.left) : Prop :=
  ∃ g : X'.obj.left.presheaf.stalk x', IsRegular g ∧
    Ideal.map (σ.hom.left.stalkMap x').hom (germFlattener f (σ.hom.left.base x')) = Ideal.span {g} ∧
      ∀ (y' : Y'.obj.left) (hp : p.hom.left.base y' = x'), IsRegular (fibreStalkMap p x' y' hp g)

/-- **Decrease at a leaving point** (Hironaka Lemma 4.6.1 via (2.4.3), Th. 2.5; Rydh L. 1.18). -/
theorem exists_fibre_decrease_of_principal (f : Y ⟶ X) (σ : X' ⟶ X) (p : Y' ⟶ X') (q : Y' ⟶ Y)
    (hsq : p ≫ σ = q ≫ f) (x' : X'.obj.left) (hx' : PrincipalPullbackAt f σ p x') :
    ∃ y : Y.obj.left, f.hom.left.base y = σ.hom.left.base x' ∧
      ∀ y' : Y'.obj.left, q.hom.left.base y' = y → p.hom.left.base y' = x' →
        ∃ h : Y.obj.left.presheaf.stalk (q.hom.left.base y'),
          h ∉ fibreIdealAt f (q.hom.left.base y') ∧
            (q.hom.left.stalkMap y').hom h ∈ fibreIdealAt p y' := by
  obtain ⟨g, hg, hIg, hpg⟩ := hx'
  choose Iy hIy using fun k : {y : Y.obj.left // f.hom.left.base y = σ.hom.left.base x'} =>
    exists_isPointFlattenerAt f _ k.1 k.2
  rw [eq_iSup_of_isGermFlattenerAt f _ _ (isGermFlattenerAt_germFlattener f _) Iy hIy] at hIg
  obtain ⟨⟨y, hy⟩, hk⟩ := exists_map_eq_span_of_iSup _ Iy g hg hIg
  exact ⟨y, hy, fun y' hq hp => exists_fibre_decrease_of_pointFlattener f σ p q hsq y' x' hp y hq
    hy _ (hIy ⟨y, hy⟩) g hg hk (hpg y' hp)⟩

/-- The leaving condition for round `n` of a flattening sequence. -/
abbrev PrincipalPullback (F : FlatteningSequence) (n : ℕ) (x' : (F.X (n + 1)).obj.left) : Prop :=
  PrincipalPullbackAt (F.f n) (F.σ n) (F.f (n + 1)) x'

theorem stepFibreDecreasesAt_of_principalPullback (F : FlatteningSequence) (n : ℕ)
    (x' : (F.X (n + 1)).obj.left) (hx' : PrincipalPullback F n x') :
    HironakaG10ChowSequenceFibreChain.StepFibreDecreasesAt F n x' :=
  exists_fibre_decrease_of_principal (F.f n) (F.σ n) (F.f (n + 1)) (F.q n)
    (F.data n).strict.comm.symm x' hx'

/-! ### Lemma 3.2, Case 1: leaving points of a sum centre -/

section SumCentre

variable (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
  (f : Y ⟶ X)

/-- **Leaving points of a sum centre** (Hironaka Lemma 3.2 with Lemma 4.5.4, printed pp. 531, 542):
if the centre stalk at `σ x'` is `I_S^β + I_Z` with `β ≥ α`, `α` an Artin–Rees number of
`(I_Z, I_S)`, and `I_Z` is the flattener stalk, then at a point `x'` off the strict transform of
`V(I_Z)` (`strictIdeal = ⊤`) the leaving condition holds, with `g` the exceptional generator. -/
theorem principalPullbackAt_of_sumCentre
    (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (IZ IS : Ideal (X.obj.left.presheaf.stalk ((stepProj B b hDense).hom.left.base x')))
    (α β : ℕ) (hαβ : α ≤ β) (hAR : ∀ m, α ≤ m → IZ ⊓ IS ^ m ≤ IS ^ (m - α) * (IZ ⊓ IS ^ α))
    (hB : LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
      ((stepProj B b hDense).hom.left.base x')) = IS ^ β ⊔ IZ)
    (hIZ : IZ = germFlattener f ((stepProj B b hDense).hom.left.base x'))
    (G : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.stalk x')
    (hG : IsRegular G)
    (hD : Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom (IS ^ β ⊔ IZ) = Ideal.span {G})
    (hleave : strictIdeal ((stepProj B b hDense).hom.left.stalkMap x').hom IZ (IS ^ β ⊔ IZ) G = ⊤) :
    PrincipalPullbackAt f (stepProj B b hDense) (strictP B b hDense f) x' := by
  have hZ : Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom IZ = Ideal.span {G} :=
    (strictIdeal_eq_top_iff _ IZ IS α β hαβ hAR G hG hD).mp hleave
  refine ⟨G, hG, hIZ ▸ hZ, fun y' hp => ?_⟩
  have hcentre : nativePulledIdealStalkIdeal (stepProj B b hDense).hom.left B b x' =
      Ideal.span {G} :=
    (congrArg (Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom) hB).trans hD
  have ha' : nativePulledIdealStalkIdeal (stepProj B b hDense).hom.left B b
      ((strictP B b hDense f).hom.left.base y') =
        Ideal.span {(eqToHom (congrArg (OriginalFiniteIdealBlowup.sourceObject B b
          hDense).obj.left.presheaf.stalk hp.symm)).hom G} := by
    rw [nativePulledIdealStalkIdeal_eqToHom _ B b hp.symm, hcentre, Ideal.map_span,
      Set.image_singleton]
  exact (strictP_generator_regular B b f hDense y' _ ha').2

end SumCentre

/-! ### Rounds -/

/-- **Frequent decrease from rounds** (Hironaka, iteration of Theorem `II_n`, pp. 544–546, with
module M3): if the rounds `[r k, r (k+1))` carry tracked sets `Tr k n` covering the non-flat locus at
their start, every leaving point satisfies the leaving condition, and at the end of a round no
non-flat point is tracked, then the fibre decreases infinitely often along every branch. -/
theorem frequentDecrease_of_rounds (F : FlatteningSequence) (r : ℕ → ℕ)
    (hr : ∀ k, r k < r (k + 1)) (Tr : ℕ → ∀ n, Set (F.X n).obj.left)
    (hstart : ∀ k, F.nonflatImage (r k) ⊆ Tr k (r k))
    (hleave : ∀ k n, r k ≤ n → n < r (k + 1) → ∀ x' ∈ F.nonflatImage (n + 1),
      (F.σ n).hom.left.base x' ∈ Tr k n → x' ∉ Tr k (n + 1) → PrincipalPullback F n x')
    (hend : ∀ k, F.nonflatImage (r (k + 1)) ∩ Tr k (r (k + 1)) = ∅) :
    ∀ z : ∀ n, (F.X n).obj.left,
      IsBranch (fun n => (F.σ n).hom.left.base) F.nonflatImage z →
        ∀ N, ∃ m, N ≤ m ∧ HironakaG10ChowSequenceFibreChain.StepFibreDecreasesAt F m (z (m + 1)) :=
  fun z hz => frequently_of_trackedRounds (fun n => (F.σ n).hom.left.base) F.nonflatImage
    (fun n x' => HironakaG10ChowSequenceFibreChain.StepFibreDecreasesAt F n x') r hr Tr hstart
    (fun k n h1 h2 x' hx h3 h4 =>
      stepFibreDecreasesAt_of_principalPullback F n x' (hleave k n h1 h2 x' hx h3 h4))
    hend z hz

open HironakaG10ChowCentreMachine

/-- **Round data** for a family `s₀.f` (the output of Hironaka's Theorems `I_n`/`II_n` for a compact
base, Lemma 4.6.1): a centre machine, its rounds, and tracked sets with the start, leaving and end
properties. -/
structure RoundData (s₀ : Stage) (hf : IsProperMap s₀.f.hom.left.base) where
  M : CentreMachine
  d₀ : M.St s₀
  r : ℕ → ℕ
  hr : ∀ k, r k < r (k + 1)
  Tr : ℕ → ∀ n, Set ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left
  start : ∀ k, (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r k) ⊆ Tr k (r k)
  leave : ∀ k n, r k ≤ n → n < r (k + 1) →
    ∀ x' ∈ (toFlatteningSequence M s₀ d₀ hf).nonflatImage (n + 1),
      ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base x' ∈ Tr k n → x' ∉ Tr k (n + 1) →
        PrincipalPullback (toFlatteningSequence M s₀ d₀ hf) n x'
  finish : ∀ k, (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1)) ∩ Tr k (r (k + 1)) = ∅

/-- **Flattening from round data**: the conclusion of `HironakaFlattening` for `s₀.f` (compact base,
proper `f`) from round data, closed non-flat images and coherent fibre kernels of its run. -/
theorem exists_flattening_of_roundData (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base) (R : RoundData s₀ hf)
    (hclosed : ∀ n, IsClosed ((toFlatteningSequence R.M s₀ R.d₀ hf).nonflatImage n))
    (hfg : ∀ (z : ∀ n, ((toFlatteningSequence R.M s₀ R.d₀ hf).X n).obj.left) n,
      IsLocallyFinitelyGenerated ((toFlatteningSequence R.M s₀ R.d₀ hf).Y 0).obj.left
        (HironakaG10ChowSequenceFibreChain.fibreKernel (toFlatteningSequence R.M s₀ R.d₀ hf) z n)) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  exists_flattening_of_machine' R.M s₀ R.d₀ hX hf hclosed hfg
    (frequentDecrease_of_rounds _ R.r R.hr R.Tr R.start R.leave R.finish)

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
