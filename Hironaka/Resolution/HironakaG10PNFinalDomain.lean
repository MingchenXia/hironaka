import Hironaka.Resolution.HironakaG10PNExtensionInduction
import Hironaka.Resolution.HironakaNativeIrreducibleSupportContinuation
import Hironaka.Resolution.HironakaSimultaneousPrimeSupportNeighborhood

/-! The final common domain of the prime targets and their continuation on it (lane G10P, run 0080;
the adapter `G10.PN.6.342_input_adapter` and the per-target continuation of `G10.PN.7` on the
selected domain).  Blueprint: `hironaka-g10-pn-final-domain.tex`.

Given finitely many prime-target models `B j` (each a `NativePrimeAllOpenCokernelData` at the same
point `p`, for a prime `P j` of the ambient stalk) and ONE original open `Ω₀ ∋ p` inside every old
domain, the whole vanishing stalk ideal of the support of `B j` on `Ω₀` at `p` is prime (derived from
the models' own generator, kernel and readback data).  The accepted geometry module
`HironakaSimultaneousPrimeSupportNeighborhood` (342) then selects ONE common open `V ⊆ Ω₀`, `p ∈ V`, on
which every support is the closure of a single connected regular component; its image in the
coordinate space is the final domain.  On `V` every support is irreducible (transported along the
genuine biholomorphism `originalImageCarrierIso`), so the accepted fixed-domain continuation
`HironakaNativeIrreducibleSupportContinuation.hom_eq_zero_of_stalk_eq_zero` applies to the support
module, and through the models' own support isomorphism to the prime target of `B j` on `V`: every map
from a finite-type source with zero stalk at `p` is zero.  No further shrinking after 342, no
continuation certificate, every repeated index kept.  Everything is stated generically in the models
(no fixed `F`). -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10PNFinalDomain

open Hironaka.HolomorphicIdealSheaves HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaChowNativePrimeSupportContinuation HironakaSingularModuleSheafStalk
  HironakaChowNativeModuleStalkExact HironakaNativeCanonicalSupportRestriction
  HironakaNativeCyclicCokernelRestriction HironakaG10PNLayerStep HironakaG10PNExtensionInduction

noncomputable section

variable {n : ℕ}

/-! ### Irreducibility along a biholomorphism -/

/-- Analytic irreducibility is invariant under biholomorphisms. -/
theorem isComplexAnalyticallyIrreducible_preimage_diffeomorph
    {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y) {A : Set Y}
    (hA : IsComplexAnalyticallyIrreducible (n := n) A) :
    IsComplexAnalyticallyIrreducible (n := n) (e ⁻¹' A) := by
  obtain ⟨hAa, ⟨y, hy⟩, hirr⟩ := hA
  refine ⟨AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage e.contMDiff hAa,
    ⟨e.symm y, by simpa using hy⟩, ?_⟩
  intro B C hB hC hBA hCA hABC
  have hB' := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage e.symm.contMDiff hB
  have hC' := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage e.symm.contMDiff hC
  have hBA' : e.symm ⁻¹' B ⊆ A := fun z hz => by simpa using hBA hz
  have hCA' : e.symm ⁻¹' C ⊆ A := fun z hz => by simpa using hCA hz
  have hABC' : A = e.symm ⁻¹' B ∪ e.symm ⁻¹' C := by
    ext z
    constructor
    · intro hz
      have h : e.symm z ∈ e ⁻¹' A := by simpa using hz
      rw [hABC] at h
      exact h
    · rintro (hz | hz)
      · exact hBA' hz
      · exact hCA' hz
  rcases hirr _ _ hB' hC' hBA' hCA' hABC' with h | h
  · left
    rw [h]
    ext x
    simp
  · right
    rw [h]
    ext x
    simp

/-! ### Transport along an equality of original opens -/

theorem irreducible_of_eq_open {E Z : Opens (ComplexModel n)} (h : E = Z) (S : Set E)
    (T : Set Z) (hST : ∀ (x : E) (z : Z), x.val = z.val → (x ∈ S ↔ z ∈ T))
    (hT : IsComplexAnalyticallyIrreducible (n := n) T) :
    IsComplexAnalyticallyIrreducible (n := n) S := by
  subst h
  have hE : S = T := Set.ext fun x => hST x x rfl
  rw [hE]
  exact hT

theorem analytic_of_eq_open {E Z : Opens (ComplexModel n)} (h : E = Z) (S : Set E)
    (T : Set Z) (hST : ∀ (x : E) (z : Z), x.val = z.val → (x ∈ S ↔ z ∈ T))
    (hS : IsComplexAnalyticSubset (n := n) S) :
    IsComplexAnalyticSubset (n := n) T := by
  subst h
  have hE : S = T := Set.ext fun x => hST x x rfl
  rw [← hE]
  exact hS

theorem wholeIdeal_isPrime_of_eq_open {E Z : Opens (ComplexModel n)} (h : E = Z) (S : Set E)
    (T : Set Z) (hST : ∀ (x : E) (z : Z), x.val = z.val → (x ∈ S ↔ z ∈ T))
    (x : E) (z : Z) (hxz : x.val = z.val)
    (hP : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) S) x).IsPrime) :
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) z).IsPrime := by
  subst h
  have hE : S = T := Set.ext fun y => hST y y rfl
  subst hE
  have hx : x = z := Subtype.ext hxz
  subst hx
  exact hP

/-! ### Zero-stalk rigidity: isomorphisms, casts and the support module -/

theorem stalkLinearMap_eq_zero_of_map_eq_zero {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {G T : SheafOfModules.{0} (forgetRing R)} (g : G ⟶ T) (x : X)
    (h : (nativeStalkFunctor R x).map g = 0) : stalkLinearMap g.val x = 0 :=
  congrArg ModuleCat.Hom.hom h

theorem zeroStalkRigid_of_iso {Ω : Opens (ComplexModel n)} {x : Ω}
    {𝒮 : OriginalModules Ω → Prop} {T T' : OriginalModules Ω} (e : T ≅ T')
    (h : ZeroStalkRigid Ω x 𝒮 T') : ZeroStalkRigid Ω x 𝒮 T := by
  intro G hG g hg
  have h1 : g ≫ e.hom = 0 := h G hG (g ≫ e.hom) (by rw [Functor.map_comp, hg, zero_comp])
  exact (cancel_mono e.hom).mp (h1.trans zero_comp.symm)

theorem zeroStalkRigid_cast {W Z : Opens (ComplexModel n)} (h : W = Z) (T : OriginalModules W)
    (x : W) (z : Z) (hxz : x.val = z.val)
    (hT : ZeroStalkRigid W x (fun G => G.IsFiniteType) T) :
    ZeroStalkRigid Z z (fun G => G.IsFiniteType) (castOriginalModule h T) := by
  subst h
  have hx : x = z := Subtype.ext hxz
  subst hx
  exact hT

/-- **Continuation into the support module on a FIXED domain** (PN.7 consumer): if the support `S`
is irreducible on the original open `Ω`, the support module of `S` is zero-stalk rigid at every point
of `S` for the finite-type sources. -/
theorem zeroStalkRigid_primeSupportModule (Ω : Opens (ComplexModel n)) (S : Set Ω)
    (hS : IsComplexAnalyticallyIrreducible (n := n) S) (x : Ω) (hx : x ∈ S) :
    ZeroStalkRigid Ω x (fun G => G.IsFiniteType) (originalPrimeSupportModule Ω S) := by
  intro G hG g hg
  have := hG
  exact HironakaNativeIrreducibleSupportContinuation.hom_eq_zero_of_stalk_eq_zero Ω S hS x hx g
    (stalkLinearMap_eq_zero_of_map_eq_zero _ g x hg)

theorem nonempty_iso_of_comp {C : Type*} [Category C] {X Y Z : C} {f : X ⟶ Y} {e : Y ≅ Z}
    {g : X ⟶ Z} (_h : f ≫ e.hom = g) : Nonempty (Y ≅ Z) := ⟨e⟩

/-! ### The support of a prime model on an original open -/

/-- The support of the model `B` on an original open `Ω` inside its old domain. -/
def domainSupport {p : ComplexModel n} {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (B : NativePrimeAllOpenCokernelData p P) (Ω : Opens (ComplexModel n)) (hΩB : Ω ≤ B.old.U) :
    Set Ω :=
  {z | (⟨z.val, hΩB z.property⟩ : B.old.U) ∈ B.old.W}

theorem contMDiff_originalImageInclusion (U : Opens (ComplexModel n)) (D : Opens U) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (originalImageInclusion U D) :=
  (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_subtype_val

theorem image_support_iff {p : ComplexModel n} {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (B : NativePrimeAllOpenCokernelData p P) (Ω : Opens (ComplexModel n)) (hΩB : Ω ≤ B.old.U)
    (x : originalImageOpen B.old.U (inverseImageOpen B.old.U Ω)) (z : Ω) (hxz : x.val = z.val) :
    x ∈ (originalImageInclusion B.old.U (inverseImageOpen B.old.U Ω)) ⁻¹' B.old.W ↔
      z ∈ domainSupport B Ω hΩB := by
  have h : originalImageInclusion B.old.U (inverseImageOpen B.old.U Ω) x =
      (⟨z.val, hΩB z.property⟩ : B.old.U) := Subtype.ext hxz
  change originalImageInclusion B.old.U (inverseImageOpen B.old.U Ω) x ∈ B.old.W ↔ _
  rw [h]
  rfl

/-- The generator ideal of the old model at `p` is prime (it is the prime `P`, read through the
original restriction stalk isomorphism). -/
theorem generatorIdeal_isPrime_at {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)} (hP : P.IsPrime)
    (A : NativePrimePresentationData p P) :
    (originalGeneratorIdeal A.U A.g ⟨p, A.hpU⟩).IsPrime := by
  have heq : originalGeneratorIdeal A.U A.g ⟨p, A.hpU⟩ =
      Ideal.comap (originalRestrictionStalkEquiv A.U ⟨p, A.hpU⟩).symm.toRingHom P := by
    ext s
    have h2 := A.prime_at_p ((originalRestrictionStalkEquiv A.U ⟨p, A.hpU⟩).symm s)
    rw [RingEquiv.apply_symm_apply] at h2
    exact (A.kernel _ s).symm.trans h2
  rw [heq]
  exact Ideal.comap_isPrime _ _

/-- On the image of any `D ⊆ U_B`, the whole vanishing stalk ideal of the support at the point over
`p` is prime: the models' `whole` and `ideal_map` identify it with the old generator ideal. -/
theorem wholeIdeal_isPrime_on_image {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)} (hP : P.IsPrime)
    (B : NativePrimeAllOpenCokernelData p P) (D : Opens B.old.U)
    (b : originalImageOpen B.old.U D) (hb : b.val = p) :
    (actualWholeSheafStalkIdeal
      (vanishingIdeal (n := n) ((originalImageInclusion B.old.U D) ⁻¹' B.old.W)) b).IsPrime := by
  have h12 := ((B.all_opens D).whole b).symm.trans ((B.all_opens D).ideal_map b)
  have hinc : originalImageInclusion B.old.U D b = ⟨p, B.old.hpU⟩ := Subtype.ext hb
  have hP0 : (originalGeneratorIdeal B.old.U B.old.g
      (originalImageInclusion B.old.U D b)).IsPrime := by
    rw [hinc]
    exact generatorIdeal_isPrime_at hP B.old
  have hmap : (Ideal.map (actualOpenLiteralStalkEquiv (originalImageOpen B.old.U D) b).toRingHom
      (actualWholeSheafStalkIdeal
        (vanishingIdeal (n := n) ((originalImageInclusion B.old.U D) ⁻¹' B.old.W)) b)).IsPrime := by
    rw [h12]
    exact Ideal.map_isPrime_of_equiv (originalImageStalkRingEquiv B.old.U D b)
  have hc := Ideal.comap_isPrime
    (actualOpenLiteralStalkEquiv (originalImageOpen B.old.U D) b).toRingHom
    (Ideal.map (actualOpenLiteralStalkEquiv (originalImageOpen B.old.U D) b).toRingHom
      (actualWholeSheafStalkIdeal
        (vanishingIdeal (n := n) ((originalImageInclusion B.old.U D) ⁻¹' B.old.W)) b))
  rwa [Ideal.comap_map_of_bijective
    (actualOpenLiteralStalkEquiv (originalImageOpen B.old.U D) b).toRingHom
    (actualOpenLiteralStalkEquiv (originalImageOpen B.old.U D) b).bijective] at hc

/-- The support of `B` on `Ω` is analytic, contains `p`, and its whole vanishing stalk ideal at `p`
is prime. -/
theorem domainSupport_data {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)} (hP : P.IsPrime)
    (B : NativePrimeAllOpenCokernelData p P) (Ω : Opens (ComplexModel n)) (hΩB : Ω ≤ B.old.U)
    (hpΩ : p ∈ Ω) :
    IsComplexAnalyticSubset (n := n) (domainSupport B Ω hΩB) ∧
      (⟨p, hpΩ⟩ : Ω) ∈ domainSupport B Ω hΩB ∧
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (domainSupport B Ω hΩB))
        ⟨p, hpΩ⟩).IsPrime := by
  have he := original_image_inverseImage B.old.U Ω hΩB
  have hpE : p ∈ originalImageOpen B.old.U (inverseImageOpen B.old.U Ω) := by
    rw [he]
    exact hpΩ
  refine ⟨?_, B.old.mem, ?_⟩
  · exact analytic_of_eq_open he _ _ (image_support_iff B Ω hΩB)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
        (contMDiff_originalImageInclusion B.old.U (inverseImageOpen B.old.U Ω)) B.old.analytic)
  · exact wholeIdeal_isPrime_of_eq_open he _ _ (image_support_iff B Ω hΩB) ⟨p, hpE⟩ ⟨p, hpΩ⟩ rfl
      (wholeIdeal_isPrime_on_image hP B (inverseImageOpen B.old.U Ω) ⟨p, hpE⟩ rfl)

/-- **Per-target continuation on a fixed domain (PN.7 on `Ω`).**  If the support of `B` on `Ω` is
irreducible, the prime target of `B` on `Ω` is zero-stalk rigid at `p` for the finite-type sources. -/
theorem zeroStalkRigid_primeTargetOnDomain {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (B : NativePrimeAllOpenCokernelData p P) (Ω : Opens (ComplexModel n)) (hΩB : Ω ≤ B.old.U)
    (hpΩ : p ∈ Ω) (hS : IsComplexAnalyticallyIrreducible (n := n) (domainSupport B Ω hΩB)) :
    ZeroStalkRigid Ω ⟨p, hpΩ⟩ (fun G => G.IsFiniteType) (primeTargetOnDomain B Ω hΩB) := by
  have he := original_image_inverseImage B.old.U Ω hΩB
  have hpE : p ∈ originalImageOpen B.old.U (inverseImageOpen B.old.U Ω) := by
    rw [he]
    exact hpΩ
  have hSE := irreducible_of_eq_open he _ _ (image_support_iff B Ω hΩB) hS
  obtain ⟨e⟩ := nonempty_iso_of_comp (B.all_opens (inverseImageOpen B.old.U Ω)).quotient_support
  have hE : ZeroStalkRigid (originalImageOpen B.old.U (inverseImageOpen B.old.U Ω)) ⟨p, hpE⟩
      (fun G => G.IsFiniteType)
      (cokernel (originalRestrictedCyclicRelation B.old.U (inverseImageOpen B.old.U Ω) B.old.δ)) :=
    zeroStalkRigid_of_iso e (zeroStalkRigid_primeSupportModule _ _ hSE ⟨p, hpE⟩ B.old.mem)
  exact zeroStalkRigid_cast he _ ⟨p, hpE⟩ ⟨p, hpΩ⟩ rfl hE

/-! ### The final common domain (PN.6 adapter) -/

/-- **The final common domain (G10.PN.6 adapter with the continuation of G10.PN.7).**  For finitely
many prime models `B j` at `p` (repetitions allowed) and ONE original open `Ω₀ ∋ p` inside every old
domain, the accepted simultaneous prime-support neighbourhood selects ONE original open
`p ∈ V ⊆ Ω₀` on which every support is irreducible and every prime target is zero-stalk rigid at `p`
for the finite-type sources.  No open is chosen after `V`. -/
theorem exists_final_common_domain {p : ComplexModel n} {r : ℕ}
    {P : Fin r → Ideal (actualComplexStructureStalk (n := n) p)} (hP : ∀ j, (P j).IsPrime)
    (B : ∀ j, NativePrimeAllOpenCokernelData p (P j))
    (Ω₀ : Opens (ComplexModel n)) (hpΩ₀ : p ∈ Ω₀) (hΩ₀B : ∀ j, Ω₀ ≤ (B j).old.U) :
    ∃ (V : Opens (ComplexModel n)) (hpV : p ∈ V) (hVΩ₀ : V ≤ Ω₀),
      ∀ j : Fin r,
        IsComplexAnalyticallyIrreducible (n := n)
          (domainSupport (B j) V (hVΩ₀.trans (hΩ₀B j))) ∧
        ZeroStalkRigid V ⟨p, hpV⟩ (fun G => G.IsFiniteType)
          (primeTargetOnDomain (B j) V (hVΩ₀.trans (hΩ₀B j))) := by
  classical
  let p₀ : Ω₀ := ⟨p, hpΩ₀⟩
  let W : Fin r → Set Ω₀ := fun j => domainSupport (B j) Ω₀ (hΩ₀B j)
  have hdata := fun j => domainSupport_data (hP j) (B j) Ω₀ (hΩ₀B j) hpΩ₀
  obtain ⟨-, -, -, -, -, -, -, -, U', hpU', -, -, hfin⟩ :=
    HironakaSimultaneousPrimeSupportNeighborhood.exists_simultaneous_prime_support_neighborhood
      Ω₀ p₀ r W (fun j => (hdata j).1) (fun j => (hdata j).2.1) (fun j => (hdata j).2.2) ⊤ trivial
  let V : Opens (ComplexModel n) := originalImageOpen Ω₀ U'
  have hpV : p ∈ V := ⟨p₀, hpU', rfl⟩
  have hVΩ₀ : V ≤ Ω₀ := by
    rintro x ⟨u, -, rfl⟩
    exact u.property
  refine ⟨V, hpV, hVΩ₀, fun j => ?_⟩
  obtain ⟨-, -, -, -, hirr⟩ := hfin j
  have hS : IsComplexAnalyticallyIrreducible (n := n)
      (domainSupport (B j) V (hVΩ₀.trans (hΩ₀B j))) :=
    isComplexAnalyticallyIrreducible_preimage_diffeomorph (originalImageCarrierIso Ω₀ U').symm hirr
  exact ⟨hS, zeroStalkRigid_primeTargetOnDomain (B j) V _ hpV hS⟩

end

end Hironaka.HironakaG10PNFinalDomain
