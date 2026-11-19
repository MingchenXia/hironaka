import Hironaka.Resolution.HironakaG10PNDownwardLayers
import Hironaka.Resolution.HironakaG10PNRestrictionExact

/-! The downward chain of actual prime-kernel layers, restricted to ONE final original open
(lane G10P, run 0080; leaf `G10.PN.5.bottom_exact_restrict`).
Blueprint: `hironaka-g10-pn-bottom-restrict.tex`.

The finite downward induction of `HironakaG10PNDownwardLayers` performs all algebraic shrinks; the
zero bottom stalk gives an actual zero object on the bottom open `Ω₀`.  On EVERY original open
`Ω ⊆ Ω₀` the literal restriction `F|Ω` then carries the restricted chain: at every level the
restriction of the literal kernel inclusion and of the actual epimorphic lift form an exact pair
(limiting kernel fork and colimiting cokernel cofork), the quotient is the restriction of the
prime target of the SAME preselected `B_i` from the open of that level, and the bottom is an
actual zero object.  Repeated primes are repeated indices; `ℓ = 0` gives `IsZero (F|Ω)`.

As in `HironakaG10PNDownwardLayers`, every predicate and lemma that elaborates a sheaf-category
construction is generic (no selected series of the stalk of a fixed `F` in its context). -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaG10PNBottomRestrict

open HironakaChowNativeFreePartContinuation
  HironakaChowNativePrimeSupportContinuation HironakaSingularModuleSheafStalk
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeLocalOverStalkTransport
  HironakaChowNativeLocalOverFiniteDataTransport HironakaNativeCanonicalSupportRestriction
  HironakaNativeCyclicCokernelRestriction HironakaChowNativeModuleStalkExact
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaSingularLocallyFreeStalk HironakaNativeOriginalRestrictionComparison
  HironakaG10PNLayerStep HironakaG10PNDownwardLayers HironakaG10PNRestrictionExact

noncomputable section

variable {n : ℕ}

/-- ONE exact step of a filtration on the fixed original open `Ω`: an exact pair
`G' → G → Q` (limiting kernel fork, colimiting cokernel cofork) whose quotient is the restriction
to `Ω` of the prime target of `B` on some original open `W ⊇ Ω`, and the continuation holds for
the subobject `G'`. -/
def RestrictedStep {q : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) q)}
    (B : NativePrimeAllOpenCokernelData q P) (Ω : Opens (ComplexModel n))
    (G : OriginalModules Ω) (next : OriginalModules Ω → Prop) : Prop :=
  ∃ (G' Q : OriginalModules Ω) (ι : G' ⟶ G) (π : G ⟶ Q) (w : ι ≫ π = 0),
    Nonempty (IsLimit (KernelFork.ofι ι w)) ∧ Nonempty (IsColimit (CokernelCofork.ofπ π w)) ∧
    (∃ (W : Opens (ComplexModel n)) (hΩW : Ω ≤ W) (hWB : W ≤ B.old.U),
      Nonempty (Q ≅ (restrictTo W Ω hΩW).obj (primeTargetOnDomain B W hWB))) ∧
    next G'

/-- A restricted step transports along an isomorphism of the top object. -/
theorem restrictedStep_of_iso {q : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) q)}
    {B : NativePrimeAllOpenCokernelData q P} {Ω : Opens (ComplexModel n)}
    {G G₁ : OriginalModules Ω} (e : G ≅ G₁) {next : OriginalModules Ω → Prop}
    (h : RestrictedStep B Ω G next) : RestrictedStep B Ω G₁ next := by
  obtain ⟨G', Q, ι, π, w, ⟨hl⟩, ⟨hc⟩, hQ, hn⟩ := h
  refine ⟨G', Q, ι ≫ e.hom, e.inv ≫ π, by simp [w], ⟨?_⟩, ⟨?_⟩, hQ, hn⟩
  · exact KernelFork.isLimitOfIsLimitOfIff hl (e.inv ≫ π) e (fun _ φ => by simp)
  · exact CokernelCofork.isColimitOfIsColimitOfIff hc (ι ≫ e.hom) e.symm (fun _ φ => by simp)

/-- The kernel condition after restriction. -/
theorem restrictTo_kernel_condition (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W)
    {M N : OriginalModules W} (f : M ⟶ N) :
    (restrictTo W Ω h).map (kernel.ι f) ≫ (restrictTo W Ω h).map f = 0 :=
  ((restrictTo W Ω h).map_comp (kernel.ι f) f).symm.trans
    ((congrArg (restrictTo W Ω h).map (kernel.condition f)).trans ((restrictTo W Ω h).map_zero (kernel f) N))

set_option backward.isDefEq.respectTransparency.types false in
/-- The restricted step of one actual layer: on `W`, the literal kernel `K` of `q = L(b)` on the
image open `E` of `V`, with its colimiting cokernel cofork, restricts to every `Ω ⊆ E`; the top is
identified with the restriction of `T` from `W` by the nesting isomorphism. -/
theorem restrictedStep_of_layer {q : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) q)}
    (B : NativePrimeAllOpenCokernelData q P) (W : Opens (ComplexModel n)) (hWB : W ≤ B.old.U)
    (T : OriginalModules W) (V : Opens W)
    (b : T.over V ⟶ (primeTargetOnDomain B W hWB).over V)
    (hC : IsColimit (CokernelCofork.ofπ ((localOverTransport (originalSpace n) W V).map b)
      (kernel.condition ((localOverTransport (originalSpace n) W V).map b))))
    (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ originalImageOpen W V)
    (next : OriginalModules Ω → Prop)
    (hnext : next ((restrictTo (originalImageOpen W V) Ω hΩ).obj
      (kernel ((localOverTransport (originalSpace n) W V).map b)))) :
    RestrictedStep B Ω ((restrictTo W Ω (hΩ.trans (image_open_le W V))).obj T) next := by
  have hl := restrictToKernelForkIsLimit (originalImageOpen W V) Ω hΩ _
    (kernelIsKernel ((localOverTransport (originalSpace n) W V).map b))
  have hc := restrictToCokernelCoforkIsColimit (originalImageOpen W V) Ω hΩ _ hC
  have hbase : RestrictedStep B Ω ((restrictTo (originalImageOpen W V) Ω hΩ).obj
      ((localOverTransport (originalSpace n) W V).obj (T.over V))) next :=
    ⟨_, _, (restrictTo (originalImageOpen W V) Ω hΩ).map
        (kernel.ι ((localOverTransport (originalSpace n) W V).map b)),
      (restrictTo (originalImageOpen W V) Ω hΩ).map ((localOverTransport (originalSpace n) W V).map b),
      restrictTo_kernel_condition (originalImageOpen W V) Ω hΩ
        ((localOverTransport (originalSpace n) W V).map b), ⟨hl⟩, ⟨hc⟩,
      ⟨W, hΩ.trans (image_open_le W V), hWB,
        ⟨(restrictToNestedIso W Ω V hΩ).app (primeTargetOnDomain B W hWB)⟩⟩, hnext⟩
  exact restrictedStep_of_iso ((restrictToNestedIso W Ω V hΩ).app T) hbase

set_option backward.isDefEq.respectTransparency.types false in
/-- A zero actual local restriction stays zero on every smaller open. -/
theorem restricted_zero_of_bottom (W : Opens (ComplexModel n)) (T : OriginalModules W)
    (V : Opens W) (hZ : IsZero ((localOverTransport (originalSpace n) W V).obj (T.over V)))
    (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ originalImageOpen W V) :
    IsZero ((restrictTo W Ω (hΩ.trans (image_open_le W V))).obj T) :=
  ((restrictTo (originalImageOpen W V) Ω hΩ).map_isZero hZ).of_iso
    ((restrictToNestedIso W Ω V hΩ).app T).symm

/-- The restricted chain on the fixed open `Ω`, from level `k` down: at each positive level a
restricted step for the SAME preselected `B_i`, at level `0` an actual zero object. -/
def RestrictedChain {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (Ω : Opens (ComplexModel n)) :
    (k : ℕ) → k ≤ d.s.length → OriginalModules Ω → Prop
  | 0, _, G => IsZero G
  | k + 1, hk, G => RestrictedStep (B ⟨k, Nat.lt_of_succ_le hk⟩) Ω G
      (RestrictedChain d B Ω k (Nat.le_of_succ_le hk))

/-- The restricted chain transports along an isomorphism of the top object. -/
theorem restrictedChain_of_iso {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (Ω : Opens (ComplexModel n)) :
    ∀ (k : ℕ) (hk : k ≤ d.s.length) {G G₁ : OriginalModules Ω} (_e : G ≅ G₁),
      RestrictedChain d B Ω k hk G → RestrictedChain d B Ω k hk G₁
  | 0, _, _, _, e, h => IsZero.of_iso h e.symm
  | _ + 1, _, _, _, e, h => restrictedStep_of_iso e h

/-- Every state carrying the downward chain gives an open `Ω₀ ∋ p` inside its open such that the
literal restriction of its module to EVERY `Ω ⊆ Ω₀` carries the restricted chain. -/
theorem restrictedChain_of_downChain {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (D : Opens (ComplexModel n)) (hDB : ∀ j : Fin d.s.length, D ≤ (B j).old.U) :
    ∀ (k : ℕ) (hk : k ≤ d.s.length) (s : LayerState U p D M (d.s (seriesIndex d k hk))),
      DownChain d B D hDB k hk s →
      ∃ (Ω₀ : Opens (ComplexModel n)) (_hp : p.val ∈ Ω₀) (hΩ₀ : Ω₀ ≤ s.W),
        ∀ (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ Ω₀),
          RestrictedChain d B Ω k hk ((restrictTo s.W Ω (hΩ.trans hΩ₀)).obj s.T)
  | 0, hk, s, h => by
    obtain ⟨V, hpV, hZ⟩ := h
    exact ⟨originalImageOpen s.W V, ⟨⟨p.val, s.mem⟩, hpV, rfl⟩, image_open_le s.W V,
      fun Ω hΩ => restricted_zero_of_bottom s.W s.T V hZ Ω hΩ⟩
  | k + 1, hk, s, h => by
    obtain ⟨_, _, _, _, _, _, _, V, _, b, _, _, hstep, hK, η₀, _, _, hnext⟩ := h
    obtain ⟨_, _, _, _, _, hC, _⟩ := hstep
    obtain ⟨Ω₀, hp, hΩ₀, hall⟩ := restrictedChain_of_downChain d B D hDB k
      (Nat.le_of_succ_le hk) _ hnext
    exact ⟨Ω₀, hp, hΩ₀.trans (image_open_le s.W V), fun Ω hΩ =>
      restrictedStep_of_layer (B ⟨k, Nat.lt_of_succ_le hk⟩) s.W
        (s.le.trans (hDB ⟨k, Nat.lt_of_succ_le hk⟩)) s.T V b hC Ω (hΩ.trans hΩ₀) _
        (hall Ω hΩ)⟩

/-- **Bottom exact restriction (G10.PN.5).**  From ONLY the ordinary original finitely presented
module `F` on `U` and a point `p`: the selected series `d`, ALL prime targets `B_i`, the common
domain `D` (with `p ∈ D ⊆ U`) and an original open `Ω₀ ∋ p` inside `D` such that, on EVERY
original open `Ω ⊆ Ω₀`, the literal restriction `F|Ω` carries the restricted chain: exact pairs
at every level with quotients the restrictions of the prime targets of the SAME `B_i`, ending in
an actual zero object. -/
theorem exists_original_bottom_exact_restrict
    (n : ℕ) (U : Opens (ComplexModel n)) (F : OriginalModules U)
    [hF : F.IsFinitePresentation] (p : U) :
    ∃ (d : SelectedPrimeSeries (OriginalRingStalk U p)
        ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F))
      (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
        (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
      (D : Opens (ComplexModel n)) (_hpD : p.val ∈ D) (hDU : D ≤ U)
      (_hDB : ∀ j : Fin d.s.length, D ≤ (B j).old.U)
      (Ω₀ : Opens (ComplexModel n)) (_hpΩ₀ : p.val ∈ Ω₀) (hΩ₀D : Ω₀ ≤ D),
      ∀ (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ Ω₀),
        RestrictedChain d B Ω d.s.length le_rfl
          ((restrictTo U Ω (hΩ.trans (hΩ₀D.trans hDU))).obj F) := by
  obtain ⟨d, B, D, hpD, hDU, hDB, hEq, hchain⟩ := exists_original_downward_prime_layers n U F p
  obtain ⟨Ω₀, hpΩ₀, hΩ₀, hall⟩ := restrictedChain_of_downChain d B D hDB d.s.length le_rfl _ hchain
  refine ⟨d, B, D, hpD, hDU, hDB, Ω₀, hpΩ₀, hΩ₀.trans (source_image_le_domain U D), ?_⟩
  intro Ω hΩ
  exact restrictedChain_of_iso d B Ω d.s.length le_rfl
    ((restrictToNestedIso U Ω (inverseImageOpen U D) (hΩ.trans hΩ₀)).app F) (hall Ω hΩ)

end

end Hironaka.HironakaG10PNBottomRestrict
