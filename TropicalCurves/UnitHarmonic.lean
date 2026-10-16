import TropicalCurves.UnitJacobian
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Harmonic interpretation of the unit-length chain Jacobian

For a finite graph with every edge of length one, harmonic one-forms are real
edge functions with zero signed boundary. Integrating a real chain against
these forms has kernel exactly the real gradient space and is surjective
onto the dual of the harmonic space. Thus the chain-coordinate covering
space used in `UnitJacobian` is canonically the harmonic dual, rather than
being identified with it by an additional assumption.
-/

noncomputable section

namespace TropicalCurves
namespace UnitHarmonic

open FiniteStability UnitJacobian

section FinitePairing

variable {A : Type*} [Fintype A]

/-- The ordinary unit-length pairing on finite real coordinate spaces. -/
def dotDual : (A → ℝ) →ₗ[ℝ] Module.Dual ℝ (A → ℝ) where
  toFun x :=
    { toFun := fun y => ∑ a, x a * y a
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r y
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring }
  map_add' := by
    intro x y
    ext z
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    ext y
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem dotDual_apply (x y : A → ℝ) : dotDual x y = ∑ a, x a * y a := rfl

theorem dotDual_injective : Function.Injective (dotDual (A := A)) := by
  classical
  intro x y h
  ext a
  have he := LinearMap.congr_fun h (Pi.single a 1)
  simpa [dotDual_apply, Pi.single_apply] using he

theorem dotDual_surjective : Function.Surjective (dotDual (A := A)) := by
  classical
  intro ℓ
  refine ⟨fun a => ℓ (Pi.single a 1), ?_⟩
  apply LinearMap.ext
  intro y
  have hy : (∑ a, y a • (Pi.single a (1 : ℝ) : A → ℝ)) = y := by
    ext a
    simp [Pi.single_apply]
  calc
    (∑ a, ℓ (Pi.single a 1) * y a) =
        ∑ a, ℓ (y a • (Pi.single a 1 : A → ℝ)) := by simp [mul_comm]
    _ = ℓ (∑ a, y a • (Pi.single a 1 : A → ℝ)) := by rw [map_sum]
    _ = ℓ y := congrArg ℓ hy

/-- Every functional on a finite real coordinate space is given by its
ordinary dot product with a unique vector. -/
def dotDualEquiv : (A → ℝ) ≃ₗ[ℝ] Module.Dual ℝ (A → ℝ) :=
  LinearEquiv.ofBijective dotDual ⟨dotDual_injective, dotDual_surjective⟩

end FinitePairing

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Harmonic one-forms satisfy conservation at every graph vertex. -/
def harmonics (G : EndpointGraph V E) : Submodule ℝ (E → ℝ) :=
  LinearMap.ker (realBoundary G)

/-- The real dual space in the harmonic definition of the tropical Jacobian. -/
abbrev HarmonicDual (G : EndpointGraph V E) := Module.Dual ℝ (harmonics G)

/-- Integration of an edge chain against harmonic one-forms. -/
def integration (G : EndpointGraph V E) : (E → ℝ) →ₗ[ℝ] HarmonicDual G :=
  (harmonics G).dualRestrict.comp dotDual

omit [Fintype V] in
@[simp] theorem integration_apply (G : EndpointGraph V E) (x : E → ℝ)
    (h : harmonics G) : integration G x h = ∑ e, x e * (h : E → ℝ) e := rfl

/-- Boundary and gradient are adjoint under the finite-coordinate duality. -/
theorem dual_boundary_dot (G : EndpointGraph V E) (φ : V → ℝ) :
    (realBoundary G).dualMap (dotDual φ) = dotDual (gradient G φ) := by
  ext x
  change (∑ v, φ v * realBoundary G x v) = ∑ e, gradient G φ e * x e
  simpa only [mul_comm] using boundary_gradient_pairing G x φ

/-- A real chain annihilates all harmonic forms precisely when it is a
gradient. This is the finite graph's exact annihilator statement. -/
theorem integration_eq_zero_iff (G : EndpointGraph V E) (x : E → ℝ) :
    integration G x = 0 ↔ ∃ φ : V → ℝ, x = gradient G φ := by
  constructor
  · intro hx
    have hmem : dotDual x ∈ (LinearMap.ker (realBoundary G)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro h hh
      have he := LinearMap.congr_fun hx ⟨h, hh⟩
      exact he
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨ψ, hψ⟩ := hmem
    obtain ⟨φ, rfl⟩ := dotDual_surjective ψ
    refine ⟨φ, dotDual_injective ?_⟩
    rw [← dual_boundary_dot]
    exact hψ.symm
  · rintro ⟨φ, rfl⟩
    ext h
    exact gradient_pairing_cycle_zero G φ h h.property

omit [Fintype V] in
/-- A harmonic chain cannot have all of its harmonic integrals vanish unless
it is zero: evaluate against the chain itself and use positivity. -/
theorem integration_harmonic_eq_zero_iff (G : EndpointGraph V E) (x : E → ℝ)
    (hx : realBoundary G x = 0) : integration G x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hsum : (∑ e, x e * x e) = 0 := LinearMap.congr_fun h ⟨x, hx⟩
    have hz := (Finset.sum_mul_self_eq_zero_iff Finset.univ x).mp hsum
    ext e
    exact hz e (Finset.mem_univ e)
  · rintro rfl
    exact map_zero _

omit [Fintype V] in
/-- Every harmonic functional is represented by integration of a real chain. -/
theorem integration_surjective (G : EndpointGraph V E) :
    Function.Surjective (integration G) :=
  (Subspace.dualRestrict_surjective (W := harmonics G)).comp dotDual_surjective

/-- The additive kernel of integration is the explicitly defined gradient
subgroup used in the chain-coordinate covering space. -/
theorem integration_ker (G : EndpointGraph V E) :
    (integration G).toAddMonoidHom.ker = gradientSubgroup G := by
  ext x
  change integration G x = 0 ↔ ∃ φ : V → ℝ, gradient G φ = x
  rw [integration_eq_zero_iff]
  exact exists_congr fun φ => eq_comm

/-- The linear version of the exact integration-kernel statement. -/
theorem integration_ker_linear (G : EndpointGraph V E) :
    LinearMap.ker (integration G) = LinearMap.range (gradient G) := by
  ext x
  change integration G x = 0 ↔ ∃ φ : V → ℝ, gradient G φ = x
  rw [integration_eq_zero_iff]
  exact exists_congr fun φ => eq_comm

/-- The covering space, expressed as a quotient by the gradient submodule,
is linearly equivalent to the dual of harmonic forms. -/
def coverLinearEquiv (G : EndpointGraph V E) :
    ((E → ℝ) ⧸ LinearMap.range (gradient G)) ≃ₗ[ℝ] HarmonicDual G :=
  (Submodule.quotEquivOfEq _ _ (integration_ker_linear G).symm).trans
    ((integration G).quotKerEquivOfSurjective (integration_surjective G))

@[simp] theorem coverLinearEquiv_mk (G : EndpointGraph V E) (x : E → ℝ) :
    coverLinearEquiv G (Submodule.Quotient.mk x) = integration G x := rfl

/-- The real chain quotient is canonically the dual of the harmonic forms. -/
def coverEquiv (G : EndpointGraph V E) : Cover G ≃+ HarmonicDual G :=
  (QuotientAddGroup.quotientAddEquivOfEq (integration_ker G).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (integration G).toAddMonoidHom
      (integration_surjective G))

@[simp] theorem coverEquiv_coverClass (G : EndpointGraph V E) (x : E → ℝ) :
    coverEquiv G (coverClass G x) = integration G x := rfl

/-- Periods are obtained by integrating actual integral cycles against
harmonic forms. -/
def harmonicPeriods (G : EndpointGraph V E) : AddSubgroup (HarmonicDual G) :=
  (integerCycles G).map ((integration G).toAddMonoidHom.comp castChain)

/-- The harmonic definition of the unit-length tropical Jacobian. -/
abbrev HarmonicJacobian (G : EndpointGraph V E) := HarmonicDual G ⧸ harmonicPeriods G

/-- Integrate a real chain and then divide by the integral cycle periods. -/
def harmonicClass (G : EndpointGraph V E) : (E → ℝ) →+ HarmonicJacobian G :=
  (QuotientAddGroup.mk' (harmonicPeriods G)).comp (integration G).toAddMonoidHom

theorem harmonicClass_eq_zero_iff (G : EndpointGraph V E) (x : E → ℝ) :
    harmonicClass G x = 0 ↔ x ∈ periodSubgroup G := by
  change (QuotientAddGroup.mk (integration G x) : HarmonicJacobian G) =
    QuotientAddGroup.mk 0 ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, sub_zero, mem_periodSubgroup_iff]
  constructor
  · rintro ⟨c, hc, hcx⟩
    have hz : integration G (x - castChain c) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hcx.symm
    obtain ⟨φ, hφ⟩ := (integration_eq_zero_iff G _).mp hz
    exact ⟨φ, c, hc, sub_eq_iff_eq_add.mp hφ⟩
  · rintro ⟨φ, c, hc, rfl⟩
    refine ⟨c, hc, ?_⟩
    change integration G (castChain c) = integration G (gradient G φ + castChain c)
    rw [map_add, (integration_eq_zero_iff G _).mpr ⟨φ, rfl⟩, zero_add]

theorem harmonicClass_ker (G : EndpointGraph V E) :
    (harmonicClass G).ker = periodSubgroup G := by
  ext x
  exact harmonicClass_eq_zero_iff G x

omit [Fintype V] in
theorem harmonicClass_surjective (G : EndpointGraph V E) :
    Function.Surjective (harmonicClass G) := by
  intro q
  obtain ⟨h, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := integration_surjective G h
  exact ⟨x, rfl⟩

/-- The chain-coordinate Jacobian is canonically the harmonic dual modulo
the period lattice of integral cycles. -/
def jacobianEquiv (G : EndpointGraph V E) : Jacobian G ≃+ HarmonicJacobian G :=
  (QuotientAddGroup.quotientAddEquivOfEq (harmonicClass_ker G).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (harmonicClass G)
      (harmonicClass_surjective G))

@[simp] theorem jacobianEquiv_classMap (G : EndpointGraph V E) (x : E → ℝ) :
    jacobianEquiv G (classMap G x) = harmonicClass G x := rfl

omit [Fintype V] in
/-- Integration of a single oriented edge displacement has the expected
evaluation against every harmonic one-form. -/
theorem integration_single (G : EndpointGraph V E) [DecidableEq E]
    (e : E) (t : ℝ) (h : harmonics G) :
    integration G (Pi.single e t) h = t * (h : E → ℝ) e := by
  simp [integration_apply, Pi.single_apply]

end UnitHarmonic
end TropicalCurves
