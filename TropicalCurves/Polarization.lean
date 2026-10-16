import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith

/-!
# Finite graph polarizations and quasistability

The unit-length Abel-map theorem uses a graph presented by two endpoint maps.
Loops and parallel edges are permitted. A cut counts each edge whose endpoints
lie on opposite sides. The function `beta` is the divisor-stability expression
`deg(D|S) - μ(S) + δ(S)/2`.

This module defines general polarizations, stability, semistability, and rooted
quasistability, and proves their equivalence for a general polarization on the
original graph. The extension to pseudo-divisors on subdivided graphs is in
`UnitPseudoDivisor`.
-/

namespace TropicalCurves
namespace FiniteStability


/-- An undirected finite multigraph presented by endpoint maps. The orientation
is used only for its presentation; all stability definitions are symmetric. -/
structure EndpointGraph (V E : Type*) where
  source : E → V
  target : E → V

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Edges crossing the boundary of a vertex subset, each counted once. -/
def cut (G : EndpointGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter fun e =>
    (G.source e ∈ S ∧ G.target e ∉ S) ∨
      (G.source e ∉ S ∧ G.target e ∈ S)

/-- The polarization stability expression, with divisor coefficients in `ℤ`. -/
noncomputable def beta (G : EndpointGraph V E) (μ : V → ℝ)
    (D : V → ℤ) (S : Finset V) : ℝ :=
  (∑ v ∈ S, (D v : ℝ)) - (∑ v ∈ S, μ v) + (cut G S).card / 2

/-- The total real degree of a polarization. -/
noncomputable def polarizationDegree (μ : V → ℝ) : ℝ := ∑ v, μ v

/-- Equality of divisor degree and polarization degree. -/
def DegreeCompatible (μ : V → ℝ) (D : V → ℤ) : Prop :=
  (∑ v, (D v : ℝ)) = polarizationDegree μ

/-- No proper nonempty vertex subset lies on a stability wall. This is the
usual genericity condition for a polarization on a connected finite graph. -/
def IsGeneral (G : EndpointGraph V E) (μ : V → ℝ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    ∀ z : ℤ, (∑ v ∈ S, μ v) - (cut G S).card / 2 ≠ (z : ℝ)

/-- Strict stability with the degree condition included. -/
def IsStable (G : EndpointGraph V E) (μ : V → ℝ) (D : V → ℤ) : Prop :=
  DegreeCompatible μ D ∧
    ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 0 < beta G μ D S

/-- Semistability with the degree condition included. -/
def IsSemistable (G : EndpointGraph V E) (μ : V → ℝ) (D : V → ℤ) : Prop :=
  DegreeCompatible μ D ∧
    ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 0 ≤ beta G μ D S

/-- Quasistability at a chosen root: semistability everywhere, and strict
inequality for proper nonempty subsets containing the root. -/
def IsQuasistable (G : EndpointGraph V E) (μ : V → ℝ) (root : V)
    (D : V → ℤ) : Prop :=
  IsSemistable G μ D ∧
    ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → root ∈ S →
      0 < beta G μ D S

/-- Generality excludes every equality wall for an integer divisor. -/
theorem beta_ne_zero_of_general (G : EndpointGraph V E) (μ : V → ℝ)
    (hgeneral : IsGeneral G μ) (D : V → ℤ) (S : Finset V)
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) : beta G μ D S ≠ 0 := by
  intro hzero
  apply hgeneral S hne hproper (∑ v ∈ S, D v)
  push_cast
  unfold beta at hzero
  linarith

/-- For a general polarization, semistability and stability coincide. -/
theorem stable_iff_semistable_of_general (G : EndpointGraph V E) (μ : V → ℝ)
    (hgeneral : IsGeneral G μ) (D : V → ℤ) :
    IsStable G μ D ↔ IsSemistable G μ D := by
  constructor
  · rintro ⟨hdegree, hstable⟩
    exact ⟨hdegree, fun S hne hproper => le_of_lt (hstable S hne hproper)⟩
  · rintro ⟨hdegree, hsemistable⟩
    refine ⟨hdegree, ?_⟩
    intro S hne hproper
    exact lt_of_le_of_ne (hsemistable S hne hproper)
      (Ne.symm (beta_ne_zero_of_general G μ hgeneral D S hne hproper))

/-- Strict stability implies quasistability at every root. -/
theorem IsStable.quasistable {G : EndpointGraph V E} {μ : V → ℝ} {D : V → ℤ}
    (h : IsStable G μ D) (root : V) : IsQuasistable G μ root D := by
  exact ⟨⟨h.1, fun S hne hproper => le_of_lt (h.2 S hne hproper)⟩,
    fun S hne hproper _ => h.2 S hne hproper⟩

/-- For a general polarization, the choice of quasistability root is irrelevant. -/
theorem quasistable_iff_stable_of_general (G : EndpointGraph V E) (μ : V → ℝ)
    (hgeneral : IsGeneral G μ) (root : V) (D : V → ℤ) :
    IsQuasistable G μ root D ↔ IsStable G μ D := by
  constructor
  · intro h
    exact (stable_iff_semistable_of_general G μ hgeneral D).mpr h.1
  · intro h
    exact h.quasistable root

end FiniteStability
end TropicalCurves
