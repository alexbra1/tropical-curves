import Mathlib.Data.Real.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Sum.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Points and divisors for the unit-length graph model

This file supplies the underlying point set, edge parametrizations, and finitely
supported integral divisors used by the unit-length theorem. The foundational
structure permits positive real lengths; `UnitAbelMap.unitGraph` specializes
every edge length to one, and `UnitLengthModel` proves the corresponding transport
for a graph whose length function is identically one. Loops and parallel edges are permitted. To obtain a *finite* graph
model, assume `[Finite V]` and `[Finite E]`.

Despite the filename, no path metric or `MetricSpace` instance is asserted here.
The point set is a canonical representative model for the usual gluing of
closed intervals: vertices are represented once, and each edge contributes only
its open interior. A metric, continuity, and invariance under subdivision remain
separate tasks.
-/

namespace TropicalCurves

/-- A graph model with oriented endpoints and strictly positive real lengths.
The orientation is auxiliary. Neither loops nor parallel edges are excluded. -/
structure RealLengthGraph (V E : Type*) where
  source : E → V
  target : E → V
  length : E → ℝ
  length_pos : ∀ e, 0 < length e

namespace RealLengthGraph

variable {V E : Type*} (G : RealLengthGraph V E)

/-- Points are vertices or strictly interior points of one specific edge. -/
def Point : Type _ := V ⊕ (Σ e : E, Set.Ioo (0 : ℝ) (G.length e))

/-- Include a graph vertex in the point set. -/
def vertex (v : V) : G.Point := Sum.inl v

/-- Include an interior edge coordinate in the point set. -/
def interior (e : E) (t : Set.Ioo (0 : ℝ) (G.length e)) : G.Point :=
  Sum.inr ⟨e, t⟩

theorem vertex_injective : Function.Injective G.vertex :=
  Sum.inl_injective

@[simp]
theorem vertex_eq_vertex_iff (v w : V) : G.vertex v = G.vertex w ↔ v = w :=
  G.vertex_injective.eq_iff

@[simp]
theorem interior_ne_vertex (e : E) (t : Set.Ioo (0 : ℝ) (G.length e)) (v : V) :
    G.interior e t ≠ G.vertex v := by
  simp [interior, vertex]

@[simp]
theorem vertex_ne_interior (v : V) (e : E) (t : Set.Ioo (0 : ℝ) (G.length e)) :
    G.vertex v ≠ G.interior e t := by
  simp [interior, vertex]

theorem interior_injective (e : E) : Function.Injective (G.interior e) := by
  intro s t h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2

/-- Every point is either a vertex or an interior edge point. -/
theorem point_cases (p : G.Point) :
    (∃ v, p = G.vertex v) ∨ (∃ e t, p = G.interior e t) := by
  cases p with
  | inl v => exact Or.inl ⟨v, rfl⟩
  | inr q => exact Or.inr ⟨q.1, q.2, rfl⟩

noncomputable section

/-- Parametrize a closed edge, identifying the two endpoints with its vertices. -/
def closedEdgeMap (e : E) (t : Set.Icc (0 : ℝ) (G.length e)) : G.Point :=
  if h₀ : (t : ℝ) = 0 then G.vertex (G.source e)
  else if h₁ : (t : ℝ) = G.length e then G.vertex (G.target e)
  else G.interior e ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm h₀),
    lt_of_le_of_ne t.property.2 h₁⟩

@[simp]
theorem closedEdgeMap_zero (e : E) :
    G.closedEdgeMap e ⟨0, le_rfl, le_of_lt (G.length_pos e)⟩ =
      G.vertex (G.source e) := by
  simp [closedEdgeMap]

@[simp]
theorem closedEdgeMap_length (e : E) :
    G.closedEdgeMap e ⟨G.length e, le_of_lt (G.length_pos e), le_rfl⟩ =
      G.vertex (G.target e) := by
  simp [closedEdgeMap, ne_of_gt (G.length_pos e)]

@[simp]
theorem closedEdgeMap_interior (e : E) (t : Set.Ioo (0 : ℝ) (G.length e)) :
    G.closedEdgeMap e ⟨t, le_of_lt t.property.1, le_of_lt t.property.2⟩ =
      G.interior e t := by
  simp [closedEdgeMap, ne_of_gt t.property.1, ne_of_lt t.property.2]

/-- The two endpoint parameters of a loop give the same point. -/
theorem closedEdgeMap_loop_endpoints (e : E) (h : G.source e = G.target e) :
    G.closedEdgeMap e ⟨0, le_rfl, le_of_lt (G.length_pos e)⟩ =
      G.closedEdgeMap e ⟨G.length e, le_of_lt (G.length_pos e), le_rfl⟩ := by
  simp [h]

/-- Integral divisors with finite support at arbitrary points of the graph model. -/
abbrev Divisor := G.Point →₀ ℤ

/-- The sum of the coefficients of a divisor. -/
def degree (D : G.Divisor) : ℤ := D.degree

@[simp]
theorem degree_zero : G.degree 0 = 0 := by
  simp [degree]

@[simp]
theorem degree_add (D D' : G.Divisor) :
    G.degree (D + D') = G.degree D + G.degree D' := by
  simp [degree]

@[simp]
theorem degree_single (p : G.Point) (n : ℤ) :
    G.degree (Finsupp.single p n) = n := by
  simp [degree]

/-- Degree as a homomorphism, useful for defining fixed-degree divisors later. -/
def degreeHom : G.Divisor →+ ℤ where
  toFun := G.degree
  map_zero' := G.degree_zero
  map_add' := G.degree_add

@[simp]
theorem degree_neg (D : G.Divisor) : G.degree (-D) = -G.degree D :=
  map_neg G.degreeHom D

@[simp]
theorem degree_sub (D D' : G.Divisor) :
    G.degree (D - D') = G.degree D - G.degree D' :=
  map_sub G.degreeHom D D'

/-- The effective divisor consisting of one chip at each point in a finite family.
Repeated points are counted with their multiplicity. -/
def movingDivisor {ι : Type*} [Fintype ι] (p : ι → G.Point) : G.Divisor :=
  ∑ i, Finsupp.single (p i) 1

@[simp]
theorem degree_movingDivisor {ι : Type*} [Fintype ι] (p : ι → G.Point) :
    G.degree (G.movingDivisor p) = (Fintype.card ι : ℤ) := by
  change G.degreeHom (∑ i, Finsupp.single (p i) 1) = _
  rw [map_sum]
  simp [degreeHom, degree]

/-- The divisor-level Abel construction in the convention `D - ∑ᵢ [pᵢ]`.
This is a map to divisors, before passing to linear equivalence or a Jacobian. -/
def abelDivisor {ι : Type*} [Fintype ι] (D : G.Divisor) (p : ι → G.Point) :
    G.Divisor := D - G.movingDivisor p

@[simp]
theorem degree_abelDivisor {ι : Type*} [Fintype ι]
    (D : G.Divisor) (p : ι → G.Point) :
    G.degree (G.abelDivisor D p) = G.degree D - (Fintype.card ι : ℤ) := by
  simp [abelDivisor]

/-- The product of specified closed edges, as their real coordinate intervals. -/
abbrev EdgeProduct {ι : Type*} (edges : ι → E) :=
  ∀ i, Set.Icc (0 : ℝ) (G.length (edges i))

/-- The divisor-level Abel map restricted to a product of closed edges. -/
def edgeAbelDivisor {ι : Type*} [Fintype ι] (D : G.Divisor)
    (edges : ι → E) (x : G.EdgeProduct edges) : G.Divisor :=
  G.abelDivisor D (fun i => G.closedEdgeMap (edges i) (x i))

@[simp]
theorem degree_edgeAbelDivisor {ι : Type*} [Fintype ι]
    (D : G.Divisor) (edges : ι → E) (x : G.EdgeProduct edges) :
    G.degree (G.edgeAbelDivisor D edges x) = G.degree D - (Fintype.card ι : ℤ) := by
  simp [edgeAbelDivisor]

/-- A divisor is vertex-supported if every interior-edge coefficient is zero. -/
def VertexSupported (D : G.Divisor) : Prop :=
  ∀ (e : E) (t : Set.Ioo (0 : ℝ) (G.length e)), D (G.interior e t) = 0

/-- Equivalent support-based description of a vertex-supported divisor. -/
theorem vertexSupported_iff_support (D : G.Divisor) :
    G.VertexSupported D ↔ ∀ p ∈ D.support, ∃ v, p = G.vertex v := by
  constructor
  · intro h p hp
    rcases G.point_cases p with hv | ⟨e, t, rfl⟩
    · exact hv
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) (h e t))
  · intro h e t
    by_contra hn
    obtain ⟨v, hv⟩ := h (G.interior e t) (Finsupp.mem_support_iff.mpr hn)
    exact G.interior_ne_vertex e t v hv

@[simp]
theorem vertexSupported_zero : G.VertexSupported 0 := by
  intro e t
  simp

theorem VertexSupported.add {D D' : G.Divisor}
    (h : G.VertexSupported D) (h' : G.VertexSupported D') :
    G.VertexSupported (D + D') := by
  intro e t
  simp [h e t, h' e t]

theorem VertexSupported.neg {D : G.Divisor} (h : G.VertexSupported D) :
    G.VertexSupported (-D) := by
  intro e t
  simp [h e t]

theorem vertexSupported_single (v : V) (n : ℤ) :
    G.VertexSupported (Finsupp.single (G.vertex v) n) := by
  intro e t
  simp

/-- The injective inclusion of vertices, packaged as an embedding. -/
def vertexEmbedding : V ↪ G.Point := ⟨G.vertex, G.vertex_injective⟩

/-- Extend an integral divisor on the vertex set by zero to all points. -/
def vertexDivisor (D : V →₀ ℤ) : G.Divisor :=
  Finsupp.embDomain G.vertexEmbedding D

@[simp]
theorem vertexDivisor_vertex (D : V →₀ ℤ) (v : V) :
    G.vertexDivisor D (G.vertex v) = D v :=
  Finsupp.embDomain_apply G.vertexEmbedding D v

@[simp]
theorem vertexDivisor_interior (D : V →₀ ℤ) (e : E)
    (t : Set.Ioo (0 : ℝ) (G.length e)) :
    G.vertexDivisor D (G.interior e t) = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨v, hv⟩
  exact G.vertex_ne_interior v e t hv

theorem vertexDivisor_vertexSupported (D : V →₀ ℤ) :
    G.VertexSupported (G.vertexDivisor D) := by
  intro e t
  exact G.vertexDivisor_interior D e t

theorem vertexDivisor_injective : Function.Injective G.vertexDivisor :=
  Finsupp.embDomain_injective G.vertexEmbedding

/-- Restrict a divisor to the graph vertices; all interior coefficients are discarded. -/
def restrictToVertices (D : G.Divisor) : V →₀ ℤ :=
  D.comapDomain G.vertex G.vertex_injective.injOn

@[simp]
theorem restrictToVertices_apply (D : G.Divisor) (v : V) :
    G.restrictToVertices D v = D (G.vertex v) :=
  Finsupp.comapDomain_apply G.vertex D G.vertex_injective.injOn v

@[simp]
theorem restrictToVertices_vertexDivisor (D : V →₀ ℤ) :
    G.restrictToVertices (G.vertexDivisor D) = D := by
  ext v
  simp

theorem vertexDivisor_restrictToVertices {D : G.Divisor}
    (h : G.VertexSupported D) : G.vertexDivisor (G.restrictToVertices D) = D := by
  ext p
  rcases G.point_cases p with ⟨v, rfl⟩ | ⟨e, t, rfl⟩
  · simp
  · simp [h e t]

/-- Vertex-supported divisors are exactly the extensions of graph divisors. -/
theorem vertexSupported_iff_exists_vertexDivisor (D : G.Divisor) :
    G.VertexSupported D ↔ ∃ A : V →₀ ℤ, G.vertexDivisor A = D := by
  constructor
  · intro h
    exact ⟨G.restrictToVertices D, G.vertexDivisor_restrictToVertices h⟩
  · rintro ⟨A, rfl⟩
    exact G.vertexDivisor_vertexSupported A

@[simp]
theorem degree_vertexDivisor (D : V →₀ ℤ) :
    G.degree (G.vertexDivisor D) = D.degree := by
  simp [degree, Finsupp.degree, vertexDivisor]

end

end RealLengthGraph

end TropicalCurves
