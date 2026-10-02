# Mathematical Formulation: Reflective Oracles and Correlated Equilibria

## 1. The Standard Kakutani Approach

### Kakutani Fixed Point Theorem
Let X be a non-empty, compact, convex subset of a Euclidean space. Let F: X ⇉ X be a correspondence (set-valued function) such that:
1. F(x) is non-empty for all x ∈ X
2. F(x) is convex for all x ∈ X
3. F has a closed graph

Then F has a fixed point: ∃x* ∈ X such that x* ∈ F(x*)

### Limitation for Discrete Spaces
When X = {0,1}, we cannot directly apply Kakutani because:
- X is not convex
- Cannot take convex combinations

**Standard Solution**: Lift to Δ(X) = [0,1], the space of distributions over {0,1}

## 2. The Fixed Point Operator Problem

### Why the Fixed Point Operator is Discontinuous

Consider g_ε(x) = x + ε·sign(x) on [-1, 1]:
- For ε = 0: Every point is a fixed point
- For ε > 0: Only x = 0 is a fixed point
- For ε < 0: Only x = 0 is a fixed point

The set of fixed points changes discontinuously! When we have set-valued fixed points, selecting one creates discontinuity.

### Scott's Insight
We need a category where:
1. Objects are some generalization of functions X → X
2. Fixed points always exist
3. **The fixed point operator itself is a morphism in the category**

## 3. Scott's Proposed Construction

### The Category of Convex-Graph Correspondences (CGC)

#### Definition 1: The Space D²(X)
For a finite set X, define:
- Δ(X) = {p ∈ R^|X| : p_i ≥ 0, Σp_i = 1} - probability distributions over X
- Δ²(X) := Δ(Δ(X)) - probability distributions over distributions

#### Definition 2: Convex-Graph Correspondences
A correspondence G: Δ(X) ⇉ Δ²(X) has a **convex graph** if:
Graph(G) = {(p, μ) : p ∈ Δ(X), μ ∈ G(p)}
is a convex subset of Δ(X) × Δ²(X).

This is stronger than Kakutani's requirement that each G(p) be convex.

#### Definition 3: The Identity Embedding
Define ι: Δ(X) → Δ²(X) by ι(p) = δ_p, where δ_p is the Dirac measure at p.

### Key Theorem: Fixed Points as Intersections
For a correspondence G: Δ(X) ⇉ Δ²(X), a point p ∈ Δ(X) is a fixed point if and only if (p, δ_p) ∈ Graph(G).

Therefore: FixedPoints(G) = π₁(Graph(G) ∩ Graph(ι))

## 4. Examples in the New Framework

### Example 1: Negation
For X = {0,1}, negation is f(0) = 1, f(1) = 0.

**Scott's Construction**:
- Define G_neg: [0,1] ⇉ Δ²({0,1})
- For p ∈ [0,1], G_neg(p) contains distributions μ such that:
  - μ puts weight (1-p) on distributions near (1,0)
  - μ puts weight p on distributions near (0,1)
- Fixed point: p = 1/2 with μ = δ_{(1/2, 1/2)}
- Interpretation: "The only stable belief is maximum uncertainty"

### Example 2: Identity
For identity f(x) = x:

**Scott's Construction**:
- G_id(p) = {μ ∈ Δ²(X) : ∫ q dμ(q) = p}
- Every p ∈ Δ(X) is a fixed point
- The correspondence maintains the mean while spreading mass
- Interpretation: "Any belief is stable under identity"

## 5. Connection to Correlated Equilibria

### Nash vs Correlated Equilibria
- **Nash**: Players independently randomize σ_i ∈ Δ(A_i)
- **Correlated**: Distribution μ ∈ Δ(Π_i A_i) over joint action profiles

### Reflective Oracles as Correlation Device
- Oracle provides shared randomization
- Fixed points = equilibrium distributions
- Scott's construction ensures continuous variation

### The Correlated Version
In Scott's framework:
- X = action profiles
- Δ(X) = mixed strategies
- Δ²(X) = beliefs about correlated play
- Fixed points = correlated equilibria

## 6. Main Conjecture

**Scott's Main Result (Conjectured)**:
In the category CGC:
1. Every object has a non-empty fixed point set (generalized Kakutani)
2. The fixed point operator FP is itself a morphism when appropriately restricted
3. Small perturbations to G lead to small perturbations in FP(G)

This provides the "well-behaved" fixed point operator that avoids the discontinuity issues of standard approaches.

## 7. Open Questions

1. **Precise Topology**: What topology on Δ²(X) makes everything work?
2. **Computational Complexity**: How hard is it to find fixed points in CGC?
3. **Relationship to Credal Sets**: Is the credal set formulation equivalent?
4. **Generalization**: Can this extend beyond finite X?
5. **Algorithmic Implementation**: Can we compute these fixed points efficiently?