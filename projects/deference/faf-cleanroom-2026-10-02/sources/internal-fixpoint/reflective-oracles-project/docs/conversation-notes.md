# Conversation Notes: Mathematical Framework Discussion

## Key Insights from Discussion

### 1. The Levels Structure
- **Level 0**: $X = \{0, 1\}$ (discrete/booleans)
- **Level 1**: $\Delta(X) \cong [0,1]$ (distributions over bools)
- **Level 2**: $\Delta^2(X) = \Delta([0,1])$ (distributions over distributions)

### 2. The Convexity Problem
**Issue identified**: If we try to lift an arbitrary function $f: [0,1] \to [0,1]$ to $G: \Delta(X) \to \Delta^2(X)$ by $G(p) = \delta_{f(p)}$, the graph won't be convex!

**Why**: Convexity would require that for $(p_1, \delta_{f(p_1)})$ and $(p_2, \delta_{f(p_2)})$ in the graph, we also have:
$$(\lambda p_1 + (1-\lambda)p_2, \lambda \delta_{f(p_1)} + (1-\lambda) \delta_{f(p_2)})$$

But $\lambda \delta_{f(p_1)} + (1-\lambda) \delta_{f(p_2)}$ is NOT a point mass unless $f(p_1) = f(p_2)$.

**Conclusion**: The convexity requirement forces correspondences to be genuinely multi-valued.

### 3. Possible Framework Versions

Based on our discussion, the main candidates are:

#### Version A: $\Delta(X) \rightrightarrows \Delta^2(X)$
- **Pro**: Matches "distributions to distributions-over-distributions" description
- **Con**: Very restrictive due to convexity requirements
- **Status**: Possibly eliminated due to restrictions

#### Version B: $\Delta^2(X) \rightrightarrows \Delta^2(X)$
- **Pro**: Can represent any level-1 function with convex lifting
- **Pro**: Natural for monad structure
- **Note**: Fixed points would be distributions-over-distributions

#### Version C: $\Delta^2(X) \rightrightarrows \Delta(X)$
- **Pro**: Incorporates monad collapse directly
- **Note**: Would combine lifting and collapse in one operation

### 4. The Two-Level Jump Advantage

Key insight from the author: When starting from discrete (bools), going two levels up provides:
1. Enough "room" for convexity
2. Geometrically nice fixed points
3. Meaningful collapse back to level 1

Any relation at level $n$ can be represented as a convex relation at level $n+1$.

### 5. Fixed Points as Intersections

In Scott's framework:
- Identity embedding: $\iota: p \mapsto \delta_p$
- Fixed points: Points where Graph$(G) \cap$ Graph$(\iota)$
- This turns algebraic equation-solving into geometric intersection

### 6. Connection to Examples

**Negation**: Should have fixed point with all mass on uniform distribution
**Identity**: Should spread mass over all distributions

These examples should help determine which framework version is correct.

### 7. Credal Sets Connection

- Multi-valued correspondences naturally give credal sets
- Each $G(p)$ is a convex set (credal set) of outputs
- Convex graph is stronger than just convex outputs

### 8. Open Questions for Scott

1. Is the mapping single-valued or multi-valued?
2. What's the exact domain and codomain?
3. Where does monad collapse happen?
4. How do credal sets fit in exactly?
5. Is it $\Delta(X) \rightrightarrows \Delta^2(X)$ or $\Delta^2(X) \rightrightarrows \Delta^2(X)$?

### 9. Important Clarifications

- $\Delta^2(X)$ means $\Delta(\Delta(X))$, NOT $\Delta(X) \times \Delta(X)$
- "Respecting the monad" refers to using the collapse operation
- The monad collapse was described as "optional" or "speculative"

## Next Steps

- [scrubbed]
- Test different framework versions with concrete examples
- Determine which version makes negation and identity work correctly
- Formalize the continuity argument