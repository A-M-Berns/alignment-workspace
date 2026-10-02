# Conversation: Reconstructing Scott's Framework

## The author's Original Description (Verbatim)

> Scott was investigating a way of taking fixed points. Say you have some function $f: X \to X$. In the kakutani approach, you'd take the convex closure of the graph of $f$, at which point you can guarantee fixed points. If $X$ isn't a space that really allows for this (eg it is the discrete set $\{0,1\}$, you might instead "lift" $X$ to the space of distributions over $X$ first (which in this case amounts to replacing $\{0,1\}$ with the unit interval $[0,1]$). So you can see that in order to guarantee that fixed points exist, we often replate our function space $X \to X$ with something else, working in a category where all the morphisms are kakutani functions; and we often substitute the underlying space with something else, too, like lifting from $X$ to the space of distributions over $X$. Scott was using Kakutani ideas, but, I think we was lifting to the space of distributions over distributions rather than just single distributions, and he was ... making more use of convexity than kakutani does? maybe requiring that the whole graph is convex, rather than just each individual output like in kakutani? I'm not sure on that part.

> Scott wanted to change that. Scott wanted the fixed point of negation to be a distribution-distribution with all its mass on 50%, while the fixed point of the identity operation should spread its mass over all the distributions. I'm not sure distribution-distribution was exactly the thing tho; he also mentioned credal sets, so maybe convex sets of distributions? but I think he did talk about distributions over distributions some...

## Key Uncertainties from Conversation

### 1. The Exact Mathematical Object

AUTHOR: "I don't know between, like, $\Delta(X) \rightrightarrows \Delta^2(X)$ vs $\Delta^2(X) \rightrightarrows \Delta^2(X)$ vs $\Delta(X)^2 \rightrightarrows \Delta(X)$"

### 2. Monad Structure

AUTHOR: "He talked about respecting the spirit of the monad by collapsing things (so $\Delta^2$ gets collapsed to $\Delta$ at some point) but I'm not sure exactly where and when and why, and also he spoke about that as more like an optional choice he was making that seemed like the right thing to do but maybe a little bit more speculative than some other parts of his picture?"

### 3. Single-valued vs Multi-valued

- Could be a function $G: \Delta(X) \to \Delta^2(X)$ (single-valued)
- Could be a correspondence $G: \Delta(X) \rightrightarrows \Delta^2(X)$ (multi-valued)
- The multi-valued nature might be where credal sets come in

## Possible Framework Options

### Option 1: Pure Lifting
$$G: \Delta(X) \rightrightarrows \Delta^2(X)$$
- Fixed points: $p \in \Delta(X)$ such that $\delta_p \in G(p)$
- The correspondence maps distributions to sets of distribution-over-distributions
- Credal interpretation: $G(p)$ is a credal set in $\Delta^2(X)$

### Option 2: Endomorphism on $\Delta^2$
$$G: \Delta^2(X) \rightrightarrows \Delta^2(X)$$
- Fixed points: $\nu \in \Delta^2(X)$ such that $\nu \in G(\nu)$
- Working entirely at the second level
- Would need to explain how this relates to original functions on $X$

### Option 3: With Monad Collapse
$$\Delta(X) \xrightarrow{\eta} \Delta^2(X) \xrightarrow{G} \Delta^2(X) \xrightarrow{\mu} \Delta(X)$$
- $\eta$: point mass embedding ($p \mapsto \delta_p$)
- $G$: transformation at the $\Delta^2$ level
- $\mu$: monad multiplication/collapse (averaging distributions)
- Fixed points: $p$ where the round trip returns $p$
- "Respects the monad structure"

### Option 4: Product Space Version
$$G: \Delta(X) \times \Delta(X) \rightrightarrows \Delta(X)$$
- This is what $\Delta(X)^2 \rightrightarrows \Delta(X)$ might mean
- Less likely based on the context

## Connection to Credal Sets

The multi-valued nature (correspondences) naturally gives rise to credal sets:
- A correspondence $G: \Delta(X) \rightrightarrows \Delta^2(X)$ assigns to each $p$ a set $G(p) \subseteq \Delta^2(X)$
- If we require $G(p)$ to be convex, it's a credal set
- The convex graph requirement means: if $(p_1, \nu_1)$ and $(p_2, \nu_2)$ are in the graph, then so is any convex combination

## My (Claude's) Current Speculation

Based on the examples (negation having fixed point at uniform, identity spreading mass):

**Most likely:** Option 1 with convex graph requirement
- $G: \Delta(X) \rightrightarrows \Delta^2(X)$
- Graph$(G) = \{(p, \nu) : \nu \in G(p)\}$ must be convex in $\Delta(X) \times \Delta^2(X)$
- Fixed points where $\delta_p \in G(p)$

This would:
- Allow representing any function via lifting (as the author noted about polynomials)
- Make the fixed point operator continuous via convexity
- Connect naturally to credal sets (each $G(p)$ is a credal set)

The monad collapse might be an additional operation Scott considers but not central to the fixed point characterization.

## Questions for Scott

1. Is the mapping single-valued or multi-valued?
2. What's the domain and codomain exactly?
3. Where does the monad collapse happen, if at all?
4. How do credal sets fit in - are they the outputs, or an alternative formulation?
5. Is it $\Delta(X) \rightrightarrows \Delta^2(X)$ or $\Delta^2(X) \rightrightarrows \Delta^2(X)$?

## Key Insight from Conversation

The author pointed out that the $\Delta(X) \rightrightarrows \Delta^2(X)$ version seems too restrictive because of the convexity requirement. If we try to lift a function $f: [0,1] \to [0,1]$ directly by $G(p) = \delta_{f(p)}$, the graph won't be convex (unless $f$ is affine). This suggests the framework might be $\Delta^2(X) \rightrightarrows \Delta^2(X)$ instead, where any level-1 function can be lifted to have a convex graph.