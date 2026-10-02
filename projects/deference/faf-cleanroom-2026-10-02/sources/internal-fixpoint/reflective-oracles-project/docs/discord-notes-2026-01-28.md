# Discord Notes: Scott, Sam, and the author - 2026-01-28

## Discord Conversation (Verbatim)

[scrubbed]

## Meeting Notes (the author's Paraphrases)

### On Kakutani Not Composing
Sam and Scott said the fact that Kakutani doesn't compose is not that big of a problem for this project. "You can just take the convex hull." the author was unsure whether Scott meant convex hull on the full relation (as discussed earlier) or just on the outputs (more like standard Kakutani).

### The Category Structure

Scott described two (or three) categories:

1. **Category of compact Hausdorff spaces** where the morphisms are total closed relations
2. **Category of compact Hausdorff convex spaces** where the morphisms are... (see proposals below)
3. Possibly a third category involving linear functions

There's a forgetful functor from (2) to (1).

**Proposed morphisms for category 2**: Things you can get by taking closed graph relations that contain a continuous function, and intersecting them.

### Design Criteria

The two main criteria:
1. **A fixed point theorem** for the category
2. **An internal hom / function object**: Given $X$ and $Y$, have something representing morphisms from $X$ to $Y$
3. **Fixed point finder as a morphism**: Goes from $(X \to X)$ to $X$, or maybe to distributions on $X$

Multiple proposals doing this for different fixed point theorems and different internal objects that "look sort of like a monad."

### Three Fixed Point Theorems

Scott suspects he cares about three things corresponding to three fixed point theorems:
1. **Tarski** — the linear thing
2. **Banach** — closed graph without probabilities at all
3. **Brouwer/Kakutani** — respecting convexity, taking full convex hull

Scott: "I'm still uncertain about what I want to do for the full Kakutani power."

### Computation as Nested Intersections

A key design criterion beyond the category structure: **everything should be approximable by intersections**. You define things as limits of nested things.

Scott's description:
> "You take nested graphs, and you define argmax of a graph as the non-dominated stuff, as you shrink down the graphs you get less non-dominated stuff, and that's how computation is supposed to work in this space. Which is why we have compactness everywhere."

### Brouwer and Computation

Scott on getting in a "better mood about Brouwer":
> "I was playing with computation in this way with nested relations, and it's like, it's fine that Brouwer hasn't really fixed a fixed point yet. We can still point out a tightening set that contains the fixed points. Taking a closed interval in the reals feels more like 'having a real' to me now."
> "Things have moved far enough that I can tell there's no fixed point here, but where they moved gives me this data that I can propagate around."

The point: when you observe an open set that's sent to a disjoint open set, the fixed point isn't there. You progressively remove non-fixed-points by finding closed sets that don't intersect their preimage, removing interiors, and shrinking.

Connection to Vietoris topology mentioned but not fully worked out.

Scott's key observation about forward/backward:
> "If you go forward and back you might gain points, but if you go back and forward you recover"

### Sam's Meta-Point About Categories

Sam said it's not just that there are three categories to work in. The situation is like **algebra vs linear algebra**: linear algebra doesn't just introduce new things (vectors, matrices), it relates them to scalars. So the picture involves **relationships between the categories**, not just working within each one.

## Key Takeaways

1. **Kakutani maps don't compose** — this is an issue but "not that big" because you can take convex hulls
2. **Total convex-graph relations DO compose** — this is why Scott cares about them
3. **Vietoris fractions** are a known category with fixed point theory that might be relevant
4. **Three categories** corresponding to Tarski/Banach/Brouwer, with relationships between them
5. **Computation = nested intersections** — fundamental design principle
6. **Compactness is everywhere** for a reason: it ensures limits of nested things behave well
7. **Internal hom + fixed point as morphism** are the key design criteria