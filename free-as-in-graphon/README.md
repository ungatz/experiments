# Polynomial categories over a distributive base

Agda on the polynomial category used by Ackerman, Freer, Kaddar, Karwowski, Moss, Roy,
Staton and Yang in *Probabilistic Programming Interfaces for Random Graphs: Markov
Categories, Graphons, and Nominal Sets*, POPL 2024, Section 4.1.2.

The directory name predates the contents and promises more than they deliver. The last
section says what is missing.

## The separation

**`Poly/Schemes.agda`** strips the question down to its combinatorial core. A representative
is a heap size together with a record of which cell each of two branches reads, and
reindexing along an injection is composition with it. The two schemes then differ in exactly
one place: the uniform one reindexes both branches by a single injection, the independent one
by a pair, one per branch. Two programs live in that gap. One draws a cell before branching
and routes it into both branches; the other draws a cell inside each branch. `schemes-differ`
is the statement that the uniform scheme keeps them apart and the independent scheme
identifies them, and the invariant doing the separating is whether the two branches read the
same cell.

**`Poly/Congruence.agda`** takes the relation as generated, over the finite graph-choice
core: worlds are positive finite labelled simple graphs given by symmetric loopless Boolean
adjacency, and a representative picks, for each world, one of its vertices. `OneStep` is the
one-block generating relation. Two facts about it are proved. It does identify the pair it is
designed to identify. And that identification does not survive composition: precomposing both
sides with a morphism that produces its argument by drawing rather than receiving it sends
them to representatives the closure cannot join, which is `one-block-separates`. The
obstruction is an invariant of the closure and not a property of the particular witness, so
`independent-not-closed` rules out every relation acting branch by branch, whatever
injections it is permitted.

## The construction

`Poly/Category.agda` builds Hermida and Tennent's `C[x : jΣ]` in general form, over an
arbitrary symmetric monoidal base, an arbitrary index, and a strong monoidal `j`. Objects are
those of the base, hom-sets are `(Σ w. C(x ⊗ jw, y))` quotiented by reindexing, composition
accumulates heaps. The three category laws hold on the quotient because each is a one-step
zigzag whose mediator is a structural isomorphism of the index.

`Poly/Cocartesian.agda` does the same over a base taken with its chosen coproduct as tensor
and its chosen initial object as unit. Only the coproduct and the initial object are used;
the tensor, the symmetry and the distributor are never touched.

`Poly/Recognition.agda` identifies the two: `C[x : id]` is the cocartesian polynomial
category, on the nose, by an isomorphism that moves the heap across the coproduct swap.

`Poly/Directed.agda` gives binary coproducts and an initial object upstairs, under a
hypothesis on the index. `Poly/DirectedColimit.agda` supplies the comparison
`colim (F × G) → colim F × colim G` that the previous module assembles, together with the
alignment lemma an injectivity argument needs.

`Poly/Chain.agda` is a three-element chain with the meet as tensor and the join as coproduct,
so the coproducts and the initial object of the previous module exist there. It carries two
further facts, which are why it is here at all: the adjoining functor is not full, and there
is no morphism from the top to the bottom. Without them nothing rules out the construction
being degenerate.

`Poly/Fam.agda` presents `Fam(D)` by finite lists, with the block-function variance of
Section 4.1.1: a morphism chooses, for every source block, a target block and a `D`-morphism
into that block. `Poly/FamSingleton.agda` adds the singleton inclusion, and is careful about
the one thing it refuses to do, which is treat list concatenation and the base tensor as the
same operation.

## Shared machinery

`Poly/Base.agda` has the zigzag closure of a step relation and the quotient by it, plus the
fact that two relations generating each other's closures give the same quotient.
`Poly/Components.agda` observes that the quotient is the set of connected components of a
category, and proves the invariant principle, the weak-cone bound and the canonical-root
criterion once rather than per instance. `Poly/Kit.agda` is lemmas.
`Poly/StrictIso.agda` is identity-on-objects isomorphism of categories, fielded directly
because the library packages the weaker notions. `Poly/Monoidal/` has the base records.

## What is not here

**The free object is not mechanised.** The quotient by the closed relation is the free
distributive symmetric monoidal category on the base with an indeterminate, and no module
here builds that relation or proves that theorem. What is here is the category the theorem is
about, and the separation that forces the relation to be closed.

**The coproduct tier does not cover finite sets and injections.** `Poly/Directed.agda`
assumes an index whose hom-types are propositions, so it applies to preorders. Finite sets
and injections form no preorder: there are many injections between two given sets. The
directedness record also asks for a common source on every pair, which is the condition the
argument actually needs, but the two are bundled here and only the bundle is proved. The
shipped instances are a three-element chain and the natural numbers under the reverse order.
So the index of the paper is outside the scope of that module, and adapting it is real work
rather than a matter of instantiation.

**The congruence result is over the combinatorial core, not over their base.** In
`Poly/Congruence.agda` the objects are heap sizes and vertex choices, not families of graphs,
and no monoidal or coproduct structure is built on them. The argument runs at the level where
it is visible, and it is not an instantiation at `Fam(G^op)[ν]`.

## Checking it

Agda 2.8.0 and cubical 0.9. With the cubical library registered,

    agda Poly/Congruence.agda

checks the four modules of the separation, and

    for f in Poly/*.agda Poly/Monoidal/*.agda; do agda "$f"; done

checks all eighteen.
