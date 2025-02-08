# Reflect

An elementary reconstruction of [free generators](https://harrisongoldste.in/papers/oopsla22.pdf) and [reflective generators](https://harrisongoldste.in/papers/icfp23-reflective.pdf) in OCaml.

My original motivation was to try understanding these two papers through an elementary lens. The original papers make free use of monads, freer monads, and some category theory which I honestly don't have a solid grasp of. So I wanted to see if I could reconstruct the ideas using more naive principles that are familiar to a wider audience -- so naive that perhaps they could taught to undergraduates who know a bit of functional programming.

As it turns out, this is possible! We can start with context-free grammars. The ultimate goal is to get to reflective generators, which can be broken down into two, largely orthogonal axes:
```
         ^
         | 
         |
[add context-sensitivity]
         |
         |
        CFG -----------------[add reflection]-----------------> 
```
Each of these axes only require a small extension to the classic CFG.
Finally, these two axes can be composed, yielding reflective generators.

The files (in the [lib](./lib) folder) reflect this journey:
1. The bottom-left corner is [gen_free.ml](./lib/gen_free.ml), which is the classic context-free grammar (using the equivalent formulation of context-free expression). We also give several classic denotational semantics, including enumeration (i.e., the language of the grammar) and fair/biased random sampling.
2. We add the vertical axis -- context-sensitivity -- in [gen_sens.ml](./lib/gen_sens.ml) by changing the context-free sequencing operator (`*`) to a context-sensitive one (`>>=`). (In Haskell terms, this goes from `Applicative` to `Monad`.)
3. Independently, we add the horizontal axis -- reflection -- in [reflect_free.ml](./lib/gen_reflect.ml) by attempting to give a reflection semantics for the original CFG. This will fail, but we will observe that reflection is the inverse of enumeration, and that almost all operators in the CFG are invertible, except for semantic actions (in Haskell terms, this corresponds to functor's `fmap`). Thus, we augment this operator to require an "semantic un-action" so that every action can be undone.
4. Finally, we combine the two axes in [reflect_sens.ml](./lib/gen_reflect_sens.ml) to get reflective generators. The only caveat is that in step 2, semantic actions (`fmap`) would have been subsumed by context-sensitive sequencing (`>>=`), so we move the semantic un-action annotation to sequencing, and adjust the types accordingly.
5. (Optional) The last observation to recover the original presentation in the papers is to note that CFGs have a natural normal form, where the multiplicative fragment is interleaved with the additive fragment. (I think this is what gives the freer monad-like structure: `one` and `*` (or `bind`) form the multiplicative fragment, while `zero` and `alt` form the additive fragment.)

I plan to eventually write a blog series to explain these ideas in more detail, but for now, I hope this code is helpful to anyone trying to understand the original papers.