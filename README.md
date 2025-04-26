# lean-logic-formalization

This is a Lean 4 formalization of the logic textbook "Logic Notes" by Lou van den Dries. We use the [Fall 2019 edition](https://www.studocu.vn/vn/document/truong-dai-hoc-cong-nghiep-thanh-pho-ho-chi-minh/cau-truc-roi-rac/logic-math/34117438), but the only official link seems to be for the [Fall 2007 edition](https://www.karlin.mff.cuni.cz/~krajicek/vddries.pdf). Most things should be the same.

The textbook treats propositions, terms, formulas, sentences, etc. as "admissible words" (defined inductively) over some alphabet with arities defined for symbols. However, in Lean it is much more natural to think of these constructs as inductive types. For example, we get unique readability (constructor injectivity) for free with inductive types, and matching is much more ergonomic. (Even the textbook admits that we should think of these as trees.) We still prove all the results about admissible words in [Chapter2.Section1.Admissibility](LogicFormalization/Chapter2/Section1/Admissibility.lean), even though we don't use them. At some point I might prove isomorphism between the two notions.

**Everyone is welcome to contribute. I am still learning Lean, so if there is something that I'm not doing correctly, please speak up!**

## Remaining work:
- [ ] Finish some lemmas in 2.1
- [ ] Homeworks for 2.1,
- [x] ~especially the conjunctive/disjunctive normal form problems, which we will need later. Those results specifically will go in [NormalForms](LogicFormalization/Chapter2/Section1/NormalForms.lean)~
- [ ] Isomorphism between admissible words and the inductive definition of `Prop'`. Low priority
- [ ] Proof of correctness for parsing admissible words (low priority as it's not in the textbook). See [DecidableReading](LogicFormalization/Chapter2/Section1/DecidableReading.lean)
- [ ] Improve the `p![⬝]` syntax to automatically bring variables into scope. Maybe rename it to `P!`, too
- [ ] Homeworks for 2.2, which are applications of compactness.
- [ ] The graph coloring example at the end of 2.2 is another application of compactness. It should go in [Coloring](LogicFormalization/Chapter2/Section2/Coloring.lean)
- [ ] All of 2.3 except for the basic definitions. We will probably want custom macros so that we can e.g. define an enum `LOAb` with `plus`, `neg`, `zero`, `lt` and have respective syntaxes `+`, `-`, `0`, `<` automatically defined.
- [ ] All of 2.4 onwards

Homework solutions should go in the `Homework.lean` file of their respective chapter and section.
