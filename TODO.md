# TODO

Homework solutions should go in the `Homework.lean` file of their respective chapter and section.

## High priority
- [ ] All of 2.3 except for the basic definitions. We will probably want custom macros so that we can e.g. define an enum `LOAb` with `plus`, `neg`, `zero`, `lt` and have respective syntaxes `+`, `-`, `0`, `<` automatically defined.
- [ ] All of 2.4 onwards

## Medium priority
- [ ] Homeworks for 2.2, which are applications of compactness.
- [ ] The graph coloring example at the end of 2.2 is another application of compactness. It should go in [Coloring](LogicFormalization/Chapter2/Section2/Coloring.lean)

## Low priority
- [ ] Finish some lemmas in 2.1 and HW problem 1. It's just admissibility, hence low priority
- [ ] Isomorphism between admissible words and the inductive definition of `Prop'` and showing that all our relations and functions respect that isomorphism
- [ ] Proof of correctness for parsing admissible words (low priority as it's not in the textbook). See [DecidableReading](LogicFormalization/Chapter2/Section1/DecidableReading.lean)


## Completed
- [x] All of the main results in Chapter 1 and Chapter 2, Section 1 and 2
- [x] The conjunctive/disjunctive normal form problems in C2S1, which we will need later.
- [x] Improve the `p![⬝]` syntax to automatically bring variables into scope. Maybe rename it to `P!`, too