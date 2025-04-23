# lean-logic-formalization

This is a Lean 4 formalization of the logic textbook "Logic Notes" by Lou van den Dries. We use the [Fall 2019 edition](https://www.studocu.vn/vn/document/truong-dai-hoc-cong-nghiep-thanh-pho-ho-chi-minh/cau-truc-roi-rac/logic-math/34117438), but the only official link seems to be for the [Fall 2007 edition](https://www.karlin.mff.cuni.cz/~krajicek/vddries.pdf). Most things should be the same.

The textbook treats propositions, terms, formulas, sentences, etc. as "admissible words" (defined inductively) over some alphabet with arities defined for symbols. However, in Lean it is much more natural to think of these constructs as inductive types. (Even the textbook admits that we should think of these as trees.) We still prove all the results about admissible words in `Chapter2.Section1.Admissibility`, even though we don't use them. At some point I might prove isomorphism between the two notions.

**Everyone is welcome to contribute. I am still learning Lean, so if there is something that I'm not doing correctly, please speak up!**