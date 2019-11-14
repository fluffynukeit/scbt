# scbt
Implements "Sound and Complete Bidirectional Typechecking..." by Dunfield and Krishnaswami, POPL 2019.
It is a newly published algorithm for typechecking and inference allowing indexed types (GADTs), although
they had been working on it for quite some time prior to its publication.

The "Sound and Complete" paper is the follow up to their "Complete and Easy Bidirectional Typechecking..."
paper from 2013.  (I believe C&E is the basis for typechecking and inference in the Purescipt language).

## The paper

The published POPL 2019 paper is version 3, but the appendix with full rules and proofs is omitted.
Version 2 is the more complete version.

Link to the arxiv main page (v2): https://arxiv.org/abs/1601.05106v2

Direct PDF link (v2): https://arxiv.org/pdf/1601.05106v2.pdf

## Implementation goals

- Correctly implement the algorithms in the paper
- Match the paper's mathematical notation as closely as is reasonable
- Allow the library to be used as a viable type-checking and inference algorithm for new language implementations

## Notational differences

Some operators in the paper are implemented as Haskell constructors, which requires they begin with a `:`.  For
cases in which the operator does not already begin with a colon or is reserved, the operator is sandwiched between
colons.  For example, `+` becomes `:+:`.  As another example, Haskel reserves both `:` and `::` operators, so they
are converted to `:::` and `::::` respectively.

For other cases, the operator is translated directly when possible (e.g., `:=`) or an alternative notation is introduced
that conforms with Haskell's syntax rules.

## Other implementations

This implementation is inspired by Soham Chowdhury's partial (at time of this writing) implementation of
the rules in earlier drafts of Sound and Complete, and for which he is credited in the published paper.
His compilation of bidirectional typechecking resources and his reference code helped me make sense of
the paper as well as the ecosystem surrounding modern typechecking, to which I was unfamiliar.  

As I understood more, I wanted to try a different approach that was structured more similarly to the 
published mathematical expressions.

Soham's original implementation: https://github.com/mrkgnao/sound-and-complete/

