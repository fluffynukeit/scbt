# scbt
Implements "Sound and Complete Bidirectional Typechecking..." by Dunfield and Krishnaswami, POPL 2019

The "Sound and Complete" paper is the follow up to their "Complete and Easy Bidirectional Typechecking..."
paper from 2013.  Sound and Complete allows indexed types (GADTS).

Link to the arxiv: https://arxiv.org/abs/1601.05106

This implementation is inspired by Soham Chowdhury's partial (at time of this writing) implementation of
the rules in earlier drafts of Sound and Complete, and for which he is credited in the published paper.
His compilation of bidirectional typechecking resources and his reference code helped me make sense of
the paper as well as the ecosystem surrounding modern typechecking.  As I understood more, I wanted to 
try a different approach that was structured more similarly to the published mathematical expressions.

Soham's original implementation: https://github.com/mrkgnao/sound-and-complete/

