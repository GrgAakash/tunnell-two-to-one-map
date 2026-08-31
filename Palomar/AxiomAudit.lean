import Solution
import Palomar.EntryB.Solution

/-!
# Axiom audit for every Comparator-selected declaration

Building this module prints the axiom dependencies of both submitted
definition values and every theorem selected by the two Comparator files.
-/

#print axioms TunnellChallenge.tunnellMap
#print axioms TunnellChallenge.tunnellMap_exactly_two
#print axioms TunnellChallenge.tunnellMap_even
#print axioms TunnellChallenge.tunnellMap_quarterTurn_one
#print axioms TunnellChallenge.tunnellMap_quarterTurn_two
#print axioms TunnellChallenge.tunnellMap_quarterTurn_three
#print axioms TunnellChallenge.tunnellMap_residual_target
#print axioms TunnellChallenge.tunnellMap_residual_stable
#print axioms TunnellChallenge.tunnellResidualMap
#print axioms TunnellChallenge.tunnellResidualInverse
#print axioms TunnellChallenge.tunnellResidualMap_agrees
#print axioms TunnellChallenge.tunnellResidualInverse_left
#print axioms TunnellChallenge.tunnellResidualInverse_right

#print axioms TunnellN41.tunnellMap41
#print axioms TunnellN41.daTrace41
#print axioms TunnellN41.card_BRep_41
#print axioms TunnellN41.card_ARep_41
#print axioms TunnellN41.tunnellMap41_exactly_two
#print axioms TunnellN41.residualPairs_41
#print axioms TunnellN41.fibre_direct_41
#print axioms TunnellN41.fibre_residual_41
#print axioms TunnellN41.daTrace41_eq
#print axioms TunnellN41.daTrace41_length
#print axioms TunnellN41.daTrace41_nonaccepting
#print axioms TunnellN41.daTrace41_accepted_image
