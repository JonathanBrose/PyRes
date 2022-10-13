import textwrap
import unittest
from lexer import Lexer
from clausesets import ClauseSet, IndexedClauseSet
from simple_path_selection import SimplePathSelection
from unification import mgu


class AlternatingPathSelection(SimplePathSelection):
    """
    This class initializes and controls the Clause-Selection with Alternating Path
    """
    def __init__(self, initial_clauses, limit=None, indexed=False, equality_clauses=[]):
        super().__init__(initial_clauses, limit, indexed, equality_clauses)
        # clauses, for which not all literals have been covered until now
        self.partly_processed = ClauseSet() if not indexed else IndexedClauseSet()

    @property
    def selected_flat_unique(self):
        return list(dict.fromkeys(self.selected_flat))

    @property
    def selected_unique(self):
        already_added = []
        unique_levels = []
        for level in self.selected:
            current_level = []
            unique_levels.append(current_level)
            for clause in level:
                if clause in already_added:
                    continue
                already_added.append(clause)
                current_level.append(clause)
        return unique_levels

    def find_next_paths(self, clause):

        def invert_inference_lits(c):
            """invert the inference selection for next time"""
            inverted_inferencelits = [l for l in clause.literals if not l.isInferenceLit()]
            c.selectInferenceLitsAll(lambda litlist: [l for l in litlist if l in inverted_inferencelits])

        def exclude_from_inference_lits(c, lit):
            """ exlcude param lit and select all other"""
            c.selectInferenceLitsAll(lambda litlist: [l for l in litlist if l is not lit])

        unprocessed = clause in self.unprocessed.clauses
        if unprocessed:
            self.unprocessed.extractClause(clause)

        inference_lits = [lit for lit in clause.literals if lit.isInferenceLit()]
        # paths can't start from the same literal again.
        for lit1 in inference_lits:
            unprocessed_partners = self.unprocessed.getResolutionLiterals(lit1)
            partly_selected_partners = self.partly_processed.getResolutionLiterals(lit1)
            partners = {(cl, cl.getLiteral(li)) for cl, li in (unprocessed_partners + partly_selected_partners)}

            for clause2, lit2 in partners:
                if lit1.isNegative() == lit2.isNegative():
                    continue # non complementary pairs are never in an AP
                sigma = mgu(lit1.atom, lit2.atom)
                if sigma is None:
                    continue # if the complementary lits are not unifiable there is not AP with them.

                # in this case we found the first ap to clause2
                if clause2 not in self.selected_flat:
                    self.selected[-1].append(clause2)
                    self.partly_processed.addClause(clause2)
                    exclude_from_inference_lits(clause2, lit2) # there can't be a new AP from this lit2 now.

                # a new ap to clause2 is only necessary if clause2 was not processed on all lits yet.
                elif clause2 in self.partly_processed.clauses and lit2.isInferenceLit():
                    self.selected[-1].append(clause2)
                    if clause2 not in self.unprocessed.clauses: # already processed clause2 will be visited again
                        invert_inference_lits(clause2) # next time we only need to check the lits we haven't yet.
                    self.partly_processed.extractClause(clause2)

        # multiple APs to clause. It will be visited again soon.
        if unprocessed and clause not in self.partly_processed.clauses:
            invert_inference_lits(clause) # next time we only need to check the lits we haven't yet.

    def select_clauses(self):
        def reset_inference_lits(clauses):
            for clause in clauses:
                for lit in clause.literals:
                    lit.setInferenceLit(True)

        selected = super().select_clauses()
        reset_inference_lits(selected)
        return selected


class TestAlternatingPathSelection(unittest.TestCase):
    """
    Unit test class for Alternating Path premise selection
    """

    def setUp(self):
        """
        Setup function for unit tests.
        Initialize the problems that will be used in the tests.
        """
        print()
        self.spec1 = """
            cnf(one_shaved_then_all_shaved,axiom,
                ( ~ member(X)
                | ~ member(Y)
                | ~ shaved(X,Y)
                | shaved(members,X) )).
            
            cnf(all_shaved_then_one_shaved,axiom,
                ( ~ shaved(members,X)
                | ~ member(Y)
                | shaved(Y,X) )).
            
            cnf(guido,hypothesis,
                ( member(guido) )).
            
            cnf(lorenzo,hypothesis,
                ( member(lorenzo) )).
            
            cnf(petruchio,hypothesis,
                ( member(petruchio) )).
            
            cnf(cesare,hypothesis,
                ( member(cesare) )).
            
            cnf(guido_has_shaved_cesare,hypothesis,
                ( shaved(guido,cesare) )).
            
            cnf(prove_petruchio_has_shaved_lorenzo,negated_conjecture,
                ( ~ shaved(petruchio,lorenzo) )).
        """
        self.problem1 = ClauseSet()
        self.problem1.parse(Lexer(self.spec1))

        self.spec2 = """
            cnf(only_cats_in_house,axiom,
                ( ~ in_house(Cat)
                | cat(Cat) )).
            
            cnf(gazers_are_suitable_pets,axiom,
                ( ~ gazer(Gazer)
                | suitable_pet(Gazer) )).
            
            cnf(avoid_detested,axiom,
                ( ~ detested(Detested)
                | avoided(Detested) )).
            
            cnf(carnivores_are_prowlers,axiom,
                ( ~ carnivore(Carnivore)
                | prowler(Carnivore) )).
            
            cnf(cats_are_mice_killers,axiom,
                ( ~ cat(Cat)
                | mouse_killer(Cat) )).
            
            cnf(in_house_if_takes_to_me,axiom,
                ( ~ takes_to_me(Taken_animal)
                | in_house(Taken_animal) )).
            
            cnf(kangaroos_are_not_pets,axiom,
                ( ~ kangaroo(Kangaroo)
                | ~ suitable_pet(Kangaroo) )).
            
            cnf(mouse_killers_are_carnivores,axiom,
                ( ~ mouse_killer(Killer)
                | carnivore(Killer) )).
            
            cnf(takes_to_me_or_detested,axiom,
                ( takes_to_me(Animal)
                | detested(Animal) )).
            
            cnf(prowlers_are_gazers,axiom,
                ( ~ prowler(Prowler)
                | gazer(Prowler) )).
            
            cnf(kangaroo_is_a_kangaroo,axiom,
                ( kangaroo(the_kangaroo) )).
            
            cnf(avoid_kangaroo,negated_conjecture,
                ( ~ avoided(the_kangaroo) )).
        """
        self.problem2 = ClauseSet()
        self.problem2.parse(Lexer(self.spec2))

        self.spec3 = """
            cnf(only_cats_in_house,axiom,
                ( ~ in_house(Cat)
                | cat(Cat) )).
            
            cnf(gazers_are_suitable_pets,axiom,
                ( ~ gazer(Gazer)
                | suitable_pet(Gazer) )).
            
            cnf(avoid_detested,axiom,
                ( ~ detested(Detested)
                | avoided(Detested) )).
            
            cnf(carnivores_are_prowlers,axiom,
                ( ~ carnivore(Carnivore)
                | prowler(Carnivore) )).
            
            cnf(cats_are_mice_killers,axiom,
                ( ~ cat(Cat)
                | mouse_killer(Cat) )).
            
            cnf(in_house_if_takes_to_me,axiom,
                ( ~ takes_to_me(Taken_animal)
                | in_house(Taken_animal) )).
            
            cnf(kangaroos_are_not_pets,axiom,
                ( ~ kangaroo(Kangaroo)
                | ~ suitable_pet(Kangaroo) )).
            
            cnf(mouse_killers_are_carnivores,axiom,
                ( ~ mouse_killer(Killer)
                | carnivore(Killer) )).
            
            cnf(takes_to_me_or_detested,axiom,
                ( takes_to_me(Animal)
                | detested(Animal) )).
            
            cnf(prowlers_are_gazers,axiom,
                ( ~ prowler(Prowler)
                | gazer(Prowler) )).
            
            cnf(kangaroo_is_a_kangaroo,axiom,
                ( kangaroo(the_kangaroo) )).
                
            cnf(avoid_kangaroo,negated_conjecture,
                ( ~ avoided(the_kangaroo) )).
                
            cnf(cat_not_useful,axiom,
                ( ~ useful(Cat)
                | cat(Cat) )).
                
            cnf(kangaroos_are_jumpers,axiom,
                ( ~ kangaroo(Kangaroo)
                | jumper(Kangaroo) )).
        """
        self.problem3 = ClauseSet()
        self.problem3.parse(Lexer(self.spec3))

        self.spec4 = """
            cnf(c,negated_conjecture,
                ( kill(b,a)
                 | drop(c,a))).
                 
            cnf(a1,axiom,
                ( ~ kill(X,Y)
                | hate(X,Y)
                | rich(X,Y))).
                
            cnf(a2,axiom,
                ( ~ drop(X,Y)
                | ~ rich(X,Y))).
            
            cnf(a3,axiom,
                ( drop(a,b))).
        """
        self.problem4 = ClauseSet()
        self.problem4.parse(Lexer(self.spec4))
    def test_initialization(self):
        """
        Test if the initialization works as expected
        """
        ap = AlternatingPathSelection(self.problem1.clauses)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem1.clauses[-1:], ap.selected[0])
        self.assertEqual(self.problem1.clauses[:-1], ap.unprocessed.clauses)

        ap = AlternatingPathSelection(self.problem2.clauses)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem2.clauses[-1:], ap.selected[0])
        self.assertEqual(self.problem2.clauses[:-1], ap.unprocessed.clauses)

        # make sure that setting the limit works
        self.assertEqual(float('inf'), ap.limit)
        ap = AlternatingPathSelection([], limit=8)
        self.assertEqual(8, ap.limit)

    def test_selection(self):
        """
        Test if the correct axioms are selected
        """
        ap = AlternatingPathSelection(self.problem1.clauses)
        selection = ap.select_clauses()
        # check that all clauses of the problem were selected.
        self.assertCountEqual(self.problem1.clauses, selection)

        ap = AlternatingPathSelection(self.problem2.clauses)
        selection = ap.select_clauses()
        # check that all clauses of the problem were selected.
        self.assertCountEqual(self.problem2.clauses, selection)

        ap = AlternatingPathSelection(self.problem3.clauses)
        selection = ap.select_clauses()
        self.assertEqual(12, len(selection))
        # the last two should not be selected
        for clause in self.problem3.clauses[-2:]:
            self.assertNotIn(clause, selection)
        # everything else should be selected
        self.assertCountEqual(self.problem3.clauses[:-2], selection)

        ap = AlternatingPathSelection(self.problem4.clauses)
        selection = ap.select_clauses()
        self.assertCountEqual(self.problem4.clauses, selection)

    def test_indexed_selection(self):
        ap = AlternatingPathSelection(self.problem3.clauses, indexed=True)
        selection = ap.select_clauses()
        self.assertEqual(12, len(selection))
        # the last two should not be selected
        for clause in self.problem3.clauses[-2:]:
            self.assertNotIn(clause, selection)
            # everything else should be selected
        self.assertCountEqual(self.problem3.clauses[:-2], selection)

        ap = AlternatingPathSelection(self.problem4.clauses, indexed=True)
        selection = ap.select_clauses()
        self.assertCountEqual(self.problem4.clauses, selection)

    def test_selection_depth(self):
        ap = AlternatingPathSelection(self.problem1.clauses)
        ap.select_clauses()
        self.assertEqual(3, ap.depth)

        ap = AlternatingPathSelection(self.problem2.clauses)
        ap.select_clauses()
        self.assertEqual(11, ap.depth)

        ap = AlternatingPathSelection(self.problem3.clauses)
        ap.select_clauses()
        self.assertEqual(11, ap.depth)

        ap = AlternatingPathSelection(self.problem4.clauses)
        ap.select_clauses()
        self.assertEqual(3, ap.depth)

    def test_indexed_selection_depth(self):
        ap = AlternatingPathSelection(self.problem1.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(3, ap.depth)

        ap = AlternatingPathSelection(self.problem2.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(11, ap.depth)

        ap = AlternatingPathSelection(self.problem3.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(11, ap.depth)

        ap = AlternatingPathSelection(self.problem4.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(3, ap.depth)

    def test_limit(self):
        """
        Make sure the depth-limit is working
        """
        indices = [11, 2, 8, 5, 0, 4, 7, 3, 9, 1, 6, 10]

        def assert_limit(limit, expected_len):
            self.setUp()
            ap = AlternatingPathSelection(self.problem2.clauses, limit=limit)
            selection = ap.select_clauses()
            self.assertEqual(expected_len, len(selection))

            expected = [self.problem2.clauses[i] for i in indices[:expected_len]]
            self.assertEqual(expected, selection)
            # also checks that elements are ordered by relevance

        assert_limit(1, 2)
        assert_limit(5, 6)
        assert_limit(8, 9)
        assert_limit(20, len(indices))


if __name__ == '__main__':
    unittest.main()
