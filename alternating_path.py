import unittest
from lexer import Lexer
from clausesets import ClauseSet
from unification import mgu


# TODO: Sonderbehandlung für equality ??

def find_complementary_mgu(clause1, lit1, clause2, lit2):
    l1 = clause1.getLiteral(lit1)
    l2 = clause2.getLiteral(lit2)
    if l1.isNegative() == l2.isNegative():
        return None
    sigma = mgu(l1.atom, l2.atom)
    return sigma


class AlternatingPath(object):

    def __init__(self, clauses, limit=float('inf')):
        self.limit = limit  # limit how deep the selection is run
        # start the algorithmen with the conjecture and any other hypotheses etc...
        self.selected = ClauseSet([c for c in clauses.clauses if c.type in ["negated_conjecture", "plain"]])
        # all the other clauses like axioms go into the unprocessed set.
        self.unprocessed = ClauseSet([c for c in clauses.clauses if c not in self.selected.clauses])
        # the path_levels contain a mapping of
        self.path_levels = [
            [(sci, -1) for sci in range(len(self.selected))]  # level zero contains the starting clauses
        ]  # schema for each level = [(selected_clause_index, lit_index)]

    def move_to_selected(self, clause):
        """
        Moves the clause from self.unprocessed to self.selected and returns the index in self.selected
        :param clause: the clause to move
        :return: the index auf clause in the selected list
        """
        if clause in self.unprocessed.clauses:
            self.unprocessed.clauses.remove(clause)
        try:
            return self.selected.clauses.index(clause)
        except ValueError:
            self.selected.addClause(clause)
            return len(self.selected.clauses) - 1

    @property
    def depth(self):
        """
        The current relevance depth of the algorithm.
        """
        return len(self.path_levels) - 1

    def find_next_paths(self, clause_index, lit_index):
        """
        Finds clauses from the unprocessed set that are reachable by an alternating path of length 1
        :param clause_index: clause_index to start the search from
        :param lit_index: literal_index that should be disabled in clause
        to fulfill the alternating path condition of a literal switch
        :return: reachable clauses
        """
        paths = []
        clause = self.selected.clauses[clause_index]
        for lit in range(len(clause)):
            if lit == lit_index:  # skip the literal that was last used in the path
                continue
            if clause.getLiteral(lit).isInferenceLit():
                partners = \
                    self.unprocessed.getResolutionLiterals(clause.getLiteral(lit))
                for (cl2, lit2) in partners:
                    sigma = find_complementary_mgu(clause, lit, cl2, lit2)
                    # If we find a mgu that results in a complementary literal pair,
                    # the condition for an alternating path is met.
                    # (We made sure that we are switching literals above)

                    if sigma is not None:
                        paths.append((cl2, lit2))
                        # Then we add the clause index with the connecting literal index as a path.
        return paths

    def saturate(self):
        """
        Main loop to find the relevant clauses.
        For each iteration the clauses of relevance k are found.
        k=0 relevant items are the conjectures and hypotheses.
        k=1 are the clauses reachable with an alternating path of length 1 and so on.
        The loop stops when all relevant clauses are processed, or if the depth-limit is reached.
        :return: ClauseSet with the selected clauses
        """
        while self.depth < self.limit:
            current_level = self.path_levels[-1]
            new_paths = []
            # Iterate over the clauses
            for clause_index, lit_index in current_level:
                new_paths += self.find_next_paths(clause_index, lit_index)

            # If we didn't find any new paths, we stop.
            if not new_paths:
                break

            # Move the now used clauses from unprocessed to selected
            next_level = [(self.move_to_selected(c), lit_index) for c, lit_index in new_paths]
            self.path_levels.append(next_level)

        return self.selected


class TestAlternatingPath(unittest.TestCase):
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

    def test_initialization(self):
        """
        Test if the initialization works as expected
        """
        ap = AlternatingPath(self.problem1)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem1.clauses[2:], ap.selected.clauses)
        self.assertEqual(self.problem1.clauses[:2], ap.unprocessed.clauses)
        self.assertEqual([(0, -1), (1, -1), (2, -1), (3, -1), (4, -1), (5, -1)], ap.path_levels[0])

        ap = AlternatingPath(self.problem2)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem2.clauses[-1:], ap.selected.clauses)
        self.assertEqual(self.problem2.clauses[:-1], ap.unprocessed.clauses)
        self.assertEqual([(0, -1)], ap.path_levels[0])

        # make sure that setting the limit works
        self.assertEqual(float('inf'), ap.limit)
        ap = AlternatingPath(self.problem1, limit=8)
        self.assertEqual(8, ap.limit)

    def test_selection(self):
        """
        Test if the correct axioms are selected
        """
        ap = AlternatingPath(self.problem1)
        selection = ap.saturate()
        # check that all clauses of the problem were selected.
        for clause in self.problem1.clauses:
            self.assertIn(clause, selection.clauses)

        ap = AlternatingPath(self.problem2)
        selection = ap.saturate()
        # check that all clauses of the problem were selected.
        for clause in self.problem2.clauses:
            self.assertIn(clause, selection.clauses)

        ap = AlternatingPath(self.problem3)
        selection = ap.saturate()
        self.assertEqual(12, len(selection))
        # the last two should not be selected
        for clause in self.problem3.clauses[-2:]:
            self.assertNotIn(clause, selection.clauses)
        # everything else should be selected
        for clause in self.problem3.clauses[:-2]:
            self.assertIn(clause, selection.clauses)

    def test_limit(self):
        """
        Make sure the depth-limit is working
        """
        indices = [11, 2, 8, 5, 0, 4, 7, 3, 9, 1, 6, 10]

        def assert_limit(limit, expected_len):
            ap = AlternatingPath(self.problem2, limit=limit)
            selection = ap.saturate()
            self.assertEqual(expected_len, len(selection))

            for clause, i in zip(selection.clauses, indices[:expected_len]):
                self.assertEqual(self.problem2.clauses[i], clause)

        assert_limit(1, 2)
        assert_limit(5, 6)
        assert_limit(8, 9)
        assert_limit(20, len(indices))

    def test_still_solvable(self):
        """
        Test if the reduced Problem is still solvable by pyres
        """
        # TODO: Example for testing is missing
        pass


if __name__ == '__main__':
    unittest.main()
