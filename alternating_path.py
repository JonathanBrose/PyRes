import textwrap
import unittest
from lexer import Lexer
from clausesets import ClauseSet, IndexedClauseSet
from unification import mgu

def find_complementary_mgu(clause1, lit1, clause2, lit2):
    l1 = clause1.getLiteral(lit1)
    l2 = clause2.getLiteral(lit2)
    if l1.isNegative() == l2.isNegative():
        return None
    sigma = mgu(l1.atom, l2.atom)
    return sigma

def selectAlternating(litlist, alt_lit_index):
    selected = litlist[:alt_lit_index]
    if len(litlist) - alt_lit_index > 1:
        selected += litlist[alt_lit_index+1:]
    return selected


class AlternatingPath(object):
    """
    This class is used to select
    """

    def __init__(self, clauses, limit=float('inf'), indexed=False, verbose=False):
        self.clause_count = len(clauses.clauses)
        self.limit = limit  # limit how deep the selection is run
        self.indexed = indexed
        self.verbose = verbose
        # start the algorithm with the conjecture and any other hypotheses etc...
        # the selected clauses are stored as nested lists, one list for each relevance level.
        self.selected = [
            ClauseSet([c for c in clauses.clauses if c.type in ["negated_conjecture"]])
        ]
        # all the other clauses like axioms go into the unprocessed set.
        unprocessed = [c for c in clauses.clauses if c not in self.selected[0].clauses]
        self.unprocessed = ClauseSet(unprocessed) if not indexed else IndexedClauseSet(unprocessed)

    @property
    def depth(self):
        """
        The current relevance depth of the algorithm.
        """
        return len(self.selected) - 1

    @property
    def selected_flat(self):
        """
        Returns all the selected clauses in one flat list
        """
        return ClauseSet([clause for cs in self.selected for clause in cs.clauses])

    @property
    def selected_count(self):
        return len(self.selected_flat)

    def find_next_paths(self, clause):
        """
        Finds clauses from the unprocessed set that are reachable by an alternating path of length 1
        :param clause: clause to start the search from
        :return: reachable clauses
        """

        for lit in range(len(clause)):
            if clause.getLiteral(lit).isInferenceLit():
                partners = self.unprocessed.getResolutionLiterals(clause.getLiteral(lit))
                for (cl2, lit2) in partners:
                    sigma = find_complementary_mgu(clause, lit, cl2, lit2)
                    #  If we find a unifier that results in a complementary literal pair,
                    #  then we add the new clause to the list if it is not already in.
                    #  This way duplicates are avoided upfront.
                    if sigma is not None:
                        if cl2 not in self.selected_flat.clauses:
                            self.unprocessed.extractClause(cl2)
                            cl2.selectInferenceLitsAll(lambda litlist: selectAlternating(litlist, lit2))
                            self.selected[-1].addClause(cl2)
                            if self.verbose:
                                print(f"# ({self.depth}) selected {cl2}")
                        else:
                            # multiple paths to a clause means, all literals can now be used for more paths
                            cl2.selectInferenceLitsAll(lambda litlist: litlist)

    def select_clauses(self):
        """
        Main loop to find the relevant clauses.
        For each iteration the clauses of relevance k are found.
        k=0 relevant items are the conjectures and hypotheses.
        k=1 are the clauses reachable with an alternating path of length 1 and so on.
        The loop stops when all relevant clauses are processed, or if the depth-limit is reached.
        :return: ClauseSet with the selected clauses
        """
        while self.depth < self.limit and self.unprocessed.clauses:
            current_level = self.selected[-1]
            next_level = ClauseSet()
            self.selected.append(next_level)

            # for each clause of the current relevance level we check for more paths
            for clause in current_level.clauses:
                self.find_next_paths(clause)

            # if we didn't find any new paths, we stop.
            if not next_level.clauses:
                break

        # reset the inference lits
        selected = self.selected_flat
        for clause in selected.clauses:
            for lit in clause.literals:
                lit.setInferenceLit(True)
        return selected

    def statistics_str(self):
        """
        Return the selection statistics in string form ready for
        output.
        """
        return textwrap.dedent(f"""\
            # Initial clauses    : {self.clause_count}
            # Selected clauses   : {self.selected_count}
            # Max path depth     : {self.depth}
            # Depth limit        : {self.limit}""")


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
        self.assertEqual(self.problem1.clauses[-1:], ap.selected[0].clauses)
        self.assertEqual(self.problem1.clauses[:-1], ap.unprocessed.clauses)

        ap = AlternatingPath(self.problem2)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem2.clauses[-1:], ap.selected[0].clauses)
        self.assertEqual(self.problem2.clauses[:-1], ap.unprocessed.clauses)

        # make sure that setting the limit works
        self.assertEqual(float('inf'), ap.limit)
        ap = AlternatingPath(self.problem1, limit=8)
        self.assertEqual(8, ap.limit)

    def test_selection(self):
        """
        Test if the correct axioms are selected
        """
        ap = AlternatingPath(self.problem1)
        selection = ap.select_clauses()
        # check that all clauses of the problem were selected.
        for clause in self.problem1.clauses:
            self.assertIn(clause, selection.clauses)

        ap = AlternatingPath(self.problem2)
        selection = ap.select_clauses()
        # check that all clauses of the problem were selected.
        for clause in self.problem2.clauses:
            self.assertIn(clause, selection.clauses)

        ap = AlternatingPath(self.problem3)
        selection = ap.select_clauses()
        self.assertEqual(12, len(selection))
        # the last two should not be selected
        for clause in self.problem3.clauses[-2:]:
            self.assertNotIn(clause, selection.clauses)
        # everything else should be selected
        for clause in self.problem3.clauses[:-2]:
            self.assertIn(clause, selection.clauses)

    def test_indexed_selection(self):
        ap = AlternatingPath(self.problem3, indexed=True)
        selection = ap.select_clauses()
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
            self.setUp()
            ap = AlternatingPath(self.problem2, limit=limit)
            selection = ap.select_clauses()
            self.assertEqual(expected_len, len(selection))

            for clause, i in zip(selection.clauses, indices[:expected_len]):
                self.assertEqual(self.problem2.clauses[i], clause)

        assert_limit(1, 2)
        assert_limit(5, 6)
        assert_limit(8, 9)
        assert_limit(20, len(indices))

if __name__ == '__main__':
    unittest.main()
