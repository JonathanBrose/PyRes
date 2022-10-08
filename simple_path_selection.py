import textwrap
import unittest
from lexer import Lexer
from clausesets import ClauseSet, IndexedClauseSet
from unification import mgu


class SimplePathSelection(object):
    """
    This class initializes and controls the Clause-Selection with Alternating Path
    """
    limit = float('inf')
    start_selected_by = "negated_conjecture"

    def __init__(self, initial_clauses, limit=None, indexed=False, equality_clauses=[]):
        self.clause_count = len(initial_clauses)
        if limit is not None:
            self.limit = limit  # limit how deep the selection is run
        self.indexed = indexed
        # start the algorithm with the conjecture and any other hypotheses etc...
        # the selected clauses are stored as nested lists, one list for each relevance level.
        self.selected = [
            [c for c in initial_clauses if c.type in ["negated_conjecture"]]
        ]
        if not self.selected[0]:
            self.selected[0] = [c for c in initial_clauses if c.type in ["plain"] and c not in equality_clauses]
            self.start_selected_by = "plain"
        if not self.selected[0]:
            self.selected[0] = [c for c in initial_clauses]
            self.start_selected_by = "all"
        # all the other clauses like axioms go into the unprocessed set.
        unprocessed = [c for c in initial_clauses if c not in self.selected[0]]
        self.unprocessed = ClauseSet(unprocessed) if not indexed else IndexedClauseSet(unprocessed)

    @property
    def depth(self):
        """
        The current relevance depth of the algorithm.
        """
        return len(self.selected_unique) - 1

    @property
    def selected_flat(self):
        """
        Returns all the selected clauses in one flat list
        """
        return [clause for cs in self.selected for clause in cs]

    @property
    def selected_flat_unique(self):
        return self.selected_flat

    @property
    def selected_unique(self):
        return self.selected

    @property
    def selected_count(self):
        return len(self.selected_flat_unique)

    def find_next_paths(self, clause):

        unprocessed = clause in self.unprocessed.clauses
        if unprocessed:
            self.unprocessed.extractClause(clause)

        inference_lits = [lit for lit in clause.literals if lit.isInferenceLit()]
        # paths can't start from the same literal again.
        for lit1 in inference_lits:
            unprocessed_partners = self.unprocessed.getResolutionLiterals(lit1)
            partners = {(cl, cl.getLiteral(li)) for cl, li in unprocessed_partners}

            for clause2, lit2 in partners:
                if lit1.isNegative() == lit2.isNegative():
                    continue # non complementary pairs are never in an AP
                sigma = mgu(lit1.atom, lit2.atom)
                if sigma is None:
                    continue # if the complementary lits are not unifiable there is not AP with them.

                # in this case we found the first ap to clause2
                if clause2 not in self.selected_flat:
                    self.selected[-1].append(clause2)

    def select_clauses(self):
        """
        Main loop to find the relevant clauses.
        For each iteration the clauses of relevance k are found.
        k=0 relevant items are the negated conjectures
        k=1 are the clauses reachable with an alternating path of length 1 and so on.
        The loop stops when all relevant clauses are processed, or if the depth-limit is reached.
        :return: selected clauses
        """
        while self.unprocessed.clauses and self.depth < self.limit:
            current_level = self.selected[-1]
            next_level = []
            self.selected.append(next_level)

            # for each clause of the current relevance level we check for more paths
            for clause in current_level:
                self.find_next_paths(clause)

            # if we didn't find any new paths, we stop.
            if not next_level:
                self.selected.pop()
                break

        selected = self.selected_flat_unique
        return selected

    def statistics_str(self):
        """
        Return the selection statistics in string form ready for
        output.
        """
        return textwrap.dedent(f"""\
            # Initial clauses    : {self.clause_count}
            # Selected clauses   : {self.selected_count}
            # Selected per level : {[len(level) for level in self.selected_unique]}
            # All per level      : {[len(level) for level in self.selected]}
            # Max path depth     : {self.depth}
            # Depth limit        : {self.limit}
            # 0-level selected by: {self.start_selected_by}""")


class TestSimplePathSelection(unittest.TestCase):
    """
    Unit test class for Simple (Alternating) Path premise selection
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
                 | kill(c,a))).
                 
            cnf(a1,axiom,
                ( ~ kill(X,Y)
                | hate(X,Y)
                | rich(X,Y))).
                
            cnf(a2,axiom,
                ( ~ kill(X,Y)
                | ~ rich(X,Y))).
            
            cnf(a3,axiom,
                ( kill(a,b))).
        """
        self.problem4 = ClauseSet()
        self.problem4.parse(Lexer(self.spec4))

    def test_initialization(self):
        """
        Test if the initialization works as expected
        """
        ap = SimplePathSelection(self.problem1.clauses)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem1.clauses[-1:], ap.selected[0])
        self.assertEqual(self.problem1.clauses[:-1], ap.unprocessed.clauses)

        ap = SimplePathSelection(self.problem2.clauses)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem2.clauses[-1:], ap.selected[0])
        self.assertEqual(self.problem2.clauses[:-1], ap.unprocessed.clauses)

        # make sure that setting the limit works
        self.assertEqual(float('inf'), ap.limit)
        ap = SimplePathSelection([], limit=8)
        self.assertEqual(8, ap.limit)

    def test_selection(self):
        """
        Test if the correct axioms are selected
        """
        ap = SimplePathSelection(self.problem1.clauses)
        selection = ap.select_clauses()
        # check that all clauses of the problem were selected.
        self.assertCountEqual(self.problem1.clauses, selection)

        ap = SimplePathSelection(self.problem2.clauses)
        selection = ap.select_clauses()
        # check that all clauses of the problem were selected.
        self.assertCountEqual(self.problem2.clauses, selection)

        ap = SimplePathSelection(self.problem3.clauses)
        selection = ap.select_clauses()
        self.assertCountEqual(self.problem3.clauses, selection)

        ap = SimplePathSelection(self.problem4.clauses)
        selection = ap.select_clauses()
        self.assertCountEqual(self.problem4.clauses, selection)

    def test_indexed_selection(self):
        ap = SimplePathSelection(self.problem3.clauses, indexed=True)
        selection = ap.select_clauses()
        selection = ap.select_clauses()
        self.assertCountEqual(self.problem3.clauses, selection)

        ap = SimplePathSelection(self.problem4.clauses, indexed=True)
        selection = ap.select_clauses()
        self.assertCountEqual(self.problem4.clauses, selection)

    def test_selection_depth(self):
        ap = SimplePathSelection(self.problem1.clauses)
        ap.select_clauses()
        self.assertEqual(3, ap.depth)

        ap = SimplePathSelection(self.problem2.clauses)
        ap.select_clauses()
        self.assertEqual(11, ap.depth)

        ap = SimplePathSelection(self.problem3.clauses)
        ap.select_clauses()
        self.assertEqual(12, ap.depth)

        ap = SimplePathSelection(self.problem4.clauses)
        ap.select_clauses()
        self.assertEqual(2, ap.depth)

    def test_indexed_selection_depth(self):
        ap = SimplePathSelection(self.problem1.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(3, ap.depth)

        ap = SimplePathSelection(self.problem2.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(11, ap.depth)

        ap = SimplePathSelection(self.problem3.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(12, ap.depth)

        ap = SimplePathSelection(self.problem4.clauses, indexed=True)
        ap.select_clauses()
        self.assertEqual(2, ap.depth)

    def test_limit(self):
        """
        Make sure the depth-limit is working
        """
        indices = [11, 2, 8, 5, 0, 4, 7, 3, 9, 1, 6, 10]

        def assert_limit(limit, expected_len):
            self.setUp()
            ap = SimplePathSelection(self.problem2.clauses, limit=limit)
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
