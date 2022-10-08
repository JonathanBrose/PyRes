import textwrap
import unittest
from lexer import Lexer
from clausesets import ClauseSet, IndexedClauseSet
from unification import mgu


def find_complementary_mgu(clause1, lit1, clause2, lit2):
    """
    Finds the most general unifier of two literals if they are complementary
    :param clause1: first clause
    :param lit1: index of literal in clause1
    :param clause2: seconde clause
    :param lit2: index of literal in clause2
    :return: most general unifier if found and if clause1 and clause2 are complementary signed
    """
    l1 = clause1.getLiteral(lit1)
    l2 = clause2.getLiteral(lit2)
    if l1.isNegative() == l2.isNegative():
        return None
    sigma = mgu(l1.atom, l2.atom)
    return sigma


def selectAlternating(litlist, alt_lit_index):
    """
    Selects all literals in litlist for inference, expect the one with the index of alt_lit_index.
    This way we make sure the alternating criterion is met.
    :param litlist: the list of literals to mark for inference
    :param alt_lit_index: the index of the literal that shouldn't be marked for inference
    :return: litlist, but all literal marked for inference, except alt_lit_index
    """
    selected = litlist[:alt_lit_index]
    if len(litlist) - alt_lit_index > 1:
        selected += litlist[alt_lit_index + 1:]
    return selected


class AlternatingPathSelection(object):
    """
    This class initializes and controls the Clause-Selection with Alternating Path
    """
    limit = float('inf')
    start_selected_by = "negated_conjecture"

    def __init__(self, initial_clauses, limit=None, indexed=False, verbose=False, equality_clauses=[]):
        self.clause_count = len(initial_clauses)
        if limit is not None:
            self.limit = limit  # limit how deep the selection is run
        self.indexed = indexed
        self.verbose = verbose
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
        # clauses, for which not all literals have been covered until now
        self.partly_selected = ClauseSet() if not indexed else IndexedClauseSet()

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

    @property
    def selected_count(self):
        return len(self.selected_flat)

    def find_next_paths(self, clause):
        """
        Finds clauses from the unprocessed set that are reachable by an alternating path of length 1
        :param clause: clause to start the search from
        :return: reachable clauses
        """
        if clause in self.unprocessed.clauses:
            self.unprocessed.extractClause(clause)
        #TODO: clean getLiteral into variable instead index
        for lit in range(len(clause)):
            if clause.getLiteral(lit).isInferenceLit():
                partners = self.unprocessed.getResolutionLiterals(clause.getLiteral(lit)) \
                           + self.partly_selected.getResolutionLiterals(clause.getLiteral(lit))
                for (cl2, lit2) in partners:
                    sigma = find_complementary_mgu(clause, lit, cl2, lit2)
                    if sigma is not None:
                        if cl2 not in self.selected_flat:
                            # self.unprocessed.extractClause(cl2)
                            self.selected[-1].append(cl2)
                            if not cl2.isUnit():
                                self.partly_selected.addClause(cl2)
                            cl2.selectInferenceLitsAll(lambda litlist: selectAlternating(litlist, lit2))
                            if self.verbose:
                                print(f"# ({self.depth}) selected {cl2}")
                        elif cl2 in self.partly_selected.clauses and cl2.getLiteral(lit2).isInferenceLit():
                            # multiple paths to a clause means, all literals can now be used for more paths
                            self.partly_selected.extractClause(cl2)
                            self.selected[-1].append(cl2)
                            if cl2 not in self.unprocessed.clauses:
                                inverted_inferencelits = [l for l in cl2.literals if not l.isInferenceLit()]
                                cl2.selectInferenceLitsAll(lambda litlist: inverted_inferencelits)

        if clause not in self.partly_selected.clauses:
            inverted_inferencelits = [l for l in clause.literals if not l.isInferenceLit()]
            clause.selectInferenceLitsAll(lambda litlist: inverted_inferencelits)


# Achtung die level die relevanz level sind instabil....

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

        # reset the inference lits
        selected = self.selected_flat_unique
        for clause in selected:
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
            # Selected per level : {[len(level) for level in self.selected_unique]}
            # All per level      : {[len(level) for level in self.selected]}
            # Max path depth     : {self.depth}
            # Depth limit        : {self.limit}
            # 0-level selected by: {self.start_selected_by}""")

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
