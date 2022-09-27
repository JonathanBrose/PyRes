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
    """
    This class is used to select
    """

    def __init__(self, clauses, limit=float('inf')):
        self.limit = limit  # limit how deep the selection is run

        # start the algorithmen with the conjecture and any other hypotheses etc...
        # the selected clauses are stored as nested lists, one list for each relevance level.
        self.selected = [
            ClauseSet([c for c in clauses.clauses if c.type in ["negated_conjecture", "plain"]])
        ]
        # all the other clauses like axioms go into the unprocessed set.
        self.unprocessed = ClauseSet([c for c in clauses.clauses if c not in self.selected[0].clauses])

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

    def find_next_paths(self, clause):
        """
        Finds clauses from the unprocessed set that are reachable by an alternating path of length 1
        :param clause: clause to start the search from
        :return: reachable clauses
        """
        path_clauses = []
        for lit in range(len(clause)):
            if clause.getLiteral(lit).isInferenceLit():
                partners = \
                    self.unprocessed.getResolutionLiterals(clause.getLiteral(lit))
                for (cl2, lit2) in partners:
                    sigma = find_complementary_mgu(clause, lit, cl2, lit2)
                    #  If we find a unifier that results in a complementary literal pair,
                    #  then we add the new clause to the list if it is not already in.
                    #  This way duplicates are avoided upfront.
                    if sigma is not None and cl2 not in path_clauses:
                        path_clauses.append(cl2)
        return path_clauses

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
            current_level = self.selected[-1]
            next_level = ClauseSet()
            self.selected.append(next_level)

            # for each clause of the current relevance level we check for more paths
            for clause in current_level.clauses:
                path_clauses = self.find_next_paths(clause)

                # move the new clauses from unprocessed to selected.
                for c in path_clauses:
                    self.unprocessed.clauses.remove(c)
                    next_level.addClause(c)

            # if we didn't find any new paths, we stop.
            if not next_level.clauses:
                break

        return self.selected_flat


class TestAlternatingPath(unittest.TestCase):
    """
    Unit test class for Alternating Path premise selection
    """

    def setUp(self):
        """
        Setup function for unit tests. Initialize
        variables needed throughout the tests.
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
            %---- Live in one of the houses
            cnf(people_live_somewhere,axiom,
                ( ~ person(Person)
                | lives(Person,house_1)
                | lives(Person,house_2)
                | lives(Person,house_3)
                | lives(Person,house_4)
                | lives(Person,house_5) ) ).
            
            %---- uniqueness.
            cnf(english_and_spaniard_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(english,H)
                | ~ lives(spaniard,H) ) ).
            
            cnf(english_and_norwegian_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(english,H)
                | ~ lives(norwegian,H) ) ).
            
            cnf(english_and_ukranian_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(english,H)
                | ~ lives(ukranian,H) ) ).
            
            cnf(english_and_japanese_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(english,H)
                | ~ lives(japanese,H) ) ).
            
            cnf(spaniard_and_norwegian_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(spaniard,H)
                | ~ lives(norwegian,H) ) ).
            
            cnf(spaniard_and_ukranian_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(spaniard,H)
                | ~ lives(ukranian,H) ) ).
            
            cnf(spaniard_and_japanese_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(spaniard,H)
                | ~ lives(japanese,H) ) ).
            
            cnf(norwegian_and_ukranian_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(norwegian,H)
                | ~ lives(ukranian,H) ) ).
            
            cnf(norwegian_and_japanese_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(norwegian,H)
                | ~ lives(japanese,H) ) ).
            
            cnf(ukranian_and_japanese_live_apart,axiom,
                ( ~ house(H)
                | ~ lives(ukranian,H)
                | ~ lives(japanese,H) ) ).
            
            %---- Drink one of the drinks
            cnf(drink_something,axiom,
                ( ~ person(Person)
                | drinks(Person,orange)
                | drinks(Person,coffee)
                | drinks(Person,tea)
                | drinks(Person,milk)
                | drinks(Person,water) ) ).
            
            %---- uniqueness.
            cnf(english_and_spaniard_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(english,H)
                | ~ drinks(spaniard,H) ) ).
            
            cnf(english_and_norwegian_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(english,H)
                | ~ drinks(norwegian,H) ) ).
            
            cnf(english_and_unkranian_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(english,H)
                | ~ drinks(ukranian,H) ) ).
            
            cnf(english_and_japanese_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(english,H)
                | ~ drinks(japanese,H) ) ).
            
            cnf(spaniard_and_norwegian_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(spaniard,H)
                | ~ drinks(norwegian,H) ) ).
            
            cnf(spaniard_and_ukranian_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(spaniard,H)
                | ~ drinks(ukranian,H) ) ).
            
            cnf(spaniard_and_japanese_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(spaniard,H)
                | ~ drinks(japanese,H) ) ).
            
            cnf(norwegian_and_ukranian_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(norwegian,H)
                | ~ drinks(ukranian,H) ) ).
            
            cnf(norwegian_and_japanese_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(norwegian,H)
                | ~ drinks(japanese,H) ) ).
            
            cnf(ukranian_and_japanese_drink_different,axiom,
                ( ~ drink(H)
                | ~ drinks(ukranian,H)
                | ~ drinks(japanese,H) ) ).
            
            %---- Somke some brand
            cnf(drive_something,axiom,
                ( ~ person(Person)
                | drives(Person,masserati)
                | drives(Person,saab)
                | drives(Person,porsche)
                | drives(Person,honda)
                | drives(Person,jaguar) ) ).
            
            %---- uniqueness.
            cnf(english_and_spaniard_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(english,H)
                | ~ drives(spaniard,H) ) ).
            
            cnf(english_and_norwegian_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(english,H)
                | ~ drives(norwegian,H) ) ).
            
            cnf(english_and_ukranian_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(english,H)
                | ~ drives(ukranian,H) ) ).
            
            cnf(english_and_japanese_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(english,H)
                | ~ drives(japanese,H) ) ).
            
            cnf(spaniard_and_norwegian_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(spaniard,H)
                | ~ drives(norwegian,H) ) ).
            
            cnf(spaniard_and_ukranian_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(spaniard,H)
                | ~ drives(ukranian,H) ) ).
            
            cnf(spaniard_and_japanese_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(spaniard,H)
                | ~ drives(japanese,H) ) ).
            
            cnf(norwegian_and_ukranian_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(norwegian,H)
                | ~ drives(ukranian,H) ) ).
            
            cnf(norwegian_and_japanese_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(norwegian,H)
                | ~ drives(japanese,H) ) ).
            
            cnf(ukranian_and_japanese_drive_different,axiom,
                ( ~ car(H)
                | ~ drives(ukranian,H)
                | ~ drives(japanese,H) ) ).
            
            %---- Own one of the pets
            cnf(own_a_pet,axiom,
                ( ~ person(Person)
                | owns(Person,dog)
                | owns(Person,snails)
                | owns(Person,horse)
                | owns(Person,fox)
                | owns(Person,zebra) ) ).
            
            %---- uniqueness.
            cnf(english_and_spaniard_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(english,H)
                | ~ owns(spaniard,H) ) ).
            
            cnf(english_and_norwegian_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(english,H)
                | ~ owns(norwegian,H) ) ).
            
            cnf(english_and_ukranian_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(english,H)
                | ~ owns(ukranian,H) ) ).
            
            cnf(english_and_japanese_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(english,H)
                | ~ owns(japanese,H) ) ).
            
            cnf(spaniard_and_norwegian_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(spaniard,H)
                | ~ owns(norwegian,H) ) ).
            
            cnf(spaniard_and_ukranian_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(spaniard,H)
                | ~ owns(ukranian,H) ) ).
            
            cnf(spaniard_and_japanese_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(spaniard,H)
                | ~ owns(japanese,H) ) ).
            
            cnf(norwegian_and_ukranian_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(norwegian,H)
                | ~ owns(ukranian,H) ) ).
            
            cnf(norwegian_and_japanese_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(norwegian,H)
                | ~ owns(japanese,H) ) ).
            
            cnf(ukranian_and_japanese_own_different_pets,axiom,
                ( ~ animal(H)
                | ~ owns(ukranian,H)
                | ~ owns(japanese,H) ) ).
            
            %---- Houses are coloured
            cnf(house_coloured,axiom,
                ( ~ house(H)
                | is_color(H,red)
                | is_color(H,yellow)
                | is_color(H,blue)
                | is_color(H,green)
                | is_color(H,ivory) ) ).
            
            %---- uniqueness.
            cnf(houses_1_and_2_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_1,H)
                | ~ is_color(house_2,H) ) ).
            
            cnf(houses_1_and_3_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_1,H)
                | ~ is_color(house_3,H) ) ).
            
            cnf(houses_1_and_4_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_1,H)
                | ~ is_color(house_4,H) ) ).
            
            cnf(houses_1_and_5_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_1,H)
                | ~ is_color(house_5,H) ) ).
            
            cnf(houses_2_and_3_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_2,H)
                | ~ is_color(house_3,H) ) ).
            
            cnf(houses_2_and_4_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_2,H)
                | ~ is_color(house_4,H) ) ).
            
            cnf(houses_2_and_5_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_2,H)
                | ~ is_color(house_5,H) ) ).
            
            cnf(houses_3_and_4_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_3,H)
                | ~ is_color(house_4,H) ) ).
            
            cnf(houses_3_and_5_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_3,H)
                | ~ is_color(house_5,H) ) ).
            
            cnf(houses_4_and_5_coloured_different,axiom,
                ( ~ color(H)
                | ~ is_color(house_4,H)
                | ~ is_color(house_5,H) ) ).
            
            %---- These are the people
            cnf(english,axiom,
                person(english) ).
            
            cnf(spaniard,axiom,
                person(spaniard) ).
            
            cnf(norwegian,axiom,
                person(norwegian) ).
            
            cnf(ukranian,axiom,
                person(ukranian) ).
            
            cnf(japanese,axiom,
                person(japanese) ).
            
            %---- These are the house numbers
            cnf(house_house_1,axiom,
                house(house_1) ).
            
            cnf(house_house_2,axiom,
                house(house_2) ).
            
            cnf(house_house_3,axiom,
                house(house_3) ).
            
            cnf(house_house_4,axiom,
                house(house_4) ).
            
            cnf(house_house_5,axiom,
                house(house_5) ).
            
            %---- These are the colours
            cnf(red,axiom,
                color(red) ).
            
            cnf(green,axiom,
                color(green) ).
            
            cnf(yellow,axiom,
                color(yellow) ).
            
            cnf(ivory,axiom,
                color(ivory) ).
            
            cnf(blue,axiom,
                color(blue) ).
            
            %---- These are the cars
            cnf(jaguar,axiom,
                car(jaguar) ).
            
            cnf(honda,axiom,
                car(honda) ).
            
            cnf(masserati,axiom,
                car(masserati) ).
            
            cnf(porsche,axiom,
                car(porsche) ).
            
            cnf(saab,axiom,
                car(saab) ).
            
            %---- These are the drinks
            cnf(tea,axiom,
                drink(tea) ).
            
            cnf(orange,axiom,
                drink(orange) ).
            
            cnf(water,axiom,
                drink(water) ).
            
            cnf(milk,axiom,
                drink(milk) ).
            
            cnf(coffee,axiom,
                drink(coffee) ).
            
            %---- These are the pets
            cnf(dog,axiom,
                animal(dog) ).
            
            cnf(zebra,axiom,
                animal(zebra) ).
            
            cnf(snails,axiom,
                animal(snails) ).
            
            cnf(horse,axiom,
                animal(horse) ).
            
            cnf(fox,axiom,
                animal(fox) ).
            
            %---- Constraints.
            %---- the englishman lives in the red house.
            cnf(english_in_red_house,axiom,
                ( is_color(H,red)
                | ~ house(H)
                | ~ lives(english,H) ) ).
            
            %---- the spaniard owns dog.
            cnf(spaniard_owns_dog,axiom,
                owns(spaniard,dog) ).
            
            %---- the norwegian lives in the first house.
            cnf(norwegian_in_house_house_1,axiom,
                lives(norwegian,house_1) ).
            
            %---- masserati is driven in the yellow house.
            cnf(masserati_in_yellow_house,axiom,
                ( is_color(H,yellow)
                | ~ person(Person)
                | ~ drives(Person,masserati)
                | ~ house(H)
                | ~ lives(Person,H) ) ).
            
            %---- saab is driven next to where the fox is kept.
            cnf(saab_with_fox,axiom,
                ( next_to(House_1,House_2)
                | ~ person(Person_1)
                | ~ owns(Person_1,fox)
                | ~ house(House_1)
                | ~ lives(Person_1,House_1)
                | ~ person(Person_2)
                | ~ drives(Person_2,saab)
                | ~ house(House_2)
                | ~ lives(Person_2,House_2) ) ).
            
            %---- the norwegian lives next to the blue house.
            cnf(norwegian_in_blue_house,axiom,
                ( is_color(House_2,blue)
                | ~ house(House_1)
                | ~ lives(norwegian,House_1)
                | ~ house(House_2)
                | ~ next_to(House_1,House_2) ) ).
            
            %---- the porsche driver owns snails.
            cnf(porsche_with_snails,axiom,
                ( owns(P,snails)
                | ~ person(P)
                | ~ drives(P,porsche) ) ).
            
            %---- the honda driver drinks orange juice.
            cnf(honda_with_orange,axiom,
                ( drinks(P,orange)
                | ~ person(P)
                | ~ drives(P,honda) ) ).
            
            %---- the ukranian drinks tea.
            cnf(ukranian_drinks_tea,axiom,
                drinks(ukranian,tea) ).
            
            %---- the japanese drives a jaguar.
            cnf(japanese_drives_jaguar,axiom,
                drives(japanese,jaguar) ).
            
            %---- the masserati driver lives next to where the horse is kept.
            cnf(masserati_next_to_horse,axiom,
                ( next_to(House_1,House_2)
                | ~ person(Person_1)
                | ~ drives(Person_1,masserati)
                | ~ house(House_1)
                | ~ lives(Person_1,House_1)
                | ~ person(Person_2)
                | ~ owns(Person_2,horse)
                | ~ house(House_2)
                | ~ lives(Person_2,House_2) ) ).
            
            %---- coffee is drunk in the green house.
            cnf(coffee_in_green_house,axiom,
                ( is_color(H,green)
                | ~ person(P)
                | ~ drinks(P,coffee)
                | ~ house(H)
                | ~ lives(P,H) ) ).
            
            %---- the green house is to the immediate right of the ivory house.
            cnf(green_right_of_ivory,axiom,
                ( left_of(House_2,House_1)
                | ~ house(House_1)
                | ~ is_color(House_1,green)
                | ~ house(House_2)
                | ~ is_color(House_2,ivory) ) ).
            
            %---- milk is drunk in the middle house.
            cnf(milk_in_middle,axiom,
                ( lives(P,house_3)
                | ~ person(P)
                | ~ drinks(P,milk) ) ).
            
            %---- axioms for next.
            cnf(left_means_next_to,axiom,
                ( next_to(X,Y)
                | ~ left_of(X,Y) ) ).
            
            cnf(right_mean_next_to,axiom,
                ( next_to(X,Y)
                | ~ left_of(Y,X) ) ).
            
            cnf(next_to_means_left_or_right,axiom,
                ( left_of(X,Y)
                | ~ next_to(X,Y)
                | left_of(Y,X) ) ).
            
            cnf(house_1_left_of_house_2,axiom,
                left_of(house_1,house_2) ).
            
            cnf(house_2_left_of_house_3,axiom,
                left_of(house_2,house_3) ).
            
            cnf(house_3_left_of_house_4,axiom,
                left_of(house_3,house_4) ).
            
            cnf(house_4_left_of_house_5,axiom,
                left_of(house_4,house_5) ).
            
            cnf(house_1_not_left_of_house_1,axiom,
                ~ left_of(house_1,house_1) ).
            
            cnf(house_2_not_left_of_house_1,axiom,
                ~ left_of(house_2,house_1) ).
            
            cnf(house_3_not_left_of_house_1,axiom,
                ~ left_of(house_3,house_1) ).
            
            cnf(house_4_not_left_of_house_1,axiom,
                ~ left_of(house_4,house_1) ).
            
            cnf(house_5_not_left_of_house_1,axiom,
                ~ left_of(house_5,house_1) ).
            
            cnf(house_2_not_left_of_house_2,axiom,
                ~ left_of(house_2,house_2) ).
            
            cnf(house_3_not_left_of_house_2,axiom,
                ~ left_of(house_3,house_2) ).
            
            cnf(house_4_not_left_of_house_2,axiom,
                ~ left_of(house_4,house_2) ).
            
            cnf(house_5_not_left_of_house_2,axiom,
                ~ left_of(house_5,house_2) ).
            
            cnf(house_1_not_left_of_house_3,axiom,
                ~ left_of(house_1,house_3) ).
            
            cnf(house_3_not_left_of_house_3,axiom,
                ~ left_of(house_3,house_3) ).
            
            cnf(house_4_not_left_of_house_3,axiom,
                ~ left_of(house_4,house_3) ).
            
            cnf(house_5_not_left_of_house_3,axiom,
                ~ left_of(house_5,house_3) ).
            
            cnf(house_1_not_left_of_house_4,axiom,
                ~ left_of(house_1,house_4) ).
            
            cnf(house_2_not_left_of_house_4,axiom,
                ~ left_of(house_2,house_4) ).
            
            cnf(house_4_not_left_of_house_4,axiom,
                ~ left_of(house_4,house_4) ).
            
            cnf(house_5_not_left_of_house_4,axiom,
                ~ left_of(house_5,house_4) ).
            
            cnf(house_1_not_left_of_house_5,axiom,
                ~ left_of(house_1,house_5) ).
            
            cnf(house_2_not_left_of_house_5,axiom,
                ~ left_of(house_2,house_5) ).
            
            cnf(house_3_not_left_of_house_5,axiom,
                ~ left_of(house_3,house_5) ).
            
            cnf(house_5_not_left_of_house_5,axiom,
                ~ left_of(house_5,house_5) ).
            
            %---- negation of goal.
            cnf(prove_configuration,negated_conjecture,
                ( ~ drinks(norwegian,water)
                | ~ drinks(ukranian,tea)
                | ~ drinks(japanese,coffee)
                | ~ drinks(english,milk)
                | ~ drinks(spaniard,orange)
                | ~ owns(norwegian,fox)
                | ~ owns(ukranian,horse)
                | ~ owns(japanese,zebra)
                | ~ owns(english,snails)
                | ~ owns(spaniard,dog)
                | ~ drives(norwegian,masserati)
                | ~ drives(ukranian,saab)
                | ~ drives(japanese,jaguar)
                | ~ drives(english,porsche)
                | ~ drives(spaniard,honda)
                | ~ lives(norwegian,house_1)
                | ~ lives(ukranian,house_2)
                | ~ lives(japanese,house_5)
                | ~ lives(english,house_3)
                | ~ lives(spaniard,house_4)
                | ~ is_color(house_1,yellow)
                | ~ is_color(house_2,blue)
                | ~ is_color(house_3,red)
                | ~ is_color(house_4,ivory)
                | ~ is_color(house_5,green) ) ).
        """
        self.problem4 = ClauseSet()
        self.problem4.parse(Lexer(self.spec4))

    def test_initialization(self):

        ap = AlternatingPath(self.problem1)
        # check that the initialisation is working correctly, conjecture and hypotheses should be selected.
        self.assertEqual(self.problem1.clauses[2:], ap.selected[0].clauses)
        self.assertEqual(self.problem1.clauses[:2], ap.unprocessed.clauses)

        self.assertEqual(float('inf'), ap.limit)
        ap = AlternatingPath(self.problem1, limit=8)
        self.assertEqual(8, ap.limit)

    def test_selection(self):
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

        ap = AlternatingPath(self.problem4)
        selection = ap.saturate()
        # check that all clauses of the problem were selected.
        for clause in self.problem4.clauses:
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


if __name__ == '__main__':
    unittest.main()
