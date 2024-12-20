# This file contains sample GAP code for verifying some of the claims made in Dietrich, Lee, Pisani, and Popiel.
# All tests are quite straightforward. Many should be reproducible by hand using data from the Atlas, and
# the remainder can be checked using routine commands in any group-theoretic software package.


# A function for checking claims about the orders of certain group's maximal subgroups.
# Although appearing quite complex, most of the code involved is for handling duplicates.

list_max_sg_div := function (group_name, divisor1, divisor2)
    # list_max_sg_div: find all maximal subgroups of group_name
    #    with orders divisible by both divisor1 and divisor2.
    #
    # input:
    #     group_name: a string used as a group identifer
    #         in the GAP Character Table Library.
    #     divisor1, divisor2: positive integers
    # output:
    #    a list of character tables for the maximal subgroups of
    #    group_name with orders divisible by both divisor1 and divisor2,
    #    or fail if group_name is not an identifier for a group
    #    with maximal subgroup data stored in the GAP Character Table Library.
    local main_table, max_sg, divisible_by_both, sg_table, name, table_names;
    
    # Load the character table for group_name and check that
    # maximal subgroup data is available
    main_table := CharacterTable(group_name);
    if main_table = fail or not HasMaxes(main_table) then
        return fail;
    fi;
    
    divisible_by_both := [];
    table_names := [];
    for max_sg in Maxes(main_table) do
        # For each maximal subgroup, load the character table and check
        # if its order has the required divisors
        sg_table := CharacterTable(max_sg);
        if Size(sg_table) mod divisor1 = 0 and Size(sg_table) mod divisor2 = 0 then
            # If it does, standardise the name, check the subgroup hasn't
            # already been listed under another alias, and store it
            if IsDuplicateTable(sg_table) then
                name := IdentifierOfMainTable(sg_table);
            else
                name := Identifier(sg_table);
            fi;
            
            if not(name in table_names) then
                Add(divisible_by_both, sg_table);
                Add(table_names, name);
            fi;
        fi;
    od;
    
    return divisible_by_both;
end;

# Find the normalisers of elements of order p in L2(p) for p = 7, 11
g := PSL(3, 2);
gclassreps := List(ConjugacyClasses(g), Representative);
Print("Normalisers of elements of order 7 in PSL3(2):\n");
for c in gclassreps do
    if Order(c) = 7 then
        Print(StructureDescription(Normaliser(g, c)), "\n");
    fi;
od;

g := PSL(2, 11);
gclassreps := List(ConjugacyClasses(g), Representative);
Print("Normalisers of elements of order 11 in PSL2(11):\n");
for c in gclassreps do
    if Order(c) = 11 then
        Print(StructureDescription(Normaliser(g, c)), "\n");
    fi;
od;

# Show the required facts about subgroups of PSL2(59)
g := PSL(2, 59);
Print("Maximal subgroups of PSL2(59): ",
List(MaximalSubgroupClassReps(g), StructureDescription),
"\n");

gclassreps := List(ConjugacyClasses(g), Representative);
Print("Element orders in PSL2(59): ", List(gclassreps, Order), "\n");
Print("Normalisers of elements of order 5 in PSL2(59):\n");
for c in gclassreps do
    if Order(c) = 5 then
        Print(StructureDescription(Normaliser(g, c)), "\n");
    fi;
od;
Print("\n");

# Check the structure of the group generated by the actions of g38, h38 on the 3^8
g := Group(Matrix(Z(3)^0*[
        [0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 2, 2, 2, 0, 0],
        [0, 2, 1, 0, 0, 0, 0, 1],
        [0, 2, 1, 1, 1, 0, 0, 0],
        [0, 2, 2, 1, 2, 2, 0, 0],
        [1, 0, 1, 2, 0, 0, 0, 2],
        [0, 1, 0, 0, 0, 1, 0, 0],
        [0, 2, 0, 2, 2, 2, 2, 1]
    ]), Matrix(Z(3)*[
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [1, 1, 2, 1, 0, 0, 0, 0],
        [1, 1, 2, 0, 0, 2, 0, 0],
        [1, 0, 2, 1, 2, 1, 0, 0],
        [0, 0, 2, 2, 0, 2, 0, 0],
        [2, 1, 1, 1, 0, 0, 2, 0],
        [1, 0, 2, 0, 0, 2, 0, 2]
    ])
);

Print("The action of <g38, h38> on the appropriate 3^8 by conjugation has structure ",
StructureDescription(g), "\n");

# Print a presentation for U3(4)
Print("Presentation of U3(4): ",
RelatorsOfFpGroup(Image(IsomorphismFpGroup(PSU(3, 4)))),
"\n");

# Verify the presentation for M11 given in the Online Atlas
gens := [(2,10)(4,11)(5,7)(8,9), (1,4,3,8)(2,5,6,9)];
m11 := Group(gens);
Print("The group named M11 has structure ", StructureDescription(m11), "\n");

fg := FreeGroup(2);

g3 := gens[1]*gens[2];
r3 := fg.1*fg.2;
g4 := gens[1]*gens[2]^2;
r4 := fg.1*fg.2^2;
g5 := gens[1]*gens[2]^-1;
r5 := fg.1*fg.2^-1;

Print("That the generators for M11 satisfies the presentation is ",
gens[1]^2 = () and gens[2]^4 = () and g3^11 = () and g4^6 = ()
and g3^2*g5*g3*g4*g5*g3*g5^2 = (), "\n");
Print("M11 has order ", Size(m11), " and the fp group ",
Size(fg/[fg.1^2, fg.2^4, r3^11, r4^6, r3^2*r5*r3*r4*r5*r3*r5^2]), "\n");
