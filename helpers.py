from mmgroup import MM, XLeech2
import numpy

e, z = MM(), MM("x", 0x1000)

# The group commutator
comm = lambda a, b: (1/a)*(1/b)*a*b


if hasattr(e, "as_int"):
    as_int = lambda x: x.as_int()
else:
    as_int = lambda x: tuple(x.reduce().as_tuples())

if hasattr(e, "as_Co1_bitmatrix"):
    to_co1 = lambda x: x.as_Co1_bitmatrix().tobytes()
else:
    # The following code is adapted from elt_to_24_mat in Dietrich et al.
    def to_co1(g):
        mat = []
        for i in range(24):
            x = mmgroup_generators.gen_leech2_op_word_leech2(2**(23-i), g.mmdata, len(g.mmdata), 0)
            mat.append([int(d) for d in format((x % 2**24), '#026b')[2:]])
        
        # The above uses a different basis to MM.as_Co1_bitmatrix. If strict
        # interoperability is required, mat should be rotated 180 degrees.
        return str(mat)

    from mmgroup import generators as mmgroup_generators

if hasattr(XLeech2, "as_Leech2_bitvector"):
    as_bitvector = lambda x: XLeech2(x).as_Leech2_bitvector()
else:
    # Inspired by mmgroup/structures/xleech2.py
    def as_bitvector(x):
        n = XLeech2(x).value
        return numpy.array([n >> i for i in range(24)], dtype=int) & 1


def dim_q(gens):
    """
    dim_q: Get the "dimension" of subgroup of Q generated by gens.
    
    Since XLeech2.as_Leech2_bitvector() is an isomorphism from
    (Q/{z}, *) to (Z(2)^24, +), the dimension of a subspace <gens>
    of Q/{z} can be discerned fairly easily with a simplified version of
    row reduction (using the fact that + and - on Z(2) are both ^ (xor)).
    The true dimension must is 1 higher if the subgroup contains z,
    which must be the case if there is:
    
    * A generator which is z.
    * A generator of order 4: since Q/{z} contains only involutions,
        such an element has square z.
    * Two non-commuting generators: since all elements of Q/{z} commute,
        their commutator must be z.
    
    input:
        gens: a sequence of MM() elements.
    output:
        the "dimension" of <gens>, and whether or not the dimension
        is known to be accurate (i.e. the subgroup was proven to
        contain z).
    """
    # In the comments below, U = <gens>
    # Initially, we haven't shown z is in U or that U/<z> < 2^{24} has positive dimension
    has_z, dim = False, 0
    
    # Try and prove the subgroup contains z (so that log_2 |U| = log_2 |U/<z>| + 1)
    for i, g in enumerate(gens):
        # First, though, check U <= Q_x0
        if not g.in_Q_x0():
            raise Exception("Not all generators lie in Q")
        
        if not has_z:
            # If one generator equals z or has order 4, then z is in U --- all elements of Q_x0/<z> have order 1 or 2
            if g == z or g**2 != e:
                has_z = True
            else:
                # Alternatively, if two generators do not commute, z is in U -- Q_x0/<z> is abelian
                for j in range(i+1, len(gens)):
                    if (g*gens[j])/(gens[j]*g) != e:
                        has_z = True
                        break
    
    # Now map the generators to bitvectors in 2^{24} ~ Q_x0/<z>
    g_vecs = [as_bitvector(g) for g in gens]
    for i, g_vec in enumerate(g_vecs):
        # Perform row reduction; for each row with a leading 1,
        # increment the dimension found of U/<z> by 1 and cancel from later rows
        if (g_vec == 0).all():
            continue
        
        dim += 1
        for first_1 in range(24):
            if g_vec[first_1]:
                break
        
        for j in range(i+1, len(gens)):
            if g_vecs[j][first_1]:
                # Over Z_2, bitwise xor (^) serves for addition and subtraction
                g_vecs[j] ^= g_vec
    
    # If z is in U, then log_2 |U| = log_2 2|U/<z>| = dim(U/<z>) + 1; if we're unsure,
    # it could be either log_2 |U/<z>| or log_2 2|U/<z>|
    return dim + has_z, has_z




# The size_image family of functions

def map_to_vectors(gens, n=0, index=0):
    """
    map_to_vectors: given independent commuting generators gens of
        equal order n, compute and store the natural isomorphism from <gens>
        to the group Z_n^|gens| or Z_n^|gens|/Z_n^index.
        
        Note that this function does not check that <gens[:index]>
        is a normal subgroup of <gens>.
    
    input:
        gens: a sequence of MM() elements of equal order.
        n: None (default) or a positive integer. If not None,
            disables checks and is taken as the common order
            of elements in gens
        
        index: "dimension" of the kernel of the homomorphism.
    output:
        a dictionary mapping (gens[0]^i0*gens[1]^i1*...*gens[l]^ik).as_int()
        to (i{index}, ... , ik) for each 0 <= i, j, ... , k < n.
    """
    [g.reduce() for g in gens]
    test_size = not n
    
    # Check hypotheses (except independence) and initialise n
    if test_size:
        n = gens[0].order()
        for i, g in enumerate(gens[1:]):
            assert g.order(n) == n
            for j, h in enumerate(gens[:i]):
                if g**h != g:
                    raise Exception("Not an elementary abelian group (c.f. %d, %d)" % (j, i))
    
    the_map = {as_int(e): tuple([0]*(len(gens) - index))}
    elements = [(e, tuple([0]*len(gens)))]
    for i, g in enumerate(gens):
        # Check g is independent of previous generators
        if test_size and as_int(g) in the_map:
            raise Exception("Generators are not independent (c.f. %d)" % i)
        
        for k in range(n**i):
            # For each generator g = gens[i], multiply the elements of <gens[:i]>
            # by all powers of g, adding the power to the associated vector.
            element, vector = elements[k]
            for j in range(1, n):
                # Print a running tally for user sanity
                print(*vector, " "*35, end="\r")
                element *= g
                vector = vector[:i] + (j,) + vector[i+1:]
                the_map[as_int(element)] = vector[index:]
                elements.append((element, vector))
    
    return the_map


def _size_image_naive(gens, hom):
    # Do not use directly; called by size_image. Generates pre-images
    # for each element of hom(<gens>) in general.
    
    # Suppose that S is a subset of <gens> such that e is in S
    # and, for any a in S and g in gens, there is b in gens
    # for which hom(b) = hom(ag). It is easily shown that
    # hom(S) = hom(<gens>): for any h in hom(<gens>) there is
    # by definition a word w in gens satisfying hom(w) = h.
    # Writing w_i for the product of the first i elements of
    # w, we have w_0 = e is in S and that w_{i+1} = w_i g
    # (for some g in gens) is in S whenever w_i is in S,
    # so that by induction w_{len(w)} = w is in S. Conversely,
    # S is a subset of <gens> and so hom(S) is a subset of hom(<gens>).
    
    # In light of the above, we start by storing the identity e
    # in a list reps. Each element of e is then right-multiplied
    # by each generator, with elements that give new images
    # under hom appended to the list.
    
    reps = [e]
    gen_set = {hom(e)}
    
    # Note the generator below does not store reps;
    # it will iterate over elements appended to the right while the loop is in progress.
    for prod in (x*g for x in reps for g in gens):
        code = hom(prod)
        if code not in gen_set:
            reps.append(prod)
            gen_set.add(code)
    
    return gen_set, reps


def _size_image_solv(gens, hom, n):
    # Do not use directly; called by size_image. Generates pre-images
    # for each element of hom(<gens>) in the special case where
    # comm(gens[i], gens[j]) is in <gens[:j]> for all i < j.
    
    # The condition imposed ensures that any product of the first i <= len(gens)
    # elements of gens can be rewritten so that the generators appear in order.
    # It therefore suffices to consider products of powers of the generators
    # in the order they are given, rather than all products as
    # in size_image_naive; otherwise, we proceed similarly.
    
    reps = [e]
    gen_set = {hom(e)}
    for i, gen in enumerate(gens):
        # If n is not set, check the hypotheses set do hold.
        if not n:
            for j, other_gen in enumerate(gens[:i]):
                if hom(comm(gen, other_gen)) not in gen_set:
                    raise Exception("Generating set invalid for is_solv (c.f. %d, %d)" % (j, i))
        
        old_reps = reps.copy()
        # Consider all possible distinct powers of gen;
        # the largest element order in M is 119.
        for j in range(1, n or 120):
            g = (gen**j).reduce()
            if hom(g) in gen_set:
                # If hom(g) = hom(y) for some y already seen, then
                # hom(xg) = hom(xy) for all x in old_reps; since old_reps = <gens[:i]> is
                # a group by the initial comment, there is nothing new to be
                # found by trying more powers of gens
                break
            
            # Otherwise, since old_reps = <gens[:i]> is a group not containing
            # any lower powers of gen, everything will be new!
            for x in old_reps:
                x *= g
                reps.append(x)
                gen_set.add(hom(x))
    
    return gen_set, reps


def _size_image_conjugation(gens, basis, hom, n):
    # Do not use directly; called by size_image. Computes the size or image of hom(<gens>)
    # in the special case where hom is the homomorphism induced by
    # the conjugation action of <gens> on an elementary abelian group.
    
    # In essence, this case is handled identically to size_image_naive.
    # However, since an action of an elementary abelian group
    # is equivalent to an endomorphism on a vector space over a finite field ---
    # everything can be done with much faster matrix arithmetic.
    
    # Express the actions of gens as matrices in numpy format.
    mat_gens = [numpy.array([hom[as_int(h**g)] for h in basis], dtype=numpy.uint) for g in gens]
    
    # Finally, do the actual enumeration with the matrices.
    reps = [numpy.identity(len(basis), dtype=numpy.uint)]
    gen_set = {reps[0].tobytes()}
    
    # Note the generator below does not store reps;
    # it will iterate over elements appended to the right while the loop is in progress.
    # Also observe that we use matrix multiplication modulo n.
    for prod in ((x @ g) % n for x in reps for g in mat_gens):
        code = prod.tobytes()
        if code not in gen_set:
            reps.append(prod)
            gen_set.add(code)
    
    return gen_set


def size_image(gens, hom=as_int, return_type=int, is_solv=False, n=None, basis=None):
    """
    size_image: generate pre-images for each element of hom(<gens>)

    input:
        gens: a sequence of MM() elements.
        hom: a function (default as_int) with domain containing <gens> and
            range consisting of objects which can be stored in a Python set.
            In practice, this is always a homomorphism composed
            with an injective map, as for example as_int (the identity composed
            with an injective map M -> Z or some set of tuples)
            and to_co1 (the canonical homomorphism G_x0 -> Co_1
            composed with an injective map Co_1 -> b,
            the set of bytestrings).
            
            Alternatively, if return_type (below) is int or set, a dictionary
            mapping integers to tuples. The homomorphism will then be taken
            as arising from the action of gens by conjugation
            on an elementary abelian group (generators in argument basis below),
            and should be in the format of the output from the function
            map_to_vectors(...) above.
        
        return_type: the desired type for the output. Must be one
            of int (to return the order of hom(<gens>)),
            list (to return a list of pre-images for elements
            of hom(<gens>)), set (for the set of images),
            and tuple (gives list and set together).
        
        is_solv: a boolean, default False. If True, optimise
            for the case of a solvable group with generators
            gens such that comm(gens[i], gens[j]) is in <gens[:j]>
            for all i < j.
        
        n: None (the default) or a non-negative integer. Use with is_solv
            is generally ill-advised. If not None, it will be taken
            as the maximum order of elements in gens and disable checks
            if is_solv is enabled, and as the common order of elements
            in basis if that is provided. Ignored otherwise.
        
        basis: None (default) or a sequence of MM() elements. If hom is
            a dictionary, an independent generating set
            for the elementary abelian group on which the action occurs.
    """
    # Check the return type is acceptable
    if return_type not in (int, set, list, tuple):
        raise Exception("Invalid return type %r" % repr(return_type))
    
    # Reduce generators for possible speed increases
    [g.reduce() for g in gens]

    # Perform the enumeration in an appropriate manner
    if type(hom) is dict:
        if return_type in (list, tuple):
            raise Exception("Please implement the homomorphism manually.")
        
        gen_set = _size_image_conjugation(gens, basis, hom, n or basis[0].order())
    
    elif is_solv:
        gen_set, reps = _size_image_solv(gens, hom, n)
    
    else:
        gen_set, reps = _size_image_naive(gens, hom)
    
    # Finally, return the appropriate data type
    if return_type is int:
        return len(gen_set)
    
    elif return_type is set:
        return gen_set
    
    elif return_type is list:
        return reps
    
    elif return_type is tuple:
        return gen_set, reps


def check_singular(gens):
    """
    check_singular: check gens is a basis for a singular subgroup
        U = <singular_gens>.

    input:
        gens: a sequence of MM() elements. These should be commuting,
            perpendicular 2B involutions which form a basis for U
            as a vector space; an error will be thrown if they
            are not.

    output:
        a list of elements in U (starting with e), and a set of
        hashable representatives thereof.
    """
    for i, g in enumerate(gens):
        # Test each generator is an involution
        if g**2 != e:
            raise Exception("The generators of U are not all involutions")
        
        g_type, g_to_z = g.conjugate_involution()
        # Test each generator is a 2B involution
        if g_type != 2:
            raise Exception("The generators of U are not all 2B involutions")
        
        for h in gens[i+1:]:
            # Test each generator commutes with subsequent generators
            if g*h != h*g:
                raise Exception("U is not abelian")
            
            # Test each generators is perpendicular to subsequent generators
            if not (h**g_to_z).in_Q_x0():
                raise Exception("Not all generators of U are perpendicular")
    
    # Generate U, using the fact its generators are commuting involutions
    U_as_int, U = size_image(gens, return_type=tuple, is_solv=True, n=2)
    
    # Test U has the size it should if singular_gens is a basis
    if len(U) != 1 << len(gens):
        raise Exception("The generators of U do not form a basis!")
    
    return U, U_as_int


def check_normalise(gens, normalisers, group_set=None):
    """
    check_singular: check <gens> is normalised by normalisers.
    
    input:
        gens: a sequence of MM() elements.
        normalisers: a sequence of MM() elements.
        group_set: None, or a set containing the image
            of <gens> under as_int. If None (the default),
            size_image is used to compute this set.
    output:
        whether or not normalisers all normalise <gens>.
    """
    if group_set is None:
        group_set = size_image(gens, as_int, set)
    
    return all(as_int(g**h) in group_set for g in gens for h in normalisers)


def test_m11(r1, r2):
    """
    test_m11: check r1 and r2 generate a group of structure M11 using
        the appropriate presentation in the Online Atlas (accessible
        in GAP via 'Display(AtlasProgram("M11", "presentation").program);');
        note this presentation can be independently verified in GAP.
    
    input:
        r1, r2: MM() elements
    output:
        whether or not r1 and r2 satisfy the relevant presentation and generate
        a group of structure M11.
    """
    
    # Check that r1 and r2 are not both the identity;
    # as M11 is simple, elements satisfying a presentation
    # for it generate either the trivial group or M11.
    if r1 == r2 == e: return False
    
    if r1**2 != e: return False
    if r2**4 != e: return False
    r3 = r1*r2;
    if r3**11 != e: return False
    r4 = r3*r2
    if r4**6 != e: return False
    r6 = r1/r2
    return r3**2*r6*r3*r4*r6*r3*r6**2 == e


def test_xsl(r1, r2, m, is_sl=False):
    """
    test_m11: check r1 and r2 generate a group of structure PSL(2, m) or
        SL(2, m) (m odd) by testing Sunday's presentation for these groups 
        ("PRESENTATIONS OF THE GROUPS SL(2, m) AND PSL(2, m)", 1972).
    
    input:
        r1, r2: MM() elements
        m: an odd integer
        is_sl: whether to test for a group of structure SL(2, m) rather
            than the default PSL(2, m); default False.
    output:
        whether or not r1 and r2 satisfy the relevant presentation and generate
        a group of structure PSL(2, m) or SL(2, m) (as specified).
    """
    
    # Check that r1 and r2 are not both the identity;
    # as the only proper non-trivial normal subgroup of SL(2, m) is 2,
    # and SL(2, m)/2 ~ PSL(2, m), we have one of the two subgroups of interest.
    if r2 == e: return False
    
    p = r2**2
    if (p == e) == is_sl: return False
    if r1**m != p or (r1*r2)**3 != p: return False
    return (r1**((m+1)//2)*r2*r1**4*r2)**2 == p


def test_pgl(r1, r2, p, r=2):
    """
    test_m11: check r1 and r2 generate a group of structure PGL(2, p),
        for p an odd prime, by testing Robertson and William's presentation
        ("A PRESENTATION OF PGL(2,p) WITH THREE DEFINING RELATIONS", 1983) -
        however, see Section 2.5 of associated thesis.
    
    input:
        r1, r2: MM() elements
        p: an odd prime
        r: default 2; must be a primitive root modulo p.
    output:
        whether or not r1 and r2 satisfy the relevant presentation and generate
        a group of structure PGL(2, p).
    """
    
    # Confirm r is a primitive root modulo p. Since the order of r divides
    # totient(p) = p - 1, it suffices to check up to p//2
    k = 1
    for i in range(p//2):
        k = (k*r) % p
        if k == 1:
            raise Exception("%d^%d = 1 mod %d, not a primitive root" % (r, i, p))
    
    # Check that r2 has order p; as the only non-trivial normal subgroups
    # of PGL(2, p) are PSL(2, p) and PGL(2, p), with corresponding quotients
    # 2 and 1, r1 and r2 must generate PGL(2, p) if they satisfy
    # a presentation thereof. Conversely, to satisfy Robertson and Williams',
    # it must have order p.
    if r2.order(p) != p: return False
    
    # Omit r2**p below, since we know it equals e
    if r1**2 != e: return False
    if (r1*r2**2*r1*r2**r)**2 != e: return False
    return (r1*r2*r1*r2**r)**3 == e



def check_lemma_2_2(x, y, l, gs, hs, σ):
    """
    check_lemma_2_2: check certain elements satisfy
        the hypotheses of Lemma 2.2 (except for x, y, l, gs, hs
        belonging to a normal $p$-subgroup of N_M(x))
    
    input:
        x, y, l: MM() elements as per Lemma 2.2
        gs, hs: lists of MM() elements as per Lemma 2.2
        σ: MM() elements as per Lemma 2.2
    output:
        whether or not the given inputes satisfy the hypotheses of Lemma 2.2
    """
    p = x.order()
    if any(u.order() != p or x*u != u*x for u in (y, l, *gs, *hs)):
        return False
    
    if not check_normalise((x, y), [σ]):
        return False
    
    x_cyc = [x**i for i in range(p)]
    if y in x_cyc or l*y == y*l:
        return False
    
    if any(u*y != y*u for u in (*gs, *hs)):
        return False
    
    if any(comm(g, u) not in x_cyc for u in (*gs, *((u**σ).reduce() for u in gs), *hs) for g in gs):
        return False
    
    if any(comm(g, u) not in x_cyc for i, u in enumerate((u**σ).reduce() for u in hs) for g in gs[i+1:]):
        return False
    
    return not any(comm(g, h**σ) in x_cyc for g, h in zip(gs, hs))

