/*
Given a polynomial f(t) over a finite field F_q and a prime l coprime to q and d:=deg(f),
This file can be used to produce the filtration sequence (using FiltrationSequence(f, l))
and the cup product vanishing sequence (using CupProducts(f, l)) for the curve y^l=f(t).

One can also collect data for large classes of curves at a time using GetData. Sample usage:

GetData(7, 3, 6, "data.txt" : filt_sequence := false);    // quite fast (cup products only)
GetData(7, 3, 6, "data.txt" : filt_sequence := true);     // much slower (computes class groups)
*/

function AllOrbitReps(l,q,d)
    /*
    return a list of representatives of orbits of degree d irreducible 
    polynomials over the finite field Fq under the action of the affine group
    */

    Fq<u> := GF(q);
    Pol<x> := PolynomialRing(Fq);
    polys := SetToSequence(AllIrreduciblePolynomials(Fq, d));
    reps := [];
    polysfound := [];

    for f in polys do
        if not f in polysfound then
            orbit := [];
            for a in Fq do
                ispower, root := IsPower(a^d, l);
                if a ne 0 and ispower then
                    for b in Fq do
                        newf := Evaluate(f, a*x+b) / root;
                        if not newf in orbit then
                            Append(~orbit, newf);
                        end if;
                    end for;
                end if;
            end for;

            Append(~reps, <Sort(orbit)[1], #orbit>);
            polysfound cat:= orbit;
        end if;
    end for;
    return reps;
end function;

function IncludelthRootsOfUnity(K, l)
    /*
    Input:  function field K and a prime l (not equal to characteristic of K)
    Return: an extension L of K, an embedding KtoL mapping K into L, and
            an l-th root of unity zeta in L.
    */

    k := ConstantField(K);
    q := Characteristic(k);
    gamma := Order(GF(l)!q);
    kk := CommonOverfield(k, GF(q^gamma));
    L, KtoL := ConstantFieldExtension(K, kk);
    zeta := L ! (kk.1^(Order(kk.1) div l));
    return L, KtoL, zeta;
end function;

function Pushforward(D, phi)
    /*
    Input:  a divisor or place D on a function field K, 
            and a map phi from K to an extension L.
    Return: the divisor on L obtained by applying phi to all the functions
            used to define places of D.
    */

    assert Domain(phi) eq FunctionField(D);
    case Type(D):
        when DivFunElt: // recursively call Pushforward on each place, then recombine
            plseq, coeffseq := Support(D);
            return &+[coeffseq[i] * Pushforward(plseq[i], phi) : i in [1..#plseq]];
        when PlcFunElt:
            f,g := TwoGenerators(D); // two elements of K with a unique common zero at D
            fzeros := ZeroDivisor(Divisor(phi(f)));
            gzeros := ZeroDivisor(Divisor(phi(g)));
            
            return GCD(fzeros, gzeros);
    end case;
end function;

function DivReduce(D)
    /*
    Input:  a divisor D on a function field
    Return: a divisor linearly equivalent to D, usually simpler
    */
    Dprime, r, A := Reduction(D);
    return Dprime + r*A;
end function;

function FindRelations(Dlist, l)
    /*
    Input:  A sequence of l-torsion divisors [D1, ..., Dn] for some integer l
    Output: A sequence of n-dim vectors c with the property that sum c[i]*Di = 0,
            and every relation of this form is in the span of the returned vectors.
    */

    n := #Dlist;
    indeps := [];
    kernel := [];
    for i in [1..n] do
        D := Dlist[i];
        foundmatch := false;
        coeffslist := CartesianPower([0..l-1], #indeps);
        for coeffs in coeffslist do
            testdiv := &+[Parent(D) | coeffs[j] * Dlist[indeps[j]] : j in [1..#indeps]];
            if IsPrincipal(D - testdiv) then
                foundmatch := true;
                fullcoeffs := [0 : j in [1..n]];
                fullcoeffs[i] := 1;
                for j in [1..#indeps] do fullcoeffs[indeps[j]] := -coeffs[j]; end for;
                Append(~kernel, fullcoeffs);
                break;
            end if;
        end for;
        if not foundmatch then
            Append(~indeps, i);
        end if;
    end for;
    
    for v in kernel do
        assert IsPrincipal(&+[v[i] * Dlist[i] : i in [1..n]]);
    end for;

    return kernel, indeps;
end function; 

function LambdaMinusOneImages(D, lambda, l)
    /*
    Return a sequence [D, (lambda-1)D, (lambda-1)^2D, ...] such that the
    last term is non-principal but its image under lambda-1 is principal.
    */

    newD := D;
    j := 0;
    Dimages := [];
    while newD ne 0 do
        Append(~Dimages, newD);
        newD := DivReduce(Pushforward(newD, lambda) - newD);
        j +:= 1;
    end while;
    return Dimages;
end function;

function FiltBasis(K, l)
    /*
    Given a function field K defined by y^l = f(t), there is a basis
    D_1,...,D_r for the l-torsion of the class group. Let lambda be the
    automorphism y -> zeta*y, for zeta an l-th root of unity. Return
    - a sequence consisting of [D_i, (lambda-1)D_i, (lambda-1)^2D_i, ...]
      for each i, where the sequence continues until the next application 
      of lambda-1 results in a principal divisor;
    - the automorphism lambda;
    - the elementary abelian invariants of the class group of K.
    */

    // construct an extension L over which lambda is defined
    L<y>, KtoL, zeta := IncludelthRootsOfUnity(K, l);
    Fgamt<t> := BaseRing(L);
    Fgam<a> := BaseRing(Fgamt);
    lambda := hom<L -> L | zeta * y>;

    // find a basis for the K-rational l-torsion points, base changed 
    // to L, as well as their images under (lambda-1)^j for all j.
    G, h := ClassGroup(K);
    Gstructure := ClassGroupAbelianInvariants(K);
    Dlists := [];
    for g in Generators(G) do
        if Order(g) ne 0 and IsDivisibleBy(Order(g), l) then
            D := DivReduce(h((Order(g) div l) * g));
            newD := DivReduce(Pushforward(D, KtoL));  
            Append(~Dlists, LambdaMinusOneImages(newD, lambda, l));
        end if;
    end for;

    return Dlists, lambda, Exclude(Gstructure, 0);
end function;

function FiltDims(Dlists, l)
    /*
    Input a basis produced by FiltBasis, and return a list of all the filtration stages
    containing an element of J[l](F_q). 

    More precisely:
    Input:  a sequence of the form [[v1, Tv1, T^2v1, ...], ..., [vn, Tvn, T^2vn, ....]] 
            where v1,...,vn are independent divisors, and the last element of each list is
            in ker(T). (The lists do not need to be the same length)
    Return: A sequence of sequences of integer vectors. The j-th sequence is a list of 
            vectors u such that (sum u[i]*vi) is in ker T^j, spanning the kernel of the 
            restriction of T^(j-1) to v1,...,vn.
    */

    n := #Dlists;
    r := Max([#i : i in Dlists]);
    // add 0s to the end of each sequence in Dlist to make them all length r:
    paddedDlists := [Dlist cat [Universe(Dlist)!0 : i in [1..r-#Dlist]] : Dlist in Dlists];

    nextker := [[(i eq k) select 1 else 0 : k in [1..n]] : i in [1..n]];
    kerlist := [nextker];
    indeplist := [[]];
    for j in [1..r] do
        innextker := [DivReduce(&+[coeffs[i] * paddedDlists[i][r+1-j] : i in [1..n]]) : coeffs in nextker];
        implicitkercoeffs, implicitindeps := FindRelations(innextker, l);
        indeps :=  [nextker[i] : i in implicitindeps];
        nextker := [[&+[c[i] * nextker[i][k] : i in [1..#nextker]] : k in [1..n]] : c in implicitkercoeffs];
        Append(~kerlist, nextker);
        Append(~indeplist, indeps);
    end for;
    return Reverse(indeplist), Reverse(kerlist);
end function;

function FiltrationSequence(f, l)
    /*
    Return the filtration sequence of y^l=f(t); that is, if J is the Jacobian of
    this curve and V_0, ..., V_{l-1} the filtration on J[l], return the set of m 
    such that there exists an element of J[l](F_q) in V_m - V_{m-1}.

    Also return the elementary abelian invariants of the class group of G (since
    the class group is computed anyways in the process).
    */
    
    Fq := BaseRing(Parent(f));
    Fqt<t> := FunctionField(Fq);
    Pol<Y> := PolynomialRing(Fqt);
    K<y> := ext< Fqt | Y^l - f >;

    Dlists, lambda, Gstructure := FiltBasis(K, l);
    indeps := FiltDims(Dlists, l);
    return [i - 1 : i in [1..#indeps] | #indeps[i] gt 0], Gstructure; // indexes by V_{i-1} = ker(lambda-1)^i
end function;

function Frob(R, q)
    /*
    R a polynomial ring; return the map R->R given by applying q-th power to all constants
    */

    k<a> := BaseRing(R);
    frob0 := hom<k -> k | a^q>;
    return hom<R -> R | frob0, R.1>;
end function;

function CupProducts(f, l)
    /* 
    Given the curve y^l=f(t),
    Return the sequence [e_1, ..., e_gamma], where e_n = 1 if a_n^[1] exists, 
                                                   e_n = 0 if a_n^[0] exists but a_n^[1] does not, 
                                                   e_n = -1 if a_n^[0] does not exist.
    (See the paper for the definitions of a_n^[k]. 
    The set T from the paper is the set of n such that e_n = 1)
    */

    q := #BaseRing(Parent(f));
    gamma := Order(GF(l)!q);
    d := Degree(f);
    r := GCD(d, gamma);

    k<c> := GF(q^gamma);
    R<x> := PolynomialRing(k);
    ff := ChangeRing(f, k);
    f1 := Factorisation(ff)[1][1];

    assert &*[Frob(R, q^j)(f1) : j in [0..r-1]] eq ff;
    gioverflist := [&*[Frob(R, q^j)(f1)^((q^(j*(i-1)) - 1) mod l) : j in [0..r-1]] : i in [1..gamma]];

    kk := ext<k | f1>;
    alpha := Roots(ChangeRing(f1, kk))[1][1];

    liftheights := [];
    for n in [1..gamma] do
        if d*(n-1) mod gamma eq 0 then
            if IsPower(Evaluate(gioverflist[n], alpha), l) then
                Append(~liftheights, 1);
            else
                Append(~liftheights, 0);
            end if;
        else
            Append(~liftheights, -1);
        end if;
    end for;
    return liftheights;
end function;

procedure GetData(l, q, d, output_file : filt_sequence := true, auts := false, filter_by_cup_products := [])
    /*
    Given a prime l, prime power q, and natural number d, collect data on all curves of the form
    y^l = f(t) over F_q for monic irreducible polynomials f of degree d, where only one f(t) per equivalence
    class is taken (equivalence by generalized Weierstrass transformation). Print the data to output_file. 
    
    Data includes:
    - l
    - q
    - gamma := order of q in F_l^*
    - f(t)
    - the number of monic irreducible polynomials equivalent to f(t)
    - a sequence [e_1, ..., e_gamma], where e_n = 1 if a_n^[1] exists, 
                                            e_n = 0 if a_n^[0] exists but a_n^[1] does not, 
                                            e_n = -1 if a_n^[0] does not exist.

    if filt_sequence := true, the data also includes:
    - the elementary abelian invariants of the class group of y^l = f(t)
    - the filtration sequence
    - the l-rank of the class group.

    if auts := true, the data also includes:
    - the number of automorphisms of the curve that are defined over F_q.

    filter_by_cup_products can be set to a list of desired cup product vanishing sequences, in which case
    only polynomials with one of the given vanishing sequences are considered.
    */

    // Printing the file header
    select_data := false;
    if #filter_by_cup_products gt 0 then 
        fprintf output_file, "Only vanishing sequences in %o\n", filter_by_cup_products;
        select_data := true; 
    end if;

    header := "\/\/l; q; gamma; polynomial; orbit size; cup products (1..gamma)";
    if filt_sequence then
        header cat:= "; class group structure; filtration sequence; l-rank";
    end if;
    if auts then
        header cat:= "; #Aut(K)";
        Fq := GF(q);
        Fqt<t> := FunctionField(Fq);
        Pol<Y> := PolynomialRing(Fqt);
    end if;
    //fprintf output_file, header cat "\n";   

    // Collecting data on representatives of equivalence classes of polynomials
    orbitreps := AllOrbitReps(l,q,d);
    for rep in orbitreps do
        f := rep[1];
        cups := CupProducts(f, l);
        if not select_data or cups in filter_by_cup_products then
            data_string :=  Sprintf("%o; %o; %o; %o; %o; %o", l, q, Order(GF(l)!q), f, rep[2], cups);
            if filt_sequence then
                filtseq, Gstructure := FiltrationSequence(f, l);
                data_string cat:= Sprintf("; %o; %o; %o", Gstructure, filtseq, #filtseq);
            end if;
            if auts then
                K<y> := ext< Fqt | Y^l - f >;
                data_string cat:= Sprintf("; %o", #AutomorphismGroup(K));
            end if;
            fprintf output_file, data_string cat "\n";
        end if;
    end for;
end procedure;

function RetrieveData(datafile)
    /* takes the outputted data from GetData and puts it back into Magma. Returns:
    <l, q, gamma, f, #orbit, cup products, class group deocmposition, filtration sequence, l-rank>
    */

    newdata := <>;
    for s in Split(Read(datafile)) do
        terms := Split(s, ";");

        q := StringToInteger(terms[2]);
        Fq<u> := GF(q);
        Pol<x> := PolynomialRing(Fq);

        Append(~newdata, <eval term : term in terms>);
    end for;
    return newdata;
end function;

procedure ExpandData(datafile)
    /* for all values of l, q, d occuring in datafile, checks if all orbit representatives
    have been computed. If not, append all the missing orbit reps (but only the cup 
    products, not the filtration sequence)
    */

    alldata := RetrieveData(datafile);
    params := SetToSequence(SequenceToSet([[s[1], s[2], Degree(s[4])] : s in alldata]));
    qs := SetToSequence(SequenceToSet([s[2] : s in alldata]));
    polys := AssociativeArray();
    for q in qs do
        polys[q] := [s[4] : s in alldata | s[2] eq q];
    end for;
    for param in [p : p in params | p ne [7,17,6]] do
        l, q, d := Explode(param);
        print l,q,d;
        time orbitreps := AllOrbitReps(l,q,d);
        for rep in orbitreps do
            f := rep[1];
            if not f in polys[q] then
                cups := CupProducts(f, l);
                data_string :=  Sprintf("%o; %o; %o; %o; %o; %o", l, q, Order(GF(l)!q), f, rep[2], cups);
                fprintf datafile, data_string cat "\n";
            end if;
        end for;
    end for;
end procedure;

/*
procedure LaTeXTable(alldata)
    /* takes data from RetrieveData and summarizes the info 

    collection := AssociativeArray();
    for data in collection do
        sort1 := [data[1], data[3], GCD(data[3], Degree(data[4]))];
        if not sort1 in collection then collection[sort1] := AssociativeArray();
        sort2 := [data[6], data[8]];
        if not sort2 in collection[sort1] then collection[sort1][sort2] := AssociativeArray();
        sort3 := [data[2], Degree(data[4])];
        if not sort3 in collection[sort1][sort2] then 
            collection[sort1][sort2][sort3] := 1;
        else
            collection[sort1][sort2][sort3] +:= 1;
        end if;
    end for;

    for sort1 in Keys(collection) do
        l := sort1[1];
        gamma := sort1[2];
        gcd := sort1[3];
        for sort2 in Keys(collection[sort1]) do
            T := sort2[1];
            filtset := sort2[2];
            for sort3 in Keys(collection[sort1][sort2]) do
                q := sort3[1];

end procedure
*/

Fq<u> := GF(3);
Pol<x> := PolynomialRing(Fq);
allorbitreps := [<x^12 + x^8 + x^7 + x^6 + x^2 + x + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^6 + 2*x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^5 + 2*x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^5 + x^3 + 2*x + 2, 6>,
<x^12 + 2*x^8 + x^6 + x^5 + x^4 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^4 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^8 + x^7 + x^6 + x^5 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^6 + 2*x^5 + x^4 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + x^6 + x^4 + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^5 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^5 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + 2*x^5 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^6 + 2*x^5 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^8 + x^7 + x^6 + x^5 + x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^8 + x^7 + x^6 + 2*x^5 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^5 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^6 + x^5 + x^4 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^6 + x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^6 + x^5 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^8 + x^6 + x^4 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + 2, 6>,
<x^12 + 2*x^8 + x^5 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^6 + x^5 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + x^2 + 2*x + 2, 6>,
<x^12 + 2*x^8 + x^7 + 2*x^6 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + x^4 + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + x^6 + 2*x^5 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + x^5 + 2*x^3 + x + 2, 6>,
<x^12 + 2*x^10 + x^7 + x^5 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^7 + x^5 + x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + 2*x^10 + x^8 + 2*x^6 + x^5 + 2*x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^8 + 2*x^6 + x^5 + 2*x^4 + x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^6 + x^5 + x^4 + 2*x^3 + 1, 6>,
<x^12 + 2*x^10 + x^6 + x^5 + 2*x^3 + 2*x + 2, 6>,
<x^12 + 2*x^8 + x^6 + x^5 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^6 + x^4 + 2*x^3 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + x^4 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + 2, 6>,
<x^12 + 2*x^10 + x^8 + x^5 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^5 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^6 + x^4 + 2*x^3 + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^7 + x^5 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + x^5 + x^4 + x + 1, 6>,
<x^12 + x^8 + x^7 + x^6 + x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^6 + x^5 + x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^6 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^6 + 2*x^5 + x^4 + 2*x^2 + 2, 6>,
<x^12 + x^10 + 2*x^8 + 2*x^4 + x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^5 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + x^9 + x^6 + 2*x^5 + 2*x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + 2*x^4 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + x^6 + x^4 + 2*x^3 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^6 + 2*x^5 + 2*x^3 + 2, 6>,
<x^12 + 2*x^8 + x^7 + x^6 + x^4 + x^3 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + 2*x^5 + x^4 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + x^6 + x^5 + x^4 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + x^5 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + x^6 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^6 + x^5 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^5 + x^4 + x^3 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^6 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^5 + x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^6 + 2*x^5 + x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + x^5 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^6 + x^5 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + x^6 + 2*x^5 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^5 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + 2*x^6 + 2*x^5 + x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + 2*x^5 + 2*x^3 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + 2*x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + 2*x^10 + x^5 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^5 + 2*x^4 + x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^6 + x^5 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^5 + 2*x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + 2*x^6 + x^4 + 2*x^3 + 2*x + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + x^4 + x + 2, 6>,
<x^12 + x^7 + x^6 + 2*x^5 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + x^6 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + x^6 + x^5 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^5 + x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^6 + 2*x^5 + 2*x^2 + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^3 + x + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^7 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + 2*x^4 + 2*x^3 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x^4 + x^3 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^6 + x^5 + x^4 + x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^6 + x^4 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^6 + x^3 + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^6 + 2*x^5 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^7 + x^6 + 2*x^5 + x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^6 + 2*x^5 + x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^6 + 2*x^5 + x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + 2*x^5 + x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^7 + x^6 + x^4 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + x^4 + 2*x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^6 + 2*x^4 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^6 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + 2*x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^6 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + x^7 + x^6 + x^5 + x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x^6 + x^5 + x^4 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + x^2 + 2*x + 1, 6>,
<x^12 + x^10 + x^7 + x^4 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + x^6 + x^5 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^4 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^2 + 2*x + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + x^5 + 2*x^4 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + x^6 + 2*x^5 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^10 + x^7 + 2*x^4 + x^2 + 1, 6>,
<x^12 + x^10 + x^7 + 2*x^4 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + x^6 + x^5 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^5 + x^4 + 2*x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^5 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^5 + 2*x^4 + 2*x^3 + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^6 + x^5 + x^3 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^6 + 2*x^5 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^7 + x^6 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + x^5 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^4 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^5 + 2*x^2 + 1, 6>,
<x^12 + x^10 + x^6 + x^5 + x^4 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^5 + 2*x^4 + 2*x^3 + x + 2, 6>,
<x^12 + 2*x^8 + 2*x^6 + x^5 + x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + 2*x^6 + 2*x^4 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^5 + x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^7 + x^6 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + x^5 + 2*x^4 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^5 + x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^7 + 2*x^6 + x^5 + 2*x^4 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + x^5 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^6 + x^5 + x^4 + x^3 + x^2 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^7 + x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^7 + 2*x^6 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^6 + 2*x^5 + x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^7 + 2*x^5 + 2*x^3 + x + 2, 6>,
<x^12 + 2*x^10 + x^8 + x^5 + x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + x + 1, 6>,
<x^12 + 2*x^10 + 2*x^8 + x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^6 + x^5 + x^4 + 1, 6>,
<x^12 + 2*x^6 + x^5 + x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^5 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^5 + x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^6 + x^5 + x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^5 + x^4 + x + 1, 6>,
<x^12 + x^8 + x^7 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + x^5 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^6 + 2*x^5 + x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + x^5 + x^4 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^5 + x^4 + x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^6 + x^5 + 2*x^4 + x^2 + x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + x^5 + x^4 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^6 + x^4 + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^6 + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + x^6 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + 2*x^5 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + 2*x^5 + x^4 + x^3 + 2, 6>,
<x^12 + x^10 + x^6 + x^5 + 2*x^4 + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + x^6 + x^5 + 2*x^4 + 2*x^2 + x + 2, 6>,
<x^12 + 2*x^10 + 2*x^8 + x^6 + x^5 + 2*x^4 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^6 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^4 + 2*x^3 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^6 + x^5 + x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^6 + x^5 + x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^5 + 2*x^4 + 2*x^2 + 1, 6>,
<x^12 + x^7 + 2*x^6 + 2*x^5 + x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^5 + x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^8 + x^7 + x^6 + x^5 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + x^6 + x^5 + 2*x^4 + x^2 + x + 2, 6>,
<x^12 + x^10 + x^8 + x^5 + x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^6 + 2*x^5 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^10 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^5 + x^3 + x^2 + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + 2*x^6 + x^5 + x^4 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^5 + x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^5 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x^5 + 2*x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + 2*x^6 + x^5 + x^4 + x + 1, 6>,
<x^12 + 2*x^8 + 2*x^6 + x^5 + 2*x^4 + x^3 + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + 2*x^4 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^6 + x^5 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + 2*x^5 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^6 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^4 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + x^6 + 2*x^5 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + x^6 + 2*x^5 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^10 + 2*x^8 + x^6 + x^5 + x^4 + x + 2, 6>,
<x^12 + x^11 + 2*x^6 + 2*x^4 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + 2*x^10 + 2*x^4 + x^3 + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^5 + 2*x^4 + x^3 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^5 + 2*x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^7 + x^6 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^8 + x^7 + 2*x^5 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + 2*x^6 + 2*x^5 + x^4 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + x^6 + 2*x^4 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + 2*x^5 + x^3 + 1, 6>,
<x^12 + x^11 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^7 + x^6 + 2*x^5 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^5 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^5 + x^4 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + x^5 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^5 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x + 1, 6>,
<x^12 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + 2*x^5 + 2*x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^6 + x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^8 + x^7 + 2*x^6 + 2*x^4 + 2*x^3 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^6 + x^5 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + x^5 + 2*x^4 + x^2 + 2, 6>,
<x^12 + 2*x^10 + 2*x^8 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + 2*x^8 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^8 + x^7 + x^4 + 2*x^3 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + x^5 + x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^10 + 2*x^8 + 2*x^6 + x^5 + x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^6 + x^4 + 2*x + 1, 6>,
<x^12 + x^8 + x^6 + x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^6 + x^5 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^6 + x^4 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^6 + x^5 + x^4 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^5 + 2*x^4 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + x^7 + x^6 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + x^4 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^7 + x^5 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^4 + x^3 + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + x^3 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^7 + x^5 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + x^5 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + x^5 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^6 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^8 + x^6 + x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^7 + 2*x^5 + 2*x^4 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + x^5 + x^4 + x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2, 6>,
<x^12 + 2*x^8 + x^7 + x^6 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^5 + 2*x^4 + x^3 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^5 + 2*x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + 2*x^10 + x^7 + 2*x^5 + x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + 2*x^6 + x^5 + x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + x^5 + x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^7 + x^6 + 2*x^5 + x^4 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^5 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + x^6 + x^5 + 2*x^4 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^7 + x^6 + x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^5 + x^3 + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^6 + 2*x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + x^3 + x^2 + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + x^4 + 2*x^3 + 2, 6>,
<x^12 + x^8 + 2*x^6 + x^5 + 2*x^3 + x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + 2*x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + 2*x^5 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^8 + x^7 + x^6 + 2*x^5 + x^4 + x^2 + 1, 6>,
<x^12 + x^7 + 2*x^6 + 2*x^5 + x^4 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + 2*x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^5 + x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^4 + 2*x^3 + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + 2*x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + 2*x^5 + x^4 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^6 + 2*x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^6 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^6 + x^3 + x + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^4 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^5 + x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + 2*x^8 + 2*x^6 + x^5 + 2*x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^5 + x^4 + 2*x^2 + x + 2, 6>,
<x^12 + x^7 + x^6 + 2*x^5 + x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^6 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^6 + x^5 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^6 + x^5 + x^4 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^5 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^6 + 2*x^2 + 2, 6>,
<x^12 + 2*x^10 + x^7 + x^5 + 2*x^4 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^5 + x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^4 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^4 + 2, 6>,
<x^12 + x^10 + x^7 + 2*x^6 + x^5 + x^4 + 2*x + 1, 6>,
<x^12 + x^10 + x^7 + 2*x^6 + x^5 + x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^7 + x^5 + 2*x^4 + 2*x^3 + 1, 6>,
<x^12 + 2*x^6 + x^5 + 2*x^4 + 2*x^2 + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^7 + x^4 + x^3 + x^2 + x + 2, 6>,
<x^12 + x^8 + x^7 + x^5 + x^4 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x + 2, 6>,
<x^12 + x^11 + x^8 + x^6 + x^5 + x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^7 + x^6 + x^5 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^7 + x^6 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^6 + x^5 + x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^7 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^5 + 2*x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^3 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + x^5 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^10 + 2*x^6 + x^5 + x^2 + 2*x + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^10 + x^8 + x^6 + x^5 + x^4 + x^3 + 1, 6>,
<x^12 + x^5 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + x^4 + 2*x^2 + 1, 6>,
<x^12 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^6 + 2*x^5 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^5 + x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^6 + x^5 + 2*x^4 + x^3 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^6 + x^5 + x^4 + x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^4 + x + 2, 6>,
<x^12 + x^10 + x^7 + 2*x^6 + 2*x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^8 + x^6 + x^5 + 2*x^4 + 2*x^3 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^6 + x^4 + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^6 + x^5 + x^2 + 2, 6>,
<x^12 + 2*x^8 + x^7 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^5 + x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^7 + x^5 + x^4 + x^3 + x^2 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^6 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^7 + x^6 + 2*x^5 + x^4 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^8 + x^7 + 2*x^6 + x^5 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^6 + x^5 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^2 + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^5 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^6 + x^5 + x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + 2*x^5 + 2, 6>,
<x^12 + x^10 + x^7 + 2*x^5 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^4 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^5 + 2, 6>,
<x^12 + x^11 + x^9 + x^7 + 2*x^6 + 2*x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^4 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^5 + x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^7 + 2*x^5 + 2*x^4 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^5 + 2*x^4 + x^3 + 2*x + 1, 6>,
<x^12 + 2*x^6 + x^5 + 2*x^4 + x + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^10 + x^8 + x^6 + x^5 + x^4 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + x^5 + x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + 2*x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^10 + 2*x^6 + x^4 + x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^5 + 2*x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^5 + x^3 + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^6 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^7 + x^5 + 2*x^4 + x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + x^6 + 2*x^5 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + x^5 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^6 + x^5 + 1, 6>,
<x^12 + x^11 + x^9 + x^4 + 2*x^2 + 2*x + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^6 + x^5 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + 2*x^4 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^6 + 2*x^5 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + x^5 + 2*x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^7 + 2*x^6 + x^5 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + x^6 + 2*x^5 + x^2 + 2*x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^5 + 2*x^4 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^5 + 2*x^4 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^7 + 2*x^5 + x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^6 + x^4 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^5 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + x^7 + x^6 + x^5 + 2*x^4 + 2*x + 2, 6>,
<x^12 + x^10 + x^7 + x^5 + x^4 + x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^6 + 2*x^5 + x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^5 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + x^5 + x^4 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + x^6 + x^5 + x^4 + 2*x^3 + 2, 6>,
<x^12 + x^7 + 2*x^6 + x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + 2*x^6 + x^5 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + 2*x^7 + x^6 + 2*x^5 + 2*x^3 + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + 2*x^5 + x^4 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + 2*x^5 + x^4 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + 2*x^5 + x^4 + 2*x^3 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^5 + 2*x^4 + x + 2, 6>,
<x^12 + x^8 + x^7 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + 2*x^8 + x^6 + x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^10 + x^7 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^6 + x^5 + x^3 + x^2 + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^6 + x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^6 + x^5 + x^4 + x^3 + x + 2, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + x^5 + x^4 + x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^8 + x^6 + 2*x^5 + x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + x^4 + x^3 + x^2 + 1, 6>,
<x^12 + 2*x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + x^5 + x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + x^5 + x^4 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^2 + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + x^5 + x^4 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^7 + x^6 + 2*x^5 + 2*x^3 + 1, 6>,
<x^12 + x^10 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^8 + 2*x^6 + x^5 + x^4 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^5 + 2*x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^7 + x^6 + 2*x^5 + x^4 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^6 + 2*x^4 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^6 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + x^5 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^7 + x^4 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^10 + x^7 + x^4 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + x^5 + x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + 2*x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + x^5 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^6 + x^4 + 2*x^2 + 2, 6>,
<x^12 + x^6 + 2*x^4 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^5 + x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^2 + 2, 6>,
<x^12 + x^8 + x^7 + x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + x^5 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^10 + x^8 + 2*x^6 + x^5 + x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^6 + 2*x^4 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + x^5 + x^4 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + x^5 + x^4 + x^3 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + x^5 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^6 + 2*x^4 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^5 + x^4 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^6 + x^3 + 1, 6>,
<x^12 + x^11 + x^9 + x^7 + x^5 + x^4 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^7 + x^6 + x^5 + 2*x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + 2*x + 1, 6>,
<x^12 + 2*x^6 + x^5 + x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^6 + x^5 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^6 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + 2*x^5 + x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^6 + x^5 + x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^5 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^7 + x^5 + x^4 + 2*x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^6 + x^5 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^10 + 2*x^6 + x^5 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + x^4 + x^3 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^6 + x^5 + x^4 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^6 + 2*x^5 + x^4 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^6 + 2*x^5 + x^3 + x^2 + 2, 6>,
<x^12 + x^7 + x^6 + x^5 + 2*x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + 2*x^6 + 2*x^5 + x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^4 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^6 + x^4 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^4 + 2*x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + x^5 + x^4 + 2*x^3 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + 2*x^5 + x^4 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + x^5 + 2*x^4 + x^2 + 1, 6>,
<x^12 + x^7 + 2*x^6 + x^5 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + 2*x^4 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^6 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + x^6 + x^5 + 2*x^4 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + x^6 + 2*x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^3 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + x^6 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^5 + 2*x^4 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^5 + 2*x^4 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^8 + x^7 + x^5 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^6 + x^5 + x^3 + x + 1, 6>,
<x^12 + x^7 + x^6 + x^5 + 2*x^4 + x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^6 + x^4 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^6 + x^5 + x^4 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + x^6 + x^5 + x^3 + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^6 + 2*x^5 + x^3 + x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^7 + x^5 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^6 + x^4 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + x^6 + x^5 + 2*x^3 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + x^5 + 2*x^4 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + 2*x^6 + x^5 + 2*x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^4 + x^3 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^5 + x^2 + 1, 6>,
<x^12 + x^8 + x^7 + 2*x^5 + 2*x^4 + x + 2, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + 2*x^4 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^5 + 2*x^4 + x^2 + 2*x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^5 + x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + 2*x^5 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + x^5 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + x^2 + x + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + 2*x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^8 + x^7 + 2*x^5 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + x^5 + x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^6 + 2*x^5 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^4 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^6 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^5 + 2*x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + 2*x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x + 2, 6>,
<x^12 + x^11 + x^6 + x^5 + 2*x^4 + x + 1, 6>,
<x^12 + 2*x^10 + 2*x^8 + 2*x^6 + x^5 + 2*x^3 + x + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^4 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + x^5 + 2*x^4 + x + 2, 6>,
<x^12 + x^6 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^5 + 2*x^2 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^6 + x^5 + x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + 2*x^8 + x^7 + 2*x^6 + 2*x^4 + x + 2, 6>,
<x^12 + x^11 + x^7 + x^5 + 2*x^4 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^6 + 2*x^5 + 2*x^4 + x^3 + 1, 6>,
<x^12 + x^11 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^8 + x^6 + x^5 + x^3 + 2*x + 2, 6>,
<x^12 + x^10 + x^7 + x^6 + 2*x^5 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + x^6 + x^5 + x^4 + 2*x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + 2*x^4 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^5 + x^4 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^6 + x^5 + 2*x^4 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + 2*x^5 + 2*x^4 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^5 + x^4 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x^6 + x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^7 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + x^5 + 2*x^4 + x^2 + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^4 + 2*x^3 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + x^6 + 2*x^5 + x^4 + x^3 + x + 2, 6>,
<x^12 + x^8 + x^7 + x^5 + 2*x^4 + x^2 + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^4 + 2*x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^6 + 2*x^5 + x^4 + 2*x^3 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + x^5 + 2*x^4 + x^3 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^4 + x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^8 + x^7 + x^5 + x^4 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^6 + 2*x^5 + x^4 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^6 + x^5 + x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^8 + x^7 + 2*x^6 + x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^7 + 2*x^5 + x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + x^4 + x^3 + x + 2, 6>,
<x^12 + x^11 + x^8 + 2*x^7 + x^4 + 1, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + 2*x^6 + x^5 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^5 + 2*x^4 + x^2 + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + 2*x^5 + 2*x^4 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^6 + x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 1, 6>,
<x^12 + 2*x^10 + x^8 + x^6 + x^5 + 2*x^2 + 2*x + 1, 6>,
<x^12 + 2*x^8 + x^7 + 2*x^5 + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^7 + 2*x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^6 + 2*x^5 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^5 + x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^5 + x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^8 + 2*x^6 + x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x + 1, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + 2*x^6 + 2*x^5 + x^4 + x^3 + x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + 2*x^7 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + 2*x^6 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^5 + x^4 + 2*x^3 + x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^6 + x^5 + x^4 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^7 + 2*x^5 + x^4 + x^3 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^6 + x^5 + x^3 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + 2*x^5 + 2*x^3 + x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^7 + 2*x^6 + x^5 + 2*x^4 + x^3 + 2*x^2 + x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + x^10 + 2*x^6 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^7 + x^6 + 2*x^4 + 2*x^3 + 1, 6>,
<x^12 + 2*x^10 + x^8 + x^6 + 2*x^4 + x^3 + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + x^6 + x^5 + 2*x^4 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + 2*x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + 2*x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^10 + x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^7 + 2*x^4 + 2*x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + 2*x^7 + x^5 + 2*x^4 + 2*x^3 + x + 2, 6>,
<x^12 + 2*x^10 + x^9 + 2*x^8 + x^6 + x^4 + 2*x^2 + 2*x + 2, 6>,
<x^12 + 2*x^10 + x^6 + x^5 + x^2 + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^6 + 2*x^2 + 2, 6>,
<x^12 + 2*x^10 + x^6 + 2*x^4 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^6 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^8 + x^6 + 2*x^4 + 2*x^3 + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^6 + x^4 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^7 + 2*x^6 + x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^6 + x^4 + x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + 2*x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + 2*x^8 + x^7 + 2*x^5 + 2*x^4 + x^3 + x + 1, 6>,
<x^12 + x^11 + x^9 + x^6 + x^5 + x^4 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + 2*x^5 + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^6 + 2*x^5 + x + 2, 6>,
<x^12 + 2*x^10 + x^8 + x^6 + x^5 + x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + x^8 + x^6 + x^5 + x^4 + x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^7 + 2*x^6 + x^4 + x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^5 + 2*x^4 + 2*x^2 + x + 2, 6>,
<x^12 + x^8 + x^7 + x^6 + x^5 + 2*x^4 + 2*x^3 + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + x^6 + x^5 + 2*x^4 + 2*x^3 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + 2*x^6 + 2*x^5 + x^4 + x + 2, 6>,
<x^12 + x^11 + x^9 + x^8 + x^7 + x^4 + x^2 + 1, 6>,
<x^12 + x^11 + 2*x^8 + 2*x^6 + 2*x^4 + x + 2, 6>,
<x^12 + x^11 + 2*x^7 + x^6 + 2*x^4 + x^3 + 2, 6>,
<x^12 + x^8 + x^6 + x^4 + x^2 + x + 1, 6>,
<x^12 + x^11 + 2*x^9 + x^8 + x^7 + 2*x^6 + x^3 + x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + 2*x^7 + 2*x^4 + x^3 + 2*x^2 + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + x^6 + 2*x^5 + 2*x^4 + 2*x^2 + 2, 6>,
<x^12 + x^10 + 2*x^8 + x^7 + x^6 + x^5 + x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^8 + x^7 + 2*x^6 + 2*x^5 + x^4 + 2*x^2 + 1, 6>,
<x^12 + x^10 + x^8 + x^7 + 2*x^6 + 2*x^5 + x^4 + 2*x^2 + 2, 6>,
<x^12 + x^11 + 2*x^9 + 2*x^8 + x^7 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + x + 1, 6>,
<x^12 + x^11 + x^9 + 2*x^8 + x^7 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^9 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^3 + x^2 + x + 1, 6>,
<x^12 + 2*x^10 + x^9 + x^8 + 2*x^6 + x^5 + 2*x^4 + 2*x + 1, 6>,
<x^12 + x^10 + x^7 + x^6 + 2*x^5 + 2*x^3 + x + 2, 6>,
<x^12 + x^10 + x^8 + x^7 + x^5 + x^2 + 2*x + 2, 6>,
<x^12 + x^11 + x^7 + x^6 + x^5 + x^3 + 2*x^2 + 2*x + 1, 6>,
<x^12 + x^11 + 2*x^8 + x^7 + x^6 + 2*x^5 + 2*x^4 + 2*x^3 + x^2 + 2*x + 2, 6>,
<x^12 + 2*x^10 + x^9 + x^6 + x^2 + 1, 6>];

procedure GetData2(l, q, d, orbitreps, output_file : filt_sequence := true, auts := false, filter_by_cup_products := [])
    
    select_data := false;

    // Collecting data on representatives of equivalence classes of polynomials
    for rep in orbitreps do
        f := rep[1];
        cups := CupProducts(f, l);
        data_string :=  Sprintf("%o; %o; %o; %o; %o; %o", l, q, Order(GF(l)!q), f, rep[2], cups);
        if filt_sequence then
            filtseq, Gstructure := FiltrationSequence(f, l);
            data_string cat:= Sprintf("; %o; %o; %o", Gstructure, filtseq, #filtseq);
        end if;
        fprintf output_file, data_string cat "\n";
    end for;
end procedure;

//GetData2(7, 3, 12, allorbitreps[662..711], "data2.txt" : filt_sequence := true);