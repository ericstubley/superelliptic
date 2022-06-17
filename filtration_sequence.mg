function Frobenius(K, q)
    // return the map K->K given by applying Frobenius to all constants

    q := Characteristic(K);
    Fqgamt<t> := BaseRing(K);
    Fqgam<a> := BaseRing(Fqgamt);
    frob0 := hom<Fqgam -> K | K!a^q>;
    frob1 := hom<Fqgamt -> K | frob0, K!t>;
    return hom<K -> K | frob1, K.1>;
end function;

function IncludelthRootsOfUnity(K, l)
    // Input:  function field K and a prime l (not equal to characteristic of K)
    // Return: an extension L of K, an embedding KtoL mapping K into L, and
    //         an l-th root of unity zeta in L.
    
    k := ConstantField(K);
    q := Characteristic(k);
    gamma := Order(GF(l)!q);
    kk := CommonOverfield(k, GF(q^gamma));
    L, KtoL := ConstantFieldExtension(K, kk);
    zeta := L ! (kk.1^(Order(kk.1) div l));
    return L, KtoL, zeta;
end function;

function Pushforward(D, phi)
    // Input:  a divisor or place D on a function field K, 
    //         and a map phi from K to an extension L.
    // Return: the divisor on L obtained by applying phi to all the functions
    //         used to define places of D.

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
    // Input:  a divisor D on a function field
    // Return: a divisor linearly equivalent to D, usually simpler
    Dprime, r, A := Reduction(D);
    return Dprime + r*A;
end function;

function FindRelations(Dlist, l)
    // Input:  A sequence of l-torsion divisors [D1, ..., Dn] for some integer l
    // Output: A sequence of n-dim vectors c with the property that sum c[i]*Di = 0,
    //         and every relation of this form is in the span of the returned vectors.

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
    // successively apply (lambda-1) to D until reaching 0
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

function FiltDims(Dlists, l)
    // Input:  a sequence of the form [[v1, Tv1, T^2v1, ...], ..., [vn, Tvn, T^2vn, ....]] 
    //         where v1,...,vn are independent divisors, and the last element of each list is
    //         in ker(T). (The lists do not need to be the same length)
    // Return: A sequence of sequences of integer vectors. If u is a vector in the j-th sequence,
    //         then sum u[i]*vi is in ker T^j; further, the vectors in the j-th sequence
    //         span the kernel of the restriction of T^(j-1) to v1,...,vn.

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
        //nextker;
        Append(~kerlist, nextker);
        Append(~indeplist, indeps);
    end for;
    return Reverse(kerlist), Reverse(indeplist);
end function;

function FiltBasis(K, l)
    // Description

    // construct an extension L over which lambda is defined
    L<y>, KtoL, zeta := IncludelthRootsOfUnity(K, l);
    Fgamt<t> := BaseRing(L);
    Fgam<a> := BaseRing(Fgamt);
    lambda := hom<L -> L | zeta * y>;

    // find a basis for the K-rational l-torsion points, base changed 
    // to L, as well as their images under (lambda-1)^j for all j.
    G, h := ClassGroup(K);
    Dlists := [];
    for g in Generators(G) do
        if Order(g) ne 0 and IsDivisibleBy(Order(g), l) then
            // get basis vector for K-rational l-torsion
            D := DivReduce(h((Order(g) div l) * g));
            newD := DivReduce(Pushforward(D, KtoL));  
            Append(~Dlists, LambdaMinusOneImages(newD, lambda, l));
        end if;
    end for;

    return Dlists, lambda;
end function;

function FiltrationSequence(K)
    //Description

    l := Degree(MinimalPolynomial(K.1));
    Dlists := FiltBasis(K, l);
    _, indeps := FiltDims(Dlists, l);
    return [i : i in [1..#indeps] | #indeps[i] gt 0];
end function;

function CupProducts(f, l)
    q := #BaseRing(Parent(f));
    gamma := Order(GF(l)!q);
    if gamma ne Degree(f) then
        error "Code only works if Degree(f) equals order of q mod l";
    end if;
    k<c> := GF(q^gamma);
    Pol<x> := PolynomialRing(k);
    ff := ChangeRing(f, k);
    alpha := Roots(ff)[1][1];

    assert &*[(x - alpha^(q^i)) : i in [0..gamma-1]] eq ff;

    testvals := [&*[(alpha - alpha^(q^i))^(q^(j*i)-1) : i in [1..gamma-1]] : j in [0..gamma-1]];
    return [IsPower(val, l) select 0 else 1 : val in testvals];
end function;

/* sample use:

l := 7;
q := 3;
d := 6;
Fq := GF(q);
Pol<x> := PolynomialRing(Fq);
Fqt<t> := FunctionField(Fq);
Pol<Y> := PolynomialRing(Fqt);

f := x^6 + x^4 + x^3 + x^2 + 2*x + 2;
K<y> := ext< Fqt | Y^l - f >;
print FiltrationSequence(K);
print CupProducts(f, l);
print #Automorphisms(K);

f := x^6 + x^5 + x^3 + x^2 + 1;
K<y> := ext< Fqt | Y^l - f >;
print FiltrationSequence(K);
print CupProducts(f, l);
*/
