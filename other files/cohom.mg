l := 7;
q := 5;
gamma := Order(GF(l)!q);
Fq<u> := GF(q);
Fqt<x> := FunctionField(Fq);
Pol<Y> := PolynomialRing(Fqt);

f := x^6 + x^4 + 2*x^3 + x^2 + 2*x + 4;
K<y> := ext< Fqt | Y^l - f >;


function Frob(R, q)
    /*
    R a polynomial ring; return the map R->R given by applying q-th power to all constants
    */

    k<a> := BaseRing(R);
    frob0 := hom<k -> k | a^q>;
    return hom<R -> R | frob0, R.1>;
end function;


G := AffineGeneralLinearGroup(1,l);
rho := GModule(G, MatrixAlgebra< GF(l), 2 | [q,0,0,1], [1,1,0,1] >);

for a in [0..6] do
    for b in [0..6] do
        for c in [0..6] do
            theta := GModule(G, MatrixAlgebra< GF(l), 3 | [q^2,0,0, 0,q,0, 0,0,1], [1,1,1/2, 0,1,1, 0,0,1] >);
            try
                SetOutputFile("trash.txt");
                CM := CohomologyModule(G, theta);
                UnsetOutputFile();
                print a,b,c,"YAY";
            catch e
                UnsetOutputFile();
            end try;            
        end for;
    end for;
end for;