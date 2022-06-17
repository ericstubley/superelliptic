function DataSet(output_file, l, q, d)
/* compute cup products, class groups for
- each irreducible polynomial f(t) of degree d
- having coefficients in Fq
- for the curve y^l - f(t)

write everything to output file
- l
- q 
- d
- polynomial
- class group full structure
- class group l rank
*/
    PrintFile(output_file, "l, q, d, polynomial, class group structure, l-rank");

    F := GF(q);
    FF<x> := FunctionField(F);
    PolFF<y> := PolynomialRing(FF);
    pols := AllIrreduciblePolynomials(F, d);

    for p in pols do
        // make function field
        FFext := ext<FF | y^l - p>;

        // compute class group
        cg := ClassGroup(FFext);
        cg_summands := [Order(g) : g in Generators(cg) | Order(g) ne 0];

        // compute l-rank
        rank := 0;
        for g in Generators(cg) do
            if (Order(g) ne 0) and ((Order(g) mod l) eq 0) then
                rank := rank + 1;
            end if; 
        end for;

        // write to file
        output_string := Sprintf("%o, %o, %o, %o, %o, %o\n", l, q, d, p, cg_summands, rank);
        PrintFile(output_file, output_string);

    end for;

    return #pols;
end function;