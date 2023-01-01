/*
A model for determining which cohomology classes lift. The main objects are sequences
[k_1, ..., k_gamma], where an entry k_i means that a_i^[k_i] exists, and if k_i is not
equal to the maximum value of the sequence, then a_i^[k_i+1] does not exist.

Basic methods include:
- Lift: finds all possible one-step lifts of a given starting sequence, assuming
        the lifting relations proven in the paper.
- LiftList: finds all possible one-step lifts of a list of starting sequences
- AllLifts: finds all possible final lifting sequences for a given set of parameters

*/

function red(n, gamma)
    /* computes n mod gamma in the range [1..gamma] */

    return ((n-1) mod gamma) + 1;
end function;

function Lift(f : l := 0, conj := false)
    /*
    given a lifting sequence with maximal height k, produce all possible lifts to height k+1.
    If l is provided, do not lift past highest contributing class unless forced to by the rules.
    */

    newf := f;
    k := Max(f);
    gamma := #f;
    pairreps := [];
    gammadividesd := (Min(f) ge 0);

    tolift := (l ne 0) select [1..Min(gamma,l-k-1)] else [1..gamma];

    for n in [n : n in tolift | f[n] eq k] do
    
        // a_1^[k] always lifts; a_{-k}^[k] is the dual to a_1
        if n eq 1 or (n+k) mod gamma eq 0 then
            newf[n] := k+1;
        end if;

        // either a_n^[k] can be modified by an obstruction, or its dual exists and can be so modified        
        for j in [1..k+1] do
            if f[red(n+j, gamma)] eq k - j or (f[red(1-k-n, gamma)] eq k and f[red(1-k-n+j, gamma)] eq k - j) then
                newf[n] := k+1;
            end if;
        end for;

        //self-dual
        if k eq 1 and gammadividesd and (2*n) mod gamma eq 0 then
            newf[n] := 2;
        end if;

        //conjectural self-dual
        if conj and (k-1) mod 2 eq 0 and (2*n + k - 1) mod gamma eq 0 then
            newf[n] := k+1;
        end if;

        // pick one a_n^[k] from each dual pair where lifting is possible but not forced
        if newf[n] eq k and not red(1-k-n, gamma) in pairreps then
            Include(~pairreps, n); 
        end if;
    end for;

    newfs := [newf]; // modify this to get all possible lifts

    for n in pairreps do
        tempfs := [];
        for newf in newfs do
            // adjoin the F_{k+1} obtained by not lifting a_n^k or its dual
            newfnolift := newf;
            Append(~tempfs, newfnolift);

            // adjoin the F_{k+1} obtained by lifting a_n^k, and its dual if it exists
            newflift := newf;
            newflift[n] := k+1;
            if newflift[red(1-n-k, gamma)] eq k then 
                newflift[red(1-n-k, gamma)] := k+1;
            end if;
            Append(~tempfs, newflift);
        end for;
        newfs := tempfs;
    end for;
    return newfs;
end function;


function FiltSeqBounds(filtseq, l, gamma)
    /* Given a filtration sequence, returns bounds on lifting sequences that
    can result in this filtration sequence. Specifically, returns fmin and fmax
    such that if a lifting sequence produces the given filtration sequence,
    and a_n^[k] is a rooftop, then fmin[n] <= a_n^[k] <= fmax[n]. */

    fmin := [l-2];
    fmax := [l-2];

    for n in [2..gamma] do
        kn := Max([1-n] cat [k : k in filtseq | (k+n-1) mod gamma eq 0]);
        Append(~fmin, kn);
        Append(~fmax, kn+gamma-1);
    end for;

    return fmin, fmax;
end function;

function FiltrationSequence(f)
    /* Return the filtration sequence corresponding to a given lifting sequence */

    gamma := #f;
    return [k : k in [1..Max(f)] | red(1-k, gamma) ne 1 and f[red(1-k, gamma)] ge k];
end function;

function AllLifts(l, gamma, d : start := [], filt_sequence := [], halt_after_max_contrib := true, conj := false)
    /*
    Produce an exhaustive list of all possible lifting behaviors. 
    
    If start is provided, it must be an F_k for some k; 
    the lifiting process will only consider lifts of F_k.

    If filt_sequence is provided, will only return the lifting
    sequences that result in the given filtration sequence.

    WARNING: can be very slow for large l.
    */

    if start eq [] then
        flist := [[IsDivisibleBy(d*(n-1), gamma) select 0 else -1 : n in [1..gamma]]];
        k0 := 0;
    else
        flist := [start];
        k0 := Max(start);
    end if;

    if filt_sequence eq [] then
        fmin := [-1 : i in [1..gamma]];
        fmax := [l-2 : i in [1..gamma]];
    else
        fmin, fmax := FiltSeqBounds(filt_sequence, l, gamma);
    end if;

    // Lift the starting point to F_{l-2}
    while Min([Max(f) : f in flist]) lt l-2 do
        newflist1 := [f : f in flist | Max(f) ge l-2];
        newflist2:= &cat[Lift(f : l := (halt_after_max_contrib select l else 0), conj := conj) : f in flist | Max(f) lt l-2];
        newflist2:= [f : f in newflist2 | &and[(f[n] eq Max(f) or f[n] ge fmin[n]) 
                                               and f[n] le fmax[n] : n in [1..gamma]]];
        flist := newflist1 cat newflist2;
    end while;
    
    // Collect statistics on each F_{l-1}
    fulldata := [];
    for f in flist do
        basevals := [Min(f[n], 1) : n in [1..gamma]];
        contribs := [Floor((n+f[n]-1)/gamma) : n in [2..gamma]];
        Append(~fulldata, <f, basevals, FiltrationSequence(f), &+([0] cat contribs)>);
    end for;
    return fulldata;
end function;

function PrntLst(lst : l:=0)
    /* if l is nonzero, also:
    - bold the classes that contradict odd self-dual lifting conjecture;
    - replace the all-the-way classes with ``\topclass'' */

    str := "";
    gamma := #lst;
    for n in [1..gamma] do
        elt := lst[n];
        if l ne 0 then
            if elt eq -1 then
                str cat:= "$\\emptyset$, ";
            elif n eq 1 or elt ge l-n then
                str cat:= "$\\topclass$, ";
            elif (2*n + elt - 1) mod gamma eq 0 then
                str cat:= "\\textbf{" cat IntegerToString(elt) cat "}, ";
            else
                str cat:= IntegerToString(elt) cat ", ";
            end if;
        else
            str cat:= (elt eq -1) select "$\\emptyset$, " else IntegerToString(elt) cat ", ";
        end if;
    end for;
    return str[1..#str-2];
end function;


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

        data := <eval term : term in terms>;

        if #data eq 6 then
            Append(~data, []);
            lifts := AllLifts(data[1], data[3], Degree(data[4]) : start := data[6]);
            if #lifts eq 1 then
                Append(~data, lifts[1][3]);
            else
                Append(~data, []);
            end if;
        end if;

        Append(~newdata, data);
    end for;
    return newdata;
end function;

procedure ProcessData(inputdata, output_file : shorten_if_beyond := 50)
    /* generates a LaTeX table with much info */

    alldata := RetrieveData(inputdata);

    lvals := Sort(SetToSequence(SequenceToSet([data[1] : data in alldata])));
    for l in lvals do
        filt1 := <data : data in alldata | data[1] eq l>;
        gammavals := Sort(SetToSequence(SequenceToSet([data[3] : data in filt1])));
        for gamma in gammavals do
            filt2 := <data : data in filt1 | data[3] eq gamma>;
            gcdvals := Sort(SetToSequence(SequenceToSet([GCD(data[3], Degree(data[4])) : data in filt2])));
            for gcd in gcdvals do
                fprintf output_file, "%o, %o, %o: \n", l, gamma, gcd;
                filt3 := <data : data in filt2 | GCD(data[3], Degree(data[4])) eq gcd>;
                alllifts := AllLifts(l, gamma, gcd);
                conjlifts := AllLifts(l, gamma, gcd : conj := true);
                orderlifts := conjlifts cat [lift : lift in alllifts | not lift in conjlifts];
                seen := [];

                sat := 0;
                notsat := 0;
                for lift in orderlifts do
                    if not lift in seen then
                        filt4 := <data : data in filt3 | data[6] eq lift[2] and data[8] eq lift[3]>;
                        duplist := [other : other in orderlifts | other[2] eq lift[2] and other[3] eq lift[3]];
                        seen cat:=duplist;

                        if #alllifts gt shorten_if_beyond and #filt4 eq 0 then
                            for other in duplist do
                                if other in conjlifts then sat +:= 1; else notsat +:= 1; end if;
                            end for;
                        else
                            fprintf output_file, "\\vtop{";
                            for other in duplist do
                                fprintf output_file, "\\hbox{\\strut %o}", PrntLst(other[1] : l := l);
                            end for;
                            fprintf output_file, "} & \\vtop{";
                            for other in duplist do
                                fprintf output_file, "\\hbox{\\strut %o}", (other in conjlifts) select "yes" else "no";
                            end for;
                            fprintf output_file, "} & %o & %o & %o & ", PrntLst(lift[2]), PrntLst(lift[3]), lift[4];
                            if #filt4 eq 0 then
                                fprintf output_file, "\\multicolumn{3}{c|}{none found} \\\\\n";
                            end if;

                            firstline := true;
                            qvals := Sort(SetToSequence(SequenceToSet([data[2] : data in filt4])));
                            for q in qvals do
                                filt5 := <data : data in filt4 | data[2] eq q>;
                                dvals := Sort(SetToSequence(SequenceToSet([Degree(data[4]) : data in filt5])));
                                for d in dvals do
                                    filt6 := <data : data in filt5 | Degree(data[4]) eq d>;
                                    if firstline then firstline := false;
                                    else fprintf output_file, " & & & & & ";
                                    end if;
                                    fprintf output_file, "%o & %o & %o \\\\\n", q, d, #filt6;
                                end for;
                            end for;
                            fprintf output_file, "\\hline ";
                        end if;
                    end if;
                end for;

                if #alllifts gt shorten_if_beyond then
                    fprintf output_file, " %o sequences & yes & & & & \\multicolumn{3}{c|}{none found} \\\\\n \\hline ", sat;
                    fprintf output_file, " %o sequences & no & & & & \\multicolumn{3}{c|}{none found} \\\\\n \\hline ", notsat;
                end if;

                leftovers := <data : data in filt3 | not (data[6] in [lift[2] : lift in alllifts] and data[8] in [lift[3] : lift in alllifts])>;
                basevals := SetToSequence(SequenceToSet([data[6] : data in leftovers]));
                for baseval in basevals do
                    fprintf output_file, "not computed & ? & %o & & & ", PrntLst(baseval);

                    filt4 := <data : data in leftovers | data[6] eq baseval>;
                    firstline := true;
                    qvals := Sort(SetToSequence(SequenceToSet([data[2] : data in filt4])));
                    for q in qvals do
                        filt5 := <data : data in filt4 | data[2] eq q>;
                        dvals := Sort(SetToSequence(SequenceToSet([Degree(data[4]) : data in filt5])));
                        for d in dvals do
                            filt6 := <data : data in filt5 | Degree(data[4]) eq d>;
                            if firstline then firstline := false;
                            else fprintf output_file, " & & & & & ";
                            end if;
                            fprintf output_file, "%o & %o & %o \\\\\n", q, d, #filt6;
                        end for;
                    end for;
                    fprintf output_file, "\n\\hline ";
                end for;
                fprintf output_file, "\n";
            end for;
        end for;
    end for;



    /*
    // sort curves into classes based on parameters
    collection := AssociativeArray();
    for eachdata in alldata do
        data := eachdata;
        if #data eq 6 then data cat:= <[], []>; end if;

        sort1 := [data[1], data[3], GCD(data[3], Degree(data[4]))];
        if not sort1 in Keys(collection) then collection[sort1] := AssociativeArray(); end if;
        sort2 := [data[6], data[8]];
        if not sort2 in Keys(collection[sort1]) then collection[sort1][sort2] := AssociativeArray(); end if;
        sort3 := [data[2], Degree(data[4])];
        if not sort3 in Keys(collection[sort1][sort2]) then 
            collection[sort1][sort2][sort3] := 1;
        else
            collection[sort1][sort2][sort3] +:= 1;
        end if;
    end for;

    // process the collection
    for sort1 in (Keys(collection)) do
        l := sort1[1];
        gamma := sort1[2];
        gcd := sort1[3];
        first1 := true;
        for sort2 in (Keys(collection[sort1])) do
            basevals := sort2[1];
            filtseq := sort2[2];

            lifts := [s[1] : s in AllLifts(l, gamma, gcd : start := basevals, filt_sequence := filtseq)];
            if #lifts gt 1 then
                print l,gamma,gcd,basevals,filtseq,#lifts;
            end if;
            first2 := true;

            for sort3 in (Keys(collection[sort1][sort2])) do
                q := sort3[1];
                d := sort3[2];

                if first1 then 
                    fprintf output_file, Sprintf("$%o$ & $%o$ & $%o$ & ", l, gamma, gcd);
                    first1 := false;
                else fprintf output_file, " & & & "; end if;
                if first2 then 
                    fprintf output_file, "$" cat PrntLst(basevals) cat "$ & ";
                    if filtseq eq [] then 
                        filtseqs := SetToSequence(SequenceToSet([FiltrationSequence(lift) : lift in lifts]));
                        fprintf output_file, "($" cat PrntLst(filtseqs[1]) cat "$";
                        for filt in filtseqs[2..#lifts] do
                            fprintf output_file, " or $" cat PrntLst(filt) cat "$";
                        end for;
                        fprintf output_file, ") & ";
                    else 
                        fprintf output_file, "$" cat PrntLst(filtseq) cat "$ & ";
                    end if;
                    fprintf output_file, "$" cat PrntLst(lifts[1][2..#lifts[1]]) cat "$ ";
                    for lift in lifts[2..#lifts] do
                        fprintf output_file, "or $" cat PrntLst(lift[2..#lift]) cat "$ ";
                    end for;
                    fprintf output_file, "& ";
                    first2 := false;
                else fprintf output_file, " & & & "; end if;
                fprintf output_file, "$%o$ & $%o$ & $%o$ \\\\\n", q, d, collection[sort1][sort2][sort3];
            end for;
        end for;
        fprintf output_file, "\\hline\n";
    end for;
    */
end procedure;

/*
function RankData(l, gamma, d : count := 0, CupProds := [], prob := -1)
    /*
    Return a list of the possible ranks. If a natural number is given
    for option "count," that many random lifts will be computed (with the probability
    of lifting determined by prob), potentially returning only a subset of the 
    possible ranks. Otherwise, all lifts will be computed.
    
    Option "CupProds" only makes a difference if gamma divides d. In this case,
    F_1 is initialized so that the specified cup products a_n cup with a_1 to 0
    (as well as a_1 itself and any other relations forced by duality).
    

    start := [IsDivisibleBy(d*(n-1), gamma) select 0 else -1 : n in [1..gamma]];

    // initialize F_1 with designated lifts
    if (#CupProds ne 0) and (d mod gamma eq 0) then 
        Include(~CupProds, 1);
        for n in CupProds do
            start[n] := 1;
            start[red(1-n, gamma)] := 1;
        end for;
    end if;

    if count le 0 then
        flist := AllLifts(l, gamma, d : start := start, prob := prob);
    else
        flist := RandomLifts(l, gamma, d, count : start := start, prob := prob);
    end if;
    
    // add up the proportion (f[5]) of results with each given rank (f[4]).
    maxrank := (GCD(d, gamma) - 1) * (l-1) / gamma;
    rankamounts := [&+([0] cat [f[5] : f in flist | f[4] eq rank]) : rank in [0..maxrank]];
    return [rank : rank in [0..maxrank] | rankamounts[rank+1] ne 0];
end function;
*/

/* sample use cases:

print "All possible lifting behaviors for l=7, gamma=d=6:";
print "<lifting behavior, vanishing sequence, contributions to rank, rank, probability>";
l:=7; gamma:=6; d:=6;
print AllLifts(l, gamma, d);
*/

/*

print "Starting with a prescribed lifting sequence:";
print "(a_1,a_3,a_4,a_6 all cup to 0 with b):";
start := [1,0,1,1,0,1]; 
print AllLifts(l, gamma, d : start := start);
print "(all cup products vanish):";
start := [1,1,1,1,1,1]; 
print AllLifts(l, gamma, d : start := start);
*/

/*
l:=17; gamma:=16; d:=16;
print "Generate some lifts randomly (good for larger l)";
print RandomLifts(l, gamma, d, 5 : prob := 3/4);

print "Extract possible ranks from a given set of cup product vanishing";
print RankData(l, gamma, d : CupProds:=[2,3], prob := 3/4);
*/