/*
A model for determining which cohomology classes lift. The main objects are sequences
[k_1, ..., k_gamma], where an entry k_i means that a_i^[k_i] exists, and if k_i is not
equal to the maximum value of the sequence, then a_i^[k_i+1] does not exist.

Basic methods include:
- Lift: finds all possible one-step lifts of a given starting sequence
- LiftList: finds all possible one-step lifts of a list of starting sequences
- AllLifts: finds all possible final lifting sequences for a given set of parameters
- 
*/

function red(n, gamma)
    /* computes n mod gamma in the range [1..gamma] */

    return ((n-1) mod gamma) + 1;
end function;

function Lift(f, k, gamma, prob)
    /*
    given F_k, produces all possible F_{k+1}. A probability is assigned to each lift according to
    the value of prob: if a lift is possible but not guaranteed, it occurs with probability prob.
    */

    newf := f;
    pairreps := [];

    for n in [n : n in [1..gamma] | f[n] eq k] do
        if n eq 1 or (n+k) mod gamma eq 0 or (k ge 1 and (2*n+k-1) mod gamma eq 0) then
            // a_1^[k] always lifts; a_{-k}^[k] is the dual to a_1; self-duals always lift unless k=0.
            newf[n] := k+1;
        end if;
        for j in [1..k+1] do
            if f[red(n+j, gamma)] eq k - j or (f[red(1-k-n, gamma)] eq k and f[red(1-k-n+j, gamma)] eq k - j) then
                // either a_n^[k] can be modified by an obstruction, or its dual exists and can be so modified
                newf[n] := k+1;
            end if;
        end for;

        if newf[n] eq k and not red(1-k-n, gamma) in pairreps then
            // include one a_n^[k] from each dual pair where lifting is possible but not forced
            Include(~pairreps, n); 
        end if;
    end for;

    newfs := [<newf, 1>]; // modify this to get all possible lifts

    for n in pairreps do
        tempfs := [];
        for newfpair in newfs do
            // adjoin the F_{k+1} obtained by not lifting a_n^k or its dual
            newfnolift := newfpair[1];
            probnolift := newfpair[2] * (1-prob);
            Append(~tempfs, <newfnolift, probnolift>);

            // adjoin the F_{k+1} obtained by lifting a_n^k, and its dual if it exists
            newflift := newfpair[1];
            problift := newfpair[2] * prob;
            newflift[n] := k+1;
            if newflift[red(1-n-k, gamma)] eq k then 
                newflift[red(1-n-k, gamma)] := k+1;
            end if;
            Append(~tempfs, <newflift, problift>);
        end for;
        newfs := tempfs;
    end for;
    return newfs;
end function;

function LiftList(flist, k, gamma, prob)
    /* Apply Lift to every F_k in a list, propagating probabilities accordingly */

    newflist := [];
    for fpair in flist do
        f := fpair[1];
        fprob := fpair[2];
        newflist cat:= [<c[1], fprob * c[2]> : c in Lift(f, k, gamma, prob)];
    end for;
    return newflist;
end function;

function VanishingSequence(f)
    /* The values of n such that a_n cup b = 0 (i.e. a_n^[1] exists) */

    return [n : n in [1..#f] | f[n] ge 1];
end function;

function Contributions(f, gamma)
    /* The number of times each a_n contributes to the l-rank */

    return [Floor((f[n]+n)/gamma) : n in [2..gamma]];
end function;

function AllLifts(l, gamma, d : start := [], prob := -1)
    /*
    Produce an exhaustive list of all possible F_{l-2}. If start is provided, 
    it must be an F_k for some k; the lifiting process will only consider lifts of F_k.

    WARNING: can be very slow for large l. "RandomLifts" is recommended.
    */

    if prob eq -1 then prob := 1/l; end if;

    if start eq [] then
        f0 := [IsDivisibleBy(d*(n-1), gamma) select 0 else -1 : n in [1..gamma]];
        k0 := 0;
    else
        f0 := start;
        k0 := Max(start);
    end if;

    // Lift the starting point to F_{l-2}
    flist := [<f0, 1>];
    for k in [k0..l-4] do
        flist := LiftList(flist, k, gamma, prob);
    end for;
    
    // Collect statistics on each F_{l-2}
    fulldata := [];
    for fpair in flist do
        vanseq := VanishingSequence(fpair[1]);
        contrib := Contributions(fpair[1], gamma);
        Append(~fulldata, <fpair[1], vanseq, contrib, &+([0] cat contrib), fpair[2]>);
    end for;
    return fulldata;
end function;

function RandomLift(l, gamma, d : start := [], prob := -1)
    /*
    Like AllLifts except it only returns a single F_{l-2} with some probability.
    Better for large l. prob (by default set to 1/l) can be increased 
    to make it more likely for classes to lift.
    */

    if prob eq -1 then prob := 1/l; end if;

    if start eq [] then
        f := [IsDivisibleBy(d*(n-1), gamma) select 0 else -1 : n in [1..gamma]];
        k0 := 0;
    else
        f := start;
        k0 := Max(start);
    end if;


    for k in [k0..l-4] do
        flist := Lift(f, k, gamma, prob);
        markers := [&+[fpair[2] : fpair in flist[1..i]] : i in [1..#flist]];
        denom := LCM([Denominator(marker) : marker in markers]);
        testval := Random(1, denom)/denom;
        i := Index(Sort(Append(markers, testval)), testval);
        f := flist[i][1];
    end for;
    
    vanseq := VanishingSequence(f);
    contrib := Contributions(f, gamma);
    return <f, vanseq, contrib, &+([0] cat contrib), 1>;
end function;

function RandomLifts(l, gamma, d, count : start := [], prob := -1)
    /* returns "count" many instances of RandomLift. */

    return [RandomLift(l, gamma, d : start := start, prob := prob) : i in [1..count]];
end function;

function RankData(l, gamma, d : count := 0, CupProds := [], prob := -1)
    /*
    Return a list of the possible ranks. If a natural number is given
    for option "count," that many random lifts will be computed (with the probability
    of lifting determined by prob), potentially returning only a subset of the 
    possible ranks. Otherwise, all lifts will be computed.
    
    Option "CupProds" only makes a difference if gamma divides d. In this case,
    F_1 is initialized so that the specified cup products a_n cup with a_1 to 0
    (as well as a_1 itself and any other relations forced by duality).
    */

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