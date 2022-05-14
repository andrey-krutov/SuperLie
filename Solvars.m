(* ::Package:: *)

(* Solving linear equations with parameters *)

BeginPackage["SuperLie`Solvars`",
  {"SuperLie`", "SuperLie`Genvect`"}]

ParamSolve::usage = "ParamSolve[equs, var] solves a system of linear equations with respect to
given unknown(s) var. (the equations are not necessary linear with respect to other parameters).
Returns the general solution and prints a message every time then eliminating of a variable
requires dividing by a non-constant. ParamSolve[equs, var, elim] first eliminates the valiable(s)
given in elim. Each of parameters var and elim may be a list of variables, a single variable or a
pattern matching the variables. If the characteristic of the base field is p>0, the function solves
the equations modulo p."

(*PatternQ::usage = "PatternQ[e] returns True if e contains a pattern"*)

SolveSupportsPattern::usage = "SolveSupportsPattern[solve] returns True if vars in
solve[equs, vars] is allowed to be a pattern"

ParamAssume::usage = "ParamAssume[code] executes the code and collects all assumption
made by ParamSolve while solving equations. Returns list {result of code, assumptions}"

$ParamAssume::usage = "Collects the cumulative list of assumptions made by consecuteve calls of ParamSolve.
Use $ParamAssume = False to disable cumulative assumptions; $ParamAssume = {} to clear the list and
$ParamAssume = list to define set user-defined assumptions"

UserRate::usage = "Rating function for selecting variables in ParamSolve"

Begin["$`"]

ParamAssume[body_] :=
  If[$ParamAssume===False,
    Block[{$ParamAssume={}}, {body, $ParamAssume}]
    With[{old=$ParamAssume}, Block[{$ParamAssume=old}, {body, Complement[$ParamAssume,old]}]]]

Attributes[ParamAssume] ^= {HoldAll}

$ParamAssume = False

PatternQ[_Alternatives] = True;
PatternQ[_Blank] = True;
PatternQ[_BlankSequence] = True;
PatternQ[_BlankNullSequence] = True;
PatternQ[_Pattern] = True;
PatternQ[_PatternTest] = True;
PatternQ[h_[args__]] := TrueQ[Scan[If[PatternQ[#], Return[True]] &, {args}]];
PatternQ[_] = False;

ToPattern[expr_] :=
  Which[
    PatternQ[expr], expr,
    ListQ[expr], Alternatives @@ expr,
    True, expr];

(* Rating function for selecting a variable for eliminating *) 

RateElim[expr_Plus, ptrn_] :=
  Module[{nvar = 0, deg = Infinity, userRate=Infinity, var, rate, ex},
    Do[rate = RateElimMonom[expr[[i]], ptrn];
      If[ListQ[rate],
        nvar++;
        If[rate[[1]] < userRate || rate[[1]] == userRate && rate[[2]] <deg,
          userRate = rate[[1]]; deg = rate[[2]]; var = rate[[3]]; ex = expr[[i]] ]],
      {i, 1, Length[expr]}];
    If[nvar > 0,
      {userRate, deg, nvar, var, DeleteCases[ex,ptrn]},
      False]]

RateElim[expr_, ptrn_] :=
  With[{rate = RateElimMonom[expr, ptrn]},
    If[ListQ[rate],
      {rate[[1]], rate[[2]], 1, rate[[3]], DeleteCases[expr,ptrn]},
      False]]

RateElimMonom[expr_Times, ptrn_] :=
  With[{var = Cases[expr, ptrn]},
    Switch[Length[var],
      0, False,
      1, {UserRate[expr,ptrn], PolyDeg[expr], var[[1]]},
      _, Message[ParamSolve::nlim, expr, ptrn]; False]]

ParamSolve::nlim = "Failed to eliminate from `` variables matching ``"

RateElimMonom[expr_, ptrn_] :=
  If[MatchQ[expr, ptrn], {UserRate[expr,ptrn], 1, expr}, False]

UserRate[__] := 1;


RateElim[expr_, ptrn_, maxRate_] :=
  Module[{rate, cmp},
    rate = RateElimMonom[expr, ptrn];
    cmp = CmpRateElim[rate, maxRate];
    If[cmp>=0,
      cf = DeleteCases[expr,ptrn];
      nAss = nAssum[rate[[2]], cf];
      If [cmp>0 || cmp==0 && nAss<maxRate[[3]],
        {rate[[1]], rate[[2]], nAss, 1, rate[[3]], DeleteCases[expr,ptrn]},
        False],
      False]]

RateElim[expr_Plus, ptrn_, maxRate_] :=
  Module[{nvar, ex, mr=maxRate, rates, found=False},
    rates = RateElimMonom[#, ptrn]& /@ (List @@expr);
    nvar = Count[rates,_List];
    If [nvar==0, Return[False]];
    Do[rate = rates[[i]];
      If[ListQ[rate],
        cmp = CmpRateElim[rate, mr];
        If[cmp>=0,
          ex = expr[[i]];
          cf = DeleteCases[ex,ptrn];
          nAss = nAssum[rate[[2]], cf];
          If [cmp>0 || cmp==0 && (nAss<mr[[3]] || nAss==mr[[3]] && nvar<mr[[4]]),
            found = True;
            mr = {rate[[1]], rate[[2]], nAss, nvar, rate[[3]], DeleteCases[ex,ptrn]}]]],
      {i, 1, Length[rates ]}];
    If [found, mr, False]]
 
CmpRateElim[rate_, maxRate_] :=
    Which[
     !ListQ[rate], -1,
     rate[[1]]>maxRate[[1]], -1,
     rate[[1]]<maxRate[[1]] , 1,
     rate[[2]]>maxRate[[2]], -1,
     rate[[2]]<maxRate[[2]] , 1,
     True, 0]


PolyDeg[expr_Plus] := Max @@ PolyDeg /@ List @@ expr
PolyDeg[expr_Times] := Plus @@ PolyDeg /@ List @@ expr
PolyDeg[a_^b_] := PolyDeg[a]*Abs[b]
PolyDeg[expr_] := If[NumberQ[expr], 0, 1]


ParamSolve[equ_, vars_, opts___Rule] :=
   SolVars[equ, ToPattern[vars], $p];
ParamSolve[equ_, vars_, elim_, opts___Rule] :=
   SolVars[ElimVars[equ, ToPattern[elim], $p], ToPattern[vars], $p];

modReduce[a_ != b_, p_] := 
 Reduce[a != b, {}, Modulus -> p] /. 
  Unequal -> (Mod[#1, p] != Mod[#2, p] &)

modReduce[a_ != b_, 0] := Reduce[a != b]
modReduce[u_Symbol,_] := u

(****
  Eliminates the variables matching the pattern from the given list of linear
  (relative to these variables but not necessary to other parameters) equations
  or expressions (assumed equal to zero). Returns the list of remaining expressions.
  With third parameter p, calculates all modulo p.
***)

ElimVars[equs_, ptrn_] :=
  Module[{sOrd, sDeg, sNVar, sVar, sInd, ord, deg, nVar, var, rate, exprList, sol, cf, cfi, cfn},
    exprList = $SNormal[equs /. a_ == b_ :> a - b];
    If[! ListQ[exprList], exprList = {exprList}];
    While[True,
      exprList = DeleteCases[Collect[#, ptrn] & /@ exprList, 0];
      sInd = 0;
      sOrd = Infinity;
      Do[rate = RateElim[exprList[[i]], ptrn];
        If[ListQ[rate],
          {ord, deg, nVar, var, cfi} = rate;
          If[ord < sOrd || ord == sOrd && (deg < sDeg || deg == sDeg && nVar < sNVar), 
            {sOrd, sDeg, sNVar, sVar, cf} = rate; sInd = i]],
        {i, 1, Length[exprList]}];
      If[sInd > 0,
        sol = Solve[exprList[[sInd]] == 0, sVar][[1]];
        If[sDeg>1,
          cfn = Numerator[cf];
          If[ListQ[$ParamAssume],
             If[!TrueQ[Reduce[Implies[And@@$ParamAssume, cfn]]],
                 AppendTo[$ParamAssume, cfn!=0];
                 Print["Assuming ", StyleForm[cfn!=0,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]]],
             (*else*)
             Print["Assuming ", StyleForm[cfn!=0,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]]]];
        exprList = $SNormal[Drop[exprList, {sInd}] /. sol],
      (*else*)
        Return[exprList]]]]

ElimVars[equs_, ptrn_, 0] := ElimVars[equs, ptrn] 

ElimVars[equs_, ptrn_, p_] :=
  Module[{sOrd, sDeg, sNVar, sVar, sInd, ord, deg, nVar, var, rate, exprList, sol, cf, cfi, cfn, cfni, sAss, optRate},
    exprList = $SNormal[equs /. a_ == b_ :> a - b];
    If[! ListQ[exprList], exprList = {exprList}];
    While[True,
      exprList = 
        DeleteCases[Collect[PolynomialMod[#, p], ptrn] & /@ exprList, 0];
      sInd = 0;
      optRate={Infinity};
      Do[rate = RateElim[exprList[[i]], ptrn, optRate];
        If[ListQ[rate],
          maxRate = rate;
          sInd = i],
        {i, 1, Length[exprList]}];
      If[sInd > 0,
        {sOrd, sDeg, sAss, sNVar, sVar, cf} = optRate; 
        sol = Solve[exprList[[sInd]] == 0, sVar][[1]];
        If[sDeg>1,
           If[ListQ[$ParamAssume],
             cfn = First /@ FactorList[Numerator[cf]];
             For [i=1,i<=Length[cfn],i++,
               cfni = modReduce[cfn[[i]]!=0,$p];
               If[!TrueQ[Reduce[Implies[And@@$ParamAssume, cfni]]],
                   AppendTo[$ParamAssume, cfni];
                   Print["ElimVars: Assuming ", StyleForm[cfni,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]]]],
             Print["ElimVars: Assuming ", StyleForm[cfn!=0,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]]]];
        exprList = $SNormal[Drop[exprList, {sInd}] /. sol],
      (*else*)
        Return[exprList]]]]

(****
  Solves the linear equations (if expression, assumes equal to zero) with respect to all
  variables matching the pattern (the equations are not necessary linear with respect to
  other parameters). Returns the list containing a single solution (as Solve).
  The function returns only the general solution (those that exists for general values
  of parameters) but prints a message every time then eliminating of a variable requires
  dividing by a non-constant. This gives the list of special cases that may be solved
  separately.
  With third parameter p, calculates all modulo p.
***)

SolVars[equs_, ptrn_] :=
  Module[{aOrd, sDeg, sNVar, sVar, sInd, ord, deg, nVar, var, rate, exprList, sol, sols = {}, cf, cfi, cfn},
    exprList = $SNormal[equs /. a_ == b_ :> a - b];
    If[! ListQ[exprList], exprList = {exprList}];
    If[MemberQ[exprList,False],Return[{}]];
    exprList = DeleteCases[exprList,True];
    While[exprList =!= {},
      exprList = DeleteCases[Collect[#, ptrn] & /@ exprList, 0];
      If[exprList === {}, Break[]];
      sInd = 0;
      sDeg = Infinity;
      sOrd = Infinity;
      Do[rate = RateElim[exprList[[i]], ptrn];
        If[ListQ[rate],
          {ord, deg, nVar, var, cfi} = rate;
          If[ord < sOrd || ord == sOrd && (deg < sDeg || deg == sDeg && nVar < sNVar), 
            {sOrd, sDeg, sNVar, sVar, cf} = rate; sInd = i]],
        {i, 1, Length[exprList]}];
      If[sInd > 0,
        sol = Solve[exprList[[sInd]] == 0, sVar][[1]];
        If[sDeg>1,
          cfn = Numerator[cf];
          If[ListQ[$ParamAssume],
             If[!TrueQ[Reduce[Implies[And@@$ParamAssume, cfn!=0]]],
                 AppendTo[$ParamAssume, cfn!=0];
                 Print["SolVars: Assuming ", StyleForm[cfn!=0,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]]],
             Print["SolVars: Assuming ", StyleForm[cfn!=0,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]]]];
        exprList = DeleteCases[$SNormal[Drop[exprList, {sInd}] /. sol], 0];
        sols = Join[sols /. sol, sol],
      (*else*)
        Message[ParamSolve::nsol, exprList];
        Break[]]];
    {sols /. (a_ -> b_) :> (a -> Collect[b, ptrn])}
    ]

ParamSolve::nsol = "Failed to solve (or find zero points of) ``"

SolVars[equs_, ptrn_, 0] := SolVars[equs, ptrn]

SolVars[equs_, ptrn_, p_] :=
  Module[{sOrd, sDeg, sNVar, sVar, sInd, ord, deg, nVar, var, rate, exprList, sol, sols = {}, cf, cfi, cfn, cfni, optRate, sAs},
    exprList = $SNormal[equs /. a_ == b_ :> a - b];
    If[! ListQ[exprList], exprList = {exprList}];
    If[MemberQ[exprList,False],Return[{}]];
    exprList = DeleteCases[exprList,True];
    DPrint[2, "SolVars[", exprList, ", ", ptrn, ", ", p];
    While[exprList =!= {},
      exprList = 
        DeleteCases[Collect[PolynomialMod[#, p], ptrn] & /@ exprList, 0];
      If[exprList === {}, Break[]];
      sInd = 0;
      optRate = {Infinity};
      Do[rate = RateElim[exprList[[i]], ptrn, optRate];
        DPrint[1, "rate(", exprList[[i]], ") = ", rate];
        If[ListQ[rate],
          optRate = rate;
          sInd = i],
        {i, 1, Length[exprList]}];
      If[sInd > 0,
        DPrint[3,"eq: ", exprList[[sInd]]];
        {sOrd, sDeg, sAs, sNVar, sVar, cf} = optRate; 
        sol =
          Solve[exprList[[sInd]] == 0, 
                sVar][[1]] /. (a_ -> b_) :> (a -> PolynomialMod[b, p]);
        If[sDeg>1,
          cfn = Numerator[cf];
          If[ListQ[$ParamAssume],
             cfn = First /@ FactorList[Numerator[cf]];
             For [i=1,i<=Length[cfn],i++,
               cfni = modReduce[cfn[[i]]!=0,$p];
               If[!TrueQ[Reduce[Implies[And@@$ParamAssume, cfni]]],
                 AppendTo[$ParamAssume, cfni];
                 Print["SolVars: Assuming ", StyleForm[cfni/.Mod[u_,_]:>u,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]/.
                         {sVar->StyleForm[sVar,FontColor->Red]}]]],
             Print["SolVars: Assuming ", StyleForm[cfn!=0,FontColor->Blue], " to solve 0 = ", exprList[[sInd]]]]];
        exprList = $SNormal[Drop[exprList, {sInd}] /. sol];
        sols = $SNormal[Join[sols /. sol, sol]];
        DPrint[3,"sol: ", sols],
      (*else*)
        Message[ParamSolve::nsol, exprList];
        Break[]]];
    {sols /. (a_ -> b_) :> (a -> Collect[PolynomialMod[b, p], ptrn])}
    ]

nAssum[deg_,cf_] :=
  If[ListQ[$ParamAssume],
    Count[
      First /@ FactorList[Numerator[cf]],
      _?(!TrueQ[Reduce[Implies[And @@ $ParamAssume, modReduce[# != 0, $p]]]] &)],
    0];

nAssum[0,cf_] = 0

SolVars::assume = "Assuming ``  to solve 0 = ``"

    
SolveSupportsPattern[_] = False;
SolveSupportsPattern[SolVars] ^= True;

GeneralSolve[equ_, v_, cf_, elim_:None] :=
  Module[{cflist, sol, vars, excl},
    cflist = MatchList[v, _cf];
    If[SolveSupportsPattern[$Solve],
      vars = _cf;
      excl = If [elim===None, {}, _elim],
    (*else*)
      vars = cflist;
      excl = If [elim===None, {}, MatchList[equ, _elim]]];
    sol = SVSolve[equ, vars, excl] [[1]];
    cflist = Complement[cflist, First /@ sol];
    v /. sol  /. SVNormalRule /. MapIndexed[(#1->cf[First[#2]])&, cflist]
  ]

GeneralReduce[v_, cf_] :=
  Module[{cflist, sol, cl1, cl2, repl, vars},
    cflist = MatchList[v, _cf];
    vars = If[SolveSupportsPattern[$Solve], _cf, cflist];
    sol = SVSolve[v==0, vars] [[1]];
    cl1 = First /@ sol;             (* significant coefs *)
    cl2 = Complement[cflist, cl1];  (* unsignificant coefs *)
    repl = Join[ MapIndexed[(#1->cf[First[#2]])&, cl1],
                 (#1->0)& /@ cl2];
    v /. repl
  ]

End[];
EndPackage[];

