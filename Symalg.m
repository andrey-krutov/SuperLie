(* --- Symalg.m ----- The Symmetric Algebra --- *)

BeginPackage["SuperLie`Symalg`", {"SuperLie`"}];

DegreeBasis::usage = "DegreeBasis[deg, vars] returns the list of elements
of degree deg in the symmetric algebra of variables vars.
DegreeBasis[deg, vars, lim] returns the list of monomial of degree deg with degrees
of variables do not exceed the corresponding limits.
DegreeBasis[deg, vars, op] and DegreeBasis[deg, vars, lim, op] use op instead of VTimes."

UpToDegreeBasis::usage = "UpToDegreeBasis[deg, vars] returns the list of elements
of degree <= deg in the symmetric algebra of variables vars.
UpToDegreeBasis[deg, vars, op] uses op instead of VTimes."

GradeBasis::usage = "GradeBasis[deg, vars] returns the list of elements
of grade deg in the symmetric algebra of variables vars. The grades of
variables must be predefined. GradeBasis[deg, vars, op] uses op instead of
VTimes. If deg is a list, PolyGrade is used instead of Grade."


FilterBasis::usage = "FilterBasis[deg, vars] returns the list of elements
of grade <= deg in the symmetric algebra of variables vars. The grades of
variables must be predefined. FilterBasis[deg, vars, op] uses op instead of
VTimes."


Begin["$`"]

Compositions[0, m_Integer] := {Table[0, {m}]}

Compositions[n_Integer, m_Integer] :=
  Flatten[
    Table[
      Prepend[#, i] & /@ Compositions[n-i, m-1],
      {i, n, 0, -1}],
    1]


grade2range[g_,d_]:=
  Which[g>0, {0,g*d}, g<0, {g*d,0}, True, {0,0}]

grades2range[g_,d_]:=Inner[grade2range, g, d, Plus]
grades2range[{}, {}] = {0, 0}

(* list all compositions of n as n=g1*n1+...+gk*nk with 0<=ni<=mi.
   Returns the set (as list) of all possible combinations of {n1,...nk}
   If the set is infinite, throws $Aborted.
   n and gi should be rational, mi should be nonegative integer or Infinity*)

GradedCompositions[n_, {}, {}] := If[n==0, {{}}, {}]

GradedCompositions[n_, m_List, g_List] :=
  Flatten[
    Which[g[[1]]==0,
      If[m[[1]]==Infinity,Throw[$Aborted]];
      Table[Prepend[#,i]& /@ GradedCompositions[n, Rest[m], Rest[g]],
        {i, m[[1]], 0, -1}],
    g[[1]]>0,
      With[{r=grades2range[Rest[g],Rest[m]]},
        If[m[[1]]==Infinity && r[[1]]==-Infinity,Throw[$Aborted]];
        Table[Prepend[#,i]& /@ GradedCompositions[n - i*g[[1]], Rest[m], Rest[g]],
          {i, Min[Floor[(n-r[[1]])/g[[1]]], m[[1]]],  Max[0,(n-r[[2]])/g[[1]]], -1}]],
    True, (* g[[1]]<0 *)
      With[{r=grades2range[Rest[g],Rest[m]]},
        If[m[[1]]==Infinity && r[[1]]==Infinity,Throw[$Aborted]];
        Table[Prepend[#,i]& /@ GradedCompositions[n - i*g[[1]], Rest[m], Rest[g]],
          {i, Min[Floor[(n-r[[2]])/g[[1]]], m[[1]]],  Max[0,(n-r[[1]])/g[[1]]], -1}]]],
    1]


polygrade2range[d_,g_List]:= Transpose[grade2range[#,d]& /@ g]

polygrades2range[d_,g_]:= Plus @@ MapThread[polygrade2range, {d, g}]
polygrades2range[{}, {}] = {0, 0}

comprange[n_, g_, {0, 0}] :=
  Module[{min=-Infinity,max=Infinity, gi, v},
    Do[ gi=g[[i]];
      If[gi!=0,
        v = n[[i]]/gi;
        If[v > min, min = Ceiling[v]];
        If[v < max, max = Floor[v]]],
      {i,Length[n]}];
    {min,max}]

comprange[n_, g_, {r1_, r2_}] :=
  Module[{min=-Infinity,max=Infinity, gi, v1, v2},
    Do[ gi=g[[i]];
      If[gi!=0,
        v1 = (n[[i]]-r2[[i]])/gi;
        v2 = (n[[i]]-r1[[i]])/gi;
        If[gi<0, {v1,v2}={v2,v1}];
        If[v1 > min, min = Ceiling[v1]];
        If[v2 < max, max = Floor[v2]]],
      {i,Length[n]}];
    {min,max}]

PolyGradedCompositions[deg_, {}, {}] :=
  If[0==Sequence@@deg, {{}}, {}]

PolyGradedCompositions[n_, m_List, g_List] :=
  With[{r=comprange[n, g[[1]], polygrades2range[Rest[m],Rest[g]]]},
    If[m[[1]]==r[[2]]==Infinity, Throw[$Aborted]];
    Flatten[
      Table[Prepend[#,i]& /@ PolyGradedCompositions[n - i*g[[1]], Rest[m], Rest[g]],
          {i, Min[r[[2]],m[[1]]],  Max[r[[1]],0], -1}],
      1]]



DegreeBasis[deg_/;deg<0, vars_, op_:VTimes, sym_:1] := {}

DegreeBasis[0, vars_, op_:VTimes, sym_:1] := {op[]}

DegreeBasis[deg_, {}, op_:VTimes, sym_:1] := {};

DegreeBasis[deg_, vars_, op_:VTimes, sym_:1] :=
  DegreeBasis[deg, vars, If[P[#]===sym,1,Infinity]& /@ vars, op]

DegreeBasis[deg_, vars_, lim_List, op_:VTimes] :=
  With[{exp=LimCompositions[deg,lim], pow=PowerOp[op]},
    If[pow===None,
      Inner[Sequence@@Table[#1,{#2}]&,vars,#,op]& /@ exp,
      Inner[If[#2==0,Unevaluated[],pow[#1,#2]]&, vars, #, op]& /@ exp]];

UpToDegreeBasis[deg_, args__] :=
 Flatten[Table[DegreeBasis[i,args],{i,0,deg}]]
 
(* Optimisation for Wedge *)

DegreeBasis[0, vars_, Wedge, sym_:1] := {wedge[]}
DegreeBasis[0, vars_, lim_List, Wedge] := {wedge[]}

DegreeBasis[deg_, vars_, lim_List, Wedge] :=
  DegreeBasis[deg, vars, lim, wedge]


(* ====================== *)
(*
GradeBasis[deg_/;deg<0, vars_, op_:VTimes, sym_:1] :={}

GradeBasis[0, vars_, op_:VTimes] :=
  With[{zg=Select[vars,Grade[#]==0&]},
    If[zg=={},
      {op[]},
      Flatten[Outer[op, Sequence @@ ({op[], #}&) /@ zg]]]]  /. SVTimes[_,x_]:>x
*)

GradeBasis[deg_, {}, op_:VTimes, sym_:1] := {};

GradeBasis[deg_Integer, vars_, lim_List, op_:VTimes] :=
  Catch[
    With[{g=Grade/@vars, pow = PowerOp[op]},
      With[{exp = GradedCompositions[deg, lim, g]},
        If[pow === None,
          Inner[Sequence @@ Table[#1, {#2}] &, vars, #, op] & /@ exp,
          Inner[pow, vars, #, op] & /@ exp]]],
    $Aborted,
      (Message[GradeBasis::infty,deg,vars,lim,op];$Aborted)&
    ]

GradeBasis[deg_List, vars_, lim_List, op_:VTimes] :=
  Catch[
    With[{g=PolyGrade/@vars, pow = PowerOp[op]},
      With[{exp = PolyGradedCompositions[deg, lim, g]},
        If[pow === None,
          Inner[Sequence @@ Table[#1, {#2}] &, vars, #, op] & /@ exp,
          Inner[pow, vars, #, op] & /@ exp]]],
    $Aborted,
      (Message[GradeBasis::infty,deg,vars,lim,op];$Aborted)&
    ]

GradeBasis::infty = "GradeBasis[``,``,``,``] failed to return an infinite set"

GradeBasis[deg_, vars_, op_:VTimes, sym_:1] :=
  GradeBasis[deg, vars, If[P[#]===sym,1,Infinity]& /@ vars, op]


(*
GradeBasis[deg_, vars_, op_:VTimes] :=
 Flatten[Table[
    With[{j = i - If[P[vars[[i]]]===1, 0, 1]},
	op[vars[[i]], GradeBasis[deg-Grade[vars[[i]]], Drop[vars,j], op]]],
    {i,1,Length[vars]}]]  /. SVTimes[_,x_]:>x
*)

GradeBasis[store_Symbol, vars_, op_:VTimes] :=
  (Clear[store];
   store[deg_] := store[deg,0];
   store[deg_/;deg<0, drop_] := {};
   store[0, drop_] := store[0, drop] =
     With[{zg=Select[Drop[vars,drop],Grade[#]==0&]},
       If[zg=={},
         {op[]},
         Flatten[Outer[op, Sequence @@ ({op[], #}&) /@ zg]] /. SVTimes[_,x_]:>x]];
   store[deg_, drop_] := store[deg, drop] =
     Flatten[Table[
       With[{j = i - If[P[vars[[i]]]===1, 0, 1]},
	       op[vars[[i]], store[deg-Grade[vars[[i]]], j]] /. SVTimes[_,x_]:>x],
       {i,drop+1,Length[vars]}]])
  
   

FilterBasis[deg_Integer, args__] :=
 If[deg>=0,
   Flatten[Table[GradeBasis[i,args],{i,0,deg}]],
   Flatten[Table[GradeBasis[i,args],{i,0,deg,-1}]]]

FilterBasis[{d1_,d2_,step_:Null}, args__] :=
  With[{s=Which[NumberQ[step],step, d1<=d2,1, True,-1]},
    Flatten[Table[GradeBasis[i,args],{i,d1,d2,s}]]]

(*
GradeBasis[deg_List, {}, op_:VTimes] := 
  If[Select[deg, #!=0&,1]==={},{op[]},{}];

GradeBasis[deg_List, vars_, op_:VTimes] :=
 Which[
   Select[deg, #!=0&,1]==={},
		{op[]},
   vars==={}, {},
   Select[deg, #<0&,1]==={},
     Flatten[Table[
       With[{j = i - If[P[vars[[i]]]===1, 0, 1]},
	op[vars[[i]], GradeBasis[deg-PolyGrade[vars[[i]]], Drop[vars,j], op]] /. SVTimes[_,x_]:>x],
        {i,1,Length[vars]}]],
   True, {}]
*)

(* Optimisation for Wedge *)
(*
GradeBasis[0, vars_, Wedge, sym_:1] :=  GradeBasis[0, vars, wedge, sym]
GradeBasis[0, vars_, lim_List, Wedge] :=  GradeBasis[0, vars, lim, wedge]
*)

GradeBasis[deg_, vars_, Wedge, sym_:1] :=  GradeBasis[deg, vars, wedge, sym]
GradeBasis[deg_, vars_, lim_List, Wedge] :=  GradeBasis[deg, vars, lim, wedge]

End[]
EndPackage[]

