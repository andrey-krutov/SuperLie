(* ::Package:: *)

BeginPackage["SuperLie`Genvect`", {"SuperLie`", "SuperLie`Domain`","SuperLie`Vsplit`"}]

(* ----------------------------------------------------- *)

GeneralSum::usage =
 "GeneralSum[cf, {v1,...}] returns the general linear combination cf[1]*v1 + ...
and declares cf[_] scalars. GeneralSum[cf, {v1,...}, f] returns the general
linear combination v = cf[1]*v1 + ... such that f[v]=0."

GeneralZero::usage =
"GeneralZero[g, v, cf] returns the general solution of Act[g, v]==0 with
coefficients cf[1], ... . The g in an element or a list of elements of 
an algebra; v is either list of vectors or general sum with coefficients
cf[1] ..."

GeneralSolve::usage =
"GeneralSolve[equ, v, cf] solves the equation equ with respect to cf[1], ... ,
substitutes the coefficients cf[1], ... in the general sum v with the found 
solution, renumber the coefficients cf and returns the result.
GeneralSolve[equ, v, cf, elim] solves the equation excludes eliminating scalar
coefficients elim[1], ... ." 

GeneralImage::usage =
"GeneralImage[f, v, cf] calculates the image f[V] of a space V under the action
of operator f:V->W. The space V is given either as general sum cf[1]*v[1]+... or as basis
{v[1],...}. The result is representad as general sum cf[1]*w1+... If f is a list
of operators, GeneralImage returns the sum of their images."

GeneralInverseImage::usage =
"GeneralInverseImage[f, v, cv, w, cw] calculates the preimage (or inverse image)
\(f\^-1\)[W] of a space W under the action of operator f:V->W. The spaces are given
either as general sum cv[1]*v[1]+... or as basis {v[1],...}. The result is
representad as general sum cv[1]*e1+... where e1, e2, ... are linear combinations
of v[i]. If f is a list of operators, GeneralInverseImage returns the intersection of
their inverse images."

GeneralKernel::usage =
"GeneralKernel[f, v, cf] calculates the kernel \(f\^-1\)[0] of the operator f:V->W.
The spaces V is given either as general sum cf[1]*v[1]+... or as basis {v[1],...}.
The result is representad as general sum cf[1]*e1+... where e1, e2, ... are linear
combinations of v[i]. If f is a list of operators, GeneralKernel returns the intersection of
their kernels."


GeneralReduce::usage =
"GeneralReduce[v, cf] eliminates insignificant coefficients in the general sum,
renumbers the remaining coefficients and returns the result."

GeneralPreImage::usage =
"GeneralPreImage[g, x,cx, y,cy] calculates the intersection of x with the
preimage of y under ad[g]."

GeneralAct::usage =
"GeneralAct[g, x, cf] calculates the image of x under ad[g]."

GeneralBasis::usage =
"GeneralBasis[v,cf] returns the basis of the space defined by the general
vector v with coefficients cf[...]"

GeneralPlus::usage =
"GeneralPlus[v1, ..., vn, cf] returnns the sum of general sums v1, ..., vn i.e., the general sum
representing the sum of the spaces represented by v1, ..., vn"
 
GeneralIntersection::usage =
"GeneralIntersection[v1, ..., vn, cf] returnns the intersection of general sums v1, ..., vn i.e., the general sum
representing the intersection of the spaces represented by v1, ..., vn"

GeneralDim::usage =
"GeneralDim[v, cf] returns the number of the indeterminate coefficients in expression v"

Begin["$`"]

(********** Aux functions *********)
ToGeneralSum[e_List, cf_] := GeneralSum[cf,e];
ToGeneralSum[e_, _] := e;
ToGeneralSum[e:List[___Rule], cf_] := ApplySplit[ToGeneralSum, e, cf];

(******************** GeneralSum **********************)
(*  GeneralSum[c, head[x1,..xn]] returns sum c[1]*x1+..+c[n]*xn with scalar coefficients c[i]
 *  GeneralSum[c, head[x1,..xn], f] returss a general solution of f[c[1]*x1+..+c[n]*xn]=0.
 *)

GeneralSum[coef_, expr_] := 
 ( SetProperties[coef, {Scalar,Standard->Subscripted,Traditional->Subscripted,TeX->Subscripted}];
   VPlus @@ MapIndexed[(coef[First[#2]]~SVTimes~#1)&, expr]
 )
GeneralSum[coef_, expr:List[___Rule]] := ApplySplit[GeneralSum[coef, #]&, expr]
GeneralSum[coef_, expr_, f_] := GeneralKernel[f, GeneralSum[coef,expr], coef];


(******************** GeneralKernel *********************)
(*   Find the general solution of f[V]=0 where
 * f is an linear function on a space or a list of such functions;
 * v defines the basis of V either as a list of vector or as a
 *   general sum with coefficients cf[i]
 * cf[1], .. are used in the answer as undeterminate coefficients
 *)

GeneralKernel[f_List, v_, cf_] := Fold[GeneralKernel[#2, #1, cf]&, ToGeneralSum[v,cf], f]
GeneralKernel[f_, v:List[___Rule], cf_] := DeleteCases[ApplySplit[GeneralKernel[f, #, cf]&, v], _->0]
GeneralKernel[f_, v_, cf_] := GeneralSolve[f[v]==0, v, cf]

(******************** GeneralImage *********************)
(*   Returns the space f[V] as a general sum where
 * f is an linear function on a space or a list of such functions;
 * v defines the basis of V either as a list of vector or as a
 *   general sum with coefficients cf[i]
 * cf[1], .. are used in the answer as undeterminate coefficients
 *)

GeneralImage[f_List, v_, cf_] := With[{s=ToGeneralSum[v,cf]}, GeneralReduce[VSum[f[[i]][s/.cf[j_]:>cf[i,j]],{i,Length[f]}],cf]]
GeneralImage[f_, v_, cf_] := GeneralReduce[f[ToGeneralSum[v,cf]], cf]

(******************** GeneralInverseImage ***************)
(*  Given to spaces X and Y represented as general sum and
 * a linear function f:X->Y or a list of such functions,
 * returns the max set S in X such that f(S) in Y [for all f in list]
 * The result is represented as a general sum with coefficients cx[i]
 *)

GeneralInverseImage[f_List, x_, cx_, y_, cy_] :=
  With[{s=ToGeneralSum[y,cy]},  Fold[GeneralInverseImage[#2, #1, cx, s, cy]&, ToGeneralSum[x,cx], f]]
GeneralInverseImage[f_, x_, cx_, y_, cy_] :=
  With[{s=ToGeneralSum[x,cx]}, GeneralSolve[f[s]==ToGeneralSum[y,cy], s, cx, cy]]


(******************** GeneralZero *********************)
(*   Find the general solution of Act[g, V]=0 where
 * g is an element or a list of elements of an algebra;
 * v defines the basis of V either as a list of vector or as a
 *   general sum with coefficients cf[i]
 * cf[1], .. are used in the answer as undeterminate coefficients
 *)

GeneralZero[g_List, v_, cf_, op___] := Fold[GeneralZero[#2, #1, cf, op]&, ToGeneralSum[v,cf], g]
GeneralZero[g_, v:List[___Rule], cf_, op___] := DeleteCases[ApplySplit[GeneralZero[g, #, cf, op]&, v], _->0]   
GeneralZero[g_, v_, cf_, op_:Act] :=
  With[{w=ToGeneralSum[v,cf]}, GeneralSolve[op[g,w]==0, w, cf]]


(******************** GeneralAct *********************)
(*   Returns the space [g,V] as a general sum where
 * g is an element of an algebra or a list of such elements;
 * v defines the basis of V either as a list of vector or as a
 *   general sum with coefficients cf[i]
 * cf[1], .. are used in the answer as undeterminate coefficients
 *)

GeneralAct[f_List, v_, cf_, op_:Act] :=
  With[{s=ToGeneralSum[v,cf]}, GeneralReduce[VSum[op[g[[i]],s/.cf[j_]:>cf[i,j]],{i,Length[f]}],cf]]
GeneralAct[g_, v_, cf_, op_:Act] := GeneralReduce[op[g,ToGeneralSum[v,cf]], cf]


(******************** GeneralSolve *********************)
(*   Solve the equation equ with respect to cf[1], ... .
 * Substitute the coefficients cf[1], ... in the general sum v with
 * the found solution. Renumber the coefficients cf. 
 *)

GeneralSolve[equ_, v_, cf_, elim_:None] := 
  Module[{cflist, sol, excl},
    cflist = MatchList[v, _cf];
    excl = If [elim===None, {}, MatchList[equ, _elim]];
    sol = SVSolve[equ, cflist, excl];
    If[sol==={},
      Message[GeneralSolve::nosol, equ]; $Failed,
    (*else*)
      sol = sol[[1]];
      cflist = Complement[cflist, First /@ sol];
      ToGeneralSum[v,cf] /. sol  /. SVNormalRule /. MapIndexed[(#1->cf[First[#2]])&, cflist]]
  ]
GeneralSolve[equ_, v:List[___Rule], cf_, elim_:None] := DeleteCases[ApplySplit[GeneralSolve[equ, #, cf, elim]&, v], _->0]   
GeneralSolve::nosol = "Equation `` has no solutions";
    
(******************** GeneralReduce *********************)
(*   Eliminate insignificant coefficients in the general sum.
 * Renumber the remaining coefficients. 
 *   E.g., (c[2]-c[4])*v  --> c[1]*v.
 *)

GeneralReduce[v_, cf_] := 
  Module[{cflist, sol, cl1, cl2, repl, w},
    w = ToGeneralSum[v,cf];
    cflist = MatchList[w, _cf];
    sol = SVSolve[v==0, cflist] [[1]];
    cl1 = First /@ sol;             (* significant coefs *)
    cl2 = Complement[cflist, cl1];  (* unsignificant coefs *)
    repl = Join[ MapIndexed[(#1->cf[First[#2]])&, cl1],
                 (#1->0)& /@ cl2];
    w /. repl
  ]
GeneralReduce[v:List[___Rule], cf_] := DeleteCases[ApplySplit[GeneralReduce, v, cf], _->0]

(******************** GeneralPreImage *********************)
(*   Given general vectors x in X and y in Y and a function f: X -> Y,
 * calculate the projection of x to the preimage of y under f.
 *)

GeneralPreImage[g_List, v_, more__] := Fold[GeneralPreImage[#2,#1,more]&, v, g]
GeneralPreImage[g_, v_, cf_, y_, cy_, op_:Act] :=
	GeneralInverseImage[op[g,#]&, v, cf, y, cy]

(******************** GeneralBasis *********************)

GeneralBasis[v_, cf_] :=  (v /. #->1 /. _cf->0)& /@ MatchList[v,_cf]
GeneralBasis[v:List[___Rule], cf_] := DeleteCases[ApplySplit[GeneralBasis, v, cf], _->{}]


(******************** GeneralDim *********************)

GeneralDim[v_, cf_] := Length[MatchList[v,_cf]]
GeneralDim[v:List[___Rule], cf_] := DeleteCases[ApplySplit[GeneralDim, v, cf], _->0]


(******************** GeneralPlus *********************)

GeneralPlus[v__, cf_] :=
  With[{w=ToGeneralSum[#,cf]&/@{v}},
    GeneralReduce[VSum[w[[i]]/.cf[j_]:>cf[i,j],{i,Length[w]}],cf]]
GeneralPlus[v:List[___Rule].., cf_] :=
  With[{w=ToGeneralSum[#,cf]&/@{v}},
    GeneralReduce[AddSplit @@ Table[w[[i]]/.cf[j_]:>cf[i,j],{i,Length[w]}],cf]]


(******************** GeneralIntersection ***************)

GeneralIntersection[0, __] = 0;
GeneralIntersection[{}, __] = {};
GeneralIntersection[x_, y_, cf_] :=
  Module[{s=ToGeneralSum[x,cf], cy}, GeneralSolve[s==ToGeneralSum[y/.cf->cy,cy], s, cf, cy]]
GeneralIntersection[x_, y_, z__, cf_] := GeneralIntersection[GeneralIntersection[x, y, cf], z, cf]



End[]
EndPackage[]

