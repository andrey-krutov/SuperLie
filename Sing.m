BeginPackage["SuperLie`Sing`", {"SuperLie`", "SuperLie`Domain`",
    "SuperLie`Enum`", "SuperLie`Space`", "SuperLie`Submod`", 
    "SuperLie`Envsort`", "SuperLie`Genvect`", "SuperLie`Generate`", 
    "SuperLie`Vsplit`", "SuperLie`Subalg`", "SuperLie`Symalg`", 
    "SuperLie`Irrmod`"}]
(*
This package defines functions for calculation of singular vectors.
*)

SuperLie`Sing`svSetAlg::usage =
"svSetAlg[g,{neg, zero, pos}] declares the algebra
and subalgebras to be used  in calculations."

SuperLie`Sing`svSetAlg2::usage =
"svSetAlg2[g,{neg, zero, pos}] declares the algebra
and subalgebras to be used  in calculations (the subalgebras are already calculated)."

SuperLie`Sing`svScalars::usage =
"svScalars[c,...] declares the indefinite scalar parameters to be used in
calculations. The first parameter will be used as indefinite coefficient
in vectors." 

SuperLie`Sing`svCheckRL::usage =
"svCheckRL[r, l, [,d]] checks that the proposed lists of raising and
lowering elements agrees with the weight defined in the algebra." 

SuperLie`Sing`svCart::usage= 
"svCart[x, h, y] builds the Cartan decomposition of \!\(g\_0\)" 

SuperLie`Sing`svVerma::usage= 
"svVerma[m, \[Lambda], grade] builds the Verma module over \!\(g\_0\)
with highest weight \[Lambda] and the basis of \!\(U(\(g\_0\^+\))\);
all computations up to the given grade."
 
SuperLie`Sing`svDefEq::usage=
"svDefEq[deg] builds the equation system for singular vectors of given
degree in Ind(V), with undefinite \!\(g\_0\)-module V."

SuperLie`Sing`svEq::usage=
"svEq[\[Eta]] builds the equation system for singular vectors in
\!\(Ind(M\_\[Lambda])\) of the degree defined by svDefEq and
weight \[Lambda]-\[Eta]."
 
SuperLie`Sing`svAct::usage=
"svAct[u,m] returns the action of \!\(u \[Element] U(\(a\_+\))\) on
\!\(m \[Element] Ind(M\_\[Lambda])\)." 

SuperLie`Sing`svSp::usage=
"svSp[u, m] returns the scalar product of  \!\(u\[Element]U(\(a\_+\))\)
and \!\(m \[Element] Ind(M\_\[Lambda])\). Defined if w(u) + w(m) = \[Lambda]."
 
SuperLie`Sing`svRep::usage =
"svRep[expr] apply the current substitutions to expression expr and tries
to simplify the result."

SuperLie`Sing`svH::usage =
"svH converts the highness conditions using current substitutions, stores
and prints the resulting equations"

SuperLie`Sing`svZ::usage =
"svZ[] converts the equations of singularity using current substitutions, 
stores and prints the resulting equations. svZ[i] do the same only for
i-th singularity condition."

SuperLie`Sing`svSub::usage =
"svSub[sol,...] adds the solutions to the substitution list. The sol may
be (a) a rule \[Lambda][_]->._; (b) a rule c[__]->_; (c) an integer, to
add the solution with this number (see svSolve); (d) en expression sv$e, to
add the  solution of sv$e==0."

SuperLie`Sing`svUnSub::usage = "sbUnSub undoes the last svSub or svExcl in the current branch"

SuperLie`Sing`svExcl::usage =
"svExcl[expr] adds the expression to the list of non-zero expressions.
Such expressions will be canceled in equations."

SuperLie`Sing`svBranch::usage =
"svBranch[level] starts new logical branch of solving equations. If level
is <= the current level, the solution list and exclusion list are restored
as they were when the level was created."

SuperLie`Sing`svHiCf::usage =
"svHiCf returns the coefficient(s) at \!\(m\_\[Lambda]\) of the vector in
question, applying solution list"
 
SuperLie`Sing`svSolve::usage =
"svSolve examines the list of stored equations, tries to solve each of them
and print the solutions together with conditions on \[Lambda] when the
equations are valid. Use svSub[i] to add the solution of i-th equation
to the substitution list."

SuperLie`Sing`svResult::usage =
"svResult returns the solution(s) of the current replacement list, as
element(s) of \!\(U(\(g\_-\))\[CircleTimes]M\_\[Lambda]\)"
 
SuperLie`Sing`svImg::usage =
"svImg[f] substitutes elements of \!\(g\_-\), \!\(g\_0\), and \!\(g\_+\)
in expression f with their images in the main algebra g"

SuperLie`Sing`sv$Out::usage =
"expr/.sv$Out converts an expression containing elements of main algebra g
and Verma module m to the user-defined form. The default sv$Out is empty"

SuperLie`Sing`svLess::usage = sv$Less::usage =
"The value of sv$Less is the ordering function used for sorting the terms in
the enveloping algebra. The default function is svLess"

SuperLie`Sing`sv$Print::usage = "Controls the amount of information printed by SuperLie`Sing`"

(* Variables *)

SuperLie`Sing`sv$g;
SuperLie`Sing`sv$n;
SuperLie`Sing`sv$a;
SuperLie`Sing`sv$p;
SuperLie`Sing`sv$y;
SuperLie`Sing`sv$h;
SuperLie`Sing`sv$x;
SuperLie`Sing`sv$r;
SuperLie`Sing`sv$l;
SuperLie`Sing`sv$d;
SuperLie`Sing`sv$m;
SuperLie`Sing`sv$\[Lambda];
SuperLie`Sing`sv$z;
SuperLie`Sing`sv$v;
SuperLie`Sing`sv$c;
SuperLie`Sing`sv$hi;
SuperLie`Sing`sv$eqHi;
SuperLie`Sing`sv$eqZ;
SuperLie`Sing`sv$e;

SuperLie`Sing`sv$solTime = 20 (*sec*)
SuperLie`Sing`sv$Print = 0

(* ======  Private ======== *)
Begin["sv`"]

(* Sort rule for enveloping algebra *)

WeightLess[x_, y_] := With[{ord = LexOrd[Weight[x], Weight[y]]},
    Which[ord > 0, True, ord < 0, False, True, OrderedQ[{x, y}]]]

LexOrd[x_, y_] := 
  Which[x=={}, 0, 
    x[[1]] <  y[[1]], 1, 
    x[[1]] >  y[[1]], -1,
    True, LexOrd[Rest[x], Rest[y]]]

svLess[x_, y_] := 
  With[{dg = Grade[x] - Grade[y]}, 
      Which[dg < 0, True, dg > 0, False, True, WeightLess[x, y]]]

sv$Less = svLess


(* Main algebra *)
(*
The main algebra is divided according to the grade in positive, zero, and
negative parts.
The "zero" part is decomposed in Cartan triade. The weight defined on the
main algebra should agree with the basis of the Cartan decomposition.
The "positive" part may be represented by generators only (as ideal over
"raising" part of "zero").
*)

svSetAlg[g_,opts___Rule] := svSetAlg[g,{Null,Null,Null},opts];

svSetAlgPar[b_List] :={Null,b}
svSetAlgPar[n_->b_] :={n,b}
svSetAlgPar[n_] :={n,Null}

svSetAlg[g_, {neg_:Null, zero_:Null, pos_:Null}, opts___Rule] :=
  Module[{negBas = {}, iBas, i, NGrade},
    For[i = -1; Length[iBas = Basis[g, i]] > 0, i--, 
      negBas = {negBas, iBas}];
    negBas = Flatten[iBas];
    Clear[sv$n, sv$a, sv$p];
    {name,bas} = svSetAlgPar[neg];
    If[name=!=Null, sv$n = name];
    If[bas=!=Null,
      SubAlgebra[sv$n, g, bas],
    (*else*)
      DefSubAlgebra[sv$n, g, negBas, Weight]];
    {name,bas} = svSetAlgPar[zero];
    If[name=!=Null, sv$a = name];
    If[bas=!=Null,
      SubAlgebra[sv$a, g, bas],
    (*else*)
      DefSubAlgebra[sv$a, g, Basis[g, 0], Weight]];
    {name,bas} = svSetAlgPar[pos];
    If[name=!=Null, sv$p = name];
    If[bas=!=Null,
      SubAlgebra[sv$p, g, bas, ToGrade -> 1];
      sv$z = Basis[sv$p],
    (*else*)
      SubAlgebra[sv$p, g, Basis[g, 1], ToGrade -> 1];
      sv$z = {} (*calculate later*)];
    AlgebraDecomposition[sv$F, g, {sv$p, sv$a, sv$n}];
    svImgRule = (x : (sv$a | sv$p | sv$n))[i_] :> Image[x][[i]];
    $SNormal = Factor[#, Modulus->$p]&;
    VNormal[a_ == b_] := (VNormal[a - b] == 0);
    NGrade[sv$n[i_]] := -GList[sv$n][[i]];
    Weight[VTimes[]] ^= Table[0,{Length[Weight[negBas[[1]]]]}];
    negBas = Sort[Basis[sv$n], sv$Less];
    envBas[d_] := Block[{Grade = NGrade}, GradeBasis[-d, negBas]];
    svVTFactors[f : (_sv$a | _sv$p | _sv$n)] := {f};
    Induct[f_sv$n, v_] ^:= f ** v;
    Induct[f_sv$a, v_] ^:= Act[f, v];
    Induct[f_sv$p, _] ^:= 0;
    sv$g = g
    ]

svSetAlg2[g_, {neg_, zero_, pos_}] :=
 Module[{negBas, NGrade},
    sv$n = neg;
    sv$a = zero;
    sv$p = pos;
    sv$z = {}; (*calculate later*)
    AlgebraDecomposition[sv$F, g, {sv$p, sv$a, sv$n}];
    svImgRule = (x : (sv$a | sv$p | sv$n))[i_] :> Image[x][[i]];
    $SNormal = Factor[#, Modulus->$p]&;
    VNormal[a_ == b_] := (VNormal[a - b] == 0);
    NGrade[sv$n[i_]] := -GList[sv$n][[i]];
    Weight[VTimes[]] ^= Table[0,{Length[Weight[neg[1]]]}];
    negBas = Sort[Basis[sv$n], sv$Less];
    envBas[d_] := Block[{Grade = NGrade}, GradeBasis[-d, negBas]];
    svVTFactors[f : (_sv$a | _sv$p | _sv$n)] := {f};
    Induct[f_sv$n, v_] ^:= f ** v;
    Induct[f_sv$a, v_] ^:= Act[f, v];
    Induct[f_sv$p, _] ^:= 0;
    sv$g = g
    ]

sv$Out={}

svScalars[c__] := (SetProperties[{c},{Scalar,Standard->Subscripted,Traditional->Subscripted}]; sv$c = {c}[[1]]);

svImg[e_]:= e/.svImgRule/.sv$Out;

(*
This function checks if the proposed lists of raising and lowering elements
agrees with the weight defined in the algebra.
*)

svCheckRL[r_, l_, d_:Auto] :=
  Module[{n, h, diag},
    n = Min[Length[r], Length[l]];
    Do[If[Weight[r[[i]]] =!= -Weight[l[[i]]],
        Print["Non-opposite weights at position ", i];
        n = i - 1], {i, n, 1, -1}];
    h = Inner[Bracket[sv$a], Take[r, n], Take[l, n], List];
    diag = If[d === Auto, h, d, h];
    Print[
      Table[(VNormal[Act[#, r[[i]]]] & /@ diag) -> Weight[r[[i]]], {i, 
            Length[r]}] // ColumnForm]; 
    Print[Table[(VNormal[Act[#, l[[i]]]] & /@ diag) -> Weight[l[[i]]], {i, 
            Length[l]}] // ColumnForm];
    h]

(*
Cartan decomposition, Verma module(require different grading) and U(ap)
*)
(*
svCart[raise_, diag_, lower_] :=
  Module[{b, ls = GList[sv$a], d = Length[Weight[raise[[1]]]]},
    svGList = GList[sv$a];
    AlgebraDecomposition[CartanTriade, 
      sv$a, {sv$x -> raise, sv$h -> diag, sv$y -> lower}];
    Do[
       b = Image[sv$x][[i]]//.{x_VPlus:>x[[1]],x_SVTimes:>x[[2]]};
	DPrint[2,"i=",i, ", img=",b,", el=", GenBasis[sv$x][[i]],", deg=",Deg[GenBasis[sv$x][[i]] //. act -> VTimes, _sv$x]];
       ls[[b[[1]]]] = Deg[GenBasis[sv$x][[i]] //. act -> VTimes, _sv$x],
      {i, 1, Dim[sv$x]}];
    Do[
      b = Image[sv$y][[i]]//.{x_VPlus:>x[[1]],x_SVTimes:>x[[2]]};
      ls[[b[[1]]]] = -Deg[GenBasis[sv$y][[i]] //. act -> VTimes, _sv$y],
      {i, 1, Dim[sv$y]}];
    altGList = ls;
    GList[sv$a] ^:= svGList;
    Block[{svGList = altGList},
      AlgebraDecomposition[CartanTriade, 
        sv$a, {sv$x -> raise, sv$h -> diag, sv$y -> lower}]];
    svArep = DecompositionRule[sv$a, CartanTriade];
    sv$r = raise;
    sv$l = lower;
    sv$d = diag;
    ]
*)
svCart[raise_, diag_, lower_, grade_:{1,0,-1}] :=
  Module[{b, ls = GList[sv$a], d = Length[Weight[raise[[1]]]], c, lw, sol},
    svGList = GList[sv$a];
    AlgebraDecomposition[CartanTriade, 
      sv$a, {sv$x -> raise, sv$h -> diag, sv$y -> lower},GList->grade];
    svArep = DecompositionRule[sv$a, CartanTriade];
    altGList = Grade /@ (Basis[sv$a] /. sv`svArep);
    sv$r = raise;
    sv$l = lower;
    sv$d = diag;
    lw = Length[Weight[sv$y[1]]];
    sol = $Solve[Table[Array[c,lw].Weight[sv$y[i]]==Grade[sv$y[i]],{i,Dim[sv$y]}]];
    w2r = If [sol=!={}, Array[c,lw]/.sol[[1]]]/._c->0;
    ]

svVerma[m_, wt_, grade_:Auto] :=
  Module[{w, glist = GList[sv$a]},
    Do[w = wt[[i]]; If[SymbolQ[w], Scalar[w]], {i, Length[wt]}];
    Block[{svGList = altGList},
      HWModule[m, sv$a, wt, Grade -> grade, Quotient -> False,
         Order->Sort[Basis[sv$y], sv$Less]]];
    sv$\[Lambda] = wt;
    sv$m = m;
    (*NGrade[x_m] := -Grade[x];
      mBasSpl = 
        Block[{Grade = NGrade}, 
          SplitList[FilterBasis[grade, Basis[m]], _, 
            Simplify[wt - Weight[#]] &]];*)
    Clear[uxBasSpl,mBasSpl];
    mBasSpl[d_] := mBasSpl[d] = SplitList[Basis[m,d], _, Simplify[wt - Weight[#]] &];
    uxBasSpl[d_] := uxBasSpl[d] = SplitList[GradeBasis[d, Basis[sv$x]], _, Weight];
    uxComp[z_m] := uxComp[-Grade[z],Weight[z] - sv$\[Lambda]];
    eqMon[z_m] :=
      Factor[svSp[#, z] & /@ uxComp[-Grade[z],Simplify[Weight[z] - Weight[m[1]]]] //. lrep,
        Modulus->$p];
    m::usage]

mComp[d_, w_] := PartSplit[mBasSpl[d], w, {}]
mComp[Auto, w_] :=
  If[ListQ[w2r], mComp[w.w2r,w],
  (*else*) Message[svEq::grade];$Failed]

uxComp[d_,w_List] := PartSplit[uxBasSpl[d], -w, {}]


(*
Searching generators of g\_+
*)

(*sv$z = GeneralBasis[GeneralZero[sv$r, Basis[sv$p, 1], c], c]*)

(* Inductive module *)

svVTFactors[VPower[g_, n_]] := Flatten[Table[svVTFactors[g], {n}]];
svVTFactors[g_VTimes] := Flatten[svVTFactors /@ (List @@ g)];

Induct[g : (_VTimes | _VPower), m_] := Induct[svVTFactors[g], m];
Induct[g_List, m_] := 
  With[{last = g[[-1]]}, 
    If[Grade[last] < 0, (VTimes @@ g) ** m, (VTimes @@ Drop[g, -1]) ** 
        Induct[last, m]]]

SetProperties[Induct, {Vector, Vector -> _, Linear}]

Act[g_, q_ ** m_] := Induct[EnvNormal[VTimes[g,q],sv$Less], m] //. LinearRule[Tp]

svImg[a_ ** b_] := svImg[a] ** b

(* U(x) *)
(*
Action on U(x) on Verma module M with result proportional to the highest \
vector of M
(uxComp returns the list of components of U(x) with appropriate weight)
*)

svSp[x_, y_] := 
  Factor[VNormal[svAct[x, y]] /. sv$m[1] -> 1 /. lrep /.
        SVTimes -> Times /. VPlus -> Plus, Modulus->$p]
svAct[z_sv$x, v_] := Act[z, v]
svAct[z_VTimes, v_] := Fold[svAct[#2, #1] &, v, Reverse[List@@z]]
svAct[VPower[f_, n_], v_] := svAct[VPower[f, n - 1], svAct[f, v]]
SetProperties[svAct, {Vector, Vector -> _, Linear}]


(* Solving tools *)
(*
Build the system of equations for condition [raise, Sum P[i](n)**v[i]]=0
*)

svRaise[f_] := 
  Flatten[Table[
      uCoords[(Act[sv$r[[i]], f] //. 
                  LinearRule[Tp, First] // VNormal // VSort) //. 
          LinearCollectRule[Tp, Last]], {i, 1, Length[sv$r]}]]

uCoords[a_ ** b_] := b
uCoords[a_VPlus] := uCoords /@ (List @@ a) /; checkTpStd[a]
uCoords[SVTimes[a_, b_]] := uCoords[b]

checkTpStd[a_] :=
  Module[{m = (List @@ a) //. x_SVTimes :> x[[2]]},
    If[Length[m] === Length[Union[m]], True,
      Message[uCoords::failed, a]; False]]

uCoords::failed = "Failed to produce standard form of ``"

Attributes[NonCommutativeMultiply] ^= {}




(* Basis of P[n]**V *)

Vector[sv$v];
Format[sv$v[i_], StandardForm] := Subscript["v",i]

modBas[d_] := 
  With[{b = envBas[-d]}, Inner[Tp, b, Array[sv$v, Length[b]], VPlus]]

(*
mvD = a general vector in Ind V of degree d.
req = the equation of hieghness. We split it in two part. The first one
(represented by hiSol) is used to express v[i] via some of them.
The second one (sv$eqHi) consists of remaining equations on remaining v[i].
*)

svDefEq[d_] := With[{v = sv$v, a = sv$a},
    Module[{reqt, so, so1, so2, dimB, ui, w, basWtList},
      sv$Deg = d;
      mvD = modBas[d]; dimB = Length[mvD]; (* general element of I(v) of degree d *)
      If [sv$Print>=1,
        CellPrint[Cell[TextData[{"General element of ", StyleBox["I",FontSlant->"Italic"],
         "(", StyleBox["V", FontSlant->"Italic"], ") of degree ", d, " (here ",
        Cell[BoxData[FormBox[SubscriptBox["v", "i"], TraditionalForm]]],
        " are indefinite elements of an indefinite module ", StyleBox["V", FontSlant->"Italic"], "):"}],
        "Text"]];
        Print[mvD // svImg]];
      req = svRaise[mvD];  (* the dependense of addends of highest vector in I(v) *)
      Vector[w];
      reqt = req /. Act[a[i_], v[j_]] :> w[i, j];
      so = VSolve[# == 0 & /@ reqt][[1]];
      so1 = Cases[so, HoldPattern[v[_] -> _]];
      so2 = Complement[so, so1];
      ui = Complement[Array[v, dimB], First /@ so1];
      hiSol = so1 /. w[i_, j_] :> Act[a[i], v[j]];
      If [sv$Print>=1,
        StylePrint["Partial solution of highness condition:", "Text"];
        Print[hiSol //svImg]];
      basWtList = Weight /@ envBas[-d][[First /@ ui]];
      basWt = Reverse[Union[basWtList]];
      basInd = First /@ ui;
      basBas = basInd[[#]] & /@ (First /@ Position[basWtList, #]) & /@ basWt;
     (* If [sv$Print>=0,
        Print[
          Inner[Rule, Hold /@ basWt, Hold /@ basBas, List] // Release //
            ColumnForm]]; *)
      sv$eqHi =
        so2 /. Rule -> Equal /. 
            w[i_, j_] :> Act[a[i], v[j]] //. hiSol;
      If [sv$Print>=1,
       StylePrint["The remaining highness equations:","Text"];
       Print[sv$eqHi //svImg]];
      sv$hi = mvD //. hiSol;
      If [sv$Print>=1,
        CellPrint[Cell[TextData[{"The candidate for general highest vector in ", StyleBox["I", FontSlant->"Italic"],
          "(", StyleBox["V", FontSlant->"Italic"], ") after partial solving of highness equations:"}],"Text"]];
        Print[sv$hi //svImg]];
      sv$eqZ = Act[#, sv$hi] == 0 & /@ sv$z;
      If [sv$Print>=0,
       CellPrint[Cell[TextData[{"The following highest singular vectors of indicated weights are possible (here ",
         Cell[BoxData[FormBox[SubscriptBox["v", "\[Lambda]"], TraditionalForm]]], " is the highest vector in ",
         StyleBox["V", FontSlant->"Italic"], " and \[Lambda] is its weight):"}], "Text"]];
       Print[
         Union[SequenceForm["\[Lambda]+",Weight[#], ": ", svImg[#]**sv$v["\[Lambda]"],"+..."] & /@ envBas[-d]] // ColumnForm
         ]];
      Null]]

(*
svRepEq[expr] apply substitution list lrep to expression expr and tries to \
simplify the result.
*)

svRep[eq_] := 
  VSort[VNormal /@ (eq /. lrep) //. LinearRule[Tp]] //. 
          LinearCollectRule[Tp, Last] /. 
        a_ ** b_ :> a ** VNormal[b] //. lrep // VNormal

(*
eqMm[expr] returns the list of scalar equations equavalent to the condition
expr\[Element] maximal submodule.
eqPr[expr] returns the list of scalar equations equavalent to the condition
expr\[Element] (maximal submodule)**...
svZ returns the equations of singularity
eqHi returns the equations of highness.
*)

eqPr[eq_VPlus] := 
  DeleteCases[Flatten[eqMon /@ (List @@ eq)], 0] // ColumnForm
eqPr[eq_] := DeleteCases[eqMon[eq], 0] // ColumnForm

eqMon[_ ** z_] := eqMon[z];
SetProperties[eqMon, {Scalar, Vector->First, Linear->First}]

eqMm[z_] := 
  Factor[svSp[#, z] & /@ uxComp[MatchList[z, _sv$m][[1]]] /. lrep, Modulus->p] // gCanc

(*
wgr[x_] := wg[x] - wg[m[1]] // Simplify
*)

svH :=
 (sv$e = DeleteCases[Flatten[eqMm /@ (First /@ DeleteCases[svRep[sv$eqHi], True])], 0];
  If[sv$e==={},
    True,
  (*else*)
    e1 = sv$e // ColumnForm;
    MapIndexed[(#2[[1]] \[Colon] #1)&, sv$e] // ColumnForm])

svZ[i_] := With[{eq = svRep[sv$eqZ[[i]]]}, If[eq === True, sv$e={};True, gPr[eq[[1]]]]];

svZ[] := With[{eq = DeleteCases[svRep[sv$eqZ], True]},
      If[eq === {}, sv$e={};True, gPr[First /@ eq]]];

gPr[eq_] := (sv$e = gCanc /@ gProj[eq];
  If[sv$e==={}, True,
  (*else*)   MapIndexed[(#2[[1]] \[Colon] #1) &, sv$e] // ColumnForm])

gProj[eq_Tp] := DeleteCases[$SNormal/@Flatten[{eqMon[eq]}], 0]
gProj[eq_] := 
    With[{z = eq /. {_sv$n ** v_ :> v, _ ** _ -> 0}}, 
      DeleteCases[svSp[#, z] & /@ uxComp[MatchList[z, _sv$m][[1]]], 0]];
gProj[eq_VPlus] := DeleteCases[Flatten[gProj /@ (List @@ eq)], 0];
gProj[eq_List] := DeleteCases[Flatten[gProj /@ (List @@ eq)], 0];

gCanc[nom_] :=
    With[{gcd = PolynomialGCD[nom, lcanc]},
      If[NumberQ[gcd], Factor[nom,Modulus->$p], gCanc[Cancel[nom/gcd, Modulus->$p]]]];
gCanc[0] = 0;
Attributes[gCanc] ^= {Listable}
lcanc = 1;

(*
Here is the weights in \!\(TraditionalForm\`\(L\_-\)\).A highest vector in \!\
\(TraditionalForm\`\(L\_-\)\[CircleTimes]V\) should contain highest vectors \
on both sides: \!\(TraditionalForm\`l\_0\[CircleTimes]v\) and \
\!\(TraditionalForm\`l\[CircleTimes]v\_0\).Therefore there is a restriction \
on possible weights of v: \!\(\*FormBox[
  FormBox[\(w(v) - w(v\_0) = w(l\_0) - w(l)\),
    "TraditionalForm"], TraditionalForm]\)
*)

(*
cEq[w] returns (and stores in lrep) the general solution for vector of required weight.
*)

svEq::grade = "Unable calculate the grade. Please repeat as svEq[weigh, grade]"


svEq[w_,d_:Auto] := ((*With[{cm = wcomp[w - #], cp = pcomp[w - #]},
                Do[Print[cp[[i]], "*", cm[[j]], ": ", 
                    RaisePr[cp[[i]], cm[[j]]]], {j, 1, Length[cm]}, {i, 1, 
                    Length[cp]}]] & /@ basWt;*)
      lrep = cRep[w,d];
      brnIni[];
      lrep);

cRep[w_,d_] :=
  Flatten[Table[
      With[{cm = mComp[d,-w + basWt[[i]]], kk = basBas[[i]]},
        Table[With[{k = kk[[j]]}, 
            sv$v[k] -> VSum[SVTimes[sv$c[k, l],cm[[l]]], {l, 1, Length[cm]}]], {j, 
            1, Length[kk]}]], {i, 1, Length[basWt]}]]


(* Solving *)

repHist = 0;
svSub[r__] :=
  (repHist = {lrep, lcanc, lexcl, repHist};
    addRep /@ {r};
    lcanc = svHiCf/.List->PolynomialGCD;
    If[lcanc==0, Message[svSub::zero]];
    lcanc *= lexcl;
    lrep)
svSub::zero="The possible solution will be in maximal submodule"

svUnSub := 
  If[repHist =!= 0, {lrep, lcanc, lrepl, repHist} = repHist; lrep]

addRep[r : (_Rule | _RuleDelayed)] :=
  (lcanc = Factor[lcanc /. r, Modulus->$p];
   lexcl = Factor[lexcl /. r, Modulus->$p];
   lrep = 
      If[MemberQ[sv$\[Lambda], r[[1]]], Flatten[{repRep[lrep, r], r}], 
        repRep[lrep, r]])
addRep[r_Integer] := addRep[(r /. $fnd)[[2, 1]]]
addRep[r_] := addRep[$Solve[r == 0][[1]]]

repRep[a_ -> b_, r_] := a -> VNormal[b /. r]
repRep[a_List, r_] := repRep[#, r] & /@ a;

svExcl[r_] := (repHist = {lrep, lexcl, lcanc, repHist}; lcanc *= r; lexcl *= r)


brnIni[] := (lexcl = 1; repHist = brnHist = brnLev = 0; lcanc = svHiCf/.List->PolynomialGCD;)
svBranch::level = "Wrong level ``. Should be from 1 to ``";
svBranch[lev_] := 
    If[IntegerQ[lev] && 1 <= lev <= brnLev + 1 ,
      While[lev <= brnLev,
        {brnLev, lrep, repHist, brnHist, lcanc, lexcl} = brnHist];
      brnHist = {brnLev, lrep, repHist, brnHist, lcanc, lexcl};
      brnLev=lev,
    (*else*)
      Message[svBranch::level, lev, brnLev + 1];
      $Failed];


svSolve := Module[{i, ex, m, cf, sol, res = {}, res2={}},
      If[sv$e==={}, $fnd={}; Return[True]];
      For[i = 1, i <= Length[sv$e], i++,
        ex = sv$e[[i]];
	If[NumberQ[ex],
	  If[ex==0, Continue[],
	  (*else*) Return["No solutions"]]];
        If[Head[ex] =!= Times,
          If[FreeQ[ex, _sv$c], cf = ex; ex = 1, cf = 1],
          cf = Select[ex, FreeQ[#, _sv$c] &];
          ex = Select[ex, ! FreeQ[#, _sv$c] &]];
        sol = TimeConstrained[$Solve[ex == 0],sv$solTime];
        If[sol===$Aborted, Continue[]];
	If[sol === {}, res = {res, i -> {cf, False}}];
        If[Length[sol] == 1,
	  If [FreeQ[sol, Power[_, -1]], 
             res = {res, i -> {cf, sol[[1]]}},
             res2 = {res2, i -> {cf, sol[[1]]}}]]];
      $fnd = Flatten[If[res=!={}, res, res2]];
      If[$fnd==={},
        "Cannot solve",
        ($fnd /. HoldPattern[i_->{e1_,e2_}]:>(i \[Colon] {e1==0,e2})) // ColumnForm]]

svHiCf := sv$hi //. lrep /. sv$m[i_] :> 0 /; i > 1 /.
  _ ** v_ :> Factor[v /. {sv$m[1] :> 1, SVTimes->Times, VPlus -> Plus}, Modulus->$p] /.
  VPlus -> List


svResult :=
  With[{r = GeneralBasis[VNormal[sv$hi //. lrep], sv$c]},
    If[Length[r] == 1, r[[1]], r]] /. a_**b_:>a**VNormal[b]/. HomogenRule[Tp]

End[]
EndPackage[]





